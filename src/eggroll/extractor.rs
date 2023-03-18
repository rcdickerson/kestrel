use coin_cbc::{Col, Model, Sense};
use crate::eggroll::ast::*;
use egg::*;
use std::collections::HashMap;

pub struct EggrollExtractor<'a> {
  egraph: &'a EGraph<Eggroll, ()>,
  model: Model,
  groups: HashMap<Id, ChoiceGroup>,
}

struct Choice {
  index: usize,
  col: Col,
  cost: f64,
  required: Vec<Choice>,
}

struct ChoiceGroup {
  col: Col,
  choices: Vec<Choice>,
}

impl<'a> EggrollExtractor<'a> {
  pub fn new(egraph: &'a EGraph<Eggroll, ()>) -> Self {
    let mut model = Model::default();

    let groups: HashMap<Id, ChoiceGroup> = egraph
      .classes()
      .map(|class| {
        let mut choices = Vec::new();
        for (index, node) in class.nodes.iter().enumerate() {
          let cost = match node {
            Eggroll::Rel(_) => 0.0,
            _ => 100.0,
          };
          choices.push(Choice { index,
                                col: model.add_binary(),
                                cost: cost,
                                required: Vec::new() })
        }
        let cgroup = ChoiceGroup { col: model.add_binary(), choices };
        (class.id, cgroup)
      })
      .collect();

    for (&id, group) in &groups {
      // One node in each selected group must get selected.
      let select_node = model.add_row();
      model.set_row_equal(select_node, 0.0);
      model.set_weight(select_node, group.col, -1.0);
      for choice in &group.choices {
        model.set_weight(select_node, choice.col, 1.0);
      }

      // All child classes of selected nodes must get selected.
      for (_, (node, choice)) in egraph[id].iter().zip(&group.choices).enumerate() {
        for child in node.children() {
          let child_group = &groups[child];
          let select_child = model.add_row();
          model.set_row_upper(select_child, 0.0);
          model.set_weight(select_child, choice.col, 1.0);
          model.set_weight(select_child, child_group.col, -1.0);
        }
      }
    }

    // Add low cost choices for good-looking alignments.
    // TODO

    // Set model to minimize cost.
    model.set_obj_sense(Sense::Minimize);
    for class in egraph.classes() {
      for (_, choice) in class.iter().zip(&groups[&class.id].choices) {
        model.set_obj_coeff(choice.col, choice.cost);
      }
    }

    Self { egraph, model, groups }
  }

  pub fn solve(&mut self, root: Id) -> RecExpr<Eggroll> {
    let egraph = self.egraph;

    let root = &egraph.find(root);
    self.model.set_col_lower(self.groups[root].col, 1.0);

    let solution = self.model.solve();
    log::info!(
      "CBC status {:?}, {:?}",
      solution.raw().status(),
      solution.raw().secondary_status()
    );

    let mut todo: Vec<Id> = vec!{ self.egraph.find(*root) };
    let mut expr = RecExpr::default();
    let mut ids: HashMap<Id, Id> = HashMap::default();

    while let Some(&id) = todo.last() {
      if ids.contains_key(&id) {
        todo.pop();
        continue;
      }
      let group = &self.groups[&id];
      assert!(solution.col(group.col) > 0.0);
      let choice_index = group.choices.iter()
        .position(|choice| solution.col(choice.col) > 0.0)
        .unwrap();
      let node = &self.egraph[id].nodes[group.choices[choice_index].index];
      if node.all(|child| ids.contains_key(&child)) {
        let new_id = expr.add(node.clone().map_children(|i| ids[&self.egraph.find(i)]));
        ids.insert(id, new_id);
        todo.pop();
      } else {
        todo.extend_from_slice(node.children())
      }
    }

    assert!(expr.is_dag(), "RelExtractor found a cyclic term!: {:?}", expr);
    expr
  }
}
