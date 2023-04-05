use coin_cbc::{Col, Model, Sense};
use crate::eggroll::ast::*;
use egg::*;
use std::collections::HashMap;
use std::mem::discriminant;

pub struct MilpExtractor<'a> {
  egraph: &'a EGraph<Eggroll, ()>,
  model: Model,
  groups: HashMap<Id, ChoiceGroup>,
}

#[derive(Clone)]
struct Choice {
  index: usize,
  col: Col,
  cost: f64,
  required: Vec<Col>,
}

#[derive(Clone)]
struct ChoiceGroup {
  class_id: Id,
  col: Col,
  choices: Vec<Choice>,
}

impl<'a> MilpExtractor<'a> {
  pub fn new(egraph: &'a EGraph<Eggroll, ()>) -> Self {
    let mut model = Model::default();

    // Create the initial choice groups based on e-classes.
    let mut groups: HashMap<Id, ChoiceGroup> = egraph
      .classes()
      .map(|class| {
        let mut choices = Vec::new();
        for (index, node) in class.nodes.iter().enumerate() {
          let cost = match node {
            Eggroll::Assert(_) => 0.0,
            Eggroll::Call(_) => 0.0,
            Eggroll::Rel(_) => 0.0,
            _ => 100.0,
          };
          choices.push(Choice { index,
                                col: model.add_binary(),
                                cost: cost,
                                required: Vec::new() })
        }
        let cgroup = ChoiceGroup { class_id: class.id, col: model.add_binary(), choices };
        (class.id, cgroup)
      })
      .collect();

    // Add low cost choices for good-looking alignments.
    for class in egraph.classes() {
      for (node_index, node) in class.nodes.iter().enumerate() {
        match node {
          Eggroll::Rel(child_ids) => {
            let left_class  = &egraph[child_ids[0]];
            let right_class = &egraph[child_ids[1]];
            let rel_col = groups[&class.id].choices[node_index].col;

            for (left_index, left_node) in left_class.iter().enumerate() {
              for (right_index, right_node) in right_class.iter().enumerate() {
                if discriminant(left_node) == discriminant(right_node)
                   && !matches!(left_node, Eggroll::Seq(_))
                   && !matches!(left_node, Eggroll::While(_)) {
                  let left_choice = &groups[&left_class.id].choices[left_index];
                  let right_choice = &groups[&right_class.id].choices[right_index];

                  let mut cheap_left_choice = Choice {
                    index: left_choice.index,
                    col: model.add_binary(),
                    cost: 1.0,
                    required: vec!(rel_col),
                  };
                  let mut cheap_right_choice = Choice {
                    index: right_choice.index,
                    col: model.add_binary(),
                    cost: 1.0,
                    required: vec!(rel_col),
                  };

                  cheap_left_choice.required.push(cheap_right_choice.col);
                  cheap_right_choice.required.push(cheap_left_choice.col);

                  groups.get_mut(&left_class.id).unwrap().choices.push(cheap_left_choice);
                  groups.get_mut(&right_class.id).unwrap().choices.push(cheap_right_choice);
                }
              }
            }
          }
          _ => ()
        }
      }
    }

    // Encode constraints.
    for (_, group) in &groups {

      // One node in each selected group must be selected.
      let select_node = model.add_row();
      model.set_row_equal(select_node, 0.0);
      model.set_weight(select_node, group.col, -1.0);
      for choice in &group.choices {
        model.set_weight(select_node, choice.col, 1.0);
      }

      // All child classes of selected nodes must get selected.
      for choice in group.choices.iter() {
        for child in egraph[group.class_id].nodes[choice.index].children().iter() {
          let child_group = &groups[child];
          let select_child = model.add_row();
          model.set_row_upper(select_child, 0.0);
          model.set_weight(select_child, choice.col, 1.0);
          model.set_weight(select_child, child_group.col, -1.0);
        }
      }

      // Any choices contingent on other selections can only be
      // made along with those selections.
      for choice in group.choices.iter() {
        for req_col in choice.required.iter() {
          let select_req = model.add_row();
          model.set_row_upper(select_req, 0.0);
          model.set_weight(select_req, choice.col, 1.0);
          model.set_weight(select_req, *req_col, -1.0);
        }
      }
    }

    // Set model to minimize cost.
    model.set_obj_sense(Sense::Minimize);
    for (_, group) in &groups {
      for choice in group.choices.iter() {
        model.set_obj_coeff(choice.col, choice.cost);
      }
    }

    Self { egraph, model, groups }
  }

  pub fn solve(&mut self, root: Id) -> RecExpr<Eggroll> {
    let root = &self.egraph.find(root);
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
