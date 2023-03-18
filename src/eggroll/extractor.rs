use coin_cbc::{Col, Model, Sense};
use crate::eggroll::ast::*;
use egg::*;
use std::collections::HashMap;

pub struct EggrollExtractor<'a> {
  egraph: &'a EGraph<Eggroll, ()>,
  model: Model,
  vars: HashMap<Id, ClassVars>,
}

struct ClassVars {
  class: Col,
  nodes: Vec<Col>,
}

impl<'a> EggrollExtractor<'a> {
  pub fn new(egraph: &'a EGraph<Eggroll, ()>) -> Self {
    let mut model = Model::default();

    let vars: HashMap<Id, ClassVars> = egraph
      .classes()
      .map(|class| {
        let cvars = ClassVars {
          class: model.add_binary(),
          nodes: class.nodes.iter().map(|_| model.add_binary()).collect(),
        };
        (class.id, cvars)
      })
      .collect();

    for (&id, cvars) in &vars {
      // One node in each selected class must get selected.
      let select_node = model.add_row();
      model.set_row_equal(select_node, 0.0);
      model.set_weight(select_node, cvars.class, -1.0);
      for &node_active in &cvars.nodes {
        model.set_weight(select_node, node_active, 1.0);
      }

      // All child classes of selected nodes must get selected.
      for (_, (node, &node_var)) in egraph[id].iter().zip(&cvars.nodes).enumerate() {
        for child in node.children() {
          let child_var = vars[child].class;
          let select_child = model.add_row();
          model.set_row_upper(select_child, 0.0);
          model.set_weight(select_child, node_var, 1.0);
          model.set_weight(select_child, child_var, -1.0);
        }
      }
    }

    // Set model to minimize cost.
    model.set_obj_sense(Sense::Minimize);
    for class in egraph.classes() {
      for (node, &node_var) in class.iter().zip(&vars[&class.id].nodes) {
        model.set_obj_coeff(node_var, 1.0);//cost_function.cost(egraph, class.id, node));
      }
    }

    Self { egraph, model, vars }
  }

  pub fn solve(&mut self, root: Id) -> RecExpr<Eggroll> {
    let egraph = self.egraph;

    let root = &egraph.find(root);
    self.model.set_col_lower(self.vars[root].class, 1.0);

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
      let cvars = &self.vars[&id];
      assert!(solution.col(cvars.class) > 0.0);
      let node_idx = cvars.nodes.iter().position(|&n| solution.col(n) > 0.0).unwrap();
      let node = &self.egraph[id].nodes[node_idx];
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
