use crate::anneal::choice_graph::*;
use crate::anneal::jumper::*;
use crate::eggroll::ast::*;
use egg::*;
use rand::seq::SliceRandom;

#[derive(Clone)]
pub struct EggrollJumper {
  choice_graph: ChoiceGraph<Eggroll>,
  selected: Option<ChoicePath<Eggroll>>,
  possible_changes: Vec<ChoicePath<Eggroll>>,
  neighbor: Option<ChoicePath<Eggroll>>,
}

impl EggrollJumper {
  pub fn new<N>(egraph: &EGraph<Eggroll, N>) -> Self
    where N: Analysis<Eggroll>,
  {
    EggrollJumper {
      choice_graph: ChoiceGraph::new(egraph),
      selected: None,
      possible_changes: Vec::new(),
      neighbor: None,
    }
  }

  pub fn set_selection_from_path(&mut self, selection: &ChoicePath<Eggroll>) {
    self.selected = Some(selection.clone());
    self.possible_changes = self.choice_graph.possible_changes(&selection, |subpath| {
      self.count_path_neighbors(subpath)
    });
  }

  fn count_path_neighbors(&self, path: &ChoicePath<Eggroll>) -> usize {
    let mut count = match path.node() {
//      Eggroll::GuardedRepeat(_) => 2,
//      Eggroll::GuardedRepeatWhile(_) => 4,
      _ => 0,
    };
    count += self.choice_graph.other_root_choices(path).len();
    count
  }
}

impl Jumper<Eggroll> for EggrollJumper {
  fn set_selection(&mut self, expr: &RecExpr<Eggroll>) {
    self.set_selection_from_path(&self.choice_graph.find_expression_path(expr));
  }

  fn set_selection_random(&mut self) {
    self.set_selection_from_path(&self.choice_graph.random_path());
  }

  fn pick_random_neighbor(&mut self) {
    if self.possible_changes.is_empty() {
      println!("no possible jumps found");
    }
    let selection = self.selected.clone().expect("no current selection");
    let to_change = self.possible_changes.choose(&mut rand::thread_rng()).unwrap();
    self.neighbor = Some(self.choice_graph.switch_choice(&selection, to_change));
  }

  fn selected_program(&self) -> RecExpr<Eggroll> {
    self.selected.clone().expect("no current program set").to_rec_expr()
  }

  fn neighbor_program(&self) -> RecExpr<Eggroll> {
    self.neighbor.clone().expect("no current program set").to_rec_expr()
  }

  fn jump_to_neighbor(&mut self) {
    self.set_selection_from_path(&self.neighbor.clone().expect("no current neighbor"));
  }
}
