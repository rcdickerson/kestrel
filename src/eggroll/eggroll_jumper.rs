use crate::anneal::choice_graph::*;
use crate::anneal::jumper::*;
use crate::eggroll::ast::*;
use crate::eggroll::to_crel::GuardedRepetitions;
use egg::*;
use rand::seq::SliceRandom;

const REPETITIONS_KEY: &str = "eggroll.jumper.repetitions";
const REPETITIONS_LHS_KEY: &str = "eggroll.jumper.repetitions_lhs";
const REPETITIONS_RHS_KEY: &str = "eggroll.jumper.repetitions_rhs";

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
    let mut count = self.choice_graph.other_root_choices(path).len();
    count += match path.node() {
      Eggroll::GuardedRepeat(_) => 2,
      Eggroll::GuardedRepeatWhile (_) => 4,
      _ => 0,
    };
    count
  }

  fn extract_repetitions(&self, path: &ChoicePath<Eggroll>) -> GuardedRepetitions {
  }
}

impl Jumper<Eggroll, GuardedRepetitions> for EggrollJumper {
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
    let mut options = self.choice_graph.other_root_choices(to_change);

    let mut rep_options = Vec::new();
    let mut push_with_repetitions = |reps: usize| {
      let mut with_tag = to_change.choice_node().clone();
      with_tag.put_metadata_usize(REPETITIONS_KEY.to_string(), reps);
      rep_options.push(with_tag);
    };

    let mut loop_rep_options = Vec::new();
    let mut push_with_loop_repetitions = |lhs_reps: usize, rhs_reps: usize| {
      let mut with_tag = to_change.choice_node().clone();
      with_tag.put_metadata_usize(REPETITIONS_LHS_KEY.to_string(), lhs_reps);
      with_tag.put_metadata_usize(REPETITIONS_RHS_KEY.to_string(), rhs_reps);
      loop_rep_options.push(with_tag);
    };

    match to_change.node() {
      Eggroll::GuardedRepeat(_) => match to_change.choice_node().get_metadata_usize(&REPETITIONS_KEY.to_string()) {
        None => push_with_repetitions(1),
        Some(reps) => {
          push_with_repetitions(reps + 1);
          if reps > 0 {
            push_with_repetitions(reps - 1);
          }
        },
      },
      Eggroll::GuardedRepeatWhile(_) => {
        let lhs_reps = to_change.choice_node().get_metadata_usize(&REPETITIONS_LHS_KEY.to_string());
        let rhs_reps = to_change.choice_node().get_metadata_usize(&REPETITIONS_LHS_KEY.to_string());
        match (lhs_reps, rhs_reps) {
          (Some(lhs_reps), Some(rhs_reps)) => {
            push_with_loop_repetitions(lhs_reps + 1, rhs_reps);
            push_with_loop_repetitions(lhs_reps, rhs_reps + 1);
            if lhs_reps > 0 {
              push_with_loop_repetitions(lhs_reps - 1, rhs_reps);
            }
            if rhs_reps > 0 {
              push_with_loop_repetitions(lhs_reps, rhs_reps - 1);
            }
          },
          _ => push_with_loop_repetitions(1, 0),
        }
      },
      _ => (),
    }

    options.append(&mut rep_options);
    options.append(&mut loop_rep_options);
    let chosen = options.choose(&mut rand::thread_rng()).unwrap();

    self.neighbor = Some(self.choice_graph.switch_choice(&selection, to_change, chosen));
  }

  fn selected_program(&self) -> (RecExpr<Eggroll>, GuardedRepetitions) {
    let selected = self.selected.clone().expect("no current program set");
    let reps = self.extract_repetitions(&selected);
    (selected.to_rec_expr(), reps)
  }

  fn neighbor_program(&self) -> (RecExpr<Eggroll>, GuardedRepetitions) {
    let neighbor = self.neighbor.clone().expect("no current program set");
    let reps = self.extract_repetitions(&neighbor);
    (neighbor.to_rec_expr(), reps)
  }

  fn jump_to_neighbor(&mut self) {
    self.set_selection_from_path(&self.neighbor.clone().expect("no current neighbor"));
  }
}
