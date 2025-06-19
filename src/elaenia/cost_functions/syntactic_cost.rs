//! A cost function which prioritizes minimizing the total number of
//! loops. Since merging two loops into a single relational loop
//! reduces the total number of loops, this has the effect of
//! maximizing the number of merged loops.

//! When two extractions have the same number of loops, this function
//! looks at conditional path complexity and overall AST size as
//! tiebreakers.

use crate::eggroll::ast::*;
use egg::*;
use std::cmp::Ordering;

/// A structure recording the loop cost of some piece of syntax.
#[derive(Clone, Debug, PartialEq)]
pub struct ElaeniaSyntacticCost {
  /// The total number of loops in the program.
  num_loops: usize,
  /// The conditional path complexity of the program (used as a
  /// tiebreak).
  cond_paths: usize,
  /// The total number of relations the program (used as a
  /// tiebreak). Fewer relations means more information for
  /// the right-hand (existential) side choices.
  num_relations: usize,
  /// The total AST size of the program (used as a tiebreak).
  ast_size: usize,
  /// True if this cost is from a conditional loop. Used for some
  /// lightweight if-else analysis.
  is_cond: bool,
}

impl PartialOrd for ElaeniaSyntacticCost {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    match self.num_loops.cmp(&other.num_loops) {
      Ordering::Equal => match self.cond_paths.cmp(&other.cond_paths) {
        Ordering::Equal => match self.num_relations.cmp(&other.num_relations) {
          Ordering::Equal => Some(self.ast_size.cmp(&other.ast_size)),
          num_rels => Some(num_rels),
        },
        path_cmp => Some(path_cmp),
      },
      loop_cmp => Some(loop_cmp),
    }
  }
}

/// An Egg cost function which computes [ElaeniaSyntacticCost]s for
/// [Eggroll] programs.
pub struct ElaeniaSyntacticCostFunction;
impl CostFunction<Eggroll> for ElaeniaSyntacticCostFunction {
    type Cost = ElaeniaSyntacticCost;
  fn cost<C>(&mut self, enode: &Eggroll, mut costs: C) -> Self::Cost
  where
    C: FnMut(Id) -> Self::Cost
  {
    let is_cond = match enode {
      Eggroll::If(_) => true,
      Eggroll::IfElse(_) => true,
      _ => false,
    };
    let num_loops = match enode {
      Eggroll::While(children) => {
        1 + costs(children[2]).num_loops
      },
      Eggroll::WhileNoBody(_) => 1,
      Eggroll::WhileRel(children) => {
        1 + costs(children[6]).num_loops
      },
      Eggroll::GuardedRepeatWhile(children) => {
        1 + costs(children[5]).num_loops + costs(children[6]).num_loops
      },
      Eggroll::IfElse(children) => {
        let then_loops = costs(children[1]).num_loops;
        let else_loops = costs(children[2]).num_loops;
        std::cmp::max(then_loops, else_loops)
      },
      _ => {
        enode.fold(0, |sum, id| sum + costs(id).num_loops)
      },
    };
    let cond_paths = match enode {
      Eggroll::If(children) => costs(children[1]).cond_paths + 1,
      Eggroll::IfElse(children) => {
        let then_cost = costs(children[1]).cond_paths;
        let mut else_cost = costs(children[2]).cond_paths;
        // Collapse nested if-else: "if c1 then t1 else (if c2 then t2 ...)" into
        // one layer of complexity: "(if c1 then t1) (else if c2 then t2) (else ...)"
        // by removing the +1 cost the else's conditional contributed.
        if costs(children[2]).is_cond { else_cost -= 1 }
        let max_child = std::cmp::max(then_cost, else_cost);
        max_child + 1
      },
      // Make cyclomatic complexity inside loops opaque to the enclosing context.
      Eggroll::GuardedRepeat(_) => 0,
      Eggroll::GuardedRepeatWhile(_) => 0,
      Eggroll::While(_) => 0,
      Eggroll::WhileRel(_) => 0,
      // In all other cases, cyclomatic complexity is the sum of child complexity.
      _ => enode.fold(0, |sum, id| sum + costs(id).cond_paths)
    };
    let num_relations = match enode {
      Eggroll::Rel(_) => enode.fold(1, |sum, id| sum + costs(id).num_relations),
      Eggroll::RelLeft(_)  => enode.fold(1, |sum, id| sum + costs(id).num_relations),
      Eggroll::RelRight(_) => enode.fold(1, |sum, id| sum + costs(id).num_relations),
      _ => enode.fold(0, |sum, id| sum + costs(id).num_relations),
    };
    let ast_size = match enode {
      Eggroll::Rel(children) if children.iter().min() == children.iter().max() => 0,
      _ => enode.fold(1, |sum, id| sum + costs(id).ast_size),
    };
    ElaeniaSyntacticCost{num_loops, cond_paths, num_relations, ast_size, is_cond}
  }
}
