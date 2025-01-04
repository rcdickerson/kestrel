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
pub struct LoopCost {
  /// The total number of loops in the program.
  num_loops: usize,
  /// The conditional path complexity of the program (used as a
  /// tiebreak).
  cond_paths: usize,
  /// The total AST size of the program (used as a tiebreak).
  ast_size: usize,
}

impl LoopCost {
  /// Construct a new [LoopCost] by adding the values of the given
  /// cost to this cost.
  pub fn plus(&self, other: LoopCost) -> LoopCost {
    LoopCost {
      num_loops: self.num_loops + other.num_loops,
      cond_paths: self.cond_paths + other.cond_paths,
      ast_size: self.ast_size + other.ast_size,
    }
  }
}

impl PartialOrd for LoopCost {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    let loop_cmp = self.num_loops.cmp(&other.num_loops);
    match loop_cmp {
      Ordering::Equal => {
        let path_cmp = self.cond_paths.cmp(&other.cond_paths);
        match path_cmp {
          Ordering::Equal => Some(self.ast_size.cmp(&other.ast_size)),
          _ => Some(path_cmp),
        }
      },
      _ => Some(loop_cmp),
    }
  }
}

/// An Egg cost function which computes [LoopCost]s for [Eggroll]
/// programs.
pub struct MinLoops;
impl CostFunction<Eggroll> for MinLoops {
    type Cost = LoopCost;
    fn cost<C>(&mut self, enode: &Eggroll, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost
    {
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
        _ => {
          enode.fold(0, |sum, id| sum + costs(id).num_loops)
        },
      };
      let cond_paths = match enode {
        Eggroll::If(children) => costs(children[1]).cond_paths + 1,
        Eggroll::IfElse(children) => {
          std::cmp::max(1, costs(children[1]).cond_paths)
            + std::cmp::max(1, costs(children[2]).cond_paths)
        },
        _ => enode.fold(0, |sum, id| sum + costs(id).cond_paths)
      };
      let ast_size = match enode {
        Eggroll::Rel(children) if children.iter().min() == children.iter().max() => 0,
        _ => enode.fold(1, |sum, id| sum + costs(id).ast_size),
      };
      LoopCost{num_loops, cond_paths, ast_size}
    }
}
