use crate::eggroll::ast::*;
use egg::*;
use std::cmp::Ordering;

#[derive(Clone, Debug, PartialEq)]
pub struct LoopCost {
  num_loops: usize,
  ast_size: usize,
}

impl LoopCost {
  pub fn plus(&self, other: LoopCost) -> LoopCost {
    LoopCost {
      num_loops: self.num_loops + other.num_loops,
      ast_size: self.ast_size + other.ast_size,
    }
  }
}

impl PartialOrd for LoopCost {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    let loop_cmp = self.num_loops.cmp(&other.num_loops);
    match loop_cmp {
      Ordering::Equal => Some(self.ast_size.cmp(&other.ast_size)),
      _ => Some(loop_cmp),
    }
  }
}

pub struct MinLoops;
impl CostFunction<Eggroll> for MinLoops {
    type Cost = LoopCost;
    fn cost<C>(&mut self, enode: &Eggroll, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost
    {
      let num_loops = match enode {
        Eggroll::While(children) => {
          1 + costs(children[1]).num_loops
        },
        Eggroll::WhileNoBody(_) => 1,
        Eggroll::WhileLockstep(children) => {
          1 + costs(children[4]).num_loops
        },
        Eggroll::WhileScheduled(children) => {
          1 + costs(children[4]).num_loops + costs(children[5]).num_loops
        },
        _ => {
          enode.fold(0, |sum, id| sum + costs(id).num_loops)
        },
      };
      let ast_size = match enode {
        Eggroll::Rel(children) if children.iter().min() == children.iter().max() => 0,
        _ => enode.fold(1, |sum, id| sum + costs(id).ast_size),
      };
      LoopCost{num_loops, ast_size}
    }
}
