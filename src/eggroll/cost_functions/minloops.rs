use crate::eggroll::ast::*;
use egg::*;
use std::cmp::Ordering;

#[derive(Clone, Debug, PartialEq)]
pub struct LoopCost {
  num_loops: usize,
  ast_size: usize,
  const_int: Option<usize>,
}

impl LoopCost {
  pub fn plus(&self, other: LoopCost) -> LoopCost {
    LoopCost {
      num_loops: self.num_loops + other.num_loops,
      ast_size: self.ast_size + other.ast_size,
      const_int: None,
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
        Eggroll::While(_) => 1,
        Eggroll::WhileNoBody(_) => 1,
        Eggroll::WhileLockstep(_) => 1,
        Eggroll::WhileScheduled(children) => std::cmp::max(
            costs(children[0]).const_int.unwrap(),
            costs(children[1]).const_int.unwrap()),
        _ => 0,
      };
      let ast_size = match enode {
        Eggroll::Rel(children) if children.iter().min() == children.iter().max() => 0,
        _ => 1,
      };
      match enode {
        Eggroll::Num(i) => {
          println!("Saw num: {}", i);
          LoopCost{num_loops, ast_size, const_int: Some(*i)}
        },
        _ => {
          let init_cost = LoopCost{num_loops, ast_size, const_int: None};
          enode.fold(init_cost, |sum, id| sum.plus(costs(id)))
        },
      }
    }
}
