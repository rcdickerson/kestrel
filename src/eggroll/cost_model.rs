use crate::eggroll::ast::*;
use egg::*;

pub struct CostModel;
impl CostFunction<Eggroll> for CostModel {
  type Cost = i32;
  fn cost<C>(&mut self, enode: &Eggroll, mut costs: C) -> Self::Cost
  where
    C: FnMut(Id) -> Self::Cost
  {
    let node_cost = match enode {
      Eggroll::Rel(children) if children.iter().min() == children.iter().max() => 0,
      _ => 1
    };
    return enode.fold(node_cost, |sum, id| sum + costs(id));
  }
}
