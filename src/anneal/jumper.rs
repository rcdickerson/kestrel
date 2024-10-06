use egg::*;

pub trait Jumper<L: Language> {
  fn set_selection(&mut self, selection: &RecExpr<L>);
  fn set_selection_random(&mut self);

  fn pick_random_neighbor(&mut self);

  fn selected_program(&self) -> RecExpr<L>;
  fn neighbor_program(&self) -> RecExpr<L>;

  fn jump_to_neighbor(&mut self);
}
