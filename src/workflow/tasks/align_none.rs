//! Creates a product program with no alignment by naively
//! concatenating the input programs together.

use crate::workflow::Context;
use crate::workflow::task::*;

pub struct AlignNone { }

impl AlignNone {
  pub fn new() -> Self {
    AlignNone {}
  }
}

impl <Ctx: Context> Task<Ctx> for AlignNone {
  fn name(&self) -> String { "align-none".to_string() }
  fn run(&self, context: &mut Ctx) {
    println!("Treating naive product as final alignment.");
    let rec_expr = context.unaligned_eggroll().parse().unwrap();
    context.accept_aligned_eggroll(rec_expr);
  }
}
