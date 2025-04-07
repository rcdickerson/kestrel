//! Creates a product program with no alignment by naively
//! concatenating the input programs together.

use crate::workflow::context::*;
use crate::workflow::task::*;

pub struct AlignNone { }

impl AlignNone {
  pub fn new() -> Self {
    AlignNone {}
  }
}

impl <Ctx: AlignsEggroll> Task<Ctx> for AlignNone {
  fn name(&self) -> String { "align-none".to_string() }
  fn run(&self, context: &mut Ctx) {
    println!("Treating naive product as final alignment.");
    let rec_expr = context.unaligned_eggroll().as_ref()
        .expect("Missing unaligned Eggroll")
        .parse().unwrap();
    context.accept_aligned_eggroll(rec_expr);
  }
}
