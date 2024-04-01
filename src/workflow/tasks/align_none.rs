use crate::workflow::context::*;
use crate::workflow::task::*;

pub struct AlignNone { }

impl AlignNone {
  pub fn new() -> Self {
    AlignNone {}
  }
}

impl Task for AlignNone {
  fn name(&self) -> String { "align-none".to_string() }
  fn run(&self, context: &mut Context) {
    println!("Treating naive product as final alignment.");
    let rec_expr = context.unaligned_eggroll().parse().unwrap();
    context.aligned_eggroll.replace(rec_expr);
  }
}
