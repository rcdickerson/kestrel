//! Converts the [Context]'s aligned [CRel] into the desired output as
//! specified by the user-provided [OutputMode].

use crate::output_mode::*;
use crate::workflow::context::*;
use crate::workflow::task::*;

pub struct AlignedOutput {
  output_mode: OutputMode,
}

impl AlignedOutput {
  pub fn new(output_mode: OutputMode) -> Self {
    AlignedOutput { output_mode }
  }
}

impl <Ctx: Context + AlignsCRel + OutputsAlignment> Task<Ctx> for AlignedOutput {
  fn name(&self) -> String { "aligned-output".to_string() }
  fn run(&self, context: &mut Ctx) {
    let unaligned_crel = context.unaligned_crel().as_ref().expect("Missing unaligned CRel");
    context.accept_aligned_output(self.output_mode.crel_to_output(
      &context.aligned_crel().as_ref().expect("Missing aligned CRel"),
      &context.precondition(),
      &context.postcondition(),
      unaligned_crel.global_decls.clone(),
      unaligned_crel.global_fundefs.clone(),
      &context.output_filename()));
  }
}
