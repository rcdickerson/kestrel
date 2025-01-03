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

impl Task for AlignedOutput {
  fn name(&self) -> String { "aligned-output".to_string() }
  fn run(&self, context: &mut Context) {
    context.aligned_output.replace(self.output_mode.crel_to_output(
      &context.aligned_crel(),
      &context.spec(),
      context.unaligned_crel().global_decls.clone(),
      context.unaligned_crel().fundefs.clone(),
      &context.filename()));
  }
}
