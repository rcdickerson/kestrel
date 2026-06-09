use crate::crel::ast::*;
use crate::crel::mapper::*;
use crate::crel::unaligned::UnalignedCRel;
use crate::elaenia::elaenia_spec::*;
use crate::elaenia::tasks::elaenia_context::*;
use crate::workflow::context::*;
use crate::workflow::task::*;

pub struct MarkChoiceFunctions {

}

impl MarkChoiceFunctions {
  pub fn new() -> Self {
    MarkChoiceFunctions { }
  }
}

impl Task<ElaeniaContext> for MarkChoiceFunctions {
  fn name(&self) -> String { "insert-elaenia-specs".to_string() }
  fn run(&self, context: &mut ElaeniaContext) {
    let crel = context.unaligned_crel().clone().expect("Missing unaligned CRel");
    let spec = context.spec().clone();
    let marked_main = crel.unaligned_main.map(&mut ChoiceMarker::new(&spec));
    context.accept_unaligned_eggroll(marked_main.to_eggroll());
    context.accept_unaligned_crel(UnalignedCRel {
      global_decls: crel.global_decls,
      global_fundefs: crel.global_fundefs,
      product_params: crel.product_params,
      unaligned_main: marked_main,
    });
  }
}

struct ChoiceMarker<'a> {
  spec: &'a ElaeniaSpec,
}

impl <'a> ChoiceMarker<'a> {
  fn new(spec: &'a ElaeniaSpec) -> ChoiceMarker<'a> {
    ChoiceMarker { spec }
  }
}

impl <'a> CRelMapper for ChoiceMarker<'a> {
  fn map_expression(&mut self, expr: &Expression) -> Expression {
    match expr {
      Expression::Call{callee, args} => {
        match callee.as_ref() {
          Expression::Identifier{ name } => {
            if self.spec.lookup_aspec(name).is_some()
            || self.spec.lookup_espec(name).is_some() {
              Expression::ChoiceCall {
                callee: callee.clone(),
                args: args.clone()
              }
            } else {
              expr.clone()
            }
          },
          _ => expr.clone(),
        }
      },
      _ => expr.clone(),
    }
  }
}
