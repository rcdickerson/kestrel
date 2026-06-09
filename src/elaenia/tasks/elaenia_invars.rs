use crate::elaenia::tasks::elaenia_context::*;
use crate::workflow::InvarsDaikon;
use crate::crel::ast::*;
use crate::workflow::task::*;

pub struct ElaeniaInvars { }

impl ElaeniaInvars {
  pub fn new() -> Self {
    ElaeniaInvars { }
  }
}

impl Task<ElaeniaContext> for ElaeniaInvars {
  fn name(&self) -> String { "elaenia-invars".to_string() }

  fn run(&self, context: &mut ElaeniaContext) {
    let mut daikon_task = InvarsDaikon::new(None);
    for havoc_decl in context.havoc_funs_as_decls() {
      daikon_task.add_global_decl(havoc_decl);
    }
    for choice_fun in context.choice_funs() {
      match context.choice_solutions().get(&choice_fun.name) {
        Some(solution) => daikon_task.add_fundef(solution.clone()),
        None => daikon_task.add_global_decl(Declaration{
          specifiers: choice_fun.specifiers.clone(),
          declarator: Declarator::Function {
            name: choice_fun.name.clone(),
            params: choice_fun.params.clone(),
          },
          initializer: None,
        }),
      }
    }
    daikon_task.run(context);
  }
}
