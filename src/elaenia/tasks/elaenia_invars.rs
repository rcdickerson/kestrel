use crate::elaenia::tasks::elaenia_context::*;
use crate::workflow::InvarsDaikon;
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
    for (_, choice_fun) in context.choice_solutions() {
      daikon_task.add_fundef(choice_fun.clone());
    }
    daikon_task.run(context);
  }
}
