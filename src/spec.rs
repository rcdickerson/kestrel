pub mod condition;
pub mod parser;

use crate::crel::ast::*;
use crate::crel::blockify::*;
use crate::names::*;
use crate::spec::condition::*;
use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq)]
pub struct KestrelSpec {
  pub pre: CondBExpr,
  pub left: String,
  pub right: String,
  pub post: CondBExpr,
}

impl KestrelSpec {

  pub fn build_unaligned_crel(&self, crel: &CRel) -> (Vec<InitDeclarator>, CRel) {
    let (decls, fundefs) = crate::crel::fundef::extract_fundefs(crel);

    let left_fun = fundefs.get(&self.left)
      .expect(format!("Function not found: {}", self.left).as_str());
    let right_fun = fundefs.get(&self.right)
      .expect(format!("Function not found: {}", self.right).as_str());

    let mut globals = global_vars(&decls);
    for f_seahorn in ["assume", "assert", "sassert"] {
      globals.insert(f_seahorn.to_string());
    }

    let left_fun = left_fun.map_vars(&|s: String| {
      if globals.contains(&s) { s } else { format!("l_{}", s) }
    });
    let right_fun = right_fun.map_vars(&|s: String| {
      if globals.contains(&s) { s } else { format!("r_{}", s) }
    });

    let new_main = CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
      name: Declarator::Identifier{ name: "main".to_string() },
      params: vec!(),
      body: Box::new(Statement::Relation {
        lhs: Box::new(left_fun.body.blockify()),
        rhs: Box::new(right_fun.body.blockify()),
      }),
    };

    (decls, new_main)
  }
}

fn global_vars(decls: &Vec<InitDeclarator>) -> HashSet<String> {
  let mut vars = HashSet::new();
  for decl in decls {
    vars.insert(declarator_name(&decl.declarator));
  }
  vars
}

fn declarator_name(decl: &Declarator) -> String {
  match &decl {
    Declarator::Identifier{name} => name.clone(),
    Declarator::Array{name, size:_} => name.clone(),
    Declarator::Function{name, params:_} => name.clone(),
    Declarator::Pointer(decl) => declarator_name(&decl),
  }
}
