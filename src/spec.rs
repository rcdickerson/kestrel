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

  pub fn build_unaligned_crel(&self, crel: &CRel) -> CRel {
    let (crel, fundefs) = crate::crel::fundef::extract_fundefs(crel);

    let left_fun = fundefs.get(&self.left)
      .expect(format!("Function not found: {}", self.left).as_str());
    let right_fun = fundefs.get(&self.right)
      .expect(format!("Function not found: {}", self.right).as_str());

    let mut globals = match &crel {
      None => HashSet::new(),
      Some(c) => global_vars(c),
    };
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

    match crel {
      None => new_main,
      Some(CRel::Seq(crels)) => {
        let mut with_main = crels.clone();
        with_main.push(new_main);
        CRel::Seq(with_main)
      },
      Some(crel) => CRel::Seq(vec!{crel, new_main})
    }
  }
}

fn global_vars(crel: &CRel) -> HashSet<String> {
  match crel {
    CRel::Declaration{ specifiers: _, declarators: decls } => {
      let mut vars = HashSet::new();
      for decl in decls {
        vars.insert(declarator_name(&decl.declarator));
      }
      vars
    },
    CRel::FunctionDefinition{specifiers: _, name:_, params: _, body:_} => {
      HashSet::new()
    },
    CRel::Seq(crels) => {
      crels.iter()
        .map(global_vars)
        .fold(HashSet::new(), |s, v| s.union(&v).cloned().collect())
    },
  }
}

fn declarator_name(decl: &Declarator) -> String {
  match &decl {
    Declarator::Identifier{name} => name.clone(),
    Declarator::Array{name, size:_} => name.clone(),
    Declarator::Function{name, params:_} => name.clone(),
    Declarator::Pointer(decl) => declarator_name(&decl),
  }
}
