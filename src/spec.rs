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

  pub fn build_unaligned_crel(&self, crel: &CRel) -> (Vec<Declaration>, CRel) {
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

    let mut params = left_fun.params.clone();
    params.append(&mut right_fun.params.clone());

    let new_main = CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
      name: "main".to_string(),
      params: params,
      body: Box::new(Statement::Relation {
        lhs: Box::new(left_fun.body.blockify()),
        rhs: Box::new(right_fun.body.blockify()),
      })
    };

    (decls, new_main)
  }

  pub fn add_arb_inits(&self, crel: &CRel) -> CRel {
    let (decls, fundefs) = crate::crel::fundef::extract_fundefs(crel);
    let main_fun = fundefs.get("main").expect("No main function found");

    let call_arb_int = Expression::Call {
      callee: Box::new(Expression::Identifier{name: "arb_int".to_string()}),
      args: Vec::new(),
    };
    let arb_param_decls: Vec<Declaration> = main_fun.params.iter()
      .filter(|param| param.declarator.is_some())
      .map(|param| {
        Declaration {
          specifiers: param.specifiers.clone(),
          declarator: param.declarator.as_ref().unwrap().clone(),
          initializer: Some(call_arb_int.clone())
          }
        }).collect();

    let mut body_items: Vec<BlockItem> = arb_param_decls.iter()
      .map(|decl| BlockItem::Declaration(decl.clone()))
      .collect();
    body_items.push(BlockItem::Statement(main_fun.body.clone()));
    let new_body = Statement::Compound(body_items);

    let new_main = CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
      name: "main".to_string(),
      params: Vec::new(),
      body: Box::new(new_body),
    };

    let mut new_seq: Vec<CRel> = decls.iter()
      .map(|decl| CRel::Declaration(decl.clone()))
      .collect();
    new_seq.push(new_main);
    CRel::Seq(new_seq)
  }
}

fn global_vars(decls: &Vec<Declaration>) -> HashSet<String> {
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
