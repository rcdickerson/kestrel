pub mod condition;
pub mod parser;
pub mod to_crel;

use crate::crel::ast::*;
use crate::crel::blockify::*;
use crate::names::*;
use crate::spec::{condition::*, to_crel::*};
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

  pub fn add_specs_to_main(&self, crel: &CRel) -> CRel {
    let (decls, fundefs) = crate::crel::fundef::extract_fundefs(crel);
    let main_fun = fundefs.get("main").expect("No main function found");

    let mut arb_inits = self.build_arb_inits(&main_fun.params);
    let preconds = self.build_preconds();
    let postconds = self.build_postconds();

    let mut body_items: Vec<BlockItem> = Vec::new();
    body_items.append(&mut arb_inits);
    body_items.push(preconds);
    body_items.push(BlockItem::Statement(main_fun.body.clone()));
    body_items.push(postconds);
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

  fn build_arb_inits(&self, params: &Vec<ParameterDeclaration>) -> Vec<BlockItem> {
    let call_arb_int = Expression::Call {
      callee: Box::new(Expression::Identifier{name: "arb_int".to_string()}),
      args: Vec::new(),
    };
    params.iter()
      .filter(|param| param.declarator.is_some())
      .map(|param| {
        BlockItem::Declaration(
          Declaration {
            specifiers: param.specifiers.clone(),
            declarator: param.declarator.as_ref().unwrap().clone(),
            initializer: Some(call_arb_int.clone())
          }
        )
      })
      .collect()
  }

  fn build_preconds(&self) -> BlockItem {
    let pre_expr = self.pre.to_crel();
    let assume = Expression::Call {
      callee: Box::new(Expression::Identifier{name: "assume".to_string()}),
      args: vec!(pre_expr),
    };
    BlockItem::Statement(Statement::Expression(Box::new(assume)))
  }

  fn build_postconds(&self) -> BlockItem {
    let post_expr = self.pre.to_crel();
    let sassert = Expression::Call {
      callee: Box::new(Expression::Identifier{name: "sassert".to_string()}),
      args: vec!(post_expr),
    };
    BlockItem::Statement(Statement::Expression(Box::new(sassert)))
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
