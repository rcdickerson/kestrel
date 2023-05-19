pub mod condition;
pub mod parser;

use crate::crel::ast::*;
use crate::crel::blockify::*;
use crate::names::*;
use crate::spec::condition::*;

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

    let left_fun = left_fun.map_vars(&|s: String| {
      format!("l_{}", s)
    });
    let right_fun = right_fun.map_vars(&|s: String| {
      format!("r_{}", s)
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
        crels.clone().push(new_main);
        CRel::Seq(crels)
      },
      Some(crel) => CRel::Seq(vec!{crel, new_main})
    }
  }

}
