use crate::names::{CollectVars, MapVars, all_vars, union_all, singleton};
use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq)]
pub enum CRel {
  Declaration {
    specifiers: Vec<DeclarationSpecifier>,
    declarators: Vec<InitDeclarator>,
  },
  FunctionDefinition {
    specifiers: Vec<DeclarationSpecifier>,
    name: Declarator,
    params: Vec<Declaration>,
    body: Box<Statement>,
  },
  Seq(Vec<CRel>),
}
impl CollectVars for CRel {
  fn vars(&self) -> HashSet<String> {
    match self {
      CRel::Declaration{ specifiers, declarators } => {
        union_all(vec!(
          all_vars(specifiers.clone()),
          all_vars(declarators.clone()),
        ))
      },
      CRel::FunctionDefinition{ specifiers, name, params, body } => {
        union_all(vec!(
          all_vars(specifiers.clone()),
          name.vars(),
          all_vars(params.clone()),
          body.vars(),
        ))
      },
      CRel::Seq(crels) => all_vars(crels.clone()),
    }
  }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expression {
  Identifier{ name: String },
  ConstInt(i32),
  StringLiteral(String),
  Call {
    callee: Box<Expression>,
    args: Vec<Expression>,
  },
  Unop {
    expr: Box<Expression>,
    op: UnaryOp,
  },
  Binop {
    lhs: Box<Expression>,
    rhs: Box<Expression>,
    op: BinaryOp,
  },
  Statement(Box<Statement>),
}
impl CollectVars for Expression {
  fn vars(&self) -> HashSet<String> {
    match self {
      Expression::Identifier{name} => singleton(name.clone()),
      Expression::ConstInt(_) => HashSet::new(),
      Expression::StringLiteral(_) => HashSet::new(),
      Expression::Call{callee, args} => {
        union_all(vec!(
          callee.vars(),
          all_vars(args.clone()),
        ))
      },
      Expression::Unop{expr, op: _} => expr.vars(),
      Expression::Binop{lhs, rhs, op: _} => {
        union_all(vec!(lhs.vars(), rhs.vars()))
      },
      Expression::Statement(stmt) => stmt.vars(),
    }
  }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Statement {
  Break,
  Compound(Vec<BlockItem>),
  Expression(Box<Expression>),
  If {
    condition: Box<Expression>,
    then: Box<Statement>,
    els: Option<Box<Statement>>,
  },
  None,
  Relation {
    lhs: Box<Statement>,
    rhs: Box<Statement>,
  },
  Return(Option<Box<Expression>>),
  While {
    condition: Box<Expression>,
    body: Option<Box<Statement>>,
  },
}
impl CollectVars for Statement {
  fn vars(&self) -> HashSet<String> {
    match self {
      Statement::Break => HashSet::new(),
      Statement::Compound(items) => all_vars(items.clone()),
      Statement::Expression(expr) => expr.vars(),
      Statement::If{condition, then, els} => {
        union_all(vec!(
          condition.vars(),
          then.vars(),
          match els {
            None => HashSet::new(),
            Some(stmt) => stmt.vars(),
          },
        ))
      },
      Statement::None => HashSet::new(),
      Statement::Relation{lhs, rhs} => {
        union_all(vec!(lhs.vars(), rhs.vars()))
      },
      Statement::Return(expr) => {
        match expr {
          None => HashSet::new(),
          Some(expr) => expr.vars(),
        }
      },
      Statement::While{condition, body} => {
        match body {
          None => condition.vars(),
          Some(body) => union_all(vec!(condition.vars(), body.vars()))
        }
      },
    }
  }
}

#[derive(Clone, Debug, PartialEq)]
pub struct InitDeclarator {
  pub declarator: Declarator,
  pub expression: Option<Expression>
}
impl CollectVars for InitDeclarator {
  fn vars(&self) -> HashSet<String> {
    match &self.expression {
      None => self.declarator.vars(),
      Some(expr) => union_all(vec!(
        self.declarator.vars(),
        expr.vars()))
    }
  }
}


#[derive(Clone, Debug, PartialEq)]
pub enum DeclarationSpecifier {
  StorageClass(StorageClassSpecifier),
  TypeSpecifier(Type),
}
impl CollectVars for DeclarationSpecifier {
  fn vars(&self) -> HashSet<String> {
    HashSet::new()
  }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
  Bool,
  Double,
  Float,
  Int,
  Void,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Declarator {
  Identifier{ name: String },
}
impl CollectVars for Declarator {
  fn vars(&self) -> HashSet<String> {
    match self {
      Declarator::Identifier{name} => singleton(name.clone()),
    }
  }
}


#[derive(Clone, Debug, PartialEq)]
pub struct Declaration {
  pub specifiers: Vec<DeclarationSpecifier>,
  pub declarators: Vec<InitDeclarator>,
}
impl CollectVars for Declaration {
  fn vars(&self) -> HashSet<String> {
    union_all(vec!(
      all_vars(self.specifiers.clone()),
      all_vars(self.declarators.clone()),
    ))
  }
}


#[derive(Clone, Debug, PartialEq)]
pub enum UnaryOp {
  Minus,
  Not,
}

#[derive(Clone, Debug, PartialEq)]
pub enum BinaryOp {
  Add,
  And,
  Assign,
  Sub,
  Div,
  Equals,
  Gt,
  Gte,
  Index,
  Lt,
  Lte,
  Mod,
  Mul,
  NotEquals,
  Or,
}

#[derive(Clone, Debug, PartialEq)]
pub enum StorageClassSpecifier {
  Extern,
}

#[derive(Clone, Debug, PartialEq)]
pub enum BlockItem {
  Declaration(Declaration),
  Statement(Statement),
}
impl CollectVars for BlockItem {
  fn vars(&self) -> HashSet<String> {
    match self {
      BlockItem::Declaration(decl) => decl.vars(),
      BlockItem::Statement(stmt) => stmt.vars(),
    }
  }
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn test_collect_vars() {
    let prog = CRel::FunctionDefinition {
      specifiers: vec!(),
      name: Declarator::Identifier{name: "foo".to_string()},
      params: vec!(Declaration {
        specifiers: vec!(),
        declarators: vec!(InitDeclarator {
          declarator: Declarator::Identifier{name: "w".to_string()},
          expression: None,
        }),
      }),
      body: Box::new(Statement::If{
        condition: Box::new(Expression::Binop {
          lhs: Box::new(Expression::Identifier{name: "x".to_string()}),
          rhs: Box::new(Expression::Identifier{name: "y".to_string()}),
          op: BinaryOp::Equals
        }),
        then: Box::new(Statement::Expression(
          Box::new(Expression::Binop {
          lhs: Box::new(Expression::Identifier{name: "x".to_string()}),
          rhs: Box::new(Expression::Identifier{name: "y".to_string()}),
          op: BinaryOp::Add
        }))),
        els: Some(Box::new(Statement::Expression(
          Box::new(Expression::Identifier{name: "z".to_string()})))),
      })
    };

    let expected = vec!("foo", "w", "x", "y", "z").iter()
      .map(|v| v.to_string())
      .collect::<HashSet<String>>();

    assert_eq!(prog.vars(), expected);
  }
}
