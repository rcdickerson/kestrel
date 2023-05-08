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
      CRel::Declaration{specifiers, declarators} => {
        union_all(vec!(
          all_vars(specifiers.clone()),
          all_vars(declarators.clone()),
        ))
      },
      CRel::FunctionDefinition{specifiers, name, params, body} => {
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
impl MapVars for CRel {
  fn map_vars<F>(&self, f: &F) -> Self
    where F: Fn(String) -> String
  {
    match self {
      CRel::Declaration{specifiers, declarators} => CRel::Declaration {
        specifiers: specifiers.clone(),
        declarators: declarators.iter().map(|d| d.map_vars(f)).collect(),
      },
      CRel::FunctionDefinition{specifiers, name, params, body} =>
        CRel::FunctionDefinition {
          specifiers: specifiers.clone(),
          name: name.map_vars(f),
          params: params.iter().map(|p| p.map_vars(f)).collect(),
          body: Box::new(body.map_vars(f)),
        },
      CRel::Seq(crels) => {
        CRel::Seq(crels.iter().map(|c| c.map_vars(f)).collect())
      },
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
impl MapVars for Expression {
  fn map_vars<F>(&self, f: &F) -> Self
    where F: Fn(String) -> String
  {
    match self {
      Expression::Identifier{name} => Expression::Identifier{name: f(name.clone())},
      Expression::ConstInt(i) => Expression::ConstInt(*i),
      Expression::StringLiteral(s) => Expression::StringLiteral(s.clone()),
      Expression::Call{callee, args} => Expression::Call {
        callee: Box::new(callee.map_vars(f)),
        args: args.iter().map(|a| a.map_vars(f)).collect(),
      },
      Expression::Unop{expr, op} => Expression::Unop {
        expr: Box::new(expr.map_vars(f)),
        op: op.clone(),
      },
      Expression::Binop{lhs, rhs, op} => Expression::Binop {
        lhs: Box::new(lhs.map_vars(f)),
        rhs: Box::new(rhs.map_vars(f)),
        op: op.clone(),
      },
      Expression::Statement(stmt) => {
        Expression::Statement(Box::new(stmt.map_vars(f)))
      }
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
impl MapVars for Statement {
  fn map_vars<F>(&self, f: &F) -> Self
    where F: Fn(String) -> String
  {
    match self {
      Statement::Break => Statement::Break,
      Statement::Compound(items) => {
        Statement::Compound(items.iter().map(|i| i.map_vars(f)).collect())
      },
      Statement::Expression(expr) => {
        Statement::Expression(Box::new(expr.map_vars(f)))
      },
      Statement::If{condition, then, els} => Statement::If {
        condition: Box::new(condition.map_vars(f)),
        then: Box::new(then.map_vars(f)),
        els: match els {
          None => None,
          Some(e) => Some(Box::new(e.map_vars(f))),
        }
      },
      Statement::None => Statement::None,
      Statement::Relation{lhs, rhs} => Statement::Relation {
        lhs: Box::new(lhs.map_vars(f)),
        rhs: Box::new(rhs.map_vars(f)),
      },
      Statement::Return(expr) => {
        Statement::Return(match expr {
          None => None,
          Some(expr) => Some(Box::new(expr.map_vars(f))),
        })
      },
      Statement::While{condition, body} => Statement::While {
        condition: Box::new(condition.map_vars(f)),
        body: match body {
          None => None,
          Some(body) => Some(Box::new(body.map_vars(f))),
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
impl MapVars for InitDeclarator {
  fn map_vars<F>(&self, f: &F) -> Self
    where F: Fn(String) -> String
  {
    InitDeclarator {
      declarator: self.declarator.map_vars(f),
      expression: match &self.expression {
        None => None,
        Some(expr) => Some(expr.map_vars(f)),
      }
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
impl MapVars for Declarator {
  fn map_vars<F>(&self, f: &F) -> Self
    where F: Fn(String) -> String
  {
    match self {
      Declarator::Identifier{name} => {
        Declarator::Identifier{name: f(name.clone())}
      },
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
impl MapVars for Declaration {
  fn map_vars<F>(&self, f: &F) -> Self
    where F: Fn(String) -> String
  {
    Declaration {
      specifiers: self.specifiers.clone(),
      declarators: self.declarators.iter().map(|s| s.map_vars(f)).collect(),
    }
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
impl MapVars for BlockItem {
  fn map_vars<F>(&self, f: &F) -> Self
    where F: Fn(String) -> String
  {
    match self {
      BlockItem::Declaration(decl) => BlockItem::Declaration(decl.map_vars(f)),
      BlockItem::Statement(stmt) => BlockItem::Statement(stmt.map_vars(f)),
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

#[test]
  fn test_map_vars() {
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

    let prog2 = prog.map_vars(&|s: String| {
      if s == "foo".to_string() {
        s.clone()
      } else {
        format!("{}2", s)
      }
    });

    let expected = CRel::FunctionDefinition {
      specifiers: vec!(),
      name: Declarator::Identifier{name: "foo".to_string()},
      params: vec!(Declaration {
        specifiers: vec!(),
        declarators: vec!(InitDeclarator {
          declarator: Declarator::Identifier{name: "w2".to_string()},
          expression: None,
        }),
      }),
      body: Box::new(Statement::If{
        condition: Box::new(Expression::Binop {
          lhs: Box::new(Expression::Identifier{name: "x2".to_string()}),
          rhs: Box::new(Expression::Identifier{name: "y2".to_string()}),
          op: BinaryOp::Equals
        }),
        then: Box::new(Statement::Expression(
          Box::new(Expression::Binop {
          lhs: Box::new(Expression::Identifier{name: "x2".to_string()}),
          rhs: Box::new(Expression::Identifier{name: "y2".to_string()}),
          op: BinaryOp::Add
        }))),
        els: Some(Box::new(Statement::Expression(
          Box::new(Expression::Identifier{name: "z2".to_string()})))),
      })
    };

    assert_eq!(prog2, expected);
  }
}
