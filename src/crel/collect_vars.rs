use crate::names::{CollectVars, all_vars, union_all, singleton};
use crate::crel::ast::*;
use std::collections::HashSet;

impl CollectVars for CRel {
  fn vars(&self) -> HashSet<String> {
    match self {
      CRel::Declaration(decl) => decl.vars(),
      CRel::FunctionDefinition{specifiers:_, name, params, body} => {
        union_all(vec!(
          singleton(name.clone()),
          all_vars(params.clone()),
          body.vars(),
        ))
      },
      CRel::Seq(crels) => all_vars(crels.clone()),
    }
  }
}

impl CollectVars for Expression {
  fn vars(&self) -> HashSet<String> {
    match self {
      Expression::Identifier{name} => singleton(name.clone()),
      Expression::ConstInt(_) => HashSet::new(),
      Expression::ConstFloat(_) => HashSet::new(),
      Expression::StringLiteral(_) => HashSet::new(),
      Expression::Call{callee, args} => {
        union_all(vec!(
          callee.vars(),
          all_vars(args.clone()),
        ))
      },
      Expression::ASpecCall{callee, args} => {
        union_all(vec!(
          callee.vars(),
          all_vars(args.clone()),
        ))
      },
      Expression::ESpecCall{callee, args} => {
        union_all(vec!(
          callee.vars(),
          all_vars(args.clone()),
        ))
      },
      Expression::Unop{expr, op: _} => expr.vars(),
      Expression::Binop{lhs, rhs, op: _} => {
        union_all(vec!(lhs.vars(), rhs.vars()))
      },
      Expression::Forall{condition, ..} => condition.vars(),
      Expression::Statement(stmt) => stmt.vars(),
    }
  }
}

impl CollectVars for Statement {
  fn vars(&self) -> HashSet<String> {
    match self {
      Statement::BasicBlock(items) => all_vars(items.clone()),
      Statement::Break => HashSet::new(),
      Statement::Compound(items) => all_vars(items.clone()),
      Statement::Expression(expr) => expr.vars(),
      Statement::GuardedRepeat{condition, body, ..} => {
        union_all(vec!(condition.vars(), body.vars()))
      }
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
      Statement::While{condition, body, ..} => {
        match body {
          None => condition.vars(),
          Some(body) => union_all(vec!(condition.vars(), body.vars()))
        }
      },
    }
  }
}

impl CollectVars for Declaration {
  fn vars(&self) -> HashSet<String> {
    match &self.initializer {
      None => self.declarator.vars(),
      Some(expr) => union_all(vec!(
        self.declarator.vars(),
        expr.vars()))
    }
  }
}

impl CollectVars for Declarator {
  fn vars(&self) -> HashSet<String> {
    match self {
      Declarator::Identifier{name} => singleton(name.clone()),
      Declarator::Array{name, sizes} => {
        let mut vars = sizes.iter()
          .map(|expr| expr.vars())
          .collect::<Vec<HashSet<String>>>();
        vars.push(singleton(name.clone()));
        union_all(vars)
      },
      Declarator::Function{name, params} => {
        let mut vars : Vec<HashSet<String>> = params.iter()
          .map(|p| p.vars())
          .collect();
        vars.push(singleton(name.clone()));
        union_all(vars)
      },
      Declarator::Pointer(decl) => {
        decl.vars()
      }
    }
  }
}

impl CollectVars for ParameterDeclaration {
  fn vars(&self) -> HashSet<String> {
    match &self.declarator {
      None => HashSet::new(),
      Some(decl) => decl.vars(),
    }
  }
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
      name: "foo".to_string(),
      params: vec!(ParameterDeclaration {
        specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
        declarator: Some(Declarator::Identifier{name: "w".to_string()}),
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

    let expected = ["foo", "w", "x", "y", "z"].iter()
      .map(|v| v.to_string())
      .collect::<HashSet<String>>();

    assert_eq!(prog.vars(), expected);
  }
}
