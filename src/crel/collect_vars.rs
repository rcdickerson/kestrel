use crate::names::{CollectVars, all_vars, union_all, singleton};
use crate::crel::ast::*;
use std::collections::HashSet;

impl CollectVars for CRel {
  fn vars(&self) -> HashSet<String> {
    match self {
      CRel::Declaration{specifiers, declarators} => {
        union_all(vec!(
          all_vars(specifiers.clone()),
          all_vars(declarators.clone()),
        ))
      },
      CRel::FunctionDefinition{specifiers, declarator, body} => {
        union_all(vec!(
          all_vars(specifiers.clone()),
          declarator.vars(),
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

impl CollectVars for Statement {
  fn vars(&self) -> HashSet<String> {
    match self {
      Statement::BasicBlock(items) => all_vars(items.clone()),
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

impl CollectVars for DeclarationSpecifier {
  fn vars(&self) -> HashSet<String> {
    HashSet::new()
  }
}

impl CollectVars for Declarator {
  fn vars(&self) -> HashSet<String> {
    match self {
      Declarator::Identifier{name} => singleton(name.clone()),
      Declarator::Array{name, size} => {
        union_all(vec!(
          singleton(name.clone()),
          size.as_ref().map_or(HashSet::new(), |expr| expr.vars()),
        ))
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
    let mut vars : Vec<HashSet<String>> = self.specifiers.iter()
      .map(|spec| spec.vars())
      .collect();
    if self.declarator.is_some() {
      vars.push(self.declarator.as_ref().unwrap().vars());
    }
    union_all(vars)
  }
}

impl CollectVars for Declaration {
  fn vars(&self) -> HashSet<String> {
    union_all(vec!(
      all_vars(self.specifiers.clone()),
      all_vars(self.declarators.clone()),
    ))
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
      declarator: Declarator::Function {
        name: "foo".to_string(),
        params: vec!(ParameterDeclaration {
          specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
          declarator: Some(Declarator::Identifier{name: "w".to_string()}),
        })
      },
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
