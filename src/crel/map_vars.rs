use crate::names::MapVars;
use crate::crel::ast::*;

impl MapVars for CRel {
  fn map_vars<F>(&self, f: &F) -> Self
    where F: Fn(String) -> String
  {
    match self {
      CRel::Declaration(decl) => CRel::Declaration(decl.map_vars(f)),
      CRel::FunctionDefinition{specifiers, name, params, body} =>
        CRel::FunctionDefinition {
          specifiers: specifiers.clone(),
          name: f(name.clone()),
          params: params.iter().map(|param| param.map_vars(f)).collect(),
          body: Box::new(body.map_vars(f)),
        },
      CRel::Seq(crels) => {
        CRel::Seq(crels.iter().map(|c| c.map_vars(f)).collect())
      },
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
      Expression::ConstFloat(f) => Expression::ConstFloat(*f),
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
      Expression::Forall{pred_var, pred_type, condition} => Expression::Forall {
        pred_var: f(pred_var.clone()),
        pred_type: pred_type.clone(),
        condition: Box::new(condition.clone().map_vars(f)),
      },
      Expression::Statement(stmt) => {
        Expression::Statement(Box::new(stmt.map_vars(f)))
      }
    }
  }
}

impl MapVars for Statement {
  fn map_vars<F>(&self, f: &F) -> Self
    where F: Fn(String) -> String
  {
    match self {
      Statement::BasicBlock(items) => {
        Statement::BasicBlock(items.iter().map(|i| i.map_vars(f)).collect())
      },
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
        els: els.as_ref().map(|e| Box::new(e.map_vars(f)))
      },
      Statement::None => Statement::None,
      Statement::Relation{lhs, rhs} => Statement::Relation {
        lhs: Box::new(lhs.map_vars(f)),
        rhs: Box::new(rhs.map_vars(f)),
      },
      Statement::Return(expr) => {
        Statement::Return(expr.as_ref().map(|expr| Box::new(expr.map_vars(f))))
      },
      Statement::While{loop_id, invariants: invariant, condition, body} => Statement::While {
        loop_id: loop_id.clone(),
        invariants: invariant.clone(),
        condition: Box::new(condition.map_vars(f)),
        body: body.as_ref().map(|body| Box::new(body.map_vars(f)))
      },
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
      Declarator::Array{name, sizes} => {
        Declarator::Array {
          name: f(name.clone()),
          sizes: sizes.iter().map(|expr| expr.map_vars(f)).collect(),
        }
      },
      Declarator::Function{name, params} => {
        Declarator::Function {
          name: f(name.clone()),
          params: params.iter().map(|decl| decl.map_vars(f)).collect(),
        }
      },
      Declarator::Pointer(decl) => {
        Declarator::Pointer(Box::new(decl.map_vars(f)))
      },
    }
  }
}

impl MapVars for ParameterDeclaration {
  fn map_vars<F>(&self, f: &F) -> Self
    where F: Fn(String) -> String
  {
    ParameterDeclaration {
      specifiers: self.specifiers.clone(),
      declarator: self.declarator.as_ref().map(|decl| decl.map_vars(f)),
    }
  }
}

impl MapVars for Declaration {
  fn map_vars<F>(&self, f: &F) -> Self
    where F: Fn(String) -> String
  {
    Declaration {
      specifiers: self.specifiers.clone(),
      declarator: self.declarator.map_vars(f),
      initializer: self.initializer.as_ref().map(|expr| expr.map_vars(f)),
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
  fn test_map_vars() {
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

    let prog2 = prog.map_vars(&|s: String| {
      if s == *"foo" {
        s.clone()
      } else {
        format!("{}2", s)
      }
    });

    let expected = CRel::FunctionDefinition {
      specifiers: vec!(),
      name: "foo".to_string(),
      params: vec!(ParameterDeclaration {
        specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
        declarator: Some(Declarator::Identifier{name: "w2".to_string()}),
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
