use crate::crel::ast::*;

pub trait CountLoops {
  fn count_loops(&self) -> usize;
}

impl CountLoops for CRel {
  fn count_loops(&self) -> usize {
    match self {
      CRel::Declaration{specifiers:_, declarators:_} => 0,
      CRel::FunctionDefinition{specifiers:_, name:_, params:_, body} => {
        body.count_loops()
      },
      CRel::Seq(crels) => crels.iter().map(|c| c.count_loops()).sum(),
    }
  }
}

impl CountLoops for Expression {
  fn count_loops(&self) -> usize {
    match self {
      Expression::Identifier{name:_} => 0,
      Expression::ConstInt(_) => 0,
      Expression::StringLiteral(_) => 0,
      Expression::Call{callee:_, args:_} => 0,
      Expression::Unop{expr, op: _} => expr.count_loops(),
      Expression::Binop{lhs, rhs, op: _} => lhs.count_loops() + rhs.count_loops(),
      Expression::Statement(stmt) => stmt.count_loops(),
    }
  }
}

impl CountLoops for Statement {
  fn count_loops(&self) -> usize {
    match self {
      Statement::BasicBlock(items) => items.iter().map(|i| i.count_loops()).sum(),
      Statement::Break => 0,
      Statement::Compound(items) => items.iter().map(|i| i.count_loops()).sum(),
      Statement::Expression(expr) => expr.count_loops(),
      Statement::If{condition:_, then, els} => {
        then.count_loops() + match els {
          None => 0,
          Some(stmt) => stmt.count_loops(),
        }
      }
      Statement::None => 0,
      Statement::Relation{lhs, rhs} => {
        lhs.count_loops() + rhs.count_loops()
      },
      Statement::Return(_) => 0,
      Statement::While{condition, body} => {
        1 + condition.count_loops() + match body {
          None => 0,
          Some(body) => body.count_loops(),
        }
      },
    }
  }
}

impl CountLoops for InitDeclarator {
  fn count_loops(&self) -> usize {
    match &self.expression {
      None => 0,
      Some(expr) => expr.count_loops(),
    }
  }
}

impl CountLoops for DeclarationSpecifier {
  fn count_loops(&self) -> usize { 0 }
}

impl CountLoops for Declarator {
  fn count_loops(&self) -> usize { 0 }
}

impl CountLoops for Declaration {
  fn count_loops(&self) -> usize { 0 }
}

impl CountLoops for BlockItem {
  fn count_loops(&self) -> usize {
    match self {
      BlockItem::Declaration(decl) => decl.count_loops(),
      BlockItem::Statement(stmt) => stmt.count_loops(),
    }
  }
}
