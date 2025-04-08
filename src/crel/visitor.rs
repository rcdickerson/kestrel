use std::borrow::BorrowMut;

use crate::crel::ast::*;

pub trait CRelVisitor {
  fn visit_crel(&mut self, _: &mut CRel) { }
  fn visit_declarator(&mut self, _: &mut Declarator) { }
  fn visit_declaration(&mut self, _: &mut Declaration) { }
  fn visit_parameter_declaration(&mut self, _: &mut ParameterDeclaration) { }
  fn visit_declaration_specifier(&mut self, _: &mut DeclarationSpecifier) { }
  fn visit_statement(&mut self, _: &mut Statement) { }
  fn visit_expression(&mut self, _: &mut Expression) { }
  fn visit_block_item(&mut self, _: &mut BlockItem) { }
  fn visit_name(&mut self, _: &mut String) { }
}

impl CRel {
  pub fn walk(&mut self, visitor: &mut dyn CRelVisitor) {
    match self {
      CRel::Declaration(decl) => {
        visitor.visit_declaration(decl);
        decl.walk(visitor);
      },
      CRel::FunctionDefinition{specifiers, name, params, body, ..} => {
        for spec in specifiers { visitor.visit_declaration_specifier(spec) }
        visitor.visit_name(name);
        for param in params {
          visitor.visit_parameter_declaration(param);
          param.walk(visitor);
        }
        visitor.visit_statement(body);
        body.walk(visitor);
      },
      CRel::Seq(stmts) => for stmt in stmts {
        visitor.visit_crel(stmt);
        stmt.walk(visitor);
      }
    }
  }
}

impl Declarator {
  pub fn walk(&mut self, visitor: &mut dyn CRelVisitor) {
    match self {
      Declarator::Identifier{name} => visitor.visit_name(name),
      Declarator::Array{name, sizes} => {
        visitor.visit_name(name);
        for expr in sizes {
          visitor.visit_expression(expr);
          expr.walk(visitor);
        }
      },
      Declarator::Function{name, params} => {
        visitor.visit_name(name);
        for param in params {
          visitor.visit_parameter_declaration(param);
          param.walk(visitor);
        }
      },
      Declarator::Pointer(decl) => {
        visitor.visit_declarator(decl);
        decl.walk(visitor);
      },
    }
  }
}

impl Declaration {
  pub fn walk(&mut self, visitor: &mut dyn CRelVisitor) {
    for spec in self.specifiers.iter_mut() { visitor.visit_declaration_specifier(spec) }
    visitor.visit_declarator(self.declarator.borrow_mut());
    self.declarator.borrow_mut().walk(visitor);
    for init in self.initializer.iter_mut() {
      visitor.visit_expression(init);
      init.walk(visitor);
    }
  }
}

impl ParameterDeclaration {
  pub fn walk(&mut self, visitor: &mut dyn CRelVisitor) {
    for spec in self.specifiers.iter_mut() {
      visitor.visit_declaration_specifier(spec);
    }
    for decl in self.declarator.iter_mut() {
      visitor.visit_declarator(decl);
      decl.walk(visitor);
    }
  }
}

impl Statement {
  pub fn walk(&mut self, visitor: &mut dyn CRelVisitor) {
    match self {
      Statement::BasicBlock(items) => for item in items {
        visitor.visit_block_item(item);
        item.walk(visitor);
      },
      Statement::Break => (),
      Statement::Compound(items) => for item in items {
        visitor.visit_block_item(item);
        item.walk(visitor);
      },
      Statement::Expression(expr) => {
        visitor.visit_expression(expr);
        expr.walk(visitor);
      },
      Statement::Fail => (),
      Statement::GuardedRepeat{body, ..} => {
        visitor.visit_statement(body);
        body.walk(visitor);
      },
      Statement::If{then, els, ..} => {
        visitor.visit_statement(then);
        then.walk(visitor);
        for e in els.iter_mut() {
          visitor.visit_statement(e);
          e.walk(visitor);
        }
      },
      Statement::None => (),
      Statement::Relation{lhs, rhs} => {
        visitor.visit_statement(lhs);
        lhs.walk(visitor);
        visitor.visit_statement(rhs);
        rhs.walk(visitor);
      },
      Statement::Return(expr) => for e in expr.iter_mut() {
        visitor.visit_expression(e);
        e.walk(visitor);
      },
      Statement::While{body, ..} => for b in body.iter_mut() {
        visitor.visit_statement(b);
        b.walk(visitor);
      },
    }
  }
}

impl Expression {
  pub fn walk(&mut self, visitor: &mut dyn CRelVisitor) {
    match self {
      Expression::Identifier{name} => visitor.visit_name(name),
      Expression::ConstInt(_) => (),
      Expression::ConstFloat(_) => (),
      Expression::StringLiteral(_) => (),
      Expression::Call{callee, args} => {
        visitor.visit_expression(callee);
        callee.walk(visitor);
        for arg in args.iter_mut() {
          visitor.visit_expression(arg);
          arg.walk(visitor);
        }
      },
      Expression::ASpecCall{callee, args} => {
        visitor.visit_expression(callee);
        callee.walk(visitor);
        for arg in args.iter_mut() {
          visitor.visit_expression(arg);
          arg.walk(visitor);
        }
      },
      Expression::ESpecCall{callee, args} => {
        visitor.visit_expression(callee);
        callee.walk(visitor);
        for arg in args.iter_mut() {
          visitor.visit_expression(arg);
          arg.walk(visitor);
        }
      },
      Expression::Unop{expr, ..} => {
        visitor.visit_expression(expr);
        expr.walk(visitor);
      },
      Expression::Binop{lhs, rhs, ..} => {
        visitor.visit_expression(lhs);
        lhs.walk(visitor);
        visitor.visit_expression(rhs);
        rhs.walk(visitor);
      },
      Expression::Forall{bindings, condition, ..} => {
        for (pred_var, _) in bindings {
          visitor.visit_name(pred_var);
        }
        visitor.visit_expression(condition);
        condition.walk(visitor);
      },
      Expression::Statement(stmt) => {
        visitor.visit_statement(stmt);
        stmt.walk(visitor);
      },
    }
  }
}

impl BlockItem {
  pub fn walk(&mut self, visitor: &mut dyn CRelVisitor) {
    match self {
      BlockItem::Declaration(decl) => {
        visitor.visit_declaration(decl);
        decl.walk(visitor);
      },
      BlockItem::Statement(stmt) => {
        visitor.visit_statement(stmt);
        stmt.walk(visitor);
      },
    }
  }
}
