use std::borrow::BorrowMut;

use crate::crel::ast::*;

pub trait CRelVisitor {
  fn visit_crel(&mut self, crel: &mut CRel) { crel.walk(self) }
  fn visit_declarator(&mut self, decl: &mut Declarator) { decl.walk(self) }
  fn visit_declaration(&mut self, decl: &mut Declaration) { decl.walk(self) }
  fn visit_parameter_declaration(&mut self, pdecl: &mut ParameterDeclaration) { pdecl.walk(self) }
  fn visit_declaration_specifier(&mut self, spec: &mut DeclarationSpecifier) { spec.walk(self) }
  fn visit_statement(&mut self, stmt: &mut Statement) { stmt.walk(self) }
  fn visit_expression(&mut self, expr: &mut Expression) { expr.walk(self) }
  fn visit_block_item(&mut self, item: &mut BlockItem) { item.walk(self) }
  fn visit_name(&mut self, _: &mut String) { }
}

impl CRel {
  pub fn walk(&mut self, visitor: &mut dyn CRelVisitor) {
    match self {
      CRel::Declaration(decl) => visitor.visit_declaration(decl),
      CRel::FunctionDefinition{specifiers, name, params, body, ..} => {
        for spec in specifiers { visitor.visit_declaration_specifier(spec) }
        visitor.visit_name(name);
        for param in params { visitor.visit_parameter_declaration(param) }
        visitor.visit_statement(body);
      },
      CRel::Seq(stmts) => for stmt in stmts { visitor.visit_crel(stmt) }
    }
  }
}

impl Declarator {
  pub fn walk(&mut self, visitor: &mut dyn CRelVisitor) {
    match self {
      Declarator::Identifier{name} => visitor.visit_name(name),
      Declarator::Array{name, sizes} => {
        visitor.visit_name(name);
        for expr in sizes { visitor.visit_expression(expr) }
      },
      Declarator::Function{name, params} => {
        visitor.visit_name(name);
        for param in params { visitor.visit_parameter_declaration(param) }
      },
      Declarator::Pointer(decl) => visitor.visit_declarator(decl),
    }
  }
}

impl Declaration {
  pub fn walk(&mut self, visitor: &mut dyn CRelVisitor) {
    for spec in self.specifiers.iter_mut() { visitor.visit_declaration_specifier(spec) }
    visitor.visit_declarator(self.declarator.borrow_mut());
    for init in self.initializer.iter_mut() { visitor.visit_expression(init) }
  }
}

impl ParameterDeclaration {
  pub fn walk(&mut self, visitor: &mut dyn CRelVisitor) {
    for spec in self.specifiers.iter_mut() { visitor.visit_declaration_specifier(spec) }
    for decl in self.declarator.iter_mut() { visitor.visit_declarator(decl) }
  }
}

impl Statement {
  pub fn walk(&mut self, visitor: &mut dyn CRelVisitor) {
    match self {
      Statement::BasicBlock(items) => for item in items { visitor.visit_block_item(item) },
      Statement::Break => (),
      Statement::Compound(items) => for item in items { visitor.visit_block_item(item) },
      Statement::Expression(expr) => visitor.visit_expression(expr),
      Statement::If{then, els, ..} => {
        visitor.visit_statement(then);
        for e in els.iter_mut() { visitor.visit_statement(e) }
      },
      Statement::None => (),
      Statement::Relation{lhs, rhs} => {
        visitor.visit_statement(lhs);
        visitor.visit_statement(rhs);
      },
      Statement::Return(expr) => for e in expr.iter_mut() { visitor.visit_expression(e) },
      Statement::While{body, ..} => for b in body.iter_mut() { visitor.visit_statement(b) },
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
        for arg in args.iter_mut() { visitor.visit_expression(arg) }
      },
      Expression::Unop{expr, ..} => visitor.visit_expression(expr),
      Expression::Binop{lhs, rhs, ..} => {
        visitor.visit_expression(lhs);
        visitor.visit_expression(rhs);
      },
      Expression::Forall{pred_var, condition, ..} => {
        visitor.visit_name(pred_var);
        visitor.visit_expression(condition);
      },
      Expression::Statement(stmt) => visitor.visit_statement(stmt),
    }
  }
}

impl BlockItem {
  pub fn walk(&mut self, visitor: &mut dyn CRelVisitor) {
    match self {
      BlockItem::Declaration(decl) => visitor.visit_declaration(decl),
      BlockItem::Statement(stmt) => visitor.visit_statement(stmt),
    }
  }
}
