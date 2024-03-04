use crate::crel::ast::*;

pub struct DaikonConverter {
  lh_counter: i32,
  lh_decls: Vec<CRel>,
  cur_scope: Vec<ParameterDeclaration>,
  statement: Statement,
}

impl DaikonConverter {

  pub fn new(statement: Statement) -> Self {
    DaikonConverter {
      lh_counter: 0,
      lh_decls: Vec::new(),
      cur_scope: Vec::new(),
      statement,
    }
  }

  pub fn convert(&mut self) -> (Statement, Vec<CRel>) {
    let converted_statement = self.convert_statement(self.statement.clone());
    (converted_statement, self.lh_decls.clone())
  }

  fn add_loop_head(&mut self) -> (String, CRel) {
    let name = format!("_loop_head_{}", self.lh_counter);
    let fundef = CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
      name: name.clone(),
      params: self.cur_scope.clone(),
      body: Box::new(Statement::None),
    };
    self.lh_counter += 1;
    (name, fundef)
  }

  fn convert_statement(&mut self, stmt: Statement) -> Statement {
    match &stmt {
      Statement::BasicBlock(items) => {
        Statement::BasicBlock(items.iter()
                              .map(|item| self.convert_block_item(item.clone()))
                              .collect())
      },
      Statement::Break => stmt,
      Statement::Compound(items) => {
        Statement::Compound(items.iter()
                            .map(|item| self.convert_block_item(item.clone()))
                            .collect())

      },
      Statement::Expression(expr) => {
        Statement::Expression(
          Box::new(self.convert_expression(*expr.clone())))
      },
      Statement::If{condition, then, els} => Statement::If{
        condition: condition.clone(),
        then: Box::new(self.convert_statement(*then.clone())),
        els: els.clone().map(|e| Box::new(self.convert_statement(*e))),
      },
      Statement::None => stmt,
      Statement::Relation{lhs, rhs} => Statement::Relation {
        lhs: Box::new(self.convert_statement(*lhs.clone())),
        rhs:Box::new(self.convert_statement(*rhs.clone())),
      },
      Statement::Return(expr) => Statement::Return(expr.clone().map(|e| {
        Box::new(self.convert_expression(*e))
      })),
      Statement::While{condition, body} => {
        let (loop_head, _) = self.add_loop_head();
        let loop_head_call = Statement::Expression(
          Box::new(Expression::Call {
            callee: Box::new(Expression::Identifier{name: loop_head}),
            args: Vec::new()
          }));
        let new_body = match &body {
          Option::None => loop_head_call,
          Option::Some(b) => Statement::Compound(vec![
            BlockItem::Statement(loop_head_call),
            BlockItem::Statement(self.convert_statement(*b.clone()))]),
        };
        Statement::While{
          condition: condition.clone(),
          body: Some(Box::new(new_body)),
        }
      },
    }
  }

  fn convert_expression(&mut self, expr: Expression) -> Expression {
    match expr {
      Expression::Statement(inner) => Expression::Statement(
        Box::new(self.convert_statement(*inner))),
      _ => expr,
    }
  }

  fn convert_block_item(&mut self, item: BlockItem) -> BlockItem {
    match &item {
      BlockItem::Declaration(_)  => item,
      BlockItem::Statement(stmt) => BlockItem::Statement(self.convert_statement(stmt.clone())),
    }
  }
}
