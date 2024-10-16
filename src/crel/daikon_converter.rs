use crate::crel::ast::*;
use uuid::Uuid;

pub struct DaikonConverter {
  lh_decls: Vec<CRel>,
  cur_scope: Vec<ScopeItem>,
  cur_scope_checkpoint: u64,
  statement: Statement,
}

enum ScopeItem {
  Decl(ParameterDeclaration),
  Checkpoint(u64),
}

impl DaikonConverter {

  pub fn new(statement: Statement) -> Self {
    DaikonConverter {
      lh_decls: Vec::new(),
      cur_scope: Vec::new(),
      cur_scope_checkpoint: 0,
      statement,
    }
  }

  pub fn convert(&mut self) -> (Statement, Vec<CRel>) {
    let converted_statement = self.convert_statement(self.statement.clone());
    (converted_statement, self.lh_decls.clone())
  }

  fn add_loop_head(&mut self, name: String) -> (String, Expression) {
    let scope_vars = self.cur_scope_vars();
    let fundef = CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
      name: name.clone(),
      params: scope_vars.clone(),
      body: Box::new(Statement::None),
    };
    self.lh_decls.push(fundef.clone());

    (name.clone(), Expression::Call {
      callee: Box::new(Expression::Identifier{name}),
      args: scope_vars.iter()
        .map(|v| Expression::Identifier {
          name: v.declarator.clone().expect("Parameter without declarator").name()
        })
        .collect(),
    })
  }

  fn push_scope(&mut self) -> u64 {
    let checkpoint = self.cur_scope_checkpoint;
    self.cur_scope_checkpoint += 1;
    self.cur_scope.push(ScopeItem::Checkpoint(checkpoint));
    checkpoint
  }

  fn pop_scope(&mut self, checkpoint: u64) {
    while !self.cur_scope.is_empty() {
      match self.cur_scope.pop() {
        Some(ScopeItem::Checkpoint(popped)) if popped == checkpoint => return,
        _ => ()
      }
    }
    panic!("Checkpoint ID not in scope stack: {}", checkpoint);
  }

  fn cur_scope_vars(&self) -> Vec<ParameterDeclaration> {
    let mut decls = Vec::new();
    for item in &self.cur_scope {
      match &item {
        ScopeItem::Decl(decl) => decls.push(decl.clone()),
        _ => ()
      }
    }
    decls.sort();
    decls.dedup();
    decls
  }

  fn convert_statement(&mut self, stmt: Statement) -> Statement {
    //let stmt = stmt.clone();
    //stmt.assign_loop_ids();

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
      Statement::GuardedRepeat{id, repetitions, condition, body} => {
        let checkpoint = self.push_scope();
        let condition = Box::new(self.convert_expression(*condition.clone()));
        let body = Box::new(self.convert_statement(*body.clone()));
        self.pop_scope(checkpoint);
        Statement::GuardedRepeat {
          id: id.clone(),
          repetitions: *repetitions,
          condition,
          body,
        }
      },
      Statement::If{condition, then, els} => {
        let checkpoint = self.push_scope();
        let cthen = self.convert_statement(*then.clone());
        self.pop_scope(checkpoint);

        let checkpoint = self.push_scope();
        let cels = els.clone().map(|e| Box::new(self.convert_statement(*e)));
        self.pop_scope(checkpoint);

        Statement::If{
          condition: condition.clone(),
          then: Box::new(cthen),
          els: cels
        }
      },
      Statement::None => stmt,
      Statement::Relation{lhs, rhs} => Statement::Relation {
        lhs: Box::new(self.convert_statement(*lhs.clone())),
        rhs:Box::new(self.convert_statement(*rhs.clone())),
      },
      Statement::Return(expr) => Statement::Return(expr.clone().map(|e| {
        Box::new(self.convert_expression(*e))
      })),
      Statement::While{id, runoff_link_id, invariants: invariant, condition, body, is_runoff, is_merged} => {
        let checkpoint = self.push_scope();
        let (_, lh_call) = self.add_loop_head(loop_head_name(id));
        let new_body = match &body {
          Option::None => Statement::Expression(Box::new(lh_call)),
          Option::Some(b) => Statement::Compound(vec![
            BlockItem::Statement(Statement::Expression(Box::new(lh_call))),
            BlockItem::Statement(self.convert_statement(*b.clone()))]),
        };
        self.pop_scope(checkpoint);
        Statement::While{
          id: id.clone(),
          runoff_link_id: runoff_link_id.clone(),
          invariants: invariant.clone(),
          condition: condition.clone(),
          body: Some(Box::new(new_body)),
          is_runoff: *is_runoff,
          is_merged: *is_merged,
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
      BlockItem::Declaration(decl) => {
        let param_decl = ParameterDeclaration {
          specifiers: decl.specifiers.clone(),
          declarator: Some(decl.declarator.clone()),
        };
        self.cur_scope.push(ScopeItem::Decl(param_decl));
        item
      },
      BlockItem::Statement(stmt) => BlockItem::Statement(self.convert_statement(stmt.clone())),
    }
  }
}
