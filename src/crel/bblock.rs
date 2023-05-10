use crate::crel::ast::*;

pub trait Blockify {
  fn blockify(&self) -> Self;
}

impl Blockify for CRel {
  fn blockify(&self) -> Self {
    match self {
      CRel::Declaration{specifiers:_, declarators:_} => self.clone(),
      CRel::FunctionDefinition{specifiers, name, params, body} => {
        CRel::FunctionDefinition{
          specifiers: specifiers.clone(),
          name: name.clone(),
          params: params.clone(),
          body: Box::new(body.blockify()),
        }
      },
      CRel::Seq(_) => self.clone(),
    }
  }
}

impl Blockify for Expression {
  fn blockify(&self) -> Self {
    match self {
      Expression::Statement(stmt) => Expression::Statement(Box::new(stmt.blockify())),
      _ => self.clone(),
    }
  }
}

impl Blockify for Statement {
  fn blockify(&self) -> Self {
    match self {
      Statement::BasicBlock(_) => self.clone(),
      Statement::Break => Statement::Break,
      Statement::Compound(items) => {
        Statement::Compound(blockify_items(items))
      },
      Statement::Expression(expr) => {
        Statement::Expression(Box::new(expr.blockify()))
      },
      Statement::If{condition, then, els} => {
        Statement::If {
          condition: condition.clone(),
          then: Box::new(then.blockify()),
          els: match els {
            None => None,
            Some(stmt) => Some(Box::new(stmt.blockify()))
          }
        }
      },
      Statement::None => Statement::None,
      Statement::Relation{lhs, rhs} => {
        Statement::Relation {
          lhs: Box::new(lhs.blockify()),
          rhs: Box::new(rhs.blockify()),
        }
      },
      Statement::Return(_) => self.clone(),
      Statement::While{condition, body} => {
        Statement::While {
          condition: condition.clone(),
          body: match body {
            None => None,
            Some(stmt) => Some(Box::new(stmt.blockify())),
          }
        }
      },
    }
  }
}

fn blockify_items(items: &Vec<BlockItem>) -> Vec<BlockItem> {
  let mut blocks = vec!{};
  let mut current_block = vec!{};
  for item in items {
    match item {
      BlockItem::Declaration(_) => current_block.push(item.clone()),
      BlockItem::Statement(stmt) => match stmt.blockify() {
        Statement::BasicBlock(items) => current_block.append(&mut items.clone()),
        Statement::Break => current_block.push(BlockItem::Statement(Statement::Break)),
        Statement::Compound(items) => {
          if current_block.len() > 0 {
            blocks.push(BlockItem::Statement(Statement::BasicBlock(current_block.clone())));
            current_block = vec!{};
          }
          blocks.append(&mut items.clone())
        },
        Statement::Expression(expr) => {
          current_block.push(BlockItem::Statement(Statement::Expression(expr)))
        },
        Statement::If{condition, then, els} => {
          if current_block.len() > 0 {
            blocks.push(BlockItem::Statement(Statement::BasicBlock(current_block.clone())));
            current_block = vec!{};
          }
          blocks.push(BlockItem::Statement(Statement::If{condition, then, els}))
        },
        Statement::None => current_block.push(item.clone()),
        Statement::Relation{lhs, rhs} => {
          if current_block.len() > 0 {
            blocks.push(BlockItem::Statement(Statement::BasicBlock(current_block.clone())));
            current_block = vec!{};
          }
          blocks.push(BlockItem::Statement(Statement::Relation{lhs, rhs}))
        },
        Statement::Return(expr) => {
          current_block.push(BlockItem::Statement(Statement::Return(expr)))
        },
        Statement::While{condition, body} => {
          if current_block.len() > 0 {
            blocks.push(BlockItem::Statement(Statement::BasicBlock(current_block.clone())));
            current_block = vec!{};
          }
          blocks.push(BlockItem::Statement(Statement::While{condition, body}))
        },
      },
    }
  };
  if current_block.len() > 0 {
    blocks.push(BlockItem::Statement(Statement::BasicBlock(current_block.clone())))
  }
  blocks
}
