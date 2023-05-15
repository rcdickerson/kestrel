use crate::shanty::Statement;

#[derive(Clone, Debug)]
pub enum Expression {
  ArrayIndex{expr: Box<Expression>, index: Box<Expression>},
  ConstInt(i32),
  Identifier{name: String},
  FnCall{name: Box<Expression>, args: Vec<Expression>},
  StringLiteral(String),
  UnOp{expr: Box<Expression>, op: String},
  BinOp{lhs: Box<Expression>, rhs: Box<Expression>, op: String},
  Statement(Box<Statement>),
}

impl Expression {
}
