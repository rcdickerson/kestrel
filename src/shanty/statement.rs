use crate::shanty::Expression;
use crate::shanty::Variable;

#[derive(Clone, Debug)]
pub enum Statement {
  Break,
  Expression(Box<Expression>),
  If {
    condition: Box<Expression>,
    then: Box<Statement>,
    els: Option<Box<Statement>>
  },
  Return(Option<Box<Expression>>),
  Seq(Vec<Statement>),
  Variable(Variable),
  While {
    condition: Box<Expression>,
    body: Option<Box<Statement>>,
  }
}

impl Statement {

}
