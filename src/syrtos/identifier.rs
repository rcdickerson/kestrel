use crate::syrtos::Expression;
use crate::syrtos::Writer;

#[derive(Clone, Debug)]
pub enum Identifier {
  Simple(String),
  Expression(Box<Expression>),
  Compound { lhs: Box<Identifier>, rhs: Box<Identifier> },
}

impl Identifier {
  pub fn simple(name: String) -> Self {
    Identifier::Simple(name)
  }

  pub fn compound(lhs: Identifier, rhs: Identifier) -> Self {
    Identifier::Compound {
      lhs: Box::new(lhs),
      rhs: Box::new(rhs)
    }
  }

  pub fn compound2(lhs: String, rhs: String) -> Self {
    Self::compound(Self::simple(lhs), Self::simple(rhs))
  }

  pub fn emit(&self, writer: &mut Writer) {
    match self {
      Identifier::Simple(name) => {
        writer.write(name);
      },
      Identifier::Expression(expr) => {
        expr.emit(writer, false);
      }
      Identifier::Compound{lhs, rhs} => {
        lhs.emit(writer);
        writer.write(".");
        rhs.emit(writer);
      },
    }
  }
}
