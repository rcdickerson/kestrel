use crate::shanty::Expression;
use crate::shanty::Writer;

#[derive(Clone, Debug)]
pub enum Initializer {
  Expression(Expression),
  List(Vec<Initializer>),
}

impl Initializer {
  pub fn emit(&self, writer: &mut Writer) {
    match self {
      Initializer::Expression(expr) => expr.emit(writer, true),
      Initializer::List(inits) => {
        writer.write("{");
        let mut comma = "";
        for init in inits {
          writer.write(comma);
          init.emit(writer);
          comma = ", ";
        }
        writer.write("}");
      },
    }
  }
}
