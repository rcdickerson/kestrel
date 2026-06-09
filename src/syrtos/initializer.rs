use crate::syrtos::Expression;
use crate::syrtos::Type;
use crate::syrtos::Writer;

#[derive(Clone, Debug)]
pub enum Initializer {
  Expression(Expression),
  Array {
    ty: Type,
    sizes: Vec<Expression>,
  },
}

impl Initializer {
  pub fn emit(&self, writer: &mut Writer) {
    match self {
      Initializer::Expression(expr) => expr.emit(writer, true),
      Initializer::Array{ty, sizes} => {
        writer.write("new ");
        ty.emit(writer);
        writer.write("[");
        let mut comma = "";
        for size in sizes {
          writer.write(comma);
          size.emit(writer, false);
          comma = ", ";
        }
        writer.write("]");
      }
    }
  }
}
