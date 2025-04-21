use crate::syrtos::Expression;
use crate::syrtos::Type;
use crate::syrtos::Writer;

#[derive(Clone, Debug)]
pub enum Initializer {
  Expression(Expression),
  Array {
    ty: Type,
    values: Vec<Initializer>
  },
}

impl Initializer {
  pub fn emit(&self, writer: &mut Writer) {
    match self {
      Initializer::Expression(expr) => expr.emit(writer, true),
      Initializer::Array{ty, values} => {
        writer.write("new ");
        ty.emit(writer);
        writer.write("[] [");
        let mut comma = "";
        for val in values {
          writer.write(comma);
          val.emit(writer);
          comma = ", ";
        }
        writer.write("]");
      }
    }
  }
}
