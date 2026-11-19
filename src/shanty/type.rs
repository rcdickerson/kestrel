use crate::shanty::Variable;
use crate::shanty::Writer;

#[derive(Clone, Debug)]
pub enum Type {
  Bool,
  Char,
  Double,
  Float,
  Int,
  Long,
  Short,
  Signed,
  Struct{name: String, fields: Option<Vec<Variable>>},
  Unsigned,
  Void,
}

impl Type {
  pub fn emit(&self, writer: &mut Writer) {
    let type_str = match self {
      Type::Struct{name, fields} => {
        writer.write("struct ").write(name);
        if let Some(fields) = fields {
          writer.write(" {");
          for field in fields {
            writer.write(" ");
            field.emit(writer);
            writer.write(";");
          }
          writer.write(" }");
        }
        return;
      },
      Type::Bool     => "bool",
      Type::Char     => "char",
      Type::Double   => "double",
      Type::Float    => "float",
      Type::Int      => "int",
      Type::Long     => "long",
      Type::Short    => "short",
      Type::Signed   => "signed",
      Type::Unsigned => "unsigned",
      Type::Void     => "void",
    };
    writer.write(type_str);
  }
}

#[derive(Clone, Debug)]
pub enum TypeQualifier {
  Const,
}
