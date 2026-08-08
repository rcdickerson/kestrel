use crate::shanty::Writer;

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
  Bool,
  Char,
  Double,
  Float,
  Int,
  Long,
  Short,
  Signed,
  Unsigned,
  Void,
}

impl Type {
  pub fn emit(&self, writer: &mut Writer) {
    let type_str = match self {
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
