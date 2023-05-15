use crate::shanty::Type;

#[derive(Clone, Debug)]
pub struct FunctionParameter {
  name: String,
  ty: Type,
}

impl FunctionParameter {

  pub fn new(name: &str, ty: Type) -> Self {
    FunctionParameter{name: name.to_string(), ty}
  }
}
