use crate::shanty::FunctionParameter;
use crate::shanty::Statement;
use crate::shanty::Type;

#[derive(Clone, Debug)]
pub struct Function {
  name: String,
  ty: Type,
  parameters: Vec<FunctionParameter>,
  body: Option<Statement>,
  is_extern: bool,
}

impl Function {

  pub fn new(name: &str, ty: Type) -> Self {
    Function{
      name: name.to_string(),
      ty,
      parameters: Vec::new(),
      body: None,
      is_extern: false,
    }
  }

  pub fn push_param(&mut self, param: &FunctionParameter) -> &Self {
    self.parameters.push(param.clone());
    self
  }

  pub fn set_extern(&mut self, is_extern: bool) -> &Self {
    self.is_extern = is_extern;
    self
  }

  pub fn set_body(&mut self, body: &Statement) -> &Self {
    self.body = Some(body.clone());
    self
  }
}
