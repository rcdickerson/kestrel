use crate::escher::FunctionParameter;
use crate::escher::Statement;
use crate::escher::Type;
use crate::escher::Writer;

#[derive(Clone, Debug)]
pub struct Function {
  name: String,
  ty: Type,
  parameters: Vec<FunctionParameter>,
  body: Option<Statement>,
  is_harness: bool,
}

impl Function {

  pub fn new(name: &str, ty: Type) -> Self {
    Function{
      name: name.to_string(),
      ty,
      parameters: Vec::new(),
      body: None,
      is_harness: false,
    }
  }

  pub fn push_param(&mut self, param: &FunctionParameter) -> &Self {
    self.parameters.push(param.clone());
    self
  }

  pub fn set_harness(&mut self, is_harness: bool) -> &Self {
    self.is_harness = is_harness;
    self
  }

  pub fn set_body(&mut self, body: &Statement) -> &Self {
    self.body = Some(body.clone());
    self
  }

  pub fn emit(&self, writer: &mut Writer) {
    self.ty.emit(writer);
    writer.write(" ").write(&self.name).write("(");
    let mut comma = false;
    for param in &self.parameters {
      if comma { writer.write(", "); }
      param.emit(writer);
      comma = true;
    }
    writer.write(")");

    match &self.body {
      None => { writer.write(";").new_line(); },
      Some(stmt) => {
        writer.write(" {").new_line();
        writer.indent();
        stmt.emit(writer);
        writer.dedent();
        writer.write("}").new_line();
      },
    }
  }
}
