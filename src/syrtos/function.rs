use crate::syrtos::Parameter;
use crate::syrtos::Statement;
use crate::syrtos::Type;
use crate::syrtos::Writer;

#[derive(Clone, Debug)]
pub struct Function {
  name: String,
  ty: Type,
  parameters: Vec<Parameter>,
  body: Option<Statement>,
}

impl Function {

  pub fn new(name: &str, ty: Type) -> Self {
    Function{
      name: name.to_string(),
      ty,
      parameters: Vec::new(),
      body: None,
    }
  }

  pub fn push_param(&mut self, param: &Parameter) -> &Self {
    self.parameters.push(param.clone());
    self
  }

  pub fn set_body(&mut self, body: &Statement) -> &Self {
    self.body = Some(body.clone());
    self
  }

  pub fn emit(&self, writer: &mut Writer) {
    writer.write("function ").write(&self.name).write("(");
    let mut comma = false;
    for param in &self.parameters {
      if comma { writer.write(", "); }
      param.emit(writer);
      comma = true;
    }
    writer.write("): ");
    self.ty.emit(writer);

    match &self.body {
      None => { writer.new_line(); },
      Some(stmt) => {
        writer.write(" {").new_line();
        writer.indent();
        stmt.emit(writer);
        writer.dedent();
        writer.write(" }").new_line();
      },
    }
  }
}
