use crate::syrtos::Parameter;
use crate::syrtos::Statement;
use crate::syrtos::Type;
use crate::syrtos::Writer;

#[derive(Clone, Debug)]
pub struct Method {
  name: String,
  parameters: Vec<Parameter>,
  ret_type: Option<Type>,
  body: Option<Statement>,
}

impl Method {

  pub fn new(name: &str, ty: Option<Type>) -> Self {
    Method {
      name: name.to_string(),
      parameters: Vec::new(),
      ret_type: ty,
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
    writer.write("method ").write(&self.name).write("(");
    let mut comma = false;
    for param in &self.parameters {
      if comma { writer.write(", "); }
      param.emit(writer);
      comma = true;
    }
    writer.write(")");
    self.ret_type.as_ref().map(|ty| {
      writer.write(" returns (y: ");
      ty.emit(writer);
      writer.write(")");
    });

    match &self.body {
      None => { writer.write(";").new_line(); },
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
