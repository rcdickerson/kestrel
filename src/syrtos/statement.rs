use crate::syrtos::Expression;
use crate::syrtos::Variable;
use crate::syrtos::Writer;

#[derive(Clone, Debug)]
pub enum Statement {
  Break,
  Expression(Box<Expression>),
  If {
    condition: Box<Expression>,
    then: Box<Statement>,
    els: Option<Box<Statement>>
  },
  Return(Option<Box<Expression>>),
  Seq(Vec<Statement>),
  Variable(Variable),
  While {
    loop_id: Option<String>,
    condition: Box<Expression>,
    invariants: Option<Vec<Expression>>,
    body: Option<Box<Statement>>,
  }
}

impl Statement {

  pub fn emit(&self, writer: &mut Writer) {
    match self {
      Statement::Break => {
        writer.write_line("break;");
      },
      Statement::Expression(expr) => {
        expr.emit(writer, false);
        writer.write(";").new_line();
      },
      Statement::If{condition, then, els} => {
        writer.write("if (");
        condition.emit(writer, false);
        writer.write(") {").new_line();
        writer.indent();
        then.emit(writer);
        writer.dedent();
        writer.write("}");
        match els {
          None => { writer.new_line(); },
          Some(else_stmt) => {
            writer.write(" else {");
            writer.indent();
            else_stmt.emit(writer);
            writer.dedent();
            writer.write("}").new_line();
          }
        }
      },
      Statement::Return(opt_expr) => {
        match opt_expr {
          None => { writer.write_line("return;"); },
          Some(expr) => {
            writer.write("return ");
            expr.emit(writer, false);
            writer.write(";").new_line();
          }
        }
      },
      Statement::Seq(stmts) => {
        for stmt in stmts { stmt.emit(writer); }
      },
      Statement::Variable(var) => {
        var.emit(writer);
        writer.write(";").new_line();
      },
      Statement::While{loop_id, condition, invariants, body} => {
        writer.write("while (");
        let start_line = writer.cur_line();
        condition.emit(writer, false);
        match invariants {
          None => {
            writer.write(") {").new_line();
          },
          Some(invars) => {
            writer.write(")").new_line();
            writer.indent();
            for invar in invars {
              writer.write("invariant ");
              invar.emit(writer, false);
              writer.new_line();
            }
            writer.dedent();
            writer.write("{").new_line();
          },
        }
        writer.indent();
        match body {
          None => (),
          Some(stmt) => { stmt.emit(writer); }
        }
        writer.dedent();
        loop_id.as_ref().map(|id| {
          writer.tag_while(id.clone(), start_line, writer.cur_line())
        });
        writer.write("}").new_line();
      }
    }
  }
}
