use crate::syrtos::Statement;
use crate::syrtos::Type;
use crate::syrtos::Writer;

#[derive(Clone, Debug)]
pub enum Expression {
  ArrayIndex{expr: Box<Expression>, index: Box<Expression>},
  ConstInt(i32),
  ConstFloat(f32),
  ConstTrue,
  ConstFalse,
  Identifier{name: String},
  FnCall{name: Box<Expression>, args: Vec<Expression>},
  StringLiteral(String),
  Ternary{condition: Box<Expression>, then: Box<Expression>, els: Box<Expression>},
  UnOp{expr: Box<Expression>, op: String},
  BinOp{lhs: Box<Expression>, rhs: Box<Expression>, op: String},
  Forall{bindings: Vec<(String, Type)>, condition: Box<Expression>},
  Statement(Box<Statement>),
}

impl Expression {

  pub fn emit(&self, writer: &mut Writer, subexp: bool) {
    match self {
      Expression::ArrayIndex{expr, index} => {
        expr.emit(writer, false);
        writer.write("[");
        index.emit(writer, false);
        writer.write("]");
      },
      Expression::ConstInt(i) => {
        writer.write(&i.to_string());
      },
      Expression::ConstFloat(f) => {
        writer.write(&f.to_string());
      },
      Expression::ConstTrue => {
        writer.write("true");
      },
      Expression::ConstFalse => {
        writer.write("false");
      },
      Expression::Identifier{name} => {
        writer.write(name);
      },
      Expression::FnCall{name, args} => {
        name.emit(writer, false);
        writer.write("(");
        let mut comma = false;
        for arg in args {
          if comma { writer.write(", "); }
          arg.emit(writer, false);
          comma = true;
        }
        writer.write(")");
      },
      Expression::StringLiteral(s) => {
        writer.write(s);
      },
      Expression::Ternary { condition, then, els } => {
        if subexp { writer.write("("); }
        writer.write("if ");
        condition.emit(writer, true);
        writer.write(" then ");
        then.emit(writer, true);
        writer.write(" else ");
        els.emit(writer, true);
        if subexp { writer.write(")"); }
      },
      Expression::UnOp{expr, op} => {
        if subexp { writer.write("("); }
        writer.write(op);
        expr.emit(writer, true);
        if subexp { writer.write(")"); }
      },
      Expression::BinOp{lhs, rhs, op} => {
        if subexp { writer.write("("); }
        lhs.emit(writer, true);
        writer.write(" ").write(op).write(" ");
        rhs.emit(writer, true);
        if subexp { writer.write(")"); }
      },
      Expression::Forall{bindings, condition} => {
        writer.write("forall ");
        let mut comma = "";
        for (pred_var, pred_type) in bindings {
          writer.write(comma).write(pred_var).write(": ");
          pred_type.emit(writer);
          comma = ", ";
        }
        writer.write(" :: ");
        condition.emit(writer, true);
      }
      Expression::Statement(stmt) => {
        stmt.emit(writer);
      },
    }
  }
}
