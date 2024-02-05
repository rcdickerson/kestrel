use crate::syrtos::Statement;
use crate::syrtos::Type;
use crate::syrtos::Writer;

#[derive(Clone, Debug)]
pub enum Expression {
  ArrayIndex{expr: Box<Expression>, index: Box<Expression>},
  ConstInt(i32),
  ConstFloat(f32),
  Identifier{name: String},
  FnCall{name: Box<Expression>, args: Vec<Expression>},
  StringLiteral(String),
  UnOp{expr: Box<Expression>, op: String},
  BinOp{lhs: Box<Expression>, rhs: Box<Expression>, op: String},
  Forall{pred_var: String, pred_type: Type, condition: Box<Expression>},
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
      Expression::Forall{pred_var, pred_type, condition} => {
        writer.write("forall ").write(pred_var).write(": ");
        pred_type.emit(writer);
        writer.write(" :: ");
        condition.emit(writer, true);
      }
      Expression::Statement(stmt) => {
        stmt.emit(writer);
      },
    }
  }
}
