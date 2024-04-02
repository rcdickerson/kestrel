mod execution;
mod state;
mod trace;

use crate::crel::fundef::*;
pub use execution::Execution;
pub use state::{HeapLocation, HeapValue, State};
pub use state::rand_states_satisfying;
use std::collections::HashMap;
pub use trace::Tag;
pub use trace::{Trace, TraceState, TraceStateValue};

use crate::crel::ast::*;

pub fn run<'a>(stmt: &Statement, state: State, max_trace: usize,
           fundefs: Option<&'a HashMap<String, FunDef>>) -> Execution<'a> {
  let mut exec = Execution::new(max_trace, fundefs);
  exec.push_state(state);
  eval_statement(stmt, &mut exec);
  exec
}

fn eval_statement(stmt: &Statement, exec: &mut Execution) {
  match stmt {
    Statement::BasicBlock(items) => {
      for item in items {
        eval_block_item(item, exec);
        if exec.cf_break() { break };
      }
    },
    Statement::Break => exec.set_break_flag(),
    Statement::Compound(items) => {
      for item in items {
        eval_block_item(item, exec);
        if exec.cf_break() { break };
      }
    },
    Statement::Expression(expr) => {
      eval_expression(expr, exec);
    },
    Statement::If{condition, then, els} => {
      eval_expression(condition, exec);
      if exec.value_is_true() {
        eval_statement(then, exec)
      } else if exec.value_is_false() {
        match els {
          None => (),
          Some(stmt) => eval_statement(stmt, exec),
        }
      }
    },
    Statement::None => (),
    Statement::Relation{lhs, rhs} => {
      exec.push_tag(Tag::RelationStart);
      eval_statement(lhs, exec);
      exec.push_tag(Tag::RelationMid);
      eval_statement(rhs, exec);
      exec.push_tag(Tag::RelationEnd);
    },
    Statement::Return(expr) => {
      match expr {
        None => exec.set_value(HeapValue::Int(0)),
        Some(expr) => eval_expression(expr, exec),
      }
      exec.set_return_flag();
    },
    Statement::While{condition, body, ..} => {
      exec.push_tag(Tag::LoopStart);
      eval_expression(condition, exec);
      while exec.value_is_true() {
        match body {
          None => (),
          Some(stmt) => {
            exec.push_tag(Tag::LoopHead);
            eval_statement(stmt, exec);
            if exec.cf_break() { break; }
            eval_expression(condition, exec);
            if exec.cf_break() { break; }
          }
        }
      }
      exec.clear_break_flag();
      exec.push_tag(Tag::LoopEnd);
    },
  }
}

fn eval_expression(expr: &Expression, exec: &mut Execution) {
  match expr {
    Expression::Identifier{name} => {
      exec.set_location_by_name(name);
      exec.set_value_by_name(name);
    },
    Expression::ConstInt(i) => {
      exec.set_value(HeapValue::Int(*i));
    },
    Expression::ConstFloat(f) => {
      exec.set_value(HeapValue::Float(*f));
    },
    Expression::StringLiteral(_) => (),
    Expression::Call{callee, args} => {
      let callee_name = match callee.as_ref() {
        Expression::Identifier{name} => Some(name),
        _ => None,
      };
      let test_impl = exec.fundefs.and_then(|defs| {
        callee_name.and_then(|name| defs.get(&format!("_{}", name)))
      });
      match test_impl {
        Some(fundef) => {
          let mut call_state = exec.current_state.clone();
          for (param_decl, arg) in fundef.params.iter().zip(args) {
            eval_expression(arg, exec);
            let param_name = &param_decl.declarator.as_ref()
              .expect(format!("Unnamed parameter in {}",
                              callee_name.unwrap_or(&"<unnamed function>".to_string())).as_str())
              .name().clone();
            call_state.store_var(param_name, exec.current_value());
          }
        },
        None => {
          // Compute a simple hash of arguments.
          let mut hash = 17 as u32;
          for arg in args {
            eval_expression(arg, exec);
            match exec.current_value() {
              HeapValue::Int(i) => hash = hash.wrapping_mul(37).wrapping_add(i as u32),
              HeapValue::Float(f) => hash = hash.wrapping_mul(37).wrapping_add(f.to_bits()),
            }
          }
          exec.set_value(HeapValue::Int(hash as i32));
        }
      }
    },
    Expression::Unop{expr, op} => eval_unop(expr, op, exec),
    Expression::Binop{lhs, rhs, op} => eval_binop(lhs, rhs, op, exec),
    Expression::Forall{..} => {
      //panic!("Forall unimplemented")
    }
    Expression::Statement(stmt) => eval_statement(stmt, exec),
  }
}

fn eval_unop(expr: &Expression, op: &UnaryOp, exec: &mut Execution) {
  eval_expression(expr, exec);
  if exec.ended() { return; }
  match op {
    UnaryOp::Minus => exec.negate_value(),
    UnaryOp::Not => {
      if exec.value_is_true() {
        exec.set_value(HeapValue::Int(0));
      } else {
        exec.set_value(HeapValue::Int(1));
      }
    },
  }
}

fn eval_binop(lhs: &Expression, rhs: &Expression, op: &BinaryOp, exec: &mut Execution) {
  eval_expression(lhs, exec);
  if exec.ended() { return; }
  let lhs_val = exec.current_value();

  let arith_binop = |exec: &mut Execution, op_i: fn(i32, i32) -> i32, op_f: fn(f32, f32) -> f32| {
    eval_expression(rhs, exec);
    match lhs_val {
      HeapValue::Int(lhs_i) => {
        let rhs_i = exec.value_int();
        exec.set_value(HeapValue::Int(op_i(lhs_i, rhs_i)));
      },
      HeapValue::Float(lhs_f) => {
        let rhs_f = exec.value_float();
        exec.set_value(HeapValue::Float(op_f(lhs_f, rhs_f)));
      },
    }
  };

  let bool_binop = |exec: &mut Execution, op_i: fn(i32, i32) -> bool, op_f: fn(f32, f32) -> bool| {
    eval_expression(rhs, exec);
    if exec.ended() { return; }
    let result = match lhs_val {
      HeapValue::Int(lhs_i) => {
        let rhs_i = exec.value_int();
        op_i(lhs_i, rhs_i)
      },
      HeapValue::Float(lhs_f) => {
        let rhs_f = exec.value_float();
        op_f(lhs_f, rhs_f)
      },
    };
    let result_i = if result { 1 } else { 0 };
    exec.set_value(HeapValue::Int(result_i));
  };

  match op {
    BinaryOp::Add => arith_binop(exec, |i1, i2| i1.wrapping_add(i2), |f1, f2| f1 + f2),
    BinaryOp::And => {
      if exec.value_is_false() {
        exec.set_value(HeapValue::Int(0));
      } else {
        eval_expression(rhs, exec);
        if exec.value_is_false() {
          exec.set_value(HeapValue::Int(0));
        } else {
          exec.set_value(HeapValue::Int(1));
        }
      }
    },
    BinaryOp::Assign => {
      let loc = exec.current_location();
      eval_expression(rhs, exec);
      exec.push_update(&loc, exec.current_value());
    },
    BinaryOp::Sub => arith_binop(exec, |i1, i2| i1.wrapping_sub(i2), |f1, f2| f1 - f2),
    BinaryOp::Div => arith_binop(exec, |i1, i2| i1 / i2, |f1, f2| f1 / f2),
    BinaryOp::Equals => bool_binop(exec, |i1, i2| i1 == i2, |f1, f2| f1 == f2),
    BinaryOp::Gt => bool_binop(exec, |i1, i2| i1 > i2, |f1, f2| f1 > f2),
    BinaryOp::Gte => bool_binop(exec, |i1, i2| i1 >= i2, |f1, f2| f1 >= f2),
    BinaryOp::Index => {
      let loc = exec.current_location();
      eval_expression(rhs, exec);
      let indexed_loc = HeapLocation::Offset {
        location: Box::new(loc),
        offset: exec.value_int() as usize,
      };
      exec.set_location(indexed_loc.clone());
      exec.set_value(exec.current_state.read_loc(&indexed_loc));
    }
    BinaryOp::Lt => bool_binop(exec, |i1, i2| i1 < i2, |f1, f2| f1 < f2),
    BinaryOp::Lte => bool_binop(exec, |i1, i2| i1 <= i2, |f1, f2| f1 <= f2),
    BinaryOp::Mod => arith_binop(exec, |i1, i2| i1 % i2, |f1, f2| f1 % f2),
    BinaryOp::Mul => arith_binop(exec, |i1, i2| i1.wrapping_mul(i2), |f1, f2| f1 * f2),
    BinaryOp::NotEquals => bool_binop(exec, |i1, i2| i1 != i2, |f1, f2| f1 != f2),
    BinaryOp::Or => {
      if exec.value_is_true() {
        exec.set_value(HeapValue::Int(1));
      } else {
        eval_expression(rhs, exec);
        if exec.value_is_true() {
          exec.set_value(HeapValue::Int(1));
        } else {
          exec.set_value(HeapValue::Int(0));
        }
      }
    },
  }
}

fn eval_block_item(item: &BlockItem, exec: &mut Execution) {
  match item {
    BlockItem::Declaration(decl) => eval_declaration(decl, exec),
    BlockItem::Statement(stmt) => eval_statement(stmt, exec),
  }
}

fn eval_declaration(decl: &Declaration, exec: &mut Execution) {
  match &decl.initializer {
    None => match &decl.declarator {
      Declarator::Identifier{name} => {
        exec.push_alloc(name.clone(), 1, HeapValue::Int(0));
      },
      Declarator::Array{name, sizes} => {
        let mut alloc_size = 1;
        for size in sizes {
          eval_expression(size, exec);
          alloc_size *= exec.value_int() as usize;
        }
        exec.push_alloc(name.clone(), alloc_size, HeapValue::Int(0));
      },
      Declarator::Function{name:_, params:_} => (),
      Declarator::Pointer(_) => (),
    },
    Some(expr) => match &decl.declarator {
      Declarator::Array{name:_, sizes:_} => {
        panic!("Unsupported: initializer for array.");
      }
      Declarator::Identifier{name} => {
        eval_expression(expr, exec);
        exec.push_update_by_name(name, exec.current_value());
      }
      Declarator::Function{name:_, params:_} => {
        panic!("Unsupported: initializer for function declaration.");
      },
      Declarator::Pointer(_) => {
        panic!("Unsupported: initializer for pointer.");
      },
    },
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::crel::parser::*;

  #[test]
  fn test_run_straightline() {
    let prog = parse_c_string(
      "int main(void) {
         int x = 0;
         int y = 5;
         x = x + 1;
         y = x + y;
       }".to_string());
    // let mut expected = Trace::new();
    // expected.push_state(&State::new());
    // expected.push_state(&state(vec!(("x", 0))));
    // expected.push_state(&state(vec!(("x", 0), ("y", 5))));
    // expected.push_state(&state(vec!(("x", 1), ("y", 5))));
    // expected.push_state(&state(vec!(("x", 1), ("y", 6))));
    assert_eq!(Trace::new(), run(&body(prog), State::new(), 100).trace);
  }

  #[test]
  fn test_run_conditional() {
    let prog = parse_c_string(
      "int main(void) {
         int x = 0;
         int y = 0;
         if (x) {
           y = 0;
         } else {
           y = 1;
         }
         if (y) {
           x = 100;
         } else {
           x = 5;
         }
       }".to_string());
    // let mut expected = Trace::new();
    // expected.push_state(&State::new());
    // expected.push_state(&state(vec!(("x", 0))));
    // expected.push_state(&state(vec!(("x", 0),   ("y", 0))));
    // expected.push_state(&state(vec!(("x", 0),   ("y", 1))));
    // expected.push_state(&state(vec!(("x", 100), ("y", 1))));
    assert_eq!(Trace::new(), run(&body(prog), State::new(), 100).trace);
  }

  #[test]
  fn test_run_loop() {
    let prog = parse_c_string(
      "int main(void) {
         int x = 0;
         int y = 5;
         while (x < y) {
           x = x + 1;
           y = y - 1;
         }
         int z = 100;
       }".to_string());
    let mut expected = Trace::new();
    expected.push_state(Tag::LoopStart, &state(vec!(("x", 0), ("y", 5))));
    expected.push_state(Tag::LoopHead, &state(vec!(("x", 0), ("y", 5))));
    expected.push_state(Tag::LoopHead, &state(vec!(("x", 1), ("y", 4))));
    expected.push_state(Tag::LoopHead, &state(vec!(("x", 2), ("y", 3))));
    expected.push_state(Tag::LoopEnd, &state(vec!(("x", 3), ("y", 2))));
    assert_eq!(expected, run(&body(prog), State::new(), 100).trace);
  }

  #[test]
  fn test_run_loop_break() {
    let prog = parse_c_string(
      "int main(void) {
         int x = 0;
         int y = 5;
         while (x < y) {
           x = x + 1;
           break;
           y = y - 1;
         }
         int z = 100;
       }".to_string());
    let mut expected = Trace::new();
    expected.push_state(Tag::LoopStart, &state(vec!(("x", 0), ("y", 5))));
    expected.push_state(Tag::LoopHead, &state(vec!(("x", 0), ("y", 5))));
    expected.push_state(Tag::LoopEnd, &state(vec!(("x", 1), ("y", 5))));
    assert_eq!(expected, run(&body(prog), State::new(), 100).trace);
  }

  #[test]
  fn test_run_loop_fuel() {
    let prog = parse_c_string(
      "int main(void) {
         int x = 0;
         while (1) {
           x = x + 1;
         }
       }".to_string());
    let mut expected = Trace::new();
    expected.push_state(Tag::LoopStart, &state(vec!(("x", 0))));
    expected.push_state(Tag::LoopHead, &state(vec!(("x", 0))));
    expected.push_state(Tag::LoopHead, &state(vec!(("x", 1))));
    expected.push_state(Tag::LoopHead, &state(vec!(("x", 2))));
    expected.push_state(Tag::LoopHead, &state(vec!(("x", 3))));
    assert_eq!(expected, run(&body(prog), State::new(), 5).trace);
  }

  #[test]
  fn test_run_array() {
    let prog = parse_c_string(
      "int main(void) {
         int x[3];
         int i = 0;
         while (i < 3) {
           x[i] = i;
           i = i + 1;
         }
       }".to_string());
    let mut expected = Trace::new();
    expected.push_state(Tag::LoopStart, &arr_state(vec!(("x", vec!(0, 0, 0)), ("i", vec!(0)))));
    expected.push_state(Tag::LoopHead, &arr_state(vec!(("x", vec!(0, 0, 0)), ("i", vec!(0)))));
    expected.push_state(Tag::LoopHead, &arr_state(vec!(("x", vec!(0, 0, 0)), ("i", vec!(1)))));
    expected.push_state(Tag::LoopHead, &arr_state(vec!(("x", vec!(0, 1, 0)), ("i", vec!(2)))));
    expected.push_state(Tag::LoopEnd, &arr_state(vec!(("x", vec!(0, 1, 2)), ("i", vec!(3)))));
    assert_eq!(expected, run(&body(prog), State::new(), 100).trace);
  }

  pub fn state(mapping: Vec<(&str, i32)>) -> State {
    let mut st = State::new();
    for (name, val) in mapping {
      let name = name.to_string();
      st.alloc(&name, 1, HeapValue::Int(val));
    }
    st
  }

  pub fn arr_state(mapping: Vec<(&str, Vec<i32>)>) -> State {
    let mut st = State::new();
    for (name, val) in mapping {
      let name = name.to_string();
      let loc = st.alloc(&name, val.len(), HeapValue::Int(val[0]));
      for i in 1..val.len() {
        let loc = HeapLocation::Offset{location: Box::new(loc.clone()), offset: i};
        st.store_loc(&loc, HeapValue::Int(val[i]));
      }
    }
    st
  }

  fn body(crel: CRel) -> Statement {
    match crel {
      CRel::FunctionDefinition{specifiers:_, name:_, params:_, body} => *body,
      CRel::Seq(crels) if !crels.is_empty() => body(crels[0].clone()),
      _ => panic!("Expected function definition, got: {:?}", crel),
    }
  }
}
