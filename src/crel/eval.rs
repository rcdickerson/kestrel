use crate::crel::ast::*;
use crate::crel::state::*;
use crate::crel::trace::*;

#[derive(Clone, Debug, PartialEq)]
pub enum Result {
  Int(i32),
  Identifier {
    name: String,
    index: Option<usize>,
    value: Option<i32>
  },
  Return(i32),
  Break,
  None,
  OutOfFuel,
}

pub struct Execution {
  current_state: Option<State>,
  pub trace: Trace,
  result: Result,
  max_trace: usize,
}

impl Execution {

  fn new(max_trace: usize) -> Self {
    Execution {
      current_state: None,
      trace: Trace::new(),
      result: Result::None,
      max_trace,
    }
  }

  pub fn current_state(&self) -> State {
    match &self.current_state {
      None => panic!("No current state"),
      Some(state) => state.clone(),
    }
  }

  fn set_state(&mut self, state: State) {
    if self.trace.len() >= self.max_trace {
      self.result = Result::OutOfFuel;
      return;
    }
    self.trace.push_state(state.clone());
    self.current_state = Some(state);
  }

  fn update_state(&mut self, id: String, index: Option<usize>, value: i32) {
    if self.trace.len() >= self.max_trace {
      self.result = Result::OutOfFuel;
      return;
    }
    let mut new_state = match &self.current_state {
      None => State::new(),
      Some(state) => state.clone(),
    };
    match index {
      None => new_state.put(id, value),
      Some(index) => new_state.put_indexed(id, index, value),
    };
    self.trace.push_state(new_state.clone());
    self.current_state = Some(new_state);
  }

  fn push_tag(&mut self, tag: Tag) {
    if self.trace.len() >= self.max_trace {
      self.result = Result::OutOfFuel;
      return;
    }
    self.trace.push_tag(tag);
  }

  fn set_break(&mut self) {
    if self.result == Result::OutOfFuel { return }
    self.result = Result::Break;
  }

  fn set_return(&mut self, value: i32) {
    if self.result == Result::OutOfFuel { return }
    self.result = Result::Return(value);
  }

  fn set_value(&mut self, value: i32) {
    if self.result == Result::OutOfFuel { return }
    self.result = Result::Int(value);
  }

  fn set_bool(&mut self, value: bool) {
    if self.result == Result::OutOfFuel { return }
    if value {
      self.set_value(1)
    } else {
      self.set_value(0)
    }
  }

  fn set_identifier(&mut self, id: String) {
    if self.result == Result::OutOfFuel { return }
    let value = match self.current_state().get(&id) {
      Some(StateValue::Int(i)) => Some(*i),
      _ => None,
    };
    self.result = Result::Identifier{name: id, index: None, value};
  }

  fn set_array_index(&mut self, id: String, index: usize) {
    if self.result == Result::OutOfFuel { return }
    let value = match self.current_state().get(&id) {
      None => panic!("Array not found: {}", id),
      Some(StateValue::Array(arr)) => arr[index].int(),
      _ => panic!("Not an array: {}", id),
    };
    self.result = Result::Identifier {
      name: id,
      index: Some(index),
      value: Some(value)
    };
  }

  fn clear_break(&mut self) {
    match self.result {
      Result::Break => self.result = Result::None,
      _ => ()
    }
  }

  fn result_true(&self) -> bool {
    match self.result {
      Result::Int(val) => val != 0,
      Result::Identifier{name:_, index:_, value: Some(val)} => val != 0,
      _ => false,
    }
  }

  fn result_false(&self) -> bool {
    match self.result {
      Result::Int(val) => val == 0,
      Result::Identifier{name:_, index:_, value: Some(val)} => val == 0,
      _ => false,
    }
  }

  pub fn result_int(&self) -> i32 {
    match self.result {
      Result::Int(i) => i,
      Result::Identifier{name:_, index:_, value: Some(val)} => val,
      Result::OutOfFuel => 0,
      _ => panic!("Result not an int: {:?}", self.result),
    }
  }

  fn result_identifier(&self) -> (String, Option<usize>) {
    match self.result.clone() {
      Result::Identifier{name, index, value:_} => (name, index),
      _ => panic!("Result not an identifier: {:?}", self.result),
    }
  }

  fn ended(&self) -> bool {
    match self.result {
      Result::Return(_) => true,
      Result::Break => true,
      Result::OutOfFuel => true,
      _ => false,
    }
  }
}

pub fn run(stmt: &Statement, state: State, max_trace: usize) -> Execution {
  let mut exec = Execution::new(max_trace);
  exec.set_state(state);
  eval_statement(stmt, &mut exec);
  exec
}

fn eval_statement(stmt: &Statement, exec: &mut Execution) {
  match stmt {
    Statement::BasicBlock(items) => {
      for item in items {
        eval_block_item(item, exec);
        if exec.ended() { break };
      }
    },
    Statement::Break => exec.set_break(),
    Statement::Compound(items) => {
      for item in items {
        eval_block_item(item, exec);
        if exec.ended() { break };
      }
    },
    Statement::Expression(expr) => {
      eval_expression(expr, exec);
    },
    Statement::If{condition, then, els} => {
      eval_expression(condition, exec);
      if exec.result_true() {
        eval_statement(then, exec)
      } else if exec.result_false() {
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
        None => exec.set_return(0),
        Some(expr) => {
          eval_expression(expr, exec);
          exec.set_return(exec.result_int());
        }
      }
    },
    Statement::While{condition, body} => {
      exec.push_tag(Tag::LoopStart);
      eval_expression(condition, exec);
      while exec.result_true() {
        match body {
          None => (),
          Some(stmt) => {
            exec.push_tag(Tag::LoopHead);
            if exec.ended() {
              exec.clear_break();
              break;
            }
            eval_statement(stmt, exec);
            if exec.ended() {
              exec.clear_break();
              break;
            }
            eval_expression(condition, exec);
            if exec.ended() {
              exec.clear_break();
              break;
            }
          }
        }
      }
      exec.push_tag(Tag::LoopEnd);
    },
  }
}

fn eval_expression(expr: &Expression, exec: &mut Execution) {
  match expr {
    Expression::Identifier{name} => {
      exec.set_identifier(name.clone());
    },
    Expression::ConstInt(i) => {
      exec.set_value(*i);
    },
    Expression::StringLiteral(_) => (),
    Expression::Call{callee: _, args: _} => {
      ()
      // panic!("Function calls unimplemented")
    },
    Expression::Unop {expr, op} => eval_unop(expr, op, exec),
    Expression::Binop {lhs, rhs, op} => eval_binop(lhs, rhs, op, exec),
    Expression::Statement(stmt) => eval_statement(stmt, exec),
  }
}

fn eval_unop(expr: &Expression, op: &UnaryOp, exec: &mut Execution) {
  eval_expression(expr, exec);
  if exec.ended() { return; }
  match op {
    UnaryOp::Minus => exec.set_value(-1 * exec.result_int()),
    UnaryOp::Not => {
      if exec.result_true() {
        exec.set_value(0);
      } else {
        exec.set_value(1);
      }
    },
  }
}

fn eval_binop(lhs: &Expression, rhs: &Expression, op: &BinaryOp, exec: &mut Execution) {
  eval_expression(lhs, exec);
  if exec.ended() { return; }
  match op {
    BinaryOp::Add => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      if exec.ended() { return; }
      exec.set_value(lhs_val + exec.result_int());
    },
    BinaryOp::And => {
      if exec.result_false() {
        exec.set_value(0);
      } else {
        eval_expression(rhs, exec);
      }
    },
    BinaryOp::Assign => {
      let (id, index) = exec.result_identifier();
      eval_expression(rhs, exec);
      if exec.ended() { return; }
      exec.update_state(id, index, exec.result_int());
    },
    BinaryOp::Sub => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      if exec.ended() { return; }
      exec.set_value(lhs_val - exec.result_int());
    },
    BinaryOp::Div => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      if exec.ended() { return; }
      exec.set_value(lhs_val / exec.result_int());
    },
    BinaryOp::Equals => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      if exec.ended() { return; }
      exec.set_bool(lhs_val == exec.result_int());
    },
    BinaryOp::Gt => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      if exec.ended() { return; }
      exec.set_bool(lhs_val > exec.result_int());
    },
    BinaryOp::Gte => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      if exec.ended() { return; }
      exec.set_bool(lhs_val >= exec.result_int());
    },
    BinaryOp::Index => {
      let (id, _) = exec.result_identifier(); // TODO: matrices.
      eval_expression(rhs, exec);
      if exec.ended() { return; }
      exec.set_array_index(id, exec.result_int() as usize);
    }
    BinaryOp::Lt => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      if exec.ended() { return; }
      exec.set_bool(lhs_val < exec.result_int());
    },
    BinaryOp::Lte => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      if exec.ended() { return; }
      exec.set_bool(lhs_val <= exec.result_int());
    },
    BinaryOp::Mod => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      if exec.ended() { return; }
      exec.set_value(lhs_val % exec.result_int());
    },
    BinaryOp::Mul => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      if exec.ended() { return; }
      exec.set_value(lhs_val * exec.result_int());
    },
    BinaryOp::NotEquals => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      if exec.ended() { return; }
      exec.set_bool(lhs_val != exec.result_int());
    },
    BinaryOp::Or => {
      if exec.result_true() {
        exec.set_value(1);
      } else {
        eval_expression(rhs, exec);
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
  fn find_name(decl: &Declarator) -> String {
    match decl {
      Declarator::Identifier{name} => name.clone(),
      Declarator::Array{name, size:_} => name.clone(),
      Declarator::Function{name, params:_} => name.clone(),
      Declarator::Pointer(decl) => find_name(decl),
    }
  }

  for init_decl in &decl.declarators {
    let name = find_name(&init_decl.declarator);
    match &init_decl.expression {
      None => exec.update_state(name.clone(), None, 0), // TODO: arrays
      Some(expr) => {
        eval_expression(&expr, exec);
        if exec.ended() { return; }
        exec.update_state(name.clone(), None, exec.result_int()) // TODO: arrays
      }
    }
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
    let mut expected = Trace::new();
    expected.push_state(State::new());
    expected.push_state(state(vec!(("x", 0))));
    expected.push_state(state(vec!(("x", 0), ("y", 5))));
    expected.push_state(state(vec!(("x", 1), ("y", 5))));
    expected.push_state(state(vec!(("x", 1), ("y", 6))));
    assert_eq!(expected, run(&body(prog), State::new(), 100).trace);
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
    let mut expected = Trace::new();
    expected.push_state(State::new());
    expected.push_state(state(vec!(("x", 0))));
    expected.push_state(state(vec!(("x", 0),   ("y", 0))));
    expected.push_state(state(vec!(("x", 0),   ("y", 1))));
    expected.push_state(state(vec!(("x", 100), ("y", 1))));
    assert_eq!(expected, run(&body(prog), State::new(), 100).trace);
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
    expected.push_state(State::new());
    expected.push_state(state(vec!(("x", 0))));
    expected.push_state(state(vec!(("x", 0), ("y", 5))));
    expected.push_tag(Tag::LoopStart);
    expected.push_tag(Tag::LoopHead);
    expected.push_state(state(vec!(("x", 1), ("y", 5))));
    expected.push_state(state(vec!(("x", 1), ("y", 4))));
    expected.push_tag(Tag::LoopHead);
    expected.push_state(state(vec!(("x", 2), ("y", 4))));
    expected.push_state(state(vec!(("x", 2), ("y", 3))));
    expected.push_tag(Tag::LoopHead);
    expected.push_state(state(vec!(("x", 3), ("y", 3))));
    expected.push_state(state(vec!(("x", 3), ("y", 2))));
    expected.push_tag(Tag::LoopEnd);
    expected.push_state(state(vec!(("x", 3), ("y", 2), ("z", 100))));
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
    expected.push_state(State::new());
    expected.push_state(state(vec!(("x", 0))));
    expected.push_state(state(vec!(("x", 0), ("y", 5))));
    expected.push_tag(Tag::LoopStart);
    expected.push_tag(Tag::LoopHead);
    expected.push_state(state(vec!(("x", 1), ("y", 5))));
    expected.push_tag(Tag::LoopEnd);
    expected.push_state(state(vec!(("x", 1), ("y", 5), ("z", 100))));
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
    expected.push_state(State::new());
    expected.push_state(state(vec!(("x", 0))));
    expected.push_tag(Tag::LoopStart);
    expected.push_tag(Tag::LoopHead);
    expected.push_state(state(vec!(("x", 1))));
    expected.push_tag(Tag::LoopHead);
    expected.push_state(state(vec!(("x", 2))));
    expected.push_tag(Tag::LoopHead);
    expected.push_state(state(vec!(("x", 3))));
    assert_eq!(expected, run(&body(prog), State::new(), 9).trace);
  }

  fn body(crel: CRel) -> Statement {
    match crel {
      CRel::FunctionDefinition{specifiers:_, declarator:_, body} => *body,
      CRel::Seq(crels) if crels.len() > 0 => body(crels[0].clone()),
      _ => panic!("Expected function definition, got: {:?}", crel),
    }
  }
}
