use crate::crel::ast::*;
use std::collections::HashMap;

pub type State = HashMap<String, i32>;

pub fn state(mapping: Vec<(&str, i32)>) -> State {
  let mut st = HashMap::new();
  for (name, val) in mapping { st.insert(name.to_string(), val); }
  st
}

#[derive(Clone, Debug, PartialEq)]
pub enum Tag {
  LoopStart,
  LoopHead,
  LoopEnd,
  RelationStart,
  RelationEnd,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TraceItem {
  Tag(Tag),
  State(State),
}

pub type Trace = Vec<TraceItem>;

#[derive(Clone, Debug, PartialEq)]
pub enum Result {
  Int(i32),
  Identifier(String, Option<i32>),
  Return(i32),
  Break,
  None,
  OutOfFuel,
}

pub struct Execution {
  current_state: Option<State>,
  trace: Trace,
  result: Result,
  max_trace: usize,
}
impl Execution {

  fn new(max_trace: usize) -> Self {
    Execution {
      current_state: None,
      trace: vec!{},
      result: Result::None,
      max_trace,
    }
  }

  fn set_state(&mut self, state: State) {
    if self.trace.len() >= self.max_trace {
      self.result = Result::OutOfFuel;
      return;
    }
    self.trace.push(TraceItem::State(state.clone()));
    self.current_state = Some(state);
  }

  fn update_state(&mut self, id: String, value: i32) {
    if self.trace.len() >= self.max_trace {
      self.result = Result::OutOfFuel;
      return;
    }
    let mut new_state = match &self.current_state {
      None => HashMap::new(),
      Some(state) => state.clone(),
    };
    new_state.insert(id, value);
    self.trace.push(TraceItem::State(new_state.clone()));
    self.current_state = Some(new_state);
  }

  fn push_tag(&mut self, tag: Tag) {
    if self.trace.len() >= self.max_trace {
      self.result = Result::OutOfFuel;
      return;
    }
    self.trace.push(TraceItem::Tag(tag));
  }

  fn current_state(&self) -> State {
    match &self.current_state {
      None => panic!("No current state"),
      Some(state) => state.clone(),
    }
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
      None => None,
      Some(i) => Some(*i),
    };
    self.result = Result::Identifier(id, value);
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
      Result::Identifier(_, Some(val)) => val != 0,
      _ => false,
    }
  }

  fn result_false(&self) -> bool {
    match self.result {
      Result::Int(val) => val == 0,
      Result::Identifier(_, Some(val)) => val == 0,
      _ => false,
    }
  }

  fn result_int(&self) -> i32 {
    match self.result {
      Result::Int(i) => i,
      Result::Identifier(_, Some(val)) => val,
      Result::OutOfFuel => 0,
      _ => panic!("Result not an int: {:?}", self.result),
    }
  }

  fn result_identifier(&self) -> String {
    match self.result.clone() {
      Result::Identifier(id, _) => id,
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

pub fn run(stmt: &Statement, state: State, max_trace: usize) -> Trace {
  let mut exec = Execution::new(max_trace);
  exec.set_state(state);
  eval_statement(stmt, &mut exec);
  exec.trace
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
      eval_expression(condition, exec);
      exec.push_tag(Tag::LoopStart);
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
      panic!("Function calls unimplemented")
    },
    Expression::Unop {expr, op} => eval_unop(expr, op, exec),
    Expression::Binop {lhs, rhs, op} => eval_binop(lhs, rhs, op, exec),
    Expression::Statement(stmt) => eval_statement(stmt, exec),
  }
}

fn eval_unop(expr: &Expression, op: &UnaryOp, exec: &mut Execution) {
  eval_expression(expr, exec);
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
  match op {
    BinaryOp::Add => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
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
      let id = exec.result_identifier();
      eval_expression(rhs, exec);
      exec.update_state(id, exec.result_int());
    },
    BinaryOp::Sub => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      exec.set_value(lhs_val - exec.result_int());
    },
    BinaryOp::Div => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      exec.set_value(lhs_val / exec.result_int());
    },
    BinaryOp::Equals => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      exec.set_bool(lhs_val == exec.result_int());
    },
    BinaryOp::Gt => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      exec.set_bool(lhs_val > exec.result_int());
    },
    BinaryOp::Gte => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      exec.set_bool(lhs_val >= exec.result_int());
    },
    BinaryOp::Index => panic!("unsupported"),
    BinaryOp::Lt => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      exec.set_bool(lhs_val < exec.result_int());
    },
    BinaryOp::Lte => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      exec.set_bool(lhs_val <= exec.result_int());
    },
    BinaryOp::Mod => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      exec.set_value(lhs_val % exec.result_int());
    },
    BinaryOp::Mul => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
      exec.set_value(lhs_val * exec.result_int());
    },
    BinaryOp::NotEquals => {
      let lhs_val = exec.result_int();
      eval_expression(rhs, exec);
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
  for init_decl in &decl.declarators {
    let name = match &init_decl.declarator {
      Declarator::Identifier{name} => name,
    };
    match &init_decl.expression {
      None => exec.update_state(name.clone(), 0),
      Some(expr) => {
        eval_expression(&expr, exec);
        exec.update_state(name.clone(), exec.result_int())
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
      "int main() {
         int x = 0;
         int y = 5;
         x = x + 1;
         y = x + y;
       }".to_string());
    let expected = vec!{
      TraceItem::State(HashMap::new()),
      TraceItem::State(state(vec!(("x", 0)))),
      TraceItem::State(state(vec!(("x", 0), ("y", 5)))),
      TraceItem::State(state(vec!(("x", 1), ("y", 5)))),
      TraceItem::State(state(vec!(("x", 1), ("y", 6)))),
    };
    assert_eq!(expected, run(&body(prog), HashMap::new(), 100));
  }

  #[test]
  fn test_run_conditional() {
    let prog = parse_c_string(
      "int main() {
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
    let expected = vec!{
      TraceItem::State(HashMap::new()),
      TraceItem::State(state(vec!(("x", 0)))),
      TraceItem::State(state(vec!(("x", 0),   ("y", 0)))),
      TraceItem::State(state(vec!(("x", 0),   ("y", 1)))),
      TraceItem::State(state(vec!(("x", 100), ("y", 1)))),
    };
    assert_eq!(expected, run(&body(prog), HashMap::new(), 100));
  }

  #[test]
  fn test_run_loop() {
    let prog = parse_c_string(
      "int main() {
         int x = 0;
         int y = 5;
         while (x < y) {
           x = x + 1;
           y = y - 1;
         }
         int z = 100;
       }".to_string());
    let expected = vec!{
      TraceItem::State(HashMap::new()),
      TraceItem::State(state(vec!(("x", 0)))),
      TraceItem::State(state(vec!(("x", 0), ("y", 5)))),
      TraceItem::Tag(Tag::LoopStart),
      TraceItem::Tag(Tag::LoopHead),
      TraceItem::State(state(vec!(("x", 1), ("y", 5)))),
      TraceItem::State(state(vec!(("x", 1), ("y", 4)))),
      TraceItem::Tag(Tag::LoopHead),
      TraceItem::State(state(vec!(("x", 2), ("y", 4)))),
      TraceItem::State(state(vec!(("x", 2), ("y", 3)))),
      TraceItem::Tag(Tag::LoopHead),
      TraceItem::State(state(vec!(("x", 3), ("y", 3)))),
      TraceItem::State(state(vec!(("x", 3), ("y", 2)))),
      TraceItem::Tag(Tag::LoopEnd),
      TraceItem::State(state(vec!(("x", 3), ("y", 2), ("z", 100)))),
    };
    assert_eq!(expected, run(&body(prog), HashMap::new(), 100));
  }

  #[test]
  fn test_run_loop_break() {
    let prog = parse_c_string(
      "int main() {
         int x = 0;
         int y = 5;
         while (x < y) {
           x = x + 1;
           break;
           y = y - 1;
         }
         int z = 100;
       }".to_string());
    let expected = vec!{
      TraceItem::State(HashMap::new()),
      TraceItem::State(state(vec!(("x", 0)))),
      TraceItem::State(state(vec!(("x", 0), ("y", 5)))),
      TraceItem::Tag(Tag::LoopStart),
      TraceItem::Tag(Tag::LoopHead),
      TraceItem::State(state(vec!(("x", 1), ("y", 5)))),
      TraceItem::Tag(Tag::LoopEnd),
      TraceItem::State(state(vec!(("x", 1), ("y", 5), ("z", 100)))),
    };
    assert_eq!(expected, run(&body(prog), HashMap::new(), 100));
  }

  #[test]
  fn test_run_loop_fuel() {
    let prog = parse_c_string(
      "int main() {
         int x = 0;
         while (1) {
           x = x + 1;
         }
       }".to_string());
    let expected = vec!{
      TraceItem::State(HashMap::new()),
      TraceItem::State(state(vec!(("x", 0)))),
      TraceItem::Tag(Tag::LoopStart),
      TraceItem::Tag(Tag::LoopHead),
      TraceItem::State(state(vec!(("x", 1)))),
      TraceItem::Tag(Tag::LoopHead),
      TraceItem::State(state(vec!(("x", 2)))),
      TraceItem::Tag(Tag::LoopHead),
      TraceItem::State(state(vec!(("x", 3)))),
    };
    assert_eq!(expected, run(&body(prog), HashMap::new(), 9));
  }

  fn body(crel: CRel) -> Statement {
    match crel {
      CRel::FunctionDefinition{specifiers:_, name:_, params:_, body} => *body,
      CRel::Seq(crels) if crels.len() > 0 => body(crels[0].clone()),
      _ => panic!("Expected function definition, got: {:?}", crel),
    }
  }
}
