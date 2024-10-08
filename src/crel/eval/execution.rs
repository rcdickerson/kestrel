use crate::crel::eval::*;
use crate::crel::eval::state::VarRead;
use crate::crel::fundef::*;
use std::collections::HashMap;

pub struct Execution<'a> {
  pub current_state: State,
  pub trace: Trace,
  max_trace_size: usize,
  flag_break: bool,
  flag_return: bool,
  flag_out_of_fuel: bool,
  reg_location: HeapLocation,
  reg_value: HeapValue,
  pub fundefs: Option<&'a HashMap<String, FunDef>>,
}

impl <'a> Execution<'a> {

  pub fn new(max_trace_size: usize, fundefs: Option<&'a HashMap<String, FunDef>>) -> Self {
    Execution {
      current_state: State::new(),
      trace: Trace::new(),
      max_trace_size,
      flag_break: false,
      flag_return: false,
      flag_out_of_fuel: false,
      reg_location: HeapLocation::Pointer(0),
      reg_value: HeapValue::Int(0),
      fundefs
    }
  }

  pub fn push_state(&mut self, state: State) {
    if self.trace.len() >= self.max_trace_size {
      self.flag_out_of_fuel = true;
      return;
    }
    self.current_state = state;
  }

  pub fn push_alloc(&mut self, name: String, size: usize, value: HeapValue) -> HeapLocation {
    let loc = self.current_state.alloc(&name, size, value);
    if self.trace.len() >= self.max_trace_size {
      self.flag_out_of_fuel = true;
      return loc;
    }
    loc
  }

  pub fn push_update(&mut self, location: &HeapLocation, value: HeapValue) {
    self.current_state.store_loc(location, value);
    if self.trace.len() >= self.max_trace_size {
      self.flag_out_of_fuel = true;
    }
  }

  pub fn push_update_by_name(&mut self, name: &String, value: HeapValue) {
    match self.current_state.lookup_loc(name) {
      None => { self.push_alloc(name.clone(), 1, value); },
      Some(loc) => { self.push_update(&loc.clone(), value); },
    };
  }

  pub fn push_tag(&mut self, tag: Tag) {
    if self.trace.len() >= self.max_trace_size {
      self.flag_out_of_fuel = true;
      return;
    }
    self.trace.push_state(tag, &self.current_state);
  }

  pub fn set_break_flag(&mut self) {
    self.flag_break = true;
  }

  pub fn get_break_flag(&self) -> bool {
    self.flag_break
  }

  pub fn clear_break_flag(&mut self) {
    self.flag_break = false;
  }

  pub fn set_return_flag(&mut self) {
    self.flag_return = true;
  }

  pub fn get_return_flag(&self) -> bool {
    self.flag_return
  }

  pub fn clear_return_flag(&mut self) {
    self.flag_return = false;
  }

  pub fn set_location(&mut self, location: HeapLocation) {
    self.reg_location = location;
  }

  pub fn set_location_by_name(&mut self, name: &String) {
    let loc = self.current_state.lookup_loc(name)
      .expect(format!("Name not found: {}", name).as_str());
    self.set_location(loc.clone())
  }

  pub fn set_value(&mut self, value: HeapValue) {
    self.reg_value = value;
  }

  pub fn set_value_by_name(&mut self, name: &String) {
    self.reg_value = match self.current_state.read_var(name) {
      VarRead::Value(val) => val,
      VarRead::Array(arr) => arr[0].clone(),
    }
  }

  pub fn current_value(&self) -> HeapValue {
    self.reg_value.clone()
  }

  pub fn current_location(&self) -> HeapLocation {
    self.reg_location.clone()
  }

  pub fn value_is_true(&self) -> bool {
    match self.reg_value {
      HeapValue::Int(val) => val != 0,
      _ => panic!("Not a boolean interpretable value: {:?}", self.reg_value),
    }
  }

  pub fn value_is_false(&self) -> bool {
    match self.reg_value {
      HeapValue::Int(val) => val == 0,
      _ => panic!("Not a boolean interpretable value: {:?}", self.reg_value),
    }
  }

  pub fn value_int(&self) -> i32 {
    match self.reg_value {
      HeapValue::Int(i) => i,
      _ => panic!("Value not an int: {:?}", self.reg_value),
    }
  }

  pub fn value_float(&self) -> f32 {
    match self.reg_value {
      HeapValue::Float(f) => f,
      _ => panic!("Value not a float: {:?}", self.reg_value),
    }
  }

  pub fn negate_value(&mut self) {
    match self.reg_value {
      HeapValue::Int(i) => self.reg_value = HeapValue::Int(-i),
      HeapValue::Float(f) => self.reg_value = HeapValue::Float(-f),
    }
  }

  pub fn cf_break(&self) -> bool {
    self.flag_break || self.flag_return || self.flag_out_of_fuel
  }

  pub fn ended(&self) -> bool {
    self.flag_return || self.flag_out_of_fuel
  }
}
