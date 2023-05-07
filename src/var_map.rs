use std::collections::HashMap;

pub struct VarMap {
  // Execution -> Original Var -> Fresh Var
  forwards: HashMap<String, HashMap<String, String>>,

  // Fresh Var -> (Exec, Original Var)
  backward: HashMap<String, (String, String)>,
}

impl VarMap {
  pub fn new() -> VarMap {
    VarMap {
      forwards: HashMap::new(),
      backward: HashMap::new(),
    }
  }

  pub fn freshen(&mut self, exec: &String, name: &String) -> String {
    let mut i = 1;
    let mut fresh = format!("{}_{}", name, i).to_string();
    self.add_exec_if_missing(exec);
    while self.contains_forward_key(exec, &fresh) {
      i = i + 1;
      fresh = format!("{}_{}", name, i).to_string();
    };
    self.forwards.get_mut(exec).unwrap().insert(name.clone(), fresh.clone());
    self.backward.insert(fresh.clone(), (exec.clone(), name.clone()));
    fresh
  }

  fn add_exec_if_missing(&mut self, exec: &String) {
    if !self.forwards.contains_key(exec) {
      self.forwards.insert(exec.clone(), HashMap::new());
    }
  }

  pub fn contains_forward_key(&self, exec: &String, name: &String) -> bool {
    self.forwards.contains_key(exec) &&
      self.forwards[exec].contains_key(name)
  }
}
