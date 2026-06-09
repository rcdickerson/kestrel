use crate::crel::ast::*;
use crate::crel::fundef::*;
use crate::crel::mapper::*;
use std::collections::HashMap;
use std::collections::HashSet;

pub trait FindsInvariants {
  fn daikon_crel(&self) -> &CRel;
  fn global_decls(&self) -> &Vec<Declaration>;
  fn global_fundefs(&self) -> &HashMap<String, FunDef>;
  fn accept_invariants(&mut self, invars: HashMap<String, Vec<Expression>>);
}

pub struct LoopKeeper<'a> {
  keep_ids: HashSet<&'a String>,
  handled_ids: HashSet<String>,
}

impl <'a> LoopKeeper<'a> {
  pub fn new(keep_ids: HashSet<&'a String>) -> Self {
    LoopKeeper{keep_ids, handled_ids: HashSet::new()}
  }
}

impl CRelMapper for LoopKeeper<'_> {
  fn map_statement(&mut self, stmt: &Statement) -> Statement {
    match stmt {
      Statement::While{id, condition, ..} => {
        let lhid = loop_head_name(id);
        if !self.keep_ids.contains(&lhid) && !self.handled_ids.contains(&lhid) {
          self.handled_ids.insert(lhid);
          Statement::If {
            condition: condition.clone(),
            then: Box::new(stmt.clone()),
            els: None,
          }
        } else {
          stmt.clone()
        }
      },
      _ => stmt.clone(),
    }
  }
}
