use crate::spec::condition::*;

#[derive(Clone, Debug, PartialEq)]
pub struct ElaeniaSpec {
  pub pre: KestrelCond,
  pub afun: String,
  pub efun: String,
  pub post: KestrelCond,
  pub aspecs: Vec<UniversalSpec>,
  pub especs: Vec<ExistentialSpec>,
}

impl ElaeniaSpec {
  pub fn lookup_aspec(&self, name: &String) -> Option<&UniversalSpec> {
    for aspec in &self.aspecs {
      if aspec.name == *name {
        return Some(aspec);
      }
    }
    None
  }

  pub fn lookup_espec(&self, name: &String) -> Option<&ExistentialSpec> {
    for aspec in &self.especs {
      if aspec.name == *name {
        return Some(aspec);
      }
    }
    None
  }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Parameter {
  Variable(String),
  Array{ lhs: Box<Parameter>, size: u32 },
}

#[derive(Clone, Debug, PartialEq)]
pub struct UniversalSpec {
  pub name: String,
  pub params: Vec<Parameter>,
  pub pre: KestrelCond,
  pub post: KestrelCond,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExistentialSpec {
  pub name: String,
  pub params: Vec<Parameter>,
  pub choice_vars: Vec<String>,
  pub pre: KestrelCond,
  pub post: KestrelCond,
}
