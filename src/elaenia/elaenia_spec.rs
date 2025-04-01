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

#[derive(Clone, Debug, PartialEq)]
pub struct UniversalSpec {
  pub name: String,
  pub params: Vec<String>,
  pub pre: KestrelCond,
  pub post: KestrelCond,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExistentialSpec {
  pub name: String,
  pub params: Vec<String>,
  pub choice_vars: Vec<String>,
  pub pre: KestrelCond,
  pub post: KestrelCond,
}
