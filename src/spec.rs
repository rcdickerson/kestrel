pub mod condition;
pub mod parser;
pub mod to_crel;

use crate::spec::{condition::*};

#[derive(Clone, Debug, PartialEq)]
pub struct KestrelSpec {
  pub pre: KestrelCond,
  pub left: String,
  pub right: String,
  pub post: KestrelCond,
}
