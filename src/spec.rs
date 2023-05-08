pub mod condition;
pub mod parser;

use crate::spec::condition::*;

#[derive(Clone, Debug, PartialEq)]
pub struct KestrelSpec {
  pub pre: CondExpr,
  pub left: String,
  pub right: String,
  pub post: CondExpr,
}
