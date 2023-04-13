pub mod parser;

#[derive(Clone, Debug, PartialEq)]
pub struct KestrelSpec {
  pub pre: String,
  pub left: String,
  pub right: String,
  pub post: String,
}
