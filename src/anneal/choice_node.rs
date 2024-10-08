use egg::*;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct ChoiceNode<L: Language> {
  id: usize,
  node: L,
  children: Vec<usize>,
  metadata: HashMap<String, String>,
}

impl <L: Language> ChoiceNode<L> {
  pub fn new(id: usize, node: L) -> Self {
    ChoiceNode { id, node, children: Vec::new(), metadata: HashMap::new() }
  }

  pub fn id(&self) -> usize {
    self.id
  }

  pub fn node(&self) -> &L {
    &self.node
  }

  pub fn children(&self) -> &Vec<usize> {
    &self.children
  }

  pub fn push_child(&mut self, child: usize) {
    self.children.push(child);
  }

  pub fn put_metadata(&mut self, key: String, value: String) {
    self.metadata.insert(key, value);
  }

  pub fn put_metadata_usize(&mut self, key: String, value: usize) {
    self.metadata.insert(key, value.to_string());
  }

  pub fn get_metadata(&self, key: &String) -> Option<&String> {
    self.metadata.get(key)
  }

  pub fn get_metadata_usize(&self, key: &String) -> Option<usize> {
    self.metadata.get(key).map(|data| data.parse::<usize>().unwrap())
  }
}
