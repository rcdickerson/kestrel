use crate::anneal::choice_node::*;
use egg::*;
use uuid::*;

#[derive(Debug, Clone)]
pub struct ChoicePath<L: Language> {
  id: Uuid,
  choice_node: ChoiceNode<L>,
  class_id: usize,
  choice: usize,
  children: Vec<ChoicePath<L>>,
}

impl <L: Language> ChoicePath<L> {

  pub fn new(id: Uuid, choice_node: ChoiceNode<L>, class_id: usize, choice: usize) -> Self {
    ChoicePath { id, choice_node, class_id, choice, children: Vec::new() }
  }

  pub fn id(&self) -> &Uuid {
    &self.id
  }

  pub fn class_id(&self) -> usize {
    self.class_id
  }

  pub fn choice(&self) -> usize {
    self.choice
  }

  pub fn size(&self) -> usize {
    1 + self.children.clone().into_iter().map(|child| child.size()).sum::<usize>()
  }

  pub fn choice_node(&self) -> &ChoiceNode<L> {
    &self.choice_node
  }

  pub fn node(&self) -> &L {
    &self.choice_node.node()
  }

  pub fn children(&self) -> &Vec<ChoicePath<L>> {
    &self.children
  }

  pub fn push_child(&mut self, child: ChoicePath<L>) {
    self.children.push(child);
  }

  pub fn to_rec_expr(&self) -> RecExpr<L> {
    RecExpr::from(self.to_node_vec())
  }

  pub fn to_node_vec(&self) -> Vec<L> {
    let mut nodes = Vec::new();
    let mut child_indices = Vec::<egg::Id>::new();
    for child in &self.children {
      let mut child_nodes = child.to_node_vec();
      for child_node in &mut child_nodes {
        child_node.update_children(|child_id| (usize::from(child_id) + nodes.len()).into());
      }
      nodes.append(&mut child_nodes);
      child_indices.push((nodes.len() - 1).into());
    }
    let mut node = self.node().clone();
    for (i, child_id) in child_indices.iter().enumerate() {
      node.children_mut()[i] = *child_id;
    }
    nodes.push(node);
    nodes
  }
}
