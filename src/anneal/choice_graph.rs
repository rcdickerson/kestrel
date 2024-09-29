use egg::*;
use rand::seq::SliceRandom;
use std::collections::HashMap;
use std::collections::HashSet;
use uuid::Uuid;

#[derive(Debug, Clone)]
pub struct ChoiceGraph<L: Language> {
  root: usize,
  classes: Vec<ChoiceClass<L>>,
}

impl <'a, L: Language> ChoiceGraph<L> {

  pub fn new<N>(egraph: &EGraph<L, N>) -> Self
      where L: Language,
            N: Analysis<L>
  {
    let mut classes = Vec::with_capacity(egraph.number_of_classes());
    let mut eclass_to_class_id = HashMap::new();
    for eclass in egraph.classes().into_iter() {
      let class_id = classes.len();
      let mut class = ChoiceClass::new(class_id);
      for node in &eclass.nodes {
        class.add_choice(node.clone());
      }
      eclass_to_class_id.insert(eclass.id, class_id);
      classes.push(class);
    }
    for eclass in egraph.classes().into_iter() {
      for (id, node) in eclass.nodes.iter().enumerate() {
        let class_id = eclass_to_class_id.get(&eclass.id).unwrap();
        let class = &mut classes[*class_id];
        let choice = class.get_choice_mut(id);
        for child in node.children() {
          choice.push_child(*eclass_to_class_id.get(child).unwrap());
        }
      }
    }

    let mut no_parents = HashSet::new();
    for id in 0..classes.len() {
      no_parents.insert(id);
    }
    for class in &classes {
      for choice in &class.choices {
        for child in &choice.children {
          no_parents.remove(&child);
        }
      }
    }
    let root = match no_parents.len() {
      1 => *no_parents.iter().next().unwrap(),
      _ => panic!("Looking for exactly 1 root, found {}", no_parents.len()),
    };

    ChoiceGraph { root, classes }
  }

  pub fn root_class(&self) -> &ChoiceClass<L> {
    &self.classes[self.root]
  }

  pub fn choice_classes(&self) -> &Vec<ChoiceClass<L>> {
    &self.classes
  }

  pub fn to_rec_expr(&self, path: &ChoicePath) -> RecExpr<L> {
    RecExpr::from(self.to_node_vec(path))
  }

  pub fn neighbor(&self, path: &ChoicePath) -> ChoicePath {
    let possible_changes = path.possible_changes(self);
    if possible_changes.is_empty() {
      return path.clone();
    }

    let to_change = possible_changes.choose(&mut rand::thread_rng()).unwrap();
    let mut choices = self.classes[to_change.class_id].choices.clone();
    choices.retain(|choice| choice.id != to_change.choice);
    let new_choice = choices.choose(&mut rand::thread_rng()).unwrap();

    path.switch(self, to_change, new_choice)
  }

  pub fn to_node_vec(&self, path: &ChoicePath) -> Vec<L> {
    let mut nodes = Vec::new();
    let mut child_indices = Vec::<egg::Id>::new();
    for child in &path.children {
      let mut child_nodes = self.to_node_vec(child);
      for child_node in &mut child_nodes {
        child_node.update_children(|child_id| (usize::from(child_id) + nodes.len()).into());
      }
      nodes.append(&mut child_nodes);
      child_indices.push((nodes.len() - 1).into());
    }
    let mut node = self.classes[path.class_id].choices[path.choice].node.clone();
    for (i, child_id) in child_indices.iter().enumerate() {
      node.children_mut()[i] = *child_id;
    }
    nodes.push(node);
    nodes
  }
}


#[derive(Debug, Clone)]
pub struct ChoiceClass<L: Language> {
  id: usize,
  choices: Vec<ChoiceNode<L>>,
}

impl <'a, L: Language> ChoiceClass<L> {
  pub fn new(id: usize) -> Self {
    ChoiceClass{ id, choices: Vec::new() }
  }

  pub fn add_choice(&mut self, node: L) {
    let choice_node = ChoiceNode::new(self.choices.len(), node);
    self.choices.push(choice_node);
  }

  pub fn get_choice(&self, id: usize) -> &ChoiceNode<L> {
    &self.choices[id]
  }

  pub fn get_choice_mut(&mut self, id: usize) -> &mut ChoiceNode<L> {
    &mut self.choices[id]
  }

  pub fn indices_of(&self, node: &L) -> Vec<usize> {
    let mut all_matches = Vec::new();
    for (index, choice) in self.choices.iter().enumerate() {
      if node.matches(&choice.node) {
        all_matches.push(index);
      }
    }
    all_matches
  }
}


#[derive(Debug, Clone)]
pub struct ChoiceNode<L: Language> {
  id: usize,
  node: L,
  children: Vec<usize>,
}

impl <L: Language> ChoiceNode<L> {
  pub fn new(id: usize, node: L) -> Self {
    ChoiceNode { id, node, children: Vec::new() }
  }

  pub fn push_child(&mut self, child: usize) {
    self.children.push(child);
  }
}


#[derive(Debug, Clone)]
pub struct ChoicePath {
  id: Uuid,
  class_id: usize,
  choice: usize,
  children: Vec<ChoicePath>,
}

impl ChoicePath {
  pub fn random<L>(graph: &ChoiceGraph<L>, start_class: usize, force_picks: &mut Vec<ChoicePath>) -> Self
      where L: Language
  {
    let class = &graph.classes[start_class];
    match force_picks.iter().position(|choice| choice.class_id == class.id) {
      None => {
        let choice = class.choices.choose(&mut rand::thread_rng()).unwrap();
        ChoicePath {
          id: Uuid::new_v4(),
          class_id: class.id,
          choice: choice.id,
          children: choice.children.iter()
            .map(|child| ChoicePath::random(graph, *child, force_picks))
            .collect(),
        }
      },
      Some(idx) => {
        let forced = force_picks[idx].clone();
        force_picks.retain(|path| path.id != forced.id);
        forced
      }
    }
  }

  pub fn from_rec_expr<L>(graph: &ChoiceGraph<L>, expr: &RecExpr<L>) -> Self
      where L: Language
  {
    let nodes = &expr.as_ref().to_vec();
    ChoicePath::from_expr_nodes(graph, graph.root_class(), nodes, nodes.len() - 1)
        .expect("could not find path to expression in graph")
  }

  fn from_expr_nodes<L>(graph: &ChoiceGraph<L>,
                        class: &ChoiceClass<L>,
                        nodes: &Vec<L>,
                        node_idx: usize) -> Option<Self>
      where L: Language
  {
    let node = &nodes[node_idx];
    'search: for index in class.indices_of(&node) {
      let choice_children = &class.choices[index].children;
      if choice_children.len() == 0 {
        return Some(ChoicePath {
          id: Uuid::new_v4(),
          class_id: class.id,
          choice: index,
          children: Vec::new(),
        });
      }

      let mut child_paths = Vec::new();
      for (choice_child, node_child) in std::iter::zip(choice_children, node.children()) {
        let child_class = &graph.classes[*choice_child];
        let child_path = ChoicePath::from_expr_nodes(graph, child_class, nodes,
                                                     usize::from(*node_child));
        match child_path {
          None => continue 'search,
          Some(path) => child_paths.push(path),
        }
      }
      return Some(ChoicePath {
        id: Uuid::new_v4(),
        class_id: class.id,
        choice: index,
        children: child_paths,
      });
    }
    None
  }

  pub fn possible_changes<L: Language>(&self, graph: &ChoiceGraph<L>) -> Vec<&ChoicePath> {
    let mut nodes = Vec::new();
    if graph.classes[self.class_id].choices.len() > 1 {
      nodes.push(self);
    }
    for child in &self.children {
      nodes.append(&mut child.possible_changes(graph));
    }
    nodes
  }

  pub fn switch<L: Language>(&self,
                             graph: &ChoiceGraph<L>,
                             to_change: &ChoicePath,
                             new_choice: &ChoiceNode<L>) -> ChoicePath {
    if self.id == to_change.id {
      let mut force_picks = self.children.clone();
      ChoicePath {
        id: Uuid::new_v4(),
        class_id: self.class_id,
        choice: new_choice.id,
        children: new_choice.children.iter()
            .map(|child| ChoicePath::random(graph, *child, &mut force_picks))
            .collect(),
      }
    } else {
      ChoicePath {
        id: self.id,
        class_id: self.class_id,
        choice: self.choice,
        children: self.children.iter()
            .map(|child| child.switch(graph, to_change, new_choice))
            .collect()
      }
    }
  }
}
