use crate::anneal::choice_node::*;
use crate::anneal::choice_path::*;
use egg::*;
use rand::seq::SliceRandom;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use uuid::Uuid;

#[derive(Debug, Clone)]
pub struct ChoiceGraph<L>
  where L: Language,
{
  roots: Vec<usize>,
  classes: Vec<ChoiceClass<L>>,
}

impl <'a, L: Language> ChoiceGraph<L> {
  pub fn new<N, M>(egraph: &EGraph<L, N>, metadata: M) -> Self
    where
      N: Analysis<L>,
      M: Fn(&L) -> Option<Vec<(String, String)>>
  {
    let mut classes = Vec::with_capacity(egraph.number_of_classes());
    let mut eclass_to_class_id = HashMap::new();
    let mut roots = Vec::new();
    for eclass in egraph.classes().into_iter() {
      let class_id = classes.len();
      let mut class = ChoiceClass::new(class_id);
      for node in &eclass.nodes {
        class.add_choice(node.clone(), metadata(node));
      }
      if eclass.parents().len() == 0 {
        roots.push(class_id);
      }
      eclass_to_class_id.insert(eclass.id, class_id);
      classes.push(class);
    }
    if roots.is_empty() {
      panic!("no roots in egraph");
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
    ChoiceGraph{roots, classes}
  }

  pub fn root_classes(&self) -> Vec<&ChoiceClass<L>> {
    self.roots.clone().into_iter().map(|id| &self.classes[id]).collect()
  }

  pub fn classes(&self) -> &Vec<ChoiceClass<L>> {
    &self.classes
  }

  pub fn random_path<F>(&self, filter: &F) -> ChoicePath<L>
    where F: Fn(&ChoiceNode<L>) -> bool
  {
    let root = *self.roots.choose(&mut rand::thread_rng()).unwrap();
    self.random_path_from(root, filter)
  }

  pub fn random_path_from<F>(&self, root: usize, filter: &F) -> ChoicePath<L>
    where F: Fn(&ChoiceNode<L>) -> bool
  {
    self.random_path_from_with_picks(root, &mut Vec::new(), filter)
  }

  pub fn random_path_from_with_picks<F>(&self,
                                        root: usize,
                                        force_picks: &mut Vec<ChoicePath<L>>,
                                        filter: &F)
                                     -> ChoicePath<L>
    where F: Fn(&ChoiceNode<L>) -> bool
  {
    let class = &self.classes[root];
    match force_picks.iter().position(|choice| choice.class_id() == class.id) {
      None => {
        let filtered = class.choices.clone().into_iter().filter(filter).collect::<Vec<_>>();
        let choices = if filtered.is_empty() { class.choices.clone() } else { filtered };
        let choice = choices.choose(&mut rand::thread_rng()).unwrap();
        let mut path = ChoicePath::new(Uuid::new_v4(), choice.clone(), class.id, choice.id());
        for child in choice.children().iter()
          .map(|child| self.random_path_from_with_picks(*child, force_picks, filter)) {
            path.push_child(child);
          }
        path
      },
      Some(idx) => {
        let forced = force_picks[idx].clone();
        //force_picks.retain(|path| path.id() != forced.id());
        forced
      }
    }
  }

  pub fn find_expression_path(&self, expr: &RecExpr<L>) -> ChoicePath<L> {
    let nodes = &expr.as_ref().to_vec();
    for root in self.root_classes() {
      match self.from_expr_nodes(root, nodes, nodes.len() - 1) {
        Some(expr) => return expr,
        _ => ()
      }
    }
    panic!("could not find path to expression in graph")
  }

  fn from_expr_nodes(&self,
                     class: &ChoiceClass<L>,
                     nodes: &Vec<L>,
                     node_idx: usize) -> Option<ChoicePath<L>> {
    let node = &nodes[node_idx];
    'search: for index in class.indices_of(&node) {
      let choice_node = &class.choices[index];
      let choice_children = &class.choices[index].children();
      if choice_children.len() == 0 {
        return Some(ChoicePath::new(Uuid::new_v4(), choice_node.clone(), class.id, index));
      }

      let mut child_paths = Vec::new();
      for (choice_child, node_child) in std::iter::zip(*choice_children, node.children()) {
        let child_class = &self.classes[*choice_child];
        let child_path = self.from_expr_nodes(child_class, nodes, usize::from(*node_child));
        match child_path {
          None => continue 'search,
          Some(path) => child_paths.push(path),
        }
      }
      let mut path = ChoicePath::new(Uuid::new_v4(), choice_node.clone(), class.id, index);
      for child in child_paths {
        path.push_child(child);
      }
      return Some(path);
    }
    None
  }

  pub fn lookup_class(&self, path: &ChoicePath<L>) -> &ChoiceClass<L> {
    &self.classes[path.class_id()]
  }

  pub fn other_root_choices(&self, path: &ChoicePath<L>) -> Vec<ChoiceNode<L>> {
    let class = self.lookup_class(path);
    let mut choices = Vec::new();
    for (i, choice) in (&class.choices).into_iter().enumerate() {
      if i == path.choice() { continue; }
      choices.push(choice.clone())
    }
    choices
  }

  pub fn possible_changes<F>(&self, path: &ChoicePath<L>, num_neighbors: F) -> Vec<ChoicePath<L>>
    where F: Fn(&ChoicePath<L>) -> usize
  {
    let mut possibilities = Vec::new();
    let mut work_queue = VecDeque::new();
    let mut seen = HashSet::new();

    work_queue.push_back(path);
    while !work_queue.is_empty() {
      let current = work_queue.pop_front().unwrap();
      if seen.contains(&current.id()) {
        continue;
      }
      seen.insert(current.id());

      if num_neighbors(current) > 0 {
        possibilities.push(current.clone());
      }
      for child in current.children() {
        work_queue.push_back(child);
      }
    }
    possibilities
  }

  pub fn switch_choice<F>(&self,
                          path: &ChoicePath<L>,
                          subpath: &ChoicePath<L>,
                          new_choice: &ChoiceNode<L>,
                          filter: &F)
                          -> ChoicePath<L>
    where F: Fn(&ChoiceNode<L>) -> bool
  {
    self.switch_rec(path, subpath, new_choice, filter)
  }

  fn switch_rec<F>(&self,
                   path: &ChoicePath<L>,
                   to_change: &ChoicePath<L>,
                   new_choice: &ChoiceNode<L>,
                   filter: &F)
                   -> ChoicePath<L>
    where F: Fn(&ChoiceNode<L>) -> bool
  {
    if path.id() == to_change.id() {
      let mut force_picks = path.children().clone();
      let mut new_path = ChoicePath::new(Uuid::new_v4(), new_choice.clone(), path.class_id(), new_choice.id());
      for child in new_choice.children().iter()
        .map(|child| self.random_path_from_with_picks(*child, &mut force_picks, filter)) {
          new_path.push_child(child);
        }
      new_path
    } else {
      let mut new_path = ChoicePath::new(path.id().clone(), path.choice_node().clone(), path.class_id(), path.choice());
      for child in path.children().iter()
        .map(|child| self.switch_rec(child, to_change, new_choice, filter)) {
          new_path.push_child(child);
        }
      new_path
    }
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

  pub fn len(&self) -> usize {
    self.choices.len()
  }

  pub fn add_choice(&mut self, node: L, metadata: Option<Vec<(String, String)>>) {
    let mut choice_node = ChoiceNode::new(self.choices.len(), node);
    metadata.map(|data| {
      for (key, value) in data {
        choice_node.put_metadata(key, value);
      }
    });
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
      if node.matches(choice.node()) {
        all_matches.push(index);
      }
    }
    all_matches
  }
}
