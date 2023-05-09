use egg::*;
use rand::{Rng, seq::SliceRandom};
use std::collections::HashMap;
use std::collections::HashSet;

pub struct Annealer<'a, L: Language, N: Analysis<L>> {
  egraph: &'a EGraph<L, N>,
}
impl<'a, L: Language, N: Analysis<L>> Annealer<'a, L, N> {

  pub fn new(egraph: &'a EGraph<L, N>) -> Self {
    Annealer{egraph}
  }

  pub fn find_best(&self, root: egg::Id) -> RecExpr<L> {
    let selection = Selection::random(self.egraph);
    selection.program(root)
  }
}

#[derive(Clone, Debug)]
struct Selection<'a, L: Language, N: Analysis<L>> {
  egraph: &'a EGraph<L, N>,
  options: HashMap<egg::Id, usize>,
  selections: HashMap<egg::Id, usize>,
}
impl<'a, L: Language, N: Analysis<L>> Selection<'a, L, N> {

  fn random(egraph: &'a EGraph<L, N>) -> Self {
    let mut rng = rand::thread_rng();
    let mut options = HashMap::new();
    let mut selections = HashMap::new();
    for eclass in egraph.classes() {
      let num_choices = eclass.nodes.len();
      if num_choices > 1 {
        options.insert(eclass.id, num_choices);
      }
      let selection: usize = rng.gen_range(0..num_choices);
      selections.insert(eclass.id, selection);
    }

    Selection { egraph, options, selections }
  }

  fn program(&self, root: egg::Id) -> RecExpr<L> {
    let selector = SelectionExtractor {
      egraph: self.egraph,
      selections: self.selections.clone(),
    };
    let extractor = Extractor::new(self.egraph, selector);
    let (_, prog) = extractor.find_best(root);
    prog
  }

  fn neighbor(&self, root: egg::Id) -> Self {
    let mut rng = rand::thread_rng();

    // Get the class IDs used by the current selection.
    let mut used_ids = HashSet::new();
    used_ids.insert(root.clone());
    for node in self.program(root).as_ref() {
      for id in node.children() {
        used_ids.insert(id.clone());
      }
    }

    // Find the used class IDs with other available options and select one at random.
    let keys = self.options.keys().map(|i| i.clone()).collect::<HashSet<egg::Id>>();
    let mut changeable = keys.intersection(&used_ids).collect::<Vec<&egg::Id>>();
    changeable.shuffle(&mut rng);
    let change_index = changeable[0];

    // Select a new option for that class ID.
    let old_selection = self.selections.get(change_index).expect("Id not in selections");
    let num_options = self.options.get(change_index).expect("Id not in options");
    let advance = rng.gen_range(1..*num_options);
    let new_selection = (old_selection + advance) % num_options;

    let mut updated_selections = self.selections.clone();
    updated_selections.insert(change_index.clone(), new_selection);
    Selection {
      egraph: self.egraph,
      options: self.options.clone(),
      selections: updated_selections,
    }
  }
}

struct SelectionExtractor<'a, L: Language, N: Analysis<L>> {
  egraph: &'a EGraph<L, N>,
  selections: HashMap<egg::Id, usize>,
}
impl<'a, L: Language, N: Analysis<L>> CostFunction<L> for SelectionExtractor<'a, L, N> {
  type Cost = usize;
  fn cost<C>(&mut self, enode: &L, _costs: C) -> Self::Cost
  where
    C: FnMut(Id) -> Self::Cost,
  {
    let class_id = self.egraph.lookup(enode.clone()).expect("Node not in graph");
    let selection_index = *self.selections.get(&class_id).expect("Id not in graph");
    let selection = &self.egraph[class_id].nodes[selection_index];
    if selection == enode { 0 } else { std::usize::MAX }
  }
}
