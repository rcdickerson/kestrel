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

  pub fn find_best<F>(&self, root: egg::Id, fitness: F) -> RecExpr<L>
    where F: Fn(RecExpr<L>) -> f32
  {
    println!("Starting simulated annealing...");

    let mut seen_selections = HashSet::new();

    let mut rng = rand::thread_rng();
    let mut selection = Selection::random(self.egraph);
    let mut score = fitness(selection.program(root));

    let mut best = selection.program(root);
    let mut best_score = score;

    let max_k = 1000;

    for k in 0..max_k {
      let mut selections = selection.selections.iter()
        .map( |(k, v)| (k.clone(), v.clone()))
        .collect::<Vec<(egg::Id, usize)>>();
      selections.sort();
      seen_selections.insert(selections);

      let temp = 1.0 - (k as f32) / ((1 + max_k) as f32);
      let neighbor = selection.neighbor(root);
      let n_score = fitness(neighbor.program(root));
      if n_score < best_score {
        best = neighbor.program(root);
        best_score = n_score;
      }
      let transition = if n_score <= score { true } else {
        println!("score: {}", score);
        println!("n score: {}", n_score);
        println!("temp: {}", temp);
        println!("Transitioning with probability: {}", ((score - n_score) as f32 / temp).exp());
        ((score - n_score) as f32 / temp).exp() > rng.gen()
      };
      if transition {
        selection = neighbor;
        score = n_score;
      }
    }
    println!("Simulated annealing complete.");
    println!("Saw {} configurations", seen_selections.len());
    println!("Best score: {}", best_score);
    best
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
    // let mut used_ids = HashSet::new();
    // used_ids.insert(root.clone());
    // for node in self.program(root).as_ref() {
    //   for id in node.children() {
    //     used_ids.insert(id.clone());
    //   }
    // }
    // println!("Used ids: {:?}", used_ids);

    // Find the used class IDs with other available options and select one at random.
    let keys = self.options.keys().map(|i| i.clone()).collect::<HashSet<egg::Id>>();
    //let mut changeable = keys.intersection(&used_ids).collect::<Vec<&egg::Id>>();
    let mut changeable = keys.iter().collect::<Vec<&egg::Id>>();
//    println!("{} possible classes to change", changeable.len());
    if changeable.len() == 0 {
      // TODO: Not sure what to do when there are no choices to change?
      return Selection::random(self.egraph)
    }
    changeable.shuffle(&mut rng);
    let change_index = changeable[0];
//    println!("Changing class {}", change_index);

    // Select a new option for that class ID.
    let old_selection = self.selections.get(change_index).expect("Id not in selections");
    let num_options = self.options.get(change_index).expect("Id not in options");
    let advance = rng.gen_range(1..*num_options);
    let new_selection = (old_selection + advance) % num_options;

    //print!("Changing class {} from {:?} => {:?}\n", change_index,
    //       self.egraph[*change_index].nodes[*old_selection],
    //       self.egraph[*change_index].nodes[new_selection]);

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
