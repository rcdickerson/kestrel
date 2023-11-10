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

  pub fn find_best<F>(&self,
                      max_iterations: usize,
                      root: egg::Id,
                      init: Option<RecExpr<L>>,
                      fitness: F)
                      -> RecExpr<L>
    where F: Fn(RecExpr<L>) -> f32
  {
    println!("Starting simulated annealing...");

    let mut seen_selections = HashSet::new();

    let mut rng = rand::thread_rng();
    let mut selection = match init {
      None => Selection::random(self.egraph),
      Some(init) => Selection::from_expr(self.egraph, &init),
    };
    let mut score = fitness(selection.program(root));

    let mut best = selection.program(root);
    let mut best_score = score;
    let mut last_best_at = 0;
    println!("Initial score: {}", best_score);

    for k in 0..max_iterations {
      if k - last_best_at > 2000 { break; }

      let mut selections = selection.selections.iter()
        .map( |(k, v)| (k.clone(), v.clone()))
        .collect::<Vec<(egg::Id, usize)>>();
      selections.sort();
      seen_selections.insert(selections);

      let temp = 1.0 - (k as f32) / ((1 + max_iterations) as f32);
      let neighbor = selection.neighbor();
      let n_score = fitness(neighbor.program(root));

      if n_score < best_score {
        best = neighbor.program(root);
        best_score = n_score;
        last_best_at = k;
        println!("Score {} at temperature {}", best_score, temp);
      }
      let transition = if n_score <= score { true } else {
        // println!("--------------------------------------");
        // println!("Transitioning with probability: {}", ((score - n_score) as f32 / temp).exp());
        // println!("temp: {}", temp);
        // println!("best: {}", best_score);
        // println!("current: {}", score);
        // println!("neighbor: {}", n_score);
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

#[derive(Debug)]
struct Selection<'a, L: Language, N: Analysis<L>> {
  egraph: &'a EGraph<L, N>,
  options: HashMap<egg::Id, usize>,
  selections: HashMap<egg::Id, usize>,
}

impl <'a, L: Language, N: Analysis<L>> Clone for Selection<'a, L, N> {
  fn clone(&self) -> Selection<'a, L, N> {
    Selection {
      egraph: self.egraph,
      options: self.options.clone(),
      selections: self.selections.clone(),
    }
  }
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

  fn from_expr(egraph: &'a EGraph<L, N>, expr: &RecExpr<L>) -> Self {
    let mut rng = rand::thread_rng();
    let mut options = HashMap::new();
    let mut selections = HashMap::new();
    let expr_nodes = Selection::expr_to_eclassed_nodes(egraph, expr);
    for eclass in egraph.classes() {
      let num_choices = eclass.nodes.len();
      if num_choices > 1 {
        options.insert(eclass.id, num_choices);
      }
      let mut found = false;
      for (i, node) in eclass.nodes.clone().into_iter().enumerate() {
        if expr_nodes.contains(&node) {
          selections.insert(eclass.id, i);
          found = true;
          break;
        }
      }
      if !found {
        let selection: usize = rng.gen_range(0..num_choices);
        selections.insert(eclass.id, selection);
      }
    }

    Selection { egraph, options, selections }
  }

  fn expr_to_eclassed_nodes(egraph: &'a EGraph<L, N>, expr: &RecExpr<L>) -> HashSet<L> {
    let nodes = expr.as_ref();
    let mut ids = Vec::with_capacity(nodes.len());
    let mut eclass_nodes = HashSet::with_capacity(nodes.len());
    for node in nodes {
      let node = node.clone().map_children(|i| ids[usize::from(i)]);
      let id = egraph.lookup(node.clone());
      ids.push(id.unwrap());
      eclass_nodes.insert(node);
    }
    eclass_nodes
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

  fn neighbor(&self) -> Self {
    let mut rng = rand::thread_rng();

    // Find the used class IDs with other available options and select one at random.
    let keys = self.options.keys().map(|i| i.clone()).collect::<HashSet<egg::Id>>();
    //let mut changeable = keys.intersection(&used_ids).collect::<Vec<&egg::Id>>();
    let mut changeable = keys.iter().collect::<Vec<&egg::Id>>();
    if changeable.len() == 0 {
      // TODO: Not sure what to do when there are no choices to change?
      return Selection::random(self.egraph)
    }
    changeable.shuffle(&mut rng);
    let change_index = changeable[0];

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
