use egg::*;
use crate::anneal::choice_graph::*;
use rand::{Rng, rngs::ThreadRng};
use std::collections::HashSet;

pub struct Annealer<'a, L: Language, N: Analysis<L>> {
  egraph: &'a EGraph<L, N>,
  choice_graph: ChoiceGraph<L>,
}
impl<'a, L: Language, N: Analysis<L>> Annealer<'a, L, N> {

  pub fn new(egraph: &'a EGraph<L, N>) -> Self {
    Annealer{egraph, choice_graph: ChoiceGraph::new(egraph)}
  }

  pub fn find_best<F, G>(&self,
                      max_iterations: usize,
                      root: egg::Id,
                      init: Option<RecExpr<L>>,
                      fitness: F,
                      debug_info: G)
                      -> RecExpr<L>
  where
      F: Fn(&RecExpr<L>) -> f32,
      G: Fn(&RecExpr<L>) -> (),
  {
    println!("Starting simulated annealing...");

    let mut seen_selections = HashSet::new();

    let mut rng = rand::thread_rng();
    let mut current = match init {
      None => self.random_expression(root),
      Some(init) => init,
    };
    let mut score = fitness(&current);

    let mut best = current.clone();
    let mut best_score = score;
    let mut last_best_at = 0;
    let mut reset_count = 0;
    let reset_threshold = max_iterations / 10;

    println!("Initial score: {}", best_score);

    for k in 0..max_iterations {
      if k - last_best_at > reset_threshold {
        if reset_count > 2 {
          println!("Simulated annealing converged after {} iterations", k);
          break;
        }
        println!("No new best seen in {} iterations, resetting", reset_threshold);
        current = best.clone();
        score = best_score;
        last_best_at = k;
        reset_count += 1;
      }

      seen_selections.insert(current.clone());

      let temp = 1.0 - (k as f32) / ((1 + max_iterations) as f32);
      let choices = ChoicePath::from_rec_expr(&self.choice_graph, &current);
      let neighbor_choices = self.choice_graph.neighbor(&choices);
      let neighbor = self.choice_graph.to_rec_expr(&neighbor_choices);
      let n_score = fitness(&neighbor);

      if n_score < best_score {
        best = neighbor.clone();
        best_score = n_score;
        last_best_at = k;
        reset_count = 0;
        println!("Score {} at temperature {}", best_score, temp);
        debug_info(&best);
      }
      let transition = if n_score <= score { true } else {
        // println!("--------------------------------------");
        // println!("Transitioning with probability: {}", ((score - n_score) as f32 / temp).exp());
        // println!("temp: {}", temp);
        // println!("best: {}", best_score);
        // println!("current: {}", score);
        // println!("neighbor: {}", n_score);
        ((score - n_score) / temp).exp() > rng.gen()
      };
      if transition {
        current = neighbor;
        score = n_score;
      }
    }
    println!("Simulated annealing complete.");
    println!("Saw {} configurations", seen_selections.len());
    println!("Best score: {}", best_score);
    best
  }

  fn random_expression(&self, root: egg::Id) -> RecExpr<L> {
    let random = RandomExtractor::new();
    let (_, expr) = Extractor::new(self.egraph, random).find_best(root);
    expr
  }
}

/// Assign random costs to every e-node. Effectively extracts
/// a random element from the search space.
struct RandomExtractor {
  rng: ThreadRng,
}

impl RandomExtractor {
  fn new() -> Self {
    Self { rng: rand::thread_rng() }
  }
}

impl<L: Language> CostFunction<L> for RandomExtractor {
  type Cost = usize;
  fn cost<C>(&mut self, _: &L, _costs: C) -> Self::Cost
  where
    C: FnMut(Id) -> Self::Cost,
  {
    self.rng.gen_range(0..100)
  }
}
