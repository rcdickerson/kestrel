use egg::*;
use crate::anneal::jumper::*;
use rand::Rng;

pub struct Annealer {
}

impl Annealer {
  pub fn new() -> Self {
    Annealer { }
  }

  pub fn find_best<L, J, F, D, M>(&self,
                                  max_iterations: usize,
                                  init: Option<RecExpr<L>>,
                                  jumper: &mut J,
                                  fitness: F,
                                  debug_info: D)
                                  -> (RecExpr<L>, M)
    where
      L: Language,
      J: Jumper<L, M>,
      F: Fn(&RecExpr<L>, &M) -> f32,
      D: Fn(&RecExpr<L>, &M) -> (),
      M: std::fmt::Debug,
  {
    println!("Starting simulated annealing...");

    match init {
      None => jumper.set_selection_random(),
      Some(init) => jumper.set_selection(&init),
    };

    let (mut best, mut best_meta) = jumper.selected_program();
    let mut best_score = fitness(&best, &best_meta);
    let mut last_best_at = 0;
    let mut reset_count = 0;
    let reset_threshold = max_iterations / 10;
    let mut rng = rand::thread_rng();

    println!("Initial score: {}", best_score);
//    println!("{:?}", debug_info(&best, &best_meta));

    for k in 0..max_iterations {
      if k - last_best_at > reset_threshold {
//        if reset_count > 2 {
//          println!("Simulated annealing converged after {} iterations", k);
//          break;
//        }
        println!("No new best seen in {} iterations, resetting", reset_threshold);
        jumper.set_selection(&best);
        last_best_at = k;
        reset_count += 1;
      }

      let temp = 1.0 - (k as f32) / ((1 + max_iterations) as f32);
      jumper.pick_random_neighbor();
      let (neighbor, neighbor_meta) = jumper.neighbor_program();
      let neighbor_score = fitness(&neighbor, &neighbor_meta);

      if neighbor_score < best_score {
        (best, best_meta) = jumper.neighbor_program();
        best_score = neighbor_score;
        last_best_at = k;
        reset_count = 0;
        println!("New best: {}", best_score);
        //println!("New best: {:?}", debug_info(&best, &best_meta));
        if best_score < 0.000000001 {
          println!("Simulated annealing converged after {} iterations.", k);
          return (best, best_meta);
        }
      }

      let transition = if neighbor_score < best_score { true } else {
        // println!("--------------------------------------");
        // println!("Transitioning with probability: {}", ((score - n_score) as f32 / temp).exp());
        // println!("temp: {}", temp);
        // println!("best: {}", best_score);
        // println!("current: {}", score);
        // println!("neighbor: {}", n_score);
        ((best_score - neighbor_score) / temp).exp() > rng.gen()
      };
      if transition {
        jumper.jump_to_neighbor();
        // println!("Transitioning with score {} at temperature {}", best_score, temp);
        // debug_info(&best);
      }
    }
    println!("Simulated annealing complete.");
    println!("Best score: {}", best_score);
    (best, best_meta)
  }
}
