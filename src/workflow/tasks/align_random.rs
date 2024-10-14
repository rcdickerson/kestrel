use crate::anneal::choice_graph::*;
use crate::anneal::choice_path::*;
use crate::eggroll::ast::*;
use crate::workflow::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use egg::*;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

pub struct AlignRandom {}

impl AlignRandom {
  pub fn new() -> Self {
    AlignRandom { }
  }

  fn random_path(&self, choice_graph: &ChoiceGraph<Eggroll>) -> Option<ChoicePath<Eggroll>> {
    let (tx, rx) = mpsc::channel();
    thread::scope(|scope| {
      scope.spawn(|| {
        let path = choice_graph.random_path(&|_| true);
        tx.send(path).unwrap()
      });
    });
    match rx.recv_timeout(Duration::from_secs(10)) {
      Ok(path) => Some(path),
      _ => None,
    }
  }

  fn to_rec_expr(&self, path: &ChoicePath<Eggroll>) -> Option<RecExpr<Eggroll>> {
    let (tx, rx) = mpsc::channel();
    thread::scope(|scope| {
      scope.spawn(|| {
        let expr = path.to_rec_expr();
        tx.send(expr).unwrap()
      });
    });
    match rx.recv_timeout(Duration::from_secs(10)) {
      Ok(path) => Some(path),
      _ => None,
    }
  }

  fn attempt_verification(&self, rec_expr: RecExpr<Eggroll>, context: &Context) -> Option<bool> {
    let (tx, rx) = mpsc::channel();
    thread::scope(|scope| {
      scope.spawn(|| {
        let mut new_ctx = context.clone();
        new_ctx.aligned_eggroll.replace(rec_expr);
        let mut verification_workflow = Workflow::new(&mut new_ctx);
        verification_workflow.add_task(AlignedCRel::new());
        verification_workflow.add_task(InvarsDaikon::new(Some(60)));
        verification_workflow.add_task(Houdafny::new(Some(60)));
        verification_workflow.execute();
        tx.send(if verification_workflow.context().timed_out { None } else {
          Some(verification_workflow.context().verified)
        }).unwrap();
      });
    });
    match rx.recv_timeout(Duration::from_secs(120)) {
      Ok(result) => result,
      _ => None,
    }
  }
}

impl Task for AlignRandom {
  fn name(&self) -> String { "align-random".to_string() }
  fn run(&self, context: &mut Context) {
    let runner = Runner::default()
      .with_expr(&context.unaligned_eggroll().parse().unwrap())
      .run(&crate::eggroll::rewrite::rewrites());
    let choice_graph = ChoiceGraph::new(&runner.egraph, |_| None);


    let mut num_tries = 0;
    let mut num_path_timeouts = 0;
    let mut num_expr_timeouts = 0;
    let mut num_verification_fails = 0;
    let mut num_verification_timeouts = 0;


    println!("Trying to verify with random elements.");
    loop {
      let random_path = match self.random_path(&choice_graph) {
        Some(path) => path,
        None => {
          println!("Giving up constructing random path after 10 seconds");
          num_path_timeouts += 1;
          continue;
        }
      };

      let random_expr = match self.to_rec_expr(&random_path) {
        Some(expr) => expr,
        None => {
          println!("Giving up converting path to rec expr after 10 seconds");
          num_expr_timeouts += 1;
          continue;
        }
      };

      println!("Verifying");
      match self.attempt_verification(random_expr.clone(), &context) {
        Some(true) => {
          println!("Random verification succeeded after {} tries.", num_tries);
          context.aligned_eggroll.replace(random_expr);
          break;
        },
        Some(false) => {
          println!("Verification failed");
          num_verification_fails += 1;
        }
        None => {
          println!("Gave up trying to verify after 2 minutes.");
          num_verification_timeouts += 1;
        }
      }
      num_tries += 1;

      println!("------------------------");
      println!("Tries: {}", num_tries);
      println!("Path timeouts: {}", num_path_timeouts);
      println!("Expression timeouts: {}", num_expr_timeouts);
      println!("Verification timeouts: {}", num_verification_timeouts);
      println!("Verification failures: {}", num_verification_fails);
      println!();
    }
  }
}
