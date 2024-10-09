use crate::anneal::choice_graph::*;
use crate::workflow::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use egg::*;

pub struct AlignRandom {
  max_tries: usize,
}

impl AlignRandom {
  pub fn new(max_tries: usize) -> Self {
    AlignRandom { max_tries }
  }
}

impl Task for AlignRandom {
  fn name(&self) -> String { "align-random".to_string() }
  fn run(&self, context: &mut Context) {
    let runner = Runner::default()
      .with_expr(&context.unaligned_eggroll().parse().unwrap())
      .run(&crate::eggroll::rewrite::rewrites());
    let choice_graph = ChoiceGraph::new(&runner.egraph, |_| None);

    println!("Trying to verify with random elements, capped at {}", self.max_tries);
    let mut tries = 0;
    loop {
      println!("Try: {}", tries + 1);
      let random_path = choice_graph.random_path(&|_| true);
      let random_expr = random_path.to_rec_expr();

      println!("Verifying");
      let mut verification_context = context.clone();
      verification_context.aligned_eggroll.replace(random_expr.clone());
      let mut verification_workflow = Workflow::new(&mut verification_context);
      verification_workflow.add_task(AlignedCRel::new());
      verification_workflow.add_task(InvarsDaikon::new());
      verification_workflow.add_task(Houdafny::new());
      verification_workflow.execute();
      println!("Done with try");

      tries += 1;
      if verification_workflow.context().verified {
        println!("Random verification succeeded after {} tries.", tries);
        context.aligned_eggroll.replace(random_expr);
        break;
      }
      if tries >= self.max_tries {
        context.aligned_eggroll.replace(random_expr);
        break;
      }
    }

  }
}
