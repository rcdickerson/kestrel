use crate::eggroll::ast::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use egg::*;
use std::collections::HashSet;

pub struct ComputeSpace { }

impl ComputeSpace {
  pub fn new() -> Self {
    ComputeSpace {}
  }
}

impl Task for ComputeSpace {
  fn name(&self) -> String { "compute-space".to_string() }

  fn run(&self, context: &mut Context) {
    let runner = Runner::default()
      .with_expr(&context.unaligned_eggroll().parse().unwrap())
      .run(&crate::eggroll::rewrite::rewrites());
    let seen = &mut HashSet::new();
    println!("\nAlignment space size: {}", space_size(&runner.egraph, runner.roots[0], seen));
  }
}

enum SpaceSize {
  Finite(usize),
  Infinite,
}
impl std::fmt::Display for SpaceSize {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      SpaceSize::Finite(size) => write!(f, "{}", size),
      SpaceSize::Infinite => write!(f, "Infinite"),
    }
  }
}

fn space_size(egraph: &EGraph<Eggroll, ()>,
              class: Id,
              seen: &mut HashSet<Id>) -> SpaceSize {
  if seen.contains(&class) {
    return SpaceSize::Infinite
  }
  seen.insert(class);
  let mut total = 0;
  for node in egraph[class].clone().nodes {
    let mut node_total = 1;
    for child in node.children() {
      match space_size(egraph, *child, seen) {
        SpaceSize::Infinite => return SpaceSize::Infinite,
        SpaceSize::Finite(child_size) => node_total *= child_size,
      }
    }
    total += node_total;
  }
  seen.remove(&class);
  SpaceSize::Finite(total)
}
