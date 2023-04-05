mod crel;
mod eggroll;

use clap::{Parser, ValueEnum};
use crate::eggroll::cost_functions::*;
use crate::eggroll::milp_extractor::*;
use egg::*;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
  /// Input file
  #[arg(short, long)]
  input: String,

  /// Output a dot file representation of the e-graph
  #[arg(short, long)]
  dot: bool,

  /// Type of extractor to use
  #[arg(value_enum, default_value_t = ExtractorArg::MILP)]
  extractor: ExtractorArg,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum ExtractorArg {
  /// Local cost function extractor that minimizes total number of loops
  CountLoops,

  /// Non-local cost function extractor that optimizes for good alignments
  MILP,
}

fn main() {
  let args = Args::parse();

  let crel = crel::parser::parse_crel(args.input);
  println!("CRel:\n{:?}", crel);

  let crel_eggroll = crel.to_eggroll();
  println!("\nEggroll:\n{:?}", crel_eggroll);

  let runner = Runner::default()
    .with_expr(&crel_eggroll.parse().unwrap())
    .run(&eggroll::rewrite::make_rules());

  if args.dot {
    write_dot(runner.egraph.dot().to_string());
  }

  let aligned_eggroll = match args.extractor {
    ExtractorArg::CountLoops => {
      let extractor = Extractor::new(&runner.egraph, CountLoops);
      let (_, best) = extractor.find_best(runner.roots[0]);
      best.to_string()
    },
    ExtractorArg::MILP => {
      let mut extractor = MilpExtractor::new(&runner.egraph);
      extractor.solve(runner.roots[0]).to_string()
    },
  };
  println!("\nAligned Eggroll:\n{}", aligned_eggroll);

  let aligned_crel = eggroll::to_crel::eggroll_to_crel(&aligned_eggroll);
  println!("\nAligned CRel:\n{:?}", aligned_crel);

  println!("\nC:\n{}", aligned_crel.to_c());
}

fn write_dot(dot: String) {
  let dot_path = Path::new("egraph.dot");
  let mut dot_file = match File::create(&dot_path) {
    Err(_) => panic!("Could not create dot file."),
    Ok(f)  => f,
  };
  dot_file.write_all(dot.as_bytes()).expect("Unable to write dot file.")
}
