use clap::{Parser, ValueEnum};
use kestrel::annealer::*;
use kestrel::crel::state::*;
use kestrel::eggroll::cost_functions::*;
use kestrel::eggroll::milp_extractor::*;
use kestrel::spec::parser::parse_spec;
use egg::*;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
  /// Input file.
  #[arg(short, long)]
  input: String,

  /// Output a dot file representation of the e-graph.
  #[arg(short, long)]
  dot: bool,

  /// Which technique to use for extracting the aligned program from the
  /// saturated e-graph.
  #[arg(value_enum, default_value_t = ExtractorArg::CountLoops)]
  extractor: ExtractorArg,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum ExtractorArg {
  /// Local cost function extractor that minimizes total number of loops.
  CountLoops,

  /// Non-local extraction which optimizes an objective function via
  /// mixed-integer linear programming.
  MILP,

  /// Non-local extraction which optimizes an objective function via simulated
  /// annealing.
  SA,
}

fn write_file(contents: &String, location: &str) {
  let path = Path::new(location);
  let mut dot_file = match File::create(&path) {
    Err(_) => panic!("Could not create file: {}", location),
    Ok(f)  => f,
  };
  dot_file.write_all(contents.as_bytes()).expect("Unable to write file.")
}

fn main() {
  let args = Args::parse();
  let spec = parse_spec(&args.input).unwrap();

  let crel = kestrel::crel::parser::parse_c_file(&args.input);
  println!("CRel:\n{:?}", crel);

  let unaligned_crel = spec.build_unaligned_crel(&crel);
  println!("\nUnaliged CRel:\n{:?}", unaligned_crel);

  let unaligned_c = unaligned_crel.to_c();
  println!("\nUnaliged C:\n{}", unaligned_c);

  let unaligned_eggroll = unaligned_crel.to_eggroll();
  println!("\nUnaliged Eggroll:\n{:?}", unaligned_eggroll);

  let runner = Runner::default()
    .with_expr(&unaligned_eggroll.parse().unwrap())
    .run(&kestrel::eggroll::rewrite::make_rules());

  if args.dot {
    write_file(&runner.egraph.dot().to_string(), "egraph.dot");
  }

  let aligned_eggroll = match args.extractor {
    ExtractorArg::CountLoops => {
      let extractor = Extractor::new(&runner.egraph, LocalCountLoops);
      let (_, best) = extractor.find_best(runner.roots[0]);
      best
    },
    ExtractorArg::MILP => {
      let mut extractor = MilpExtractor::new(&runner.egraph);
      extractor.solve(runner.roots[0])
    },
    ExtractorArg::SA => {
      let max_iterations = 3000;
      let num_trace_states = 10;
      let trace_fuel = 10000;

      let annealer = Annealer::new(&runner.egraph);
      let trace_states = rand_states_satisfying(num_trace_states, &spec.pre);
      annealer.find_best(max_iterations, runner.roots[0], |expr| {
        kestrel::eggroll::cost_functions::sa_score(&trace_states, trace_fuel, expr)
      })
    },
  };
  println!("\nAligned Eggroll:\n{}", aligned_eggroll.pretty(80));

  let aligned_crel = kestrel::eggroll::to_crel::eggroll_to_crel(&aligned_eggroll.to_string());
  println!("\nAligned CRel:\n{:?}", aligned_crel);

  println!("\nC:\n{}", aligned_crel.to_c());
}
