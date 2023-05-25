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

  /// Output file.
  #[arg(short, long)]
  output: Option<String>,

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

  /// Output the naive product program without doing any alignment.
  Unaligned,
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
  // println!("CRel:\n{:?}", crel);

  let (global_decls, unaligned_crel) = spec.build_unaligned_crel(&crel);
  // println!("\nUnaliged CRel:\n{:?}", unaligned_crel);

  let unaligned_c = unaligned_crel.to_c();
  println!("\nUnaligned Product Program");
  println!("--------------------------");
  println!("{}", unaligned_c);
  println!("--------------------------");

  let unaligned_eggroll = unaligned_crel.to_eggroll();
  // println!("\nUnaliged Eggroll:\n{:?}", unaligned_eggroll);

  let runner = Runner::default()
    .with_expr(&unaligned_eggroll.parse().unwrap())
    .run(&kestrel::eggroll::rewrite::make_rules());

  if args.dot {
    println!("Writing dot file to egraph.dot");
    write_file(&runner.egraph.dot().to_string(), "egraph.dot");
  }

  let aligned_eggroll = match args.extractor {
    ExtractorArg::Unaligned => {
      println!("Treating naive product as final alignment.");
      unaligned_eggroll.parse().unwrap()
    },
    ExtractorArg::CountLoops => {
      let extractor = Extractor::new(&runner.egraph, LocalCountLoops);
      let (_, best) = extractor.find_best(runner.roots[0]);
      println!("Computed alignment by local loop counting extraction.");
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
      let trace_states = rand_states_satisfying(num_trace_states, &spec.pre).iter()
        .map(|state| state.with_declarations(&global_decls, trace_fuel))
        .collect();
      annealer.find_best(max_iterations, runner.roots[0], |expr| {
        kestrel::eggroll::cost_functions::sa_score(&trace_states, trace_fuel, expr)
      })
    },
  };

  println!("\nAligned Eggroll");
  println!("--------------------------");
  println!("{}", aligned_eggroll.pretty(80));
  println!("--------------------------");

  let aligned_crel_raw = kestrel::eggroll::to_crel::eggroll_to_crel(&aligned_eggroll.to_string());
  let aligned_crel = spec.add_arb_inits(&aligned_crel_raw);
  // println!("\nAligned CRel:\n{:?}", aligned_crel);

  let aligned_c = aligned_crel.to_c();
  println!("\nAligned Product Program");
  println!("--------------------------");
  println!("{}", aligned_c);
  println!("--------------------------");

  args.output.map(|path| {
    println!("Writing output to {}...", path);
    let mut file = File::create(&path)
      .expect(format!("Error creating file: {}", path).as_ref());
    match file.write_all(aligned_c.as_bytes()) {
      Ok(_) => println!("Done"),
      Err(err) => panic!("Error writing output file: {}", err),
    }
  });
}
