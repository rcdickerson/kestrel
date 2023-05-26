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

/// The high-level KestRel workflow is:
///   1. Read in a C file and parse its @KESTREL spec.
///   2. Convert the C into CRel. CRel is an IR which can represent C-like
///      relational control flow structures.
///   3. Convert the CRel into Eggroll, an s-expression based representation
///      of CRel defined in the way the Egg library expects languages.
///   4. Hand the Eggroll off to Egg and ask Egg to perform equality saturation.
///   5. Extract an aligned program using the technique requested by the user.
///   6. Convert the extracted Eggroll back to CRel, and then into a C product
///      program.
///
/// The reason we have two IRs (CRel and Eggroll) is to separate two orthogonal
/// translation concerns: 1) converting non-relational programs into relational
/// ones, and 2) packaging C-like programs into an Egg-compatible language
/// definition.
fn main() {
  let args = Args::parse();
  let spec = parse_spec(&args.input).unwrap();

  let crel = kestrel::crel::parser::parse_c_file(&args.input);
  let (global_decls, unaligned_crel) = spec.build_unaligned_crel(&crel);

  let unaligned_c = unaligned_crel.to_c();
  println!("\nUnaligned Product Program");
  println!("--------------------------");
  println!("{}", unaligned_c);
  println!("--------------------------");

  let unaligned_eggroll = unaligned_crel.to_eggroll();
  let runner = Runner::default()
    .with_expr(&unaligned_eggroll.parse().unwrap())
    .run(&kestrel::eggroll::rewrite::make_rules());

  if args.dot {
    println!("Writing egraph structure to egraph.dot");
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
      println!("Computed alignment by local loop counting.");
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

  let aligned_crel_no_specs =
    kestrel::eggroll::to_crel::eggroll_to_crel(&aligned_eggroll.to_string());
  let aligned_crel = spec.add_specs_to_main(&aligned_crel_no_specs);
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
