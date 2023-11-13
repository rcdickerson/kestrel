use clap::{Parser, ValueEnum};
use kestrel::annealer::*;
use kestrel::crel::eval::*;
use kestrel::eggroll::cost_functions::{minloops::*, sa::*};
use kestrel::eggroll::milp_extractor::*;
use kestrel::output_mode::*;
use kestrel::spec::parser::parse_spec;
use kestrel::unaligned::*;
use egg::*;
use std::collections::HashSet;
use std::fs::File;
use std::io::prelude::*;
use std::path::{Path, PathBuf};

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
  /// Input file.
  #[arg(short, long)]
  input: String,

  /// Output file.
  #[arg(short, long)]
  output: Option<String>,

  /// Output format.
  #[arg(long, value_enum, default_value_t = OutputMode::Seahorn)]
  output_mode: OutputMode,

  /// Output a dot file representation of the e-graph.
  #[arg(short, long)]
  dot: bool,

  /// Which technique to use for extracting the aligned program from the
  /// saturated e-graph.
  #[arg(value_enum, default_value_t = ExtractorArg::CountLoops)]
  extractor: ExtractorArg,

  /// How many iterations to use when running simulated annealing.
  #[arg(long, default_value_t=3000)]
  sa_max_iterations: usize,

  /// Start simulated annealing from a random element instead of
  /// count loops alignment.
  #[arg(long)]
  sa_start_random: bool,

  /// Count and print the size of the alignment state space.
  #[arg(short, long)]
  space_size: bool,
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
///   2. Convert the C into CRel. CRel is a C-like IR which can represent
///      relational control flow structures.
///   3. Convert the CRel into Eggroll, an s-expression based representation
///      of CRel defined in the way the Egg library expects languages.
///   4. Hand the Eggroll off to Egg and ask Egg to perform equality saturation.
///   5. Extract an aligned program using the technique requested by the user.
///   6. Convert the extracted Eggroll back to CRel, and then into a C product
///      program.
///
/// The reason we have two IRs (CRel and Eggroll) is to separate two
/// orthogonal translation concerns: 1) converting between
/// non-relational and relational programs, and 2) packaging programs
/// into an Egg-compatible language definition.
fn main() {
  let args = Args::parse();
  let spec = parse_spec(&args.input).unwrap();

  let crel = kestrel::crel::parser::parse_c_file(&args.input);
  // println!("\nCRel");
  // println!("--------------------------");
  // println!("{:?}", crel);
  // println!("--------------------------");

  let unaligned_crel = UnalignedCRel::from(&crel, &spec);

  let unaligned_c = unaligned_crel.main.to_c();
  println!("\nUnaligned Product Program");
  println!("--------------------------");
  println!("{}", unaligned_c);
  println!("--------------------------");

  let unaligned_eggroll = unaligned_crel.main.to_eggroll();
  println!("\nUnaligned Eggroll");
  println!("--------------------------");
  let ue_expr: RecExpr<kestrel::eggroll::ast::Eggroll> = unaligned_eggroll.parse().unwrap();
  println!("{}", ue_expr.pretty(80));
  println!("--------------------------");

  if args.dot {
    println!("Writing egraph structure to egraph.dot");
      let runner = Runner::default()
        .with_expr(&unaligned_eggroll.parse().unwrap())
        .run(&kestrel::eggroll::rewrite::eggroll_rules_with_unroll());
    write_file(&runner.egraph.dot().to_string(), "egraph.dot");
  }

  if args.space_size {
    let runner = Runner::default()
      .with_expr(&unaligned_eggroll.parse().unwrap())
      .run(&kestrel::eggroll::rewrite::eggroll_rules_with_unroll());
    let seen = &mut HashSet::new();
    println!("Alignment space size: {}", space_size(&runner.egraph, runner.roots[0], seen));
  }

  let aligned_eggroll = match args.extractor {
    ExtractorArg::Unaligned => {
      println!("Treating naive product as final alignment.");
      unaligned_eggroll.parse().unwrap()
    },
    ExtractorArg::CountLoops => {
      let runner = Runner::default()
        .with_expr(&unaligned_eggroll.parse().unwrap())
        .run(&kestrel::eggroll::rewrite::eggroll_rules());
      let extractor = Extractor::new(&runner.egraph, MinLoops);
      let (_, best) = extractor.find_best(runner.roots[0]);
      println!("Computed alignment by local loop counting.");
      best
    },
    ExtractorArg::MILP => {
      let runner = Runner::default()
        .with_expr(&unaligned_eggroll.parse().unwrap())
        .run(&kestrel::eggroll::rewrite::eggroll_rules_with_unroll());
      let mut extractor = MilpExtractor::new(&runner.egraph);
      extractor.solve(runner.roots[0])
    },
    ExtractorArg::SA => {
      let num_trace_states = 10;
      let trace_fuel = 10000;

      let init_runner = Runner::default()
        .with_expr(&unaligned_eggroll.parse().unwrap())
        .run(&kestrel::eggroll::rewrite::eggroll_rules());
      let init = if args.sa_start_random { None } else {
        let extractor = Extractor::new(&init_runner.egraph, MinLoops);
        let (_, initial) = extractor.find_best(init_runner.roots[0]);
        println!("\nPre-SA Initial Alignment");
        println!("--------------------------");
        println!("{}", initial.pretty(80));
        println!("--------------------------");
        Some(initial)
      };

      let runner = Runner::default()
        .with_expr(&init.clone().unwrap_or(unaligned_eggroll.parse().unwrap()))
        .run(&kestrel::eggroll::rewrite::eggroll_rules_with_unroll());
      let (_, fundefs) = kestrel::crel::fundef::extract_fundefs(&crel);
      let generator = fundefs.get(&"_generator".to_string());
      let decls = unaligned_crel.global_decls_and_params();
      let trace_states = rand_states_satisfying(
        num_trace_states, &spec.pre, Some(&decls), generator, 1000);
      let annealer = Annealer::new(&runner.egraph);
      annealer.find_best(args.sa_max_iterations, runner.roots[0], init,
                         |expr| { sa_score(&trace_states, trace_fuel, expr) })
    },
  };

  println!("\nAligned Eggroll");
  println!("--------------------------");
  println!("{}", aligned_eggroll.pretty(80));
  println!("--------------------------");

  let aligned_crel =
    kestrel::eggroll::to_crel::eggroll_to_crel(&aligned_eggroll.to_string(),
                                               Some(args.output_mode.options()));
  let filename = args.output.as_ref().map(|outpath| {
    let path = Path::new(outpath);
    path.file_name().unwrap().to_str().unwrap().to_string()
  });
  let aligned_c = args.output_mode.crel_to_c(
    &aligned_crel, &spec, unaligned_crel.global_decls, &filename);
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
    if args.output_mode == OutputMode::SvComp {
      let mut yaml_pathbuf = PathBuf::from(path);
      yaml_pathbuf.set_extension("yml");
      let yaml_path = yaml_pathbuf.to_str().unwrap();
      println!("Writing yaml to {}...", yaml_path);
      let mut file = File::create(&yaml_path)
        .expect(format!("Error creating file: {}", yaml_path).as_ref());
      match file.write_all(svcomp_yaml(&filename.unwrap()).as_bytes()) {
        Ok(_) => println!("Done"),
        Err(err) => panic!("Error writing output file: {}", err),
      }
    }
  });
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

fn space_size(egraph: &EGraph<kestrel::eggroll::ast::Eggroll, ()>,
              class: Id,
              seen: &mut HashSet<Id>) -> SpaceSize {
  if seen.contains(&class) {
    return SpaceSize::Infinite
  }
  seen.insert(class);
  let mut total = 0;
  for node in egraph[class.clone()].clone().nodes {
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

fn svcomp_yaml(filename: &String) -> String {
format!(
"format_version: '2.0'

input_files: '{}'

properties:
  - property_file: ../properties/unreach-call.prp
    expected_verdict: true

options:
  language: C
  data_model: ILP32
", filename)
}
