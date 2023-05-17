use clap::{Parser, ValueEnum};
use kestrel::annealer::*;
use kestrel::crel::{ast::*, blockify::*, state::*};
use kestrel::eggroll::cost_functions::*;
use kestrel::eggroll::milp_extractor::*;
use kestrel::names::*;
use kestrel::spec::{KestrelSpec, parser::parse_spec};
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

fn build_unaligned_crel(spec: &KestrelSpec, crel: &CRel) -> CRel {
  let (crel, fundefs) = kestrel::crel::fundef::extract_fundefs(crel);
  let left_fun = fundefs.get(&spec.left)
    .expect(format!("Function not found: {}", spec.left).as_str());
  let right_fun = fundefs.get(&spec.right)
    .expect(format!("Function not found: {}", spec.right).as_str());

  let left_fun = left_fun.map_vars(&|s: String| {
    format!("l_{}", s)
  });
  let right_fun = right_fun.map_vars(&|s: String| {
    format!("r_{}", s)
  });

  let new_main = CRel::FunctionDefinition {
    specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
    name: Declarator::Identifier{ name: "main".to_string() },
    params: vec!(),
    body: Box::new(Statement::Relation {
      lhs: Box::new(left_fun.body.blockify()),
      rhs: Box::new(right_fun.body.blockify()),
    }),
  };

  match crel {
    None => new_main,
    Some(CRel::Seq(crels)) => {
      crels.clone().push(new_main);
      CRel::Seq(crels)
    },
    Some(crel) => CRel::Seq(vec!{crel, new_main})
  }
}

fn main() {
  let args = Args::parse();
  let spec = parse_spec(&args.input).unwrap();

  let crel = kestrel::crel::parser::parse_c_file(args.input);
  println!("CRel:\n{:?}", crel);

  let unaligned_crel = build_unaligned_crel(&spec, &crel);
  println!("\nUnaliged CRel:\n{:?}", unaligned_crel);

  let unaligned_eggroll = unaligned_crel.to_eggroll();
  println!("\nUnaliged Eggroll:\n{:?}", unaligned_eggroll);

  let runner = Runner::default()
    .with_expr(&unaligned_eggroll.parse().unwrap())
    .run(&kestrel::eggroll::rewrite::make_rules());

  if args.dot {
    write_dot(runner.egraph.dot().to_string());
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
      let annealer = Annealer::new(&runner.egraph);
      let trace_states = rand_states_satisfying(3, &spec.pre);
      annealer.find_best(runner.roots[0], |expr| {
        kestrel::eggroll::cost_functions::sa_score(&trace_states, expr)
      })
    },
  };
  println!("\nAligned Eggroll:\n{}", aligned_eggroll.pretty(80));

  let aligned_crel = kestrel::eggroll::to_crel::eggroll_to_crel(&aligned_eggroll.to_string());
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
