mod annealer;
mod crel;
mod eggroll;
mod names;
mod spec;

use clap::{Parser, ValueEnum};
use crate::crel::ast::*;
use crate::eggroll::cost_functions::*;
use crate::eggroll::milp_extractor::*;
use crate::names::*;
use crate::spec::{KestrelSpec, parser::parse_spec};
use egg::*;
use std::collections::HashMap;
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
  let (crel, fundefs) = extract_fundefs(spec.left.as_str(), crel);
  let left_fun = fundefs.get(&spec.left).expect(format!("Function not found: {}", spec.left).as_str());
  let right_fun = fundefs.get(&spec.right).expect(format!("Function not found: {}", spec.right).as_str());

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
      lhs: Box::new(left_fun.body),
      rhs: Box::new(right_fun.body),
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

fn extract_fundefs(name: &str, crel: &CRel) -> (Option<CRel>, HashMap<String, FunDef>) {
  match crel {
    CRel::Declaration{ specifiers: _, declarators: _ } => {
      (Some(crel.clone()), HashMap::new())
    },
    CRel::FunctionDefinition{ specifiers: _, name, params: _, body } => {
      let name = match name {
        Declarator::Identifier{name} => name.clone(),
      };
      let mut map = HashMap::new();
      map.insert(name, FunDef{
        body: *body.clone(),
      });
      (None, map)
    },
    CRel::Seq(crels) => {
      let (crels, defs): (Vec<_>, Vec<_>) = crels.iter()
        .map(|c| extract_fundefs(name, c))
        .unzip();
      let crels: Vec<_> = crels.iter().flatten().map(|c| (*c).clone()).collect();
      let mut def_union = HashMap::new();
      for def in defs {
        def_union.extend(def);
      }
      ( if crels.len() > 0 { Some(CRel::Seq(crels)) } else { None }, def_union )
    },
  }
}

#[derive(Clone, Debug)]
struct FunDef {
  // TODO: Params, initialized to arbitrary values.
  body: Statement,
}
impl MapVars for FunDef {
  fn map_vars<F>(&self, f: &F) -> Self
    where F: Fn(String) -> String
  {
    FunDef{body: self.body.map_vars(f)}
  }
}

fn main() {
  let args = Args::parse();

  let spec = parse_spec(&args.input).unwrap();

  let crel = crel::parser::parse_c_file(args.input);
  println!("CRel:\n{:?}", crel);

  let unaligned_crel = build_unaligned_crel(&spec, &crel);
  println!("\nUnaliged CRel:\n{:?}", crel);

  let unaligned_eggroll = unaligned_crel.to_eggroll();
  println!("\nUnaliged Eggroll:\n{:?}", unaligned_eggroll);

  let runner = Runner::default()
    .with_expr(&unaligned_eggroll.parse().unwrap())
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
    ExtractorArg::SA => {
      panic!("unimplemented")
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
