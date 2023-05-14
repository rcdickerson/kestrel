mod annealer;
mod crel;
mod eggroll;
mod names;
mod spec;

use clap::{Parser, ValueEnum};
use crate::annealer::*;
use crate::crel::{ast::*, bblock::*};
use crate::eggroll::ast::*;
use crate::eggroll::cost_functions::*;
use crate::eggroll::milp_extractor::*;
use crate::names::*;
use crate::spec::{KestrelSpec, parser::parse_spec};
use egg::*;
use std::collections::HashMap;
use std::collections::HashSet;
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
  let (crel, fundefs) = extract_fundefs(crel);
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

fn extract_fundefs(crel: &CRel) -> (Option<CRel>, HashMap<String, FunDef>) {
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
        .map(|c| extract_fundefs(c))
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
  println!("\nUnaliged CRel:\n{:?}", unaligned_crel);

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
      best
    },
    ExtractorArg::MILP => {
      let mut extractor = MilpExtractor::new(&runner.egraph);
      extractor.solve(runner.roots[0])
    },
    ExtractorArg::SA => {
      let annealer = Annealer::new(&runner.egraph);
      annealer.find_best(runner.roots[0], |expr| {
        let crel = eggroll::to_crel::eggroll_to_crel(&expr.to_string());
        let body = extract_fundefs(&crel).1
          .get(&"main".to_string())
          .expect("Missing main function")
          .body.clone();
//        let trace = crel::trace::run(&body, crel::trace::state(vec!(("l_n", 5), ("r_n", 5))), 100);
        let trace = crel::trace::run(&body, crel::trace::state(vec!(("l_x", 5), ("r_x", 5))), 100);
        let loop_heads = crel::trace::loop_heads(&trace);
        let rel_states = crel::trace::relation_states(&trace);

        let num_rels = rel_states.len() as i32;
        let score_rel_size = if num_rels == 0 {
          1.0
        } else {
          let sum : usize = rel_states.iter().map(|v| v.len()).sum();
          (sum as f32) / (num_rels as f32) / (trace.len() as f32)
        };

        let mut similarity_sum : f32 = 0.0;
        for head_states in &loop_heads {
          if head_states.len() == 0 { continue }

          let mut l_vals : HashMap<String, Vec<i32>> = HashMap::new();
          let mut r_vals : HashMap<String, Vec<i32>> = HashMap::new();
          for head_state in head_states {
            for (exec_var, val) in head_state {
              let(exec, var) = (&exec_var[..1], &exec_var[2..]);
              match exec {
                "l" => {
                  let mut seq = match l_vals.get(var) {
                    None => Vec::new(),
                    Some(seq) => seq.clone(),
                  };
                  seq.push(val.clone());
                  l_vals.insert(var.to_string(), seq);
                },
                "r" => {
                  let mut seq = match r_vals.get(var) {
                    None => Vec::new(),
                    Some(seq) => seq.clone(),
                  };
                  seq.push(val.clone());
                  r_vals.insert(var.to_string(), seq);
                },
                _ => continue,
              }
            }
          }

          let mut l_diffs = HashMap::new();
          for (k,v) in &l_vals {
            let diffs = v.windows(2).map(|w| w[1] - w[0]).collect::<Vec<i32>>();
            if diffs.len() > 0 && !diffs.iter().all(|i| *i == 0) {
              l_diffs.insert(k.clone(), diffs);
            }
          }

          let mut r_diffs = HashMap::new();
          for (k,v) in &r_vals {
            let diffs = v.windows(2).map(|w| w[1] - w[0]).collect::<Vec<i32>>();
            if diffs.len() > 0 && !diffs.iter().all(|i| *i == 0) {
              r_diffs.insert(k.clone(), diffs);
            }
          }

          let l_keys : HashSet<&String> = HashSet::from_iter(l_diffs.keys());
          let r_keys : HashSet<&String> = HashSet::from_iter(r_diffs.keys());
          let keys = l_keys.union(&r_keys).collect::<HashSet<&&String>>();

          let mut matching : f32 = 0.0;
          for var in &keys {
            let left = l_diffs.get(**var);
            let right = r_diffs.get(**var);
            match (left, right) {
              (None, _) => continue,
              (_, None) => continue,
              (Some(left), Some(right)) => {
                let ratios = left.iter().zip(right)
                  .map(|(l,r)| (l / r, l % r))
                  .collect::<Vec<(i32, i32)>>();
                let homogeneous = ratios.iter()
                  .all(|(d,m)| *d == ratios[0].0 && *m == ratios[0].1);
                //if homogeneous { matching += 1; }
                if l_vals.get(**var) == r_vals.get(**var) {
                  matching += 1.0;
                } else if homogeneous {
                  matching += 0.5;
                }
              },
            }
          }
          similarity_sum += (matching as f32) / (keys.len() as f32);
        }
        let score_similarity = 1.0 - (similarity_sum / loop_heads.len() as f32);

        (0.5 * score_rel_size) + (0.5 * score_similarity)
      })
    },
  };
  println!("\nAligned Eggroll:\n{}", aligned_eggroll.pretty(80));

  let aligned_crel = eggroll::to_crel::eggroll_to_crel(&aligned_eggroll.to_string());
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
