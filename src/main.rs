mod crel;
mod eggroll;

use clap::Parser;
use egg::*;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
   /// Input file
   #[arg(short, long)]
   input: String,

   /// Output a dot file representation of the e-graph
   #[arg(short, long)]
   dot: bool,
}

fn main() {
  let args = Args::parse();

  let crel = crel::parser::parse_crel(args.input);
  println!("CRel:\n{:?}", crel);

  let crel_egg = crel::conversion::crel_to_egg(&crel);
  println!("\nCRel Egg:\n{:?}", crel_egg);

  let runner = Runner::default().with_expr(&crel_egg.parse().unwrap()).run(&eggroll::rewrite::make_rules());
  let extractor = Extractor::new(&runner.egraph, eggroll::cost_model::CostModel);
  let root = runner.roots[0];
  let (best_cost, best) = extractor.find_best(root);
  println!("\nAligned:\n{}", best);
  println!("Alignment cost: {}", best_cost);

  let aligned_egg = format!("{}", best);
  let aligned_crel = crel::conversion::egg_to_crel(&aligned_egg);

  println!("\nAligned CRel:\n{:?}", aligned_crel);

  println!("\nC:\n{}", aligned_crel.to_c());
}
