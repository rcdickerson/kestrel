mod crel;
mod crel_parser;
mod crel_writer;

use clap::Parser;
use crate::crel_parser::parse_crel;
use crate::crel_writer::{crel_to_c, crel_to_egg};

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
  let crel = parse_crel(args.input);
  let crel_egg = crel_to_egg(&crel);
  let c = crel_to_c(&crel);
  println!("CRel:\n{:?}", crel);
  println!("CRel Egg:\n{:?}", crel_egg);
  println!("\nC:\n{}", c);
}
