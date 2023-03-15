mod crel;
mod crel_parser;
mod crel_writer;

use clap::Parser;
use crate::crel_parser::parse_crel;
use crate::crel_writer::crel_to_c;

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
  let c = crel_to_c(&crel);
  println!("RelC:\n{:?}", crel);
  println!("\nC:\n{}", c);
}
