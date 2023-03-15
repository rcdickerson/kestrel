mod crel;
mod crel_parser;

use clap::Parser;
use crate::crel_parser::parse_relc;

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
  println!("{:?}", parse_relc(args.input));
}
