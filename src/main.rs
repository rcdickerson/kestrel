mod crel;

use clap::Parser;

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
  let crel_egg = crel::writer::crel_to_egg(&crel);
  let c = crel::writer::crel_to_c(&crel);
  println!("CRel:\n{:?}", crel);
  println!("CRel Egg:\n{:?}", crel_egg);
  println!("\nC:\n{}", c);
}
