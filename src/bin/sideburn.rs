use clap::Parser;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
  /// Input file.
  #[arg(short, long)]
  input: String,
}

fn main() {
  let args = Args::parse();
  let crel = kestrel::crel::parser::parse_c_file(args.input);
  println!("CRel:\n{:?}", crel);
}
