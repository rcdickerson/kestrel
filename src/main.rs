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

}
