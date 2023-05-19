use clap::{Parser, ValueEnum};
use egg::*;
use kestrel::crel::{ast::*, state::*};
use kestrel::eggroll::{ast::*, cost_functions::*, to_crel::*};
use kestrel::spec::{KestrelSpec, parser::parse_spec};
use regex::Regex;
use std::fs;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum SideburnMode {
  PrintEggroll,
  PrintSA,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum InputMode {
  C,
  Eggroll,
}

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
  /// Input file.
  #[arg(short, long)]
  input_file: String,

  /// Auxillary specification file, if needed.
  #[arg(short, long)]
  spec_file: Option<String>,

  /// Which type of file is being input.
  #[arg(value_enum, default_value_t = InputMode::C)]
  input_mode: InputMode,

  /// Which sideburn mode to run.
  #[arg(value_enum, default_value_t = SideburnMode::PrintEggroll)]
  run_mode: SideburnMode,
}

struct Input {
  spec: KestrelSpec,
  crel: CRel,
  eggroll: RecExpr<Eggroll>,
}

impl Input {

  fn read_c_file(input_file: &String) -> Self {
    let spec = parse_spec(input_file).unwrap();
    let raw_crel = kestrel::crel::parser::parse_c_file(input_file);
    let crel = spec.build_unaligned_crel(&raw_crel);
    let eggroll_str = crel.to_eggroll();
    let eggroll = eggroll_str.parse().unwrap();
    Input{spec, crel, eggroll}
  }

  fn read_eggroll_file(spec_file: &String, eggroll_file: &String) -> Self {
    let spec = parse_spec(spec_file).unwrap();
    let eggroll_raw_str = fs::read_to_string(eggroll_file).unwrap();
    let newlines = Regex::new(r"\n+").unwrap();
    let eggroll_str = newlines.replace_all(eggroll_raw_str.as_str(), " ").to_string();
    let eggroll = eggroll_str.parse().unwrap();
    let crel = eggroll_to_crel(&eggroll_str);
    Input{spec, crel, eggroll}
  }

  fn main_body(&self) -> Statement {
    kestrel::crel::fundef::extract_fundefs(&self.crel).1
      .get(&"main".to_string())
      .expect("Missing main function")
      .body.clone()
  }

  fn print_eggroll(&self) {
    println!("{}", self.eggroll.pretty(80));
  }
}

fn main() {
  let args = Args::parse();
  let input = match args.input_mode {
    InputMode::C => Input::read_c_file(&args.input_file),
    InputMode::Eggroll => {
      let spec_file = args.spec_file
        .expect("Must provide a specification file for eggroll input.");
      Input::read_eggroll_file(&spec_file, &args.input_file)
    },
  };

  match args.run_mode {
    SideburnMode::PrintEggroll => {
      input.print_eggroll();
    },
    SideburnMode::PrintSA => {
      input.print_eggroll();
      let state = &rand_states_satisfying(1, &input.spec.pre)[0];
      let trace = kestrel::crel::eval::run(&input.main_body(), state.clone(), 100);
      SAScore::score_trace(&input.crel, &trace).print();
    },
  }
}
