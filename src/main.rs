use clap::{Parser, ValueEnum};
use kestrel::output_mode::*;
use kestrel::spec::parser::parse_spec;
use kestrel::unaligned::*;
use kestrel::workflow::*;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
  /// Input file.
  #[arg(short, long)]
  input: String,

  /// Output file.
  #[arg(short, long)]
  output: Option<String>,

  /// Output format.
  #[arg(long, value_enum, default_value_t = OutputMode::Seahorn)]
  output_mode: OutputMode,

  /// Verbose.
  #[arg(short, long)]
  verbose: bool,

  /// Output a dot file representation of the e-graph.
  #[arg(short, long)]
  dot: bool,

  /// Which technique to use for extracting the aligned program from the
  /// saturated e-graph.
  #[arg(value_enum, default_value_t = ExtractorArg::CountLoops)]
  extractor: ExtractorArg,

  /// How many iterations to use when running simulated annealing.
  #[arg(long, default_value_t=3000)]
  sa_max_iterations: usize,

  /// Start simulated annealing from a random element instead of
  /// count loops alignment.
  #[arg(long)]
  sa_start_random: bool,

  /// Count and print the size of the alignment state space.
  #[arg(short, long)]
  space_size: bool,
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

  /// Output the naive product program without doing any alignment.
  Unaligned,
}

/// The high-level KestRel workflow is:
///   1. Read in a C file and parse its @KESTREL spec.
///   2. Convert the C into CRel. CRel is a C-like IR which can represent
///      relational control flow structures.
///   3. Convert the CRel into Eggroll, an s-expression based representation
///      of CRel defined in the way the Egg library expects languages.
///   4. Hand the Eggroll off to Egg and ask Egg to perform equality saturation.
///   5. Extract an aligned program using the technique requested by the user.
///   6. Convert the extracted Eggroll back to CRel, and then into a C product
///      program.
///
/// The reason we have two IRs (CRel and Eggroll) is to separate two
/// orthogonal translation concerns: 1) converting between
/// non-relational and relational programs, and 2) packaging programs
/// into an Egg-compatible language definition.
fn main() {
  let args = Args::parse();
  let spec = parse_spec(&args.input).unwrap();
  let raw_crel = kestrel::crel::parser::parse_c_file(&args.input);
  let unaligned_crel = UnalignedCRel::from(&raw_crel, &spec);
  let unaligned_eggroll = unaligned_crel.main.to_eggroll();

  let mut context = Context::new();
  context.spec = Some(&spec);
  context.unaligned_crel = Some(&unaligned_crel);
  context.unaligned_eggroll = Some(&unaligned_eggroll);
  context.output_path = args.output.clone();

  let mut workflow = Workflow::new(context);
  if args.verbose {
    workflow.add_task(PrintInfo::with_header("Unaligned Product Program", &|ctx| {
      ctx.unaligned_crel().main.to_c().to_string()
    }));
  }
  if args.dot { workflow.add_task(WriteDot::new()) }
  if args.space_size { workflow.add_task(ComputeSpace::new()) }
  match args.extractor {
    ExtractorArg::Unaligned => workflow.add_task(AlignNone::new()),
    ExtractorArg::CountLoops => workflow.add_task(AlignCountLoops::new()),
    ExtractorArg::MILP => workflow.add_task(AlignMilp::new()),
    ExtractorArg::SA => workflow.add_task(AlignSa::new(args.sa_start_random, args.sa_max_iterations)),
  }
  workflow.add_task(AlignedCRel::new());
  workflow.add_task(InvarsDaikon::new());
  workflow.add_task(Houdafny::new());
  workflow.add_task(AlignedOutput::new(args.output_mode));
  match args.output {
    Some(_) => workflow.add_task(WriteProduct::new(args.output_mode)),
    None => workflow.add_task(PrintInfo::with_header("Aligned Product Program", &|ctx| {
      ctx.aligned_output().clone()
    })),
  }
  workflow.execute();
  println!("Done!");
}
