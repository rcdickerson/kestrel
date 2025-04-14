//! The main entry point for KestRel executions.

use clap::{Parser, ValueEnum};
use kestrel::crel::unaligned::*;
use kestrel::elaenia::parser::parse_elaenia_spec;
use kestrel::elaenia::tasks::elaenia_context::ElaeniaContext;
use kestrel::elaenia::tasks::insert_specs::*;
use kestrel::elaenia::tasks::solve_sketch::*;
use kestrel::elaenia::tasks::write_sketch::*;
use kestrel::kestrel_context::KestrelContext;
use kestrel::output_mode::*;
use kestrel::spec::parser::parse_kestrel_spec;
use kestrel::workflow::*;
use kestrel::workflow::context::*;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
  /// Input file.
  #[arg(short, long)]
  input: String,

  /// Specification format.
  #[arg(long, value_enum, default_value_t = SpecFormat::Kestrel)]
  spec_format: SpecFormat,

  /// Output file.
  #[arg(short, long)]
  output: Option<String>,

  /// Output format.
  #[arg(long, value_enum, default_value_t = OutputMode::Dafny)]
  output_mode: OutputMode,

  /// Append verification summary data as a comma-separated value line
  /// in the given file. Useful for collecting results over batches of
  /// verification tasks.
  #[arg(long)]
  output_summary: Option<String>,

  /// Write per-task timings to the given file.
  #[arg(long)]
  output_timings: Option<String>,

  /// Output a dot file representation of the e-graph.
  #[arg(short, long)]
  dot: bool,

  /// Which technique to use for extracting the aligned program from the
  /// saturated e-graph.
  #[arg(value_enum, default_value_t = ExtractorArg::SA)]
  extractor: ExtractorArg,

  /// If set, infers invariants via Houdini-style refinement.
  #[arg(long)]
  infer_invariants: bool,

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

  /// Provide verbose output.
  #[arg(short, long)]
  verbose: bool,


  // Ablation study flags for cost function.

  /// Disable loop fusion counting in the cost function.
  #[arg(long)]
  af_fusion: bool,

  /// Disable runoff loop iteration counting in the cost function.
  #[arg(long)]
  af_runoffs: bool,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum SpecFormat {
  /// Default Kestrel specification format; everything is universally
  /// quantified.
  Kestrel,

  /// Elaenia forall-exists specification format.
  Elaenia,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum ExtractorArg {
  /// Local cost function extractor that minimizes total number of loops.
  CountLoops,

  /// Non-local extraction which optimizes an objective function via simulated
  /// annealing.
  SA,

  /// Output the naive product program without doing any alignment.
  Unaligned,
}

impl ExtractorArg {
  fn tag(&self) -> String {
    match self {
      ExtractorArg::CountLoops => "count-loops".to_string(),
      ExtractorArg::SA         => "sa".to_string(),
      ExtractorArg::Unaligned  => "unaligned".to_string(),
    }
  }
}

fn main() {
  let args = Args::parse();
  match args.spec_format {
    SpecFormat::Kestrel => kestrel_workflow(args),
    SpecFormat::Elaenia => elaenia_workflow(args),
  };
}

/// The high-level KestRel workflow is:
///   1. Read in a C file and parse its @KESTREL spec.
///   2. Convert the C into CRel. CRel is a C-like IR which can represent
///      relational control flow structures.
///   3. Convert the CRel into Eggroll, an s-expression based representation
///      of CRel defined in the way the Egg library expects languages.
///   4. Hand the Eggroll off to Egg and ask Egg to perform equality saturation.
///   5. Extract an aligned program using the technique requested by the user.
///   6. Convert the extracted Eggroll back to CRel, and then into a
///      final product program.
///
/// The reason we have two IRs (CRel and Eggroll) is to separate two
/// orthogonal translation concerns: 1) converting between
/// non-relational and relational programs, and 2) packaging programs
/// into an Egg-compatible language definition.
fn kestrel_workflow(args: Args) {
  let mut raw_crel = kestrel::crel::parser::parse_c_file(&args.input);
  if args.extractor == ExtractorArg::Unaligned {
    // Annotated invariants are relational.
    raw_crel.clear_invariants();
  }

  let spec = parse_kestrel_spec(&args.input).unwrap();
  let unaligned_crel = UnalignedCRel::from_kestrel_spec(&raw_crel, &spec);
  let unaligned_eggroll = unaligned_crel.unaligned_main.to_eggroll();

  let mut context = KestrelContext::new(args.input.clone(), spec);
  context.accept_unaligned_crel(unaligned_crel);
  context.accept_unaligned_eggroll(unaligned_eggroll);
  args.output.as_ref().map(|output_path| {
    context.accept_output_path(output_path.clone());
  });

  let mut workflow = Workflow::new(context);
  if args.verbose {
    workflow.add_task(PrintInfo::with_header("Unaligned Product Program",
        &|ctx: &KestrelContext| {
          ctx.unaligned_crel().as_ref()
            .expect("Missing unaligned CRel")
            .unaligned_main.to_c().to_string()
        }));
  }
  if args.dot { workflow.add_task(WriteDot::new()) }
  if args.space_size { workflow.add_task(ComputeSpace::new()) }
  match args.extractor {
    ExtractorArg::Unaligned => workflow.add_task(AlignNone::new()),
    ExtractorArg::CountLoops => workflow.add_task(AlignCountLoops::new()),
    ExtractorArg::SA => {
      if !args.sa_start_random {
        workflow.add_task(AlignCountLoops::new());
        workflow.add_task(AlignedCRel::new());
        if args.infer_invariants {
          workflow.add_task(InvarsDaikon::new(None));
          workflow.add_task(Houdafny::new(None));
        }
      }
      let mut align_sa_task = AlignSa::new(args.sa_start_random, args.sa_max_iterations);
      if args.af_fusion  { align_sa_task.ablate_fusion() }
      if args.af_runoffs { align_sa_task.ablate_runoffs() }
      workflow.add_task_unless_verifed(align_sa_task);
    },
  }
  workflow.add_task_unless_verifed(AlignedCRel::new());
  if args.infer_invariants {
    workflow.add_task_unless_verifed(InvarsDaikon::new(None));
    workflow.add_task_unless_verifed(Houdafny::new(None));
  }
  workflow.add_task(AlignedOutput::new(args.output_mode));
  match args.output {
    Some(_) => workflow.add_task(WriteProduct::new(args.output_mode)),
    None => workflow.add_task(PrintInfo::with_header("Aligned Product Program",
        &|ctx: &KestrelContext| {
          ctx.aligned_output().as_ref().expect("Missing aligned output").clone()
        })),
  }
  workflow.add_task(PrintInfo::with_header("Per-Task Times (ms)",
      &|ctx: &KestrelContext| {
        let mut lines = Vec::new();
        for (task_name, duration) in &ctx.task_timings() {
          lines.push(format!("{}: {}", task_name, duration.as_millis()));
        }
        lines.join("\n") + "\n"
      }));
  args.output_summary.map(|location| {
    workflow.add_task(WriteSummary::new(location, vec!(args.extractor.tag())));
  });

  workflow.execute();

  println!("KestRel completed in {}ms", workflow.context().total_elapsed_time().as_millis());
  println!("Verified: {}", workflow.context().is_verified());
}


fn elaenia_workflow(args: Args) {
  let mut raw_crel = kestrel::crel::parser::parse_c_file(&args.input);
  if args.extractor == ExtractorArg::Unaligned {
    // Annotated invariants are relational.
    raw_crel.clear_invariants();
  }

  let spec = parse_elaenia_spec(&args.input).unwrap();
  let unaligned_crel = UnalignedCRel::from_elaenia_spec(&raw_crel, &spec);
  let unaligned_eggroll = unaligned_crel.unaligned_main.to_eggroll();

  println!("Unaligned CRel: {:?}", unaligned_crel.clone());

  let mut context = ElaeniaContext::new(args.input.clone(), spec);
  context.accept_unaligned_crel(unaligned_crel);
  context.accept_unaligned_eggroll(unaligned_eggroll);
  // args.output.as_ref().map(|output_path| {
  //   context.accept_output_path(output_path.clone());
  // });

  let mut workflow = Workflow::new(context);
  if args.verbose {
    workflow.add_task(PrintInfo::with_header("Unaligned Product Program",
        &|ctx: &ElaeniaContext| {
          ctx.unaligned_crel().as_ref()
            .expect("Missing unaligned CRel")
            .unaligned_main.to_c().to_string()
        }));
  }
  if args.dot { workflow.add_task(WriteDot::new()) }
  if args.space_size { workflow.add_task(ComputeSpace::new()) }
  match args.extractor {
    ExtractorArg::Unaligned => workflow.add_task(AlignNone::new()),
    ExtractorArg::CountLoops => workflow.add_task(AlignCountLoops::new()),
    ExtractorArg::SA => panic!("Semantic alignment currently unsupported for Elaenia workflows."),
  }
  workflow.add_task(AlignedCRel::new());
  workflow.add_task(InsertSpecs::new());
  workflow.add_task(PrintInfo::with_header("Aligned Product Program (After Insert Specs)",
        &|ctx: &ElaeniaContext| {
          ctx.aligned_crel().as_ref().expect("Missing aligned CRel").clone().to_dafny().0
        }));
  workflow.add_task(CRelLoopUnroll::new(3));
  workflow.add_task(WriteSketch::new());
  workflow.add_task(PrintInfo::with_header("Aligned Product Program Sketch",
        &|ctx: &ElaeniaContext| {
          ctx.sketch_output().as_ref().expect("Missing aligned CRel").clone()
        }));
  workflow.add_task(SolveSketch::new(None));
  workflow.add_task(AlignedOutput::new(args.output_mode));
  workflow.add_task(PrintInfo::with_header("Aligned Product Program",
        &|ctx: &ElaeniaContext| {
          ctx.aligned_output().as_ref().expect("Missing aligned output").clone()
        }));
  workflow.execute();

  println!("Elaenia completed in {}ms", workflow.context().total_elapsed_time().as_millis());
  println!("Verified: {}", workflow.context().is_verified());
}
