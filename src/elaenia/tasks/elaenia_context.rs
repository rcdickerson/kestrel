use crate::crel::ast::*;
use crate::crel::fundef::*;
use crate::crel::unaligned::*;
use crate::eggroll::ast::*;
use crate::eggroll::to_crel::*;
use crate::elaenia::crel_inliner::*;
use crate::elaenia::elaenia_spec::*;
use crate::spec::condition::KestrelCond;
use crate::spec::to_crel::*;
use crate::syrtos as Daf;
use crate::workflow::context::*;
use egg::RecExpr;
use std::collections::HashMap;
use std::path::Path;
use std::time::Duration;

#[derive(Clone)]
pub struct ElaeniaContext {
  workflow_name: String,
  working_dir: String,
  spec: ElaeniaSpec,
  unaligned_crel: Option<UnalignedCRel>,
  unaligned_eggroll: Option<String>,
  aligned_eggroll: Option<RecExpr<Eggroll>>,
  aligned_eggroll_repetitions: Option<GuardedRepetitions>,
  aligned_crel: Option<CRel>,
  sketch_output: Option<String>,
  solved_choice_funs: HashMap<String, FunDef>,

  aligned_output: Option<String>,

  choice_funs: Vec<FunDef>,
  choice_gens: Vec<FunDef>,
  havoc_funs: Vec<FunDef>,

  output_path: Option<String>,
  output_filename: Option<String>,

  stopwatch: WorkflowStopwatch,

  sketch_failed: bool,
  sketch_succeeded: bool,
  timed_out: bool,
  verified: bool,
}

impl ElaeniaContext {
  pub fn new(workflow_name: String, spec: ElaeniaSpec) -> Self {
    ElaeniaContext {
      workflow_name,
      working_dir: ".".to_string(),
      spec,
      unaligned_crel: None,
      unaligned_eggroll: None,
      aligned_eggroll: None,
      aligned_eggroll_repetitions: None,
      aligned_crel: None,
      sketch_output: None,
      solved_choice_funs: HashMap::new(),
      aligned_output: None,
      choice_funs: Vec::new(),
      choice_gens: Vec::new(),
      havoc_funs: Vec::new(),
      output_path: None,
      output_filename: None,
      stopwatch: WorkflowStopwatch::new(),
      sketch_failed: false,
      sketch_succeeded: false,
      timed_out: false,
      verified: false,
    }
  }

  pub fn set_working_dir(&mut self, path: String) {
    self.working_dir = path;
  }

  pub fn spec(&self) -> &ElaeniaSpec {
    &self.spec
  }

  pub fn precondition_sketch(&self) -> KestrelCond {
    match &self.spec.pre_sketch {
      None => self.spec.pre.clone(),
      Some(pre_sk) => KestrelCond::And {
        lhs: Box::new(pre_sk.clone()),
        rhs: Box::new(self.spec.pre.clone()),
      },
    }
  }

  pub fn accept_choice_fun(&mut self, fundef: FunDef) {
    self.choice_funs.push(fundef);
  }

  pub fn choice_funs(&self) -> &Vec<FunDef> {
    &self.choice_funs
  }

  pub fn accept_choice_gen(&mut self, gendef: FunDef) {
    self.choice_gens.push(gendef);
  }

  pub fn choice_gens(&self) -> &Vec<FunDef> {
    &self.choice_gens
  }

  pub fn accept_havoc_fun(&mut self, havocdef: FunDef) {
    self.havoc_funs.push(havocdef);
  }

  pub fn havoc_funs(&self) -> &Vec<FunDef> {
    &self.havoc_funs
  }

  pub fn havoc_funs_as_decls(&self) -> Vec<Declaration> {
    self.havoc_funs.clone().into_iter().map(|havoc_fun| Declaration{
      specifiers: havoc_fun.specifiers.clone(),
      declarator: Declarator::Function {
        name: havoc_fun.name.clone(),
        params: havoc_fun.params.clone(),
      },
      initializer: None,
    })
    .collect()
  }

  pub fn accept_sketch_output(&mut self, sketch_output: String) {
    self.sketch_output = Some(sketch_output);
  }

  pub fn sketch_output(&self) -> &Option<String> {
    &self.sketch_output
  }

  pub fn accept_choice_solution(&mut self, name: String, solution: FunDef) {
    self.solved_choice_funs.insert(name, solution);
  }

  pub fn choice_solutions(&self) -> &HashMap<String, FunDef> {
    &self.solved_choice_funs
  }

  pub fn mark_sketch_success(&mut self, succeeded: bool) {
    self.sketch_failed = !succeeded;
    self.sketch_succeeded = succeeded;
  }

  pub fn clear_sketch_success(&mut self) {
    self.sketch_failed = false;
    self.sketch_succeeded = false;
  }

  pub fn sketch_failed(&self) -> bool {
    self.sketch_failed
  }

  pub fn sketch_succeeded(&self) -> bool {
    self.sketch_succeeded
  }
}

impl Context for ElaeniaContext {
  fn workflow_name(&self) -> &String {
    &self.workflow_name
  }

  fn working_dir(&self) -> &String {
    &self.working_dir
  }

  fn precondition(&self) -> &KestrelCond {
    &self.spec.pre
  }

  fn postcondition(&self) -> &KestrelCond {
    &self.spec.post
  }

  fn mark_verified(&mut self, verified: bool) {
    self.verified = verified;
  }

  fn is_verified(&self) -> bool {
    self.verified
  }

  fn mark_timed_out(&mut self, timed_out: bool) {
    self.timed_out = timed_out;
  }

  fn is_timed_out(&self) -> bool {
    self.timed_out
  }
}

impl AlignsCRel for ElaeniaContext {
  fn unaligned_crel(&self) -> &Option<UnalignedCRel> {
    &self.unaligned_crel
  }

  fn accept_unaligned_crel(&mut self, crel: UnalignedCRel) {
    self.unaligned_crel = Some(crel);
  }

  fn aligned_crel(&self) -> &Option<CRel> {
    &self.aligned_crel
  }

  fn accept_aligned_crel(&mut self, crel: CRel) {
    self.aligned_crel = Some(crel);
  }
}

impl AlignsEggroll for ElaeniaContext {
  fn unaligned_eggroll(&self) -> &Option<String> {
    &self.unaligned_eggroll
  }

  fn accept_unaligned_eggroll(&mut self, eggroll: String) {
    self.unaligned_eggroll = Some(eggroll);
  }

  fn aligned_eggroll(&self) -> &Option<RecExpr<Eggroll>> {
    &self.aligned_eggroll
  }

  fn accept_aligned_eggroll(&mut self, eggroll: RecExpr<Eggroll>) {
    self.aligned_eggroll = Some(eggroll);
  }

  fn aligned_eggroll_repetitions(&self) -> &Option<GuardedRepetitions> {
    &self.aligned_eggroll_repetitions
  }

  fn accept_aligned_eggroll_repetitions(&mut self, reps: GuardedRepetitions) {
    self.aligned_eggroll_repetitions = Some(reps);
  }
}

impl GeneratesDafny for ElaeniaContext {
  fn generate_dafny(&self, _: &String)
                    -> (String, HashMap<String, (usize, usize)>) {
    let aligned_crel = self.aligned_crel().as_ref().expect("Missing aligned CRel");
    let (_, fundefs) = crate::crel::fundef::extract_fundefs(&aligned_crel);
    let main_fun = fundefs.get("main").expect("No main function found");

    let preconds  = BlockItem::Statement(self.spec().pre.to_crel(StatementKind::Assume));
    let postconds = BlockItem::Statement(self.spec().post.to_crel(StatementKind::Assert));

    let unaligned_crel = self.unaligned_crel().as_ref().expect("Missing unaligned CRel");

    let mut global_decls = unaligned_crel.global_decls.clone();
    global_decls.append(&mut self.havoc_funs_as_decls());
    global_decls.append(&mut self.choice_funs().iter()
        .filter(|fun| self.choice_solutions().get(&fun.name).is_none())
        .map(|fun| Declaration {
            specifiers: fun.specifiers.clone(),
            declarator: Declarator::Function {
                name: fun.name.clone(),
                params: fun.params.clone(),
            },
            initializer: None,
        }).collect());
    let globals = global_decls.iter()
      .map(|decl| CRel::Declaration(decl.clone()).to_dafny().0)
      .collect::<Vec<String>>()
      .join("");

    let choice_funs = self.choice_solutions().iter()
      .map(|(name, fundef)| {
        let mut source = Daf::Source::new();
        let mut fun = Daf::Function::new(name, Daf::Type::Int);
        for param in &fundef.params {
          fun.push_param(&param.to_dafny());
        }
        let mut inliner = CRelInliner::new();
        let inlined_body = inliner.inline_statement(&fundef.body);
        fun.set_body(&inlined_body.to_dafny());
        source.push_function(&fun);
        source.to_string().replace(";", "")
      })
      .collect::<Vec<String>>()
      .join("");

    let mut body_items: Vec<BlockItem> = Vec::new();
    body_items.push(preconds);
    body_items.push(BlockItem::Statement(main_fun.body.clone()));
    body_items.push(postconds);
    let new_body = Statement::Compound(body_items);

    let new_main = CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
      name: "Product".to_string(),
      params: main_fun.params.clone(),
      body: Box::new(new_body),
    };
    let (dafny_output, while_lines) = new_main.to_dafny();
    let topmatter = format!("{}{}", globals, choice_funs);
    let while_lines = while_lines.iter()
      .map(|(id, (start, end))| (id.clone(), (start + topmatter.lines().count() + 1,
                                              end   + topmatter.lines().count() + 1)))
      .collect::<HashMap<_, _>>();
    (format!("{}{}", topmatter, dafny_output), while_lines)
  }
}

impl OutputsAlignment for ElaeniaContext {
  fn aligned_output(&self) -> &Option<String> {
    &self.aligned_output
  }

  fn accept_aligned_output(&mut self, output: String) {
    self.aligned_output = Some(output);
  }

  fn accept_output_path(&mut self, path: String) {
    self.output_path = Some(path.clone());
    self.output_filename = Some(Path::new(&path)
      .file_name().unwrap()
      .to_str().unwrap()
      .to_string());
  }

  fn output_path(&self) -> &Option<String> {
    &self.output_path
  }

  fn output_filename(&self) -> &Option<String> {
    &self.output_filename
  }
}

impl Stopwatch for ElaeniaContext {
 fn mark_started(&mut self) {
    self.stopwatch.mark_started();
  }

  fn mark_completed(&mut self) {
    self.stopwatch.mark_completed();
  }

  fn push_task_time(&mut self, task_name: String, duration: Duration) {
    self.stopwatch.push_task_time(task_name, duration);
  }

  fn task_timings(&self) -> Vec<(String, Duration)> {
    self.stopwatch.task_timings()
  }

  fn total_elapsed_time(&self) -> Duration {
    self.stopwatch.total_elapsed_time()
  }
}
