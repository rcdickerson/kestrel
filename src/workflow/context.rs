use crate::crel::ast::*;
use crate::eggroll::ast::*;
use crate::spec::*;
use crate::unaligned::*;
use egg::*;
use std::path::Path;
use std::time::{Duration, Instant};

pub struct Context<'a> {
  pub task_name: String,
  pub start_time: Instant,
  pub spec: Option<&'a KestrelSpec>,
  pub unaligned_crel: Option<&'a UnalignedCRel>,
  pub unaligned_eggroll: Option<&'a String>,
  pub aligned_eggroll: Option<RecExpr<Eggroll>>,
  pub aligned_crel: Option<CRel>,
  pub aligned_output: Option<String>,
  pub output_path: Option<String>,
  pub verified: bool,
}

impl Context<'_> {
  pub fn new(task_name: String) -> Self {
    Context {
      task_name,
      start_time: Instant::now(),
      spec: None,
      unaligned_crel: None,
      unaligned_eggroll: None,
      aligned_eggroll: None,
      aligned_crel: None,
      aligned_output: None,
      output_path: None,
      verified: false,
    }
  }

  pub fn spec(&self) -> &KestrelSpec {
    self.spec.expect("Missing unaligned CRel")
  }

  pub fn unaligned_crel(&self) -> &UnalignedCRel {
    self.unaligned_crel.expect("Missing unaligned CRel")
  }

  pub fn unaligned_eggroll(&self) -> &String {
    self.unaligned_eggroll.expect("Missing unaligned eggroll")
  }

  pub fn aligned_eggroll(&self) -> &RecExpr<Eggroll> {
    self.aligned_eggroll.as_ref().expect("Missing aligned eggroll")
  }

  pub fn aligned_crel(&self) -> &CRel {
    self.aligned_crel.as_ref().expect("Missing aligned CRel")
  }

  pub fn aligned_output(&self) -> &String {
    self.aligned_output.as_ref().expect("Missing aligned output")
  }

  pub fn output_path(&self) -> &String {
    self.output_path.as_ref().expect("Missing output path")
  }

  pub fn filename(&self) -> Option<String> {
    self.output_path.as_ref().map(|path| {
      Path::new(&path).file_name().unwrap().to_str().unwrap().to_string()
    })
  }

  pub fn elapsed_time(&self) -> Duration {
    self.start_time.elapsed()
  }
}
