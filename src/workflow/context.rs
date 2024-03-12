use crate::crel::ast::*;
use crate::spec::*;
use crate::unaligned::*;

pub struct Context<'a> {
  pub spec: Option<&'a KestrelSpec>,
  pub unaligned_crel: Option<&'a UnalignedCRel>,
  pub unaligned_eggroll: Option<&'a String>,
  pub aligned_crel: Option<&'a CRel>,
}

impl Context<'_> {
  pub fn new() -> Self {
    Context {
      spec: None,
      unaligned_crel: None,
      unaligned_eggroll: None,
      aligned_crel: None,
    }
  }

  pub fn unaligned_crel(&self) -> &UnalignedCRel {
    self.unaligned_crel.expect("Missing unaligned CRel")
  }

  pub fn unaligned_eggroll(&self) -> &String {
    self.unaligned_eggroll.expect("Missing unaligned eggroll")
  }
}
