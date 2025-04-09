use crate::crel::ast::CRel;
use crate::crel::unaligned::UnalignedCRel;

pub trait AlignsCRel {
  fn unaligned_crel(&self) -> &Option<UnalignedCRel>;
  fn accept_unaligned_crel(&mut self, crel: UnalignedCRel);

  fn aligned_crel(&self) -> &Option<CRel>;
  fn accept_aligned_crel(&mut self, crel: CRel);
}
