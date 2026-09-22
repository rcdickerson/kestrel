// Automatic specification repair
use crate::spec::KestrelSpec;
use crate::crel::unaligned::UnalignedCRel;

pub fn repair_spec(spec: &KestrelSpec, unaligned: &UnalignedCRel) -> KestrelSpec {
    spec.clone()
}