//! KestRel is a tool for automatically constructing aligned product
//! programs for relational verification. It uses e-graphs to
//! represent a space of possible product alignments between two
//! programs, and finds desirable product programs through a variety
//! of configurable extraction techniques. The generated product
//! programs may then be given to various off-the-shelf non-relational
//! verifiers.

pub mod anneal;
pub mod crel;
pub mod daikon;
pub mod eggroll;
pub mod elaenia;
pub mod kestrel_context;
pub mod names;
pub mod output_mode;
pub mod shanty;
pub mod spec;
pub mod syrtos;
pub mod unaligned;
pub mod workflow;
