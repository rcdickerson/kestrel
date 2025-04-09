//! A C-like intermediate language supporting relational groupings.

pub mod ast;
pub mod auto_fun_impl;
pub mod blockify;
pub mod clear_invariants;
pub mod collect_vars;
pub mod count_loops;
pub mod daikon_converter;
pub mod eval;
pub mod fundef;
pub mod invariant_decorator;
pub mod map_vars;
pub mod mapper;
pub mod parser;
pub mod to_c;
pub mod to_dafny;
pub mod to_eggroll;
pub mod unaligned;
pub mod visitor;
