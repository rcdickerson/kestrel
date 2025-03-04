//! A collection of [Task]s used in various KestRel [Workflow]s.

pub mod align_count_loops;
pub mod align_none;
pub mod align_sa;
pub mod aligned_crel;
pub mod aligned_output;
pub mod compute_space;
pub mod houdafny;
pub mod invars_daikon;
pub mod predicate_task;
pub mod print_info;
pub mod write_dot;
pub mod write_product;
pub mod write_summary;

pub use align_count_loops::*;
pub use align_none::*;
pub use align_sa::*;
pub use aligned_crel::*;
pub use aligned_output::*;
pub use compute_space::*;
pub use houdafny::*;
pub use invars_daikon::*;
pub use predicate_task::*;
pub use print_info::*;
pub use write_dot::*;
pub use write_product::*;
pub use write_summary::*;
