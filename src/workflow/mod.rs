//! All KestRel executions are organized as collections of [Task]s
//! called [Workflow]s. This structure allows KestRel development to
//! more easily re-use or re-configure existing functionality to
//! accomodate new user options or verification workflows.

pub mod context;
pub mod task;
pub mod tasks;
pub mod workflow;

pub use context::*;
pub use tasks::*;
pub use workflow::*;
