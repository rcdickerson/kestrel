//! All KestRel executions are organized as sequences of [tasks](Task)
//! called [workflows](Workflow). This structure allows KestRel
//! development to more easily re-use or re-configure existing
//! functionality to accomodate new user options or verification
//! pipelines.

pub mod kestrel_context;
pub mod stopwatch;
pub mod task;
pub mod tasks;
pub mod workflow;

pub use kestrel_context::*;
pub use tasks::*;
pub use workflow::*;
