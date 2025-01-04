//! A utility for constructing C program syntax.
//!
//! To use, create a [Source], push declarations and functions to it,
//! then call *to_string*:
//!
//! ```
//! let mut source = C::Source::new();
//!
//! let mut fun = C::Function::new(name, fun_ty);
//! fun.push_param(...);
//! fun.set_body(...);
//!
//! source.push_function(fun);
//! println!("{}", source.to_string());
//! ```
//!
//! I wrote this because I couldn't find a Rust library for this that
//! I liked. Ultimately, KestRel should either be migrated to use an
//! existing C writer library, or else this should be broken out into
//! a standalone library. ~Rob

mod expression;
mod function;
mod function_parameter;
mod include;
mod source;
mod statement;
mod r#type;
mod variable;
mod writer;

pub use expression::Expression;
pub use function::Function;
pub use function_parameter::FunctionParameter;
pub use include::Include;
pub use source::Source;
pub use statement::Statement;
pub use variable::Variable;
pub use r#type::Type;
pub use r#type::TypeQualifier;
pub use writer::Writer;
