//! A utility for constructing Sketch program syntax.
//!
//! To use, create a [Source], push declarations and functions to it,
//! then call *to_string*:
//!
//! ```
//! let mut source = Escher::Source::new();
//!
//! let mut fun = Escher::Function::new(name, fun_ty);
//! fun.push_param(...);
//! fun.set_body(...);
//!
//! source.push_function(fun);
//! println!("{}", source.to_string());
//! ```

mod expression;
mod function;
mod function_parameter;
mod source;
mod statement;
mod r#type;
mod variable;
mod writer;

pub use expression::Expression;
pub use function::Function;
pub use function_parameter::FunctionParameter;
pub use source::Source;
pub use statement::Statement;
pub use r#type::Type;
pub use r#type::TypeQualifier;
pub use variable::Variable;
pub use writer::Writer;
