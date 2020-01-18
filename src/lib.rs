// this ensures that crate users generating docs with --no-deps will still
// properly get links to the public docs for boolector's types
#![doc(html_root_url = "https://docs.rs/boolector/0.1.2")]

mod btor;
pub use btor::{Btor, SolverResult};
mod node;
pub use node::BV;
pub use node::Array;
pub use node::BVSolution;
pub mod option;
mod sort;
