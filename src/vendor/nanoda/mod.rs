// Integration root for the private Lean export auditor.
#![deny(clippy::cast_possible_truncation)]

mod debug_printer;
pub(crate) mod env;
mod expr;
mod inductive;
mod level;
mod name;
mod parser;
mod pretty_printer;
mod quot;
mod tc;
mod unique_hasher;
pub(crate) mod util;
use util::hash64;
