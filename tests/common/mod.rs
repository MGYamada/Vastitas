//! Shared process and filesystem harness. Each integration binary uses its own
//! subset; source names and package layouts are configured by its tests.
//! Every item is re-exported here, so a test names it `common::<item>`.
#![allow(dead_code)]
mod diagnostics;
mod lean;
mod process;
mod wire;
pub use diagnostics::*;
pub use lean::*;
pub use process::*;
pub use wire::*;

/// The driver's own list of the files that a native build verifies in the
/// selected kernel root.
#[path = "../../src/runtime_inputs.rs"]
pub mod runtime_inputs;
