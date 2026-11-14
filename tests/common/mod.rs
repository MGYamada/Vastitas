//! Shared process and filesystem harness. Each integration binary uses its own
//! subset; source names and package layouts are configured by its tests.
//! Every item is re-exported here, so a test names it `common::<item>`.
#![allow(dead_code)]
mod diagnostics;
mod lean;
mod packages;
mod process;
mod wire;
// A binary that uses no item of a module would otherwise warn of its re-export.
#[allow(unused_imports)]
pub use {diagnostics::*, lean::*, packages::*, process::*, wire::*};

/// The driver's own list of the files that a native build verifies in the
/// selected kernel root.
#[path = "../../src/runtime_inputs.rs"]
pub mod runtime_inputs;
