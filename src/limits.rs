//! Values come from the kernel's compiler-limits.json at build time.
//! Distinct resource budgets remain distinct even when their values coincide.
include!(concat!(env!("OUT_DIR"), "/compiler_limits.rs"));
