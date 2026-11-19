//! The LLVM preview shares the ordinary public parser, source checks
//! and installation rules. Its byte endpoint also works in a check-only build.
use super::Sources;
use serde_json::Value;
use std::ffi::OsStr;
use std::path::Path;

pub(super) struct Target {
    pub(super) triple: String,
    pub(super) layout: String,
}

pub(super) struct Artifact<'a> {
    pub(super) bytes: &'a [u8],
    #[cfg(feature = "llvm-native")]
    boxed_runtime: bool,
}

pub(super) fn checked_bytes<'a>(
    response: &'a Value,
    target: &Target,
    executable: bool,
) -> Result<Artifact<'a>, String> {
    let artifact = &response["llvm"];
    let kind = artifact["kind"].as_str();
    let supported = match kind {
        Some("entry-status" | "assembled-bool" | "finite-program" | "boxed-exact-program") => true,
        Some("unary-lookup" | "binary-lookup" | "static-call" | "boxed-exact-library") => {
            !executable
        }
        _ => false,
    };
    if !supported
        || artifact["triple"] != target.triple.as_str()
        || artifact["layout"] != target.layout.as_str()
        || artifact["verification_endpoint"] != "modeled-llvm-bytes"
        || artifact["verifier"] != "compiled-lean-checker"
        || artifact["official_kernel_checked"] != false
        || artifact["native_generated"] != false
        || response.get("lean_source").is_some()
    {
        return Err("E_PROTOCOL: incompatible LLVM checker response".into());
    }
    let text = artifact["ir"]
        .as_str()
        .filter(|s| !s.is_empty() && s.is_ascii() && !s.as_bytes().contains(&0))
        .ok_or_else(|| "E_PROTOCOL: missing or invalid complete LLVM text".to_owned())?;
    Ok(Artifact {
        bytes: text.as_bytes(),
        #[cfg(feature = "llvm-native")]
        boxed_runtime: kind == Some("boxed-exact-program"),
    })
}

#[cfg(feature = "llvm-native")]
pub(super) fn host_target() -> Result<Target, String> {
    let (triple, layout) = super::llvm_backend::host_target()
        .map_err(|e| format!("E_BUILD: cannot select LLVM target: {e}"))?;
    Ok(Target { triple, layout })
}

#[cfg(feature = "llvm-native")]
pub(super) fn build(
    artifact: &Artifact<'_>,
    output: &Path,
    sources: &Sources,
    cc: Option<&OsStr>,
) -> Result<(), String> {
    use crate::process;
    let dir = super::PrivateDirectory::create("E_BUILD", "LLVM build directory")?;
    let bytes = artifact.bytes;
    let handoff = dir.0.join("program.ll");
    let object = dir.0.join("program.o");
    let program = dir.0.join("program");
    std::fs::write(&handoff, bytes)
        .map_err(|e| format!("E_BUILD: cannot write LLVM handoff: {e}"))?;
    super::llvm_backend::emit_object(bytes, &handoff, &object)
        .map_err(|e| format!("E_BUILD: LLVM object generation failed: {e}"))?;
    let mut command = if artifact.boxed_runtime {
        boxed_linker(&dir.0, cc)?
    } else {
        std::process::Command::new(super::invocation_compiler(cc.unwrap_or(OsStr::new("cc")))?)
    };
    command.arg(&object).arg("-o").arg(&program);
    let result = process::capture(
        command,
        None,
        process::Retention::Tail(process::DIAGNOSTIC_TAIL),
    )
    .map_err(|e| super::subprocess_error(e, "E_BUILD", "host linker", false))?;
    if !result.status.success() {
        return Err(format!(
            "E_BUILD: LLVM native link failed ({})\n{}{}",
            result.status,
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr),
        ));
    }
    super::install_output(&program, output, sources)
}

/// Link the checked object with the embedded integer shim and the selected Lean
/// runtime. leanc only drives the C linker here. The program body is the LLVM object.
#[cfg(feature = "llvm-native")]
fn boxed_linker(dir: &Path, cc: Option<&OsStr>) -> Result<std::process::Command, String> {
    let pin = super::expected_kernel::TOOLCHAIN;
    std::fs::write(dir.join("lean-toolchain"), pin)
        .map_err(|e| format!("E_BUILD: cannot select boxed runtime toolchain: {e}"))?;
    super::check_lean_version(dir, pin)?;
    let prefix = super::pinned_lean_prefix(dir)?;
    let shim = dir.join("exact.c");
    std::fs::write(&shim, include_bytes!("../../llvm/runtime/exact.c"))
        .map_err(|e| format!("E_BUILD: cannot write integer runtime shim: {e}"))?;
    let mut command = std::process::Command::new(prefix.join("bin/leanc"));
    command
        .current_dir(dir)
        .env("LEAN_SYSROOT", &prefix)
        .env_remove("LEAN_CC");
    if let Some(cc) = cc {
        command.env("LEAN_CC", super::invocation_compiler(cc)?);
        command.arg("-L").arg(prefix.join("lib"));
    }
    command.arg("-O2").arg(shim);
    Ok(command)
}

#[cfg(not(feature = "llvm-native"))]
const MISSING: &str = "E_BUILD: LLVM native generation requires Vastitas built with --features llvm-native and LLVM 23.1.4";

#[cfg(not(feature = "llvm-native"))]
pub(super) fn host_target() -> Result<Target, String> {
    Err(MISSING.into())
}

#[cfg(not(feature = "llvm-native"))]
pub(super) fn build(
    _: &Artifact<'_>,
    _: &Path,
    _: &Sources,
    _: Option<&OsStr>,
) -> Result<(), String> {
    Err(MISSING.into())
}
