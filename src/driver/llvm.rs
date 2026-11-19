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

#[cfg(feature = "llvm-native")]
enum Runtime {
    Pure,
    Boxed,
    Storage,
    Gemm,
}

pub(super) struct Artifact<'a> {
    pub(super) bytes: &'a [u8],
    #[cfg(feature = "llvm-native")]
    runtime: Runtime,
}

pub(super) fn checked_bytes<'a>(
    response: &'a Value,
    target: &Target,
    executable: bool,
) -> Result<Artifact<'a>, String> {
    let artifact = &response["llvm"];
    let kind = artifact["kind"].as_str();
    let supported = match kind {
        Some(
            "entry-status"
            | "assembled-bool"
            | "finite-program"
            | "boxed-exact-program"
            | "storage-program"
            | "storage-gemm-program",
        ) => true,
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
        runtime: match kind {
            Some("boxed-exact-program") => Runtime::Boxed,
            Some("storage-program") => Runtime::Storage,
            Some("storage-gemm-program") => Runtime::Gemm,
            _ => Runtime::Pure,
        },
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
    sources: &mut Sources,
    cc: Option<&OsStr>,
    openblas: Option<&Path>,
) -> Result<(), String> {
    use crate::process;
    let dir = super::PrivateDirectory::create("E_BUILD", "LLVM build directory")?;
    let provider = match (&artifact.runtime, openblas) {
        (Runtime::Gemm, Some(prefix)) => Some(stage_gemm(&dir.0, prefix, sources)?),
        (Runtime::Gemm, None) => return Err("E_BUILD: numerical program requires --openblas-prefix with pinned sequential LP64 OpenBLAS 0.3.34".into()),
        (_, Some(_)) => return Err("E_USAGE: --openblas-prefix requires a checked GEMM operation in the LLVM program".into()),
        (_, None) => None,
    };
    sources.protect_output(output)?;
    let bytes = artifact.bytes;
    let handoff = dir.0.join("program.ll");
    let object = dir.0.join("program.o");
    let program = dir.0.join("program");
    std::fs::write(&handoff, bytes)
        .map_err(|e| format!("E_BUILD: cannot write LLVM handoff: {e}"))?;
    super::llvm_backend::emit_object(bytes, &handoff, &object)
        .map_err(|e| format!("E_BUILD: LLVM object generation failed: {e}"))?;
    let mut command = if matches!(artifact.runtime, Runtime::Boxed) {
        boxed_linker(&dir.0, cc)?
    } else {
        std::process::Command::new(super::invocation_compiler(cc.unwrap_or(OsStr::new("cc")))?)
    };
    command.arg(&object);
    if provider.is_some() {
        command
            .args(["-std=c11", "-O3", "-ffp-contract=off", "-fno-fast-math"])
            .arg("-I")
            .arg(&dir.0)
            .arg(dir.0.join("gemm.c"));
    }
    if matches!(artifact.runtime, Runtime::Storage | Runtime::Gemm) {
        let archive = dir.0.join("libvastitas_llvm_storage.a");
        std::fs::write(
            &archive,
            include_bytes!(concat!(env!("OUT_DIR"), "/libvastitas_llvm_storage.a")),
        )
        .map_err(|e| format!("E_BUILD: cannot stage the storage runtime: {e}"))?;
        command.arg(archive);
    }
    if let Some(blas) = provider {
        command.arg(blas).args(["-pthread", "-lm"]);
    }
    command.arg("-o").arg(&program);
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

/// Source builds bind the fixed adapter to the headers and static archive of
/// the selected prefix. All three inputs are snapshotted before invoking the
/// host compiler. The application continues to come from the checked object.
#[cfg(feature = "llvm-native")]
fn stage_gemm(
    dir: &Path,
    prefix: &Path,
    sources: &mut Sources,
) -> Result<std::path::PathBuf, String> {
    for (name, contents) in [
        (
            "gemm.c",
            &include_bytes!("../../lean-kernel/numerical/gemm.c")[..],
        ),
        (
            "gemm.h",
            include_bytes!("../../lean-kernel/numerical/gemm.h"),
        ),
        (
            "gemm_kernels.inc",
            include_bytes!("../../lean-kernel/numerical/gemm_kernels.inc"),
        ),
        (
            "storage.h",
            include_bytes!("../../lean-kernel/native/storage.h"),
        ),
        (
            "diagonal.h",
            include_bytes!("../../lean-kernel/native/diagonal.h"),
        ),
    ] {
        std::fs::write(dir.join(name), contents).map_err(|e| {
            format!("E_BUILD: cannot stage the fixed numerical adapter {name}: {e}")
        })?;
    }
    for (relative, name) in [
        ("include/cblas.h", "cblas.h"),
        ("include/openblas_config.h", "openblas_config.h"),
        ("lib/libopenblas.a", "libopenblas.a"),
    ] {
        let path = prefix.join(relative);
        let mut snapshot = || -> std::io::Result<()> {
            let canonical = path.canonicalize()?;
            let mut file = std::fs::File::open(&canonical)?;
            let metadata = file.metadata()?;
            if !metadata.is_file() {
                return Err(std::io::Error::other("expected a regular file"));
            }
            sources.protect_input(canonical, &metadata, "OpenBLAS input");
            let mut copy = std::fs::File::create_new(dir.join(name))?;
            std::io::copy(&mut file, &mut copy)?;
            Ok(())
        };
        snapshot().map_err(|e| {
            format!(
                "E_BUILD: cannot stage pinned OpenBLAS input {}: {e}",
                super::shown(&path)
            )
        })?;
    }
    Ok(dir.join("libopenblas.a"))
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
    _: &mut Sources,
    _: Option<&OsStr>,
    _: Option<&Path>,
) -> Result<(), String> {
    Err(MISSING.into())
}
