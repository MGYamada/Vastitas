use nanoda_lib::util::Config;
use serde_json::{Value, json};
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

const POLICY: &str = include_str!("../config/nanoda-internal-audit.json");
pub const WORKER_COMMAND: &str = "__internal-nanoda-worker";

fn export_path(args: &[OsString]) -> Result<PathBuf, String> {
    if args.len() != 1 || args[0] == "--help" || args[0] == "-h" {
        return Err("E_USAGE: expected vastitas audit-lean LEAN4EXPORT.ndjson".into());
    }
    Ok(PathBuf::from(args[0].clone()))
}

fn config_for(path: &Path) -> Result<Config, String> {
    let mut config: Config = serde_json::from_str(POLICY)
        .map_err(|error| format!("E_LEAN_AUDIT_POLICY: invalid policy: {error}"))?;
    let allowed = ["propext", "Classical.choice", "Quot.sound"];
    let configured = config
        .permitted_axioms
        .as_ref()
        .map(|axioms| axioms.iter().map(String::as_str).collect::<Vec<_>>());
    if configured.as_deref() != Some(allowed.as_slice())
        || !config.unpermitted_axiom_hard_error
        || config.unsafe_permit_all_axioms
    {
        return Err("E_LEAN_AUDIT_POLICY: internal policy must allow exactly the three standard Lean axioms, fail on any other axiom, and forbid permit-all".into());
    }
    config.export_file_path = Some(path.to_path_buf());
    config.use_stdin = false;
    Ok(config)
}

/// Recheck a Lean export inside the isolated worker. This is not an official
/// Lean-kernel decision and never confers acceptance of Vastitas source/Core.
pub fn run_worker(args: &[OsString]) -> Result<(), String> {
    let path = export_path(args)?;
    let config = config_for(&path)?;
    let (export, skipped_axioms) = config
        .to_export_file()
        .map_err(|error| format!("E_LEAN_AUDIT: cannot read/recheck export: {error}"))?;
    if !skipped_axioms.is_empty() || export.declars.is_empty() {
        return Err("E_LEAN_AUDIT: empty export or skipped axioms are not an accepted audit".into());
    }
    // nanoda_lib may panic or exit on invalid exports; the caller supervises
    // this worker in a separate process so no rejection can crash the driver.
    export.check_all_declars();
    println!(
        "{}",
        json!({
            "status": "internal_only",
            "checker": "nanoda_lib",
            "declarations_checked": export.declars.len()
        })
    );
    Ok(())
}

/// An opt-in, non-authoritative cross-check. The official Lean kernel remains
/// the only authority for CI proofs, kernel compilation, and the Constitution.
pub fn run_cli(args: &[OsString]) -> Result<(), String> {
    let path = export_path(args)?;
    let executable = std::env::current_exe()
        .map_err(|error| format!("E_LEAN_AUDIT: cannot locate audit worker: {error}"))?;
    let output = Command::new(executable)
        .arg(WORKER_COMMAND)
        .arg(&path)
        .output()
        .map_err(|error| format!("E_LEAN_AUDIT: cannot run audit worker: {error}"))?;
    if !output.status.success() {
        let diagnostics = String::from_utf8_lossy(&output.stderr);
        let brief = diagnostics.trim().chars().take(2000).collect::<String>();
        return Err(format!(
            "E_LEAN_AUDIT: nanoda rejected {} (worker status: {})\n{}",
            path.display(),
            output.status,
            brief
        ));
    }
    let receipt: Value = serde_json::from_slice(&output.stdout)
        .map_err(|error| format!("E_LEAN_AUDIT: invalid internal audit receipt: {error}"))?;
    let checked = receipt
        .get("declarations_checked")
        .and_then(Value::as_u64)
        .filter(|count| *count > 0);
    if receipt.get("checker").and_then(Value::as_str) != Some("nanoda_lib")
        || receipt.get("status").and_then(Value::as_str) != Some("internal_only")
        || checked.is_none()
    {
        return Err("E_LEAN_AUDIT: invalid internal audit receipt".into());
    }
    println!(
        "internal-only Lean audit passed (nanoda_lib): {} declarations in {}\nThis is NOT official Lean-kernel verification and confers no Vastitas Core or constitutional acceptance.",
        checked.expect("checked count validated"),
        path.display()
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::config_for;
    use std::path::Path;

    #[test]
    fn checked_in_policy_is_strict() {
        let config = config_for(Path::new("dummy.ndjson")).unwrap();
        assert!(!config.unsafe_permit_all_axioms);
        assert!(config.unpermitted_axiom_hard_error);
        assert_eq!(
            config.permitted_axioms.unwrap(),
            ["propext", "Classical.choice", "Quot.sound"]
        );
    }
}
