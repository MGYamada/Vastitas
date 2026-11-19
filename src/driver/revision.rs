//! Host transport only: equality, function identities and selections are checked by Lean.
use super::*;
use serde_json::value::RawValue;

const MAX_RECEIPT: usize = 16 * 1024 * 1024;

pub(super) fn attach(
    request: &mut Vec<u8>,
    path: &Path,
    sources: &mut Sources,
) -> Result<(), String> {
    let canonical = path.canonicalize().map_err(|err| {
        format!(
            "E_INPUT: cannot resolve function revision {}: {err}",
            shown(path)
        )
    })?;
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(nix::libc::O_NONBLOCK)
        .open(&canonical)
        .map_err(|err| {
            format!(
                "E_INPUT: cannot open function revision {}: {err}",
                shown(path)
            )
        })?;
    let metadata = file
        .metadata()
        .map_err(|err| format!("E_INPUT: cannot inspect function revision: {err}"))?;
    if !metadata.is_file() {
        return Err("E_INPUT: function revision must be a regular file".into());
    }
    const KEY: &[u8] = br#","expected_function_revision":"#;
    let limit =
        MAX_RECEIPT.min(crate::limits::MAX_REQUEST_BYTES.saturating_sub(request.len() + KEY.len()));
    if metadata.len() > limit as u64 {
        return Err("E_LIMIT: function revision exceeds receipt or request limit".into());
    }
    let mut bytes = Vec::new();
    file.take(limit as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|err| format!("E_INPUT: cannot read function revision: {err}"))?;
    if bytes.len() > limit {
        return Err("E_LIMIT: function revision exceeds receipt or request limit".into());
    }
    // Validate framing before inserting; keep the original object bytes so WireScan
    // sees duplicate keys, number spellings and any other invalid raw wire.
    let raw: &RawValue = serde_json::from_slice(&bytes)
        .map_err(|_| "E_FUNCTION_REVISION: expected one JSON object")?;
    if !raw.get().starts_with('{') {
        return Err("E_FUNCTION_REVISION: expected one JSON object".into());
    }
    sources.protect_input(canonical, &metadata, "function revision");
    if request.pop() != Some(b'}') {
        return Err("E_PROTOCOL: invalid package envelope".into());
    }
    request.extend_from_slice(KEY);
    request.extend_from_slice(raw.get().as_bytes());
    request.push(b'}');
    Ok(())
}

// A checked source can legitimately nest more than serde_json::Value's
// default recursion limit. Keep its exact returned serialization opaque.
pub(super) fn decode_print_response(bytes: &[u8]) -> serde_json::Result<(Value, Option<String>)> {
    let mut fields: std::collections::BTreeMap<&str, &RawValue> = serde_json::from_slice(bytes)?;
    let receipt = fields
        .remove("function_revision")
        .map(|v| v.get().to_owned());
    let mut envelope = serde_json::Map::new();
    for (key, raw) in fields {
        envelope.insert(key.to_owned(), serde_json::from_str(raw.get())?);
    }
    Ok((Value::Object(envelope), receipt))
}

pub(super) fn print(receipt: Option<&str>) -> Result<(), String> {
    let raw = receipt
        .filter(|s| s.starts_with('{'))
        .ok_or("E_PROTOCOL: backend omitted checked function revision")?;
    if raw.len() >= MAX_RECEIPT {
        return Err("E_LIMIT: function revision exceeds the 16 MiB receipt limit".into());
    }
    writeln!(std::io::stdout().lock(), "{raw}")
        .map_err(|err| format!("E_OUTPUT: cannot write function revision: {err}"))
}
