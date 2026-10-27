//! Actual stdlib sources through flat and package inputs, including raw-IR tampering.
use serde_json::{Value, json};
use std::fs;
use std::io::Write;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static SERIAL: AtomicU64 = AtomicU64::new(0);
fn root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}
fn kernel() -> PathBuf {
    root().join("lean-kernel/.lake/build/bin/vastitas-kernel")
}
struct Scratch(PathBuf);
impl Scratch {
    fn new(source: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "vastitas promotion {} {}",
            std::process::id(),
            SERIAL.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("flat.vast"), source).unwrap();
        fs::write(
            path.join("main.vast"),
            format!("use std::arithmetic::generic::promote;\n{source}"),
        )
        .unwrap();
        fs::write(path.join("Vastitas.toml"), format!("[package]\nname='promotion_app'\nversion='0.1.0'\nroot='main.vast'\n[dependencies]\nstd={{path={}}}\n", serde_json::to_string(&root().join("stdlib").to_string_lossy()).unwrap())).unwrap();
        Self(path)
    }
    fn cli(&self, mode: &str, package: bool) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_vastitas"));
        command.current_dir(&self.0).arg(mode);
        if package {
            command.args(["--manifest-path", "Vastitas.toml"]);
        } else {
            command.arg("flat.vast");
            for file in ["int", "nat", "generic"] {
                command
                    .arg("--lib")
                    .arg(root().join(format!("stdlib/src/arithmetic/{file}.vast")));
            }
        }
        command
    }
    fn raw(&self, package: bool) -> Value {
        let script = self.0.join("capture");
        let capture = self.0.join("request.json");
        fs::write(
            &script,
            "#!/bin/sh\ncat > \"$CAPTURE\"\nexec \"$REAL_KERNEL\" \"$@\" < \"$CAPTURE\"\n",
        )
        .unwrap();
        fs::set_permissions(&script, fs::Permissions::from_mode(0o755)).unwrap();
        success(
            self.cli("check", package)
                .env("VASTITAS_KERNEL", script)
                .env("REAL_KERNEL", kernel())
                .env("CAPTURE", &capture)
                .output()
                .unwrap(),
        );
        serde_json::from_slice(&fs::read(capture).unwrap()).unwrap()
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn success(output: Output) {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}
fn check_raw(raw: &Value) -> Value {
    let mut child = Command::new(kernel())
        .arg("check")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(&serde_json::to_vec(raw).unwrap())
        .unwrap();
    serde_json::from_slice(&child.wait_with_output().unwrap().stdout).unwrap()
}
fn rejects(raw: &Value, code: &str) {
    let result = check_raw(raw);
    assert_eq!(result["ok"], false, "{result}");
    assert_eq!(result["diagnostics"][0]["code"], code, "{result}");
}

const VALUES: &str = "
fn main() -> Int {
    let n: Nat = 123456789012345678901234567890;
    let z: Nat = 0;
    let nn: Pair<Nat> = promote(n, z);
    let ni: Pair<Int> = promote(n, -7);
    let in_: Pair<Int> = promote(-7, n);
    let ii: Pair<Int> = promote(-7, -2);
    let again: Pair<Int> = promote(pair_first(ni), pair_second(ni));
    let identity: Pair<Nat> = promote(pair_first(nn), pair_second(nn));
    if pair_first(nn) == n && pair_second(nn) == z &&
       pair_first(ni) == int(n) && pair_second(ni) == -7 &&
       pair_first(in_) == -7 && pair_second(in_) == int(n) &&
       pair_first(ii) == -7 && pair_second(ii) == -2 &&
       pair_first(again) == pair_first(ni) && pair_second(again) == pair_second(ni) &&
       pair_first(identity) == n && pair_second(identity) == z { 42 } else { -1 }
}";

#[test]
fn promotion_values_types_reversal_and_idempotence_execute_in_both_modes() {
    let scratch = Scratch::new(VALUES);
    for package in [false, true] {
        success(scratch.cli("check", package).output().unwrap());
        success(
            scratch
                .cli("build", package)
                .args(["-o", "program"])
                .output()
                .unwrap(),
        );
        let output = Command::new(scratch.0.join("program")).output().unwrap();
        assert_eq!(output.stdout, b"42\n");
        success(output);
    }
    success(
        Command::new("python3")
            .arg(root().join("scripts/sync_stdlib_package.py"))
            .arg("--check")
            .output()
            .unwrap(),
    );
}

#[test]
fn stdlib_rules_are_independently_checked_and_result_expectations_do_not_select() {
    let scratch = Scratch::new(VALUES);
    let raw = scratch.raw(false);
    let indices: Vec<_> = raw["methods"]
        .as_array()
        .unwrap()
        .iter()
        .enumerate()
        .filter(|(_, m)| m["name"] == "promote")
        .map(|(i, _)| i)
        .collect();
    assert_eq!(indices.len(), 4);
    for (index, element) in indices.iter().zip(["Nat", "Int", "Int", "Int"]) {
        assert_eq!(
            raw["methods"][index]["return_type"],
            json!({"kind":"pair","element":element})
        );
    }
    let mut reordered = raw.clone();
    reordered["methods"].as_array_mut().unwrap().reverse();
    assert_eq!(check_raw(&reordered)["ok"], true);
    let mut missing = raw.clone();
    missing["methods"]
        .as_array_mut()
        .unwrap()
        .remove(indices[1]);
    rejects(&missing, "E_DISPATCH_COVERAGE");
    let mut wrong = raw;
    wrong["methods"][indices[1]]["return_type"]["element"] = json!("Nat");
    rejects(&wrong, "E_TYPE");
    for source in [
        "fn bad(n: Nat) -> Pair<Nat> { promote(n, -1) }",
        "fn bad() -> Pair<Nat> { promote(1, 2) }",
        "fn bad() -> Int { pair_first(promote(true, false)) }",
    ] {
        let scratch = Scratch::new(source);
        for package in [false, true] {
            let output = scratch.cli("check", package).output().unwrap();
            assert!(!output.status.success());
            let message = String::from_utf8_lossy(&output.stderr);
            assert!(
                message.contains("E_TYPE") || message.contains("E_DISPATCH_DOMAIN"),
                "{message}"
            );
        }
    }
}

#[test]
fn package_promote_owner_is_exact_and_imports_only_grant_calls() {
    let scratch = Scratch::new(VALUES);
    let raw = scratch.raw(true);
    let packages = raw["packages"].as_array().unwrap();
    let std_index = packages
        .iter()
        .position(|p| p["name"] == "vastitas_std")
        .unwrap();
    let app_index = packages
        .iter()
        .position(|p| p["name"] == "promotion_app")
        .unwrap();
    let generic_index = packages[std_index]["modules"]
        .as_array()
        .unwrap()
        .iter()
        .position(|m| m["path"] == json!(["arithmetic", "generic"]))
        .unwrap();
    let method = raw["packages"][std_index]["modules"][generic_index]["methods"][0].clone();
    for path in [
        vec!["arithmetic", "generic", "child"],
        vec!["arithmetic", "sibling"],
    ] {
        let mut altered = raw.clone();
        let mut method = method.clone();
        method["name"] = json!("package::arithmetic::generic::promote");
        altered["packages"][std_index]["modules"].as_array_mut().unwrap().push(json!({"path":path,"public":true,"span":{"start":0,"end":0,"line":1,"column":1},"imports":[],"functions":[],"generics":[],"methods":[method]}));
        rejects(&altered, "E_OWNER");
    }
    let mut external = raw;
    let mut method = method;
    method["name"] = json!("std::arithmetic::generic::promote");
    external["packages"][app_index]["modules"][0]["methods"] = json!([method]);
    rejects(&external, "E_OWNER");
    fs::write(
        scratch.0.join("main.vast"),
        "method std::arithmetic::generic::promote(x: Int, y: Int) -> Pair<Int> { pair(x, y) }",
    )
    .unwrap();
    let output = scratch.cli("check", true).output().unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("E_OWNER"));
}

#[test]
fn aliases_reexports_and_reordered_imports_keep_the_same_family() {
    let scratch = Scratch::new(VALUES);
    fs::write(scratch.0.join("main.vast"), format!("pub mod facade {{ pub use std::arithmetic::generic::promote as convert; }}\nuse facade::convert as promote;\nuse std::arithmetic::generic as arithmetic;\nfn repeated(n: Nat) -> Pair<Int> {{ arithmetic::promote(pair_first(promote(n, n)), -7) }}\n{VALUES}")).unwrap();
    success(scratch.cli("check", true).output().unwrap());
    let mut raw = scratch.raw(true);
    raw["packages"].as_array_mut().unwrap().reverse();
    for package in raw["packages"].as_array_mut().unwrap() {
        package["modules"].as_array_mut().unwrap().reverse();
        for module in package["modules"].as_array_mut().unwrap() {
            module["imports"].as_array_mut().unwrap().reverse();
            module["methods"].as_array_mut().unwrap().reverse();
        }
    }
    assert_eq!(check_raw(&raw)["ok"], true);
}

#[test]
fn promotion_families_in_distinct_package_locations_and_versions_stay_distinct() {
    let scratch = Scratch::new(VALUES);
    let raw = scratch.raw(true);
    for version in ["0.1.0", "0.2.0"] {
        let mut altered = raw.clone();
        let packages = altered["packages"].as_array_mut().unwrap();
        let mut other = packages
            .iter()
            .find(|p| p["name"] == "vastitas_std")
            .unwrap()
            .clone();
        other["source"] = json!("/another-stdlib/Vastitas.toml");
        other["version"] = json!(version);
        packages
            .iter_mut()
            .find(|p| p["name"] == "promotion_app")
            .unwrap()["dependencies"]
            .as_array_mut()
            .unwrap()
            .push(json!({"alias":"other","target":"/another-stdlib/Vastitas.toml"}));
        packages.push(other);
        // Both complete families are independently checked, even though the
        // application calls only one. Merging short names would create duplicates.
        assert_eq!(check_raw(&altered)["ok"], true);
    }
}

#[test]
fn source_children_and_siblings_cannot_extend_the_promote_owner() {
    let scratch = Scratch::new("");
    let definitions = ["int", "nat", "generic"]
        .map(|name| {
            fs::read_to_string(root().join(format!("stdlib/src/arithmetic/{name}.vast"))).unwrap()
        })
        .join("\n")
        .replace("\ngeneric promote", "\npub generic promote");
    let body = "(x: Int, y: Int) -> Pair<Int> { pair(x, y) }";
    for (inside, outside) in [
        (
            format!("pub mod child {{ method super::promote{body} }}"),
            String::new(),
        ),
        (
            String::new(),
            format!("pub mod sibling {{ method super::generic::promote{body} }}"),
        ),
    ] {
        fs::write(
            scratch.0.join("main.vast"),
            format!(
                "pub mod arithmetic {{ pub mod generic {{ {definitions} {inside} }} {outside} }}"
            ),
        )
        .unwrap();
        let output = scratch.cli("check", true).output().unwrap();
        assert!(!output.status.success());
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("E_OWNER"),
            "{output:?}"
        );
    }
}
