//! Actual stdlib sources through flat and package inputs, including raw-IR tampering.
mod common;
use common::{Scratch, exits, kernel_path as kernel, ran, root, success};
use serde_json::{Value, json};
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::process::Command;
impl Scratch {
    fn new(source: &str) -> Self {
        common::prepare_stdlib_package();
        let scratch = Self::empty("promotion");
        let path = &scratch.0;
        fs::write(path.join("flat.vast"), source).unwrap();
        fs::write(
            path.join("main.vast"),
            format!("use std::arithmetic::generic::promote;\n{source}"),
        )
        .unwrap();
        fs::write(path.join("Vastitas.toml"), format!("[package]\nedition = \"2026\"\nname='promotion_app'\nversion='0.1.0'\nroot='main.vast'\n[dependencies]\nstd={{path={}}}\n", serde_json::to_string(&root().join("stdlib").to_string_lossy()).unwrap())).unwrap();
        scratch
    }
    /// The compiler in `mode` in this directory, on the package when
    /// `package` and on the flat program otherwise.
    fn compiler(&self, mode: &str, package: bool) -> Command {
        let mut command = self.cli();
        command.arg(mode);
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
            &self
                .compiler("check", package)
                .env("VASTITAS_KERNEL", script)
                .env("REAL_KERNEL", kernel())
                .env("CAPTURE", &capture)
                .output()
                .unwrap(),
        );
        serde_json::from_slice(&fs::read(capture).unwrap()).unwrap()
    }
}
fn check_raw(raw: &Value) -> Value {
    common::kernel(raw, "check")
}

/// The request that `vastitas check` sends for `source` as the flat input
/// `promotion-contract.vast`, with the three stdlib arithmetic files as `--lib`
/// inputs: the one package of a flat unit. Its declarations are in
/// `common::flat_module`.
fn flat_request(source: &str) -> Value {
    flat_edited_request(source, None)
}

fn flat_edited_request(source: &str, edit: Option<(&str, &str)>) -> Value {
    let scratch = Scratch::empty("promotion request");
    scratch.write("promotion-contract.vast", source);
    let mut command = scratch.cli();
    command.args(["check", "promotion-contract.vast"]);
    for name in ["int", "nat", "generic"] {
        let relative = format!("arithmetic/{name}.vast");
        let mut text = fs::read_to_string(root().join("stdlib/src").join(&relative)).unwrap();
        if name == "generic"
            && let Some((before, after)) = edit
        {
            assert_eq!(text.matches(before).count(), 1);
            text = text.replace(before, after);
        }
        scratch.write(&relative, &text);
        command.arg("--lib").arg(relative);
    }
    common::captured_wire(command, common::CURRENT_PROTOCOL)
}
fn rejects(raw: &Value, code: &str) {
    let result = check_raw(raw);
    common::assert_wire_rejected(&result, code);
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
        success(&scratch.compiler("check", package).output().unwrap());
        success(
            &scratch
                .compiler("build", package)
                .args(["-o", "program"])
                .output()
                .unwrap(),
        );
        let output = Command::new(scratch.0.join("program")).output().unwrap();
        assert_eq!(ran(&output), exits(42));
    }
    success(
        &Command::new("python3")
            .arg(root().join("scripts/build_stdlib_package.py"))
            .arg("--check")
            .output()
            .unwrap(),
    );
}

#[test]
fn stdlib_rules_are_independently_checked_and_result_expectations_do_not_select() {
    let scratch = Scratch::new(VALUES);
    // The flat unit is the root module of the one package of its request.
    let raw = scratch.raw(false);
    fn methods(raw: &mut Value) -> &mut Vec<Value> {
        raw.pointer_mut("/packages/0/modules/0/methods")
            .and_then(Value::as_array_mut)
            .unwrap()
    }
    let indices: Vec<_> = methods(&mut raw.clone())
        .iter()
        .enumerate()
        .filter(|(_, m)| m["name"] == "promote")
        .map(|(i, _)| i)
        .collect();
    assert_eq!(indices.len(), 4);
    for (index, element) in indices.iter().zip(["Nat", "Int", "Int", "Int"]) {
        assert_eq!(
            methods(&mut raw.clone())[*index]["return_type"],
            json!({"kind":"pair","element":element})
        );
    }
    let mut reordered = raw.clone();
    methods(&mut reordered).reverse();
    assert_eq!(check_raw(&reordered)["ok"], true);
    let mut missing = raw.clone();
    methods(&mut missing).remove(indices[1]);
    rejects(&missing, "E_DISPATCH_COVERAGE");
    let mut wrong = raw;
    methods(&mut wrong)[indices[1]]["return_type"]["element"] = json!("Nat");
    rejects(&wrong, "E_TYPE");
    for (source, code) in [
        ("fn bad(n: Nat) -> Pair<Nat> { promote(n, -1) }", "E_TYPE"),
        ("fn bad() -> Pair<Nat> { promote(1, 2) }", "E_TYPE"),
        (
            "fn bad() -> Int { pair_first(promote(true, false)) }",
            "E_DISPATCH_DOMAIN",
        ),
    ] {
        let scratch = Scratch::new(source);
        for package in [false, true] {
            let output = scratch.compiler("check", package).output().unwrap();
            assert!(!output.status.success());
            let message = String::from_utf8_lossy(&output.stderr);
            common::assert_first_code(&message, code);
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
        "fn std::arithmetic::generic::promote(x: Int, y: Int) -> Pair<Int> { pair(x, y) }",
    )
    .unwrap();
    let output = scratch.compiler("check", true).output().unwrap();
    assert!(!output.status.success());
    common::expect_code(&output, "E_OWNER");
}

#[test]
fn aliases_reexports_and_reordered_imports_keep_the_same_family() {
    let scratch = Scratch::new(VALUES);
    fs::write(scratch.0.join("main.vast"), format!("pub mod facade {{ pub use std::arithmetic::generic::promote as convert; }}\nuse facade::convert as promote;\nuse std::arithmetic::generic as arithmetic;\nfn repeated(n: Nat) -> Pair<Int> {{ arithmetic::promote(pair_first(promote(n, n)), -7) }}\n{VALUES}")).unwrap();
    success(&scratch.compiler("check", true).output().unwrap());
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
    let stdlib = root().join("stdlib");
    let manifest = fs::read_to_string(stdlib.join("Vastitas.toml")).unwrap();
    let app = fs::read_to_string(scratch.0.join("Vastitas.toml")).unwrap();
    scratch.write("Vastitas.toml", &(app + "other={path='other'}\n"));
    let other = scratch.0.join("other");
    fs::create_dir_all(other.join("target")).unwrap();
    std::os::unix::fs::symlink(stdlib.join("src"), other.join("src")).unwrap();
    success(
        &Command::new("cp")
            .arg("-R")
            .arg(stdlib.join("target/package"))
            .arg(other.join("target"))
            .output()
            .unwrap(),
    );
    for version in ["0.1.0", "0.2.0"] {
        fs::write(
            other.join("Vastitas.toml"),
            manifest.replace("0.1.0", version),
        )
        .unwrap();
        let wire = scratch.raw(true);
        let packages: Vec<_> = wire["packages"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|p| p["name"] == "vastitas_std")
            .collect();
        assert_eq!(packages.len(), 2);
        assert_ne!(packages[0]["source"], packages[1]["source"]);
        assert!(packages.iter().any(|p| p["version"] == version));
        // Both families are checked even though only one is called.
        assert_eq!(check_raw(&wire)["ok"], true);
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
        .replace("\nfn promote", "\npub fn promote");
    let body = "(x: Int, y: Int) -> Pair<Int> { pair(x, y) }";
    for (inside, outside) in [
        (
            format!("pub mod child {{ fn super::promote{body} }}"),
            String::new(),
        ),
        (
            String::new(),
            format!("pub mod sibling {{ fn super::generic::promote{body} }}"),
        ),
    ] {
        fs::write(
            scratch.0.join("main.vast"),
            format!(
                "pub mod arithmetic {{ pub mod generic {{ {definitions} {inside} }} {outside} }}"
            ),
        )
        .unwrap();
        let output = scratch.compiler("check", true).output().unwrap();
        assert!(!output.status.success());
        common::expect_code(&output, "E_OWNER");
    }
}

#[test]
fn mixed_arithmetic_delegates_to_homogeneous_kernels_in_both_modes() {
    let source = "fn main() -> Int {
        let n: Nat = 20; let m: Nat = 22; let z: Nat = 0;
        let big: Nat = 123456789012345678901234567890;
        let nn: Nat = self::add(n, m); let nm: Nat = maximum(n, m);
        if nn == 42 && nm == m && self::add(n, 22) == 42 && self::add(22, n) == 42 &&
           maximum(n, 22) == 22 && maximum(22, n) == 22 &&
           self::add(n, -7) == 13 && self::add(-7, n) == 13 &&
           maximum(n, -7) == 20 && maximum(-7, n) == 20 &&
           self::add(-7, -2) == -9 && maximum(-7, -2) == -2 &&
           self::add(big, -1) == 123456789012345678901234567889 &&
           maximum(-1, big) == int(big) && self::add(z, 0) == 0 && maximum(z, -1) == 0
        { 42 } else { -1 }
    }";
    let scratch = Scratch::new(source);
    fs::write(
        scratch.0.join("main.vast"),
        format!(
            "use std::arithmetic::generic::add as promoted_add; use std::arithmetic::generic::maximum;\n{}",
            source.replace("self::add", "promoted_add")
        ),
    )
    .unwrap();
    assert_eq!(check_raw(&flat_request(source))["ok"], true);
    for package in [false, true] {
        success(&scratch.compiler("check", package).output().unwrap());
        success(
            &scratch
                .compiler("build", package)
                .args(["-o", "program"])
                .output()
                .unwrap(),
        );
        let output = Command::new(scratch.0.join("program")).output().unwrap();
        assert_eq!(ran(&output), exits(42));
    }
}

#[test]
fn promotion_does_not_hide_specialized_cycles_or_bad_applicable_bodies() {
    let declarations = [
        (
            "fn cycle(x, y) domain((Nat, Nat), (Nat, Int), (Int, Nat), (Int, Int)); fn cycle(x: Number, y: Number) -> Int { let p = promote(x, y); cycle(pair_first(p), pair_second(p)) }",
            "E_RECURSION",
        ),
        (
            "fn cycle(x, y) domain((Nat, Int), (Int, Int)); fn cycle(x: Nat, y: Int) -> Int { let p = promote(x, y); cycle(pair_first(p), pair_second(p)) } fn cycle(x: Int, y: Int) -> Int { cycle(x, y) }",
            "E_RECURSION",
        ),
        (
            "fn helper(x: Int, y: Int) -> Int { cycle(x, y) } fn cycle(x, y) domain((Int, Int)); fn cycle(x: Int, y: Int) -> Int { helper(x, y) }",
            "E_RECURSION",
        ),
        (
            "fn add(x: Number, y: Number) -> Int { let p = promote(x, y); pair_first(p) }",
            "E_TYPE",
        ),
        (
            "fn add(x: Any, y: Any) -> Int { let p = promote(x, y); pair_first(p) }",
            "E_TYPE",
        ),
        ("fn bad(n: Nat) -> Int { n + 1 }", "E_TYPE"),
    ];
    for (source, code) in declarations {
        // Higher-order presence must not disable unused-instance auditing.
        for extra in [
            "",
            "fn unused() -> Int { let f = fn(x: Int) -> Int { x }; f(0) }",
        ] {
            let source = format!("{source}\n{extra}");
            rejects(&flat_request(&source), code);
            let scratch = Scratch::new(&source);
            let output = scratch.compiler("check", false).output().unwrap();
            assert!(!output.status.success());
            common::expect_code(&output, code);
        }
    }
}

#[test]
fn missing_homogeneous_delegation_is_an_error() {
    let base = flat_request("fn main() -> Int { 0 }");
    let mut raw = base.clone();
    common::flat_module(&mut raw)["methods"]
        .as_array_mut()
        .unwrap()
        .retain(|m| {
            !(m["name"] == "add"
                && m["params"][0]["ty"]["name"] == "Int"
                && m["params"][1]["ty"]["name"] == "Int")
        });
    rejects(&raw, "E_DISPATCH_COVERAGE");
    let mut raw = base.clone();
    let add = common::flat_module(&mut raw)["generics"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|g| g["name"] == "add")
        .unwrap();
    add["domain"]
        .as_array_mut()
        .unwrap()
        .retain(|key| key != &json!([{"kind":"named","name":"Int"},{"kind":"named","name":"Int"}]));
    rejects(&raw, "E_DISPATCH_DOMAIN");
    let mut raw = base;
    common::flat_module(&mut raw)["functions"]
        .as_array_mut()
        .unwrap()
        .retain(|f| f["name"] != "int_add");
    rejects(&raw, "E_NAME");
}

/// The frontend's request for the stdlib arithmetic sources, an empty input
/// file with the three arithmetic libraries, is the proof fixture
/// `promotion.json`, from which `VastitasPromotion.IndexedFixture` reflects
/// the Core of the oracle's promotion theorems.
/// `VASTITAS_UPDATE_PROMOTION_FIXTURE=1` rewrites it.
#[test]
fn stdlib_ir_matches_proof_fixture() {
    for (name, source) in [
        ("promotion.json", ""),
        (
            "promotion-entry.json",
            "fn main() -> Int { self::add(20, 22) }\n",
        ),
    ] {
        let actual = flat_request(source);
        let path = root().join("tests/fixtures").join(name);
        if common::regenerate_fixture("VASTITAS_UPDATE_PROMOTION_FIXTURE") {
            fs::write(&path, serde_json::to_string(&actual).unwrap() + "\n").unwrap();
        }
        let expected: Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
        assert_eq!(
            actual, expected,
            "stdlib frontend request differs from {name}"
        );
        assert_eq!(check_raw(&expected)["ok"], true);
    }
}

/// Replacing one declaration with another of the same byte length keeps the
/// other declarations' global positions. The Lean regression applies these
/// small deltas to the canonical request and evaluates the resulting Core.
#[test]
fn promotion_policy_mutations_are_real_frontend_requests() {
    let canonical = flat_request("");
    let mut cases = Vec::new();
    for (index, before, after) in [
        (1, "pair(int(left), right)", "pair(000000000, 00000)"),
        (
            0,
            "fn promote(left: Nat, right: Nat) -> Pair<Nat> {\n    pair(left, right)",
            "fn promote(lo: Nat, hi: Nat) -> Pair<Int> {\n    pair(int(lo), int(hi))",
        ),
    ] {
        assert_eq!(before.len(), after.len());
        let actual = flat_edited_request("", Some((before, after)));
        let method = &actual["packages"][0]["modules"][0]["methods"][index];
        let mut replay = canonical.clone();
        common::flat_module(&mut replay)["methods"][index] = method.clone();
        let files = replay["root_source"]["files"].as_array_mut().unwrap();
        let generic = files
            .iter_mut()
            .find(|file| file["path"] == "arithmetic/generic.vast")
            .unwrap();
        generic["text"] = json!(generic["text"].as_str().unwrap().replace(before, after));
        assert_eq!(replay, actual);
        assert_eq!(check_raw(&actual)["ok"], true);
        cases.push(json!({"index":index, "before":before, "after":after, "method":method}));
    }
    let path = root().join("tests/fixtures/promotion-policy.json");
    if common::regenerate_fixture("VASTITAS_UPDATE_PROMOTION_FIXTURE") {
        fs::write(&path, serde_json::to_string_pretty(&cases).unwrap() + "\n").unwrap();
    }
    let stored: Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
    assert_eq!(json!(cases), stored);
}
