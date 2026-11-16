//! old-route(#533): the development-only wire parity harness of #533, round 1
//! (W2). It compares the routes that retire at the cutover to epoch 10 with
//! protocol 9 and is removed with them; it grants no acceptance authority.
//!
//! For each program of the corpus, the harness captures the wire request at
//! the version that the frontend selects today and re-encodes it as protocol
//! 9: a package request of protocol 3 to 8 by its version and
//! `input: "package"`, and a flat request (protocol 2 or 4) in the package
//! shape of `packages::flat_request`. Both requests go through the kernel's
//! `check` and `emit`, and the harness compares `ok`, the diagnostics (code,
//! message, span and notes), `lean_source` and the runtime flags; protocols
//! 2 to 7 answer without the flags, which the comparison reads as `false`.
//!
//! The corpus is every flat program and package under `examples/` (the
//! rejected programs included), the packages under `tests/emit_corpus/` and
//! `tests/fixtures/`, and the wire fixtures of `tests/fixtures/`. A program
//! that observes values with `show!` selects protocol 9, so it also runs
//! without its observations (`show!(` replaced by `(` in a copy of the
//! corpus), as the request that it would send otherwise.
//!
//! The report has one line per program: its route pair and what differs,
//! with the class of each divergence (`Class`). The test fails on a
//! divergence of no class. It writes the report to `report.txt` in
//! `$VASTITAS_WIRE_PARITY_DIR` (by default `target/tmp/wire-parity`), and
//! there the request pairs with `pairs.json`, from which
//! `scripts/wire_parity.lean` compares the checked Core of both requests.
//! `bash scripts/check_wire_parity.sh` runs both.
mod common;

use common::{CURRENT_PROTOCOL, Scratch, cli, kernel_bytes, root};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

const INT: &str = "stdlib/src/arithmetic/int.vast";
const NAT: &str = "stdlib/src/arithmetic/nat.vast";
const GENERIC: &str = "stdlib/src/arithmetic/generic.vast";

/// The `--lib` inputs of the flat programs that need them, as
/// `tests/examples.rs` checks them.
const FLAT_LIBRARIES: &[(&str, &[&str])] = &[
    ("examples/book/programs/flat-library.vast", &[INT]),
    ("examples/dispatch-arithmetic.vast", &[INT, NAT, GENERIC]),
    ("examples/promotion.vast", &[INT, NAT, GENERIC]),
    ("examples/stdlib-arithmetic.vast", &[INT, NAT]),
];

/// The wire requests among the fixtures.
const WIRE_FIXTURES: &[&str] = &[
    "tests/fixtures/edit-authority.json",
    "tests/fixtures/edit-recipients.json",
    "tests/fixtures/promotion.json",
    "tests/fixtures/reverse-example.wire.json",
];

/// The directories whose packages, and under `examples/` flat programs, form
/// the corpus.
const CORPUS: &[&str] = &["examples", "tests/emit_corpus", "tests/fixtures"];

/// The directories that the copy without observations holds: the corpus and
/// the packages that it depends on by path.
const COPIED: &[&str] = &[
    "examples",
    "tests/emit_corpus",
    "tests/fixtures",
    "stdlib",
    "nature",
];

/// The package identity of a flat unit in a protocol-9 request
/// (`packages::FLAT_PACKAGE` and `FLAT_SOURCE`).
const FLAT_PACKAGE: &str = "legacy_flat";
const FLAT_SOURCE: &str = "vastitas:compat:flat";

#[derive(Clone)]
enum Input {
    /// A flat program and its `--lib` inputs, relative to the directory that
    /// the command runs in.
    Flat(String, Vec<String>),
    /// A package, by its manifest relative to that directory.
    Package(String),
    /// A wire fixture.
    Wire(PathBuf),
}

#[derive(Clone)]
struct Program {
    name: String,
    input: Input,
    /// The directory that the command runs in: the repository root, or the
    /// copy of the corpus without observations.
    directory: PathBuf,
}

/// The kernel's answers to one request.
#[derive(Clone)]
struct Answers {
    check: Value,
    emit: Value,
}

enum Outcome {
    /// The frontend rejected the program before it wrote a request: the
    /// first line of its diagnostics.
    Frontend(String),
    /// The frontend already writes the current protocol.
    Current,
    Pair(Box<Pair>),
}

/// The request at the selected version, its protocol-9 encoding, the
/// kernel's answers to both and what differs.
struct Pair {
    from: u64,
    original: Value,
    current: Value,
    before: Answers,
    after: Answers,
    differences: Vec<String>,
}

/// The classes of the divergences that #533 expects or that the report
/// found. Each class is a property of the routes, not of a program.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Class {
    /// Protocols 2 to 6 add an implicit compatibility package with the
    /// legacy geometry (`Scheme`, `Point`, …); protocol 9 requires one
    /// validated `geometry_compat` export instead. Legacy geometry without
    /// one is rejected under 9 before anything else
    /// ([`LEGACY_GEOMETRY`]).
    GeometryCompat,
    /// The implicit compatibility package of protocols 2 to 6 also reaches
    /// the Core of programs that use no legacy geometry: their emitted Lean
    /// declares its two package structures (`Package_0`, `Package_1`), which
    /// protocol 9 does not. The rest of the source is the same.
    CompatibilityStructures,
    /// A flat unit becomes the package `legacy_flat` under 9, so the
    /// kernel's diagnostics name its declarations `legacy_flat::name`.
    /// `LegacySource.describeDiagnostic` removes that prefix for flat input
    /// of protocols 2 and 4; for a flat protocol-9 request the driver does
    /// (`driver.rs`). Code, span and notes are otherwise the same.
    FlatNames,
    /// A hand-written recipient record by manifest path (`grantee_source`),
    /// which only protocols 5 to 8 decode; the frontend never writes it
    /// (#533). Protocol 9 names the recipient package instead.
    GranteeSource,
}

/// The first diagnostic of legacy geometry without a compatibility export
/// under protocol 9.
const LEGACY_GEOMETRY: &str =
    "legacy geometry syntax requires exactly one explicit library compatibility export";

impl Class {
    fn label(self) -> &'static str {
        match self {
            Class::GeometryCompat => "geometry-compat",
            Class::CompatibilityStructures => "compatibility-structures",
            Class::FlatNames => "flat-names",
            Class::GranteeSource => "grantee-source",
        }
    }
}

#[test]
fn wire_parity_report() {
    common::prepare_stdlib_package();
    let copy = observations_removed();
    let mut programs = corpus(root());
    let observed: Vec<Program> = programs
        .iter()
        .filter(|program| observes(root(), &program.input))
        .map(|program| Program {
            name: format!("{} [unobserved]", program.name),
            input: program.input.clone(),
            directory: copy.0.clone(),
        })
        .collect();
    programs.extend(observed);
    assert!(
        programs.len() > 200,
        "corpus of {} programs",
        programs.len()
    );
    let outcomes = run_all(&programs);
    let directory = output_directory();
    let mut report = String::new();
    let mut pairs = Vec::new();
    let mut unclassified = Vec::new();
    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    for (index, (program, outcome)) in programs.iter().zip(&outcomes).enumerate() {
        let (route, verdict) = match outcome {
            Outcome::Frontend(line) => ("frontend".to_string(), format!("no request: {line}")),
            Outcome::Current => (
                format!("{CURRENT_PROTOCOL}"),
                "current protocol".to_string(),
            ),
            Outcome::Pair(pair) => {
                let Pair {
                    from,
                    original,
                    current,
                    before,
                    after,
                    differences,
                } = pair.as_ref();
                let route = format!("{from}→{CURRENT_PROTOCOL}");
                let verdict = if differences.is_empty() {
                    "same".to_string()
                } else {
                    let classes = classify(*from, original, before, after);
                    match classes {
                        Ok(classes) => format!(
                            "differs: {} [{}]",
                            differences.join("; "),
                            classes
                                .iter()
                                .map(|class| class.label())
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                        Err(reason) => {
                            unclassified.push(format!("{}: {reason}", program.name));
                            format!(
                                "differs: {} [UNCLASSIFIED: {reason}]",
                                differences.join("; ")
                            )
                        }
                    }
                };
                let stem = format!("pairs/{index:03}");
                write(&directory.join(format!("{stem}.from.json")), original);
                write(&directory.join(format!("{stem}.current.json")), current);
                write_answers(
                    &directory.join(format!("{stem}.answers.json")),
                    before,
                    after,
                );
                pairs.push(json!({
                    "name": program.name,
                    "from": from,
                    "original": format!("{stem}.from.json"),
                    "current": format!("{stem}.current.json"),
                    "wire": verdict,
                }));
                (route, verdict)
            }
        };
        let key = match outcome {
            Outcome::Pair(pair) if !pair.differences.is_empty() => {
                format!("{route} differs")
            }
            _ => format!("{route} {}", verdict.split(':').next().unwrap()),
        };
        *counts.entry(key).or_default() += 1;
        writeln!(report, "{} | {route} | {verdict}", program.name).unwrap();
    }
    let mut summary = String::from("# Wire parity of #533 round 1 (W2): development-only\n");
    for (key, count) in &counts {
        writeln!(summary, "# {count:4} {key}").unwrap();
    }
    let report = summary + &report;
    write_text(&directory.join("report.txt"), &report);
    write(&directory.join("pairs.json"), &Value::Array(pairs));
    println!("{report}");
    println!("report: {}", directory.join("report.txt").display());
    assert!(
        unclassified.is_empty(),
        "divergences of no class:\n{}",
        unclassified.join("\n")
    );
    // Since #533 round 1 (W3, W4) the frontend writes neither protocol 7 nor
    // protocol 8, so no captured request has a 7 → 9 or 8 → 9 pair.
    let older: Vec<&str> = programs
        .iter()
        .zip(&outcomes)
        .filter(|(program, outcome)| {
            !matches!(program.input, Input::Wire(_))
                && matches!(outcome, Outcome::Pair(pair) if matches!(pair.from, 7 | 8))
        })
        .map(|(program, _)| program.name.as_str())
        .collect();
    assert!(
        older.is_empty(),
        "the frontend wrote protocol 7 or 8 for:\n{}",
        older.join("\n")
    );
}

/// The divergence classes of a pair, or why its differences fit none.
/// The divergence classes of a pair, or what remains different once the
/// classes that apply are accounted for. A class that ends the check under
/// 9 explains the whole pair; the others normalize one side, and the pair
/// is classified when nothing else differs.
fn classify(
    from: u64,
    original: &Value,
    before: &Answers,
    after: &Answers,
) -> Result<Vec<Class>, String> {
    let rejected = &after.check["diagnostics"][0];
    if after.check["ok"] == false {
        if from <= 6 && rejected["code"] == "E_TYPE" && rejected["message"] == LEGACY_GEOMETRY {
            return Ok(vec![Class::GeometryCompat]);
        }
        if (5..=8).contains(&from)
            && rejected["code"] == "E_PROTOCOL"
            && rejected["message"]
                .as_str()
                .is_some_and(|message| message.ends_with("field 'grantee_source'"))
            && original.to_string().contains("\"grantee_source\"")
        {
            return Ok(vec![Class::GranteeSource]);
        }
    }
    let mut classes = Vec::new();
    let mut before = before.clone();
    let mut after = after.clone();
    if from <= 6
        && let Some(source) = before.emit["lean_source"].as_str()
    {
        let stripped = without_compatibility_structures(source);
        if stripped != source {
            before.emit["lean_source"] = json!(stripped);
            classes.push(Class::CompatibilityStructures);
        }
    }
    if original.get("packages").is_none() {
        let check = without_flat_names(&mut after.check);
        let emit = without_flat_names(&mut after.emit);
        if check || emit {
            classes.push(Class::FlatNames);
        }
    }
    let residual = compare(&before, &after);
    if residual.is_empty() && !classes.is_empty() {
        Ok(classes)
    } else {
        Err(residual.join("; "))
    }
}

/// `source` without the package structures `Package_0` and `Package_1` of
/// the implicit compatibility package: each holds a `witness` object and one
/// point.
fn without_compatibility_structures(source: &str) -> String {
    let mut text = source.to_string();
    for index in 0..2 {
        let structure = format!(
            "structure Package_{index} where\n  witness : VastitasKernel.IndexedRuntime.Object\n  field_0 : VastitasKernel.IndexedRuntime.Point\n\n"
        );
        text = text.replacen(&structure, "", 1);
    }
    text
}

/// Removes the prefix `legacy_flat::` from the messages and notes of the
/// diagnostics of `answer`, as the driver does for a flat protocol-9
/// request. Returns whether there was one.
fn without_flat_names(answer: &mut Value) -> bool {
    let prefix = format!("{FLAT_PACKAGE}::");
    let mut changed = false;
    let mut strip = |message: &mut Value| {
        if let Some(text) = message.as_str().filter(|text| text.contains(&prefix)) {
            *message = json!(text.replace(&prefix, ""));
            changed = true;
        }
    };
    for diagnostic in answer["diagnostics"].as_array_mut().into_iter().flatten() {
        strip(&mut diagnostic["message"]);
        for note in diagnostic["notes"].as_array_mut().into_iter().flatten() {
            strip(&mut note["message"]);
        }
    }
    changed
}

/// Every program of the corpus under `base`.
fn corpus(base: &Path) -> Vec<Program> {
    let mut programs = Vec::new();
    for directory in CORPUS {
        walk(base, &base.join(directory), false, &mut programs);
    }
    for fixture in WIRE_FIXTURES {
        programs.push(Program {
            name: fixture.to_string(),
            input: Input::Wire(base.join(fixture)),
            directory: base.to_path_buf(),
        });
    }
    programs.sort_by(|a, b| a.name.cmp(&b.name));
    programs
}

/// The packages under `directory` and, outside a package, its flat programs.
fn walk(base: &Path, directory: &Path, in_package: bool, programs: &mut Vec<Program>) {
    let relative = |path: &Path| {
        path.strip_prefix(base)
            .unwrap()
            .to_str()
            .unwrap()
            .to_string()
    };
    let in_package = in_package || directory.join("Vastitas.toml").is_file();
    if directory.join("Vastitas.toml").is_file() {
        programs.push(Program {
            name: relative(directory),
            input: Input::Package(relative(&directory.join("Vastitas.toml"))),
            directory: base.to_path_buf(),
        });
    }
    let mut entries: Vec<PathBuf> = fs::read_dir(directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            // The generated `std` entrypoint package of the stdlib is no
            // corpus program.
            if path.file_name().is_some_and(|name| name == "target") {
                continue;
            }
            walk(base, &path, in_package, programs);
        } else if !in_package
            && path
                .extension()
                .is_some_and(|extension| extension == "vast")
            && relative(&path).starts_with("examples/")
        {
            let name = relative(&path);
            let libraries = FLAT_LIBRARIES
                .iter()
                .find(|(file, _)| *file == name)
                .map(|(_, libraries)| libraries.iter().map(|l| l.to_string()).collect())
                .unwrap_or_default();
            programs.push(Program {
                name: name.clone(),
                input: Input::Flat(name, libraries),
                directory: base.to_path_buf(),
            });
        }
    }
}

/// Whether a source file of the program `input` under `base` uses `show!`.
fn observes(base: &Path, input: &Input) -> bool {
    match input {
        Input::Flat(file, _) => fs::read_to_string(base.join(file))
            .unwrap()
            .contains("show!("),
        Input::Package(manifest) => {
            let mut stack = vec![base.join(manifest).parent().unwrap().to_path_buf()];
            while let Some(directory) = stack.pop() {
                for entry in fs::read_dir(directory).unwrap() {
                    let path = entry.unwrap().path();
                    if path.is_dir() {
                        stack.push(path);
                    } else if path
                        .extension()
                        .is_some_and(|extension| extension == "vast")
                        && fs::read_to_string(&path).unwrap().contains("show!(")
                    {
                        return true;
                    }
                }
            }
            false
        }
        Input::Wire(_) => false,
    }
}

/// A copy of the corpus and of the packages that it depends on, with every
/// `show!(` of the corpus replaced by `(`.
fn observations_removed() -> Scratch {
    let copy = Scratch::empty("wire parity");
    for directory in COPIED {
        copy.copy_sources(&root().join(directory), directory, &[]);
    }
    for directory in CORPUS {
        let mut stack = vec![copy.0.join(directory)];
        while let Some(directory) = stack.pop() {
            for entry in fs::read_dir(directory).unwrap() {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    stack.push(path);
                } else if path
                    .extension()
                    .is_some_and(|extension| extension == "vast")
                {
                    let text = fs::read_to_string(&path).unwrap();
                    if text.contains("show!(") {
                        fs::write(&path, text.replace("show!(", "(")).unwrap();
                    }
                }
            }
        }
    }
    copy
}

/// The outcomes of `programs`, in their order, from a few worker threads.
fn run_all(programs: &[Program]) -> Vec<Outcome> {
    let next = AtomicUsize::new(0);
    let results: Mutex<Vec<Option<Outcome>>> =
        Mutex::new((0..programs.len()).map(|_| None).collect());
    let workers = std::thread::available_parallelism()
        .map(|count| count.get())
        .unwrap_or(1)
        .clamp(1, 4);
    std::thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                loop {
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    let Some(program) = programs.get(index) else {
                        break;
                    };
                    let outcome = run(program);
                    results.lock().unwrap()[index] = Some(outcome);
                }
            });
        }
    });
    results
        .into_inner()
        .unwrap()
        .into_iter()
        .map(Option::unwrap)
        .collect()
}

fn run(program: &Program) -> Outcome {
    let original = match &program.input {
        Input::Wire(path) => serde_json::from_str(&fs::read_to_string(path).unwrap()).unwrap(),
        input => match capture(&program.directory, input) {
            Ok(wire) => wire,
            Err(line) => return Outcome::Frontend(line),
        },
    };
    let from = original["version"].as_u64().unwrap();
    if from == CURRENT_PROTOCOL {
        return Outcome::Current;
    }
    let current = reencode(&original);
    let before = answers(&original);
    let after = answers(&current);
    let differences = compare(&before, &after);
    Outcome::Pair(Box::new(Pair {
        from,
        original,
        current,
        before,
        after,
        differences,
    }))
}

/// The wire request that `vastitas check` sends for `input`, run in
/// `directory`, or the first line of the diagnostics with which the frontend
/// rejects it. The capture backend echoes the request's own version, so the
/// driver accepts the version of its failure response.
fn capture(directory: &Path, input: &Input) -> Result<Value, String> {
    use std::os::unix::fs::PermissionsExt;
    let capture = Scratch::empty("parity capture");
    let stub = capture.write(
        "capture",
        "#!/bin/sh\nwire=\"$(dirname \"$0\")/wire.json\"\ncat > \"$wire\"\nversion=$(head -c 32 \"$wire\" | sed -n 's/^{\"version\":\\([0-9]*\\).*/\\1/p')\nprintf '{\"version\":%s,\"ok\":false,\"diagnostics\":[{\"code\":\"E_CAPTURED\",\"message\":\"captured\"}]}\\n' \"${version:-0}\"\nexit 1\n",
    );
    fs::set_permissions(&stub, fs::Permissions::from_mode(0o755)).unwrap();
    let mut command = cli();
    command
        .current_dir(directory)
        .env("VASTITAS_KERNEL", &stub)
        .arg("check");
    match input {
        Input::Flat(file, libraries) => {
            command.arg(file);
            for library in libraries {
                command.args(["--lib", library]);
            }
        }
        Input::Package(manifest) => {
            command.args(["--manifest-path", manifest]);
        }
        Input::Wire(_) => unreachable!(),
    }
    let output = command.output().unwrap();
    let wire = capture.0.join("wire.json");
    if wire.is_file() {
        Ok(serde_json::from_str(&fs::read_to_string(wire).unwrap()).expect("captured wire"))
    } else {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let first = stderr.lines().next().unwrap_or("").to_string();
        Err(first
            .strip_prefix(&format!("{}/", directory.display()))
            .map(str::to_string)
            .unwrap_or(first))
    }
}

/// The protocol-9 encoding of `original`: a package request with its version
/// and `input` replaced, or a flat request in the shape of
/// `packages::flat_request`.
fn reencode(original: &Value) -> Value {
    if original.get("packages").is_some() {
        let mut current = original.clone();
        current["version"] = json!(CURRENT_PROTOCOL);
        current["input"] = json!("package");
        current
    } else {
        flat_request(original)
    }
}

/// `packages::flat_request` on the JSON of a flat request: the unit is the
/// root module of the package `legacy_flat`, with every function, generic and
/// abstract type public.
fn flat_request(flat: &Value) -> Value {
    let public = |key: &str| -> Value {
        Value::Array(
            flat.get(key)
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .map(|item| {
                    let mut item = item.clone();
                    item["public"] = json!(true);
                    item
                })
                .collect(),
        )
    };
    let mut module = json!({
        "path": [],
        "public": true,
        "imports": [],
        "functions": public("functions"),
        "generics": public("generics"),
        "methods": flat["methods"],
        "span": {"start": 0, "end": 0, "line": 1, "column": 1},
    });
    let present = |key: &str| {
        flat.get(key)
            .and_then(Value::as_array)
            .is_some_and(|items| !items.is_empty())
    };
    if present("abstract_types") {
        module["abstract_types"] = public("abstract_types");
    }
    for key in ["subtypes", "abstract_methods"] {
        if present(key) {
            module[key] = flat[key].clone();
        }
    }
    json!({
        "version": CURRENT_PROTOCOL,
        "input": "package",
        "file": flat["file"],
        "root": FLAT_SOURCE,
        "packages": [{
            "source": FLAT_SOURCE,
            "name": FLAT_PACKAGE,
            "version": "1.0.0",
            "dependencies": [],
            "modules": [module],
        }],
    })
}

fn answers(wire: &Value) -> Answers {
    let respond = |mode: &str| -> Value {
        let output = kernel_bytes(mode, serde_json::to_vec(wire).unwrap());
        serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
            panic!(
                "invalid kernel response: {error}; {}",
                String::from_utf8_lossy(&output.stderr)
            )
        })
    };
    Answers {
        check: respond("check"),
        emit: respond("emit"),
    }
}

/// What differs between the answers to the original request and to its
/// protocol-9 encoding.
fn compare(before: &Answers, after: &Answers) -> Vec<String> {
    let mut found = Vec::new();
    for (mode, a, b) in [
        ("check", &before.check, &after.check),
        ("emit", &before.emit, &after.emit),
    ] {
        if a["ok"] != b["ok"] {
            found.push(format!("{mode}.ok {}→{}", a["ok"], b["ok"]));
        }
        let empty = Vec::new();
        let left = a["diagnostics"].as_array().unwrap_or(&empty);
        let right = b["diagnostics"].as_array().unwrap_or(&empty);
        if left.len() != right.len() {
            found.push(format!("{mode}.diagnostics {}→{}", left.len(), right.len()));
        }
        for (index, (x, y)) in left.iter().zip(right).enumerate() {
            for field in ["code", "message", "span", "notes"] {
                if x.get(field) != y.get(field) {
                    found.push(format!("{mode}.diagnostics[{index}].{field}"));
                }
            }
        }
    }
    if before.emit.get("lean_source") != after.emit.get("lean_source") {
        found.push("emit.lean_source".into());
    }
    for flag in ["storage_runtime", "numerical_runtime"] {
        let flag_of = |answer: &Value| answer.get(flag).cloned().unwrap_or(json!(false));
        if flag_of(&before.emit) != flag_of(&after.emit) {
            found.push(format!("emit.{flag}"));
        }
    }
    found
}

/// The directory of the report and the request pairs. Only the files of an
/// earlier report are removed from it.
fn output_directory() -> PathBuf {
    let directory = std::env::var_os("VASTITAS_WIRE_PARITY_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_TARGET_TMPDIR")).join("wire-parity"));
    let pairs = directory.join("pairs");
    if pairs.exists() {
        fs::remove_dir_all(&pairs).unwrap();
    }
    for file in ["report.txt", "pairs.json", "core.txt"] {
        let _ = fs::remove_file(directory.join(file));
    }
    fs::create_dir_all(&pairs).unwrap();
    directory
}

fn write(path: &Path, value: &Value) {
    write_text(path, &serde_json::to_string_pretty(value).unwrap());
}

fn write_text(path: &Path, text: &str) {
    fs::write(path, text).unwrap();
}

/// The kernel's answers to both requests, for the reader of the report.
fn write_answers(path: &Path, before: &Answers, after: &Answers) {
    write(
        path,
        &json!({
            "before": {"check": before.check, "emit": before.emit},
            "after": {"check": after.check, "emit": after.emit},
        }),
    );
}

/// The JSON shape of `flat_request` above is the frontend's: a flat unit with
/// an observation is a protocol-9 request in that shape, so the flat request
/// of its source, re-encoded, is the request that `vastitas check` sends.
#[test]
fn flat_reencoding_matches_the_frontend_flat_request() {
    for (file, source) in [
        (
            "hello.vast",
            include_str!("../examples/book/programs/hello.vast"),
        ),
        (
            "contracts.vast",
            include_str!("../examples/abstract-contracts.vast"),
        ),
    ] {
        let scratch = Scratch::empty("parity flat");
        scratch.write(file, source);
        let sent = capture(&scratch.0, &Input::Flat(file.into(), Vec::new())).unwrap();
        assert_eq!(sent["version"], CURRENT_PROTOCOL, "{file}");
        let flat = common::request(source, file);
        assert_eq!(reencode(&flat), sent, "{file}");
    }
}
