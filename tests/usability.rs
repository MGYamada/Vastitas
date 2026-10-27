use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static SERIAL: AtomicU64 = AtomicU64::new(0);
struct Scratch(PathBuf);
impl Scratch {
    fn new(source: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "vastitas-usability-{}-{}",
            std::process::id(),
            SERIAL.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("main.vast"), source).unwrap();
        Self(path)
    }
    fn cli(&self, mode: &str) -> Command {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_vastitas"));
        cmd.current_dir(&self.0).args([mode, "main.vast"]);
        cmd
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn success(output: &Output) {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}
fn rejection(source: &str, code: &str) -> String {
    let scratch = Scratch::new(source);
    let output = scratch.cli("check").output().unwrap();
    assert!(!output.status.success());
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(error.contains(&format!(": {code}: ")), "{error}");
    error
}

#[test]
fn block_comments_and_package_field_order_have_specific_diagnostics() {
    let source = "fn main() -> Int {\n    /* comment */\n    0\n}";
    let errors = vastitas::frontend::parse(source, "comment.vast").unwrap_err();
    assert_eq!(&source[errors[0].span.start..errors[0].span.end], "/*");
    assert!(errors[0].message.contains("use // line comments"));
    for source in [
        "fn f() -> Pointed<Scheme, QQ> { let X = Affine(QQ, 1); pack { point: origin(X), scheme: X } }",
        "fn f(p: Pointed<Scheme, QQ>) -> Int { unpack p as { point: x, scheme: X }; 0 }",
    ] {
        assert!(rejection(source, "E_PARSE").contains("`scheme`, then `point`"));
    }
}

#[test]
fn native_explicit_embedding_and_else_if_preserve_exact_arithmetic() {
    let scratch = Scratch::new(
        "fn main() -> Int { let n: Nat = 123456789012345678901234567890; if false { 0 } else if dimension(Base(QQ)) == 0 { nat_to_int(n) - int(1) } else { -1 } }",
    );
    let library = Path::new(env!("CARGO_MANIFEST_DIR")).join("stdlib/src/arithmetic/nat.vast");
    let output = scratch
        .cli("build")
        .arg("--lib")
        .arg(library)
        .args(["-o", "program"])
        .output()
        .unwrap();
    success(&output);
    let output = Command::new(scratch.0.join("program")).output().unwrap();
    success(&output);
    assert_eq!(output.stdout, b"123456789012345678901234567889\n");
}

#[test]
fn explicit_embedding_has_no_implicit_or_reverse_conversion() {
    rejection("fn main() -> Int { let n: Int = 1; int(n) }", "E_TYPE");
    rejection("fn main() -> Int { let n: Nat = int(1); 0 }", "E_TYPE");
    rejection("fn main() -> Int { int(true) }", "E_TYPE");
    let message = rejection("fn main() -> Int { int(1, 2) }", "E_ARITY");
    assert!(
        message.contains("1 argument,") && !message.contains("1 arguments"),
        "{message}"
    );
}

#[test]
fn identity_diagnostics_name_objects_and_their_introduction_sites() {
    let message = rejection(
        "fn same(X: Scheme) -> Scheme { X }\nfn main() -> Int {\n let X = Affine(QQ, 2);\n let Y = same(X);\n let p: Point<Y, Base(QQ)> = origin(X);\n 0\n}",
        "E_TYPE",
    );
    assert!(
        message.contains("Point<Y,") && message.contains("Point<X,"),
        "{message}"
    );
    assert!(
        message.contains("main.vast:3:") && message.contains("main.vast:4:"),
        "{message}"
    );
    assert!(
        message.contains(": note:") && message.contains("same"),
        "{message}"
    );
}

#[test]
fn library_identity_notes_keep_library_source_locations() {
    let scratch = Scratch::new("fn main() -> Int { 0 }");
    fs::write(
        scratch.0.join("library.vast"),
        "// library\nfn bad(X: Scheme, Y: Scheme) -> Point<X, Base(QQ)> { origin(Y) }",
    )
    .unwrap();
    let output = scratch
        .cli("check")
        .args(["--lib", "library.vast"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let message = String::from_utf8(output.stderr).unwrap();
    assert!(
        message.contains("E_TYPE") && message.contains("library.vast:2:"),
        "{message}"
    );
    let notes: Vec<_> = message
        .lines()
        .filter(|line| line.contains(": note:"))
        .collect();
    assert!(!notes.is_empty(), "{message}");
    assert!(
        notes.iter().all(|line| line.contains("library.vast:2:")),
        "{message}"
    );
}

#[test]
fn unsupported_constructs_have_specific_diagnostics() {
    for source in [
        "fn main() -> Int { 7 / 2 }",
        "fn main() -> Int { 7 % 2 }",
        "fn main() -> Int { 1.5 }",
        "fn main() -> Int { return 1; }",
        "fn main() -> Int { while true { 0 } }",
        "fn main() -> Int { for x in 0 { 0 } }",
        "fn main() -> Int { loop { 0 } }",
        "fn main() -> Int { let mut x = 1; x }",
    ] {
        rejection(source, "E_UNSUPPORTED");
    }
}
