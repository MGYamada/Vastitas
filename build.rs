use std::{env, fs, path::PathBuf};

fn main() {
    let path = "lean-kernel/compiler-limits.json";
    println!("cargo:rerun-if-changed={path}");
    let limits: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(path).expect("read compiler limits"))
            .expect("parse compiler limits");
    let mut source = String::new();
    for (key, name) in [
        ("parseNesting", "MAX_PARSE_NESTING"),
        ("astDepth", "MAX_AST_DEPTH"),
        ("moduleNesting", "MAX_MODULE_NESTING"),
        ("packageNesting", "MAX_PACKAGE_NESTING"),
    ] {
        let value = limits[key]
            .as_u64()
            .expect("positive integer compiler limit");
        assert!(value > 0 && usize::try_from(value).is_ok());
        source.push_str(&format!("pub const {name}: usize = {value};\n"));
    }
    let output = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo output directory"));
    fs::write(output.join("compiler_limits.rs"), source).expect("write compiler limits");
}
