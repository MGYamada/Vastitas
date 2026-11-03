//! Flat-mode name resolution stays linear in local bindings (#552). This is a
//! separate test binary, so no concurrent test perturbs the timing.

// Entering a block, branch or lambda once copied the whole enclosing scope, so
// resolving n block-valued lets took quadratic time. Only the frontend runs;
// the kernel's per-function budget would reject such a body later. Plain lets
// are the machine-speed control: at this size the old copies cost several times
// more than parsing and resolving every binding.
#[test]
fn flat_scope_resolution_is_linear_in_local_bindings() {
    let count = 90_000;
    let program = |binding: &dyn Fn(usize) -> String| {
        let mut source = String::from("fn main() -> Int {\n");
        for i in 0..count {
            source.push_str(&binding(i));
        }
        source.push_str("a0\n}\n");
        source
    };
    let plain = program(&|i| format!("let a{i}: Int = 0;\n"));
    let scoped = program(&|i| match i % 3 {
        0 => format!("let a{i}: Int = {{ 0 }};\n"),
        1 => format!("let a{i}: Int = if true {{ 0 }} else {{ 1 }};\n"),
        _ => format!("let a{i} = fn(x: Int) -> Int {{ x }};\n"),
    });
    let time = |source: &str| {
        let start = std::time::Instant::now();
        let module = vastitas::frontend::parse(source, "lets.vast").unwrap();
        let elapsed = start.elapsed();
        assert_eq!(module.functions[0].body.statements.len(), count);
        elapsed
    };
    // Alternate the measurements and keep the fastest of each.
    let (mut fastest_plain, mut fastest_scoped) =
        (std::time::Duration::MAX, std::time::Duration::MAX);
    for _ in 0..2 {
        fastest_plain = fastest_plain.min(time(&plain));
        fastest_scoped = fastest_scoped.min(time(&scoped));
    }
    eprintln!("{count} plain lets: {fastest_plain:?}; block-valued lets: {fastest_scoped:?}");
    assert!(
        fastest_scoped < fastest_plain * 4,
        "{count} block-valued lets took {fastest_scoped:?}; plain lets took {fastest_plain:?}"
    );
}
