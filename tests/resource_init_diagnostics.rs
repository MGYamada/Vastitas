//! The diagnostic of a read borrow whose view is not initialized. The kernel
//! decides the rejection first; the text after `requested read region is not
//! initialized` only explains it. A named cell must be one that the checked
//! writes do not cover, and a rejection without such a cell must name none.
mod common;
use common::{Scratch, cli, success};

/// A padded fill of two stored rows, read through a transposed view of three
/// stored rows.
const PADDED_TRANSPOSE: &str = "resource fn main() -> Int {
    allocate data: F64[8];
    borrow w = write(data, layout(8, 2, 2, 4, false));
    fill(w, f64(0.25));
    store(w, 0, 1, f64(3.0));
    release(w);

    borrow r = read(data, layout(8, 3, 2, 4, true));
    expect(r, 1, 0, f64(3.0));
    expect(r, 0, 1, f64(0.25));
    release(r);
    drop(data);
    value { 0 }
}";

/// Two fills of stored rows with gaps between their cells. Together they
/// write all eight cells, but the checker joins no such fills.
const INTERLEAVED: &str = "resource fn main() -> Int {
    allocate data: F64[8];
    borrow low = write(data, layout(0, 2, 2, 4, false));
    fill(low, f64(1));
    release(low);
    borrow high = write(data, layout(16, 2, 2, 4, false));
    fill(high, f64(2));
    release(high);
    borrow r = read(data, layout(0, 4, 2, 4, false));
    release(r);
    drop(data);
    value { 0 }
}";

const REJECTED: &str = "requested read region is not initialized";
const NO_CELL: &str = ": the bounded check could not establish that the preceding writes cover the region, \
    and a bounded search found no uninitialized cell";

fn fixture(source: &str) -> Scratch {
    let scratch = Scratch::empty("resource init diagnostics");
    scratch.write(
        "Vastitas.toml",
        "[package]\nname = \"diagnostics\"\nversion = \"0.1.0\"\nroot = \"src/main.vast\"\n",
    );
    scratch.write("src/main.vast", source);
    scratch
}

fn run(scratch: &Scratch, mode: &str) -> std::process::Output {
    let mut command = cli();
    command
        .args([mode, "--manifest-path"])
        .arg(scratch.0.join("Vastitas.toml"));
    if mode == "build" {
        command.arg("-o").arg(scratch.0.join("program"));
    }
    command.output().unwrap()
}

fn location(source: &str, marker: &str) -> String {
    let before = &source[..source.find(marker).unwrap()];
    let line = before.bytes().filter(|&byte| byte == b'\n').count() + 1;
    let column = before.rsplit('\n').next().unwrap().chars().count() + 1;
    format!("main.vast:{line}:{column}")
}

/// `check` and `build` reject `source` at `borrow r` with the code, the
/// first sentence and `reason` as the whole primary message, and keep the
/// note that names the allocation.
fn rejected(source: &str, reason: &str) -> String {
    let scratch = fixture(source);
    let mut messages = Vec::new();
    for mode in ["check", "build"] {
        let output = run(&scratch, mode);
        assert!(
            !output.status.success(),
            "unexpected acceptance: {output:?}"
        );
        assert!(!scratch.0.join("program").exists());
        let message = String::from_utf8(output.stderr).unwrap();
        let primary = format!(
            "{}: E_RESOURCE_INIT: {REJECTED}{reason}",
            location(source, "borrow r =")
        );
        assert!(
            message.lines().next().unwrap().ends_with(&primary),
            "expected {primary}\n{message}"
        );
        let note = format!(
            "{}: note: borrowed allocation is `data`, introduced here",
            location(source, "allocate data")
        );
        assert!(message.contains(&note), "missing {note}\n{message}");
        messages.push(message);
    }
    assert_eq!(messages[0], messages[1], "check and build differ");
    messages.remove(0)
}

fn accepted(source: &str) -> Scratch {
    let scratch = fixture(source);
    success(&run(&scratch, "check"));
    scratch
}

#[test]
fn a_padded_transposed_read_names_its_uncovered_cell_in_both_conventions() {
    // Stored row 2 of stored column 0 is the first cell that the fill of two
    // stored rows leaves out. The transposed view has it in row 0, column 2,
    // and it starts 8 + 2 * 8 bytes into the allocation.
    rejected(
        PADDED_TRANSPOSE,
        " at logical row 0, column 2 of the view \
         (physical row 2, column 0; allocation bytes [24, 32))",
    );

    // The explanation changes no decision: the view of two stored rows is
    // accepted, and its executable reads the cells that the program wrote.
    let covered = PADDED_TRANSPOSE.replace("layout(8, 3, 2, 4, true)", "layout(8, 2, 2, 4, true)");
    let scratch = accepted(&covered);
    success(&run(&scratch, "build"));
    let output = std::process::Command::new(scratch.0.join("program"))
        .output()
        .unwrap();
    success(&output);
    assert_eq!(output.stdout, b"0\n");

    // The logical coordinates are those that `store` takes: writing the named
    // cell moves the diagnostic to the other uncovered cell, in stored column 1.
    rejected(
        &PADDED_TRANSPOSE.replace("    release(w);\n", &stores("store(gap, 0, 2, f64(1));")),
        " at logical row 1, column 2 of the view \
         (physical row 2, column 1; allocation bytes [56, 64))",
    );
}

/// `PADDED_TRANSPOSE` with `statements` on a write loan of the rejected view.
fn stores(statements: &str) -> String {
    format!(
        "    release(w);\n    borrow gap = write(data, layout(8, 3, 2, 4, true));\n    \
         {statements}\n    release(gap);\n"
    )
}

#[test]
fn a_rejection_without_an_uncovered_cell_names_no_cell() {
    // Every cell of each view is written, and the checker rejects the read
    // because it does not join a fill of stored rows that have gaps with
    // another write. The diagnostic must not claim an unwritten cell.
    let completed = PADDED_TRANSPOSE.replace(
        "    release(w);\n",
        &stores("store(gap, 0, 2, f64(1)); store(gap, 1, 2, f64(1));"),
    );
    for source in [INTERLEAVED, &completed] {
        let message = rejected(source, NO_CELL);
        for word in ["logical", "physical", "column", "bytes"] {
            assert!(!message.contains(word), "{word} in\n{message}");
        }
    }

    // No cell is uncovered: each of the eight cells is readable alone.
    let cells = (0..8)
        .map(|cell| {
            format!(
                "    borrow r{cell} = read(data, layout({}, 1, 1, 1, false));\n    release(r{cell});\n",
                8 * cell
            )
        })
        .collect::<String>();
    accepted(&INTERLEAVED.replace(
        "    borrow r = read(data, layout(0, 4, 2, 4, false));\n    release(r);\n",
        &cells,
    ));
}

#[test]
fn a_cell_written_in_one_arm_only_is_uncovered_after_the_join() {
    let source = "resource fn main() -> Int {
    let flag: Bool = value { true };
    allocate data: F64[2];
    borrow w = write(data, layout(0, 2, 1, 2, false));
    if flag { fill(w, f64(1)); } else { store(w, 0, 0, f64(1)); }
    release(w);
    borrow r = read(data, layout(0, 2, 1, 2, false));
    release(r);
    drop(data);
    value { 0 }
}";
    rejected(
        source,
        " at logical row 1, column 0 of the view \
         (physical row 1, column 0; allocation bytes [8, 16))",
    );
    accepted(&source.replace("store(w, 0, 0, f64(1));", "fill(w, f64(2));"));
}

#[test]
fn the_bytes_of_a_complex_cell_and_an_unwritten_allocation_are_exact() {
    // A cell of `Complex<F64>` has 16 bytes.
    let source = "resource fn main() -> Int {
    allocate data: Complex<F64>[4];
    borrow w = write(data, layout(0, 1, 1, 1, false));
    fill(w, complex(1, 0));
    release(w);
    borrow r = read_write(data, layout(0, 2, 2, 2, true));
    release(r);
    drop(data);
    value { 0 }
}";
    rejected(
        source,
        " at logical row 0, column 1 of the view \
         (physical row 1, column 0; allocation bytes [16, 32))",
    );
    // Without a write the first cell of the view is uncovered.
    rejected(
        &source.replace("    fill(w, complex(1, 0));\n", ""),
        " at logical row 0, column 0 of the view \
         (physical row 0, column 0; allocation bytes [0, 16))",
    );
}

#[test]
fn large_views_are_explained_without_enumerating_their_cells() {
    // A step of the search passes the 2^30 cells of the fill at once.
    let half = "resource fn main() -> Int {
    allocate data: F64[2147483647];
    borrow w = write(data, layout(0, 1073741824, 1, 1073741824, false));
    fill(w, f64(1));
    release(w);
    borrow r = read(data, layout(0, 2147483647, 1, 2147483647, false));
    release(r);
    drop(data);
    value { 0 }
}";
    rejected(
        half,
        " at logical row 1073741824, column 0 of the view \
         (physical row 1073741824, column 0; allocation bytes [8589934592, 8589934600))",
    );

    // A step passes a whole stored column that the fill covers, so the search
    // reaches the unwritten last column of a thousand.
    let column = "resource fn main() -> Int {
    allocate data: F64[2000000000];
    borrow w = write(data, layout(0, 1000000, 999, 2000000, false));
    fill(w, f64(1));
    release(w);
    borrow r = read(data, layout(0, 1000000, 1000, 2000000, true));
    release(r);
    drop(data);
    value { 0 }
}";
    rejected(
        column,
        " at logical row 999, column 0 of the view \
         (physical row 0, column 999; allocation bytes [15984000000, 15984000008))",
    );

    // Two fills of stored rows cover both cells of each of 2^31 - 1 stored
    // columns. The check does not join them, and the search ends by its bound
    // long before the last column: it names no cell.
    let rows = "resource fn main() -> Int {
    allocate data: F64[6442450941];
    borrow low = write(data, layout(0, 1, 2147483647, 3, false));
    fill(low, f64(1));
    release(low);
    borrow high = write(data, layout(8, 1, 2147483647, 3, false));
    fill(high, f64(2));
    release(high);
    borrow r = read(data, layout(0, 2, 2147483647, 3, false));
    release(r);
    drop(data);
    value { 0 }
}";
    rejected(rows, NO_CELL);
}
