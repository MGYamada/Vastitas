//! The records that the checker keeps of the writes to one allocation. A
//! write beyond their limit is an error with the code of the limit, at the
//! write. A store that continues the run of cells of the last recorded write
//! extends that record, so that consecutive stores initialize a view of any
//! length and a cell that no path writes stays uninitialized.
mod common;
use common::{Scratch, success};

/// `vastitas check` of a package whose root module is `source`.
fn checked(source: &str) -> std::process::Output {
    let scratch = Scratch::empty("initialization records");
    scratch.write(
        "Vastitas.toml",
        "[package]\nname = \"records\"\nversion = \"0.1.0\"\nroot = \"src/main.vast\"\n",
    );
    scratch.write("src/main.vast", source);
    common::manifest_command("check", scratch.0.join("Vastitas.toml"))
        .output()
        .unwrap()
}

/// The first line of the diagnostic of `source`, which the checker rejects.
fn rejected(source: &str) -> String {
    let output = checked(source);
    assert!(!output.status.success(), "unexpected acceptance:\n{source}");
    let message = String::from_utf8(output.stderr).unwrap();
    message.lines().next().unwrap().to_owned()
}

fn accepted(source: &str) {
    success(&checked(source));
}

/// `main.vast:LINE:5`, the place of the first statement that contains `marker`.
fn line_of(source: &str, marker: &str) -> String {
    let line = source
        .lines()
        .position(|line| line.contains(marker))
        .unwrap()
        + 1;
    format!("main.vast:{line}:5")
}

fn store(cell: usize) -> String {
    format!("store(w, {cell}, 0, f64_bits(0));")
}

/// A function that allocates `cells` cells, writes them through one loan with
/// `body` and then borrows `layout(offset, rows, 1, rows, false)` for reading.
fn program(cells: usize, body: &[String], read: Option<(usize, usize)>) -> String {
    let mut lines = vec![
        "resource fn main() -> Int {".to_owned(),
        "    let c: Bool = value { true };".to_owned(),
        format!("    allocate d: F64[{cells}];"),
        format!("    borrow w = write(d, layout(0, {cells}, 1, {cells}, false));"),
    ];
    lines.extend(body.iter().map(|line| format!("    {line}")));
    lines.push("    release(w);".to_owned());
    if let Some((offset, rows)) = read {
        lines.push(format!(
            "    borrow r = read(d, layout({}, {rows}, 1, {rows}, false));",
            8 * offset
        ));
        lines.push("    release(r);".to_owned());
    }
    lines.extend(["    drop(d);", "    value { 0 }", "}"].map(str::to_owned));
    lines.join("\n") + "\n"
}

fn stores(cells: impl IntoIterator<Item = usize>) -> Vec<String> {
    cells.into_iter().map(store).collect()
}

fn branch(yes: impl IntoIterator<Item = usize>, no: impl IntoIterator<Item = usize>) -> String {
    format!(
        "if c {{ {} }} else {{ {} }}",
        stores(yes).join(" "),
        stores(no).join(" ")
    )
}

/// The program of the issue on the cells `spacing * index`: two stores, then
/// `joins` `if` statements whose arms each store two cells, the second of them
/// the same in both arms, then `finals` stores.
fn joins(spacing: usize, joins: usize, finals: usize) -> String {
    let cell = |index: usize| spacing * index;
    let mut body = stores([cell(0), cell(1)]);
    for k in 0..joins {
        body.push(branch(
            [cell(3 * k + 2), cell(3 * k + 3)],
            [cell(3 * k + 3), cell(3 * k + 4)],
        ));
    }
    body.extend(stores((0..finals).map(|k| cell(3 * joins + 2 + k))));
    program(80, &body, None)
}

#[test]
fn a_write_beyond_the_initialization_records_reports_the_limit() {
    // With every index doubled no two cells are adjacent and no record merges.
    // Each join keeps the records of both arms: nine joins leave 4091 nodes,
    // and five further writes reach the 4096 of the limit.
    accepted(&joins(2, 9, 5));
    let sixth = joins(2, 9, 6);
    let message = rejected(&sixth);
    assert!(
        message.ends_with(&format!(
            "{}: E_RESOURCE_LIMIT: write initialization metadata budget exceeded: \
             the record of the writes to one allocation holds at most 4096 nodes",
            line_of(&sixth, &store(2 * 34))
        )),
        "{message}"
    );
    // A tenth join is beyond the limit at the join.
    let tenth = joins(2, 10, 0);
    let message = rejected(&tenth);
    assert!(
        message.ends_with(&format!(
            "{}: E_RESOURCE_LIMIT: branch join initialization metadata budget exceeded",
            line_of(&tenth, &store(2 * 29))
        )),
        "{message}"
    );
    // The program of the issue stores consecutive cells: its records merge, and
    // each join after the first leaves the one cell that its arms share.
    accepted(&joins(1, 9, 6));
    accepted(&joins(1, 20, 6));
}

#[test]
fn consecutive_single_stores_initialize_a_view_of_any_length() {
    for count in [255, 256, 1024] {
        accepted(&program(count, &stores(0..count), Some((0, count))));
        accepted(&program(count, &stores((0..count).rev()), Some((0, count))));
    }
    // The expansion of calls admits at most 2040 stores beside the other
    // statements of this function.
    accepted(&program(2040, &stores(0..2040), Some((0, 2040))));
}

#[test]
fn a_cell_that_no_store_writes_stays_uninitialized() {
    for count in [8, 256, 1024] {
        let missing = count / 2 - 1;
        let source = program(
            count,
            &stores((0..count).filter(|&cell| cell != missing)),
            Some((0, count)),
        );
        let message = rejected(&source);
        assert!(
            message.ends_with(&format!(
                "{}: E_RESOURCE_INIT: requested read region is not initialized at logical row \
                 {missing}, column 0 of the view (physical row {missing}, column 0; \
                 allocation bytes [{}, {}))",
                line_of(&source, "borrow r ="),
                8 * missing,
                8 * missing + 8
            )),
            "{message}"
        );
        // The cells on either side of the gap are readable.
        let before = stores((0..count).filter(|&cell| cell != missing));
        accepted(&program(count, &before, Some((0, missing))));
        accepted(&program(
            count,
            &before,
            Some((missing + 1, count - missing - 1)),
        ));
    }
}

#[test]
fn stores_in_the_arms_of_an_if_initialize_the_cells_of_both_arms() {
    // Arms that store the same cells, in either order, initialize them.
    accepted(&program(256, &[branch(0..256, 0..256)], Some((0, 256))));
    accepted(&program(
        256,
        &[branch(0..256, (0..256).rev())],
        Some((0, 256)),
    ));
    // An arm that continues the stores before the `if` initializes nothing for
    // the other arm: the cells that both arms write are readable, the others not.
    let mut body = stores(0..100);
    body.push(branch(100..256, []));
    let extended = program(256, &body, Some((0, 256)));
    assert!(
        rejected(&extended).ends_with(
            "requested read region is not initialized at logical row 100, column 0 of the \
             view (physical row 100, column 0; allocation bytes [800, 808))"
        ),
        "{extended}"
    );
    accepted(&program(256, &body, Some((0, 100))));
    // Arms that store complementary halves initialize no cell of the view.
    let halves = program(256, &[branch(0..128, 128..256)], Some((0, 256)));
    assert!(
        rejected(&halves).ends_with(
            "requested read region is not initialized at logical row 0, column 0 of the \
             view (physical row 0, column 0; allocation bytes [0, 8))"
        ),
        "{halves}"
    );
    // Overlapping arms leave the cells that they share.
    let shared = [branch(0..200, 50..256)];
    accepted(&program(256, &shared, Some((50, 150))));
    let message = rejected(&program(256, &shared, Some((49, 151))));
    assert!(
        message.ends_with(
            "at logical row 0, column 0 of the view (physical row 0, column 0; \
             allocation bytes [392, 400))"
        ),
        "{message}"
    );
}
