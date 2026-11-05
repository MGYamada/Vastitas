# Specifications

A *specification* records the properties of a language construct or of a
standard-library module, apart from the code that implements them. A
*property* states one mathematical fact and gives an example of it. A *claim*
says what establishes a property, and each claim has exactly one *claim
status*. People write and review the specification files. Two checks then
confirm that the evidence of every claim exists and still matches:
`scripts/check_spec.py` and the resolver `scripts/spec_resolve.lean`.

A specification never changes what the compiler accepts or generates.

## Properties and claims

A property has:

- an *id*, such as `differential.pullback.composition`, that begins with the
  id of its file;
- a title and a *subject*, the module item or construct that it is about;
- a *statement*;
- a link to the one section of the book that states the rule;
- an example, with the test that runs it, or the reason that no test runs it;
- one or more claims.

The statement summarizes the property for readers. The cited theorem's
statement is the authority: a statement in a specification file never
widens what a theorem proves.

A claim has a name, such as `oracle` or `test`, a status, and the evidence that
its status requires. One property often needs several claims. For example, the
kernel accepts nondegenerate evidence only after it computes an inverse of the
Gram matrix and checks it again. The oracle proves that this check is sound,
and the bridge proves what it means. That the search for an inverse always
succeeds is only tested. Each of these facts is a claim of its own.

## Claim statuses

| Status | Meaning | Evidence that the checks look up |
| --- | --- | --- |
| <a id="proved-oracle"></a>Proved (oracle) | A mathlib-free theorem in `lean/` states it | Fully qualified names of theorems under `VastitasOracle`. Each one reaches only the axioms `propext`, `Classical.choice` and `Quot.sound`, and has its pinned statement |
| <a id="proved-bridge"></a>Proved (bridge) | A mathlib theorem in `lean-bridge/` states it | The same, for theorems under `VastitasBridge`, in the bridge environment |
| <a id="tested"></a>Tested | A test that a CI step runs exercises it | A Rust test `tests/<file>.rs::<function>`, a Python test `<directory>/test_<name>.py::<Class>::<method>`, or a module that `scripts/check_kernel_regressions.sh` builds |
| <a id="assumed"></a>Assumed | A trusted component supplies it | An entry of the assumption registry |
| <a id="not-claimed"></a>Not claimed | It is outside the profile | A reason |
| <a id="planned"></a>Planned | A GitHub issue proposes it, and nothing establishes it | The number of the issue |

Proved, Tested and Planned keep the meanings that the
[Introduction](index.md#what-exists-today) gives them. Proved (oracle) and
Proved (bridge) name the environment of the theorem. Implemented stays a word
for features: no claim has that status.

The rules for claims:

- A Proved claim must list in `premises` the hypotheses that its theorems do
  not discharge. An empty list states that there are none.
- A Proved or Tested claim may list in `assumes` the registry entries that
  its evidence rests on.
- A Tested claim's tests must exist, and a CI step must run each of them. A CI
  step is a `run:` step of a workflow that runs on pull requests. A Rust test
  marked `#[ignore]` needs a step that passes `--ignored` or
  `--include-ignored` and selects it. A Python test that is skipped without a
  condition is not run.
- An Assumed claim must cite entries of the assumption registry,
  `docs/spec/assumptions.toml`. Its chapter lists every claim that cites each
  entry.
- A Not claimed claim must give a reason, and a Planned claim must give an
  issue number.

The checks infer no status and upgrade none. A claim whose evidence does not
resolve is an error; the checks do not turn it into a Planned claim.

## Enforcement

A claim may name, in `enforced_by`, the kernel definition that rejects
violations of the property and the diagnostic code that it reports.
Enforcement is not a status. That the kernel rejects every violation is
itself a claim, and that claim is Proved or Tested. The code must appear in
the [diagnostics reference](appendix/diagnostics.md), and the definition must
exist in the kernel.

## Specification files

Each public module or construct has one TOML file under `docs/spec/`. The file
`docs/spec/<name>.toml` generates the chapter `docs/spec/<name>.md`. A file
starts with a `[spec]` table and holds one table for each property, with one
subtable for each claim:

```toml
[spec]
id = "differential"
title = "std::differential"
subject = "std::differential"
description = "Laws of the metric-free pullback of `std::differential`."

[property."differential.pullback.identity"]
title = "Identity"
subject = "std::differential::pullback"
statement = "Pullback along the identity map is the identity on covectors."
specified_in = "[ADR 0001 §10, Laws](adr/0001-mathematics-first-stdlib.md#laws)"
example = "The identity of the plane pulls (5, 7) at (1, 2) back to (5, 7)."
example_test = "tests/smooth_differential.rs::smooth_example_checks_builds_and_executes"

[property."differential.pullback.identity".claim.oracle]
status = "proved-oracle"
evidence = ["VastitasOracle.SmoothRuntime.pullback_identity"]
premises = ["the seed lies over the point", "the seed has as many components as the point has coordinates"]
```

| Table | Keys |
| --- | --- |
| `[spec]` | `id`, `title`, `subject`, `description` |
| `[property."<id>"]` | `title`, `subject`, `statement`, `specified_in`, `example`, and exactly one of `example_test` and `example_not_executed` |
| `[property."<id>".claim.<name>]` | `status`, the keys that the status requires (`evidence`, `premises`, `reason` or `issue`), and optionally `assumes`, `enforced_by` and `note` |

`specified_in` is one Markdown link to a book chapter, relative to `docs/`.
An unknown key is an error, as is a missing one.

A specification file may hold two kinds of record. `property` records are the
ones above. `symbol` records describe one public mathematical symbol each, for
the standard-library admission manifest: its owner, its counterparts and its
properties. Their fields are not defined yet, so a `symbol` record is an
error. A symbol record will cite the properties that state its meaning, and
its proof, test and executability states will follow from their claims. The
six claim statuses therefore stay the only status words.

## Statement pins

The files `docs/spec/pins/oracle.json` and `docs/spec/pins/bridge.json` pin
every Lean name that a claim cites. A pin records the name's defining module,
its kind (theorem or kernel definition) and, for a theorem, the hash of its
statement.

The hash is the SHA-256 of a canonical text of the statement. The text holds
the theorem's universe parameters and its type: constants, universe levels,
de Bruijn indices and literals. It leaves out binder names, binder annotations
and metadata. Every form in the text delimits itself, so two different types
have different texts.

A changed statement fails the resolver until someone reviews the change and
regenerates the pins. The pin's diff is where people approve a statement
change. A pin covers the statement's expression only. It does not cover the
bodies of the definitions that the statement names, so a changed definition
keeps its pin.

## What the checks verify

`scripts/check_spec.py` needs no Lean. It rejects:

- a malformed file, an unknown or missing key, and a `symbol` record;
- a duplicate property id or file id, and a property id outside its file's id;
- an unknown status, Tested evidence under a Proved status, and a theorem name
  that is not fully qualified under the root of its environment;
- a cited Lean name without a pin, a pin that no claim cites, and a pinned
  module without a source file;
- a missing test file, test function or test method, a test that no CI step
  runs, and a module that the kernel regression script does not build;
- an unknown diagnostic code and an unknown assumption;
- a Planned claim without an issue and a Not claimed claim without a reason;
- an example with neither a test nor a not-executed mark;
- a `specified_in` link to a missing chapter;
- a generated chapter that is missing, out of date or absent from the
  contents, and a chapter under `docs/spec/` that no file generates.

`scripts/spec_resolve.lean` imports exactly the modules that a pins file lists.
It rejects:

- a pinned name that the modules do not define;
- a name outside the root of the environment, which is `VastitasOracle` for
  oracle theorems, `VastitasKernel` for kernel definitions and `VastitasBridge`
  for bridge theorems;
- a declaration defined in another module, or of another kind, than its pin;
- a theorem that reaches any axiom other than `propext`, `Classical.choice` and
  `Quot.sound`, such as `sorryAx`;
- a theorem whose statement differs from its pin.

Before it checks anything, the resolver checks its SHA-256 against fixed test
vectors. The axiom search walks types, values and constructors itself, as the
axiom audit does. `scripts/test_check_spec.py` tests each rejection of
`check_spec.py` on fixture repositories. `scripts/check_spec_lean.py` tests each
rejection of the resolver on fixture modules. It also compares the resolver's
SHA-256 with Python's on the canonical text.

## Boundaries

- Specifications reach no wire request, kernel input or generated code, and
  cost nothing at run time.
- A claim grants no acceptance, authority or evidence to a program.
- The specification layer adds no kernel check, no axiom and no trusted code.
  The resolver is a check, like the axiom audit.
- The oracle resolver needs no mathlib. The bridge resolver runs only in the
  bridge workflow.
- A property about storage must cite storage theorems, because pure-Core
  results do not extend to mutable storage
  ([verification boundaries](verification.md#what-is-outside-these-claims)).

## Maintenance

Run from the repository root:

```sh
python3 scripts/check_spec.py
python3 scripts/check_spec.py --write
```

The first command checks the files. The second regenerates the chapters after
a change to a specification file. Add a generated chapter to `SUMMARY.md` under
this chapter.

A claim that cites a Lean name needs a pin. The update runs the resolver in the
built package of the environment, so build that package first. Then review the
diff of the pins file:

```sh
lake -d lean build VastitasOracle
python3 scripts/check_spec.py --update-statements oracle
(cd lean-bridge && lake build)
python3 scripts/check_spec.py --update-statements bridge
```

The bridge build and the bridge update load Mathlib. Run them one at a time,
as [memory budget for local verification](development/validation.md#memory-budget-for-local-verification)
describes. To run the resolver and its regressions as CI does:

```sh
(cd lean && VASTITAS_SPEC_INPUT=../docs/spec/pins/oracle.json \
  lake env lean -DwarningAsError=true ../scripts/spec_resolve.lean)
lake -d lean env python3 scripts/check_spec_lean.py
```

CI runs `check_spec.py` and `test_check_spec.py` in "Rust formatting and
lint", and `check_spec_lean.py` in "Lean proofs and axiom audit".

## History

The specification layer is
[#647](https://github.com/MGYamada/Vastitas/issues/647). The decision to use
one file format for properties and for the symbol records of the
standard-library admission manifest is recorded on
[#285](https://github.com/MGYamada/Vastitas/issues/285#issuecomment-6646014436).
