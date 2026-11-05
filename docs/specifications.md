# Specifications

A *specification* records the properties of a language construct or of a
standard-library module, apart from the code that implements them. A
*property* states one mathematical fact and gives an example of it. A *claim*
records what establishes a property, or why nothing does, and each claim has
exactly one *claim status*. People write and review the specification files.
Two checks then confirm that the evidence of every claim exists, that each
cited theorem keeps its reviewed statement, and that a CI step runs each cited
test: `scripts/check_spec.py` and the resolver `scripts/spec_resolve.lean`.

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
and the [mathematical bridge](verification.md#independent-mathematical-bridge)
proves what it means. Only tests show that the search finds an inverse of
every invertible Gram matrix. Each of these facts is a claim of its own.

## Claim statuses

| Status | Meaning | Evidence that the checks look up |
| --- | --- | --- |
| <a id="proved-oracle"></a>Proved (oracle) | A mathlib-free theorem in `lean/` states it | Fully qualified names of theorems under `VastitasOracle`, each with its pinned statement and only approved axioms |
| <a id="proved-bridge"></a>Proved (bridge) | A mathlib theorem in `lean-bridge/`, the mathematical bridge, states it | The same, for theorems under `VastitasBridge` |
| <a id="tested"></a>Tested | A test that a CI step runs exercises it | A Rust test `tests/<file>.rs::<function>`, a Python test `<directory>/test_<name>.py::<Class>::<method>`, or a module that `scripts/check_kernel_regressions.sh` builds |
| <a id="assumed"></a>Assumed | A trusted component supplies it | An entry of the assumption registry |
| <a id="not-claimed"></a>Not claimed | It is outside the finite profile that the specification covers | A reason |
| <a id="planned"></a>Planned | A GitHub issue proposes it, and nothing establishes it | The number of the issue |

Proved, Tested and Planned keep the meanings that the
[Introduction](index.md#what-exists-today) gives them. Proved (oracle) and
Proved (bridge) name the *specification environment* of the theorem: the
oracle environment, which resolves theorems under `VastitasOracle` and kernel
definitions under `VastitasKernel`, or the bridge environment, which resolves
theorems under `VastitasBridge`. Implemented stays a word for features: no
claim has that status.

The rules for claims:

- A Proved claim must list in `premises` the hypotheses that its theorems do
  not discharge. An empty list states that there are none.
- A Proved or Tested claim may list in `assumes` the entries of the assumption
  registry that relate its evidence to the property as the statement reads
  it. For example, a theorem about the kernel's checked declarations stands
  for a rule about source declarations only through the Rust frontend.
- A Tested claim's tests must exist, and a CI step must run each of them. An
  ignored Rust test must be selected by a step that passes `--ignored` or
  `--include-ignored`. A Rust test under `#[cfg(...)]`, other than
  `cfg(test)`, does not count as run, nor does a Python test that a decorator
  always skips: `skip`, `skipIf(True, …)` or `skipUnless(False, …)`.
- An Assumed claim must cite entries of the assumption registry,
  `docs/spec/assumptions.toml`. The registry's chapter,
  [Assumptions](spec/assumptions.md), lists every claim that cites each entry.
- A Not claimed claim must give a reason, and a Planned claim must give an
  issue number.

The checks infer no status and upgrade none. A claim whose evidence does not
resolve is an error; the checks do not turn it into a Planned claim.

### Enforcement

A Proved or Tested claim may name, in `enforced_by`, the kernel definitions
that reject violations of the property and the diagnostic codes that they
report:

```toml
enforced_by = [{ definition = "VastitasKernel.SmoothDeclarations.certifyNondegenerate", code = "E_METRIC" }]
```

Enforcement is not a status. That the kernel rejects every violation is itself
a claim, and that claim is Proved or Tested. Each code must appear in the
[diagnostics reference](appendix/diagnostics.md), and each definition must
exist in the kernel.

## Specification files

A specification file covers one public module or construct. The file
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
example = "The identity of the plane pulls the covector (5, 7) at (1, 2) back to itself."
example_test = "tests/smooth_differential.rs::smooth_example_checks_builds_and_executes"

[property."differential.pullback.identity".claim.oracle]
status = "proved-oracle"
evidence = ["VastitasOracle.SmoothRuntime.pullback_identity"]
premises = ["the seed lies over the point and has one component per coordinate of the point"]
```

| Table | Required keys | Optional keys |
| --- | --- | --- |
| `[spec]` | `id`, `title`, `subject`, `description` | |
| `[property."<id>"]` | `title`, `subject`, `statement`, `specified_in`, `example`, and exactly one of `example_test` and `example_not_executed` | |
| `[property."<id>".claim.<name>]`, Proved | `status`, `evidence`, `premises` | `assumes`, `enforced_by`, `note` |
| the same, Tested | `status`, `evidence` | `assumes`, `enforced_by`, `note` |
| the same, Assumed | `status`, `evidence` | `note` |
| the same, Not claimed | `status`, `reason` | `note` |
| the same, Planned | `status`, `issue` | `note` |

The file id is lower-case words joined by hyphens, and a property id is
dot-separated words that begin with the file id. `specified_in` is one Markdown
link to a book chapter, relative to `docs/`. Titles hold no `|`, `[`, `]`, `<`,
`>` or backquote. An unknown key is an error, as is a missing one.

The assumption registry, `docs/spec/assumptions.toml`, holds one table
`[assumption.<id>]` for each trusted component, with a `title` and a
`statement`.

The table name `symbol` is reserved for the symbol records of the
standard-library admission manifest, one for each public mathematical symbol.
Their fields are undefined, so a `symbol` table is an error. The
[History](#history) section records the planned design.

## Statement pins

The files `docs/spec/pins/oracle.json` and `docs/spec/pins/bridge.json` pin
every theorem and kernel definition that a claim cites. A pin records the
defining module and the kind of the name and, for a theorem, the hash of its
statement. A cited kernel definition must be a `def` that is not `partial`.
When no claim cites a name of an environment, its pins file and its CI step
must not exist.

The hash is the SHA-256 of a canonical text of the statement. The text holds
the theorem's universe parameter names and its type: constants, universe
levels, de Bruijn indices and literals. It leaves out binder names, binder
annotations and metadata. Every form in the text delimits itself, so two types
that differ other than in those have different texts.

A changed statement fails the resolver until someone reviews the change and
regenerates the pins. The pin's diff is where people approve a statement
change. A pin covers the statement's expression only. It does not cover the
bodies of the definitions that the statement names, so a changed definition
keeps its pin.

## What the checks verify

`scripts/check_spec.py` needs no Lean. It rejects:

- a malformed file, an unknown or missing key, and a `symbol` table;
- a duplicate property id or file id, and a property id outside its file's id;
- an unknown status, Tested evidence under a Proved status, and a theorem name
  that is not fully qualified under the root of its specification environment;
- a cited name without a pin, a pin that no claim cites, a pinned module
  without a source file, and a pins file of an environment that no claim cites;
- a missing test file, test function or test method, a test that no CI step
  runs, and a module that the kernel regression script does not build;
- an unknown diagnostic code and an unknown assumption;
- a Planned claim without an issue and a Not claimed claim without a reason;
- an example with neither `example_test` nor `example_not_executed`;
- a `specified_in` link to a missing chapter;
- a generated chapter that is missing, out of date or absent from the
  contents, and a chapter under `docs/spec/` that no file generates.

A CI step is a `run:` step of a workflow that every pull request starts: its
`pull_request` trigger has no `paths`, `branches` or `types` filter. A step,
or its job, with an `if:` condition or with a `continue-on-error` that can be
true does not count. `check_spec.py` reads each step with a model of the
shell. It follows `cd` and `working-directory`, and it ignores comments,
quoted text, redirections and here-document bodies. A command whose failure
cannot fail the step does not count: the condition of an `if`, a command
before `||`, a command before `|` without `pipefail`, and a command after
`set +e`. It recognizes `cargo test` in the root package, with its target,
filter, `--skip`, `--exact`, `--ignored`, `--no-run` and `--list` options,
`python3 -m unittest discover`, and runs of the kernel regression script. A
form that it does not model counts as not running a test.

`scripts/spec_resolve.lean` imports exactly the modules that a pins file lists.
It rejects:

- a pinned name that the modules do not define, or that two modules declare;
- a name outside the root of its environment;
- a declaration defined in another module, or of another kind, than its pin;
- a pinned declaration that reaches an axiom other than `propext` of
  `Init.Core` and `Classical.choice` and `Quot.sound` of `Init.Prelude`, such
  as `sorryAx`, or a constant that the imported modules do not define;
- a theorem whose statement differs from its pin, and a statement whose
  canonical text exceeds 4 MiB.

Before it checks anything, the resolver checks its SHA-256 against fixed test
vectors. The axiom search walks types, values and constructors itself, as the
axiom audit does. Lean merges declarations of one name and one type on import,
as it does for the equation lemmas that several modules generate, and keeps
one copy. The search therefore walks every copy that a project module
declares. `scripts/test_check_spec.py` tests each rejection of `check_spec.py`
listed above on fixture repositories, and `scripts/check_spec_lean.py` tests
each rejection of the resolver on fixture modules. The latter also compares
the resolver's SHA-256 with Python's on the canonical text.

No check verifies what people review:

- that the premises list every hypothesis of the cited theorems;
- that a statement, an example or a note says what the evidence establishes;
- that a cited test exercises the property or runs the example;
- that an `enforced_by` definition reports its code;
- that a Planned claim's issue exists and is open.

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

A claim that cites a theorem or a kernel definition needs a pin.
`--update-statements` runs the resolver in the built package of the
environment, so build that package first. It imports the root of the
environment, `VastitasOracle` or `VastitasBridge`, so a cited name must be
reachable from that root. Then review the diff of the pins file:

```sh
lake -d lean build VastitasOracle
python3 scripts/check_spec.py --update-statements oracle
(cd lean-bridge && lake build)
python3 scripts/check_spec.py --update-statements bridge
```

The bridge build, the bridge update and the bridge resolver load mathlib. Run
them one at a time, as
[memory budget for local verification](development/validation.md#memory-budget-for-local-verification)
describes. To run the resolvers and their regressions as CI does:

```sh
(cd lean && VASTITAS_SPEC_INPUT=../docs/spec/pins/oracle.json \
  lake env lean -DwarningAsError=true ../scripts/spec_resolve.lean)
(cd lean-bridge && VASTITAS_SPEC_INPUT=../docs/spec/pins/bridge.json \
  lake env lean -DwarningAsError=true ../scripts/spec_resolve.lean)
lake -d lean env python3 scripts/check_spec_lean.py
```

CI runs the checks in three places:

- "Rust formatting and lint" runs `check_spec.py` and `test_check_spec.py`.
- "Lean proofs and axiom audit" runs the oracle resolver on
  `docs/spec/pins/oracle.json`, after it builds every kernel library and the
  oracle, and runs `check_spec_lean.py`.
- The mathematical bridge workflow runs the bridge resolver on
  `docs/spec/pins/bridge.json` after it builds the bridge. A change to that
  file or to the resolver starts the workflow.

## History

[#647](https://github.com/MGYamada/Vastitas/issues/647) proposes the
specification layer. [#285 records the decision](https://github.com/MGYamada/Vastitas/issues/285#issuecomment-6646014436)
to use one file format for properties and for the symbol records of the
standard-library admission manifest. In that design a symbol record cites the
properties that state its meaning, and its proof, test and executability
states follow from their claims, so the six claim statuses stay the only
status words. [#649](https://github.com/MGYamada/Vastitas/issues/649) tracks
the seed linearity of the pullback, which no theorem states.
