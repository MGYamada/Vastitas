# Kernel-reduction feasibility workload

This experiment supplies the first reduction-cost measurement for
[#749](https://github.com/MGYamada/Vastitas/issues/749). It does not implement
production MidIR, a public compiler mode, or authenticated proof-to-artifact
admission. A passing run does not close that issue.

`Model.lean` defines a straight-line typed SSA fragment with natural constants,
addition, multiplication, equality and selection. Register IDs are instruction
positions; references must point backwards and have the required type. Its
target replaces arithmetic with a closed set of runtime-call symbols. The
target interpreter models those calls with mathematical natural operations; it
does not run or prove a foreign runtime.

The generated source and target lists are serialized separately. The validator
checks source typing, the complete target against the specified lowering, and
an explicit index witness. Independent source and target interpreters supply
the observation. `accepted_refines` proves their result equality for every
source, target and witness accepted by this isolated validator.

Each chunk has an actual `decide` (or `rfl`) proof of acceptance and an
application of the soundness theorem. It also proves rejection of a changed
final target call and a changed final witness entry. Separate negative proofs
cover forward references and using a Boolean as a natural operand. Splitting
the workload measures a proposed per-function proof granularity; it is not a
whole-module composition theorem.

## Run

From the repository root:

```sh
python3 -m unittest discover -s experiments/compiler_validation/reduction -p 'test_*.py'
python3 experiments/compiler_validation/reduction/run.py --operations 1000 --chunk-size 1000
python3 experiments/compiler_validation/reduction/run.py --operations 1000 --chunk-size 64 \
  --output target/compiler-validation/reduction-chunk64.json
```

Use `--proof rfl` to select definitional reduction instead of `decide`.
`--timeout` bounds each child process (300 seconds by default). A timeout,
failed child, invalid export or incomplete nanoda report fails the experiment.
`--logs` prints temporary child diagnostics on failure.

The runner creates a private temporary Lake package with no dependencies and
removes it afterwards. It copies the model, generates the workload and uses
only the repository's pinned Lean 4.35.0 toolchain. It neither builds nor
modifies the production kernel or oracle. It uses `scripts/replay_lean.sh`
with one Lean worker and an explicit module. Run it without another heavy
Lean build, as the repository's validation guide requires.

The four measured phases are elaboration, official-kernel replay, export and
the toolchain's nanoda 0.4.19 audit. Replay checks the workload module against
its imported model; the selected export includes the model and transitive
declaration dependencies. Export names both the module and every target
theorem: a valid prefix without any requested theorem cannot pass. The runner
checks the format/toolchain identity, permitted axiom names, declaration
structure, unsupported records and the exact declaration count reported by
nanoda. It does not authenticate the standard axiom statements as a production
Fast-mode bundle; the report explicitly records that limitation.

`wait4` supplies elapsed CPU and peak resident-set measurements without
`time -l` or a platform timer. Its peak RSS is not the sum of simultaneous
process memory. Output records contain OS/architecture, toolchain, workload
and export identities, measured phases and status, without local paths or
user/host names. Reports go under ignored `target/` unless `--output` selects
another location.

## Evidence boundary

The retained JSON records are exploratory macOS arm64 runs of this isolated
fragment. They are not a controlled timing comparison or a compilation-time
budget: host variation, filesystem caches and chunk granularity affect them.
Each record describes its own workload and theorem list. Linux evidence,
production Core/MidIR artifacts, CFG/block parameters, ownership/effects,
LLVM-byte binding and compiler Fast/Official admission remain separate work.

The general theorem and the concrete `decide` proofs contain no native
evaluation proof shortcut. The exported closure uses the permitted `propext`
and `Quot.sound` axioms. nanoda audits the complete exported closure but remains
an external checker, not the official Lean kernel.
