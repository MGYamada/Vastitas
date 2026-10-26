# Stage 0 verification boundary

The proof oracle in `lean/` imports the implementation's definitions from
`lean-kernel/`. It has no executable target and is not consulted when compiling
or executing `.vast` programs. mathlib is pinned to v4.35.0; the executable
kernel depends only on the Lean distribution.

## What the proofs establish

- The actual `checkApply`, `checkCompose`, and `checkPack` rules satisfy explicit
  contracts on nominal endpoints and geometric bases when they accept.
- Base-preserving substitution retains type well-formedness and the association
  between a point and its target. Distinct fresh unpacked names cannot be mixed;
  a correctly unpacked point can be repackaged.
- The actual scope-checking rule accepts only endpoint references present in
  the outer scope (or canonical base objects). A fresh unpacked endpoint absent
  from that scope is rejected; a repackaged point does not expose that endpoint.
- The actual runtime definitions satisfy origin, identity, composition,
  application, and package-projection laws. Runtime descriptor equality alone
  is not used to establish nominal identity.
- The accepted-module boundary carries a checked proposition that all type
  annotations have compatible bases and every function body's annotated result
  equals its declared return type. `certifiedModule_annotation_property` exposes
  the property carried by this subtype; it is not a soundness theorem about
  `checkModule` or a relation between raw input and elaborated output.

These results use actual implementation definitions, rather than a copied
toy checker. They contain no `sorry`, `admit`, or project-specific unproved
axioms. CI audits the oracle namespace against Lean's standard logical axioms
(`propext`, `Classical.choice`, and `Quot.sound`).

## What remains a trust boundary

The finite annotation postcondition is not a proof of a full source-language
typing derivation or of the entire elaborator. Scope management, fresh-name
allocation, function dependency analysis, the Rust frontend, JSON transport,
and code generation are implemented and regression-tested. Their complete
semantic preservation proofs remain future work.

Lean's compiler, generated C, the C toolchain, linker, OS, and hardware are also
outside the proved claims. Native tests establish observed behavior for the
tested cases, not a proof of all native executions.

The ordinary/smooth affine descriptors are a restricted semantic skeleton.
The oracle does not formalize all schemes or C-infinity schemes, prove general
geometric constructions, establish numerical accuracy, or certify physical
adequacy. Any mathematical coordinate interpretation in the oracle is limited
to the stated zero/identity fragment.

## Executable checks

The Rust tests cover parsing and lexical scope, positive native examples,
nominal endpoint mismatches, base/setting mismatches, dependent arguments,
package escape, invalid scalar coercions, recursion, malformed/forged IR,
missing backends, and preservation of existing artifacts on failure.

The compiler CI job checks out the compiler without `lean/`, builds and tests
on macOS and Linux, and runs `scripts/check_boundaries.py` to ensure the kernel
has no external package dependency. The independent oracle job builds proofs
and audits their axioms.
