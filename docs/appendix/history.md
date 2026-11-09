# Appendix E: Historical roadmap and Stage 1 records

The compiler grew in historical stages. This appendix keeps the plan for the
stages ahead and the records of the stage already delivered. The teaching
chapters describe the current language; these pages describe how it got there
and where it is going.

- [Historical Stages 2–7](../guide/historical-roadmap.md) follows one line of
  development from the coordinate ring of an affine scheme to an observable
  compared with physical measurements. Current GitHub issue decisions govern
  the plan, and each stage names an example that could establish completion.
- [Stage 1 delivery and performance handoff](../stage1-completion.md) records
  the finite Stage 1 delivery, its validation and the performance acceptance
  that moved to Stage 2 or later.
- [Finite-profile acceptance and evidence](../stage1-acceptance.md) maps each
  initial numerical and storage contract to its implementation, tests, theorems
  and native evidence at the recorded revisions.

These records cite exact revisions and measurements. The teaching chapters and
the Vastitas Reference describe the behaviour of the current compiler.

## Source migrations

A source migration changes the spelling that a program must use. The
compiler rejects the old spelling with a diagnostic that names the new one.

### Named edit recipients

The recipient of a `grant`, `delegation` or `transfer` was once written as a
manifest location and a module path, `to module("../addon/Vastitas.toml", "ops")`.
That form is an error (`E_UNSUPPORTED`). To migrate a declaration:

1. Read the `[package] name` of the manifest that the old form named.
2. Write the recipient as that name followed by the module path:
   `to addon::ops`, or `to addon` for the root module.
3. Use neither the directory name of the manifest nor a dependency alias.

Moving the recipient package then changes only the dependency manifests, not
the issuing source. [Grants and delegations](../language/edit-authority.md#grants-and-delegations)
gives the rules. The migrations of the `fn` family form and of `assemble`
([#462](https://github.com/MGYamada/Vastitas/issues/462),
[#455](https://github.com/MGYamada/Vastitas/issues/455)) are separate and
pending.
