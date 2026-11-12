# Appendix E: Historical roadmap and delivery records

The compiler is developed in numbered Stages. This appendix holds the plan for
the Stages ahead, the records of the Stages that are delivered, and the
[source migrations](#source-migrations). The guide and the Vastitas Reference
describe the language as it is. These pages record how it was built and what
is Planned.

- [Historical Stages 2–7](../guide/historical-roadmap.md) follows one line of
  development, from the coordinate ring of an affine scheme to an observable
  that is compared with physical measurements. Each Stage has an example that
  could establish its completion. Stages 2 and 3 are delivered as finite
  profiles, and Stages 4 to 7 are Planned. The GitHub issues that the chapter
  links govern the plan.
- A **delivery record** maps the acceptance conditions of a delivery to their
  evidence at recorded revisions: the implementation, the tests, the theorems
  and the native measurements. The delivery records are archived. They keep
  the wording of their delivery, and the style guide of this book does not
  apply to them.
  - [Stage 1 delivery and performance handoff](../stage1-completion.md)
    records the finite Stage 1 delivery, its validation and the performance
    acceptance that it left open.
  - [Finite-profile acceptance and evidence](../stage1-acceptance.md) maps
    each numerical and storage contract of Stage 1 to its implementation,
    tests, theorems and native evidence.
  - [Stage 2 finite affine geometry acceptance](../stage2-acceptance.md) is
    the record of presented affine geometry over the rational numbers.
  - [Stage 3 smooth affine geometry acceptance](../stage3-acceptance.md) is
    the record of smooth affine geometry and reverse pullbacks.
  - [Compiled reverse Core acceptance](../reverse-core-acceptance.md) is the
    record of the reverse passes that the kernel compiles.

A delivery record states what held at its revisions. For the behaviour of the
compiler today, read the guide and the Vastitas Reference. For the theorems
and their assumptions, read
[Verification boundaries](../verification.md).

## Source migrations

A source migration changes the spelling that a program must use. The compiler
rejects the old spelling with a diagnostic that names the replacement.

### Named edit recipients

The recipient of a `grant`, `delegation` or `transfer` was once written as a
manifest location and a module path, `to module("../addon/Vastitas.toml", "ops")`.
That form is an error (`E_UNSUPPORTED`). To migrate a declaration:

1. Read the `[package] name` of the manifest that the old form named.
2. Write the recipient as that name followed by the module path:
   `to addon::ops`, or `to addon` for the root module. The name must be an
   identifier: a package named `add-on` cannot be a recipient.
3. Use neither the directory name of the manifest nor a dependency alias.

Moving the recipient package then changes only the dependency manifests, not
the issuing source. [Grants and delegations](../language/edit-authority.md#grants-and-delegations)
gives the rules.

### Planned migrations

Two migrations are Planned, and each is separate from the migration above:

- the single family form of every named `fn`
  ([#462](https://github.com/MGYamada/Vastitas/issues/462));
- the `assemble` blocks that replace the flat `assembly` trace
  ([#455](https://github.com/MGYamada/Vastitas/issues/455)).
