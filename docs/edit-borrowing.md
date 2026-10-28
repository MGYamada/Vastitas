# Scoped edit borrowing and validated assemblies

This is the protocol-5 implemented increment under #64 and #154–158. It is a
finite package-only increment, not completion of historical Stage 1.

## Source declarations

The generic's exact module declares a grant:

```vast
pub grant integers : choose to module("../addon/Vastitas.toml", "ops") {
  domain (Int, Int);
}
```

The quoted manifest location is relative to the issuer's manifest. It must
identify a package already in the root's selected dependency closure. The
second quoted string is its exact logical module path; `""` denotes the root.
Grant resolution never loads a package. The region lists concrete scalar tuples;
`domain;` permits an empty region. A grant does not authorize membership or
abstract-contract edits.

The grantee declares a named block for one generic:

```vast
pub contribution refine : lib::choose {
  method lib::choose(x: Int, y: Int) -> Int { x + y }
}
```

A contribution has a stable identity from its declaring package, module and
name; each contained method has its ordinal within that declaration. Aliases
preserve this identity. Contributions do not inspect intermediate method tables.
Their methods may use the existing finite selectors and capabilities; they have
bodies and are never abstract contracts.

At most one assembly occurs, in the root package's root module:

```vast
assembly {
  borrow lib::integers as edit;
  apply addon::ops::refine using edit;
  return edit;
  seal lib::choose;
}
```

Omitting the root assembly is equivalent to `assembly { }`. Consumers of a
library that declares grants need not activate those grants. Grant declarations
and every unapplied contribution body still undergo independent checking;
assemblies in dependency packages or child modules remain invalid.

An owner contribution uses `apply owner::repair;` without a loan. It is forbidden
while that generic is borrowed. The root coordinates this declarative trace;
it does not acquire arbitrary edit authority. Grant and contribution visibility
uses ordinary namespace rules. New words are contextual; existing unrelated
bindings named `grant`, `borrow`, `seal` or `contribution` remain legal.

## State and completion

A grant is permission, not an active loan. Borrowing is exclusive per canonical
generic identity. Loan names cannot be reused. Return preserves all installed
methods and may leave the generic Open. Owner repair after return is allowed.
Sealing with an outstanding loan, applying outside the appropriate loan, using
an alias to overlap loans, and editing a sealed generic are rejected.

Exact replay of a contribution under the same effective grant is idempotent.
Changed provenance under the same identity and duplicate normalized signatures
under different identities are rejected. The immutable decoded declarations
supply bodies and origins, rather than an application event's claimed metadata.

Seal completion uses the final environment: all-key ambiguity, generic/contract
domain-union coverage, exact contract result types and final winning footprints
within each grant's region. A sealed family cannot subsequently change; its
completion is checked before acceptance. Every applicable body, including losing
bodies, is checked. Unapplied contributions are checked against the final
environment but supply no dispatch candidates. All borrowed generics must be
returned and every edited generic explicitly sealed; untouched generics undergo
the previous completion checks.

Any changed input causes whole-closure validation. There is no format for cached
winner choices, trusted owner flags or reused specialized code. Decoded-input
consistency does not authenticate files or authors. Reborrowing from a borrower,
owner transfer, runtime method mutation, incremental caches, recursion extensions,
geometry migration, storage ownership and linear algebra are outside this increment.

## Wire extension

Protocol 5 requires `input: "package"`. Modules may additionally contain
`grants`, `contributions` and `assembly`; unknown fields in these new declaration
and event records are rejected.
Grants retain `name`, unresolved `target`, canonical `grantee_source`,
`grantee_path`, concrete `region`, `public` and `span`. Contributions retain
`name`, unresolved `target`, original `methods`, `public` and `span`.
Assembly retains `events` and `span`; events have `op` values
`borrow`/`apply`/`return`/`seal`, unresolved declaration paths and loan names.
No event contains an asserted owner, body replacement, accepted flag or winner.

Inputs without new declarations retain protocol 2, 3 or 4 and `--lib`
compatibility. Resource bounds are in `lean-kernel/compiler-limits.json`: 4096 events, 4096
contribution methods, and 4096 ground instances in the unapplied-body audit.
See [verification](verification.md#scoped-edit-assembly-acceptance-protocol-5)
for the actual checker theorem statements.


Try the complete example:

```sh
cargo run -- check --manifest-path examples/packages/edit-borrow/app/Vastitas.toml
cargo run -- build --manifest-path examples/packages/edit-borrow/app/Vastitas.toml -o /tmp/vastitas-edit
/tmp/vastitas-edit # 42
```
