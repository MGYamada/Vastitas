# Scoped edit borrowing and validated assemblies

The assembly model originated in the protocol-5 increment under #64 and #154–158. It is a
finite package-only increment, not completion of historical Stage 1.
The subsequent [protocol-6 extension](edit-authority.md) adds nested reborrowing
and permanent edit-authority transfer while preserving protocol-5 wire
compatibility. Current source recipients use protocol 9 as described below.
Protocols 2–6 now enter `Indexed.LegacySource.check` and the common
`Indexed.AuthoritySource` checker; the retained `checkEditProgram` composition
is documented separately in [verification boundaries](verification.md).

## Source declarations

The generic's exact module declares a grant:

```vast
pub grant integers : choose to addon::ops {
  domain (Int, Int);
}
```

`addon` is the recipient's manifest `[package] name`, not an import or dependency
alias. The rest is its exact logical module path; `to addon` denotes its root.
Protocol 9 carries this unresolved name and path. Lean independently traverses
the root's dependency graph, requires exactly one selected package with that
name, and then checks the distinct exact module. Different versions, locations,
module availability and declaration order do not disambiguate equal names.
The issuer need not depend on the recipient. Grant resolution never loads a
package, and injected records unreachable from the root cannot become recipients.
The region lists concrete scalar tuples; `domain;` permits an empty region.
A grant does not authorize membership or abstract-contract edits.

This is Rust-shaped path syntax with a different resolution rule: Rust/Cargo
uses the caller's dependency names (including renames), while edit recipients
use manifest names across the selected closure. Ordinary Vastitas call/import
resolution still uses its existing dependency aliases.

### Migrating recipients for v0.1.0

The old source form `to module("../addon/Vastitas.toml", "ops")` is removed.
Read that selected manifest's `[package] name`, then rewrite it as
`to addon::ops`; use `to addon` for an empty module path. Do not substitute the
manifest's directory name or a dependency alias. A name must be expressible as
an ordinary source path component. Same-name packages are rejected; version
qualification and root-bound recipient roles are deferred. Apply the same
rewrite to `grant`, `delegation` and `transfer`. Moving the recipient only
requires updating dependency manifests, not the issuing source.

Wire protocols 2–8 retain their original decoders and recipient-location records.
Protocol 9 uses the full protocol-8 pure/resource composition, even for a
pure-only edit assembly. As in protocols 7/8, legacy geometry spellings on this
route require an explicit validated library `geometry_compat` export. The
separate `fn`-family and `assemble` migrations (#462/#455) remain pending; this
recipient change does not complete their v0.1.0 gates.

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
See [current routes and proof boundaries](verification.md#current-public-checker-routes)
for the public `LegacySource`/`IndexedAuthority` connection and
[the retained protocol-5 composition](verification.md#scoped-edit-assembly-acceptance-protocol-5)
for the older `checkEditProgram` theorem statements. The current JSON regression
is `VastitasPublicTest.AuthorityRegression`; old `EditRegression` remains a
separate check of retained APIs and shared trace logic.


Try the complete example:

```sh
cargo run -- check --manifest-path examples/packages/edit-borrow/app/Vastitas.toml
cargo run -- build --manifest-path examples/packages/edit-borrow/app/Vastitas.toml -o /tmp/vastitas-edit
/tmp/vastitas-edit # 42
```

The [non-punitive diagnostic reference](diagnostic-reference.md) reuses the
crossing-method return/repair regression for presentation and identity experiments.
Its synthetic attribution records are not a checker-derived provenance ledger.
