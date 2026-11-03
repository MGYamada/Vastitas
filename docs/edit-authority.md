# Nested edit loans and permanent authority transfer

The protocol-6 model extends the [protocol-5 assembly](edit-borrowing.md) for
#181/#182. Current source uses protocol-9 named recipients; see the
[recipient migration](edit-borrowing.md#migrating-recipients-for-v010).
The immutable function identity is still its defining package, module and name.
The current editor is tracked separately, with a complete transfer history.
This is compile-time assembly of one fixed environment, not runtime mutation.

## Explicit delegation

An owner grant permits reborrowing only when marked `delegable`:

```vast
pub grant outer : choose to addon delegable {
  domain (Int, Int);
}
```

The borrower must separately declare its delegation to an exact module:

```vast
pub delegation inner : base::choose to addon::ops {
  domain (Int, Int);
}
```

The root coordinates the declared permissions:

```vast
assembly {
  borrow base::outer as parent;
  reborrow parent via addon::inner as child;
  apply addon::ops::sum using child;
  return child;
  return parent;
  seal base::choose;
}
```

Every child names the same canonical function, is declared by the exact parent
borrower, and has a region contained in its parent's region. A delegation may
itself be `delegable`. Parent loans remain present but suspended until their
child is returned. Only the leaf may edit or delegate; return proceeds from
the inside out. Loan names are never reused. All events count toward the shared
4096-event bound. Empty regions are allowed but cannot authorize a final winner.

## Permanent transfer

The current owner declares a named operation; an assembly cannot invent the
issuer or recipient:

```vast
pub transfer handoff : choose to addon;
```

After every loan has returned, `transfer base::handoff;` consumes that operation
and changes the current owner to its declared recipient. Transfer to a sealed
generic, a repeated transfer operation, or a transfer declared by a module
that is no longer the owner is rejected. The new owner can use
`apply addon::repair;`; the former owner loses direct contribution authority.
Transfer alone requires final sealing, even if it installs no methods.

All existing methods, grants, contribution records and open dispatch obligations
survive transfer. Grants from established owners remain declared permissions;
they still require active loans. A new owner's grant becomes usable only after
that module receives authority. Every owner grant, including unused grants,
must be issued by a module that actually holds authority at some point in the
validated history. Transfer declarations are also checked against that history.
Unused delegations have no authority without an active explicitly delegable
parent. All recipients must be distinct existing exact modules in the selected
dependency closure; declaring a permission never loads another package.

The initial ordinary methods remain part of the defining module's fixed input.
Post-transfer edits use named contributions. Transferring a generic does not
transfer abstract-type membership or abstract-method contract authority: those
continue to require the exact defining module. No transfer of an ordinary `fn`
body or individual method is supported.

## Completion, provenance and proof boundary

The complete declaration bodies are independently reconstructed. Each applied
contribution records its effective grant/delegation chain and authority history.
An identical replay under identical provenance is idempotent; changed provenance
under one contribution ID is rejected. The prefix audit separately checks the
current owner, leaf exclusivity, region containment, all state preservation and
each history/declaration correspondence.

Returning a loan and transferring authority can leave ambiguity or coverage
obligations Open. Authorized repairs are allowed before sealing. Final assembly
checks all scalar keys, generic/contract coverage, every applicable body including
nonwinners, unapplied contributions, and winning footprints within every ancestor
grant. Transfer does not repair or discard an obligation by itself.

`VastitasOracle.Authority` proves properties of the shared `Authority.assemble`
trace, current-owner/leaf requirements, preserved contribution provenance and
ancestor-region inclusion. Its `checkAuthorityProgram_*` results concern the
retained old top-level checker. Current public composition is connected by
`IndexedAuthority.authority_trace`, `applied_authorized`, `final_footprints`,
`instance_body_checked` and `both_passes`; `LegacySource`/`IndexedWire` connect
the actual JSON acceptance to that composition and the exact returned indexed
Core. `IndexedProgramSafety` supplies its typed total evaluation. These are
decoded-input guarantees, not legacy source-correspondence results, filesystem/authorship
authentication, parser correctness or native-code equivalence. Storage ownership
and the eight mathematical domain checkers remain separate contracts (#180/#184).

`VastitasPublicTest.AuthorityRegression` exercises protocol-5/6/7/8 compatibility
and protocol 9 with separate historical and current Rust-frontend fixtures,
exact returned-Core evaluation/emission and
forged source/authority mutations. `AuthorityRegression` remains a separate
test of the retained checker and shared trace helpers.

```sh
cargo run -- check --manifest-path examples/packages/edit-authority/app/Vastitas.toml
cargo run -- build --manifest-path examples/packages/edit-authority/app/Vastitas.toml -o target/edit-authority
./target/edit-authority # 44
```

Protocol 5 and existing source inputs retain their wire decoders, then enter
`Indexed.LegacySource.check` and the common indexed authority/body checker.
`checkAuthorityProgram` is a retained legacy API, not Main's public route. Protocol 6
uses the package envelope, optional `delegable` on grants, new `delegations` and
`transfers` module arrays, and `reborrow`/`transfer` events. Older envelopes reject
these semantic fields instead of ignoring them. See [the wire contract](protocol.md).


Protocol 9 replaces `grantee_source` with `grantee_package` in all three
recipient-bearing declarations, retaining the exact `grantee_path`. Both forms
cannot be combined. `Namespace.recipientCandidates` reconstructs the root-selected
package graph and `recipientPackage` rejects missing or ambiguous names before
module resolution. `Edit.lowerGrant` (also used for delegations) and
`Authority.lowerTransfer` preserve the selected package's full identity.
`VastitasOracle.EditRecipients` proves these actual lowering connections and
exposes complete declaration replay from the public `ResourceSource.Wire`
certificate. No filesystem or authorship authentication is claimed.
