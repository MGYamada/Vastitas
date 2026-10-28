# Nested edit loans and permanent authority transfer

Protocol 6 extends the [protocol-5 assembly](edit-borrowing.md) for #181/#182.
The immutable function identity is still its defining package, module and name.
The current editor is tracked separately, with a complete transfer history.
This is compile-time assembly of one fixed environment, not runtime mutation.

## Explicit delegation

An owner grant permits reborrowing only when marked `delegable`:

```vast
pub grant outer : choose to module("../addon/Vastitas.toml", "") delegable {
  domain (Int, Int);
}
```

The borrower must separately declare its delegation to an exact module:

```vast
pub delegation inner : base::choose to module("Vastitas.toml", "ops") {
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
pub transfer handoff : choose to module("../addon/Vastitas.toml", "");
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

`VastitasOracle.Authority` proves properties of the actual protocol-6 checker,
its trace, current-owner/leaf requirements, preserved contribution provenance,
ancestor-region inclusion, final footprints, and the exact returned typed and
dependency-ordered Core. The same pure-Core evaluation theorem applies after
assembly. These are decoded-input guarantees, not filesystem/authorship
authentication, parser correctness or native-code equivalence. Storage ownership
and the eight mathematical domain checkers remain separate contracts (#180/#184).

```sh
cargo run -- check --manifest-path examples/packages/edit-authority/app/Vastitas.toml
cargo run -- build --manifest-path examples/packages/edit-authority/app/Vastitas.toml -o target/edit-authority
./target/edit-authority # 44
```

Protocol 5 and existing source inputs retain their existing route. Protocol 6
uses the package envelope, optional `delegable` on grants, new `delegations` and
`transfers` module arrays, and `reborrow`/`transfer` events. Older envelopes reject
these semantic fields instead of ignoring them. See [the wire contract](protocol.md).
