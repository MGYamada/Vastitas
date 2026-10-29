# Dense layout/preflight reference for Ownership/Borrow

Status: executable Python reference and finite regression evidence for
[#183](https://github.com/MGYamada/Vastitas/issues/183), following
[Storage/Ownership §§7.3–7.7, 7.12](storage-ownership.md). The Lean statements
below are **proposed proof obligations**, not implemented or proved theorems.
This is a component specification for the existing Ownership/Borrow Checker
(Core Safety), not a ninth Domain Checker or a second public acceptance path.
It does not complete #183, protocol 8, or the performance goal in
[#222](https://github.com/MGYamada/Vastitas/issues/222).

## Run and inspect

```sh
python3 scripts/storage_layout_reference.py
python3 -m unittest discover -s scripts -p 'test_storage_layout_reference.py' -v
```

The [reference](../scripts/storage_layout_reference.py) uses only the Python
standard library and arbitrary-precision integers. The existing CI discovery
of `test_*.py` includes the [regressions](../scripts/test_storage_layout_reference.py).
The demo prints decisions, never dereferences storage. No buffers, native
pointers, BLAS calls, output writes, or code generation enter its API.

## Closed initial profile

Each live allocation has an identity **and generation**, capacity in bytes,
integer base address and element width/alignment. `World` is an authoritative
fixture snapshot, with a resource epoch and all active loans. It rejects two
live generations of one identity and overlapping nonempty physical allocation
ranges with distinct identities. Actual allocator provenance and liveness must
come from the production resource environment; external metadata cannot assert
them. The integer address is only a model of a pointer, not proof that memory
exists. Initialization and allocator/device/ABI validity remain separate.

A rank-two layout has exact extents, byte strides, byte offset, element
representation, kind and a dense-source descriptor. Supported kinds are:

| Kind | Reconstruction and restrictions |
| --- | --- |
| Column-major dense | Source `(m,n,ld)`, shape `(m,n)`, strides `(w,ld*w)`; `ld >= max(1,m)` |
| Explicit transpose | That same source, shape `(n,m)`, strides `(ld*w,w)`; no conjugation or new allocation |
| Read-only broadcast | A dense source with singleton axes explicitly expanded; expanded strides are zero. Both axes may broadcast. Writes are rejected, including empty broadcasts |
| Other strided descriptors | Diagnostic input only; require additional evidence, even when their envelope is in bounds |

The leading-dimension rule also applies to empty metadata in this initial
profile. Negative strides, packed bits, rank other than two, arbitrary
permutations/partitions, foreign device storage, reshape and adjoint are not
admitted. Malformed rank/element metadata is invalid; a well-shaped negative
stride descriptor needs a separately specified extension. This is deliberately
incomplete, not a decision procedure for arbitrary strided layouts.

`Mode.READ`, `WRITE` and `READ_WRITE` denote requested access. WRITE does not
grant initialized-read rights. READ_WRITE still needs the separate initialization
audit before execution. The reference does not model moves, partial writes,
branch joins, reborrows, suspension, escape, asynchronous completion or retention.

## Separate decisions and closed-form arithmetic

`LayoutReport` separates metadata, provenance, profile reconstruction, bounds,
alignment, write injectivity and native conversion. A failed prerequisite
short-circuits dependent checks; a missing check is not a successful check.
The aggregate priority is INVALID, then NEEDS_EVIDENCE, then SAFE. SAFE means
only that all checks of this limited reference succeeded.

Let `w > 0` be the element byte width and `a > 0` its power-of-two alignment,
with `a | w`. For nonnegative byte strides `s0,s1`, define over integers:

```text
D(L)       = {(i,j) | 0 <= i < rows and 0 <= j < columns}
start(L,i,j) = offset + i*s0 + j*s1
bytes(L,i,j) = [start(L,i,j), start(L,i,j) + w)
region(L) = union of bytes(L,i,j) over D(L)       -- specification only
end(L)    = offset + (rows-1)*s0 + (columns-1)*s1 + w
```

For a nonempty view the range check is `0 <= offset` and `end(L) <= capacity`.
Alignment checks `(base + offset) % a = 0`, and `sk % a = 0` on each axis
whose extent exceeds one. Singleton axes impose no access-stride alignment
obligation. The actual absolute address is checked; an assumed aligned base
does not replace this calculation.

When **either extent is zero**, `D(L)` and `region(L)` are empty. The code
branches before computing either `extent-1`; validates `0 <= offset <= capacity`
and the descriptor/native fields; and produces no accessible envelope. Access
alignment/injectivity are vacuous, and an unaligned empty offset is permitted.
No element or one-past pointer is formed or dereferenced. Empty metadata can
still fail generation, shape, leading-dimension or native narrowing checks.

For dense writes, different columns are separated by `ld*w >= rows*w` and
different rows by `w`. Thus **whole element byte intervals**, not merely their
start addresses, are pairwise disjoint. Transpose transports that argument by
the explicit index swap. Broadcast is read-only. For unsupported strides the
reference detects only constant-size counterexamples: an active axis with
stride less than width, or `(1,0)`/`(0,1)` whose starts differ by less than width.
Absence of these witnesses does not certify write injectivity.

In particular, `(2,2)`, width 8, strides `(8,8)`, capacity 24 passes bounds and
alignment but fails write injectivity. The dense `(8,16)` counterpart requires
capacity 32 and succeeds. Width 16 with stride 8 also fails, despite distinct
starts. These are byte-safety distinctions, not numerical semantics.

### Native representability is a separate obligation

The default `NativeLimits` contract uses unsigned 64-bit addresses, nonnegative
signed-64 byte offsets/capacities, and nonnegative signed-32 dimensions/leading
dimensions (LP64). Tests also instantiate smaller limits. The checker validates
`index_bits <= offset_bits <= pointer_bits`; indices are widened to the offset
type before multiplication. It validates
every dimension, stored stride, width, alignment, capacity, offset and final
exclusive end, plus `base + capacity` fitting the address type. This deliberately
conservative contract excludes a one-past address equal to `2^pointer_bits`.

For the exact access expression `((offset + i*s0) + j*s1)` and the final byte
end, all intermediate products/sums are nonnegative and bounded by `end(L)`.
Loop increments reach at most the checked extent. Thus the arithmetic fits
without first narrowing or wrapping. The reference computes integers first
and checks conversion second. It does not silently replace overflow by wrap,
saturation or modulo arithmetic. Mathematical bounds can pass while narrowing
fails, including an oversized `ld`, an offset exceeding signed range, or an
absolute address overflow.

This argument covers only those expressions. A flattened `rows*columns` loop,
rounded vector load, pointer pre-increment beyond the last cell, alternative
pointer arithmetic or backend ABI operation needs its own intermediate bounds.
No BLAS or complex-number ABI is certified by this reference.

## Loan compatibility without general partition solving

Preflight checks all active loans together with all requested accesses; the
reference IR gives them simultaneous lifetimes. It also checks old/old pairs,
so an inconsistent input environment cannot mint a successful receipt.

| Condition after layout checks | Decision |
| --- | --- |
| Read/read, including shared broadcast | SAFE |
| Either accessed region empty | SAFE |
| Different allocations in the validated live snapshot | SAFE |
| Same allocation, disjoint enclosing half-open intervals | SAFE |
| Same allocation, an actual common byte is reconstructed | INVALID |
| Same allocation, overlapping envelopes without a supported witness/partition | NEEDS_EVIDENCE |

The actual-overlap witness tests either first accessible byte against the other
dense source using one quotient/remainder by `ld*w`. Transpose has the same
byte set; nonempty broadcasts repeat their source cells. This can prove an
overlap, but is not a complete overlap solver. All other overlapping-envelope
cases require evidence; they never become SAFE by failing to find a witness.
Some NEEDS_EVIDENCE cases really overlap in later columns; the tests include
one. The classification means undecided by this bounded checker, not disjoint.

For width 8, views `(rows=1,columns=3,ld=2)` with offsets 0 and 8 have disjoint
actual bytes and overlapping envelopes. Read/read succeeds. If either writes,
the result is NEEDS_EVIDENCE, not a claim of actual collision. Offsets 0 and 16
have a reconstructible common byte and incompatible loans are INVALID.
No hidden copy repairs either rejection. A later explicit partition checker
may prove more cases; it must bind both exact layouts and the same generation.

For `A` allocations and `L` live/requested accesses, this reference uses
`O(A^2 + A*L + L^2)` metadata operations, with arbitrary-precision arithmetic
cost depending on integer bit length. No preflight loop or storage allocation
depends on `rows*columns`. Full enumeration occurs **only in the small tests**.

## Successful-branch evidence and exact returned IR

The reference flow is `Prepared(ir)` → `PreflightSession.preflight` → either
`(report,None)` or `(report,Success)`. A prepared plan and a successful diagnostic
report are not receipts. Only completed SAFE preflight issues a receipt in that
session; neither INVALID nor NEEDS_EVIDENCE issues one.

`Success.ir` is the **same immutable LayoutIR actually returned** by this path,
with every access, mode, layout kind/source, allocation generation, operation
identity and revision. The receipt also binds the exact allocation/active-loan
snapshot, epoch and native target. `audit_for_bounds_elision` checks issuance,
full equality against the supplied actual returned IR/current environment,
and independently recomputes preflight. It rejects changed layouts even if
their byte sets happen to agree, including a square transpose. It rejects
new generations at the same address, changed capacities, modes, targets,
operations, loans or epochs. `end_scope` expires the receipt; a different
session or copied/forged receipt cannot consume it.

This demonstrates dependencies in an executable API. Python object identity
is not a production proof, cryptographic capability or defense against arbitrary
Python memory mutation. `LayoutIR` is a **reference IR**, not the compiler's
`Indexed.Core`. Production must reconstruct these facts from actual checked
resource IR, audit the actual returned compiler IR and preserve the successful
branch's control dependency. It must not deserialize a `passed=true` flag or
accept this receipt as a Lean certificate.

No preflight function has a buffer/write callback. Failure preserves output
by construction in this model. The production before-first-write property,
including scratch allocation and external calls, still requires its own proof
and native regression. Snapshot equality does not establish physical liveness;
the resource transition checker must establish stability through the last use.

## Lean soundness targets

These are specification signatures for the future **actual** resource checker.
The names below are proposed, not current Lean declarations. They must be
implemented in `lean-kernel/` and proved by importing those exact definitions
into `lean/`; copying the Python model into an unrelated proof is insufficient.
No unproved axiom, assumed `AllAccessesSafe`, or enumeration-based acceptance
may substitute for the closed-form proof.

1. `checkLayout` returns finite reconstruction and integer inequalities. Prove
   the universal address/alignment and injectivity lemmas from those facts.
2. `checkNative` proves the specified native address expression equals its
   integer denotation and every intermediate/conversion fits.
3. `checkLoanPair = safe` proves actual region compatibility. Prove soundness,
   not completeness; NEEDS_EVIDENCE need not imply actual overlap.
4. Compose those lemmas with the actual preflight return equation, scope,
   initialization and resource-environment preservation obligations.

For clarity, use `Int` for descriptor arithmetic; `InDomain L i j` abbreviates
the four integer inequalities defining `D(L)` above. `ByteSafe A L i j` means
`0 <= start` and `start+w <= A.capacity` and alignment of `A.base+start`.
`ByteInjective L` means distinct domain indices have disjoint byte intervals.
`NativeExact T A L i j` includes equality of the computed address to the integer
denotation **and** representability of each intermediate in its declared type.
`Compatible A B` permits read/read or actual disjoint regions; different
allocations require validated live provenance, not pointer inequality alone.

```lean
-- Proposed signatures, not compiled code or claims of completed proofs.
theorem checkLayout_all_accesses
    (h : checkLayout env allocKey layout mode = .ok cert) :
    cert.allocKey = allocKey ∧ cert.layout = layout ∧ cert.mode = mode ∧
    LiveGeneration env allocKey ∧
    (∀ i j, InDomain layout i j → ByteSafe (env.lookup allocKey) layout i j) ∧
    (mode.writes → ByteInjective layout)

theorem checkNative_all_accesses
    (hL : checkLayout env key layout mode = .ok lc)
    (hN : checkNative target env lc = .ok nc) :
    ∀ i j, InDomain layout i j →
      NativeExact target (env.lookup key) layout i j

theorem checkLoanPair_sound
    (h : checkLoanPair env left right = .safe proof) :
    Compatible env left right

theorem preflight_returned_ir_safe
    (h : runPreflight env target request = .ok result) :
    result.ir = reconstructActualResourceIR env target request ∧
    EvidenceBoundTo result.evidence env.epoch target result.ir ∧
    (∀ access ∈ result.ir.accesses,
      LiveGeneration env access.allocKey ∧
      (∀ i j, InDomain access.layout i j →
        ByteSafe (env.lookup access.allocKey) access.layout i j ∧
        NativeExact target (env.lookup access.allocKey) access.layout i j) ∧
      (access.mode.writes → ByteInjective access.layout)) ∧
    AllSimultaneousLoansCompatible env result.ir
```

The proof of dense injectivity should order the physical column/row indices:
within a column, distinct starts differ by at least `w`; across columns,
`(j2-j1)*ld + i2-i1 >= ld-(rows-1) >= 1`. Multiply by positive `w` to separate
whole byte intervals. Transpose reduces by the bijection `(i,j) ↦ (j,i)`.
For range/alignment, use nonnegative-stride monotonicity and divisibility.
For empty domains, eliminate the impossible index hypotheses before any
subtraction or pointer construction. Broadcast repeats already safe source
addresses and supplies no write certificate.

### Conditions for eliminating inner bounds checks

Only a use dominated by the successful preflight event may consume its facts.
The proposed subsequent theorem must quantify the **actual emitted access**:

```lean
theorem dominated_access_safe
    (accepted : runPreflight env target request = .ok result)
    (actual : finalResourceAudit result.ir = .ok auditedIR)
    (same : auditedIR = result.ir)
    (dominates : SuccessfulBranchDominates result.event useSite)
    (stable : ResourcesStableThrough env result.event useSite)
    (emitted : EmittedAccessOf target auditedIR useSite access i j)
    (index : InDomain access.layout i j) :
    ByteSafeAtUse env access i j ∧ NativeExactAtUse target env access i j
```

`EmittedAccessOf` must establish membership in that IR and the exact address
expression/element width; it is not a caller-supplied name match. Range evidence
must come from validated loop bounds or refined indices. `ResourcesStableThrough`
must establish the same live generation, layout, capacity, loans, representation
and target, with no drop/reuse/move or incompatible transition until the last
use. A dynamic preflight event is unavailable before its success branch, on a
failure branch or at a join reachable without success. Static evidence must
provide the same facts without a runtime event. The empty branch emits no
access, even if a backend accepts a null pointer.

Once these facts hold, the particular inner bounds/alignment/overflow tests
they imply can be omitted. Initialization, permissions, nominal/numerical
contracts and lifetime safety remain separate resource/Core obligations;
omitting borrow checks also requires the verified whole loan schedule. The
reference's bounds-elision audit returns only a layout eligibility decision.
It does not implement the above compiler theorem or remove any check.
Optimization changing an address, layout, packing, fusion, loop range or alias
scope must re-audit the actual resulting IR and rebind its evidence. Pairwise
loan compatibility alone never authorizes function-wide `restrict`/`noalias`.

## Evidence ledger

Implemented here: mathematical-integer reference checks, tri-state diagnostics,
explicit transpose/broadcast reconstruction, native-field checks, conservative
loan checks, successful-session receipts and independent reference-IR re-audit.
Regression coverage includes 18,900 small dense/transpose cases against literal
enumeration, 5,184 loan pairs against actual byte sets, small native-boundary
cases, malformed/forged/stale evidence, empty layouts, and a `10^9 × 10^9`
matrix that must finish preflight without enumerating its `10^18` elements.
The subprocess deadline tests the absence of element enumeration; it is not
a native performance benchmark.

Pending: Lean implementation and universal soundness proofs above; actual
Ownership/Borrow/Core composition and protocol-8 integration; initialized reads
and resource transitions; compiler/code-generation correspondence; native
failure-before-write tests and generated-code check-elision regressions; and
equivalent C/C++ runtime/memory measurements. The #183 and #222 completion
conditions stay open. These reference tests establish none of those claims.
