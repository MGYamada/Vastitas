# Remaining monoidal Graph proof obligations

The internal [crossing checker](graph-crossings.md) now has audited returns,
typed metadata checks and conditional local/trace semantic preservation.
The following obligations remain open under [#201](https://github.com/MGYamada/Vastitas/issues/201).
They are specifications, not completed Lean proofs or release conditions.

## Certified hierarchy and intended denotation

Define `CertifiedMonoidal P`, `CertifiedBraided P` and `CertifiedSymmetric P`
over the exact same category/tensor/unit/associator/unitors/chosen braiding.
Higher evidence must supply lower evidence for that same profile.

- Monoidal: bifunctoriality/interchange; associator and unitor naturality,
  inverses, pentagon and triangle.
- Braided: the specified invertible braiding, naturality and both hexagons.
- Symmetric: `β_(B,A) ∘ β_(A,B) = id_(A⊗B)` for that specified braiding.

Implement the production `Graph.Authority` law predicate using these verified
laws. Derive an `Interpretation P capability arity M` for the intended typed
categorical model. The current conditional interpretation theorem cannot
substitute for this construction or for selecting the intended model.

For each fixed bracketed boundary Γ and valid adjacent position i, explicitly
construct the structural lift `b_i⁺(Γ)` using tensor, identities and the chosen
associator. Define `b_i⁻(Γ) = inverse(b_i⁺(swap_i Γ))`. In particular, the
negative crossing at `A,B` is `β_(B,A)^(-1)` and not `β_(A,B)^(-1)` with
incorrectly relabeled input ports.

Derive the exact generating laws already consumed by the oracle:

```text
Braided:
  b_i^(-ε)(swap_i Γ) ∘ b_i^ε(Γ) = id
  denote [i^ε; (i+1)^ε; i^ε] = denote [(i+1)^ε; i^ε; (i+1)^ε]
  denote [i^ε; j^δ] = denote [j^δ; i^ε]           (|i-j| ≥ 2)

Symmetric:
  b_i^ε(swap_i Γ) ∘ b_i^ε(Γ) = id
```

All positions must be valid in the same fixed arity, and intermediate typed
boundaries and nominal identities must be explicit. The existing oracle
proves preservation from these laws through exact rule instances, contexts
and finite traces; it does not yet derive the laws from a category record.

## Source, method implementation and actual compiler Core

The current internal `Context` must be obtained from the actual checked
environment. Prove that it binds the canonical generic declaration for both
`⊗` and `tensor`, the actually selected method/specialization and implementation
revision, exact profile/certificate, and actual in-scope object references.
An arbitrary frontend-authored context or `Lawful := True` is not admissible.

Separate abstract laws from method realization. The required bridge has this
shape, where the identifiers below are proposed specifications:

```text
actualResolve E occurrence = ok resolved
resolved.genericId = E.canonicalStdTensorId
verifiedImplementationEvidence E resolved P
compileSelected E resolved (f,g) = ok actualCore
----------------------------------------------------------------
denoteCore E P actualCore = P.tensorMap (denote f) (denote g)
```

Add analogous bridges for braiding, inverse, associator and unitors. Then
connect `Graph.Core` structural nodes and their exact checked output to the
actual `Indexed.Core` terms returned by the compiler. Profile IDs and compiled
method evidence must survive elaboration, specialization and optimization.
Implementation changes invalidate/revalidate dependent evidence.

The end-to-end theorem must bind all of these to one acceptance result:

```text
acceptGraph E source actualInputCore request = ok result
----------------------------------------------------------------
exists resolved P evidence,
  actualResolve E source.tensorOccurrence = ok resolved
  ∧ resolved.genericId = E.canonicalStdTensorId
  ∧ actualVerifiedProfile E resolved = ok (P,evidence)
  ∧ result.inputCore = actualInputCore
  ∧ SourceCorresponds E P source actualInputCore
  ∧ CheckedStructuralTrace E P actualInputCore result.returnedCore
  ∧ WellTyped E P result.returnedCore
  ∧ SameExactBoundary E P actualInputCore result.returnedCore
  ∧ denoteCore E P result.returnedCore = denoteSourceMath E P source
```

This is not obtained merely by renaming the internal graph certificate to
`Indexed.Core`. Source correspondence and method realization must be proved
on the actual compilation path. Numerical/native refinement, independent
Domain Coherence, Base/Coefficient/Grading and Ownership/Borrow obligations
remain separate.

## Reassociation and exact reference semantics

Reassociation is currently rejected. A future rule must retain explicit
associator/inverse arrows between distinct nominal endpoints, prove their
implementation correspondence, and use pentagon/triangle/naturality for
coherent lifting. Coordinate equality, equal dimension and scalar-one
associators must not create nominal object equality.

The Python reference calculations are finite tests. Separate universal Lean
proofs could show that nonzero rational `q` gives the bicharacter `q^(a*b)`,
prove both multiplicativities for all integer degrees, and connect its exact
evaluator to typed word semantics. `q^2=1` supplies symmetric scalar equations
in that model. These would not establish faithful representation, arbitrary
braid equality, or compiler correctness. The pure-braid counterexample in the
reference tests rules out using observation equality as a general decision
procedure.
