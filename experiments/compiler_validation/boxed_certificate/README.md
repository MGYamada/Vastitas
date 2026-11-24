# Live boxed-program certificates

The driver checks a closed proof about one public boxed integer program with static calls and forward control flow. The proof subject contains the complete protocol-10 input and function revision, target header, typed instruction graph, mathematical integer result and all emitted LLVM bytes. The frontend replays the saved revision before returning its preview. A second execution of the Lean emitter recovers the graph from the linked artifact and compares its revision and bytes with that preview. [Capture](Capture.lean)

For a conditional, the certificate checks the typed graph, the chosen edge, the full
integer at the join and the complete printed module. Its subject imports the printer,
execution model and physical input decoder. The publication theorem also connects
the subject to the public emitter, Core and both MidIR phases. The assembly suite
checks the selected comparison and rejects its saved certificate after removing the
contribution. [Certificate subject](../../../lean/VastitasOracle/FlowCertificate/Subject.lean) · [Publication theorem](../../../lean/VastitasOracle/FlowCertificate.lean)

From the repository root, build the matching frontend, checker and oracle, then run the qualification.

```sh
lake -d lean-kernel build vastitas-kernel
lake -d lean build VastitasOracle
cargo build --locked --bin vastitas
python3 experiments/compiler_validation/boxed_certificate/regression.py
```

To check another source, give the driver its path and the exact target arguments. Flat inputs accept repeated `--lib` arguments in load order. Packages use `--manifest-path Vastitas.toml`. The JSON report identifies the verifier, physical input count, target, ABI, integer result, complete byte length, revision digest and measured worker phases.

```sh
python3 experiments/compiler_validation/boxed_certificate/verify.py \
  --source llvm/fixtures/BoxedProgram.vast --mode fast \
  --target-triple x86_64-unknown-linux-gnu \
  --data-layout e-m:e-i64:64-n8:16:32:64-S128 \
  --save-candidate /tmp/boxed-program.ndjson
```

Using the same inputs, replace `--save-candidate` with `--candidate` to check an existing export in either mode. Both verifiers regenerate the statement and declaration prefix from the current input and check the exact standard axioms and transitive references. A supplied proof may use any supported proof term in this environment. The verifier reads the input once and passes a private snapshot to its worker.

Official passes that snapshot to Lean 4.35.0’s `leanchecker --from-export`. It starts from an empty kernel environment and checks the reconstructed quotient primitives. Fast passes the same export to nanoda 0.4.19 and requires its exact declaration count. The qualification depends on the frontend, execution of the public Lean checker, the exporter and construction of the concrete subject from their outputs.

The four functions in `boxed-program.ll` return −226854911280625642308916404954512140972 before the host projects this integer to status 84. Both workers accepted the same 5,613-declaration export for all 1,830 bytes. The regression also accepts an alternative proof of the same proposition and rejects a foreign theorem, an ill-typed proof, a one-byte change to an add operand and a substituted source text. [Retained LLVM module](../../../llvm/src/boxed-program.ll)

The single-function program computes the integer quotient of 3²⁵⁶ by 7. Its intermediate squares exceed the constant folder’s work budget, so the compiled entry contains eight calls to the multiplication shim. Both workers check the same certificate for the full 403-bit result and all 1,977 bytes. [Vastitas source](../../../llvm/fixtures/SingletonPower.vast) · [LLVM module](../../../llvm/src/singleton-power.ll)

For each compilation the driver reopens the physical files, compares their bytes with the captured input and recomputes their offsets. The proof identifies this ordered snapshot with the layout decoded from the wire. For packages the driver independently follows the TOML dependencies from the root manifest and checks the package names, versions, editions and root module locations. External Vastitas module discovery and declaration parsing still use the frontend. A two-file flat program and a four-file package each return 42 and produce 1,127 LLVM bytes for the macOS arm64 target. Editing a comment in the library or dependency manifest preserves all 1,127 bytes and invalidates the earlier proof. [Physical input decoder](../../../lean-kernel/VastitasKernel/PhysicalSources.lean)

The boxed publication theorem places each resolved implementation, classification and indexed family
in Core and in both MidIR environments for the same revision and complete bytes.
The Lean certificate generator shares repeated source text and paths as closed string definitions.
It constructs long strings by appending short literals. The physical layout equality still covers every UTF-8 byte.
In a local macOS arm64 replay of the four-file indexed-record package, this changed certificate
elaboration from 37.77 to 19.30 seconds. Lean 4.35.0 and nanoda both verified the same
2,311 LLVM bytes under the 120-second per-worker limit.

The input suite compiles the ordered calls against three separate dependency fixtures.
Each compilation reads four physical files. Official and Fast replay the same certificate
for that compilation. The first fixture changes an implementation marker, a classification
domain, the slots of a family constraint, a package index and a descriptor primitive.
The second changes a Gram entry, the subject of metric evidence and a moving frame with
its inverse. The third changes a scale magnitude, the order of a basis and an algebraically
equal manifold witness. Each of the eleven edits preserves the 2,311 LLVM bytes and result
23 and invalidates the certificate from before the edit. [Ordered calls](../../../llvm/fixtures/OrderedCalls.vast) · [Retained LLVM](../../../llvm/src/ordered-calls.ll)

The assembly suite replays the same certificate in both modes for a three-package program. Six physical files fix the owner of the family, the contribution selected by the borrow block, and the protected `Int + Int` operation. The 2,051 certified LLVM bytes contain the selected method and all four specializations of its unselected sibling. [Assembled program](../../../llvm/fixtures/borrowed-operator/main.vast) · [Checked LLVM](../../../llvm/src/borrowed-operator.ll)

The selected-projection fixture retains both pair field functions and both scalar methods.
The assembled contribution returns the second element, 19, while the default returns the first, 7.
Official and Fast verify the 1,968-byte selected module. Changing the assembly invalidates its certificate.
[Pair field selection](../../../llvm/fixtures/SelectedProjection.vast) · [Checked LLVM](../../../llvm/src/selected-projection.ll)

The assembly suite also selects a method that negates its boxed integer argument.
Its retained caller and the identity sibling agree on their signature and produce opposite
signs for 2¹²⁸ + 43. Switching the selected method invalidates the saved certificate.
[Unary method](../../../llvm/fixtures/AssembledNegation.vast) · [Checked LLVM](../../../llvm/src/assembled-negation.ll)

The pair fixture uses an edition 2026 manifest and one source file. Both certificate workers check the same five-function module. The unbounded integer calculated by the selected method's caller is 42. Its bytes retain the default method and the selected contribution. [Pair-valued assembly](../../../llvm/fixtures/BoxedPairs.vast) · [Checked LLVM](../../../llvm/src/boxed-pairs.ll)

The assembly suite also checks a `Nat → Int` method selected by `apply exact`.
The module contains the selected conversion, the entry, and its zero-returning
sibling. Both certificate workers check the full integer 2¹²⁸ + 43 and all
1,376 bytes. Binding the argument to a local before conversion preserves every
LLVM byte. Removing that local and replaying its certificate fails because the
function revision identifies the body that introduced the local. Native integer probes distinguish this result from 2¹²⁸ + 299,
which has the same exit status. [Conversion source](../../../llvm/fixtures/AssembledConversion.vast) · [LLVM module](../../../llvm/src/assembled-conversion.ll)

The same suite checks a second package that seals the family and returns 7 without calling it. Official and Fast verify the 1,829-byte module, including all five method specializations and the entry. [Uncalled operator package](../../../llvm/fixtures/uncalled-operator/main.vast) · [Checked LLVM](../../../llvm/src/uncalled-operator.ll)

The composition theorem takes the dependent publication witness from the public emitter and the checked stage certificate. It connects the returned Core, optimization and execution MidIR, complete LLVM module, parser and hosted status to the same integer. General per-build source admission proofs, additional LLVM profiles and native linking remain separate release obligations. [Composition theorem](../../../lean/VastitasOracle/BoxedCertificate.lean) · [LLVM corpus](../../../llvm/docs/README.md)
