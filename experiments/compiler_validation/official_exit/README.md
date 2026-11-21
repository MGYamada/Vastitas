# Official kernel feasibility for an executable artifact

This experiment checks a closed instance of the decoded source and the
complete LLVM image for [ExitStatus.vast](../../../llvm/fixtures/ExitStatus.vast).
The source returns −(2¹²⁸ + 1). The retained macOS arm64 module returns 255.
[Inputs.lean](Inputs.lean) contains the complete protocol-10 JSON value from
the public flat frontend, the 126 original UTF-8 source bytes, the nominal
owner, target header, mathematical integer and every byte of
[exit-status.ll](../../../llvm/src/exit-status.ll).
The flat identity uses the protected package `vastitas:compat:flat` and file
`ExitStatus.vast`. No host directory is substituted into that identity.

[Decoded.lean](Decoded.lean) proves that the mandatory root source field
decodes at offset zero and contains all 126 physical bytes. It also proves
that the wire decoder and integer literal parser recover the source owner
and signed value. [Printed.lean](Printed.lean)
proves that the saved bytes parse as the model selected by that value and
target. [Facts.lean](Facts.lean) combines both equations with the modeled
exit observation. The canonical parser theorem rules out every different
byte sequence for this exact model.

[Current.lean](Current.lean) defines the stronger compile acceptance obligation.
Its witness contains the exact result of `Emission.check wire target true`,
the checked source/Core/MidIR artifact returned from that invocation and the
complete UTF-8 byte equality for its actual returned text. Its `of_validate`
theorem also recovers the function revision, Core evaluation, observations
of both linked phases, and Euclidean exit status. The original endpoint experiment attempts direct reduction of both the wire
checker and the emission validator. The decomposed artifact experiment below
constructs an `Observes` witness from the exact successful public result.

To reproduce from the repository root, use the pinned Lean toolchain and run

```sh
lake -d lean-kernel build vastitas-kernel
cargo build --locked --bin vastitas
lake -d lean build VastitasOracle.ExitFunction VastitasKernel.LLVM.Emission
python3 experiments/compiler_validation/official_exit/run.py --timeout 75
```

The runner first compares the freshly checked frontend input and saved bytes
with the entire retained Lean data file. Successful elaborations use
warning-as-error and may depend on `propext`, `Classical.choice` and `Quot.sound`.
Each successful proof module is replayed as a named `leanchecker` target. The
runner reports elapsed time and maximum resident memory separately per child,
and returns nonzero when any measured proof or replay is incomplete. Hashes
identify the measured data; Lean equalities check the source and artifact.

To refresh the retained input after a reviewed wire change, add
`--save-inputs experiments/compiler_validation/official_exit/Inputs.lean`.
The runner checks the entry file against the source text in the public
revision before serializing both as Lean data, preserving every line ending.

In the [macOS arm64 run](results/macos-arm64.json), all five named
module replays succeeded. Replaying the decoder and root source proofs took
8.58 seconds and 1,268,219,904 bytes peak RSS, the LLVM byte proof took
4.37 seconds and 915,030,016 bytes, and the combined endpoint statement took
3.58 seconds and 841,793,536
bytes. Both stronger closed obligations reached their independent 75-second
time limits during elaboration. Their peak RSS was 936,968,192 and
966,754,304 bytes respectively. The report records this run as incomplete.

## Decomposed source admission

The staged experiment follows the actual signed-literal request through the
source and namespace checkers. Run the physical source replay with the same
limits as the complete artifact job.

```sh
python3 experiments/compiler_validation/official_exit/run.py --staged --timeout 120 --memory 2500
```

[Source.lean](Source.lean) identifies the entire decoded `ResourceSource.Program`,
including every expression span, and proves acceptance of its public envelope.
Its layout equality connects the captured request to the physical checks.
[PhysicalScan.lean](PhysicalScan.lean) locates the singleton in the file.
[PhysicalDeclaration.lean](PhysicalDeclaration.lean) parses its signature, body and
signed integer at that location. [PhysicalReplay.lean](PhysicalReplay.lean)
combines this result with the flat manifest check and the empty cell and product
inventories. Each module elaborates and undergoes independent `leanchecker`
replay in a separate process under the same limits. The lexer uses a proved
byte-to-character lookup for this ASCII fixture.
[NamespaceGates.lean](NamespaceGates.lean) establishes unique owners and emitted
symbol names for all 25 declarations, the root package lookup and the
full wire charge of 34 units. One declaration is `main`. The other 24 come
from the protected compatibility profile. [NamespaceValidation.lean](NamespaceValidation.lean)
uses those identities to prove `Namespace.validate idx = .ok ()`. Given the
exact result of `Indexed.Source.lower` and the reference, identity, data and
geometry predicates, it also recovers that same result from `checkDeclarations`.

[Lexical.lean](Lexical.lean) proves the real assembly lexer reads the 126
physical bytes at offset zero and produces no assembly events. The reduction
uses a kernel-checked equivalence between UTF-8 indexing and character
indexing for this ASCII file. [Admission.lean](Admission.lean) composes the
actual inner authority pass with the resource, work budget, assembly and
revision checks. `wire_of_pass` proves the concrete public wire is accepted
*if* the inner authority checker returns an artifact within the remaining
budget and with the original empty event list.

The runner elaborates each fixture module and replays its new declarations
with `leanchecker -v` over the pinned imports. A missing prerequisite skips its
descendants. The Lean memory setting bounds elaboration. The wall clock bounds
both elaboration and replay, and the report gives per-process peak RSS.

The [staged macOS arm64 run](results/macos-arm64-staged.json) replayed all
seven modules, including `Current` and `Inputs`. The five source-admission
replays had the following wall times and maximum resident sizes.

| Replayed module | Seconds | Peak RSS in bytes |
| --- | ---: | ---: |
| `Source` | 5.62 | 1,140,506,624 |
| `NamespaceGates` | 13.99 | 1,593,884,672 |
| `NamespaceValidation` | 4.92 | 1,018,609,664 |
| `Admission` | 5.54 | 964,902,912 |
| `Lexical` | 8.54 | 1,536,049,152 |

In this staged run the first unresolved declaration step was `Indexed.Source.lower headers` for
the actual compatibility-backed environment. Reducing the success of this
operation reached the 55-second limit after 55.04 seconds with peak RSS of
1,050,198,016 bytes. The complete public `Wire.check` goal remained open after
2.33 seconds of reduction. The report retains both outcomes as incomplete.

## Concrete declaration acceptance

The declaration run replaces the direct `Indexed.Source.lower` reduction with
a candidate table and independent proofs of every step. Reproduce it with

```sh
python3 experiments/compiler_validation/official_exit/run.py --declarations --timeout 55 --memory 2048
```

The protected compatibility source contains 24 declarations. Each body proof
preserves the previous environment and appends the actual references in
resolution order. The [fold proof](DeclarationFold.lean) composes the Scheme,
smooth and shared groups into 11 indexed entries, one package and 12 primitive
bindings. The thirteen subsequent source checks and elaboration stages preserve
that table. The geometry export contributes 21 references after the 47 body
references. `actualLowered` identifies the exact output of the public source
pass, including all 68 resolved references. [Declaration lowering](DeclarationLowering.lean)

The class hierarchy gives `Objects` rank 1 and its two children `Scheme` and
`CInfScheme` rank 2. The proof relates the real hash-map lookup to the entry
validator independently of dictionary iteration order. The resulting
`acceptedDeclarations` equation identifies the full output of
`Indexed.Source.checkDeclarations` on this input. [Declaration acceptance](DeclarationAcceptance.lean)

The runner snapshots the local imported libraries before elaboration so each
replay reads the same files. The [macOS arm64 declaration run](results/macos-arm64-declarations.json)
elaborated and replayed all 16 modules. Replaying the complete lowering took
9.83 seconds and 968,884,224 bytes peak RSS. The declaration acceptance proof
took 6.18 seconds and 924,024,832 bytes to replay. The whole wire goal remained
open after 3.18 seconds of reduction. The later runs below discharge the authority, function-body and artifact
checks on those exact declarations.

The Rust parse, UTF-8/JSON capture and pinned imported declaration environment
are assumptions. Independent full dependency authentication, nanoda/Fast
checking, linking and process execution have separate evidence. The decoder and printer endpoints on their own leave the concrete public
compiler invocation open.

## Authority, dispatch and function compilation

With `--authority --timeout 55 --memory 2048` the runner also replays the
actual namespace lowering, edit preparation and authority assembly. The
[authority run](results/macos-arm64-authority.json) replayed all 18 named
modules. Replaying `actualAssembly` took 14.23 seconds and 875,479,040 bytes
peak RSS. Replaying `acceptedPurePreparation` took 5.67 seconds and
880,132,096 bytes. Substituting the resulting prepared authority into the
public check exposed the remaining function lifting step.

[CompilerInputs.lean](CompilerInputs.lean) identifies the sole protected
`main` and the compiler environment returned by the real preparation.
[FunctionLowering.lean](FunctionLowering.lean) proves the exact result of
both lowering passes. The result retains the initial geometry resolution
trace, symbol 0, its specialization key, and four elaboration work units.
[ModuleTyping.lean](ModuleTyping.lean) derives the independent typing judgment
for the signed literal. [PassAcceptance.lean](PassAcceptance.lean) combines the
two pass validations and Core audits. [PureProgram.lean](PureProgram.lean)
proves that reverse compilation accepts the unchanged module and identifies the
full value returned by `Indexed.AuthoritySource.checkProgram`.
[PublicWire.lean](PublicWire.lean) discharges the remaining source, resource,
budget, revision and assembly obligations for this input. Replay it with

```sh
python3 experiments/compiler_validation/official_exit/run.py --wire --timeout 75 --memory 2048
```

The [public wire run](results/macos-arm64-wire.json) passed all 26 named
kernel replays. Replaying `PureProgram` took 9.82 seconds and 933,068,800 bytes
peak RSS. Replaying `PublicWire` took 43.59 seconds and 606,781,440 bytes.
The closed theorem asserts that the real protocol-10 request succeeds with
the executable entry check enabled.


## Closed public executable artifact

The artifact experiment runs on the same frozen imports as the wire proof.
[ResourceRecord.lean](ResourceRecord.lean) reconstructs every computational
field of the checked input. [RevisionBound.lean](RevisionBound.lean) applies the
actual size check to the complete nominal revision.
[LinkedMid.lean](LinkedMid.lean) proves the exact equations for `MidIR.lowerChecked`
and `MidIR.Module.execute`. Both modules contain the same source owner, symbol
0 and specialization key. A single integer instruction carries −(2¹²⁸ + 1).

[SignedArtifact.lean](SignedArtifact.lean) identifies the artifact returned by
`ExitFunction.compile`. [PublicArtifact.lean](PublicArtifact.lean) recovers
the exact result of `Emission.check wire target true`. The kernel theorem
`Emission.check_literal` selects the literal branch from the checked request,
the compiler result and the parser equation. The fixture checks the parser on all
374 retained bytes. The final `Observes`
theorem uses the accepted request, the Core entry evaluation at every
sufficient fuel, the two MidIR observations and all 374 bytes of the retained
LLVM module. The modeled `main` returns status 255. Reproduce the run with

```sh
python3 experiments/compiler_validation/official_exit/run.py --artifact --timeout 120 --memory 2500
```

The certificate covers one signed-literal program on the retained arm64 target.
The named modules are replayed over the pinned imported Lean libraries.
The independent authentication of those libraries and standard axioms,
a general Fast/Official CLI mode, and native execution require separate evidence.

The [complete artifact run](results/macos-arm64-artifact.json) elaborated and
independently replayed all 32 fixture modules under Lean 4.35.0. The final
module elaborated in 26.54 seconds with 1,726,005,248 bytes peak RSS. Its
official replay took 15.20 seconds with 1,919,614,976 bytes peak RSS.
The report records each proof source digest and the inventory digest of the
frozen local imports.

The [live public comparison](results/macos-arm64-live.json) records the current
default compiler binaries. The [frozen toolpair comparison](results/macos-arm64-pinned-live.json)
records the binaries that supplied the proof fixture. The full printed nominal
revision, protocol-10 request, original root bytes and all 374 emitted bytes
are identical across these builds. To compare the current tools to the
retained theorem inputs, run

```sh
python3 experiments/compiler_validation/official_exit/run.py --compare-live
```

## Offline nanoda qualification

Provisioning and checking use separate trust inputs. The authority builds the
reviewed concrete fixture and replays its named declarations with the Official
kernel. The independently supplied candidate is an untrusted Lean export. An
offline audit reads the current compiler's full source request, complete nominal
function revision, target and emitted bytes. A separately provisioned directory supplies the reference. The [reviewed image pins](qualified-exports.json) identify every byte of each canonical reference. Substituting a reference directory and an identical untrusted candidate fails if their image differs from the qualified one. The reviewed pins, repository and installed toolchain belong to the trust base.

```sh
python3 experiments/compiler_validation/official_exit/run.py --provision-fast target/exit-authority --timeout 120 --memory 2048
python3 experiments/compiler_validation/official_exit/run.py --provision-fast target/exit-candidate --timeout 120 --memory 2048
python3 experiments/compiler_validation/official_exit/fast_check.py --authority target/exit-authority --candidate target/exit-candidate/public-artifact.ndjson --profile public-artifact --timeout 900 --stack-kib 49152
python3 experiments/compiler_validation/official_exit/fast_negative.py --authority target/exit-authority
```

Supply a new directory for each provisioning run. The second invocation above independently regenerates a candidate for reproduction. A verifier may instead receive a candidate from an untrusted producer. The candidate must be generated with
the same fixed root order and exporter version as the selected profile.
To reuse the approved libraries after a rebuild, pass `--import-snapshot DIR`
to each provisioning run. `DIR/0` and `DIR/1` contain the frozen local
library trees in Lake search order. Qualifying a changed library closure
requires a fresh Official replay and review of the resulting export.
`--profile public-artifact` requests the complete public checker result;
`signed-endpoints` requests the decoded source and LLVM byte endpoints;
`printed-bytes` requests only the checked LLVM parser result. Each profile has
a distinct theorem and acceptance terminus.

The [standard axiom pin](standard-axioms.ndjson) is the complete 225-record
closure exported from Lean 4.35.0 `Init` for `propext`, `Classical.choice`,
and `Quot.sound`, in that order. The 16 declarations in the pin include these three statements
with their original implicit binders and universe parameters.

```lean
@propext : ∀ {a b : Prop}, (a ↔ b) → Eq.{1} a b
@Classical.choice.{u} : {α : Sort u} → Nonempty.{u} α → α
@Quot.sound.{u} : ∀ {α : Sort u} {r : α → α → Prop} {a b : α},
  r a b → Eq.{u} (Quot.mk.{u} r a) (Quot.mk.{u} r b)
```

The offline auditor regenerates these records
in a standard-library-only environment and compares every byte, including their
universe parameters, types, and referenced inductive and quotient declarations.
The candidate must start with the same 13,039 bytes. The tool compares the
complete remaining export with the authority copy while writing a private
immutable input for nanoda. This compares theorem types, proof terms, definitions,
inductive groups and recursor rules. The SHA-256 values in the reports identify
the files for reproduction. The auditor checks the reference image pin in addition to the complete stream comparison and the independent nanoda judgment.

The scanner checks the typed name, level and expression indices and all
constant, projection, recursor, constructor and mutual-group references. The
pinned exporter's first pass can name companion functions in a definition's
`all` field without emitting those companions. The authority exporter adds
exactly the missing names as roots and checks closure again. Grouping and
numeric components are preserved in each exported name. The pinned nanoda
0.4.19 process must report the exact number of declarations with no
diagnostics, under the reviewed three-axiom policy. The ordinary audit uses
the declared 48 MiB POSIX main-thread stack and a per-process time bound.
An inherited-stack audit is reproducible with `--stack-kib 0`.

[RevisionBinding.lean](RevisionBinding.lean) proves that the complete function
revision of the returned resource record has exactly the tokens in
[ExpectedRevision.lean](ExpectedRevision.lean). Object and array arities delimit
all values, keys retain their order, and numerical tokens retain mantissa and
exponent. The offline checker reconstructs this entire token list from the live
compiler. [FastSubject.lean](FastSubject.lean) requires this equation and the
public emission/observation theorem together. Python JSON capture, the pinned
exporter and installed toolchain, authority provisioning and the external
checker are explicit assumptions of this operational experiment.

The macOS arm64 run on the signed corpus fixture passed both independent
endpoint audits. The [parser result](results/macos-arm64-fast-printed.json)
checked 1,371 declarations over 2,633,111 export bytes. The
[source and byte endpoints](results/macos-arm64-fast-endpoints.json) checked
9,251 declarations over 79,572,654 bytes and took 12.13 seconds at
514,490,368 bytes peak RSS. These CPU checks share the target and complete
bytes of the [LLVM comparison](../../../llvm/docs/README.md).

For the earlier `observesArtifact` root the stock targeted export omitted 26
mutual-group companions. A second export pass recovered all 29,331 declarations.
After full structural authentication the [inherited-stack worker](results/macos-arm64-fast-observes-inherited.json)
aborted. The [48 MiB worker](results/macos-arm64-fast-large-stack.json)
reached its 720-second deadline with 3,189,702,656 bytes peak RSS. Both
attempts rejected the full obligation. The `verification_terminus` in these
reports identifies the requested statement. Success requires both `passed`
status and the complete nanoda declaration count.

The [falsification run](results/macos-arm64-fast-negative.json) checked the
genuine `printed-bytes` certificate with nanoda over 1,371 declarations.
Each of the 17 substitutions then produced its expected rejection phase and
diagnostic. The four live-subject tests used that same genuine certificate.
The changed-source case also compiled to the original 374 bytes before its
changed public revision was rejected. A separate valid fixture named `printed` passed standalone
nanoda over 20 declarations and failed admission against the current artifact.
Giving the verifier that same foreign proof as the reference and the candidate also failed. Other controls change a transitive definition, proof term or standard axiom,
truncate the stream, supply a dotted axiom alias or new assumption, omit a
referenced declaration, or change only the source, LLVM image, claimed integer
or public function revision.

The stronger [complete artifact qualification](results/macos-arm64-fast-artifact.json)
passed the external checker for all 29,374 declarations in 400.49 seconds, with
3,651,846,144 bytes peak RSS. This run used `--profile public-artifact
--timeout 420 --stack-kib 49152`, one checker process and one type-checking
thread. Its 290,726,880 bytes contain 5,470,500 records. The
[Official provisioning run](results/macos-arm64-fast-provision.json) replayed
35 fixture modules and four additional revision-binding modules. A second
export pass supplied 26 mutual declarations for the full certificate. An
independent export matched the complete provisioned image.

The [final public compiler comparison](results/macos-arm64-fast-live.json)
uses the rebuilt owner-seal driver and kernel. The original 126 source bytes,
whole protocol-10 request, full 1,547-byte canonical nominal revision and
374 emitted LLVM bytes agree with the signed proof subject. The report gives
both installed binary identities. The approved proof used the frozen library
inventory in the provisioning report. Comparing observable fields on the
newly installed compiler does not authenticate its entire declaration
environment. Per-build authentication of arbitrary inputs and targets, public
CLI verifier modes, and native refinement remain separate obligations.

The [second full audit](results/macos-arm64-fast-replay.json) compared an
independently regenerated candidate against the new Official provisioning
directory and the complete reviewed image pin. With a 900-second limit and
48 MiB main-thread stack, nanoda again checked all 29,374 declarations. This
run took 337.02 seconds and 3,618,701,312 bytes peak RSS. The
[stronger root with the inherited stack](results/macos-arm64-fast-bound-inherited.json)
rejected after 22.55 seconds. These runs retain each requested profile and
its actual checker outcome.
