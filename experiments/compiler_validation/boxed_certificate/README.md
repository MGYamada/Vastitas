# Live boxed-program certificates

The driver checks a closed proof about one public boxed integer program with static calls and forward control flow. The proof subject contains the complete protocol-10 input and function revision, target header, typed instruction graph, mathematical integer result and all emitted LLVM bytes. One invocation of `check --llvm-proof-input` returns the full function revision and LLVM report from the same emission. An independent execution of the Lean emitter recovers the graph and revision from the original request. The driver compares the complete revision and LLVM text before constructing the proof. [Capture](Capture.lean)

For a conditional, the certificate checks the typed graph, the chosen edge, the full
integer at the join and the complete printed module. Its subject imports the printer,
execution model and physical input decoder. The publication theorem also connects
the subject to the public emitter, Core and both MidIR phases. For a retained
dispatch callee, the family selects the method recorded for its key, and both
phases carry its specialization to the same printed function slot. The assembly suite
checks the selected comparison and rejects its saved certificate after removing the
contribution. [Certificate subject](../../../lean/VastitasOracle/FlowCertificate/Subject.lean) · [Publication theorem](../../../lean/VastitasOracle/FlowCertificate.lean)

For a control-flow graph, separate Lean workers prove the evaluated integer and
the printed bytes. For blocks containing several calls, the evaluation proof uses
Lean's kernel to decide the equality of the computed and expected integers.
Each verifier includes both proofs and their dependencies in the regenerated
declaration prefix. The assembly log
reports elapsed seconds and peak resident memory for each worker.

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

To seal an export of `E` bytes, the driver compares the entire supplied prefix
with its private authority file in 1 MiB chunks. It appends the remaining proof to
the private file, then publishes a second name for that inode. This pass takes
linear time in `E` and a constant number of chunk buffers. During sealing, private
export data occupies at most `E` bytes for a supplied candidate and `2E` for one
generated in the same invocation. These bounds cover export contents during this
pass. The Lean modules, logs and filesystem metadata have separate costs.

The driver and regression suite pass a 1,536 MiB memory limit to Lean during capture and elaboration.
Use `--memory MiB` to select another budget. A failed elaboration stops that case.
The CI runners use 6,144 MiB for the full suites. Each measured phase reports its peak RSS separately,
including the external checkers, whose memory use is outside Lean's allocator limit.

The file-count qualification varies the number of physical inputs to the same
four-function program. Each mode starts from the public compiler, reads the
source files, and compares all 1,830 LLVM bytes with the retained module. Fast
replays the complete export produced by Official. Each Lean worker elaborates
up to 128 file transitions. Its theorem composes the batch with any remaining
rows in order. The wire and scan share the captured JSON rows. The expected
files come from disk. Each flat library with a UTF-8 path uses the shared
three-field decoder theorem and supplies its own path, offset and size checks.
Identical contents share a proof of UTF-8 length.

This macOS arm64 run used the same 1,536 MiB Lean allocator limit and 360-second
per-worker timeout for all three sizes, including the decoder's 8,192-file limit.
Each pair of measurements gives Official first and Fast second. Wall time
includes frontend checking, proof preparation and export auditing. The replay
column measures only leanchecker or nanoda. Peak RSS is the largest measured
child process. Private file bytes count unique regular files immediately after
sealing, including the generated proof when present. The runner removes each
case before starting the next size.

| Files | Certificate bytes | Wall time (s) | Replay (s) | Largest worker RSS (MiB) | Private files at seal (MiB) |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 129 | 41,887,934 | 20.2 / 14.6 | 5.1 / 3.3 | 1,451 / 1,443 | 83.2 / 43.2 |
| 2,048 | 49,870,657 | 79.0 / 68.0 | 18.7 / 11.0 | 1,457 / 1,457 | 121.2 / 73.6 |
| 8,192 | 76,296,351 | 274.8 / 244.1 | 65.1 / 40.1 | 1,507 / 1,511 | 244.6 / 171.8 |

```sh
python3 experiments/compiler_validation/boxed_certificate/regression.py --file-counts 129 2048 8192 --timeout 360
```

The byte-size qualification holds the program and file count fixed. It adds a flat
library with a multibyte UTF-8 comment and a seeded sequence of hexadecimal digits.
Libraries longer than 1,024 Unicode scalars use leaves of up to 128 scalars.
Lean checks that each literal spells its list of characters and proves its byte
length from their UTF-8 widths. A balanced tree adds the checked lengths. A
worker emits up to 128 tree nodes per module. Equal leaves and equal
pairs share definitions. Constructing the tree takes a linear number of leaf
and join visits. These measurements cover two physical files on macOS arm64
with a 120-second timeout per worker and a 1,536 MiB Lean allocator budget.

| Library bytes | Exported declarations | Wall time (s), Official / Fast | Replay (s), Official / Fast | Largest worker RSS (MiB), Official / Fast |
| ---: | ---: | ---: | ---: | ---: |
| 4,096 | 6,132 | 16.3 / 12.9 | 4.1 / 2.7 | 1,438 / 1,430 |
| 16,384 | 6,324 | 21.1 / 21.9 | 4.4 / 3.0 | 1,447 / 1,443 |
| 65,536 | 7,092 | 38.0 / 32.8 | 5.8 / 3.8 | 1,448 / 1,444 |
| 262,144 | 10,164 | 107.1 / 101.4 | 11.1 / 8.2 | 1,470 / 1,467 |

Both modes check the same export and all 1,830 retained LLVM bytes at each size.
The single-entry and four-file sweeps below exercise the file and aggregate limits with repeated text.

```sh
python3 experiments/compiler_validation/boxed_certificate/regression.py --library-bytes 4096 16384 65536 262144
```

For a single flat input, the physical layout theorem checks the two root-source
fields, the protected package identity, the filename, its path bytes and the
entry's checked UTF-8 byte length. Appending a 64 KiB repeated comment to the
four-function entry previously exceeded the conversion recursion limit. On
macOS arm64 both workers checked the resulting single-file revision, all 6,066
declarations and the same 1,830 LLVM bytes. Official took 14.9 seconds end to
end with a 3.9-second replay. Fast took 10.6 seconds with a 2.5-second replay.
The boxed suite also changes the final chunk of a single-function entry and
checks that the earlier certificate fails for the revised source.

For a flat entry followed by libraries, the proof checks the canonical root
fields, file count and first table row against the same protected filename
and entry text. A 64 KiB comment in the entry of a two-file compilation
previously exhausted the conversion recursion budget in two places. The
header and first-row theorems reuse the entry's checked extent. Both modes
check all 1,830 LLVM bytes. The inputs suite changes the first wire path and
the last physical library path across two proof batches. Lean rejects each.
A joint run at the 8,192-file limit appends a comment containing 4,096 copies
of `0123456789abcdef` to the four-function entry. The 120-second per-worker
timeout and 1,536 MiB Lean allocator budget apply to both modes. Official and
Fast accept the same 76,730,387-byte export with 38,990 declarations and the
retained 1,830 LLVM bytes. End-to-end times are 276.4 and 248.2 seconds.
The external checkers take 65.1 and 39.3 seconds. Peak child RSS is 1,514
and 1,512 MiB respectively.

```sh
python3 experiments/compiler_validation/boxed_certificate/regression.py --file-counts 8192 --with-entry-comment
```

The single-entry byte sweep uses a repeated multibyte pattern and keeps the
four compiled functions fixed. A 15 MiB file produces a compact tree because
equal chunks share definitions. The two modes checked the same 6,334
declarations and all 1,830 LLVM bytes in 33.6 and 29.2 seconds. Peak worker RSS
was 1,446 and 1,443 MiB. The checker work for this pattern depends on the
number of distinct chunks as well as the total source size.

```sh
python3 experiments/compiler_validation/boxed_certificate/regression.py --entry-bytes 1048576 4194304 15728640 16777216
```

The packaged entry sweep uses the selected integer comparison in an edition 2026
manifest and a repeated UTF-8 comment in its root module. The header uses the
proved byte length to check every root module span. The file row checks the
same length, entry offset, path, accumulated bytes and manifest ownership.
The inputs regression moves the root module end one byte past the physical
entry and requires Lean to reject the span. Both modes returned 42 and checked
all 2,382 corpus bytes at each size on macOS arm64 under the same 120-second
worker timeout and 1,536 MiB Lean allocator limit.

| Entry bytes | Declarations | Wall time (s), Official / Fast | Replay (s), Official / Fast | Largest worker RSS (MiB), Official / Fast |
| ---: | ---: | ---: | ---: | ---: |
| 4,096 | 6,204 | 20.0 / 15.0 | 4.7 / 2.8 | 1,364 / 1,364 |
| 65,536 | 6,287 | 19.0 / 15.4 | 4.4 / 2.8 | 1,372 / 1,360 |
| 1,048,576 | 6,368 | 20.8 / 17.1 | 4.4 / 2.7 | 1,368 / 1,368 |
| 15,728,640 | 6,450 | 42.6 / 40.6 | 4.4 / 2.8 | 1,373 / 1,365 |
| 16,777,216 | 6,452 | 40.5 / 36.9 | 4.3 / 2.7 | 1,368 / 1,364 |

The 15 MiB entry yielded a 39,488,821-byte proof export. Private files at
sealing occupied 215,206,428 bytes for Official and 175,710,536 for Fast.
Repeated chunks share proof terms. The four-file sweep below keeps the flat
function graph fixed while increasing aggregate source size.

```sh
python3 experiments/compiler_validation/boxed_certificate/regression.py --package-entry-bytes 4096 65536 1048576 15728640 16777216
```

At exactly 16 MiB the flat entry yielded 6,338 declarations and all 1,830
corpus bytes in both modes. Official took 37.2 s and Fast took 32.0 s. The
packaged entry yielded the 39,488,670-byte export measured above. The public
proof input includes the original wire once, alongside the remaining revision
fields from the same artifact. A change to a revision field fails independent
capture. The standalone receipt retains its 16 MiB transport limit. The loader
rejects an entry one byte over its file limit. [CLI reference](../../../docs/guide/cli.md)

Four flat files with different prefixes and repeated UTF-8 comments exercise
the aggregate limit. At 64 MiB, each file is exactly 16 MiB. Both modes
checked the same 41,952,372-byte export, all 6,455 declarations and every
byte of the 1,830-byte boxed module on macOS arm64. Official took 47.5 s and
Fast took 44.2 s. The largest worker reached 1,631 and 1,632 MiB RSS
respectively under the 1,536 MiB Lean allocation limit. At sealing the
private files occupied 454,532,566 and 412,571,548 bytes. The physical
source reader compares the original file contents in slices of at most
64 KiB of UTF-8. An additional one-byte file exceeds the aggregate limit.
High-entropy text and large dependency graphs still need qualification.

```sh
python3 experiments/compiler_validation/boxed_certificate/regression.py --aggregate-bytes 65536 16777216 67108864
```

Official passes that snapshot to Lean 4.35.0’s `leanchecker --from-export`. It starts from an empty kernel environment and checks the reconstructed quotient primitives. Fast passes the same export to nanoda 0.4.19 and requires its exact declaration count. The qualification depends on the frontend, execution of the public Lean checker, the exporter and construction of the concrete subject from their outputs.

The four functions in `boxed-program.ll` return −226854911280625642308916404954512140972 before the host projects this integer to status 84. Both workers accepted the same 5,840-declaration export for all 1,830 bytes. The regression also accepts an alternative proof of the same proposition and rejects a foreign theorem, an ill-typed proof, a one-byte change to an add operand, a substituted source text and a changed package version. [Retained LLVM module](../../../llvm/src/boxed-program.ll)

The single-function program computes the integer quotient of 3²⁵⁶ by 7. Its intermediate squares exceed the constant folder’s work budget, so the compiled entry contains eight calls to the multiplication shim. Both workers check the same certificate for the full 403-bit result and all 1,977 bytes. [Vastitas source](../../../llvm/fixtures/SingletonPower.vast) · [LLVM module](../../../llvm/src/singleton-power.ll)

For each compilation the driver reopens the physical files, compares their bytes with the captured input and recomputes their offsets. The proof identifies this ordered snapshot with the layout decoded from the wire. For packages the driver follows the TOML dependencies from the root manifest and checks the package names, versions, editions and root source paths. Lean replays each module declaration at its source tokens. From these declarations the driver looks up both supported file names for each external module and checks the spelling of each path component. It checks every file occurrence in depth-first declaration order, including two names that resolve to the same file. Directory lookup and symlink resolution depend on the host filesystem. [Physical input decoder](../../../lean-kernel/VastitasKernel/PhysicalSources.lean) · [Checked module spans](../../../lean-kernel/VastitasKernel/FiniteSourceFiles.lean)

For each edition 2026 manifest the driver reconstructs the ordered dependencies from
the preserved TOML text and resolves their paths on disk. It visits packages in
dependency order and records each shared package once. Flat compilations use the
reserved flat owner. The per-input Lean proof checks this graph and the wire's
compatibility flag against the same header and package decoders as the public compiler.
Given a publication, both the straight-line and control-flow theorems identify
these owners with those in its checked program. [Package graph proof](../../../lean/VastitasOracle/CertificatePackages.lean)

The inputs suite calls the same integer helper through a flat library and through an external module in a dependency. The flat case places the edited helper in file 129, immediately after the first proof batch. The package has five physical inputs. Editing a comment in its dependency manifest changes the function revision and preserves all 1,127 LLVM bytes. The suite checks both verifier modes and rejects the earlier proof after that edit.

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

The physical layout proof checks each file at its incoming byte offset and tracks
the remaining manifest names before composing the rows. On the same macOS arm64
host, nanoda replay of the six-file program took 9.5 seconds and 3,499 MiB peak
RSS before this change. With literal LLVM lines and shared file prefixes it took
3.1 seconds and 479 MiB. Both verifiers replayed 5,889 declarations for the
current certificate and obtained 42 and the same 2,051 LLVM bytes. The assembly
regression checks a 1,536 MiB RSS budget for this nanoda worker.

For `F` file rows and `P` packages, the generator emits one step proof per row and one
header proof. The layout checker uses a balanced manifest set with logarithmic lookup in
`P`. Each comparison checks the UTF-8 length first, then inspects at most the full label
on a tie. The measurements at the file-count limit use short flat libraries.
The source-byte limit and large manifest graphs have separate costs.

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
