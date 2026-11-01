# Linux source block lifetimes: complete standard profile

This record measures clean `8212d7d0a6720e37913b6d44d5932e8ff263ead8` on
GitHub-hosted Linux x86-64 (7.0.0-1017-azure, glibc 2.43), with the explicit
HASWELL backend target. Source-cost schema 4 connects the actual checked
two-edge contraction source to the calibrated lifetime runtime across both
backends. It contains no operation timings or controlled-host acceptance claim.

The [complete compact record](evidence.zip) and original
[manifest with full replay summary](artifact-manifest.json) preserve:

- All 12 tiny/small/bulk real/complex cases with/without padding, eight
  backend/runtime configurations and batches 1, 2 and 17.
- 96 canonical public check/build/executions using stock libraries; 1,152 normal
  observations, 96 failure cleanups and 18,048 actual CBLAS calls.
- 12,480 calling-thread statistics snapshots and 1,560 before/after lifetime
  boundary pairs, independently reconciled with main-heap visits.
- 66 actual source packing contracts, checked by 264 additional plain/sanitized
  stock/diagnostic footprint executions.
- Both complete nested allocator calibrations, the backend calibration, exact
  returned source, raw commands, linker maps and object/archive receipts.
  All 86 source snapshots match the measured Git commit and both macOS records.

The archive has 12,813 members and 97,879,951 bytes. Its SHA-256 is
`5e0b78a1a8e18b8624846e46dad3649a1748e820c4d63988392388925c36c7be`.
It is an exact member of the original
[GitHub artifact](https://github.com/MGYamada/Vastitas/actions/runs/41328770423/artifacts/13093344313);
the outer ZIP's 92,065,912 bytes and SHA-256
`a4281e54a1c1ff2811ffabf1c3e84d674a2bde6ba90da5bdb610b3b642b625c3`
match GitHub's published digest. The [provenance](github-provenance.json) retains
the run, job, original artifact and download receipts. Neither retained member
was regenerated. Executables and Lake caches are excluded; their fingerprints
remain in the evidence. Offline replay does not execute archived code.

The [original push job](https://github.com/MGYamada/Vastitas/actions/runs/41328770423/job/124914221870)
completed measurement/export and all 26 fresh lifetime-calibration tests. Its
90-test source suite failed only
`test_phase_hooks_must_bracket_the_existing_observer`: the test helper selected
the inspected and mutated cases independently from unordered filenames. Commit
`a4e50ee4d695b005514c359f58d6e3e0f601892e` makes that selection deterministic
and checks that the mutation changes the inspected bytes. The measured source
and runtime are unchanged; this original CI run is still a failed run.

After that correction, independent replay passes, and 33 actual lifetime,
allocator-record and complete packing regressions pass against this ZIP with
no skips. The retained-export regression also replays all three complete
macOS/Linux/large-output archives, requires equality with each original manifest
summary and checks identical measured input hashes. The complete source suite
passed 90 tests against the macOS standard record before that additional
retained-export test was added; final-head CI is a separate requirement.

## Observed logical-block costs

All 12 cases and both backends agree on the following run-scope costs in the
private lifetime runtime. Independent calling-thread statistics reconcile
allocation counts, usable-byte traffic and live-byte changes.

| Run scope | Allocations / frees | Requested / acquired / released bytes | Peak usable bytes above entry |
| --- | --- | --- | --- |
| Generated lifecycle, 1 operation | 5 / 5 | 104 / 104 / 104 | 72 |
| Generated lifecycle, 2 operations | 7 / 7 | 144 / 144 / 144 | 72 |
| Generated lifecycle, 17 operations | 37 / 37 | 744 / 744 / 744 | 72 |
| Generated caller-buffer reuse, any batch | 3 / 3 | 64 / 64 / 64 | 48 |
| Matched C, either scope/any batch | 0 / 0 | 0 / 0 / 0 | 0 |
| Checked generated failure | 7 / 7 | 180 / 184 / 184 | 136 |

The failure's two actual error payload objects have 92 requested / 96 usable
bytes, separately from the selected error-result object. Selected-site,
statistics and lifetime channels overlap and must not be added together.
The C comparator remains Lean-hosted; its run scope follows initialization and
cold generated work. Zero run-scope counts do not establish zero startup cost.

Pre-cold state retains 11,130–11,132 cumulative allocations, 2,986 live blocks,
124,768 or 124,776 live usable bytes and a global peak of 125,040 or 125,048
bytes. These include initialization and command-argument traffic. Setup can
release preexisting arguments while still allocating. Interval peaks expose
transient run storage even when entry/exit live state agrees and startup had
a higher global peak. The [macOS standard](../2026-11-02-macos-lifetimes/RESULTS.md)
and [large-output](../2026-11-02-macos-lifetimes-streaming/RESULTS.md) records
agree on these run-scope costs; they are separate executions, not timing pairs.

The lifetime observer adds 4,194,417 declared static bytes and 1,208 bytes of
phase storage, separately from the existing 43,732-byte statistics observer.
Native arenas and backend workspace remain distinct channels. Independent
subsystem peaks cannot be summed as a simultaneous whole-process peak.
Physical allocator backing/RSS, libc/GMP and other allocator traffic, reporting,
process teardown, stock timing, full cost attribution and Fast like C acceptance
remain open.
