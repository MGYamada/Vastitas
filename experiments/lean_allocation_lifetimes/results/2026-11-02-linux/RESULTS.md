# Linux private block lifetime calibration

This record comes from [PR CI run 41325335132](https://github.com/MGYamada/Vastitas/actions/runs/41325335132),
[Linux numerical job 124903981045](https://github.com/MGYamada/Vastitas/actions/runs/41325335132/job/124903981045),
artifact `13090633447` (`lean-heap-lifetimes-ubuntu-latest-pull_request`).
The [retained GitHub metadata](github-provenance.json) identifies the clean test
merge `e732f2554437497b9679a82daa81b5331ecde1f9`, whose parents are main
`0e4d117a932a9e83d046a0bb3a9c30480c8d7ad7` and feature
`a6ff4d07180a1652648abaacb7c6bf7557b733b0`. The test merge and feature head have
the same tree, `4aefa0a60dac566ab6ff914663d193515029d629`. All **27** repository
input snapshots independently match the feature revision. Publication and final
merge are later, separate revisions.

[evidence.zip](evidence.zip) is the original GitHub artifact ZIP, unchanged:
489 members, 6,874,210 bytes and SHA-256
`c172da6748b5b9eac48e66ade242df95cb5a2325f0f8eaeae9f8aa19a94fff28`.
The digest agrees with GitHub's artifact metadata. The archive includes hidden
members of the pinned upstream source tree; the offline audit checks every
reconstructed source file rather than accepting an incomplete upload.

The host was x86-64 Linux 7.0.0-1017-azure with glibc 2.43, GCC 15.2.0 and
Clang 21.1.8 with libc++. Lean was 4.35.0. The runner preserves `clang++` as the
invoked C++ driver; resolving it to `clang` incorrectly omitted C++ ABI linkage
in the initial CI attempt. This record is from the corrected, successful run.
The shared runner is not a controlled timing host. No operation clocks are used.

All **7** normal executions and **2** expected capacity-failure controls pass:
54 Lean snapshots, 44 native snapshots and 26 observation/provenance tests with
no skips in this numerical step. Only `mimalloc.cpp.o` changes in the private
runtime; **34** other members remain byte-identical. The observer is separately
linked and its fixed storage is 4,194,417 bytes.

| Observation | Retained result |
| --- | ---: |
| Lean baseline live blocks / usable bytes, all runs | 2,985 / 124,728 |
| Startup allocations, runs 1 / 2 / 3 | 11,105 / 11,106 / 11,106 |
| Startup allocation-hook requests, runs 1 / 2 / 3 | 249,251 / 249,275 / 249,275 bytes |
| Lean fixture maximum simultaneous usable bytes, all runs | 18,999,096 |
| Native held small + 4 MiB + 32 MiB usable-byte peak | 37,748,752 |
| Eight-worker allocation/free pairs, each native run | 160,000 |
| Concurrent native peaks, runs 1 / 2 / 3 | 41,920 / 31,664 / 36,792 bytes |
| Concurrent peak in the sanitizer fixture | 31,864 bytes |
| Final independently visited allocator metadata | 1 block / 320 usable bytes |

Every paired Lean observation leaves the counters unchanged, and independent
heap visiting matches the actual live set. All known hold, release and transient
traffic and peak checks pass. Each concurrent peak lies within the independent
worker held-pair bounds; workers restore their initial live set. Scheduling
variation is retained instead of requiring identical peaks across runs or hosts.
Both capacity controls return exit 90 and the exact audit diagnostic.

```sh
python3 experiments/lean_allocation_lifetimes/verify.py \
  experiments/lean_allocation_lifetimes/results/2026-11-02-linux/evidence.zip
python3 -m unittest discover -s experiments/lean_allocation_lifetimes -p 'test_*.py'
```

The [macOS record](../2026-11-02-macos/RESULTS.md) independently satisfies the same
finite contracts. ASan/UBSan instrument the observer/probe only, not the upstream
allocator; LeakSanitizer is disabled. These records do not establish actual
public `.vast` source cost coverage, other allocators, physical backing/RSS,
stock-runtime speed, native refinement or Fast like C acceptance. No Stage 1
issue is closed by this calibration alone.
