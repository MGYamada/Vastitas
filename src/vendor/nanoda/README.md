# Bundled Lean export checker

This directory contains the twelve production modules of ammkrn/nanoda_lib
0.4.31 from commit `8de7e0c4ed3052745a7f8725164efd9e76d84c56`, under
the accompanying Apache-2.0 license. The Vastitas audit worker uses them
to check existing Lean exports. [Upstream source](https://github.com/ammkrn/nanoda_lib/tree/8de7e0c4ed3052745a7f8725164efd9e76d84c56/src)

The local module root keeps the checker private. Imports referring to the
upstream crate root refer to `crate::nanoda` here. Three quotation macros
are local to their module and `hash64` is visible inside the checker.
The parser's inline regression tests remain available. Upstream's CLI and
standalone test harness are maintained in the upstream repository.

To verify the exact source adaptation in a project checkout, run
`python3 scripts/check_nanoda_vendor.py PATH_TO_UPSTREAM_GIT_CHECKOUT`.
The comparison reads the pinned Git objects independently of the upstream
checkout's current branch.
