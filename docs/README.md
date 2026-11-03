# Vastitas

Vastitas compiles mathematical programs to native executables. A Rust frontend
reads `.vast` source, and an independent Lean checker validates the program
before code generation. The finite Stage 1 compiler includes functions and
dispatch, ordinary and smooth affine geometry, storage ownership, real and
complex matrix multiplication, and checked tensor contraction trees.
[Stage 1 delivery and evidence](https://github.com/MGYamada/Vastitas/blob/7d612a4b76ef54a17bd859c466fb3407912ac14b/docs/stage1-completion.md)

## Where the language goes next

Start with [Historical Stages 2–7](guide/historical-roadmap.md). The roadmap
follows one line of development from the coordinate ring of an affine scheme
to an observable compared with physical measurements. Each stage has an
example that could establish completion and links to the issues that govern
the current plan.

To build the compiler or run existing programs, use the
[repository guide](https://github.com/MGYamada/Vastitas#readme).
The [verification reference](https://github.com/MGYamada/Vastitas/blob/main/docs/verification.md)
identifies the proved guarantees and their assumptions.

Copyright 2026 Vastitas Project Contributors.
[Apache License, Version 2.0](https://github.com/MGYamada/Vastitas/blob/main/LICENSE)
