# Appendix F: Contributing and validation

This appendix holds the procedures of a contributor: the checks that a change
must pass, the maintenance of this book, the steps that add a primitive, and
the decision record that governs what enters the standard library.

Read the contributor guidance in
[`AGENTS.md`](https://github.com/MGYamada/Vastitas/blob/main/AGENTS.md) before
changing the repository. It sets the scope rules, the architecture invariants
and the validation commands. `CLAUDE.md` is an identical copy, and
`python3 scripts/check_docs.py` checks that the two files are equal and within
their size limits.

- [Run compiler, proof and native checks](../development/validation.md) lists
  the Rust, kernel, oracle, bridge and native checks, and the jobs of the
  continuous integration that run them.
- [Maintain the documentation](../development/documentation.md) explains how to
  build, check and change this book, and holds its style guide.
- [Add an indexed primitive](../development/primitives.md) lists what a
  primitive touches in the kernel, the oracle, the frontend and the tests.
- [Standard-library admission and trust](../adr/0001-mathematics-first-stdlib.md)
  is the decision record ADR 0001. It states the test that a mathematical
  family or operation must pass to enter `std`, and the procedure of an
  admission.

Report the commands that you ran and their results. Report native tests apart
from proofs, and do not claim that a check passed when you did not run it.
