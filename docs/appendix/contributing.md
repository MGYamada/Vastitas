# Appendix F: Contributing and validation

Read the contributor guidance in
[`AGENTS.md`](https://github.com/MGYamada/Vastitas/blob/main/AGENTS.md) before
changing the repository. It sets the scope rules, the architecture invariants
and the validation commands. `CLAUDE.md` is an identical copy.

- [Run compiler, proof and native checks](../development/validation.md) lists the
  Rust, kernel, oracle, native and CI checks.
- [Maintain the documentation](../development/documentation.md) explains how to
  build, check and change this book.
- [Add an indexed primitive](../development/primitives.md) lists what a
  primitive touches in the kernel, the oracle, the frontend and the tests.

Report the commands you actually ran and their results. Native tests and proofs
are reported separately, and a check that was not run is not claimed to pass.
