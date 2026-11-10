# Getting Started

This chapter takes you from a machine without Vastitas to programs that you
check, build and run. It has four sections:

- [Installation](installation.md) builds the two parts of the compiler.
- [Hello, Vastitas](hello-vastitas.md) writes a first program, checks it,
  builds it and runs it. It then reads a first diagnostic.
- [Creating a package](creating-a-package.md) puts a program in a package
  with a manifest, and gives the package a dependency.
- [The standard library](stdlib.md) calls functions of the standard library,
  from a package and from a single file.

Vastitas runs on macOS and Linux. You write `.vast` source files, and two
commands work on them: `vastitas check` checks a program, and
`vastitas build` checks it and builds a native executable. There is no REPL,
interpreter, language server or package registry.

## See also

- [Programs](../language/programs.md): what a program is, and its entry
  point.
- [Packages](../packages.md): manifests and dependencies.
- [Appendix A](cli.md): the commands and their options.
