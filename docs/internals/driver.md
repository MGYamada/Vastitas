# The driver

This chapter describes the [driver](../appendix/glossary.md#driver): what the
Rust side of the compiler does between the command line and the kernel, and
between the kernel's response and the output file. It covers reading and
parsing the inputs, loading packages, choosing the wire protocol, starting
the kernel, rendering diagnostics, the native build, output files, signals
and locks. Each section names the source file that holds the code and the
tests that pin it.

The rules that a user relies on are elsewhere, and this chapter does not
restate them. [Appendix A](../guide/cli.md) gives the commands, the options
and the environment variables. [Diagnostics](../language/diagnostics.md)
gives the form, the place, the number and the order of diagnostics and the
exit status. [Limits](../language/limits.md) and
[Appendix D](../appendix/limits.md) give the limits.
[Compiler architecture](../development/architecture.md) places the driver
among the other components.

## The command line

`src/main.rs` passes the arguments to `driver::run` in `src/driver.rs`. An
error of `run` is one string. `main` writes it to standard error and exits
with the status of `process::exit_code`.

`run` works in this order:

1. It installs the signal handlers
   ([Subprocesses and signals](#subprocesses-and-signals)).
2. It answers `--help`, `-h` and `--version` and returns. The version line
   lists `ir::PUBLIC_PROTOCOLS`, the wire protocols that the driver
   writes.
3. It passes `audit-lean` to `src/internal_lean_audit.rs`
   ([The proof-audit command](#the-proof-audit-command)).
4. `options` reads the remaining arguments into a mode and its paths. The
   command `check` becomes the kernel mode `check`, and `build` becomes the
   kernel mode `emit`. An argument that the usage does not admit is
   `E_USAGE`.
5. For `build` it checks the output path
   ([Output files](#output-files)).
6. It reads and parses the inputs and writes the request.
7. It locates and starts the kernel.
8. For `build` it runs the native build and installs the output.

The steps before step 7 need no kernel. The driver therefore reports a wrong
output path and a syntax error without one.

Tests:

- `tests/driver_issues.rs::subcommand_help_succeeds_without_inputs_or_backend`
  and `version_reports_package_and_every_public_wire_protocol`;
- `tests/packages.rs::manifest_validation_and_cli_modes_are_explicit`, for
  the options that exclude one another;
- `tests/driver_issues.rs::invalid_output_paths_fail_before_starting_the_backend`
  and `output_protection_still_precedes_source_parsing`, for the order of
  steps 5 to 7.

## Reading inputs

`src/sources.rs` holds the table `Sources`. Every file that the driver reads
has one entry: a manifest, an entry file, a library and a module file. An
entry holds the path that diagnostics show, the canonical path, the device
and inode numbers, the text and a byte offset.

`Sources::push_file` reads one file:

- It opens the canonical path without blocking and inspects the open
  descriptor. A descriptor that is not a regular file is `E_INPUT`. The
  driver therefore reads no byte of a FIFO or a device.
- It compares the size of the file with what is left of the budgets of
  `MAX_FILE_BYTES` and `MAX_INPUT_BYTES`, before it reads and again for each
  block that it reads, because a file can grow. `MAX_INPUT_FILES` bounds the
  number of entries. A file that two modules load has two entries and counts
  twice. An exceeded budget is `E_LIMIT`.
- It requires UTF-8 text (`E_INPUT`).
- It checks for a signal before each block.

The byte offset of an entry is the offset of the entry before it, plus the
length of that entry's text, plus one. The files of one compilation therefore
occupy disjoint ranges of byte offsets. A **span** is the position of one
node of the request: a start and an end as such byte offsets, and a line and
a column that are local to the file. A span holds no path. The kernel returns
spans, and `Sources::file_index` finds the file of a span by its start
offset.

The request names files only in its field `file` and, in
[manifest mode](../appendix/glossary.md#manifest-mode), in `root`, in the
`source` of each package and in the `target` of each dependency. In
[flat mode](../appendix/glossary.md#flat-mode) `file` is the name of the
entry file as the command spells it. In manifest mode all four hold
canonical paths of manifests, and `source` is part of the identity of a
package.

In flat mode `Sources::load` reads the entry file and then the libraries, in
the order of the command. It rejects a
name that does not end in `.vast`, and a file that the command names twice,
which it finds by the canonical path (`E_INPUT`).
[Flat mode](../language/programs.md#flat-mode) gives both rules.

Tests:

- `tests/input_safety.rs::blocking_and_device_sources_are_rejected_without_reading`;
- `tests/input_safety.rs::oversized_regular_input_is_rejected_before_parsing`,
  `reused_source_bytes_are_charged_for_each_logical_module` and
  `input_file_count_is_bounded_before_the_backend`;
- `tests/usability.rs::library_identity_notes_keep_library_source_locations`,
  for the place of a kernel diagnostic in a library.

## Parsing

`src/frontend.rs` holds the lexer, the token primitives of the
recursive-descent parser and the entry points. The rest of the parser and the
resolver of lexical scopes are in `src/frontend/`: `declarations.rs`,
`authority.rs` for edit authority, `types.rs`, `expressions.rs` and
`resolver.rs`.
[Lexical structure](../language/lexical-structure.md) gives the rules of
source text.

- The lexer admits ASCII identifiers. It counts positions in UTF-8 bytes and
  columns in Unicode scalar values. It rejects a byte order mark, a line
  separator other than LF and CRLF, and a character in a comment that can
  hide text (`E_LEX`).
- The parser bounds the nesting of types, expressions and blocks with
  `MAX_PARSE_NESTING`, and the depth of an expression tree with
  `MAX_AST_DEPTH`. `build.rs` generates both constants from
  `lean-kernel/compiler-limits.json`. The second bound covers a chain of
  binary operators, which the parser reads in a loop.
- The parser stops at its first error.

`frontend::parse_sources` serves flat mode. It parses each file by itself,
so no construct continues across the end of a file. It collects the
declarations of all files in one `ir::Module`. `Resolver::module` then checks
the names and the scopes of the whole module and returns every error that it
finds. `Sources::parse` rejects a `main` in a library (`E_LIBRARY`).

`frontend::parse_module_source` serves manifest mode. It parses one module
file with the package syntax: `mod`, `use`, `pub` and the declarations that
only packages have. It runs no resolver. Every path of the source reaches the
request unresolved, and the kernel resolves it. The result holds one record
for the module and for each inline module, and the list of the `mod name;`
declarations whose files the loader has to read.

Three files extend the parser for packages:

- `src/frontend/indexed_parser.rs` parses indexed declarations, indexed type
  annotations and typed `pack` expressions. It marks a module that uses one,
  which the choice of the wire protocol reads.
- `src/frontend/resource_parser.rs` parses resource functions and their
  statements. It checks that the kernel's decoder can read the statements of
  each function within its bound. `packages::load` adds up the `value`
  blocks of all resource functions and compares the sum with the bound of
  the kernel. A program beyond one of the two bounds is `E_RESOURCE_LIMIT`
  at the function.
- `src/frontend/exact_float.rs` converts the literal of an `f64(…)` payload
  to its bits. It accepts a decimal literal only when an integer
  reconstruction of the bits equals the literal.

The parser writes the records of `src/ir.rs`, `src/namespace.rs`,
`src/indexed.rs` and `src/storage.rs`. Their `serde` forms are the wire
forms of the request.
`src/primitive_table.rs` gives the fields of each indexed primitive.
`scripts/check_primitive_table.py` generates it from the families of the
kernel, and CI fails when the file differs from them. No identifier of a
source file becomes Lean code: the kernel names every generated definition
itself.

Tests:

- `tests/frontend_diagnostics.rs::source_cases_produce_the_recorded_frontend_diagnostics`
  and the unit tests in `src/frontend/tests.rs`;
- `tests/compiler.rs::excessive_source_nesting_is_a_diagnostic_not_a_process_abort`
  and `tests/stabilization.rs::else_if_limit_names_the_chain_and_accepts_the_documented_boundary`;
- `tests/promotion.rs::stdlib_ir_matches_proof_fixture`, which compares the
  whole request of three library files with a recorded file;
- `tests/usability_kernel.rs::frontend_and_kernel_use_the_same_name_violation_codes`.

## Loading packages

`src/packages.rs` loads the packages of manifest mode.
[Packages](../packages.md) and [Modules](../language/modules.md) give the
rules. `packages::load` starts `Loader::package` at the root manifest.

`Loader::package` handles one manifest:

- It rejects a manifest whose file name is not `Vastitas.toml` (`E_INPUT`),
  as [Manifests](../packages.md#manifests) requires. The canonical path of
  the manifest is the `source` of the package in the request.
- A dependency that names a manifest on the current chain of dependencies
  is `E_CYCLE`. The loader loads a manifest once, so two dependency aliases
  of one location yield one package. `MAX_PACKAGE_NESTING` bounds the depth
  of the dependencies.
- The `toml` crate decodes the manifest into records that admit no unknown
  key. An error of the manifest is `E_MANIFEST`.
- The loader loads the dependencies in the order of their aliases and then
  the modules of the package. The packages of the request are therefore in
  an order in which a package follows its dependencies.

`Loader::module_file` handles one module file:

- It compares the canonical path of the file with the directory of the
  manifest, so it rejects a symbolic link that leaves the package
  (`E_INPUT`).
- The device and inode numbers of the files on the current chain of `mod`
  declarations form a set. A file that is in the set is `E_CYCLE`.
- For each `mod name;` the loader looks for `name.vast` and `name/mod.vast`
  below the directory of the root file. `existence` compares each component
  with the names that the directory lists, so a file whose name differs only
  in case does not count on a file system that ignores case. The loader
  rejects a declaration for which neither file or both files exist
  (`E_INPUT`).
- The loader counts every module record, including inline modules and a file
  that two `mod` declarations load, against `MAX_LOADED_MODULES`.

[Module declarations](../language/modules.md#module-declarations) gives the
rules on module files that these checks enforce.

The loader resolves no path of the source and loads no package for one. The
recipient of a grant stays the name that the source writes.

Tests:

- `tests/packages.rs::manifest_validation_and_cli_modes_are_explicit`,
  `dependency_cycles_collisions_and_main_selection_are_checked` and
  `filesystem_escape_and_module_loading_cycles_are_rejected`;
- `tests/driver_hardening.rs::module_files_must_match_module_names_exactly`;
- `tests/input_safety.rs::symlink_module_fanout_is_bounded_across_the_package_closure`.

## Choosing the wire protocol

The driver writes one request. It chooses the version from the declarations
that the program holds and, in manifest mode, from the `geometry_compat`
export of a manifest. [Protocol selection](../protocol.md#protocol-selection)
gives the list.

- In flat mode `frontend::parse_sources` writes version 2. It writes version
  4 with `input: "flat"` when the module holds an abstract type, a subtype or
  an abstract method.
- In manifest mode `packages::request_protocol`, at the end of
  `packages::load`, takes the first condition that holds, from version 9
  down to version 3. It writes
  `input: "package"` for every version other than 3.

`serde_json` serializes the request in `kernel_request`. A first pass
counts the bytes and stops at `MAX_REQUEST_BYTES`, the limit `requestBytes`
of `lean-kernel/compiler-limits.json`, which also bounds the requests that the
kernel reads. A request beyond it is `E_LIMIT` at `FILE:1:1`, and the driver
never holds it. A second pass writes a request within the limit into a buffer
of its size. The driver sends the same request for
`check` and for `build`. It requires the version of a successful response to
equal the version of the request (`E_PROTOCOL`). It shows the diagnostics of
a failure response of another version and adds a note.

Tests:

- `tests/packages.rs::package_requests_do_not_fall_back_to_a_protocol_two_backend`;
- the unit tests `bounded_json_stops_at_its_bound` and
  `bounded_json_reports_an_encoding_error` of `src/driver.rs`, and the
  ignored `tests/input_safety.rs::request_bound_is_a_limit_of_the_program`;
- `tests/driver_issues.rs::mismatched_failure_version_preserves_diagnostics_but_success_is_rejected`;
- `tests/edit_authority.rs` and `tests/protocol_shape.rs`, which read the
  version and the fields of requests that the driver writes for packages.

## Starting the kernel

`kernel_root` gives the [kernel root](../appendix/glossary.md#kernel-root):
the value of `VASTITAS_KERNEL_ROOT`, or the `lean-kernel` directory of the
sources that the driver was built from, as a canonical path. The kernel
executable is the value of `VASTITAS_KERNEL`, or
`.lake/build/bin/vastitas-kernel` in the kernel root. `run` computes the
root for the default executable and for every `build`, so a `check` with
`VASTITAS_KERNEL` reads no root. A default executable that does not exist is
`E_BACKEND`, with the command that builds it.
[The kernel and its build identity](../guide/cli.md#the-kernel-and-its-build-identity)
gives the rules.

`invoke_kernel` starts the executable with the mode as its only argument. It
writes the request to standard input and reads standard output. It keeps at
most `MAX_BACKEND_RESPONSE` bytes of standard output and fails beyond them.

### The build identity

The numbers of the wire protocols do not change between releases. A kernel
of another revision can therefore answer a request of the same version. The
[build identity](../appendix/glossary.md#build-identity) ties a kernel
executable to a driver. This section says how each side computes it.

- The kernel computes the digest while Lean elaborates `Main.lean`
  (`kernel_source_digest%` in `VastitasKernel/BuildIdentity.lean`). The
  digest covers `Main.lean`, every module that it imports and whose source
  lies in the kernel package, and `compiler-limits.json`. Every response
  carries the identity in the field `kernel`.
- `build.rs` computes the same digest from the same files of the sources
  that the driver is built from (`runtime_inputs::executable_inputs`). It
  reads the version of Lean from `lean-kernel/lean-toolchain`. Cargo runs
  `build.rs` again when one of these files changes.
- The digest is FNV-1a with 64 bits over the path, the size and the bytes
  of each file, in the order of the paths.
- `lean-kernel/lakefile.toml` names each digested file as an input of the
  executable. Lake therefore elaborates `Main` again, with its digest, when
  a file changes that changes no compiled module.

`invoke_kernel` applies its checks in this order:

1. A kernel that does not start, and a failure of the capture other than
   an interruption, are `E_BACKEND`.
2. Standard output that is not one JSON value is `E_PROTOCOL`, followed by
   the standard error of the kernel. A kernel that exits without a response
   has this form, whatever its exit status.
3. For a failure response, one whose `ok` is `false`, the driver renders the
   diagnostics. It adds a note for another version, and a note that the
   diagnostics may come from a stale or foreign kernel when the identity is
   missing or differs. A failure response without a diagnostic is
   `E_PROTOCOL`.
4. Any other response of another version than the request is `E_PROTOCOL`.
5. A response of the version of the request whose `ok` is not `true`, and a
   kernel that exits with an unsuccessful status, are `E_BACKEND`.
6. A success response whose identity is missing or differs is `E_BACKEND`.

The identity covers the kernel executable. It does not cover the files that
a native build compiles, which [The native build](#the-native-build)
compares.

Tests:

- `tests/compiler.rs::backend_is_required_and_failure_has_no_frontend_fallback`;
- `tests/driver_issues.rs::explicit_kernel_check_does_not_require_a_kernel_root`
  and `unbuilt_default_kernel_names_its_absolute_root`;
- `tests/driver_hardening.rs::kernel_build_identity_fails_closed`,
  `kernel_build_identity_covers_the_compiler_limits` and
  `kernel_executable_needs_every_file_of_its_identity`;
- `tests/driver_hardening.rs::subprocess_output_is_bounded`.

## Rendering diagnostics

A diagnostic of the frontend and a diagnostic of the kernel take the same
path. `Sources::diagnostic` finds the file of the span, and writes the path,
the line, the column, the code and the message.
[Diagnostic lines](../language/diagnostics.md#diagnostic-lines) gives the
form.

- For a kernel diagnostic `invoke_kernel` reads `code`, `message` and `span`
  from the response. It renders each entry of `notes` as a line with the
  code `note` and the place of the note.
- `sources::shown_text` writes every path, and the message of every
  diagnostic with a place and of its notes. It writes some characters as
  their code points.
  [Names and text in diagnostics](../language/diagnostics.md#names-and-text-in-diagnostics)
  gives the rule and the characters.
- The driver writes three texts as the child process wrote them: the
  standard error of the kernel after an `E_PROTOCOL` for a response that is
  not JSON and after an `E_BACKEND` for a failed kernel, and the output of
  Lake after `E_BUILD`.
- `packages::manifest_error` renders an error of the `toml` crate. It shows
  the quoted line of the manifest through `shown_text` and moves the marks
  under the line by the width that the names add.
- An error without a place is the code and the message alone. The errors of
  the command line, of the output path, of the kernel process and of the
  native build have this form.

Tests:

- the unit tests of `src/sources.rs` and of `src/packages.rs`;
- `tests/input_safety.rs`: the six tests whose names end in
  `no_terminal_controls`;
- `tests/packages.rs::package_diagnostics_preserve_main_and_identify_the_declaring_manifest`
  and `namespace_diagnostics_render_source_names_and_keep_locations`.

## The native build

For `build` the driver reads three fields of the `emit` response:
`lean_source`, `storage_runtime` and `numerical_runtime`.
[Wire protocols 2–9](../protocol.md) describes them. The kernel generates
`lean_source` from the result of the check of the same request, as
[The three checker routes](../development/architecture.md#the-three-checker-routes)
describes. After the kernel answers, `run` checks the response and the
options in this order:

1. A response without `lean_source` is `E_PROTOCOL`.
2. The driver accepts the two runtime fields only in a response of protocol
   8 or 9, and a numerical requirement only with a storage requirement
   (`E_PROTOCOL`).
3. A numerical requirement without `--openblas-prefix` is `E_BUILD`.
4. `--openblas-prefix` or `--native-cc` for a response without a numerical
   requirement is `E_USAGE`.

[Numerical builds](../guide/cli.md#numerical-builds) gives the rules on the
two options.

A **runtime input** is a file that Lake reads from the kernel root when it
compiles a generated program. `src/runtime_inputs.rs` lists the runtime
inputs of three packages: the kernel package, the storage runtime in
`native` and the numerical runtime in `numerical`. Each list names files,
the modules that generated programs import, and the other name of the
package's Lake configuration, which the driver refuses. `build.rs` digests
the runtime inputs of the driver's own sources into a table, and fails when
the sources do not hold what the lists name.

`build_native` works in this order:

1. It reads `lean-toolchain` of the kernel root. It rejects a file that it
   cannot read, an empty file and a pin other than the pin that the driver
   was built for (`E_BUILD`).
2. It selects the packages: the kernel package, and the storage runtime and
   the numerical runtime when the response requires them.
3. `check_generated_imports` reads the imports of the generated source. An
   import of a module that is not a listed module of a selected package is
   `E_PROTOCOL`.
4. `verify_runtime_inputs` digests the runtime inputs of each selected
   package in the kernel root: the listed files, the listed modules and the
   modules of the same library that those import. It compares them with the
   table of `build.rs`. A file that differs, is missing or is added, and a
   forbidden name that exists, are `E_BUILD`. The diagnostic names the
   files.
5. It creates a private directory in the temporary directory of the system,
   with mode 0700 whatever the umask. A guard removes the directory when
   `build_native` returns.
6. It composes a Lake configuration. The configuration is a `lakefile.toml`
   that requires the kernel package by its path and, when selected, the
   storage runtime. For a numerical program it is a `lakefile.lean` that
   requires the kernel package and the numerical runtime, and passes the
   canonical path of the OpenBLAS prefix to the numerical runtime. With
   `--native-cc` the driver runs `lean --print-prefix` in the kernel root
   and writes the `lib` directory of that installation into the
   configuration as `moreLinkArgs`. `toml_string` and `lean_string` escape
   each path for the syntax of its file. A path that is not UTF-8 is
   `E_BUILD`.
7. It writes the configuration, a copy of `lean-toolchain` and the generated
   source as `Main.lean` into the directory.
8. `check_lean_version` runs `lean --version` in that directory, as Lake
   resolves `lean` there. Another version than the pinned one is `E_BUILD`.
9. It takes the locks of the selected runtime packages ([Locks](#locks)).
10. It runs `lake build program`, with `LEAN_CC` set when the command names a
    C compiler. It keeps the last `DIAGNOSTIC_TAIL` bytes of each output
    stream. A failure of Lake is `E_BUILD` with that output.
11. It installs the executable of the project ([Output files](#output-files)).

Steps 1 to 4 write nothing.
[What `check` and `build` start](../guide/cli.md#what-check-and-build-start)
gives the rules on the toolchain, and
[Checks on the kernel root](../guide/cli.md#checks-on-the-kernel-root) says
what the comparison of step 4 covers and what it does not.

Tests:

- `tests/native_build_identity.rs`: a changed runtime source under an
  unchanged kernel, a kernel executable with the root of another tree, the
  optional packages, the forbidden names, the lists against the Lake
  configurations, and a generated source with another import;
- `tests/resource_entry_runtime.rs`, for the storage requirement of a
  resource entry and a response that imports the storage runtime without it;
- `tests/driver_hardening.rs::lean_toolchain_mismatch_fails_before_lake`,
  `build_directory_is_private_under_a_permissive_umask`,
  `generated_manifests_escape_paths_for_their_own_syntax`,
  `non_utf8_kernel_root_is_rejected_before_the_backend`,
  `native_options_require_a_numerical_program` and
  `optional_runtime_flags_are_refused_for_protocols_before_eight`;
- `tests/driver_issues.rs::native_project_uses_the_selected_kernel_toolchain`
  and `missing_or_empty_kernel_toolchain_preserves_output`;
- the unit tests of `src/driver.rs` for the embedded tables and for the two
  escapes.

## Output files

The driver replaces the output file in one step and leaves an existing file
as it is until that step.

- `validate_output` runs before the driver reads an input. It rejects a
  path that names no file, a path whose directory does not exist, and an
  existing output that is neither a regular file nor a symbolic link to one
  (`E_OUTPUT`).
- A **staging file** is a file beside the final place of the output, to
  which the driver copies the executable before it renames the file onto
  that place. `probe_output_directory` creates and removes one before the
  driver reads an input, so a directory that admits no file fails before
  the kernel runs.
- The driver rejects an output that is an input (`E_OUTPUT`).
  `OutputIdentity` holds the canonical path and the device and inode numbers
  of an existing output, and the driver compares each entry of `Sources`
  with both. Manifest mode compares each file when the loader reads it.
  Flat mode compares the files after it reads them and before it parses
  them.
- `install_output` runs after Lake. It validates the path and compares the
  inputs again. It creates a staging file beside the target, which only the
  user can read and write, and copies the executable in blocks, with a
  check for a signal before each block. It gives the staging file the mode
  of the executable, flushes it to the disk and repeats the two checks.
  Then it renames the staging file onto the target.
- For an output that is a symbolic link the target is the file that the
  link names. The link stays, and the driver fails when the link names
  another file after the copy.
- A guard removes the staging file when a step fails. The name of a staging
  file holds the process number and a counter, and the driver tries the
  next name when one exists.

[The output of `build`](../guide/cli.md#the-output-of-build) gives the rules
that these checks enforce.

Tests:

- `tests/driver_hardening.rs::output_symlink_is_written_through_to_its_target`,
  `staging_names_are_retried_and_output_directory_is_probed_first` and
  `existing_output_is_replaced_with_new_bytes_and_mode`;
- `tests/driver_issues.rs::output_cannot_replace_any_input_or_alias`;
- `tests/packages.rs::all_manifests_and_module_sources_are_protected_from_output`;
- `tests/input_safety.rs::special_outputs_and_their_symlinks_are_preserved`;
- `tests/compiler.rs::failed_compilation_preserves_existing_output` and
  `native_toolchain_failure_preserves_existing_output`.

## Subprocesses and signals

`src/process.rs` runs every child process: the kernel, `lean`, Lake and the
checker of `audit-lean`.

`process::install` registers a handler for SIGINT, SIGTERM, SIGHUP and
SIGQUIT. The handler stores the number of the signal and does nothing else.
`process::check` reads the number. The driver calls it where it can wait:
before each block that it reads from an input, while it waits for a lock
and before each block that it copies to the staging file. `capture` reads
the number in each turn of its loop. An interrupted step of `check` or
`build` returns `E_INTERRUPTED`, and the guards remove the temporary
directory and the staging file. An interrupted checker of `audit-lean`
returns `E_LEAN_AUDIT`. `process::exit_code` gives 128 plus the number of
the signal.

`process::capture` runs one child:

- The child gets a process group of its own.
- All three pipes are nonblocking. One loop writes the input, reads both
  output streams and waits for the child, with a bound on the work of each
  turn. The loop sleeps only in a turn that moved no byte.
- `Retention::Complete` keeps every byte of standard output up to a limit,
  and the capture fails beyond the limit. `Retention::Tail` keeps the last
  bytes and counts the bytes that it drops. Standard error always keeps a
  tail.
- After a signal the loop sends the same signal to the process group. It
  sends SIGKILL after `TERM_GRACE` and stops waiting after `KILL_GRACE`.
- After the child exits, the loop goes on while a pipe is open or a process
  of the group lives. A descendant that holds a pipe, and a descendant that
  lives in the group without one, get `DRAIN_GRACE`. Then the loop ends the
  group in the same way, and the capture fails.
- After the loop reaps the child and finds its group empty, it sends no
  signal to that group number, which the system can give to another group.

A live compiler has no time limit. Only the steps after a signal and after
the exit of the child have one.

Tests:

- the unit tests of `src/process.rs`;
- `tests/driver_issues.rs::interrupted_build_reaps_children_and_removes_temporary_files`,
  `exited_compilers_cannot_leave_pipe_holders_or_silent_descendants` and
  `interrupted_backend_has_no_spawn_failure_or_rebuild_hint`.

## Locks

Lake writes build products into the storage runtime and the numerical
runtime of the kernel root when it compiles a program that requires them.
Two builds that share a root would write the same files.

- `lock_native_packages` takes an exclusive `flock` on the directory
  `native`, and on `numerical` for a numerical program. A program that
  requires no storage runtime takes no lock.
- It sorts the canonical paths and removes a repeated one, so every build
  takes the locks of shared packages in the same order.
- `acquire_lock` tries the lock, sleeps and checks for a signal, so a
  signal interrupts a waiting build.
- On a file system that cannot lock a directory, `lock_file` locks the file
  `.vastitas-build.lock` in the package instead.
- The driver clears the close-on-exec flag of each lock descriptor. Lake and
  its descendants inherit the lock, and the lock holds while one of them
  lives, also after a signal kills the driver.

A generated program takes no lock. The lock excludes other builds of the
driver. It does not exclude a `lake` that a user starts in the same package.

Tests:

- `tests/native_build_concurrency.rs::same_optional_package_serializes_but_independent_roots_do_not`,
  `waiting_for_either_package_is_interruptible_and_failure_releases_locks`,
  `lake_retains_package_lock_after_driver_is_killed` and
  `simultaneous_cold_resource_builds_execute_and_reuse_native_artifacts`;
- the unit test `package_lock_falls_back_to_an_exclusive_lock_file` of
  `src/driver.rs`.

## The proof-audit command

`vastitas audit-lean` is a separate command of the same executable, in
`src/internal_lean_audit.rs`. It runs the checker `nanoda_bin` of the pinned
Lean toolchain on an export of Lean proofs, under `process::capture`. It
reads no `.vast` source and starts no kernel, and its result is no part of
the acceptance of a program. [Appendix A](../guide/cli.md) describes the
command, and
[Independent internal Lean export audit](../verification.md#independent-internal-lean-export-audit-v010-gate)
states what it establishes. `tests/internal_lean_audit.rs` tests it.

## History

- The build identity of the kernel and the check of the Lean version before
  Lake come from [#550](https://github.com/MGYamada/Vastitas/issues/550).
  [#724](https://github.com/MGYamada/Vastitas/issues/724) added
  `compiler-limits.json` to the digest and the digested files to the inputs
  of the kernel executable.
- The comparison of the runtime inputs comes from
  [#679](https://github.com/MGYamada/Vastitas/issues/679), and the storage
  requirement of a resource entry from
  [#681](https://github.com/MGYamada/Vastitas/issues/681).
- [#519](https://github.com/MGYamada/Vastitas/issues/519) made the driver
  write through an output that is a symbolic link.
  [#522](https://github.com/MGYamada/Vastitas/issues/522) gave the generated
  Lake configurations the escapes of their own syntax.
- [#564](https://github.com/MGYamada/Vastitas/issues/564) covers the private
  build directory, the staging names, the bounds on captured output, the
  lock file and the byte-exact match of module names.
- [#680](https://github.com/MGYamada/Vastitas/issues/680) and
  [#718](https://github.com/MGYamada/Vastitas/issues/718) cover the names of
  control characters in paths, manifests and messages.
- [#704](https://github.com/MGYamada/Vastitas/issues/704) gave the two
  bounds on resource functions a place at the function.
