# Build and run your first program

From the repository root, use the pinned Rust and Lean toolchains and a host C
compiler. On macOS, install the Xcode Command Line Tools. The compiler uses
Rust 1.99.1 and Lean 4.35.0. Build the kernel before invoking the driver.

```sh
lake -d lean-kernel build vastitas-kernel
cargo build --locked
target/debug/vastitas check examples/pointed.vast
target/debug/vastitas build examples/pointed.vast -o target/pointed
./target/pointed
```

The executable prints `42`. The example returns a geometric object together
with a point on it. When the caller opens the package, the checker still
knows which object the point belongs to.
[Example source](https://github.com/MGYamada/Vastitas/blob/main/examples/pointed.vast) · [Geometric indices](../indexed-source.md)

Try a rejection in a scratch source file. This declares an integer result and
returns a Boolean.

```sh
printf '%s\n' 'fn main() -> Int { true }' > target/manual-bad.vast
target/debug/vastitas check target/manual-bad.vast
```

The process exits unsuccessfully with `E_TYPE`. For multi-file programs,
continue with [packages and the standard library](stdlib.md). The
[command-line guide](cli.md) explains library inputs, native output and
development overrides.

## Pass an independent function

```vast
fn invoke(f: Fn<Int, Int>, x: Int) -> Int { f(x) }
fn main() -> Int {
    let increment: Fn<Int, Int> = fn(x: Int) -> Int { x + 1 };
    invoke(increment, 41)
}
```

Function types use `Fn<Int, Int>`, `Fn<(Int, Int), Int>`, `Fn<(), Int>`,
or `Fn<Unit, Int>`; the last two distinguish zero arguments from one Unit
argument. Lambdas have explicit parameter/result types and cannot capture
outer locals. Named functions can also be passed, aliased, returned and called.
Lean resolves calls to a single static target and erases function values.
Generic families remain declarations, usable through ordinary wrappers.
See [Stage 1b](../stage1b.md) for the contract and proof boundary.

```sh
cargo run --locked -- check examples/functions.vast
cargo run --locked -- build examples/functions.vast -o target/functions
./target/functions
# 42
```

## Construct and project a pair

Ordinary functions and selected methods support homogeneous `Pair<Nat>` / `Pair<Int>` values
through `pair`, `pair_first`, and `pair_second`. Their elements are inferred
without conversion; Pair is excluded from dispatch keys and Fn contracts.
See [the Pair contract](../stage1b.md#homogeneous-data-pairs) and
[native example](https://github.com/MGYamada/Vastitas/blob/main/examples/pairs.vast). The stdlib's four-key `promote` preserves
Nat/Nat as `Pair<Nat>` and embeds mixed keys into `Pair<Int>` explicitly. See the
[promotion contract and package usage](https://github.com/MGYamada/Vastitas/blob/main/stdlib/README.md#explicit-promotion).
The [numerical proof contract](../stage1a.md#promotion) covers the actual checked
stdlib bodies. The [Stage 1 record](../stage1-completion.md) covers the integrated finite language.
