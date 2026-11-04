# Storage and resource programs

Everything so far has been pure: values without memory. Numerical work needs
buffers. Vastitas makes every allocation, borrow, write and release explicit,
and checks them before generating code. This is how the language pursues its
**Fast like C** goal: a resource program's buffers are never copied or
allocated behind your back, and each buffer's lifetime is written in the
source.

Resource programs need manifest mode.

## Resource functions

A `resource fn` is a sequence of storage statements followed by a pure
`value { ... }` block. The library package in
[`examples/packages/storage`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/storage)
allocates, initializes and checks a buffer:

```vast
// buffers/src/operations/mod.vast
pub resource fn make() returns (data: Owned<F64, 8> initialized [layout(8, 2, 2, 4, false)]) -> Unit {
    allocate data: F64[8];
    borrow output = write(data, layout(8, 2, 2, 4, false));
    fill(output, f64_bits(4613937818241073152));
    release(output);
    value { () }
}

pub resource fn inspect(input: Read<F64, 2, 2>) -> Unit {
    expect(input, 0, 0, f64_bits(4613937818241073152));
    value { () }
}

pub resource fn round_trip(data: Owned<F64, 8> initialized [layout(8, 2, 2, 4, false)])
    returns (data: Owned<F64, 8> initialized [layout(8, 2, 2, 4, false)]) -> Unit {
    value { () }
}
```

Read `make` line by line:

1. `allocate data: F64[8];` creates an owner of eight uninitialized `F64` cells.
2. `borrow output = write(data, layout(...));` takes a write loan on a 2×2 view.
3. `fill(output, ...)` initializes every cell of that view.
4. `release(output);` returns the loan, so `data` is usable again.
5. `returns (data: Owned<...> initialized [...])` hands the owner to the caller
   and promises that this exact region is initialized.

`layout(offset, rows, columns, leading, transposed)` gives a byte offset, the
logical shape, an element leading dimension and a transpose flag. Here the view
starts 8 bytes in and its rows are 4 elements apart.

## Calling resource functions

The application package receives the owner, lends it out and finally drops it:

```vast
// app/src/main.vast
use buffers::make;
use buffers::inspect;
use buffers::round_trip;

generic answer(x) { domain (Int); }
method answer(x: Number) -> Int { 0 }
method answer(x: Int) -> Int { x + 1 }

resource fn main() -> Int {
    call make() -> (data);
    borrow input = read(data, layout(8, 2, 2, 4, false));
    call inspect(input) -> ();
    release(input);
    call round_trip(data) -> (returned);
    borrow check_view = read(returned, layout(8, 2, 2, 4, false));
    call inspect(check_view) -> ();
    release(check_view);
    drop(returned);
    value {
        let increment: Fn<Int, Int> = fn(x: Int) -> Int { x + 1 };
        increment(answer(40))
    }
}
```

```sh
target/debug/vastitas check --manifest-path examples/packages/storage/app/Vastitas.toml
target/debug/vastitas build --manifest-path examples/packages/storage/app/Vastitas.toml -o target/storage-example
./target/storage-example
```

The program prints `42`, computed by ordinary dispatch and a lambda in the
`value` block. `call round_trip(data) -> (returned)` consumes `data`, so using
`data` after that point is rejected. Every owner must be dropped or returned,
and every loan released, before the function ends.

## The statements

| Statement | Meaning |
| --- | --- |
| `allocate data: F64[8];` | Allocate an uninitialized owner; `Complex<F64>` also works |
| `move data -> next;` | Transfer an unborrowed owner; `data` is revoked |
| `borrow view = read(data, layout(...));` | Borrow, also `write` and `read_write` |
| `release(view);` | Return a loan that has no children |
| `drop(data);` | Free an unborrowed owner |
| `transpose(view);` | Swap the logical axes without copying or conjugating |
| `fill(view, payload);` | Fill the writable view |
| `store(view, row, column, payload);` | Initialize one cell |
| `expect(view, row, column, payload);` | Assert a cell's exact bits at run time |
| `copy(input, output);` | Copy between compatible views into an existing destination |
| `call path(arguments) -> (owners);` | Call a resource function and receive its owners |
| `let n: Nat = value { expression };` | Compute a checked pure scalar mid-body |
| `if flag { ... } else { ... }` | Run one arm; both arms are checked and joined |

Borrowed parameters are `Read<S, rows, columns>`, `Write<...>` or
`ReadWrite<...>`. They receive a child loan of the caller's actual view,
including its offset, padding and transpose. Two read arguments may alias, and
parameter names never prove that a writer is separate from anything else.

## Exact floating-point payloads

`f64(value)` and `complex(real, imaginary)` take **exact** binary64 values.
Hexadecimal makes the binary exponent explicit:

```vast
fill(output, f64(0x1.8p1));                      // 3.0
store(output, 0, 0, f64(-0x1p-2));               // -0.25
fill(complex_output, complex(0x1.8p0, -0x1p1));  // 1.5 - 2i
```

There is no rounding on acceptance: `f64(0.1)` is rejected and the diagnostic
shows the two neighbouring binary64 values. Negative zero, infinities and NaN
payloads use `f64_bits(bits)` or `complex_bits(real_bits, imaginary_bits)`, as
in the example above. These are storage payloads only. Pure code still has no
floating-point values or arithmetic.

## Runtime shapes

So far every size is static. The runtime-shape profile lets a resource function
take whole caller-owned maps whose extents are immutable runtime integers.
Each call is checked against the caller's frame before any write.
[Runtime extents and caller-owned maps](../storage/resource-programs.md#runtime-shapes)
describes the interface.

> **What is checked.** Lean checks ownership, loans, layouts, byte-level
> initialization, aliases and branch joins for every resource body, and the
> native runtime repeats its physical preflight before writes. The full
> contract is in [Resource programs](../storage/resource-programs.md); the
> design and its performance obligations are in
> [Storage, ownership and residual retention](../storage-ownership.md). Equivalent-C
> performance acceptance is still open; see the
> [Stage 1 delivery record](../stage1-completion.md#stage-2-or-later-performance-acceptance).
