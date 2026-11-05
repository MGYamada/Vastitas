# Numerical maps, GEMM, metrics and tensor networks

[Chapter 10](storage.md) gave you buffers and loans. This chapter gives those
buffers a mathematical meaning: a coordinate matrix becomes a linear map between
nominal spaces, in named bases. Then the compiler can check that a product
makes sense before it calls BLAS.

All numerical statements live inside `resource fn` bodies. Builds of programs
that execute GEMM or diagonal Hermitian pairing need sequential LP64 OpenBLAS
0.3.34; `check` does not.

## Coefficient profiles

A profile declares what the coefficients mean mathematically. Each numerical
example package has its own profile module. This excerpt shows the smooth
profiles of the GEMM example:

```vast
// examples/packages/numerical/numerical/src/profiles/mod.vast (first part)
pub indexed marker RealCoefficients;
pub indexed marker ComplexCoefficients;

// The geometric smooth base is real even for complex linear fibers.
pub indexed implementation SmoothScalar(RealCoefficients, scalar_base(smooth, real)) capabilities();
pub indexed global SmoothBase(SmoothScalar);
pub indexed implementation RealSmooth(RealCoefficients, linear_descriptor(SmoothBase, real)) capabilities();
pub indexed implementation ComplexSmooth(ComplexCoefficients, linear_descriptor(SmoothBase, complex)) capabilities();
// ... the file continues with the corresponding scheme-based profiles ...
```

The storage scalars `F64` and `Complex<F64>` are binary64 **realizations** of
these ideal coefficients. Neither is an exact field.

## Spaces, bases and maps

Inside a resource function, with three live loans of matching shapes, the real
half of
[`examples/packages/numerical/numerical`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/numerical/numerical)
multiplies two matrices:

```vast
space u = linear(super::profiles::RealSmooth, 2);
space v = linear(super::profiles::RealSmooth, 3);
space w = linear(super::profiles::RealSmooth, 2);
basis bu = basis(u);
basis bv = basis(v);
basis bw = basis(w);
// ... allocate and initialize a (2x3), b (3x2) and c (2x2) ...
map left = view(input_a, bv, bw);
map right = view(input_b, bu, bv);
map destination = view(output, bu, bw);
gemm(left, right, destination, overwrite, NativeFast);
```

- `space` makes a **fresh** nominal space. Two spaces of dimension 2 are still
  different spaces.
- `basis` introduces a basis tied to one space.
- `map left = view(input_a, bv, bw)` reads the loan `input_a` as a map from `v`
  to `w` in those bases.
- `gemm(left, right, destination, overwrite, NativeFast)` requires
  `left: V → W`, `right: U → V` and `destination: U → W`, with matching bases,
  and then multiplies. `accumulate` adds to the destination instead.

The real product is `[[1,2,3],[4,5,6]] * [[7,8],[9,10],[11,12]] = [[58,64],[139,154]]`.
The example checks every output cell with `expect`, accumulates a second product
into the same destination and checks again. The complex half computes
`[[1,i,2],[0,1,-i]] * [[1,0],[2,1],[0,i]] = [[1+2i,3i],[2,2]]` with no implicit
conjugation.

```sh
cargo run --locked -- check --manifest-path examples/packages/numerical/numerical/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/numerical/numerical/Vastitas.toml \
  --openblas-prefix /path/to/openblas-0.3.34 -o target/numerical-example
./target/numerical-example
```

On Linux, add `--native-cc cc`. The prefix must contain the pinned OpenBLAS
headers and static archive; see
[the adapter contract](../linalg/maps-and-gemm.md#numerical-adapter). A program
whose checked entry runs neither GEMM nor diagonal Hermitian pairing never
links OpenBLAS.

## Duals, conjugates, adjoints and metrics

Transposes and conjugations are never implicit. You derive them explicitly, and
each one has its own nominal space and basis.
[`examples/packages/numerical/linear-transforms`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/numerical/linear-transforms/src/main.vast)
declares them:

```vast
space v = linear(profiles::ComplexSmooth, 1);
space w = linear(profiles::ComplexSmooth, 1);
basis bv = basis(v);
basis bw = basis(w);
involution sigma = canonical(v);
space vd = dual(v);
space wd = dual(w);
basis bvd = derived(bv, vd);
basis bwd = derived(bw, wd);
space vc = conjugate(v, sigma);
space wc = conjugate(w, sigma);
basis bvc = derived(bv, vc);
basis bwc = derived(bw, wc);
metric hv = orthonormal(bv, sigma);
metric hw = diagonal(bw, sigma, [1]);
```

A map `a: V@bv → W@bw` then has three different transforms:

| Operation | Endpoints | Coordinates |
| --- | --- | --- |
| `dual(a, bwd, bvd)` | `W∨@bwd → V∨@bvd` | Transpose |
| `conjugate(a, bvc, bwc, sigma)` | `Conj<V>@bvc → Conj<W>@bwc` | Conjugate each entry |
| `adjoint(a, hv, hw)` | `W@bw → V@bv` | Conjugate transpose, for the declared orthonormal metrics |

The example distinguishes `dual([i]) = [i]` from `adjoint([i]) = [-i]` and
`conjugate([i]) = [-i]`. A transform is a checked read child loan of the
original map: no copy and no allocation. Resource functions accept these
nominal values as typed parameters:

```vast
resource fn adjoint_into(v: Space<profiles::ComplexSmooth, 1>, w: Space<profiles::ComplexSmooth, 1>,
    bv: Basis<v>, bw: Basis<w>, sigma: Involution<v>, hv: OrthonormalMetric<bv, sigma>, hw: OrthonormalMetric<bw, sigma>,
    input: ReadMap<bv, bw>, identity: ReadMap<bw, bw>, output: WriteMap<bw, bv> initializes) -> Unit {
    map transformed = adjoint(input, hv, hw);
    call multiply(w, v, bw, bv, transformed, identity, output) -> ();
    release(transformed);
    value { () }
}
```

For diagonal metrics that are not orthonormal, the adjoint is not a view.
Explicit statements materialize it into a caller's destination and evaluate
Hermitian forms with caller scratch; see
[Explicit diagonal metrics](../linalg/transforms-and-metrics.md#diagonal-metrics).

## Tensor networks

A `contract` block wires map occurrences together and writes the result into a
destination. [`examples/packages/tensor/finite_network`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/tensor/finite_network)
expresses the same product as a two-node network:

```vast
contract(destination, NativeFast) {
    occurrence a = left;
    occurrence b = right;
    edge(a.input, b.output);
    input(b.input);
    output(a.output);
}
```

`a.input` is the dual factor of the source of `left`, and `a.output` its target
factor. The edge contracts `V∨ ⊗ V → K`. The boundaries keep the uncontracted
input of `b` and output of `a`, which must match the destination's objects and
bases exactly. Contraction inserts no conjugation, metric or basis change.

```sh
cargo run --locked -- check --manifest-path examples/packages/tensor/finite_network/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/tensor/finite_network/Vastitas.toml \
  --openblas-prefix /path/to/openblas-0.3.34 -o target/finite-network
./target/finite-network
```

The program prints `42` after its coordinate checks. Larger networks use
explicit execution plans:

- [Finite rank-three contraction and explicit packing](../linalg/networks-and-packing.md#tensor-packing)
- [Bounded finite contraction trees](../linalg/networks-and-packing.md#contraction-trees)
- [Checked reuse of packed tensor values](../linalg/networks-and-packing.md#cached-packing)

> **What is checked.** Lean resolves every space, basis and metric itself; the
> wire cannot supply a checked identity or a product receipt. Raw dimensions
> never authorize a product. The native adapter rechecks layouts and aliases
> before writing and then calls pinned OpenBLAS. Floating-point field laws,
> numerical error bounds and source-to-native refinement are not proved. See
> [Numerical maps, ownership and GEMM](../linalg/maps-and-gemm.md#numerical-adapter--responsibilities-along-the-implemented-path)
> and the [proof boundary](../verification.md#what-is-outside-these-claims).
