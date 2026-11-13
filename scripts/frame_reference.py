"""Exact two-dimensional reference model of ordered frames for the Stage 4 runtime.

This is a Python reference model, not a Lean proof and not the compiler's
implementation. It models the frames of ADR 0001 §11 on the real plane: a
frame is a 2 by 2 matrix P of polynomials in the coordinates (x, y) whose
column j is frame vector j in the coordinate frame, valid when a two-sided
inverse Q exists as a polynomial identity. It computes, independently of the
kernel:

- frame arrays: Q(p) v for a vector and P(p)^T a for a covector at p, and the
  decoding maps P(p) a and Q(p)^T a;
- transitions Q_b'(p) P_b(p) between two frames of one object;
- map arrays Q_c(F(p)) J(p) P_b(p) of a polynomial map F, from the Jacobian J
  (the kernel takes the rows from reverse runs instead);
- apply, coapply, compose and the pairing of arrays;
- Gram matrices P(p)^T G P(p) of a constant metric G in a frame.

`fixture()` serializes fixed inputs and results to `tests/fixtures/frames.json`.
The kernel regression `VastitasAlgebraTest.FrameReferenceRegression` checks
that the kernel's frame runtime and frame checks compute the same values.
Polynomials use the encoding of `algebra-bases.json`: arity-2 terms
`[exponents, "num/den"]` in strictly decreasing degLex order, coordinate 0
most significant. Matrices are lists of rows. A frame records both its
`columns` (as a program writes them) and the `rows` of P, so that a
transposition in a reader shows up. An invalid frame records the reason code
instead of its inverse.

Run `python3 scripts/frame_reference.py --check` to compare the fixture with
the model, or `--write` to regenerate it.
"""

import argparse
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

import metric_free_reference as mf
from affine_algebra_reference import encode_rational, key

FIXTURE = Path(__file__).resolve().parent.parent / "tests" / "fixtures" / "frames.json"
ARITY = 2
X, Y, ZERO = mf.X, mf.Y, mf.ZERO
ONE = ZERO + 1


class Invalid(ValueError):
    """A frame or input that the model rejects, with a reason code."""

    def __init__(self, code):
        super().__init__(code)
        self.code = code


# --- Polynomial matrices --------------------------------------------------------

def const(value):
    return ZERO + Q(value)


def poly(value):
    """A model polynomial from an int, a Fraction or a model polynomial."""
    if type(value) in (int, Q):
        return const(value)
    mf.audit_polynomial(value)
    return value


def poly_matrix(rows):
    return tuple(tuple(poly(entry) for entry in row) for row in rows)


def from_columns(columns):
    """P from its columns: column j of P is columns[j]."""
    n = len(columns)
    if any(len(column) != n for column in columns):
        raise Invalid("WRONG_SIZE")
    return tuple(tuple(poly(columns[j][i]) for j in range(n)) for i in range(n))


def poly_mul(left, right):
    n, inner, m = len(left), len(right), len(right[0]) if right else 0
    return tuple(tuple(sum((left[i][k] * right[k][j] for k in range(inner)), ZERO)
                       for j in range(m)) for i in range(n))


def poly_identity(n):
    return tuple(tuple(ONE if i == j else ZERO for j in range(n)) for i in range(n))


def is_constant(p):
    return all(sum(powers) == 0 for powers, _ in p.terms)


def constant_value(p):
    return mf.evaluate(p, (0, 0))


def evaluate(rows, point):
    return tuple(tuple(mf.evaluate(entry, point) for entry in row) for row in rows)


# --- Rational matrices ---------------------------------------------------------

def mat_mul(left, right):
    m = len(right[0]) if right else 0
    return tuple(tuple(sum((left[i][k] * right[k][j] for k in range(len(right))), Q(0))
                       for j in range(m)) for i in range(len(left)))


def mat_vec(matrix, vector):
    return tuple(sum((a * b for a, b in zip(row, vector)), Q(0)) for row in matrix)


def transpose(matrix):
    return tuple(zip(*matrix))


def identity(n):
    return tuple(tuple(Q(int(i == j)) for j in range(n)) for i in range(n))


def inverse(matrix):
    """The exact inverse by Gauss-Jordan elimination, or SINGULAR."""
    n = len(matrix)
    rows = [list(row) + list(unit) for row, unit in zip(matrix, identity(n))]
    for column in range(n):
        pivot = next((r for r in range(column, n) if rows[r][column] != 0), None)
        if pivot is None:
            raise Invalid("SINGULAR")
        rows[column], rows[pivot] = rows[pivot], rows[column]
        scale = rows[column][column]
        rows[column] = [value / scale for value in rows[column]]
        for r in range(n):
            if r != column and rows[r][column] != 0:
                factor = rows[r][column]
                rows[r] = [a - factor * b for a, b in zip(rows[r], rows[column])]
    return tuple(tuple(row[n:]) for row in rows)


# --- Frames ----------------------------------------------------------------------

class Frame:
    """A checked frame: P and its two-sided inverse Q, as polynomial matrices."""

    def __init__(self, name, columns, declared_inverse=None):
        self.name = name
        self.columns = columns
        self.matrix = from_columns(columns)
        n = len(self.matrix)
        constant = all(is_constant(entry) for row in self.matrix for entry in row)
        if constant:
            if declared_inverse is not None:
                raise Invalid("INVERSE_OF_CONSTANT")
            values = tuple(tuple(constant_value(e) for e in row) for row in self.matrix)
            self.inverse = poly_matrix(inverse(values))
        else:
            if declared_inverse is None:
                raise Invalid("MISSING_INVERSE")
            self.inverse = from_columns(declared_inverse)
            if (poly_mul(self.matrix, self.inverse) != poly_identity(n)
                    or poly_mul(self.inverse, self.matrix) != poly_identity(n)):
                raise Invalid("WRONG_INVERSE")
        self.dimension = n

    def at(self, point):
        return evaluate(self.matrix, point)

    def inverse_at(self, point):
        return evaluate(self.inverse, point)


def encode(frame, variance, point, components):
    if variance == "tangent":
        return mat_vec(frame.inverse_at(point), components)
    return mat_vec(transpose(frame.at(point)), components)


def decode(frame, variance, point, array):
    if variance == "tangent":
        return mat_vec(frame.at(point), array)
    return mat_vec(transpose(frame.inverse_at(point)), array)


def transition(source, target, point):
    """Q_target(p) P_source(p): source-frame coordinates to target-frame ones."""
    return mat_mul(target.inverse_at(point), source.at(point))


def apply_map(images, point):
    return tuple(mf.evaluate(p, point) for p in images)


def jacobian(images, point):
    return tuple(tuple(mf.evaluate(p.derivative(i), point) for i in range(ARITY)) for p in images)


def frame_matrix(images, point, source, target):
    """Q_target(F(p)) J(p) P_source(p), from the Jacobian."""
    return mat_mul(mat_mul(target.inverse_at(apply_map(images, point)), jacobian(images, point)),
                   source.at(point))


def compose_maps(after, before):
    return tuple(mf.substitute(p, before) for p in after)


def pairing(covector, vector):
    return sum((a * b for a, b in zip(covector, vector)), Q(0))


def gram(frame, metric, point):
    p = frame.at(point)
    return mat_mul(mat_mul(transpose(p), metric), p)


# --- Fixed inputs -----------------------------------------------------------------

COORDINATES = ((1, 0), (0, 1))
# Nonorthogonal constant frames with P != P^T and det not in {1, -1}.
B = ((1, 0), (1, 2))            # P = [[1, 1], [0, 2]], det 2
B_PRIME = ((2, 1), (-1, 3))     # P = [[2, -1], [1, 3]], det 7
C = ((1, 1), (0, 3))            # P = [[1, 0], [1, 3]], det 3
C_PRIME = ((1, -1), (2, 1))     # P = [[1, 2], [-1, 1]], det 3
# Polynomial frames with a constant determinant and a polynomial inverse.
R = ((1, 0), (X, 2))            # P = [[1, x], [0, 2]], det 2
R_INVERSE = ((1, 0), (Q(-1, 2) * X, Q(1, 2)))
S = ((1, Y), (0, 1))            # P = [[1, 0], [y, 1]], det 1
S_INVERSE = ((1, -Y), (0, 1))

SQUARE = (X ** 2, X * Y + Y)
SHEAR = (X + Y, Y)
RANK_ONE = (X + Y, 2 * X + 2 * Y)

POINTS = ((3, -1), (Q(1, 2), 2), (0, 0))
METRIC = ((2, 1), (1, 3))
LORENTZ = ((1, 0), (0, -1))


def frames():
    return {
        "coordinates": Frame("coordinates", COORDINATES),
        "b": Frame("b", B),
        "b'": Frame("b'", B_PRIME),
        "c": Frame("c", C),
        "c'": Frame("c'", C_PRIME),
        "r": Frame("r", R, R_INVERSE),
        "s": Frame("s", S, S_INVERSE),
    }


INVALID_FRAMES = (
    ("singular constant frame", ((1, 2), (2, 4)), None),
    ("inverse declared for a constant frame", B, ((1, 0), (Q(-1, 2), Q(1, 2)))),
    ("polynomial frame without an inverse", R, None),
    ("wrong polynomial inverse", R, ((1, 0), (Q(1, 2) * X, Q(1, 2)))),
    ("singular at the origin", ((X, 0), (0, 1)), ((1, 0), (0, 1))),
    ("wrong number of entries", ((1, 0), (1,)), None),
)


# --- Encoding --------------------------------------------------------------------

def encode_poly(value):
    mf.audit_polynomial(value)
    terms = [(powers[:ARITY], coefficient) for powers, coefficient in value.terms]
    return [[list(m), encode_rational(c)] for m, c in sorted(terms, key=lambda t: key(t[0]), reverse=True)]


def encode_vector(values):
    return [encode_rational(Q(value)) for value in values]


def encode_matrix(rows):
    return [encode_vector(row) for row in rows]


def encode_poly_matrix(rows):
    return [[encode_poly(poly(entry)) for entry in row] for row in rows]


def frame_case(frame):
    return {
        "name": frame.name,
        "columns": encode_poly_matrix(frame.columns),
        "rows": encode_poly_matrix(frame.matrix),
        "inverse": encode_poly_matrix(frame.inverse),
    }


def invalid_case(name, columns, declared):
    try:
        Frame(name, columns, declared)
    except Invalid as error:
        code = error.code
    else:
        raise AssertionError(f"{name} was accepted")
    entry = {"name": name, "columns": [[encode_poly(poly(e)) for e in column] for column in columns],
             "declaredInverse": None if declared is None else encode_poly_matrix(declared),
             "error": code}
    return entry


def encoding_cases(table):
    cases = []
    for frame_name in ("b", "b'", "r", "s"):
        frame = table[frame_name]
        for point in POINTS:
            for variance, components in (("tangent", (3, Q(-1, 2))), ("cotangent", (Q(2, 3), 5))):
                array = encode(frame, variance, point, components)
                assert decode(frame, variance, point, array) == tuple(Q(c) for c in components)
                cases.append({"frame": frame_name, "variance": variance,
                              "point": encode_vector(point), "components": encode_vector(components),
                              "expected": encode_vector(array)})
    return cases


def transition_cases(table):
    cases = []
    for source, target in (("b", "b'"), ("b'", "b"), ("b", "b"), ("r", "s"), ("r", "b"), ("coordinates", "r")):
        for point in POINTS:
            cases.append({"source": source, "target": target, "point": encode_vector(point),
                          "expected": encode_matrix(transition(table[source], table[target], point))})
    return cases


def matrix_cases(table):
    cases = []
    for name, images in (("square", SQUARE), ("shear", SHEAR), ("rank one", RANK_ONE),
                         ("square after shear", compose_maps(SQUARE, SHEAR))):
        for source, target in (("b", "c"), ("b'", "c'"), ("r", "s"), ("coordinates", "coordinates")):
            for point in POINTS:
                cases.append({"map": name, "images": [encode_poly(p) for p in images],
                              "source": source, "target": target, "point": encode_vector(point),
                              "expected": encode_matrix(frame_matrix(images, point, table[source], table[target]))})
    return cases


def gram_cases(table):
    cases = []
    for name, metric in (("positive", METRIC), ("lorentz", LORENTZ)):
        values = tuple(tuple(Q(v) for v in row) for row in metric)
        for frame_name in ("coordinates", "b", "r"):
            for point in POINTS:
                cases.append({"metric": name, "gram": encode_matrix(values), "frame": frame_name,
                              "point": encode_vector(point),
                              "expected": encode_matrix(gram(table[frame_name], values, point))})
    return cases


def fixture():
    table = frames()
    return {
        "order": "degLex",
        "frames": [frame_case(frame) for frame in table.values()],
        "invalidFrames": [invalid_case(*case) for case in INVALID_FRAMES],
        "encodings": encoding_cases(table),
        "transitions": transition_cases(table),
        "matrices": matrix_cases(table),
        "grams": gram_cases(table),
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--check", action="store_true")
    group.add_argument("--write", action="store_true")
    args = parser.parse_args(argv)
    expected = json.dumps(fixture(), indent=2) + "\n"
    if args.write:
        FIXTURE.write_text(expected)
        return 0
    if not FIXTURE.is_file() or FIXTURE.read_text() != expected:
        print(f"{FIXTURE} differs from the reference model", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
