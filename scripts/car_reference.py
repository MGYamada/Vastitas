"""Exact one/two-mode CAR and ordinary-spin observations for issue #246.

Standard library only, over Q(i) with a specified embedding into C. Every
exchange coefficient comes from graph_reference, including the Jordan-Wigner
prefix. Matrix observations NEVER authorize a Graph rewrite or certify Core.
This is neither a general Clifford calculator nor a production proof provider.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from types import MappingProxyType
from typing import TypeAlias

import graph_reference as graph

Rejected = graph.Rejected


def rational(value: int | Fraction) -> Fraction:
    if type(value) not in (int, Fraction):
        raise Rejected("exact int/Fraction required; no Float, complex or Bool coercion")
    return Fraction(value)


@dataclass(frozen=True)
class Qi:
    """a + b*i, i^2 = -1; no Python floating-point complex numbers."""

    real: Fraction = Fraction(0)
    imag: Fraction = Fraction(0)

    def __post_init__(self):
        object.__setattr__(self, "real", rational(self.real))
        object.__setattr__(self, "imag", rational(self.imag))

    def __add__(self, other: Qi) -> Qi:
        if type(other) is not Qi:
            return NotImplemented
        return Qi(self.real + other.real, self.imag + other.imag)

    def __neg__(self) -> Qi:
        return Qi(-self.real, -self.imag)

    def __sub__(self, other: Qi) -> Qi:
        return self + (-other)

    def __mul__(self, other: Qi) -> Qi:
        if type(other) is not Qi:
            return NotImplemented
        return Qi(self.real * other.real - self.imag * other.imag,
                  self.real * other.imag + self.imag * other.real)

    def conjugate(self) -> Qi:
        return Qi(self.real, -self.imag)

    def __truediv__(self, other: Qi) -> Qi:
        norm = other.real ** 2 + other.imag ** 2
        if not norm:
            raise ZeroDivisionError("zero in Q(i)")
        numerator = self * other.conjugate()
        return Qi(numerator.real / norm, numerator.imag / norm)


ZERO, ONE, I = Qi(), Qi(1), Qi(0, 1)
Matrix: TypeAlias = tuple[tuple[Qi, ...], ...]


def matrix(rows) -> Matrix:
    result = tuple(tuple(x if type(x) is Qi else Qi(x) for x in row) for row in rows)
    audit_matrix(result)
    return result


def audit_matrix(a: Matrix) -> None:
    if (type(a) is not tuple or not a or
            any(type(row) is not tuple or len(row) != len(a) for row in a) or
            any(type(x) is not Qi for row in a for x in row)):
        raise Rejected("immutable square matrix over Q(i) required")


def identity(n: int) -> Matrix:
    return matrix([[int(i == j) for j in range(n)] for i in range(n)])


def scale(s: Qi, a: Matrix) -> Matrix:
    return matrix([[s * x for x in row] for row in a])


def add(a: Matrix, b: Matrix) -> Matrix:
    audit_matrix(a)
    audit_matrix(b)
    if len(a) != len(b):
        raise Rejected("matrix dimensions differ")
    return matrix([[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)])


def mul(a: Matrix, b: Matrix) -> Matrix:
    audit_matrix(a)
    audit_matrix(b)
    if len(a) != len(b):
        raise Rejected("matrix dimensions differ")
    n = len(a)
    return matrix([[sum((a[i][k] * b[k][j] for k in range(n)), ZERO)
                    for j in range(n)] for i in range(n)])


def kron(a: Matrix, b: Matrix) -> Matrix:
    """Coordinate Kronecker product, not a selected mathematical tensor method."""
    audit_matrix(a)
    audit_matrix(b)
    return matrix([[a[i][j] * b[k][l] for j in range(len(a)) for l in range(len(b))]
                   for i in range(len(a)) for k in range(len(b))])


def conjugate_transpose(a: Matrix) -> Matrix:
    """Coordinate operation; operator adjoint additionally requires its profile."""
    audit_matrix(a)
    return matrix([[a[j][i].conjugate() for j in range(len(a))] for i in range(len(a))])


ID2 = identity(2)
R = matrix([[0, 1], [0, 0]])
Z = matrix([[1, 0], [0, -1]])
X = matrix([[0, 1], [1, 0]])
Y = matrix([[0, -I], [I, 0]])


@dataclass(frozen=True)
class AdjointProfile:
    profile_id: str
    coefficient_id: str
    involution_id: str
    inner_product_id: str


@dataclass(frozen=True)
class Model:
    """Closed named fixture identity, not resolver IDs or verified law evidence."""

    model_id: str
    owner_id: str
    implementation_revision: str
    carrier_id: str
    interpretation_id: str
    kind: str
    sites: int
    coefficient_id: str
    tensor_interpretation_id: str
    complex_embedding: str
    crossing_scalar_embedding: str
    tensor_profile: graph.ProfileKey
    basis: tuple[tuple[int, ...], ...]
    local_basis_parity: tuple[int, int]
    basis_parity: tuple[int, ...]
    adjoint_profile: AdjointProfile


def _model(kind: str, sites: int) -> Model:
    name = f"fixture-only:{kind}:{sites}"
    basis = tuple(product((0, 1), repeat=sites))
    local_parity = (0, 1) if kind == "CAR" else (0, 0)
    return Model(
        name, "fixture-owner:car-reference", "fixture-impl:1", f"{name}:carrier",
        "occupation-Fock" if kind == "CAR" else "independent-spin-sites",
        kind, sites, "QQ(i)",
        "fixture-only:SuperVec_QQ(i):Koszul" if kind == "CAR" else "fixture-only:Vec_QQ(i):ordinary",
        "QQ(i)->CC: i maps to +sqrt(-1)",
        "QQ->QQ(i): a maps to (a,0)",
        graph.FIXTURES["symmetric_sign" if kind == "CAR" else "symmetric_one"].key,
        basis, local_parity, tuple(sum(local_parity[x] for x in b) % 2 for b in basis),
        AdjointProfile(f"{name}:dagger", "QQ(i)", "a+bi maps to a-bi",
                       f"{name}:ordered-basis-orthonormal-Gram-I"),
    )


MODELS = MappingProxyType({(kind, n): _model(kind, n)
                          for kind in ("CAR", "spin") for n in (1, 2)})


def parity(value: int) -> int:
    if type(value) is not int or value not in (0, 1):
        raise Rejected("explicit even/odd parity required; unknown is not even")
    return value


def audit_model(model: Model) -> None:
    if type(model) is not Model or type(model.sites) is not int:
        raise Rejected("missing named finite model")
    if type(model.basis) is not tuple or any(
        type(b) is not tuple or any(type(x) is not int for x in b) for b in model.basis
    ):
        raise Rejected("explicit immutable ordered basis required")
    for degrees in (model.local_basis_parity, model.basis_parity):
        if type(degrees) is not tuple:
            raise Rejected("explicit immutable grading required")
        for p in degrees:
            parity(p)
    graph.fixture_profile(model.tensor_profile)
    if type(model.adjoint_profile) is not AdjointProfile or model != MODELS.get((model.kind, model.sites)):
        raise Rejected("unknown/stale model, basis, coefficient, adjoint or tensor profile")


def exchange_word(model: Model, left: int, right: int, *, double=False) -> graph.Word:
    """Degree-line observation only; odd operators are not Graph morphism nodes."""
    audit_model(model)
    source = graph.Boundary(
        f"{model.model_id}:degree-line-presentation", (0, 1),
        (graph.Strand("left", f"{model.carrier_id}:left-degree-line", parity(left)),
         graph.Strand("right", f"{model.carrier_id}:right-degree-line", parity(right))),
    )
    return graph.make_word(model.tensor_profile, source,
                           ((0, graph.Direction.POSITIVE),) * (2 if double else 1))


@dataclass(frozen=True)
class Operator:
    model: Model
    name: str
    degree: int
    entries: Matrix

    def __post_init__(self):
        audit_model(self.model)
        parity(self.degree)
        audit_matrix(self.entries)
        if type(self.name) is not str or not self.name:
            raise Rejected("operator name required")
        if len(self.entries) != len(self.model.basis):
            raise Rejected("matrix and named ordered basis dimensions differ")
        degrees = self.model.basis_parity
        for row, values in enumerate(self.entries):
            for col, value in enumerate(values):
                if value != ZERO and degrees[row] != (degrees[col] + self.degree) % 2:
                    raise Rejected("matrix is not homogeneous for the declared parity")


def embed_local(model: Model, site: int, local: Matrix, degree: int, name: str) -> Operator:
    """Only 1/2 sites. Move a homogeneous operation past the occupied prefix.

    The existing graph evaluator supplies the coefficient. In the CAR model
    this produces R tensor I and Z tensor R, without implementing another sign
    rule. In the spin model it produces ordinary site operators.
    """
    audit_model(model)
    parity(degree)
    audit_matrix(local)
    if type(site) is not int or not 0 <= site < model.sites or len(local) != 2:
        raise Rejected("a two-state local operator and valid site required")
    result = [[ZERO for _ in model.basis] for _ in model.basis]
    for col, state in enumerate(model.basis):
        factor = Fraction(1)
        if site == 1:
            word = exchange_word(model, model.local_basis_parity[state[0]], degree)
            factor = graph.evaluate(word).scalar
        for output in (0, 1):
            target = state[:site] + (output,) + state[site + 1:]
            row = model.basis.index(target)
            result[row][col] = Qi(factor) * local[output][state[site]]
    return Operator(model, name, degree, matrix(result))


def adjoint(operator: Operator, profile: AdjointProfile) -> Operator:
    """Explicit conjugate transpose in the selected orthonormal basis."""
    if type(operator) is not Operator:
        raise Rejected("named operator required")
    if type(profile) is not AdjointProfile or profile != operator.model.adjoint_profile:
        raise Rejected("missing, unsupported or cross-model adjoint profile")
    return Operator(operator.model, f"({operator.name})†", operator.degree,
                    conjugate_transpose(operator.entries))


def annihilators(sites: int) -> tuple[Operator, ...]:
    if type(sites) is not int or sites not in (1, 2):
        raise Rejected("only one/two-mode CAR is supported")
    model = MODELS["CAR", sites]
    return tuple(embed_local(model, site, R, 1, f"c{site + 1}") for site in range(sites))


def spin_x(sites: int = 2) -> tuple[Operator, ...]:
    if type(sites) is not int or sites not in (1, 2):
        raise Rejected("only one/two spin sites are supported")
    model = MODELS["spin", sites]
    return tuple(embed_local(model, site, X, 0, f"X{site + 1}") for site in range(sites))


@dataclass(frozen=True)
class Relation:
    label: str
    lhs: Matrix
    rhs: Matrix

    @property
    def holds(self) -> bool:
        return self.lhs == self.rhs


@dataclass(frozen=True)
class MatrixObservation:
    """Bound to the full operands/model; not a certificate, even when all hold."""

    model: Model
    operators: tuple[Operator, ...]
    adjoints: tuple[Operator, ...]
    relations: tuple[Relation, ...]

    @property
    def all_hold(self) -> bool:
        return all(relation.holds for relation in self.relations)


def _family(operators: tuple[Operator, ...], kind: str) -> Model:
    if (type(operators) is not tuple or not operators or
            any(type(op) is not Operator for op in operators)):
        raise Rejected("immutable nonempty operator family required")
    model = operators[0].model
    audit_model(model)
    if model.kind != kind or len(operators) != model.sites or any(op.model != model for op in operators):
        raise Rejected("family must use one exact named model and its site count")
    return model


def observe_car(operators: tuple[Operator, ...], profile: AdjointProfile) -> MatrixObservation:
    model = _family(operators, "CAR")
    if any(op.degree != 1 for op in operators):
        raise Rejected("CAR generators must be odd")
    creators = tuple(adjoint(op, profile) for op in operators)
    zero, unit = scale(ZERO, identity(len(model.basis))), identity(len(model.basis))
    relations = []
    for i, j in product(range(model.sites), repeat=2):
        for label, a, b, rhs in (
            ("cc", operators[i], operators[j], zero),
            ("dagger-dagger", creators[i], creators[j], zero),
            ("c-dagger", operators[i], creators[j], unit if i == j else zero),
        ):
            lhs = add(mul(a.entries, b.entries), mul(b.entries, a.entries))
            relations.append(Relation(f"{label}[{i + 1},{j + 1}]", lhs, rhs))
    return MatrixObservation(model, operators, creators, tuple(relations))


def observe_spins(operators: tuple[Operator, ...]) -> MatrixObservation:
    model = _family(operators, "spin")
    zero, unit = scale(ZERO, identity(len(model.basis))), identity(len(model.basis))
    relations = [Relation(f"X{i + 1}^2", mul(op.entries, op.entries), unit)
                 for i, op in enumerate(operators)]
    for i in range(model.sites):
        for j in range(i + 1, model.sites):
            a, b = operators[i].entries, operators[j].entries
            relations.append(Relation(f"commutator[{i + 1},{j + 1}]",
                                      add(mul(a, b), scale(-ONE, mul(b, a))), zero))
    return MatrixObservation(model, operators, (), tuple(relations))


def span_rank(images: tuple[Matrix, ...]) -> int:
    """Exact Q(i)-rank of flattened matrices (columns), not a Clifford solver."""
    if not images:
        raise Rejected("nonempty matrix images required")
    for image in images:
        audit_matrix(image)
        if len(image) != len(images[0]):
            raise Rejected("matrix image dimensions differ")
    a = [list(row) for row in zip(*(tuple(x for row in m for x in row) for m in images))]
    pivot = 0
    for col in range(len(images)):
        selected = next((r for r in range(pivot, len(a)) if a[r][col] != ZERO), None)
        if selected is None:
            continue
        a[pivot], a[selected] = a[selected], a[pivot]
        divisor = a[pivot][col]
        a[pivot] = [x / divisor for x in a[pivot]]
        for r in range(pivot + 1, len(a)):
            factor = a[r][col]
            a[r] = [x - factor * y for x, y in zip(a[r], a[pivot])]
        pivot += 1
    return pivot


@dataclass(frozen=True)
class PauliObservation:
    model: Model
    quadratic_form: str
    abstract_generator_parity: tuple[int, int, int]
    operators: tuple[Operator, ...]
    relations: tuple[Relation, ...]
    cl2_words: tuple[str, ...]
    cl2_images: tuple[Matrix, ...]
    cl3_words: tuple[str, ...]
    cl3_images: tuple[Matrix, ...]


def observe_pauli() -> PauliObservation:
    model = MODELS["spin", 1]
    operators = tuple(Operator(model, name, 0, m) for name, m in (("X", X), ("Y", Y), ("Z", Z)))
    zero = scale(ZERO, ID2)
    relations = [Relation(f"{op.name}^2", mul(op.entries, op.entries), ID2) for op in operators]
    for a, b in ((X, Y), (X, Z), (Y, Z)):
        relations.append(Relation("distinct generators anticommute", add(mul(a, b), mul(b, a)), zero))
    relations.append(Relation("XYZ=iI", mul(mul(X, Y), Z), scale(I, ID2)))
    return PauliObservation(
        model, "q=sum(x_j^2); e_j^2=1", (1, 1, 1), operators, tuple(relations),
        ("1", "e1", "e2", "e1e2"), (ID2, X, Y, mul(X, Y)),
        ("1", "e1", "e2", "e3", "e1e2", "e1e3", "e2e3", "e1e2e3"),
        (ID2, X, Y, Z, mul(X, Y), mul(X, Z), mul(Y, Z), mul(mul(X, Y), Z)),
    )


def require_independent_images(images: tuple[Matrix, ...]) -> int:
    """Necessary rank test only; passing does not certify a universal isomorphism."""
    rank = span_rank(images)
    if rank != len(images):
        raise Rejected(f"nonfaithful word images: rank {rank} < {len(images)}")
    return rank
