"""Exact polynomial differentials on named real planes; no metric dependency.

Reference arithmetic only, not AD Core or Lean acceptance. Reuse the existing
four-variable polynomial engine through the subring Q[x0,x1]; reject x2,x3 at
every public polynomial boundary. The geometric semantics here are R^2.
"""

from dataclasses import dataclass, fields
from fractions import Fraction as Q

from symplectic_reference import Invalid, Poly, identifier


SCALAR_PROFILE = "Q-to-R-polynomial-plane/v1"
ZERO = Poly.constant(0)
X, Y = Poly.variable(0), Poly.variable(1)


def rational(value):
    if type(value) not in (int, Q):
        raise Invalid("INEXACT_INPUT", "expected int or Fraction, never float/bool")
    return Q(value)


def vector(value):
    if type(value) is not tuple or len(value) != 2:
        raise Invalid("INVALID_SHAPE", "expected an immutable pair")
    return tuple(rational(x) for x in value)


def matrix(value):
    if type(value) is not tuple or len(value) != 2:
        raise Invalid("INVALID_SHAPE", "expected an immutable 2 by 2 matrix")
    return tuple(vector(row) for row in value)


IDENTITY = matrix(((1, 0), (0, 1)))


def transpose(value):
    return tuple(zip(*matrix(value)))


def matvec(value, coordinates):
    value, coordinates = matrix(value), vector(coordinates)
    return tuple(sum((a * b for a, b in zip(row, coordinates)), Q(0)) for row in value)


def multiply(left, right):
    left, columns = matrix(left), transpose(right)
    return tuple(tuple(sum((a * b for a, b in zip(row, col)), Q(0))
                       for col in columns) for row in left)


def determinant(value):
    (a, b), (c, d) = matrix(value)
    return a * d - b * c


def inverse(value):
    value = matrix(value)
    det = determinant(value)
    if det == 0:
        raise Invalid("SINGULAR", "exact determinant is zero")
    (a, b), (c, d) = value
    return ((d / det, -b / det), (-c / det, a / det))


def audit_polynomial(value):
    if (type(value) is not Poly or value.arity != 4
            or any(p[2:] != (0, 0) for p, _ in value.terms)):
        raise Invalid("UNSUPPORTED_POLYNOMIAL", "only Q[x0,x1] interpreted over R^2")


def substitute(value, coordinates):
    audit_polynomial(value)
    if type(coordinates) is not tuple or len(coordinates) != 2:
        raise Invalid("INVALID_SHAPE", "expected two polynomial coordinates")
    for coordinate in coordinates:
        audit_polynomial(coordinate)
    return sum((c * coordinates[0] ** p[0] * coordinates[1] ** p[1]
                for p, c in value.terms), ZERO)


def evaluate(value, coordinates):
    audit_polynomial(value)
    x, y = vector(coordinates)
    return sum((c * x ** p[0] * y ** p[1] for p, c in value.terms), Q(0))


@dataclass(frozen=True)
class Frame:
    environment_id: str
    object_id: str
    base_id: str
    chart_id: str
    tangent_frame_id: str
    cotangent_frame_id: str
    model_id: str
    model_revision: str
    coordinates: tuple[str, str]
    scalar_profile: str = SCALAR_PROFILE

    def __post_init__(self):
        for field in fields(self):
            if field.name != "coordinates":
                identifier(getattr(self, field.name), field.name)
        if (type(self.coordinates) is not tuple or len(self.coordinates) != 2
                or any(type(c) is not str or not c for c in self.coordinates)
                or len(set(self.coordinates)) != 2):
            raise Invalid("INVALID_FRAME", "expected two ordered distinct coordinate names")
        if self.scalar_profile != SCALAR_PROFILE:
            raise Invalid("UNSUPPORTED_PROFILE", "only rational coefficients with real semantics")


@dataclass(frozen=True)
class Point:
    frame: Frame
    coordinates: tuple

    def __post_init__(self):
        if type(self.frame) is not Frame:
            raise Invalid("INVALID_FRAME", "expected a named coordinate frame")
        object.__setattr__(self, "coordinates", vector(self.coordinates))


def require_point(point, frame):
    if type(point) is not Point or point.frame != frame:
        raise Invalid("FIBER_MISMATCH", "point must use the exact expected object/base/frame")


@dataclass(frozen=True)
class Tangent:
    point: Point
    components: tuple

    def __post_init__(self):
        if type(self.point) is not Point:
            raise Invalid("FIBER_MISMATCH", "expected an exact basepoint")
        object.__setattr__(self, "components", vector(self.components))


@dataclass(frozen=True)
class Cotangent:
    point: Point
    components: tuple

    def __post_init__(self):
        if type(self.point) is not Point:
            raise Invalid("FIBER_MISMATCH", "expected an exact basepoint")
        object.__setattr__(self, "components", vector(self.components))


def pairing(alpha, tangent):
    if type(alpha) is not Cotangent or type(tangent) is not Tangent:
        raise Invalid("VARIANCE_MISMATCH", "pair a covector with a vector explicitly")
    if alpha.point != tangent.point:
        raise Invalid("FIBER_MISMATCH", "pairing requires the same basepoint and dual frames")
    return sum((a * v for a, v in zip(alpha.components, tangent.components)), Q(0))


@dataclass(frozen=True)
class ScalarPolynomial:
    frame: Frame
    expression: Poly

    def __post_init__(self):
        if type(self.frame) is not Frame:
            raise Invalid("INVALID_FRAME", "expected a coordinate frame")
        audit_polynomial(self.expression)


def differential(function, point):
    if type(function) is not ScalarPolynomial:
        raise Invalid("UNSUPPORTED_FUNCTION", "expected a real-valued polynomial")
    require_point(point, function.frame)
    return Cotangent(point, tuple(evaluate(function.expression.derivative(i), point.coordinates)
                                  for i in range(2)))


@dataclass(frozen=True)
class PolynomialMap:
    source: Frame
    target: Frame
    expressions: tuple

    def __post_init__(self):
        if type(self.source) is not Frame or type(self.target) is not Frame:
            raise Invalid("INVALID_FRAME", "expected source and target frames")
        for name in ("environment_id", "base_id", "scalar_profile"):
            if getattr(self.source, name) != getattr(self.target, name):
                raise Invalid("BASE_MISMATCH", f"map changes {name}")
        if type(self.expressions) is not tuple or len(self.expressions) != 2:
            raise Invalid("INVALID_SHAPE", "expected two polynomial components")
        for expression in self.expressions:
            audit_polynomial(expression)

    def at(self, point):
        require_point(point, self.source)
        return Point(self.target, tuple(evaluate(p, point.coordinates) for p in self.expressions))


def cotangent_pullback(mapping, point, seed):
    """J(point)^T seed, with seed strictly in the fiber over mapping(point)."""
    if type(mapping) is not PolynomialMap:
        raise Invalid("UNSUPPORTED_MAP", "expected a polynomial map")
    if type(seed) is not Cotangent:
        raise Invalid("VARIANCE_MISMATCH", "pullback requires a cotangent seed")
    if seed.point != mapping.at(point):
        raise Invalid("SEED_BASEPOINT_MISMATCH", "seed must lie over the actual map output")
    jacobian = tuple(tuple(evaluate(p.derivative(i), point.coordinates) for i in range(2))
                     for p in mapping.expressions)
    return Cotangent(point, matvec(transpose(jacobian), seed.components))


@dataclass(frozen=True)
class CoordinateChange:
    """x = A u, on one nominal real plane, with ordered dual coordinate frames."""

    source: Frame  # u frame
    target: Frame  # x frame
    forward: tuple

    def __post_init__(self):
        if type(self.source) is not Frame or type(self.target) is not Frame:
            raise Invalid("INVALID_FRAME", "expected coordinate frames")
        for name in ("environment_id", "object_id", "base_id", "model_id",
                     "model_revision", "scalar_profile"):
            if getattr(self.source, name) != getattr(self.target, name):
                raise Invalid("COORDINATE_OBJECT_MISMATCH", f"coordinate change changes {name}")
        object.__setattr__(self, "forward", matrix(self.forward))
        inverse(self.forward)  # exact invertibility, independent of any metric
        if self.source == self.target and self.forward != IDENTITY:
            raise Invalid("INVALID_FRAME", "a nonidentity reexpression needs distinct frames")

    def as_map(self):
        return PolynomialMap(self.source, self.target,
                             tuple(a * X + b * Y for a, b in self.forward))

    def at(self, point):
        require_point(point, self.source)
        return Point(self.target, matvec(self.forward, point.coordinates))

    def reexpress(self, function):
        if type(function) is not ScalarPolynomial or function.frame != self.target:
            raise Invalid("FIBER_MISMATCH", "function must use the target coordinate frame")
        return ScalarPolynomial(self.source, substitute(function.expression, self.as_map().expressions))

    def push_tangent(self, tangent):
        if type(tangent) is not Tangent:
            raise Invalid("VARIANCE_MISMATCH", "cannot push a covector as a tangent")
        return Tangent(self.at(tangent.point), matvec(self.forward, tangent.components))

    def reexpress_tangent(self, point, tangent):
        if type(tangent) is not Tangent:
            raise Invalid("VARIANCE_MISMATCH", "cannot transform df as a tangent")
        if tangent.point != self.at(point):
            raise Invalid("FIBER_MISMATCH", "tangent must lie over the mapped basepoint")
        return Tangent(point, matvec(inverse(self.forward), tangent.components))


def require_coordinate_change(change):
    if type(change) is not CoordinateChange:
        raise Invalid("UNSUPPORTED_COORDINATE_CHANGE", "expected a checked rational linear coordinate change")


def check_cotangent_transport(change, point, alpha, claimed):
    """Check a supplied claim against the independent x=A u request."""
    require_coordinate_change(change)
    expected = cotangent_pullback(change.as_map(), point, alpha)
    if type(claimed) is not Cotangent:
        raise Invalid("VARIANCE_MISMATCH", "expected cotangent transport result")
    if claimed != expected:
        raise Invalid("COTANGENT_TRANSPORT_MISMATCH", "expected A^T alpha at the source point")
    return expected
