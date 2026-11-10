"""Finite pointwise Hodge reference for #375; no Lean/Core/physical authority.

Rational coordinates on real Euclidean 3-space or Lorentz 4-space only.
Forms use increasing multi-indices, without factorials. Twisted coordinates
use the sign-line generator associated with the *declared ordered basis*;
this is a presentation, not an implicitly selected geometric orientation.
"""

from dataclasses import dataclass, fields, replace
from fractions import Fraction as Q
from itertools import combinations, permutations
from math import isqrt, prod

from rational_polynomial_calculus import rational
from rational_polynomial_reference import Invalid
from symplectic_reference import identifier


SCALAR_PROFILE = "Q-to-R-pointwise/v1"


def _vector(value, size):
    if type(value) is not tuple or len(value) != size:
        raise Invalid("INVALID_SHAPE", f"expected {size} immutable rational components")
    return tuple(rational(x) for x in value)


def _matrix(value, size):
    if type(value) is not tuple or len(value) != size:
        raise Invalid("INVALID_SHAPE", f"expected an immutable {size} by {size} matrix")
    return tuple(_vector(row, size) for row in value)


# Small private coordinate arithmetic, not another public linalg API. The
# existing metric_reference matrix helpers deliberately accept only rank two.
def _transpose(a):
    return tuple(zip(*a))


def _multiply(a, b):
    return tuple(tuple(sum((x * y for x, y in zip(row, col)), Q(0))
                       for col in _transpose(b)) for row in a)


def _apply(a, v):
    return tuple(sum((x * y for x, y in zip(row, v)), Q(0)) for row in a)


def _sign(indices):
    return (-1) ** sum(a > b for i, a in enumerate(indices) for b in indices[i + 1:])


def _det(a):
    return sum((_sign(p) * prod((a[i][j] for i, j in enumerate(p)), start=Q(1))
                for p in permutations(range(len(a)))), Q(0))


def _minor(a, rows, cols):
    return _det(tuple(tuple(a[i][j] for j in cols) for i in rows))


def _identity(n):
    return tuple(tuple(Q(i == j) for j in range(n)) for i in range(n))


@dataclass(frozen=True)
class Frame:
    environment_id: str
    object_id: str
    base_id: str
    fiber_id: str
    model_id: str
    revision: str
    coefficient_id: str
    scalar_profile: str
    basis_id: str
    dual_basis_id: str
    dimension: int
    basis: tuple

    def __post_init__(self):
        for f in fields(self):
            if f.name not in ("dimension", "basis"):
                identifier(getattr(self, f.name), f.name)
        if type(self.dimension) is not int or self.dimension not in (3, 4):
            raise Invalid("UNSUPPORTED_DIMENSION", "supply rank 3 or 4 explicitly")
        if self.scalar_profile != SCALAR_PROFILE:
            raise Invalid("UNSUPPORTED_COEFFICIENTS", "only the declared Q-to-R profile")
        if (type(self.basis) is not tuple or len(self.basis) != self.dimension
                or any(type(x) is not str or not x for x in self.basis)
                or len(set(self.basis)) != self.dimension):
            raise Invalid("INVALID_BASIS", "supply an ordered, distinctly named basis")


def _require_frame(frame):
    if type(frame) is not Frame:
        raise Invalid("MISSING_FRAME", "supply the complete named finite fiber")


@dataclass(frozen=True)
class OrientationLine:
    frame: Frame

    def __post_init__(self):
        _require_frame(self.frame)


@dataclass(frozen=True)
class Orientation:
    frame: Frame
    sign: int

    def __post_init__(self):
        _require_frame(self.frame)
        if type(self.sign) is not int or self.sign not in (-1, 1):
            raise Invalid("INVALID_ORIENTATION", "choose +1 or -1 relative to the ordered basis")


def _orientation(frame, orientation):
    if type(orientation) is not Orientation:
        raise Invalid("MISSING_ORIENTATION", "an untwisted display requires a choice")
    if orientation.frame != frame:
        raise Invalid("ORIENTATION_MISMATCH", "orientation belongs to another fiber/basis")
    return orientation.sign


@dataclass(frozen=True)
class Metric:
    frame: Frame
    metric_id: str
    revision: str
    gram: tuple

    def __post_init__(self):
        _require_frame(self.frame)
        identifier(self.metric_id, "metric_id")
        identifier(self.revision, "metric revision")
        object.__setattr__(self, "gram", _matrix(self.gram, self.frame.dimension))
        if self.gram != _transpose(self.gram):
            raise Invalid("NOT_SYMMETRIC", "expected a real symmetric bilinear metric")


@dataclass(frozen=True)
class NondegenerateEvidence:
    subject: Metric
    inverse_gram: tuple


@dataclass(frozen=True)
class SignatureEvidence:
    subject: Metric
    diagonalizer: tuple
    diagonal: tuple
    negative_count: int


@dataclass(frozen=True)
class VolumeEvidence:
    subject: Metric
    magnitude: Q


@dataclass(frozen=True)
class HodgeEvidence:
    nondegenerate: NondegenerateEvidence
    signature: SignatureEvidence
    volume: VolumeEvidence


def _subject(metric, evidence, kind, missing):
    if type(metric) is not Metric:
        raise Invalid("MISSING_METRIC", "select the mathematical metric independently")
    if type(evidence) is not kind:
        raise Invalid(missing, "explicit evidence is required")
    if evidence.subject != metric:
        raise Invalid("EVIDENCE_SUBJECT_MISMATCH", "wrong fiber/basis/coefficient/metric/revision/data")


def check_nondegenerate(metric, evidence):
    _subject(metric, evidence, NondegenerateEvidence, "MISSING_NONDEGENERACY")
    n = metric.frame.dimension
    inverse = _matrix(evidence.inverse_gram, n)
    if (_multiply(metric.gram, inverse) != _identity(n)
            or _multiply(inverse, metric.gram) != _identity(n)):
        raise Invalid("INVALID_INVERSE", "both G B = I and B G = I must hold exactly")
    return inverse


def check_hodge(metric, evidence):
    if type(metric) is not Metric:
        raise Invalid("MISSING_METRIC", "select a mathematical metric explicitly")
    if type(evidence) is not HodgeEvidence:
        raise Invalid("MISSING_HODGE_EVIDENCE", "inverse, signature and volume are separate premises")
    inverse = check_nondegenerate(metric, evidence.nondegenerate)
    sig = evidence.signature
    _subject(metric, sig, SignatureEvidence, "MISSING_SIGNATURE")
    n = metric.frame.dimension
    a, d = _matrix(sig.diagonalizer, n), _vector(sig.diagonal, n)
    if (not _det(a) or any(x == 0 for x in d)
            or _multiply(_multiply(_transpose(a), metric.gram), a)
            != tuple(tuple(d[i] if i == j else Q(0) for j in range(n)) for i in range(n))):
        raise Invalid("INVALID_SIGNATURE_WITNESS", "require invertible A and A^T G A = diagonal(d)")
    if type(sig.negative_count) is not int or sig.negative_count != sum(x < 0 for x in d):
        raise Invalid("SIGNATURE_MISMATCH", "count negative squares, not positive ones")
    if (n, sig.negative_count) not in ((3, 0), (4, 1), (4, 3)):
        raise Invalid("UNSUPPORTED_SIGNATURE", "only Euclidean rank 3 and Lorentz rank 4")
    vol = evidence.volume
    _subject(metric, vol, VolumeEvidence, "MISSING_VOLUME")
    magnitude = rational(vol.magnitude)
    det = abs(_det(metric.gram))
    if isqrt(det.numerator) ** 2 != det.numerator or isqrt(det.denominator) ** 2 != det.denominator:
        raise Invalid("COEFFICIENT_EXTENSION_REQUIRED", "normalized star needs sqrt(abs(det G)) outside Q")
    if magnitude <= 0 or magnitude * magnitude != det:
        raise Invalid("VOLUME_MISMATCH", "require positive rational volume with volume^2 = abs(det G)")
    return inverse, magnitude


def indices(frame, degree):
    _require_frame(frame)
    if type(degree) is not int or not 0 <= degree <= frame.dimension:
        raise Invalid("INVALID_DEGREE", "expected an exterior degree between zero and rank")
    return tuple(combinations(range(frame.dimension), degree))


@dataclass(frozen=True)
class Form:
    frame: Frame
    degree: int
    components: tuple
    line: OrientationLine | None

    def __post_init__(self):
        object.__setattr__(self, "components", _vector(self.components, len(indices(self.frame, self.degree))))
        if self.line is not None and (type(self.line) is not OrientationLine or self.line.frame != self.frame):
            raise Invalid("LINE_MISMATCH", "twist must be this fiber's orientation/sign line")


def basis_form(frame, multi_index):
    if (type(multi_index) is not tuple or any(type(i) is not int for i in multi_index)
            or multi_index not in indices(frame, len(multi_index))):
        raise Invalid("INVALID_BLADE", "supply an increasing tuple of basis indices")
    return Form(frame, len(multi_index), tuple(Q(i == multi_index) for i in indices(frame, len(multi_index))), None)


def scale(value, scalar):
    if type(value) not in (Form, PolarVector, AxialVector):
        raise Invalid("INVALID_VALUE", "expected a typed form or vector")
    scalar = rational(scalar)
    return replace(value, components=tuple(scalar * x for x in value.components))


def _same_frame(left, right):
    if left != right:
        raise Invalid("FIBER_MISMATCH", "nominal base/fiber/basis/coefficient identities must all match")


def wedge(a, b):
    if type(a) is not Form or type(b) is not Form:
        raise Invalid("VARIANCE_MISMATCH", "wedge takes exterior forms")
    _same_frame(a.frame, b.frame)
    degree = a.degree + b.degree
    out = {i: Q(0) for i in indices(a.frame, degree)}
    for i, x in zip(indices(a.frame, a.degree), a.components):
        for j, y in zip(indices(b.frame, b.degree), b.components):
            if set(i).isdisjoint(j):
                out[tuple(sorted(i + j))] += _sign(i + j) * x * y
    # Canonical sign-character tensor law: or(V) tensor or(V) = trivial.
    line = OrientationLine(a.frame) if (a.line is None) != (b.line is None) else None
    return Form(a.frame, degree, tuple(out.values()), line)


def _argument(metric, alpha):
    if type(metric) is not Metric:
        raise Invalid("MISSING_METRIC", "select the metric explicitly")
    if type(alpha) is not Form:
        raise Invalid("VARIANCE_MISMATCH", "expected an exterior form")
    _same_frame(metric.frame, alpha.frame)


def _pairing(inverse, a, b):
    blades = indices(a.frame, a.degree)
    return sum((x * y * _minor(inverse, i, j)
                for i, x in zip(blades, a.components)
                for j, y in zip(blades, b.components)), Q(0))


def star_twisted(metric, alpha, evidence):
    """Toggle the sign-line factor; twisted input uses canonical or(V)^2 = 1."""
    _argument(metric, alpha)
    inverse, volume = check_hodge(metric, evidence)
    n = alpha.frame.dimension
    out = {i: Q(0) for i in indices(alpha.frame, n - alpha.degree)}
    for i in indices(alpha.frame, alpha.degree):
        complement = tuple(j for j in range(n) if j not in i)
        out[complement] = _sign(i + complement) * volume * _pairing(inverse, basis_form(alpha.frame, i), alpha)
    line = OrientationLine(alpha.frame) if alpha.line is None else None
    return Form(alpha.frame, n - alpha.degree, tuple(out.values()), line)


def display_twisted(value, orientation):
    """Return components, never implicitly turn an axial vector into a polar one."""
    if not (type(value) is AxialVector or type(value) is Form and value.line is not None):
        raise Invalid("NOT_TWISTED", "only an orientation-line-valued object has this display")
    sign = _orientation(value.frame, orientation)
    return tuple(sign * x for x in value.components)


def star(metric, alpha, evidence, orientation):
    _argument(metric, alpha)
    _orientation(alpha.frame, orientation)
    if alpha.line is not None:
        raise Invalid("TWIST_MISMATCH", "oriented star here takes ordinary forms")
    result = star_twisted(metric, alpha, evidence)
    return Form(result.frame, result.degree, display_twisted(result, orientation), None)


def verify_star(metric, alpha, evidence, claimed, *, orientation):
    """Check the wedge definition, independently of star's complement formula.

    orientation=None means the twisted map, not a default orientation. Every
    degree-k basis alpha is paired against the independently supplied beta.
    """
    _argument(metric, alpha)
    inverse, volume = check_hodge(metric, evidence)
    if orientation is None:
        expected_line = OrientationLine(alpha.frame) if alpha.line is None else None
        sign = 1
    else:
        sign = _orientation(alpha.frame, orientation)
        if alpha.line is not None:
            raise Invalid("TWIST_MISMATCH", "oriented verification takes ordinary input")
        expected_line = None
    if (type(claimed) is not Form or claimed.frame != alpha.frame
            or claimed.degree != alpha.frame.dimension - alpha.degree or claimed.line != expected_line):
        raise Invalid("RESULT_TYPE_MISMATCH", "wrong result fiber, degree or orientation-line type")
    for i in indices(alpha.frame, alpha.degree):
        probe = basis_form(alpha.frame, i)
        if wedge(probe, claimed).components[0] != sign * volume * _pairing(inverse, probe, alpha):
            raise Invalid("HODGE_IDENTITY_FAILED", "candidate fails alpha wedge star(beta) = <alpha,beta> vol")
    return claimed


@dataclass(frozen=True)
class PolarVector:
    frame: Frame
    components: tuple

    def __post_init__(self):
        _require_frame(self.frame)
        object.__setattr__(self, "components", _vector(self.components, self.frame.dimension))


@dataclass(frozen=True)
class AxialVector:
    frame: Frame
    components: tuple

    def __post_init__(self):
        _require_frame(self.frame)
        object.__setattr__(self, "components", _vector(self.components, self.frame.dimension))

    @property
    def line(self):
        return OrientationLine(self.frame)


def flat(metric, vector):
    if type(metric) is not Metric:
        raise Invalid("MISSING_METRIC", "select the metric explicitly")
    if type(vector) not in (PolarVector, AxialVector):
        raise Invalid("VARIANCE_MISMATCH", "flat takes a vector, not a covector")
    _same_frame(metric.frame, vector.frame)
    line = vector.line if type(vector) is AxialVector else None
    return Form(vector.frame, 1, _apply(metric.gram, vector.components), line)


def sharp(metric, alpha, evidence):
    _argument(metric, alpha)
    if alpha.degree != 1:
        raise Invalid("VARIANCE_MISMATCH", "sharp takes a one-form")
    inverse = check_nondegenerate(metric, evidence)
    kind = PolarVector if alpha.line is None else AxialVector
    return kind(alpha.frame, _apply(inverse, alpha.components))


def cross_twisted(metric, a, b, evidence):
    if type(a) is not PolarVector or type(b) is not PolarVector:
        raise Invalid("POLAR_REQUIRED", "this cross profile takes two polar vectors")
    if a.frame.dimension != 3:
        raise Invalid("UNSUPPORTED_DIMENSION", "cross requires Euclidean rank three")
    return sharp(metric, star_twisted(metric, wedge(flat(metric, a), flat(metric, b)), evidence), evidence.nondegenerate)


@dataclass(frozen=True)
class FrameAutomorphism:
    """Active linear action on ONE declared fiber; not passive chart transport."""

    frame: Frame
    forward: tuple
    inverse: tuple

    def __post_init__(self):
        _require_frame(self.frame)
        n = self.frame.dimension
        object.__setattr__(self, "forward", _matrix(self.forward, n))
        object.__setattr__(self, "inverse", _matrix(self.inverse, n))
        if (_multiply(self.forward, self.inverse) != _identity(n)
                or _multiply(self.inverse, self.forward) != _identity(n)):
            raise Invalid("INVALID_INVERSE", "action requires both exact inverse identities")

    def act(self, value):
        if type(value) not in (Form, PolarVector, AxialVector):
            raise Invalid("INVALID_VALUE", "expected a typed form or vector")
        _same_frame(self.frame, value.frame)
        twisted = type(value) is AxialVector or type(value) is Form and value.line is not None
        sign = (-1 if _det(self.forward) < 0 else 1) if twisted else 1
        if type(value) is Form:
            # Active covector action is Q^{-T}, not Q or Q^T in general.
            blades = indices(self.frame, value.degree)
            dual = _transpose(self.inverse)
            components = tuple(sum((_minor(dual, i, j) * x for j, x in zip(blades, value.components)), Q(0))
                               for i in blades)
        else:
            components = _apply(self.forward, value.components)
        return replace(value, components=tuple(sign * x for x in components))


def check_isometry(metric, action):
    if type(metric) is not Metric or type(action) is not FrameAutomorphism:
        raise Invalid("INVALID_ISOMETRY", "supply a selected metric and explicit action")
    _same_frame(metric.frame, action.frame)
    if _multiply(_multiply(_transpose(action.forward), metric.gram), action.forward) != metric.gram:
        raise Invalid("NOT_ISOMETRIC", "require Q^T G Q = G for Hodge naturality")
    return action
