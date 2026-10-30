"""Finite exact SSH reference for #247; not Vastitas or Lean acceptance.

Only QQ[v,w,E,z,z^-1], 2 by 2 matrices, QQ[epsilon]/(epsilon^2), and
nonzero principal z-saturation in QQ[E,z]. No CAS, floats, root finder,
general ideal checker, fan gluing, or expression parser. See
docs/ssh-toric-reference.md for the scheme data and pending obligations.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


VARIABLES = ("v", "w", "E", "z")


def rational(value):
    if type(value) not in (int, Fraction):
        raise ValueError("expected an exact int or Fraction, not Float or bool")
    return Fraction(value)


def powers_checked(powers):
    if (type(powers) is not tuple or len(powers) != 4
            or any(type(n) is not int for n in powers)
            or any(n < 0 for n in powers[:3])):
        raise ValueError("expected (v,w,E,z) integer powers; only z may be negative")


@dataclass(frozen=True)
class Laurent:
    """Canonical finite support in QQ[v,w,E,z,z^-1]."""

    terms: tuple

    def __post_init__(self):
        if type(self.terms) is not tuple:
            raise ValueError("terms must be immutable")
        previous = None
        for term in self.terms:
            if type(term) is not tuple or len(term) != 2:
                raise ValueError("expected a (powers, coefficient) pair")
            powers, coefficient = term
            powers_checked(powers)
            if type(coefficient) is not Fraction or coefficient == 0:
                raise ValueError("canonical coefficients must be nonzero Fractions")
            if previous is not None and powers <= previous:
                raise ValueError("canonical terms must be unique and sorted")
            previous = powers

    @staticmethod
    def from_terms(terms):
        result = {}
        for powers, coefficient in terms:
            powers_checked(powers)
            coefficient = rational(coefficient)
            result[powers] = result.get(powers, Fraction(0)) + coefficient
        return Laurent(tuple((p, c) for p, c in sorted(result.items()) if c))

    @staticmethod
    def constant(value):
        return Laurent.from_terms([((0, 0, 0, 0), value)])

    @staticmethod
    def variable(name):
        if name not in VARIABLES:
            raise ValueError("unknown variable")
        return Laurent.from_terms([(tuple(int(s == name) for s in VARIABLES), 1)])

    @staticmethod
    def character(power):
        return Laurent.from_terms([((0, 0, 0, power), 1)])

    def __add__(self, other):
        if type(other) is not Laurent:
            other = Laurent.constant(other)
        return Laurent.from_terms(self.terms + other.terms)

    __radd__ = __add__

    def __neg__(self):
        return Laurent.from_terms((p, -c) for p, c in self.terms)

    def __sub__(self, other):
        if type(other) is not Laurent:
            other = Laurent.constant(other)
        return self + (-other)

    def __mul__(self, other):
        if type(other) is not Laurent:
            other = Laurent.constant(other)
        return Laurent.from_terms(
            (tuple(a + b for a, b in zip(p, q)), c * d)
            for p, c in self.terms for q, d in other.terms
        )

    __rmul__ = __mul__

    def __pow__(self, power):
        if type(power) is not int or power < 0:
            raise ValueError("use character(n) for negative powers of z only")
        result, base = Laurent.constant(1), self
        while power:
            if power % 2:
                result = result * base
            base = base * base
            power //= 2
        return result

    def specialize(self, **values):
        """Exact rational ring map; z=0 is never a map out of a Laurent ring."""
        if any(name not in VARIABLES for name in values):
            raise ValueError("unknown specialization variable")
        values = {name: rational(value) for name, value in values.items()}
        if values.get("z") == 0:
            raise ValueError("z must map to a unit; z=0 is outside the torus")
        terms = []
        for powers, coefficient in self.terms:
            new_powers = list(powers)
            for i, name in enumerate(VARIABLES):
                if name in values:
                    coefficient *= values[name] ** powers[i]
                    new_powers[i] = 0
            terms.append((tuple(new_powers), coefficient))
        return Laurent.from_terms(terms)

    def constant_value(self):
        if any(any(p) for p, _ in self.terms):
            raise ValueError("unresolved variables in scalar matrix")
        return sum((c for _, c in self.terms), Fraction(0))


ZERO, ONE = Laurent.constant(0), Laurent.constant(1)
V, W, E, Z = (Laurent.variable(name) for name in VARIABLES)
Z_INV = Laurent.character(-1)


def matrix2(rows):
    result = tuple(tuple(x if type(x) is Laurent else Laurent.constant(x)
                         for x in row) for row in rows)
    if len(result) != 2 or any(len(row) != 2 for row in result):
        raise ValueError("only 2 by 2 matrices are supported")
    return result


def ssh_hamiltonian():
    return matrix2(((0, V + W * Z_INV), (V + W * Z, 0)))


def characteristic2(hamiltonian):
    h = matrix2(hamiltonian)
    if any(p[2] for row in h for entry in row for p, _ in entry.terms):
        raise ValueError("Hamiltonian entries must be independent of energy E")
    return (E - h[0][0]) * (E - h[1][1]) - h[0][1] * h[1][0]


def specialize_matrix(hamiltonian, **values):
    return tuple(tuple(entry.specialize(**values) for entry in row)
                 for row in matrix2(hamiltonian))


def kernel_dimension2(scalar_matrix):
    """Exact scalar rank only; not a Jordan solver over a parameter/quotient ring."""
    h = tuple(tuple(entry.constant_value() for entry in row)
              for row in matrix2(scalar_matrix))
    if h[0][0] * h[1][1] - h[0][1] * h[1][0]:
        return 0
    return 1 if any(x for row in h for x in row) else 2


@dataclass(frozen=True)
class TorusPresentation:
    """Spec(QQ[coordinates,z^-1]/(equation)), as a presentation, not a Scheme API.

    Coordinates always contain z; the inverted element is exactly z.
    Structural equality compares presentations, NOT nominal scheme identity.
    """

    coordinates: tuple[str, ...]
    equation: Laurent

    def __post_init__(self):
        if (type(self.coordinates) is not tuple or "z" not in self.coordinates
                or tuple(s for s in VARIABLES if s in self.coordinates) != self.coordinates):
            raise ValueError("coordinates must be an ordered subset of (v,w,E,z), including z")
        if type(self.equation) is not Laurent:
            raise ValueError("expected a Laurent equation")
        if any(n and s not in self.coordinates for p, _ in self.equation.terms
               for s, n in zip(VARIABLES, p)):
            raise ValueError("equation uses a coordinate absent from the base/ambient")

    def specialize(self, **values):
        if any(s not in self.coordinates or s == "z" for s in values):
            raise ValueError("specialize active parameters or E; retain the torus coordinate")
        assignments = tuple((s, rational(values[s])) for s in VARIABLES if s in values)
        target = TorusPresentation(tuple(s for s in self.coordinates if s not in values),
                                   self.equation.specialize(**dict(assignments)))
        return Specialization(self, target, assignments)


@dataclass(frozen=True)
class Specialization:
    """An explicit source/target and QQ-algebra substitution, including E fibers."""

    source: TorusPresentation
    target: TorusPresentation
    assignments: tuple

    def __post_init__(self):
        if type(self.source) is not TorusPresentation or type(self.target) is not TorusPresentation:
            raise ValueError("expected source and target presentations")
        if type(self.assignments) is not tuple:
            raise ValueError("assignments must be immutable")
        names = []
        for item in self.assignments:
            if type(item) is not tuple or len(item) != 2:
                raise ValueError("expected (coordinate, rational value)")
            name, value = item
            if name not in self.source.coordinates or name == "z" or type(value) is not Fraction:
                raise ValueError("invalid base change assignment")
            names.append(name)
        if tuple(names) != tuple(s for s in VARIABLES if s in names):
            raise ValueError("assignments must be unique and ordered")
        expected = TorusPresentation(tuple(s for s in self.source.coordinates if s not in names),
                                     self.source.equation.specialize(**dict(self.assignments)))
        if self.target != expected:
            raise ValueError("target does not match the exact specialization")


def ssh_bloch_family():
    return TorusPresentation(VARIABLES, characteristic2(ssh_hamiltonian()))


def clear_z_denominator(poly):
    """Return (k, z^k * poly) with minimal k>=0; retain that z was inverted."""
    if type(poly) is not Laurent:
        raise ValueError("expected a Laurent polynomial")
    power = max(0, -min((p[3] for p, _ in poly.terms), default=0))
    return power, Laurent.character(power) * poly


def polynomial_boundary_at_z_zero(poly):
    """Affine-boundary evaluation of a polynomial, NOT Laurent specialization."""
    if type(poly) is not Laurent or any(p[3] < 0 for p, _ in poly.terms):
        raise ValueError("only polynomial representatives extend to z=0")
    return Laurent.from_terms((p, c) for p, c in poly.terms if p[3] == 0)


def require_qe_z_polynomial(poly):
    if (type(poly) is not Laurent or not poly.terms
            or any(p[0] or p[1] or p[3] < 0 for p, _ in poly.terms)):
        raise ValueError("saturation fragment: one nonzero polynomial in QQ[E,z] only")


@dataclass(frozen=True)
class PrincipalZSaturation:
    original: Laurent
    removed_power: int
    generator: Laurent


def check_principal_z_saturation(expected, witness):
    """Check f=z^k*g and z does not divide g, only in the stated UFD fragment."""
    require_qe_z_polynomial(expected)
    if type(witness) is not PrincipalZSaturation:
        raise ValueError("expected a principal z-saturation witness")
    require_qe_z_polynomial(witness.generator)
    if type(witness.removed_power) is not int or witness.removed_power < 0:
        raise ValueError("removed power must be a nonnegative integer")
    return (witness.original == expected
            and expected == Laurent.character(witness.removed_power) * witness.generator
            and polynomial_boundary_at_z_zero(witness.generator) != ZERO)


def saturate_principal_z(poly):
    """Compute (poly):z^infinity by removing its z factor in QQ[E,z].

    This uses that QQ[E,z] is a UFD and z is prime. No lists of generators,
    arbitrary base rings, zero divisors, radicalization or general ideal tests.
    """
    require_qe_z_polynomial(poly)
    power = min(p[3] for p, _ in poly.terms)
    return PrincipalZSaturation(poly, power, Laurent.character(-power) * poly)


@dataclass(frozen=True)
class Dual:
    """The exact normal form a+b*epsilon in QQ[epsilon]/(epsilon^2)."""

    a: Fraction = Fraction(0)
    b: Fraction = Fraction(0)

    def __post_init__(self):
        object.__setattr__(self, "a", rational(self.a))
        object.__setattr__(self, "b", rational(self.b))

    def __add__(self, other):
        if type(other) is not Dual:
            other = Dual(other)
        return Dual(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Dual(-self.a, -self.b)

    def __sub__(self, other):
        if type(other) is not Dual:
            other = Dual(other)
        return self + (-other)

    def __mul__(self, other):
        if type(other) is not Dual:
            other = Dual(other)
        return Dual(self.a * other.a, self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def inverse(self):
        if self.a == 0:
            raise ValueError("a+b*epsilon is a unit exactly when a != 0")
        return Dual(1 / self.a, -self.b / self.a ** 2)

    def __pow__(self, power):
        if type(power) is not int:
            raise ValueError("expected an integer exponent")
        result, base = Dual(1), self
        if power < 0:
            base, power = self.inverse(), -power
        while power:
            if power % 2:
                result = result * base
            base = base * base
            power //= 2
        return result

    def multiplication_matrix(self):
        """Columns are images of (1,epsilon); the regular representation is faithful."""
        return ((self.a, Fraction(0)), (self.b, self.a))


EPSILON, DUAL_Z = Dual(0, 1), Dual(-1, 1)


def in_double_point(poly):
    """Evaluate QQ[z,z^-1] at z=-1+epsilon. Other variables must be removed."""
    if type(poly) is not Laurent or any(any(p[:3]) for p, _ in poly.terms):
        raise ValueError("specialize v,w,E before using the double-point quotient")
    return sum((c * DUAL_Z ** p[3] for p, c in poly.terms), Dual())


def require_ssh_double_point(presentation):
    """Bind the dual-number model to the exact SSH fiber, not just its zero set."""
    if (type(presentation) is not TorusPresentation
            or presentation.coordinates != ("z",)
            or presentation.equation != -Z_INV * (Z + 1) ** 2):
        raise ValueError("expected the exact v=w=1, E=0 SSH presentation")
    # The generator differs from (z+1)^2 by the Laurent unit -z^-1.
    return (Dual(1), EPSILON)
