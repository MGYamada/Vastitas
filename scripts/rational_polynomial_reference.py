"""Shared exact sparse QQ polynomials for Python reference checks, not Lean proofs.

The four-variable defaults preserve symplectic_reference's original Poly API.
Other consumers must pass arity explicitly; variable names/order belong to the
consumer's bound context. Arithmetic never coerces floats or changes arity.
"""

from dataclasses import dataclass
from fractions import Fraction


class Invalid(ValueError):
    """Malformed or unsupported input, never a mathematical acceptance."""

    def __init__(self, code, message):
        self.code = code
        super().__init__(message)


def natural(value, name):
    if type(value) is not int or value < 0:
        raise Invalid("INVALID_SCHEMA", f"{name} must be a nonnegative integer")


def exponents(powers, arity):
    natural(arity, "arity")
    if type(powers) is not tuple or len(powers) != arity:
        raise Invalid("INVALID_SCHEMA", f"expected {arity} exponents")
    for power in powers:
        natural(power, "exponent")


@dataclass(frozen=True)
class Poly:
    """Canonical sorted (exponents, nonzero Fraction) pairs with explicit arity."""

    terms: tuple
    arity: int = 4

    def __post_init__(self):
        natural(self.arity, "arity")
        if type(self.terms) is not tuple:
            raise Invalid("INVALID_SCHEMA", "polynomial terms must be immutable")
        previous = None
        for term in self.terms:
            if type(term) is not tuple or len(term) != 2:
                raise Invalid("INVALID_SCHEMA", "expected exponent/coefficient pair")
            powers, coefficient = term
            exponents(powers, self.arity)
            if type(coefficient) is not Fraction or coefficient == 0:
                raise Invalid("INVALID_SCHEMA", "expected nonzero exact rational")
            if previous is not None and powers <= previous:
                raise Invalid("INVALID_SCHEMA", "terms must be sorted and unique")
            previous = powers

    @staticmethod
    def from_terms(terms, arity=4):
        """Arithmetic constructor: validate before merging/removing zero terms."""
        natural(arity, "arity")
        result = {}
        for powers, coefficient in terms:
            exponents(powers, arity)
            if type(coefficient) not in (int, Fraction):
                raise Invalid("INVALID_SCHEMA", "no floating point coefficients")
            result[powers] = result.get(powers, Fraction(0)) + coefficient
        return Poly(tuple((p, Fraction(c)) for p, c in sorted(result.items()) if c), arity)

    @staticmethod
    def constant(value, arity=4):
        natural(arity, "arity")
        return Poly.from_terms([((0,) * arity, value)], arity)

    @staticmethod
    def variable(index, arity=4):
        natural(arity, "arity")
        natural(index, "variable index")
        if index >= arity:
            raise Invalid("INVALID_SCHEMA", "variable index out of range")
        return Poly.from_terms([(tuple(int(i == index) for i in range(arity)), 1)], arity)

    def _operand(self, other):
        if type(other) in (int, Fraction):
            other = Poly.constant(other, self.arity)
        if type(other) is not Poly:
            return NotImplemented
        if other.arity != self.arity:
            raise Invalid("POLYNOMIAL_ARITY_MISMATCH", "cannot combine different polynomial rings")
        return other

    def __add__(self, other):
        other = self._operand(other)
        if other is NotImplemented:
            return NotImplemented
        return Poly.from_terms(self.terms + other.terms, self.arity)

    __radd__ = __add__

    def __neg__(self):
        return Poly.from_terms(((p, -c) for p, c in self.terms), self.arity)

    def __sub__(self, other):
        other = self._operand(other)
        if other is NotImplemented:
            return NotImplemented
        return self + (-other)

    def __mul__(self, other):
        other = self._operand(other)
        if other is NotImplemented:
            return NotImplemented
        return Poly.from_terms(
            ((tuple(a + b for a, b in zip(p, q)), c * d)
             for p, c in self.terms for q, d in other.terms), self.arity,
        )

    __rmul__ = __mul__

    def __pow__(self, exponent):
        natural(exponent, "power")
        result, base = Poly.constant(1, self.arity), self
        while exponent:
            if exponent % 2:
                result = result * base
            base = base * base
            exponent //= 2
        return result

    def derivative(self, index):
        natural(index, "derivative index")
        if index >= self.arity:
            raise Invalid("INVALID_SCHEMA", "derivative index out of range")
        return Poly.from_terms(
            ((tuple(n - int(i == index) for i, n in enumerate(p)), c * p[index])
             for p, c in self.terms if p[index]), self.arity,
        )
