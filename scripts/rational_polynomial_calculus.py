"""Finite exact substitution/evaluation/integration for the shared Poly.

Coefficient arithmetic only: no enclosure, quadrature, AD engine or proof
authority. Variable roles/order and supported domains belong to each consumer.
"""

from fractions import Fraction as Q

from rational_polynomial_reference import Invalid, Poly, natural


def rational(value):
    if type(value) not in (int, Q):
        raise Invalid("INEXACT_INPUT", "expected int or Fraction, never float/bool")
    return Q(value)


def polynomial(value):
    if type(value) is not Poly:
        raise Invalid("INVALID_POLYNOMIAL", "expected the shared exact Poly")
    return value


def substitute(value, coordinates):
    """Simultaneous substitution into one explicitly specified polynomial ring."""
    polynomial(value)
    if (type(coordinates) is not tuple or len(coordinates) != value.arity
            or not coordinates):
        raise Invalid("INVALID_SHAPE", "expected one polynomial per source variable")
    arity = polynomial(coordinates[0]).arity
    if any(polynomial(p).arity != arity for p in coordinates):
        raise Invalid("POLYNOMIAL_ARITY_MISMATCH", "substitutions need one target ring")
    result = Poly.constant(0, arity)
    for powers, coefficient in value.terms:
        term = Poly.constant(coefficient, arity)
        for coordinate, power in zip(coordinates, powers):
            term = term * coordinate ** power
        result = result + term
    return result


def evaluate(value, coordinates):
    polynomial(value)
    if type(coordinates) is not tuple or len(coordinates) != value.arity:
        raise Invalid("INVALID_SHAPE", "expected one rational per variable")
    coordinates = tuple(rational(x) for x in coordinates)
    result = Q(0)
    for powers, coefficient in value.terms:
        term = coefficient
        for coordinate, power in zip(coordinates, powers):
            term *= coordinate ** power
        result += term
    return result


def integrate(value, index, lower, upper):
    """Integrate one variable coefficientwise; remove it, preserving other order.

    Each monomial contributes c*(upper**(n+1)-lower**(n+1))/(n+1).
    The primitive is oriented; consumer profiles must check their own intervals.
    """
    polynomial(value)
    natural(index, "integration index")
    if index >= value.arity:
        raise Invalid("INVALID_SCHEMA", "integration index out of range")
    lower, upper = rational(lower), rational(upper)
    return Poly.from_terms(
        ((powers[:index] + powers[index + 1:],
          coefficient * (upper ** (powers[index] + 1) - lower ** (powers[index] + 1))
          / (powers[index] + 1))
         for powers, coefficient in value.terms), value.arity - 1,
    )
