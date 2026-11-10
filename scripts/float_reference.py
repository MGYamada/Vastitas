"""Pure binary64 reference fragment for #318/#322; no host FP operations.

Integer bits and exact Fractions define results and SYMBOLIC operation-local
flags. This is neither an IEEE conformance proof nor a CPU/GPU flag reader.
Profile: roundTiesToEven, gradual underflow, tininess after rounding, first NaN
operand (left before right), quiet that NaN, invalid if any operand is signaling.
Invalid operations without NaN inputs return the positive default quiet NaN.
See docs/float-reference.md for the deliberately separate execution layer.
"""

from dataclasses import dataclass
from enum import IntFlag
from fractions import Fraction as Q


PROFILE = "binary64-rne-gradual-tiny-after-first-nan-v1"
SIGN = 1 << 63
FRACTION = (1 << 52) - 1
EXPONENT = 0x7FF << 52
QUIET = 1 << 51


class Flags(IntFlag):
    NONE = 0
    INVALID = 1
    DIVIDE_BY_ZERO = 2
    OVERFLOW = 4
    UNDERFLOW = 8
    INEXACT = 16


@dataclass(frozen=True)
class F64:
    """Representation equality is integer-bit equality, including every NaN."""
    bits: int

    def __post_init__(self):
        if type(self.bits) is not int or not 0 <= self.bits < 1 << 64:
            raise ValueError("F64 requires an unsigned 64-bit integer")

    @property
    def negative(self):
        return bool(self.bits & SIGN)

    @property
    def is_zero(self):
        return self.bits & ~SIGN == 0

    @property
    def is_infinite(self):
        return self.bits & ~SIGN == EXPONENT

    @property
    def is_nan(self):
        return self.bits & EXPONENT == EXPONENT and bool(self.bits & FRACTION)

    @property
    def is_signaling(self):
        return self.is_nan and not self.bits & QUIET

    def as_fraction(self):
        """Finite denotation only. NaN/infinity have no rational/RR denotation."""
        if self.is_nan or self.is_infinite:
            raise ValueError("nonfinite representation has no rational denotation")
        exponent = (self.bits & EXPONENT) >> 52
        significand = self.bits & FRACTION
        if exponent:
            significand += 1 << 52
        value = significand * _pow2(exponent - 1075 if exponent else -1074)
        return -value if self.negative else value


@dataclass(frozen=True)
class Local:
    value: F64
    flags: Flags = Flags.NONE


def zero(negative=False):
    return F64(SIGN if negative else 0)


def infinity(negative=False):
    return F64(EXPONENT | (SIGN if negative else 0))


DEFAULT_NAN = F64(EXPONENT | QUIET)


def _pow2(exponent):
    return Q(1 << exponent) if exponent >= 0 else Q(1, 1 << -exponent)


def from_fraction(value: Q, *, negative_zero=False) -> Local:
    """Explicit conversion from exact rationals, not arbitrary real numbers.

    Round an exact significand using integer quotient/remainder and tie parity.
    negative_zero specifies the sign when the EXACT input is zero; nonzero
    inputs that underflow to zero keep their own sign.
    """
    if type(value) is not Q:
        raise TypeError("conversion requires an explicit Fraction")
    if type(negative_zero) is not bool:
        raise TypeError("negative_zero must be bool")
    if not value:
        return Local(zero(negative_zero))
    negative, magnitude = value < 0, abs(value)
    exponent = magnitude.numerator.bit_length() - magnitude.denominator.bit_length()
    if magnitude < _pow2(exponent):
        exponent -= 1
    spacing = max(exponent - 52, -1074)
    scaled = magnitude / _pow2(spacing)
    mantissa, remainder = divmod(scaled.numerator, scaled.denominator)
    twice = 2 * remainder
    if twice > scaled.denominator or (twice == scaled.denominator and mantissa % 2):
        mantissa += 1
    flags = Flags.INEXACT if remainder else Flags.NONE
    if mantissa == 1 << 53:
        mantissa >>= 1
        spacing += 1
    if spacing + 52 > 1023:
        return Local(infinity(negative), Flags.OVERFLOW | Flags.INEXACT)
    if mantissa < 1 << 52:
        bits = mantissa  # Zero or subnormal, in units of 2**-1074.
        if remainder:
            flags |= Flags.UNDERFLOW
    else:
        bits = ((spacing + 1075) << 52) | (mantissa - (1 << 52))
    return Local(F64(bits | (SIGN if negative else 0)), flags)


def _nan_result(a, b):
    if a.is_nan or b.is_nan:
        selected = a if a.is_nan else b
        flags = Flags.INVALID if a.is_signaling or b.is_signaling else Flags.NONE
        return Local(F64(selected.bits | QUIET), flags)
    return None


def add(a: F64, b: F64) -> Local:
    nan = _nan_result(a, b)
    if nan is not None:
        return nan
    if a.is_infinite or b.is_infinite:
        if a.is_infinite and b.is_infinite and a.negative != b.negative:
            return Local(DEFAULT_NAN, Flags.INVALID)
        return Local(a if a.is_infinite else b)
    # Under RNE, exact cancellation is +0 except -0 + -0.
    return from_fraction(a.as_fraction() + b.as_fraction(),
                         negative_zero=a.negative and b.negative)


def sub(a: F64, b: F64) -> Local:
    nan = _nan_result(a, b)  # Do not flip a selected NaN's sign.
    return nan if nan is not None else add(a, F64(b.bits ^ SIGN))


def mul(a: F64, b: F64) -> Local:
    nan = _nan_result(a, b)
    if nan is not None:
        return nan
    negative = a.negative != b.negative
    if a.is_infinite or b.is_infinite:
        if a.is_zero or b.is_zero:
            return Local(DEFAULT_NAN, Flags.INVALID)
        return Local(infinity(negative))
    return from_fraction(a.as_fraction() * b.as_fraction(), negative_zero=negative)


def div(a: F64, b: F64) -> Local:
    """Raw IEEE-style division, distinct from mathematical and checked division."""
    nan = _nan_result(a, b)
    if nan is not None:
        return nan
    negative = a.negative != b.negative
    if (a.is_zero and b.is_zero) or (a.is_infinite and b.is_infinite):
        return Local(DEFAULT_NAN, Flags.INVALID)
    if a.is_infinite:
        return Local(infinity(negative))  # Includes infinity / zero: no flag.
    if b.is_zero:
        return Local(infinity(negative), Flags.DIVIDE_BY_ZERO)
    if b.is_infinite:
        return Local(zero(negative))
    return from_fraction(a.as_fraction() / b.as_fraction(), negative_zero=negative)
