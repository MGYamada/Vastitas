"""Pure binary32/binary64 reference fragment for #318/#322/#758; no host FP.

Integer bits and exact Fractions define results and SYMBOLIC operation-local
flags. This is neither an IEEE conformance proof nor a CPU/GPU flag reader.
Profile: roundTiesToEven, gradual underflow, tininess after rounding, first NaN
operand (left before right), quiet that NaN, invalid if any operand is signaling.
Invalid operations without NaN inputs return the positive default quiet NaN.
See docs/reference/execution-plans.md#float-reference for the deliberately separate execution layer.
"""

from dataclasses import dataclass
from enum import IntFlag
from fractions import Fraction as Q


PROFILE = "binary64-rne-gradual-tiny-after-first-nan-v1"
PROFILE32 = "binary32-rne-gradual-tiny-after-first-nan-v1"
SIGN = 1 << 63
FRACTION = (1 << 52) - 1
EXPONENT = 0x7FF << 52
QUIET = 1 << 51
SIGN32 = 1 << 31
FRACTION32 = (1 << 23) - 1
EXPONENT32 = 0xFF << 23
QUIET32 = 1 << 22


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
class F32:
    """Binary32 bit carrier; no native-float conversion or implicit widening."""
    bits: int

    def __post_init__(self):
        if type(self.bits) is not int or not 0 <= self.bits < 1 << 32:
            raise ValueError("F32 requires an unsigned 32-bit integer")

    @property
    def negative(self):
        return bool(self.bits & SIGN32)

    @property
    def is_zero(self):
        return self.bits & ~SIGN32 == 0

    @property
    def is_infinite(self):
        return self.bits & ~SIGN32 == EXPONENT32

    @property
    def is_nan(self):
        return self.bits & EXPONENT32 == EXPONENT32 and bool(self.bits & FRACTION32)

    @property
    def is_signaling(self):
        return self.is_nan and not self.bits & QUIET32

    def as_fraction(self):
        if self.is_nan or self.is_infinite:
            raise ValueError("nonfinite representation has no rational denotation")
        exponent = (self.bits & EXPONENT32) >> 23
        significand = self.bits & FRACTION32
        if exponent:
            significand += 1 << 23
        value = significand * _pow2(exponent - 150 if exponent else -149)
        return -value if self.negative else value


@dataclass(frozen=True)
class Local:
    value: F32 | F64
    flags: Flags = Flags.NONE


def _format(kind):
    if kind is F64:
        return (SIGN, EXPONENT, QUIET, 52, 1023, -1074)
    if kind is F32:
        return (SIGN32, EXPONENT32, QUIET32, 23, 127, -149)
    raise TypeError("expected F32 or F64, without implicit promotion")


def _same_format(a, b):
    if type(a) is not type(b):
        raise TypeError("scalar operation requires identical F32/F64 formats")
    _format(type(a))


def zero(negative=False, *, kind=F64):
    sign = _format(kind)[0]
    return kind(sign if negative else 0)


def infinity(negative=False, *, kind=F64):
    sign, exponent, *_ = _format(kind)
    return kind(exponent | (sign if negative else 0))


DEFAULT_NAN = F64(EXPONENT | QUIET)
DEFAULT_NAN32 = F32(EXPONENT32 | QUIET32)


def _pow2(exponent):
    return Q(1 << exponent) if exponent >= 0 else Q(1, 1 << -exponent)


def from_fraction(value: Q, *, negative_zero=False, kind=F64) -> Local:
    """Explicit conversion from exact rationals, not arbitrary real numbers.

    Round an exact significand using integer quotient/remainder and tie parity.
    negative_zero specifies the sign when the EXACT input is zero; nonzero
    inputs that underflow to zero keep their own sign.
    """
    if type(value) is not Q:
        raise TypeError("conversion requires an explicit Fraction")
    if type(negative_zero) is not bool:
        raise TypeError("negative_zero must be bool")
    sign, _, _, fraction_bits, bias, minimum_spacing = _format(kind)
    if not value:
        return Local(zero(negative_zero, kind=kind))
    negative, magnitude = value < 0, abs(value)
    exponent = magnitude.numerator.bit_length() - magnitude.denominator.bit_length()
    if magnitude < _pow2(exponent):
        exponent -= 1
    spacing = max(exponent - fraction_bits, minimum_spacing)
    scaled = magnitude / _pow2(spacing)
    mantissa, remainder = divmod(scaled.numerator, scaled.denominator)
    twice = 2 * remainder
    if twice > scaled.denominator or (twice == scaled.denominator and mantissa % 2):
        mantissa += 1
    flags = Flags.INEXACT if remainder else Flags.NONE
    if mantissa == 1 << (fraction_bits + 1):
        mantissa >>= 1
        spacing += 1
    if spacing + fraction_bits > bias:
        return Local(infinity(negative, kind=kind), Flags.OVERFLOW | Flags.INEXACT)
    if mantissa < 1 << fraction_bits:
        bits = mantissa  # Zero or subnormal, in minimum-spacing units.
        if remainder:
            flags |= Flags.UNDERFLOW
    else:
        bits = ((spacing + bias + fraction_bits) << fraction_bits) | (mantissa - (1 << fraction_bits))
    return Local(kind(bits | (sign if negative else 0)), flags)


def _nan_result(a, b):
    _same_format(a, b)
    if a.is_nan or b.is_nan:
        selected = a if a.is_nan else b
        flags = Flags.INVALID if a.is_signaling or b.is_signaling else Flags.NONE
        quiet = _format(type(a))[2]
        return Local(type(a)(selected.bits | quiet), flags)
    return None


def _default_nan(kind):
    return DEFAULT_NAN32 if kind is F32 else DEFAULT_NAN


def add(a: F64, b: F64) -> Local:
    nan = _nan_result(a, b)
    if nan is not None:
        return nan
    if a.is_infinite or b.is_infinite:
        if a.is_infinite and b.is_infinite and a.negative != b.negative:
            return Local(_default_nan(type(a)), Flags.INVALID)
        return Local(a if a.is_infinite else b)
    # Under RNE, exact cancellation is +0 except -0 + -0.
    return from_fraction(a.as_fraction() + b.as_fraction(),
                         negative_zero=a.negative and b.negative, kind=type(a))


def sub(a: F32 | F64, b: F32 | F64) -> Local:
    nan = _nan_result(a, b)  # Do not flip a selected NaN's sign.
    return nan if nan is not None else add(a, type(a)(b.bits ^ _format(type(a))[0]))


def mul(a: F64, b: F64) -> Local:
    nan = _nan_result(a, b)
    if nan is not None:
        return nan
    negative = a.negative != b.negative
    if a.is_infinite or b.is_infinite:
        if a.is_zero or b.is_zero:
            return Local(_default_nan(type(a)), Flags.INVALID)
        return Local(infinity(negative, kind=type(a)))
    return from_fraction(a.as_fraction() * b.as_fraction(), negative_zero=negative, kind=type(a))


def div(a: F64, b: F64) -> Local:
    """Raw IEEE-style division, distinct from mathematical and checked division."""
    nan = _nan_result(a, b)
    if nan is not None:
        return nan
    negative = a.negative != b.negative
    if (a.is_zero and b.is_zero) or (a.is_infinite and b.is_infinite):
        return Local(_default_nan(type(a)), Flags.INVALID)
    if a.is_infinite:
        return Local(infinity(negative, kind=type(a)))  # Includes infinity / zero: no flag.
    if b.is_zero:
        return Local(infinity(negative, kind=type(a)), Flags.DIVIDE_BY_ZERO)
    if b.is_infinite:
        return Local(zero(negative, kind=type(a)))
    return from_fraction(a.as_fraction() / b.as_fraction(), negative_zero=negative, kind=type(a))


def abs_bits(a: F32 | F64) -> Local:
    """IEEE abs: clear the sign bit without quieting a signaling NaN."""
    return Local(type(a)(a.bits & ~_format(type(a))[0]))


def rdiv(a: F32 | F64, b: F32 | F64) -> Local:
    """#318's totalized real division: a / ±0 = a * +0, including local flags."""
    _same_format(a, b)
    return mul(a, zero(kind=type(a))) if b.is_zero else div(a, b)
