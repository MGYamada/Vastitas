"""Pure representation/arithmetic regressions, separate from the monad laws."""

from fractions import Fraction as Q
import unittest

import float_reference as r


F = r.Flags
ONE = r.F64(0x3FF0000000000000)
TWO = r.F64(0x4000000000000000)


class RepresentationTests(unittest.TestCase):
    def test_bit_identity_distinguishes_signed_zero_and_nan_payloads(self):
        self.assertNotEqual(r.zero(), r.zero(True))
        self.assertEqual(r.zero().as_fraction(), r.zero(True).as_fraction())
        for bits in (0, r.SIGN, 1, 0x0010000000000000, 0x7FEFFFFFFFFFFFFF,
                     r.EXPONENT, r.SIGN | r.EXPONENT, 0x7FF8000000000042,
                     0xFFF8000000000043, 0x7FF0000000000042):
            value = r.F64(bits)
            self.assertEqual(value, r.F64(bits))
            self.assertEqual(value.bits, bits)
        self.assertNotEqual(r.F64(0x7FF8000000000042), r.F64(0x7FF8000000000043))
        self.assertNotEqual(r.F64(0x7FF0000000000042), r.F64(0x7FF8000000000042))

    def test_nonfinite_has_no_rr_denotation(self):
        for bits in (r.EXPONENT, r.SIGN | r.EXPONENT,
                     0x7FF8000000000001, 0xFFF0000000000001):
            with self.assertRaises(ValueError):
                r.F64(bits).as_fraction()

    def test_rejects_implicit_native_float_conversion_and_invalid_bits(self):
        for value in (-1, 1 << 64, True, 0.0):
            with self.assertRaises(ValueError):
                r.F64(value)
        for value in (0.1, 1, "0.1"):
            with self.assertRaises(TypeError):
                r.from_fraction(value)


class PureArithmeticTests(unittest.TestCase):
    def test_independent_known_rounding_vectors(self):
        cases = (
            (Q(1, 10), 0x3FB999999999999A, F.INEXACT),
            (Q(1, 3), 0x3FD5555555555555, F.INEXACT),
            (Q(2**53 + 1), 0x4340000000000000, F.INEXACT),
            (Q(2**53 + 3), 0x4340000000000002, F.INEXACT),
            (Q(1, 2**1074), 1, F.NONE),
            (Q(1, 2**1075), 0, F.UNDERFLOW | F.INEXACT),
            (-Q(1, 2**1075), r.SIGN, F.UNDERFLOW | F.INEXACT),
            (Q(3, 2**1075), 2, F.UNDERFLOW | F.INEXACT),
            (Q(1, 2**1022) - Q(1, 2**1075), 0x0010000000000000, F.INEXACT),
            (Q((2**53 - 1) * 2**971), 0x7FEFFFFFFFFFFFFF, F.NONE),
            (Q((2**53 - 1) * 2**971 + 2**969), 0x7FEFFFFFFFFFFFFF, F.INEXACT),
            (Q((2**53 - 1) * 2**971 + 2**970), r.EXPONENT, F.OVERFLOW | F.INEXACT),
        )
        for exact, bits, flags in cases:
            with self.subTest(bits=hex(bits), flags=flags):
                self.assertEqual(r.from_fraction(exact), r.Local(r.F64(bits), flags))

    def test_finite_bit_roundtrip_across_every_exponent_and_both_signs(self):
        for sign in (0, r.SIGN):
            for exponent in range(0x7FF):
                for fraction in (0, 1, r.QUIET, r.FRACTION):
                    bits = sign | (exponent << 52) | fraction
                    value = r.F64(bits)
                    self.assertEqual(r.from_fraction(value.as_fraction(),
                                                     negative_zero=value.negative),
                                     r.Local(value))

    def test_raw_division_special_cases_are_not_typed_failure(self):
        for sign in (False, True):
            z = r.zero(sign)
            self.assertEqual(r.div(ONE, z), r.Local(r.infinity(sign), F.DIVIDE_BY_ZERO))
            self.assertEqual(r.div(r.zero(), z), r.Local(r.DEFAULT_NAN, F.INVALID))
            self.assertEqual(r.div(r.infinity(), z), r.Local(r.infinity(sign)))
            self.assertEqual(r.div(ONE, r.infinity(sign)), r.Local(z))
        self.assertEqual(r.div(r.infinity(), r.infinity()), r.Local(r.DEFAULT_NAN, F.INVALID))

    def test_selected_nan_payload_sign_and_quieting(self):
        q = r.F64(0xFFF8000000000042)
        other = r.F64(0x7FF8000000000043)
        s = r.F64(0x7FF0000000000007)
        for operation in (r.add, r.sub, r.mul, r.div):
            self.assertEqual(operation(q, other), r.Local(q))
            self.assertEqual(operation(other, q), r.Local(other))
            self.assertEqual(operation(q, s), r.Local(q, F.INVALID))
            self.assertEqual(operation(ONE, s), r.Local(r.F64(s.bits | r.QUIET), F.INVALID))
        self.assertEqual(r.sub(ONE, q), r.Local(q))  # Do not negate a NaN payload.

    def test_signed_zero_arithmetic(self):
        plus, minus = r.zero(), r.zero(True)
        self.assertEqual(r.add(minus, minus), r.Local(minus))
        self.assertEqual(r.add(plus, minus), r.Local(plus))
        self.assertEqual(r.sub(minus, plus), r.Local(minus))
        self.assertEqual(r.sub(ONE, ONE), r.Local(plus))
        self.assertEqual(r.mul(minus, ONE), r.Local(minus))
        self.assertEqual(r.div(plus, r.F64(ONE.bits | r.SIGN)), r.Local(minus))
        self.assertEqual(r.from_fraction(Q(0), negative_zero=True), r.Local(minus))

    def test_invalid_overflow_and_gradual_underflow(self):
        invalid = r.Local(r.DEFAULT_NAN, F.INVALID)
        self.assertEqual(r.add(r.infinity(), r.infinity(True)), invalid)
        self.assertEqual(r.mul(r.zero(), r.infinity()), invalid)
        maximum = r.F64(0x7FEFFFFFFFFFFFFF)
        self.assertEqual(r.mul(maximum, TWO), r.Local(r.infinity(), F.OVERFLOW | F.INEXACT))
        self.assertEqual(r.div(r.F64(2), TWO), r.Local(r.F64(1)))  # Exact subnormal.
        self.assertEqual(r.div(r.F64(1), TWO), r.Local(r.zero(), F.UNDERFLOW | F.INEXACT))
        self.assertEqual(r.mul(r.F64(1), ONE), r.Local(r.F64(1)))  # No DAZ or FTZ.

    def test_numerical_addition_is_not_associative(self):
        x = r.F64(0x4340000000000000)  # 2**53
        negative = r.F64(x.bits | r.SIGN)
        self.assertEqual(r.add(r.add(x, ONE).value, negative).value, r.zero())
        self.assertEqual(r.add(x, r.add(ONE, negative).value).value, ONE)


if __name__ == "__main__":
    unittest.main()
