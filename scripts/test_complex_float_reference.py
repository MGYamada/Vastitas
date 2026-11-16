"""#855 F32/F64 bit-level graph, trace, exceptional-bits and flags regressions."""

from dataclasses import replace
from fractions import Fraction as Q
from itertools import product
import unittest

import complex_division_reference as complex_ref
import float_reference as scalar


F = scalar.Flags
ORDER = (
    ("abs_c", "abs_bits"), ("abs_d", "abs_bits"), ("s", "add"),
    ("t", "rdiv"), ("A", "mul"), ("B", "mul"), ("C", "mul"),
    ("D", "mul"), ("CC", "mul"), ("DD", "mul"), ("v", "add"),
    ("u", "rdiv"), ("AC", "mul"), ("BD", "mul"),
    ("qr_sum", "add"), ("qr", "mul"), ("BC", "mul"),
    ("AD", "mul"), ("qi_diff", "sub"), ("qi", "mul"),
)


class Binary32ReferenceTests(unittest.TestCase):
    def test_rounding_golden_vectors(self):
        cases = (
            (Q(1, 10), 0x3DCCCCCD, F.INEXACT),
            (Q(1, 3), 0x3EAAAAAB, F.INEXACT),
            (Q(2**24 + 1), 0x4B800000, F.INEXACT),
            (Q(2**24 + 3), 0x4B800002, F.INEXACT),
            (Q(1, 2**149), 1, F.NONE),
            (Q(1, 2**150), 0, F.UNDERFLOW | F.INEXACT),
            (-Q(1, 2**150), scalar.SIGN32, F.UNDERFLOW | F.INEXACT),
            (Q(3, 2**150), 2, F.UNDERFLOW | F.INEXACT),
            (Q(1, 2**126) - Q(1, 2**150), 0x00800000, F.INEXACT),
            (Q((2**24 - 1) * 2**104), 0x7F7FFFFF, F.NONE),
            (Q((2**24 - 1) * 2**104 + 2**103), scalar.EXPONENT32,
             F.OVERFLOW | F.INEXACT),
        )
        for exact, bits, flags in cases:
            with self.subTest(exact=str(exact)):
                self.assertEqual(scalar.from_fraction(exact, kind=scalar.F32),
                                 scalar.Local(scalar.F32(bits), flags))

    def test_bit_roundtrip_all_binary32_exponents_and_both_signs(self):
        for sign, exponent, fraction in product((0, scalar.SIGN32), range(0xFF),
                                                 (0, 1, scalar.QUIET32, scalar.FRACTION32)):
            x = scalar.F32(sign | (exponent << 23) | fraction)
            self.assertEqual(scalar.from_fraction(x.as_fraction(),
                             negative_zero=x.negative, kind=scalar.F32), scalar.Local(x))

    def test_f32_nan_flags_and_signed_zero(self):
        one = complex_ref.one(scalar.F32)
        s_nan = scalar.F32(0xFF800042)
        q_nan = scalar.F32(0xFFC00042)
        self.assertEqual(scalar.add(s_nan, one), scalar.Local(q_nan, F.INVALID))
        self.assertEqual(scalar.abs_bits(s_nan), scalar.Local(scalar.F32(0x7F800042)))
        self.assertEqual(scalar.mul(one, scalar.zero(True, kind=scalar.F32)),
                         scalar.Local(scalar.zero(True, kind=scalar.F32)))
        self.assertEqual(scalar.rdiv(one, scalar.zero(kind=scalar.F32)),
                         scalar.Local(scalar.zero(kind=scalar.F32)))
        self.assertEqual(scalar.div(one, scalar.zero(kind=scalar.F32)),
                         scalar.Local(scalar.infinity(kind=scalar.F32), F.DIVIDE_BY_ZERO))
        self.assertEqual(scalar.rdiv(scalar.infinity(kind=scalar.F32),
                                    scalar.zero(kind=scalar.F32)),
                         scalar.Local(scalar.DEFAULT_NAN32, F.INVALID))

    def test_rejects_mixed_precision_and_native_float(self):
        with self.assertRaises(TypeError):
            scalar.add(scalar.F32(0), scalar.F64(0))
        with self.assertRaises(TypeError):
            scalar.rdiv(scalar.F32(0), scalar.F64(0))
        for illegal in (-1, 2**32, True, 0.0):
            with self.assertRaises(ValueError):
                scalar.F32(illegal)


class FixedGraphTests(unittest.TestCase):
    @staticmethod
    def cases():
        for kind in (scalar.F32, scalar.F64):
            sign = scalar._format(kind)[0]
            one = complex_ref.one(kind)
            minus_one = kind(one.bits | sign)
            plus = scalar.zero(kind=kind)
            minus = scalar.zero(True, kind=kind)
            yield kind, sign, one, minus_one, plus, minus

    def test_full_operation_order_no_fma_and_flag_folding(self):
        for kind, _, one, _, plus, _ in self.cases():
            result = complex_ref.divide(complex_ref.ComplexBits(one, plus),
                                        complex_ref.ComplexBits(one, one))
            self.assertEqual(tuple((s.name, s.operation) for s in result.steps), ORDER)
            self.assertEqual(len(result.steps), 20)
            half = kind(0x3F000000 if kind is scalar.F32 else 0x3FE0000000000000)
            self.assertEqual((result.value.real, result.value.imag),
                             (half, kind(half.bits | scalar._format(kind)[0])))
            sticky = F.NONE
            for step in result.steps:
                self.assertIn(step.operation, ("add", "sub", "mul", "rdiv", "abs_bits"))
                sticky |= step.flags
            self.assertEqual(result.flags, sticky)
            self.assertEqual(result.graph_id, complex_ref.GRAPH_ID)

    def test_all_zero_denominator_signs_and_finite_numerator_signs(self):
        # Exhaustively cross four denominator signs with 4×4 representative
        # numerator sign/zero classes, for each binary format.
        for kind, sign, one, minus_one, plus, minus in self.cases():
            numerators = (plus, minus, one, minus_one)
            zero_signs = (plus, minus)
            for a, b, c, d in product(numerators, numerators, zero_signs, zero_signs):
                with self.subTest(kind=kind.__name__, a=a.bits, b=b.bits,
                                  c=c.bits, d=d.bits):
                    trace = complex_ref.divide(complex_ref.ComplexBits(a, b),
                                               complex_ref.ComplexBits(c, d))
                    # Signed-zero algebra of the ordered scalar graph:
                    # qr < 0 iff both AC and BD are -0;
                    # qi < 0 iff BC is -0 and AD is +0.
                    qr_negative = (a.negative != c.negative) and (b.negative != d.negative)
                    qi_negative = (b.negative != c.negative) and (a.negative == d.negative)
                    self.assertEqual(trace.value.real, kind(sign if qr_negative else 0))
                    self.assertEqual(trace.value.imag, kind(sign if qi_negative else 0))
                    self.assertEqual(trace.flags, F.NONE)
                    self.assertEqual([step.selected_primitive for step in trace.steps
                                      if step.operation == "rdiv"], ["mul_zero", "mul_zero"])

    def test_negative_regression_graph_is_not_componentwise_complex_mul(self):
        for kind, sign, one, minus_one, plus, _ in self.cases():
            result = complex_ref.divide(complex_ref.ComplexBits(one, minus_one),
                                        complex_ref.ComplexBits(plus, plus))
            self.assertEqual(result.value, complex_ref.ComplexBits(plus, kind(sign)))
            # (1-i)*(0+i0) would have two positive-zero components instead.
            product_real = scalar.sub(scalar.mul(one, plus).value,
                                      scalar.mul(minus_one, plus).value).value
            product_imag = scalar.add(scalar.mul(one, plus).value,
                                      scalar.mul(minus_one, plus).value).value
            self.assertEqual((product_real, product_imag), (plus, plus))

    def test_no_fallback_on_subnormal_or_huge_finite_denominators(self):
        for kind, _, one, _, plus, _ in self.cases():
            minimum_subnormal = kind(1)
            maximum = kind(0x7F7FFFFF if kind is scalar.F32 else 0x7FEFFFFFFFFFFFFF)
            tiny = complex_ref.divide(complex_ref.ComplexBits(minimum_subnormal, plus),
                                      complex_ref.ComplexBits(minimum_subnormal, plus))
            self.assertTrue(tiny.value.real.is_nan)
            self.assertTrue(tiny.value.imag.is_nan)
            self.assertTrue(tiny.flags & F.OVERFLOW)
            self.assertTrue(tiny.flags & F.INVALID)
            self.assertFalse(tiny.flags & F.DIVIDE_BY_ZERO)
            self.assertEqual(tiny.steps[3].selected_primitive, "div")
            huge = complex_ref.divide(complex_ref.ComplexBits(one, plus),
                                      complex_ref.ComplexBits(maximum, maximum))
            self.assertEqual(huge.value, complex_ref.ComplexBits(plus, plus))
            self.assertTrue(huge.flags & F.OVERFLOW)
            self.assertEqual(huge.steps[3].selected_primitive, "div")
            self.assertEqual(huge.steps[11].selected_primitive, "mul_zero")

    def test_qnan_snan_and_infinity_follow_same_graph(self):
        for kind, _, one, _, plus, _ in self.cases():
            quiet = kind(0xFFC00042 if kind is scalar.F32 else 0xFFF8000000000042)
            signaling = kind(0x7F800042 if kind is scalar.F32 else 0x7FF0000000000042)
            infinite = scalar.infinity(kind=kind)
            for a in (quiet, signaling, infinite):
                result = complex_ref.divide(complex_ref.ComplexBits(a, plus),
                                            complex_ref.ComplexBits(plus, plus))
                self.assertEqual(len(result.steps), 20)
                self.assertTrue(result.value.real.is_nan)
                self.assertTrue(result.value.imag.is_nan)
                self.assertFalse(result.flags & F.DIVIDE_BY_ZERO)
                self.assertEqual(bool(result.flags & F.INVALID),
                                 a is not quiet)

    def test_reciprocal_is_the_same_division_entry_point(self):
        for kind, _, one, _, plus, _ in self.cases():
            for denominator in (complex_ref.ComplexBits(one, one),
                                complex_ref.ComplexBits(plus, plus),
                                complex_ref.ComplexBits(kind(1), plus)):
                self.assertEqual(complex_ref.reciprocal(denominator),
                                 complex_ref.divide(complex_ref.ComplexBits(one, plus),
                                                    denominator))

    def test_rejects_mixed_precision_and_forged_schedule(self):
        f32 = complex_ref.ComplexBits(scalar.F32(0), scalar.F32(0))
        f64 = complex_ref.ComplexBits(scalar.F64(0), scalar.F64(0))
        with self.assertRaises(TypeError):
            complex_ref.ComplexBits(scalar.F32(0), scalar.F64(0))
        with self.assertRaises(TypeError):
            complex_ref.divide(f32, f64)
        result = complex_ref.divide(f32, f32)
        forged = replace(result, steps=result.steps[:-1])  # A shortcut/optimized graph.
        self.assertNotEqual(tuple((s.name, s.operation) for s in forged.steps), ORDER)
        forged = replace(result, steps=(replace(result.steps[15],
                                                operation="fma"),) + result.steps[1:])
        self.assertNotEqual(tuple((s.name, s.operation) for s in forged.steps), ORDER)


if __name__ == "__main__":
    unittest.main()
