import json
import unittest
from fractions import Fraction as Q

import frame_reference as ref

POINTS = ref.POINTS


def rationals(values):
    return tuple(Q(value) for value in values)


class FrameReference(unittest.TestCase):
    def setUp(self):
        self.frames = ref.frames()

    def test_fixture_is_current(self):
        self.assertTrue(ref.FIXTURE.is_file(), "run scripts/frame_reference.py --write")
        self.assertEqual(ref.FIXTURE.read_text(), json.dumps(ref.fixture(), indent=2) + "\n")

    def test_columns_are_not_rows(self):
        b = self.frames["b"]
        self.assertEqual(b.at((0, 0)), ((1, 1), (0, 2)))
        self.assertNotEqual(b.at((0, 0)), ref.transpose(b.at((0, 0))))
        self.assertEqual(ref.encode(b, "tangent", (0, 0), (1, 2)), (0, 1))

    def test_constant_and_polynomial_inverses(self):
        for frame in self.frames.values():
            for point in POINTS:
                self.assertEqual(ref.mat_mul(frame.at(point), frame.inverse_at(point)), ref.identity(2))
        r = self.frames["r"]
        self.assertNotEqual(r.at((3, -1)), r.at((Q(1, 2), 2)))

    def test_invalid_frames_have_their_codes(self):
        codes = [case["error"] for case in ref.fixture()["invalidFrames"]]
        self.assertEqual(codes, ["SINGULAR", "INVERSE_OF_CONSTANT", "MISSING_INVERSE",
                                 "WRONG_INVERSE", "WRONG_INVERSE", "WRONG_SIZE"])

    def test_decoding_inverts_encoding(self):
        for frame in self.frames.values():
            for point in POINTS:
                for variance in ("tangent", "cotangent"):
                    value = rationals((Q(5, 3), -2))
                    array = ref.encode(frame, variance, point, value)
                    self.assertEqual(ref.decode(frame, variance, point, array), value)
                    self.assertEqual(ref.encode(frame, variance, point, ref.decode(frame, variance, point, value)), value)

    def test_transition_laws(self):
        b, b2, r = self.frames["b"], self.frames["b'"], self.frames["r"]
        for point in POINTS:
            self.assertEqual(ref.transition(b, b, point), ref.identity(2))
            self.assertEqual(ref.mat_mul(ref.transition(b2, r, point), ref.transition(b, b2, point)),
                             ref.transition(b, r, point))
            self.assertEqual(ref.mat_mul(ref.transition(b2, b, point), ref.transition(b, b2, point)),
                             ref.identity(2))
            v = rationals((7, Q(-1, 4)))
            self.assertEqual(ref.mat_vec(ref.transition(b, b2, point), ref.encode(b, "tangent", point, v)),
                             ref.encode(b2, "tangent", point, v))

    def test_pairing_does_not_depend_on_the_frame(self):
        alpha, v = rationals((Q(2, 3), 5)), rationals((3, Q(-1, 2)))
        for frame in self.frames.values():
            for point in POINTS:
                self.assertEqual(ref.pairing(ref.encode(frame, "cotangent", point, alpha),
                                             ref.encode(frame, "tangent", point, v)),
                                 ref.pairing(alpha, v))

    def test_one_map_in_two_frame_pairs(self):
        b, c, b2, c2 = (self.frames[name] for name in ("b", "c", "b'", "c'"))
        for images in (ref.SQUARE, ref.SHEAR, ref.RANK_ONE):
            for point in POINTS:
                m, m2 = ref.frame_matrix(images, point, b, c), ref.frame_matrix(images, point, b2, c2)
                image = ref.apply_map(images, point)
                change = ref.mat_mul(ref.mat_mul(ref.transition(c, c2, image), m), ref.transition(b2, b, point))
                self.assertEqual(m2, change)
                jacobian = ref.jacobian(images, point)
                for frame_s, frame_t, array in ((b, c, m), (b2, c2, m2)):
                    decoded = ref.mat_mul(ref.mat_mul(frame_t.at(image), array), frame_s.inverse_at(point))
                    self.assertEqual(decoded, jacobian)
        self.assertNotEqual(ref.frame_matrix(ref.SQUARE, (3, -1), b, c), ref.frame_matrix(ref.SQUARE, (3, -1), b2, c2))

    def test_coapply_is_the_pullback(self):
        b, c = self.frames["b"], self.frames["c"]
        seed = rationals((1, Q(-2, 5)))
        for point in POINTS:
            image = ref.apply_map(ref.SQUARE, point)
            m = ref.frame_matrix(ref.SQUARE, point, b, c)
            coapplied = ref.mat_vec(ref.transpose(m), ref.encode(c, "cotangent", image, seed))
            pullback = ref.mat_vec(ref.transpose(ref.jacobian(ref.SQUARE, point)), seed)
            self.assertEqual(ref.decode(b, "cotangent", point, coapplied), pullback)

    def test_chain_rule_in_frames(self):
        b, c, s = self.frames["b"], self.frames["c"], self.frames["s"]
        composite = ref.compose_maps(ref.SQUARE, ref.SHEAR)
        for point in POINTS:
            middle = ref.apply_map(ref.SHEAR, point)
            self.assertEqual(ref.frame_matrix(composite, point, b, s),
                             ref.mat_mul(ref.frame_matrix(ref.SQUARE, middle, c, s),
                                         ref.frame_matrix(ref.SHEAR, point, b, c)))

    def test_rank_one_map_stays_rank_one(self):
        for source, target in (("b", "c"), ("b'", "c'"), ("r", "s")):
            for point in POINTS:
                (a, b), (c, d) = ref.frame_matrix(ref.RANK_ONE, point, self.frames[source], self.frames[target])
                self.assertEqual(a * d - b * c, 0)
                self.assertNotEqual((a, b, c, d), (0, 0, 0, 0))

    def test_gram_transport(self):
        metric = tuple(rationals(row) for row in ref.METRIC)
        b, b2, r = self.frames["b"], self.frames["b'"], self.frames["r"]
        for point in POINTS:
            for source, target in ((b, b2), (b, r), (r, b2)):
                t = ref.transition(target, source, point)
                self.assertEqual(ref.gram(target, metric, point),
                                 ref.mat_mul(ref.mat_mul(ref.transpose(t), ref.gram(source, metric, point)), t))


if __name__ == "__main__":
    unittest.main()
