"""The Stage 5 spectral fixture is fresh and records the values that the acceptance conditions cite."""
import json
import unittest

import spectral_fixture as sf


def by_label(cases):
    return {case["label"]: case for case in cases}


class SpectralFixtureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(sf.FIXTURE.read_text())

    def test_fixture_is_fresh(self):
        self.assertEqual(sf.main(["--check"]), 0)

    def test_stage5_characteristic_polynomial_and_trace_square(self):
        stage5 = next(s for s in self.data["spectra"] if s["name"] == "stage5")
        # chi = t^2 - x^2 - y^2 and tr(H^2) = 2x^2 + 2y^2.
        self.assertEqual(stage5["characteristic"], [[[2, 0, 0], "-1"], [[0, 2, 0], "-1"], [[0, 0, 2], "1"]])
        self.assertEqual(stage5["tracePowers"][1], [[[2, 0], "2"], [[0, 2], "2"]])
        self.assertEqual(stage5["tracePowers"][0], [])

    def test_scalar_and_jordan_share_chi_and_differ_in_the_action(self):
        modules = {m["name"]: m for m in self.data["modules"]}
        for scalar, jordan, element in (("scalar", "jordan", "t - 2"), ("zero", "nilpotent", "t")):
            self.assertEqual(modules[scalar]["characteristic"], modules[jordan]["characteristic"])
            act = {m: {a["element"]: a["annihilates"] for a in modules[m]["actions"]} for m in (scalar, jordan)}
            self.assertTrue(act[scalar][element])
            self.assertFalse(act[jordan][element])
        spectra = {s["name"]: s for s in self.data["spectra"]}
        self.assertEqual(spectra["scalar"]["tracePowers"], spectra["jordan"]["tracePowers"])

    def test_charts(self):
        charts = by_label(self.data["charts"])
        self.assertTrue(charts["stage5 gap"]["accepted"])
        self.assertTrue(charts["cubic off the discriminant"]["accepted"])
        for label in ("stage5 without a gap", "stage5 perturbed witness", "stage5 wrong exponent",
                      "stage5 unreduced witness", "stage5 zero localizer", "cubic without a gap",
                      "jordan without a gap", "jordan shifted witness"):
            with self.subTest(label=label):
                self.assertFalse(charts[label]["accepted"])
                self.assertIsNotNone(charts[label]["failure"])

    def test_branch_points(self):
        points = by_label(self.data["branchPoints"])
        plus, minus = points["stage5 (3, 4), 5"], points["stage5 (3, 4), -5"]
        self.assertEqual(plus["projector"], [["4/5", "2/5"], ["2/5", "1/5"]])
        self.assertEqual(minus["projector"], [["1/5", "-2/5"], ["-2/5", "4/5"]])
        self.assertEqual(plus["differential"], ["3/5", "4/5"])
        self.assertEqual(minus["differential"], ["-3/5", "-4/5"])
        for label in ("stage5 (3, 4), 4 is no eigenvalue", "stage5 origin, 0 is off the chart",
                      "cubic 2, 1 is off the chart"):
            with self.subTest(label=label):
                self.assertFalse(points[label]["onChart"])
                self.assertIsNone(points[label]["projector"])


if __name__ == "__main__":
    unittest.main()
