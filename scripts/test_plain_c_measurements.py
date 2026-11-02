"""Failures that must invalidate the new three-arm performance comparison."""
import copy
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest

from check_plain_c_baselines import load_profile

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("plain_c_measurements", ROOT / "experiments/plain_c/harness.py")
harness = importlib.util.module_from_spec(spec)
spec.loader.exec_module(harness)


def record(costs=False):
    result = dict(elapsed_ns=1000, repetitions=7, checksum="0123456789abcdef",
                  observed="fedcba9876543210", process_maxrss_kib=42, cost_instrumentation=costs)
    if costs:
        result.update({key: 0 for key in harness.COST_FIELDS})
    return result


def group(pair=0):
    rows = []
    for order, name in enumerate(harness.order_for(0, "measurement", pair)):
        row = record(name != "plain_c")
        if name == "plain_c":
            row.update({key: None for key in harness.COST_FIELDS})
        row["elapsed_ns"] *= {"generated": 6, "arena_c": 3, "plain_c": 2}[name]
        rows.append(dict(case="tiny", scope="lifecycle", phase="measurement", pair=pair,
                         order=order, implementation=name, **row))
    return rows


class PlainCMeasurements(unittest.TestCase):
    def test_timing_cannot_use_instrumented_or_relabelled_cost_records(self):
        harness.check_plain_record(record(), False)
        for bad in [record(True), {**record(), "data_allocations": 0},
                    {**record(), "cost_instrumentation": 0}, {**record(), "repetitions": True},
                    {**record(), "elapsed_ns": -1}, {**record(), "checksum": "wrong"}]:
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                harness.check_plain_record(bad, False)

    def test_every_cost_and_output_channel_is_checked(self):
        reference = record(True)
        harness.compare_diagnostic(reference, reference)
        for key in harness.COST_FIELDS | harness.PAYLOAD:
            bad = copy.deepcopy(reference)
            bad[key] = "f" * 16 if key in {"checksum", "observed"} else bad[key] + 1
            with self.subTest(key=key), self.assertRaises(ValueError):
                harness.compare_diagnostic(reference, bad)

    def test_six_groups_balance_each_position_and_pair_orientation(self):
        orders = [harness.order_for(0, "measurement", n) for n in range(6)]
        for name in harness.IMPLEMENTATIONS:
            for position in range(3):
                self.assertEqual(sum(order[position] == name for order in orders), 2)
        for a, b in [("generated", "arena_c"), ("generated", "plain_c"), ("arena_c", "plain_c")]:
            self.assertEqual(sum(order.index(a) < order.index(b) for order in orders), 3)

    def test_group_rejects_missing_duplicate_wrong_order_or_cost_forgery(self):
        valid = group()
        harness.validate_groups(valid)
        bad_groups = [valid[:-1], valid + [valid[0]]]
        for name, key, value in [("plain_c", "checksum", "f" * 16),
                                 ("plain_c", "data_allocations", 0),
                                 ("plain_c", "cost_instrumentation", True),
                                 ("arena_c", "copied_bytes", 1),
                                 ("generated", "repetitions", 8),
                                 ("plain_c", "elapsed_ns", float("nan")),
                                 ("plain_c", "process_maxrss_kib", -1),
                                 ("generated", "phase", "invented"),
                                 ("arena_c", "pair", True),
                                 ("arena_c", "unexpected", 0),
                                 ("plain_c", "blas_calls_timed", 0),
                                 ("arena_c", "order", 0)]:
            bad = copy.deepcopy(valid)
            next(row for row in bad if row["implementation"] == name)[key] = value
            bad_groups.append(bad)
        for bad in bad_groups:
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                harness.validate_groups(bad)
        forged = group()
        for row in forged:
            if row["implementation"] != "plain_c":
                row["copied_bytes"] = -1
        with self.assertRaises(ValueError):
            harness.validate_groups(forged)

    def test_summary_uses_plain_c_and_keeps_arena_attribution_separate(self):
        _, module = load_profile("public_gemm")
        with tempfile.TemporaryDirectory() as temporary:
            out = Path(temporary)
            harness.summarize(group(0) + group(1) + group(2), out, module.copy_experiment, "comparison")
            summary = json.loads((out / "summary.json").read_text())
            self.assertEqual(summary["acceptance_comparator"], "plain_c")
            comparisons = summary["records"][0]["comparisons"]
            self.assertEqual(comparisons["generated/plain_c"]["ratio"]["median"], 3)
            self.assertEqual(comparisons["generated/arena_c"]["ratio"]["median"], 2)
            self.assertEqual(comparisons["arena_c/plain_c"]["ratio"]["median"], 1.5)
            self.assertIn("not established", summary["performance_acceptance"])

    def test_measure_runs_actual_plain_executable_with_matching_repetitions(self):
        class Runner:
            def __init__(self): self.commands = []
            def run(self, command, **_):
                self.commands.append(command)
                plain = command[0] == "plain"
                result = record(False) if plain else record(True)
                result["repetitions"] = int(command[2] if plain else command[3])
                if not plain: result.pop("cost_instrumentation")
                return {"stdout": json.dumps(result)}
        _, module = load_profile("public_gemm")
        runner, rows, raw = Runner(), [], io.StringIO()
        harness.measure(runner, {"case": "tiny"}, "generated", "plain", 3, .001,
                        rows, raw, 0, ["lifecycle"], module.compare_pair)
        self.assertEqual(len(runner.commands) % 3, 0)
        self.assertEqual(sum(command[0] == "plain" for command in runner.commands), len(runner.commands) // 3)
        harness.validate_groups(rows)
        for row in rows:
            if row["implementation"] == "plain_c":
                self.assertIsNone(row["data_allocations"])


if __name__ == "__main__":
    unittest.main()
