import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import direct_logic_bench as bench


class SemanticTests(unittest.TestCase):
    def by_id(self, workload_id):
        return next(w for w in bench.pinned_workloads() if w.workload_id == workload_id)

    def test_public_swap_relation_accepts_published_invalid_witness(self):
        workload = self.by_id("bitlogic.swap.published-invalid-witness")
        outcome = bench.evaluate_lane("M-SPEC", workload)
        self.assertFalse(workload.expected)
        self.assertTrue(outcome.accepted)
        self.assertEqual(0, outcome.output)

    def test_field_cancellation_is_reproduced_and_nowrap_refuses_it(self):
        workload = self.by_id("gabbay.babybear-cancellation")
        naive = bench.evaluate_lane("G-FIELD-NAIVE", workload)
        nowrap = bench.evaluate_lane("D-NOWRAP", workload)
        self.assertTrue(naive.accepted)
        self.assertEqual("unsupported", nowrap.status)
        # The natural square of the canonical field representative already
        # exceeds p, so the corrected route refuses before it can cast.  This
        # is stronger than silently reaching the cancelling field sum.
        self.assertEqual("atom_square_not_below_modulus", nowrap.reason)
        self.assertEqual(bench.BABY_BEAR_SQRT_NEG_ONE**2, nowrap.max_integer_accumulator)

    def test_corrected_and_conventional_lanes_match_reference(self):
        workloads = bench.pinned_workloads() + list(bench.random_workloads(2_000))
        gates, _ = bench.semantic_conformance(workloads)
        self.assertEqual("pass", gates["lanes"]["D-NOWRAP"]["gate_status"])
        self.assertEqual("pass", gates["lanes"]["D-BOOLGRAPH"]["gate_status"])
        self.assertEqual("pass", gates["lanes"]["C-AIR"]["gate_status"])
        self.assertEqual(0, gates["lanes"]["D-BOOLGRAPH"]["mismatches"])
        self.assertEqual(0, gates["lanes"]["C-AIR"]["mismatches"])

    def test_published_and_naive_field_lanes_fail_semantic_gate(self):
        gates, _ = bench.semantic_conformance(bench.pinned_workloads())
        self.assertEqual("fail", gates["lanes"]["M-SPEC"]["gate_status"])
        self.assertEqual("fail", gates["lanes"]["G-FIELD-NAIVE"]["gate_status"])
        self.assertGreater(gates["lanes"]["M-SPEC"]["mismatches"], 0)
        self.assertGreater(gates["lanes"]["G-FIELD-NAIVE"]["mismatches"], 0)

    def test_cost_mirror_matches_lean_boolean_formula(self):
        formula = bench.and_(bench.atom(0), bench.not_(bench.atom(1)))
        cost = bench.symbolic_cost("D-BOOLGRAPH", formula)
        # 2 atoms, 1 not, 1 binary gate, plus one acceptance equation.
        self.assertEqual(11, cost.equations)
        self.assertEqual(9, cost.multiplications)
        self.assertEqual(6, cost.witnesses)
        self.assertEqual(2, cost.max_degree)

    def test_single_polynomial_degree_tracks_connective_direction(self):
        conjunction = bench.all_((bench.atom(0), bench.atom(1), bench.atom(2)))
        disjunction = bench.any_((bench.atom(0), bench.atom(1), bench.atom(2)))
        self.assertEqual(3, bench.symbolic_cost("M-SPEC", conjunction).max_degree)
        self.assertEqual(1, bench.symbolic_cost("M-SPEC", disjunction).max_degree)
        self.assertEqual(2, bench.symbolic_cost("G-FIELD-NAIVE", conjunction).max_degree)
        self.assertEqual(6, bench.symbolic_cost("G-FIELD-NAIVE", disjunction).max_degree)
        self.assertEqual(2, bench.symbolic_cost("M-SPEC", conjunction).multiplications)
        self.assertEqual(0, bench.symbolic_cost("M-SPEC", disjunction).multiplications)
        self.assertEqual(3, bench.symbolic_cost("G-FIELD-NAIVE", conjunction).multiplications)
        self.assertEqual(5, bench.symbolic_cost("G-FIELD-NAIVE", disjunction).multiplications)

    def test_artifact_run_is_machine_readable_and_excludes_failed_lanes(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "run"
            args = bench.parse_args(
                [
                    "--output",
                    str(output),
                    "--run-id",
                    "test-run",
                    "--random-cases",
                    "100",
                    "--no-timing",
                ]
            )
            bench.run(args)
            summary = json.loads((output / "summary.json").read_text())
            self.assertIn("M-SPEC", summary["excluded_from_speedups"])
            self.assertIn("G-FIELD-NAIVE", summary["excluded_from_speedups"])
            self.assertEqual([], summary["timing_ratios"])
            for filename in (
                "META.json",
                "workloads.json",
                "gates.json",
                "costs.csv",
                "samples.csv",
                "samples.jsonl",
                "summary.json",
                "SUMMARY.md",
            ):
                self.assertTrue((output / filename).exists(), filename)


if __name__ == "__main__":
    unittest.main()
