import copy
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import direct_logic_reference as reference


class ReferenceCompilerTests(unittest.TestCase):
    def load(self, name):
        return json.loads((ROOT / "fixtures" / name).read_text())

    def test_hostile_corpus_matches_source_and_every_admitted_plan(self):
        corpus = self.load("hostile-corpus.json")
        self.assertEqual("dregg.direct-logic.hostile-corpus.v1", corpus["schema"])
        for case in corpus["cases"]:
            with self.subTest(case=case["id"]):
                wrapper = reference.compile_source(case["source"])
                artifact = wrapper["artifact"]
                self.assertEqual(case["expected"], artifact["source_semantics"]["value"])
                boolean = artifact["plans"]["boolean"]
                self.assertEqual(case.get("boolean_status", "admitted"), boolean["status"])
                if boolean["status"] == "admitted":
                    self.assertEqual(case["expected"], boolean["acceptance"]["satisfied"])
                else:
                    self.assertEqual(case["boolean_reason"], boolean["reason"])
                nowrap = artifact["plans"]["nowrap"]
                self.assertEqual(case["nowrap_status"], nowrap["status"])
                if nowrap["status"] == "admitted":
                    self.assertEqual(case["expected"], nowrap["acceptance"]["satisfied"])
                else:
                    self.assertEqual(case["nowrap_reason"], nowrap["reason"])
                self.assertEqual((True, "ok"), reference.check_wrapper(wrapper))

    def test_hash_fixture_is_stable(self):
        fixture = self.load("deterministic-hash.json")
        source = self.load(fixture["source"])
        wrapper = reference.compile_source(source)
        self.assertEqual(fixture["artifact_sha256"], wrapper["sha256"])
        self.assertEqual(reference.canonical_bytes(wrapper), reference.canonical_bytes(json.loads(reference.canonical_bytes(wrapper))))

    def test_hybrid_hash_fixture_is_stable(self):
        fixture = self.load("deterministic-hybrid-hash.json")
        wrapper = reference.optimize_source(self.load(fixture["source"]))
        self.assertEqual(fixture["artifact_sha256"], wrapper["sha256"])
        self.assertEqual((True, "ok"), reference.check_wrapper(wrapper))

    def test_hybrid_is_strictly_cheaper_for_mixed_formula(self):
        wrapper = reference.optimize_source(self.load("hybrid-source.json"))
        plan = wrapper["artifact"]["plan"]
        self.assertEqual("admitted", plan["status"])
        self.assertTrue(plan["acceptance"]["satisfied"])
        self.assertEqual("unsupported", plan["baselines"]["all_nowrap"]["status"])
        self.assertEqual(
            "no_pure_presentation_under_single_field_bounds",
            plan["baselines"]["all_nowrap"]["reason"],
        )
        self.assertTrue(plan["certificate"]["strictly_cheaper_than_all_boolean"])
        self.assertLess(
            plan["certificate"]["cost"]["multiplications"],
            plan["baselines"]["all_boolean"]["cost"]["multiplications"],
        )
        kinds = [node["kind"] for node in plan["nodes"]]
        self.assertIn("residual_square", kinds)
        self.assertIn("boolean_zero_test", kinds)
        self.assertIn("boolean_to_residual", kinds)

    def test_hybrid_uses_boolean_atom_when_square_bound_refuses_nowrap(self):
        corpus = self.load("hostile-corpus.json")
        case = next(c for c in corpus["cases"] if c["id"] == "babybear-cancellation-vector-is-not-admitted")
        wrapper = reference.optimize_source(case["source"])
        plan = wrapper["artifact"]["plan"]
        self.assertEqual("admitted", plan["status"])
        self.assertFalse(plan["acceptance"]["satisfied"])
        self.assertEqual("unsupported", plan["baselines"]["all_nowrap"]["status"])
        kinds = [node["kind"] for node in plan["nodes"]]
        self.assertIn("boolean_zero_test", kinds)
        self.assertIn("boolean_to_residual", kinds)
        self.assertEqual((True, "ok"), reference.check_wrapper(wrapper))

    def test_hybrid_keeps_cost_bound_pareto_candidate(self):
        atom = {
            "op": "eq",
            "lhs": {"op": "var", "name": "x"},
            "rhs": {"op": "lit", "value": 0},
        }
        source = {
            "schema": reference.SOURCE_SCHEMA,
            "modulus": 101,
            "model": [{"name": "x", "value": 1, "bound": 9}],
            "formula": {"op": "or", "args": [copy.deepcopy(atom), copy.deepcopy(atom)]},
        }
        wrapper = reference.optimize_source(source)
        plan = wrapper["artifact"]["plan"]
        self.assertEqual("unsupported", plan["baselines"]["all_nowrap"]["status"])
        self.assertEqual("admitted", plan["status"])
        kinds = [node["kind"] for node in plan["nodes"]]
        # Native squares have bound 81 each, whose product cannot project to
        # F_101.  The DP must retain the dearer bound-1 Boolean conversion for
        # one side instead of pruning solely on local cost.
        self.assertIn("residual_square", kinds)
        self.assertIn("boolean_to_residual", kinds)
        self.assertIn("residual_mul", kinds)
        self.assertEqual((True, "ok"), reference.check_wrapper(wrapper))

    def test_hybrid_choice_tampering_is_detected_after_rehash(self):
        wrapper = reference.optimize_source(self.load("hybrid-source.json"))
        tampered = copy.deepcopy(wrapper)
        tampered["artifact"]["plan"]["certificate"]["optimal_over_enumerated_presentations"] = False
        tampered["sha256"] = reference.sha256_json(tampered["artifact"])
        self.assertEqual((False, "artifact_recompilation_mismatch"), reference.check_wrapper(tampered))

    def test_hybrid_small_formula_exhaustion_matches_source(self):
        x = {"op": "var", "name": "x"}
        bases = [
            {"op": "top"},
            {"op": "bottom"},
            {"op": "eq", "lhs": copy.deepcopy(x), "rhs": {"op": "lit", "value": 0}},
            {"op": "eq", "lhs": copy.deepcopy(x), "rhs": {"op": "lit", "value": 1}},
        ]
        formulas = list(bases)
        formulas.extend({"op": "not", "arg": copy.deepcopy(base)} for base in bases)
        for left in bases:
            for right in bases:
                formulas.append({"op": "and", "args": [copy.deepcopy(left), copy.deepcopy(right)]})
                formulas.append({"op": "or", "args": [copy.deepcopy(left), copy.deepcopy(right)]})
        for value in (0, 1, 2):
            for formula in formulas:
                source = {
                    "schema": reference.SOURCE_SCHEMA,
                    "modulus": 101,
                    "model": [{"name": "x", "value": value, "bound": 3}],
                    "formula": formula,
                }
                wrapper = reference.optimize_source(source)
                self.assertEqual((True, "ok"), reference.check_wrapper(wrapper))
                self.assertEqual(
                    wrapper["artifact"]["source_semantics"]["value"],
                    wrapper["artifact"]["plan"]["acceptance"]["satisfied"],
                )

    def test_tampering_is_detected_even_when_outer_hash_is_recomputed(self):
        wrapper = reference.compile_source(self.load("hash-source.json"))
        tampered = copy.deepcopy(wrapper)
        tampered["artifact"]["plans"]["boolean"]["nodes"][0]["out"] ^= 1
        tampered["sha256"] = reference.sha256_json(tampered["artifact"])
        self.assertEqual((False, "artifact_recompilation_mismatch"), reference.check_wrapper(tampered))

    def test_boolean_zero_test_equations_hold(self):
        wrapper = reference.compile_source(self.load("hash-source.json"))
        plan = wrapper["artifact"]["plans"]["boolean"]
        p = wrapper["artifact"]["source"]["modulus"]
        for node in plan["nodes"]:
            if node["kind"] == "zero_test":
                b, x, inv = node["out"], node["residual"], node["inverse"]
                self.assertEqual(0, b * (b - 1) % p)
                self.assertEqual(0, x * b % p)
                self.assertEqual((1 - b) % p, x * inv % p)

    def test_nowrap_certificate_covers_every_materialized_value(self):
        wrapper = reference.compile_source(self.load("hash-source.json"))
        plan = wrapper["artifact"]["plans"]["nowrap"]
        self.assertEqual("admitted", plan["status"])
        p = wrapper["artifact"]["source"]["modulus"]
        self.assertTrue(plan["certificate"]["field_projection_exact"])
        for node in plan["nodes"]:
            self.assertLessEqual(node["integer_value"], node["static_bound"])
            self.assertLess(node["static_bound"], p)
            self.assertEqual(node["integer_value"] % p, node["field_value"])

    def test_nonprime_modulus_fails_closed(self):
        source = self.load("hash-source.json")
        source["modulus"] = 15
        with self.assertRaisesRegex(reference.ReferenceError, "prime field"):
            reference.compile_source(source)

    def test_unknown_keys_and_quantifier_shadowing_fail_closed(self):
        source = self.load("hash-source.json")
        source["surprise"] = True
        with self.assertRaisesRegex(reference.ReferenceError, "unknown keys"):
            reference.compile_source(source)
        shadow = self.load("hash-source.json")
        shadow["formula"] = {
            "op": "forall",
            "binder": "x",
            "domain": [0],
            "body": {"op": "top"},
        }
        with self.assertRaisesRegex(reference.ReferenceError, "shadowing"):
            reference.compile_source(shadow)

    def test_cli_compile_check_and_evaluate(self):
        with tempfile.TemporaryDirectory() as temporary:
            artifact = Path(temporary) / "artifact.json"
            compile_result = subprocess.run(
                [sys.executable, str(ROOT / "direct_logic_reference.py"), "compile", str(ROOT / "fixtures" / "hash-source.json"), "-o", str(artifact)],
                check=False,
                capture_output=True,
            )
            self.assertEqual(0, compile_result.returncode, compile_result.stderr.decode())
            self.assertEqual(reference.canonical_bytes(json.loads(artifact.read_bytes())), artifact.read_bytes())
            check_result = subprocess.run(
                [sys.executable, str(ROOT / "direct_logic_reference.py"), "check", str(artifact)],
                check=False,
                capture_output=True,
            )
            self.assertEqual(0, check_result.returncode, check_result.stderr.decode())
            self.assertTrue(json.loads(check_result.stdout)["ok"])
            eval_result = subprocess.run(
                [sys.executable, str(ROOT / "direct_logic_reference.py"), "evaluate", str(ROOT / "fixtures" / "hash-source.json")],
                check=False,
                capture_output=True,
            )
            self.assertEqual(0, eval_result.returncode, eval_result.stderr.decode())
            self.assertTrue(json.loads(eval_result.stdout)["value"])
            hybrid = Path(temporary) / "hybrid.json"
            optimize_result = subprocess.run(
                [
                    sys.executable,
                    str(ROOT / "direct_logic_reference.py"),
                    "optimize",
                    str(ROOT / "fixtures" / "hybrid-source.json"),
                    "-o",
                    str(hybrid),
                ],
                check=False,
                capture_output=True,
            )
            self.assertEqual(0, optimize_result.returncode, optimize_result.stderr.decode())
            hybrid_check = subprocess.run(
                [sys.executable, str(ROOT / "direct_logic_reference.py"), "check", str(hybrid)],
                check=False,
                capture_output=True,
            )
            self.assertEqual(0, hybrid_check.returncode, hybrid_check.stderr.decode())
            self.assertTrue(json.loads(hybrid_check.stdout)["ok"])


if __name__ == "__main__":
    unittest.main()
