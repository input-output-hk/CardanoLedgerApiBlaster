"""Process-level checks for stdout, exit codes, argument errors and supervision.

Functional equivalence and counterexample tests live in Tests/Equivalence/*.lean.
"""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
CLI = ROOT / ".lake/build/bin/uplc_equiv"


def data_at(path):
    term = "c"
    for index in path:
        fields = f"[(force (force (builtin sndPair))) [(builtin unConstrData) {term}]]"
        for _ in range(index):
            fields = f"[(force (builtin tailList)) {fields}]"
        term = f"[(force (builtin headList)) {fields}]"
    return term


def reject_if(condition):
    return ("(lam c (force [[[(force (builtin ifThenElse)) " + condition +
            "] (delay (error))] (delay (con unit ()))]))")


def reject_data_at(path, expected):
    return reject_if(f"[[(builtin equalsData) {data_at(path)}] (con data ({expected}))]")


def integer_at_equals(path, value):
    return f"[[(builtin equalsInteger) [(builtin unIData) {data_at(path)}]] (con integer {value})]"


class CheckerProcess(unittest.TestCase):
    def invoke(self, left, right, *flags, json_output=True, equivalence=True):
        with tempfile.TemporaryDirectory(prefix="uplc cli tests ") as directory:
            # Exercise spaces and quotes while running outside the repository.
            paths = [Path(directory) / 'left "script".uplc', Path(directory) / 'right.uplc']
            for path, term in zip(paths, (left, right)):
                path.write_text(f"(program 1.1.0 {term})")
            result = subprocess.run(
                [str(CLI),
                 *(str(path) for path in paths), "--format", "textual",
                 *(["--equivalence", "--inputs", "integer", "--max-steps", "40"]
                   if equivalence else ["--budget", "1000000", "10000"]),
                 "--wall-timeout", "30",
                 *(["--json"] if json_output else []), *flags],
                cwd=directory, capture_output=True, text=True, timeout=90)
            return result.returncode, json.loads(result.stdout) if json_output else result.stdout

    def test_acceptance_is_directional(self):
        accept, reject = "(lam c (con unit ()))", "(lam c (error))"
        for old, new, code, verdict in [
                (reject, accept, 0, "preserved"),
                (accept, reject, 1, "regression"),
                (accept, accept, 0, "preserved"),
                (reject, reject, 0, "preserved")]:
            with self.subTest(verdict=verdict, old=old, new=new):
                actual_code, report = self.invoke(old, new, equivalence=False)
                self.assertEqual(actual_code, code, report)
                self.assertEqual(report["verdict"], verdict)
                if code == 1:
                    witness = report["counterexample"]
                    self.assertTrue(witness["replayed"])
                    self.assertTrue(witness["old"]["accepts"])
                    self.assertFalse(witness["new"]["accepts"])

    def test_budget_boundaries_and_slower_replacement(self):
        accept = "(lam c (con unit ()))"
        slower = "(lam c [(lam x (con unit ())) c])"
        # Applying the validator costs four machine nodes plus startup.
        for cpu, memory, expected in [(64100, 500, "regression"),
                                      (64099, 500, "preserved"),
                                      (64100, 499, "preserved")]:
            code, report = self.invoke(accept, "(lam c (error))", "--budget", str(cpu), str(memory),
                                       equivalence=False)
            self.assertEqual((code, report["verdict"]),
                             (1 if expected == "regression" else 0, expected), report)
        for budget, code in [("64100", 1), ("1000000", 0)]:
            actual, report = self.invoke(accept, slower, "--budget", budget, "10000",
                                         equivalence=False)
            self.assertEqual(actual, code, report)
            if code == 1:
                witness = report["counterexample"]
                self.assertTrue(witness["replayed"])
                self.assertEqual(witness["new"]["kind"], "budget_exhausted")
                self.assertEqual(witness["old"]["spent_cpu"], 64100)
                self.assertEqual(witness["old"]["spent_memory"], 500)

    def test_builtin_cost_is_included_in_shared_budget(self):
        accept = "(lam c (con unit ()))"
        addition = "(lam c [(lam x (con unit ())) [[(builtin addInteger) (con integer 1)] (con integer 2)]])"
        # Eleven machine nodes, startup, and AddInteger E (CPU 101208, memory 2).
        for cpu, memory, code in [(277308, 1202, 0), (277307, 1202, 1), (277308, 1201, 1)]:
            with self.subTest(cpu=cpu, memory=memory):
                actual, report = self.invoke(accept, addition, "--budget", str(cpu), str(memory),
                                             equivalence=False)
                self.assertEqual(actual, code, report)
                if code:
                    self.assertTrue(report["counterexample"]["replayed"])
                    self.assertEqual(report["counterexample"]["new"]["kind"], "budget_exhausted")

    def test_language_return_rule(self):
        for language, code in [("PlutusV3", 1), ("PlutusV2", 0), ("PlutusV1", 0)]:
            actual, report = self.invoke("(lam c (con unit ()))", "(lam c (con integer 42))",
                                         "--language", language, equivalence=False)
            self.assertEqual(actual, code, report)

    def test_directional_composed_context_witness_and_export(self):
        with tempfile.TemporaryDirectory() as directory:
            emitted = Path(directory) / "acceptance.lean"
            old, new = Path(directory) / "old.uplc", Path(directory) / "new.uplc"
            old.write_text("(program 1.1.0 (lam c (con unit ())))")
            new.write_text("(program 1.1.0 " + reject_data_at([2, 1, 0, 2], "I 1001") + ")")
            result = subprocess.run([str(CLI), str(old), str(new), "--format", "textual",
                "--inputs", "vesting-partial", "--case", "81",
                "--variation", "datum-total,fee-positive", "--budget", "100000000", "1000000",
                "--emit-lean", str(emitted), "--json"],
                cwd=ROOT, capture_output=True, text=True, timeout=60)
            code, report = result.returncode, json.loads(result.stdout)
            self.assertEqual(code, 1, report)
            witness = report["counterexample"]
            self.assertTrue(witness["replayed"], report)
            self.assertTrue(witness["old"]["accepts"])
            self.assertFalse(witness["new"]["accepts"])
            checked = subprocess.run(["lake", "env", "lean", "--memory=8192", str(emitted)],
                                     cwd=ROOT, capture_output=True, text=True, timeout=60)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_three_argument_acceptance(self):
        accept = "(lam d (lam r (lam c (con integer 42))))"
        reject = "(lam d (lam r (lam c (error))))"
        for old, new, code in [(accept, reject, 1), (reject, accept, 0)]:
            actual, report = self.invoke(old, new, "--inputs", "data3", "--language", "PlutusV2",
                                         equivalence=False)
            self.assertEqual(actual, code, report)
            if code:
                witness = report["counterexample"]
                self.assertTrue(witness["replayed"])
                self.assertEqual(set(witness["input"]), {"datum", "redeemer", "context"})
                self.assertTrue(witness["old"]["accepts"])
                self.assertFalse(witness["new"]["accepts"])

    def test_acceptance_text_report_identifies_budget_and_model(self):
        code, output = self.invoke("(lam c (con unit ()))", "(lam c (con unit ()))",
                                   equivalence=False, json_output=False)
        self.assertEqual(code, 0, output)
        self.assertIn("preserved:", output)
        self.assertIn('Budget: {"cpu":1000000,"memory":10000}', output)
        self.assertIn("Cost model: bundled post-Conway E", output)

    def test_generalized_times_are_independent_and_replayed(self):
        lower = integer_at_equals([0, 7, 0, 0, 0], 42)
        upper = integer_at_equals([0, 7, 1, 0, 0], -17)
        condition = f"[[[(force (builtin ifThenElse)) {lower}] {upper}] (con bool False)]"
        code, report = self.invoke("(lam c (con unit ()))", reject_if(condition),
            "--inputs", "vesting-partial", "--case", "81", "--variation", "time-any",
            "--budget", "100000000", "1000000", equivalence=False)
        self.assertEqual(code, 1, report)
        witness = report["counterexample"]
        self.assertTrue(witness["replayed"], report)
        bounds = witness["input"]["fields"][0]["fields"][7]["fields"]
        self.assertEqual(bounds[0]["fields"][0]["fields"][0], {"int": 42})
        self.assertEqual(bounds[1]["fields"][0]["fields"][0], {"int": -17})

    def test_generalized_data_symbols_do_not_alias_unused_fields(self):
        conditions = [integer_at_equals([2, 1, 0], 11),
                      integer_at_equals([1], 22), integer_at_equals([0, 3], 33)]
        condition = "(con bool True)"
        for item in reversed(conditions):
            condition = f"[[[(force (builtin ifThenElse)) {item}] {condition}] (con bool False)]"
        # Only this exact triple can be accepted by OLD. A malformed Data value
        # errors in OLD and cannot supply a spurious regression.
        only_accept = ("(lam c (force [[[(force (builtin ifThenElse)) " + condition +
                       "] (delay (con unit ()))] (delay (error))]))")
        code, report = self.invoke(only_accept, "(lam c (error))", "--inputs", "htlc-refund",
            "--case", "0", "--variation", "datum-any,redeemer-any,raw-unused",
            "--budget", "100000000", "1000000", equivalence=False)
        self.assertEqual(code, 1, report)
        witness = report["counterexample"]
        self.assertTrue(witness["replayed"], report)
        fields = witness["input"]["fields"]
        self.assertEqual(fields[2]["fields"][1]["fields"][0], {"int": 11})
        self.assertEqual(fields[1], {"int": 22})
        self.assertEqual(fields[0]["fields"][3], {"int": 33})

    def test_widening_deduplicates_erased_case_distinctions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            old, new, emitted = root / "old.uplc", root / "new.uplc", root / "check.lean"
            for path in [old, new]:
                path.write_text("(program 1.1.0 (lam c (con unit ())))")
            result = subprocess.run([str(CLI), str(old), str(new), "--format", "textual",
                "--inputs", "vesting-partial", "--variation", "time-any,inputs-any,outputs-any,signers-any",
                "--budget", "100000000", "1000000", "--wall-timeout", "30",
                "--emit-lean", str(emitted), "--json"],
                cwd=ROOT, capture_output=True, text=True, timeout=60)
            report = json.loads(result.stdout)
            self.assertEqual(result.returncode, 0, report)
            # 96 cases collapse to four treasury/donation combinations, each
            # with two universal queries. The checked export must still compile.
            self.assertEqual(emitted.read_text().count("#blaster"), 8)
            checked = subprocess.run(["lake", "env", "lean", "--memory=8192", str(emitted)],
                                     cwd=ROOT, capture_output=True, text=True, timeout=60)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_generic_spending_context_preserves_shape_and_replays(self):
        code, report = self.invoke("(lam c (con unit ()))", "(lam c (error))",
            "--inputs", "spending", equivalence=False)
        self.assertEqual(code, 1, report)
        witness = report["counterexample"]
        self.assertTrue(witness["replayed"])
        context = witness["input"]
        self.assertEqual(context["constructor"], 0)
        self.assertEqual(len(context["fields"]), 3)
        self.assertEqual(len(context["fields"][0]["fields"]), 16)
        self.assertEqual(context["fields"][2]["constructor"], 1)
        self.assertEqual(len(context["fields"][2]["fields"]), 2)
        self.assertNotIn("restricted to case", report["input_domain"])

    def test_verdict_exit_codes(self):
        for left, right, flags, expected_code, expected_verdict in [
                ("(lam n n)", "(lam n n)", [], 0, "equivalent"),
                ("(lam n (con integer 1))", "(lam n (con integer 2))", [], 1, "inequivalent"),
                ("(lam n n)", "(lam n n)", ["--max-steps", "0"], 2, "inconclusive")]:
            with self.subTest(verdict=expected_verdict):
                code, report = self.invoke(left, right, *flags)
                self.assertEqual(code, expected_code, report)
                self.assertEqual(report["verdict"], expected_verdict)

    def test_invalid_arguments_are_tool_errors(self):
        for args in [
                ["old", "new"],
                ["old", "new", "--inputs", "spending", "--language", "PlutusV2"],
                ["old", "new", "--inputs", "spending", "--case", "0"],
                ["old", "new", "--budget", "1", "1", "--left-steps", "1"],
                ["old", "new", "--budget", "-1", "1"],
                ["old", "new", "--budget", "1", "1", "--equivalence"],
                ["--unknown-option"],
                ["left", "right", "--inputs", "integer", "--case", "0"],
                ["left", "right", "--inputs", "escrow-refund", "--case", "72"],
                ["left", "right", "--inputs", "vesting-full", "--variation", "secret-wrong"],
                ["left", "right", "--inputs", "htlc-claim", "--variation", "state-accepted"],
                ["left", "right", "--inputs", "vesting-full", "--variation", "fee-positive,secret-wrong"],
                ["left", "right", "--inputs", "vesting-full", "--variation", "fee-positive,"],
                ["left", "right", "--inputs", "vesting-full", "--variation", ""]]:
            with self.subTest(args=args):
                if args != ["old", "new"] and "--budget" not in args:
                    args += ["--budget", "1", "1"]
                result = subprocess.run(
                    [str(CLI), *args, "--json"],
                    capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 3, result.stdout)
                self.assertEqual(json.loads(result.stdout)["verdict"], "error")

    def test_vesting_variation_reaches_worker_and_replay(self):
        # A valid spending datum can change freely; the selected variation
        # changes its total while preserving the ledger context field encodings.
        inspect = reject_data_at([2, 1, 0, 2], "I 1001")
        code, report = self.invoke(inspect, "(lam c (con unit ()))",
                                   "--inputs", "vesting-partial", "--case", "81",
                                   "--variation", "datum-total", "--max-steps", "600")
        self.assertEqual(code, 1, report)
        self.assertEqual(report["verdict"], "inequivalent")
        self.assertTrue(report["counterexample"]["replayed"], report)
        context = report["counterexample"]["input"]
        datum = context["fields"][2]["fields"][1]["fields"][0]
        self.assertEqual(datum["fields"][2], {"int": 1001})
        self.assertIn("context variation: datum-total:", report["input_domain"])

    def test_shared_and_specific_variations_compose_in_either_order(self):
        inspect = reject_data_at([2, 1, 0, 2], "I 1001")
        for selection in ["fee-positive,datum-total", "datum-total, fee-positive"]:
            with self.subTest(selection=selection):
                code, report = self.invoke(inspect, "(lam c (con unit ()))",
                                           "--inputs", "vesting-partial", "--case", "81",
                                           "--variation", selection, "--max-steps", "600")
                self.assertEqual(code, 1, report)
                self.assertTrue(report["counterexample"]["replayed"], report)
                fields = report["counterexample"]["input"]["fields"]
                self.assertEqual(fields[0]["fields"][3], {"int": 1})
                self.assertEqual(fields[2]["fields"][1]["fields"][0]["fields"][2], {"int": 1001})
                self.assertIn(f"context variation: {selection}:", report["input_domain"])

    def test_later_variation_wins_for_overlapping_fields(self):
        for selection, expected, data in [
                ("redeemer-fields,redeemer-tag", {"constructor": 2, "fields": []}, "Constr 2 []"),
                ("redeemer-tag,redeemer-fields", {"constructor": 2, "fields": [{"int": 42}]},
                 "Constr 2 [I 42]")]:
            with self.subTest(selection=selection):
                code, report = self.invoke(reject_data_at([1], data), "(lam c (con unit ()))",
                                           "--inputs", "htlc-claim", "--case", "10",
                                           "--variation", selection, "--max-steps", "400")
                self.assertEqual(code, 1, report)
                self.assertTrue(report["counterexample"]["replayed"], report)
                self.assertEqual(report["counterexample"]["input"]["fields"][1], expected)

    def test_composed_lean_queries_can_be_checked_again(self):
        with tempfile.TemporaryDirectory(prefix="uplc composed export ") as directory:
            root = Path(directory)
            left, right, emitted = root / 'left "script".uplc', root / "right.uplc", root / "queries.lean"
            left.write_text("(program 1.1.0 " + reject_data_at([2, 1, 0, 2], "I 1001") + ")")
            right.write_text("(program 1.1.0 (lam c (con unit ())))")
            result = subprocess.run(
                [str(CLI), str(left), str(right), "--format", "textual", "--inputs", "vesting-partial",
                 "--case", "81", "--variation", "datum-total,fee-positive", "--equivalence", "--max-steps", "600",
                 "--timeout", "5", "--wall-timeout", "30", "--emit-lean", str(emitted), "--json"],
                cwd=ROOT, capture_output=True, text=True, timeout=40)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            checked = subprocess.run(
                ["lake", "env", "lean", "--memory=8192", str(emitted)],
                cwd=ROOT, capture_output=True, text=True, timeout=60)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_text_report_shows_witness(self):
        code, output = self.invoke("(lam n (con integer 1))", "(lam n (con integer 2))",
                                   json_output=False)
        self.assertEqual(code, 1, output)
        self.assertIn("Counterexample:", output)
        self.assertIn('"replayed": true', output)
        self.assertIn('"input":', output)

    def test_htlc_variation_and_case_reach_worker_and_replay(self):
        # Reject an empty signature list. Restricting to a signed case removes
        # that witness, which must not be recovered from another boundary case.
        inspect = reject_data_at([0, 8], "List []")
        for mode in ["htlc-refund", "htlc-claim"]:
            for case, expected_code in [(8, 1), (10, 0)]:
                with self.subTest(mode=mode, case=case):
                    code, report = self.invoke(inspect, "(lam c (con unit ()))",
                                               "--inputs", mode, "--case", str(case),
                                               "--max-steps", "400")
                    self.assertEqual(code, expected_code, report)
                    if expected_code == 1:
                        self.assertTrue(report["counterexample"]["replayed"], report)
            # Changing the redeemer must be reflected in the concrete witness.
            reject_tag_two = reject_data_at([1], "Constr 2 []")
            code, report = self.invoke(reject_tag_two, "(lam c (con unit ()))",
                                       "--inputs", mode, "--case", "10",
                                       "--variation", "redeemer-tag", "--max-steps", "200")
            self.assertEqual(code, 1, report)
            self.assertTrue(report["counterexample"]["replayed"], report)
            self.assertEqual(report["counterexample"]["input"]["fields"][1],
                             {"constructor": 2, "fields": []})
            self.assertIn("context variation: redeemer-tag:", report["input_domain"])

    def test_malformed_script_is_tool_error(self):
        code, report = self.invoke("not uplc", "(lam n n)")
        self.assertEqual(code, 3, report)

    @unittest.skipUnless(hasattr(os, "mkfifo"), "requires POSIX named pipes")
    def test_wall_timeout_stops_blocked_worker(self):
        with tempfile.TemporaryDirectory() as directory:
            blocked = Path(directory) / "blocked.uplc"
            os.mkfifo(blocked)
            result = subprocess.run(
                [str(CLI), str(blocked), str(blocked), "--format", "textual",
                 "--budget", "1000000", "10000", "--wall-timeout", "1", "--json"],
                capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 2, result.stdout)
            self.assertEqual(json.loads(result.stdout)["verdict"], "inconclusive")


if __name__ == "__main__":
    unittest.main()
