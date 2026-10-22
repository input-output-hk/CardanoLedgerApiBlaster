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


def reject_data_at(path, expected):
    term = "c"
    for index in path:
        fields = f"[(force (force (builtin sndPair))) [(builtin unConstrData) {term}]]"
        for _ in range(index):
            fields = f"[(force (builtin tailList)) {fields}]"
        term = f"[(force (builtin headList)) {fields}]"
    return ("(lam c (force [[[(force (builtin ifThenElse)) "
            f"[[(builtin equalsData) {term}] (con data ({expected}))]] "
            "(delay (error))] (delay (con unit ()))]))")


class CheckerProcess(unittest.TestCase):
    def invoke(self, left, right, *flags, json_output=True):
        with tempfile.TemporaryDirectory(prefix="uplc cli tests ") as directory:
            # Exercise spaces and quotes while running outside the repository.
            paths = [Path(directory) / 'left "script".uplc', Path(directory) / 'right.uplc']
            for path, term in zip(paths, (left, right)):
                path.write_text(f"(program 1.1.0 {term})")
            result = subprocess.run(
                [str(CLI),
                 *(str(path) for path in paths), "--format", "textual",
                 "--max-steps", "40", "--wall-timeout", "30",
                 *(["--json"] if json_output else []), *flags],
                cwd=directory, capture_output=True, text=True, timeout=90)
            return result.returncode, json.loads(result.stdout) if json_output else result.stdout

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
                ["--unknown-option"],
                ["left", "right", "--inputs", "integer", "--case", "0"],
                ["left", "right", "--inputs", "escrow-refund", "--case", "72"],
                ["left", "right", "--inputs", "vesting-full", "--variation", "secret-wrong"],
                ["left", "right", "--inputs", "htlc-claim", "--variation", "state-accepted"],
                ["left", "right", "--inputs", "vesting-full", "--variation", "fee-positive,secret-wrong"],
                ["left", "right", "--inputs", "vesting-full", "--variation", "fee-positive,"],
                ["left", "right", "--inputs", "vesting-full", "--variation", ""]]:
            with self.subTest(args=args):
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
                 "--case", "81", "--variation", "datum-total,fee-positive", "--max-steps", "600",
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
                 "--wall-timeout", "1", "--json"],
                capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 2, result.stdout)
            self.assertEqual(json.loads(result.stdout)["verdict"], "inconclusive")


if __name__ == "__main__":
    unittest.main()
