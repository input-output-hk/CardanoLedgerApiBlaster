"""Process-level checks for stdout, exit codes, argument errors and supervision.

Functional acceptance, model replay and context tests live in Tests/Equivalence/*.lean.
"""

import json
import os
from pathlib import Path
import selectors
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


class CheckerProcess(unittest.TestCase):
    def test_progress_identifies_query_order_without_polluting_json(self):
        for skip in [False, True]:
            with self.subTest(skip=skip), tempfile.TemporaryDirectory() as directory:
                old, new = Path(directory) / "old.uplc", Path(directory) / "new.uplc"
                for path in (old, new):
                    path.write_text("(program 1.1.0 (lam c (con unit ())))")
                result = subprocess.run([str(CLI), str(old), str(new), "--format", "textual",
                    "--budget", "1000000", "10000", "--json",
                    *(["--skip-old-rejected"] if skip else [])],
                    cwd=ROOT, capture_output=True, text=True, timeout=30)
                report = json.loads(result.stdout)
                self.assertEqual((result.returncode, report["verdict"]), (0, "preserved"), report)
                stages = ["Starting: loading OLD script", "Starting: loading NEW script",
                          "Starting: constructing a ledger-model-valid domain witness",
                          "Starting: preparing symbolic checker", "Starting: preparing symbolic input families"]
                if skip:
                    stages += ["Skipping: old_rejected (--skip-old-rejected)"]
                stages += ["Starting: proving OLD-to-NEW acceptance preservation [acceptance_preserved]",
                           "Skipping: no_acceptance_regression (derived from acceptance_preserved)"]
                if not skip:
                    stages += ["Starting: looking for an OLD-accepting replay",
                               "Skipping: old_rejected (OLD acceptance confirmed by native replay)"]
                stages += ["Starting: validating replay witnesses and classifying results"]
                offset = 0
                for stage in stages:
                    position = result.stderr.find(stage, offset)
                    self.assertGreaterEqual(position, offset, result.stderr)
                    offset = position + len(stage)
                if skip:
                    self.assertNotIn("checking whether OLD rejects every input", result.stderr)
                self.assertNotIn("[uplc_equiv]", result.stdout)

    def test_deferred_rejection_export(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            old, new, emitted = root / "old.uplc", root / "new.uplc", root / "rejects.lean"
            old.write_text("(program 1.1.0 (lam c (error)))")
            new.write_text(old.read_text())
            args = [str(CLI), "--raw-context", str(old), str(new), "--format", "textual",
                    "--inputs", "htlc-claim", "--case", "45", "--equivalence",
                    "--budget", "10000000000", "14000000", "--timeout", "5",
                    "--wall-timeout", "30", "--json"]
            result = subprocess.run(args + ["--emit-lean", str(emitted)], cwd=ROOT,
                                    capture_output=True, text=True, timeout=40)
            report = json.loads(result.stdout)
            self.assertEqual((result.returncode, report["verdict"]), (4, "vacuously_equivalent"), report)
            self.assertIn("Derived: acceptance_preserved (from old_rejected)", result.stderr)
            self.assertLess(result.stderr.index("[acceptance_preserved]"),
                            result.stderr.index("[old_rejected]"))
            source = emitted.read_text()
            self.assertIn("-- old_rejected,", source)
            self.assertNotIn("-- new_rejected,", source)
            self.assertNotIn("-- acceptance_preserved,", source)
            self.assertNotIn("-- no_acceptance_regression,", source)
            self.assertIn("(reconstruct-proofs: 0)", source)
            checked = subprocess.run(["lake", "env", "lean", "--memory=8192", str(emitted)],
                                     cwd=ROOT, capture_output=True, text=True, timeout=60)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def invoke(self, left, right, *flags, json_output=True):
        with tempfile.TemporaryDirectory(prefix="uplc cli tests ") as directory:
            # Exercise spaces and quotes while running outside the repository.
            paths = [Path(directory) / 'left "script".uplc', Path(directory) / 'right.uplc']
            for path, term in zip(paths, (left, right)):
                path.write_text(f"(program 1.1.0 {term})")
            result = subprocess.run(
                [str(CLI), "--inputs", "data", "--raw-context",
                 *(str(path) for path in paths), "--format", "textual",
                 "--budget", "1000000", "10000",
                 "--wall-timeout", "30",
                 *(["--json"] if json_output else []), *flags],
                cwd=directory, capture_output=True, text=True, timeout=90)
            return result.returncode, json.loads(result.stdout) if json_output else result.stdout

    def test_composed_context_witness_and_export(self):
        inspect = reject_data_at([2, 1, 0, 2], "I 1001")
        for symmetric in [False, True]:
            with self.subTest(symmetric=symmetric), tempfile.TemporaryDirectory() as directory:
                emitted = Path(directory) / "acceptance.lean"
                old, new = Path(directory) / 'old "script".uplc', Path(directory) / "new.uplc"
                accept = "(lam c (con unit ()))"
                for path, term in [(old, inspect if symmetric else accept),
                                   (new, accept if symmetric else inspect)]:
                    path.write_text(f"(program 1.1.0 {term})")
                result = subprocess.run([str(CLI), "--raw-context", str(old), str(new), "--format", "textual",
                    "--inputs", "vesting-partial", "--case", "81",
                    "--variation", "datum-total,fee-positive", "--budget", "100000000", "1000000",
                    *(["--equivalence"] if symmetric else []),
                    "--timeout", "5", "--wall-timeout", "30", "--emit-lean", str(emitted), "--json"],
                    cwd=ROOT, capture_output=True, text=True, timeout=40)
                report = json.loads(result.stdout)
                self.assertEqual((result.returncode, report["verdict"]),
                                 (1, "inequivalent" if symmetric else "regression"), report)
                witness = report["counterexample"]
                self.assertTrue(witness["replayed"], report)
                self.assertEqual(witness["old"]["accepts"], not symmetric)
                self.assertEqual(witness["new"]["accepts"], symmetric)
                self.assertEqual(witness["direction"], "new_to_old" if symmetric else "old_to_new")
                checked = subprocess.run(["lake", "env", "lean", "--memory=8192", str(emitted)],
                                         cwd=ROOT, capture_output=True, text=True, timeout=60)
                self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_text_report_identifies_budget_model_and_witness(self):
        code, output = self.invoke("(lam c (con unit ()))", "(lam c (error))",
                                   json_output=False)
        self.assertEqual(code, 1, output)
        self.assertIn("regression:", output)
        self.assertIn('Budget: {"cpu":1000000,"memory":10000}', output)
        self.assertIn("Cost model: bundled post-Conway E", output)
        self.assertIn("Counterexample:", output)
        self.assertIn('"replayed": true', output)
        self.assertIn('"input":', output)

    def test_widening_deduplicates_erased_case_distinctions(self):
        for symmetric in [False, True]:
            with self.subTest(symmetric=symmetric), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                old, new, emitted = root / "old.uplc", root / "new.uplc", root / "check.lean"
                for path in [old, new]:
                    path.write_text("(program 1.1.0 (lam c (con unit ())))")
                result = subprocess.run([str(CLI), "--raw-context", str(old), str(new), "--format", "textual",
                    "--inputs", "vesting-partial", "--variation", "time-any,inputs-any,outputs-any,signers-any",
                    "--budget", "100000000", "1000000", "--wall-timeout", "30",
                    *(["--equivalence"] if symmetric else []),
                    "--emit-lean", str(emitted), "--json"],
                    cwd=ROOT, capture_output=True, text=True, timeout=60)
                report = json.loads(result.stdout)
                self.assertEqual((result.returncode, report["verdict"]),
                                 (0, "equivalent" if symmetric else "preserved"), report)
                # 96 cases collapse to four families for each preservation proof.
                # No-regression queries follow from those proofs and are omitted.
                source = emitted.read_text()
                names = ["acceptance_preserved"]
                if symmetric:
                    names += ["reverse_acceptance_preserved"]
                for name in names:
                    self.assertEqual(source.count(f"-- {name}, case "), 4)
                for name in ["no_acceptance_regression", "reverse_no_acceptance_regression",
                             "old_rejected", "new_rejected"]:
                    self.assertNotIn(f"-- {name}, case ", source)
                checked = subprocess.run(["lake", "env", "lean", "--memory=8192", str(emitted)],
                                         cwd=ROOT, capture_output=True, text=True, timeout=60)
                self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_invalid_arguments_are_tool_errors(self):
        with tempfile.TemporaryDirectory() as directory:
            old_path, new_path = Path(directory) / "old.uplc", Path(directory) / "new.uplc"
            for path in [old_path, new_path]:
                path.write_text("(program 1.1.0 (lam c (con unit ())))")
            for args in [
                    ["old", "new"],
                    ["old", "new", "--inputs", "spending", "--language", "PlutusV2"],
                    ["old", "new", "--inputs", "spending", "--case", "0"],
                    ["old", "new", "--budget", "1", "1", "--left-steps", "1"],
                    ["old", "new", "--budget", "-1", "1"],
                    ["old", "new", "--equivalence"],
                    ["old", "new", "--unknown-option"],
                    ["left", "right", "--inputs", "integer", "--case", "0"],
                    ["left", "right", "--inputs", "escrow-refund", "--case", "72"],
                    ["left", "right", "--inputs", "vesting-full", "--variation", "secret-wrong"],
                    ["left", "right", "--inputs", "htlc-claim", "--variation", "state-accepted"],
                    ["left", "right", "--inputs", "vesting-full", "--variation", "fee-positive,secret-wrong"],
                    ["left", "right", "--inputs", "vesting-full", "--variation", "fee-positive,"],
                    ["left", "right", "--inputs", "vesting-full", "--variation", ""]]:
                with self.subTest(args=args):
                    if args not in [["old", "new"], ["old", "new", "--equivalence"]] and "--budget" not in args:
                        args += ["--budget", "1", "1"]
                    args = [str(old_path) if a in ("old", "left") else
                            str(new_path) if a in ("new", "right") else a for a in args]
                    result = subprocess.run(
                        [str(CLI), "--inputs", "data", "--raw-context", *args, "--json"],
                        capture_output=True, text=True, timeout=10)
                    self.assertEqual(result.returncode, 3, result.stdout)
                    self.assertEqual(json.loads(result.stdout)["verdict"], "error")

    def test_malformed_script_is_tool_error(self):
        code, report = self.invoke("not uplc", "(lam n n)")
        self.assertEqual(code, 3, report)

    @unittest.skipUnless(hasattr(os, "mkfifo"), "requires POSIX named pipes")
    def test_wall_timeout_stops_blocked_worker(self):
        with tempfile.TemporaryDirectory() as directory:
            blocked = Path(directory) / "blocked.uplc"
            os.mkfifo(blocked)
            with subprocess.Popen(
                [str(CLI), "--inputs", "data", "--raw-context", str(blocked), str(blocked), "--format", "textual",
                 "--budget", "1000000", "10000", "--wall-timeout", "5", "--json"],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) as process:
                with selectors.DefaultSelector() as selector:
                    selector.register(process.stderr, selectors.EVENT_READ)
                    self.assertTrue(selector.select(timeout=4), "Progress was buffered until worker completion")
                line = process.stderr.readline()
                self.assertIn("Starting: loading OLD script", line)
                self.assertIsNone(process.poll(), "Worker finished before live progress was observed")
                stdout, _ = process.communicate(timeout=10)
                self.assertEqual(process.returncode, 2, stdout)
                self.assertEqual(json.loads(stdout)["verdict"], "inconclusive")


if __name__ == "__main__":
    unittest.main()
