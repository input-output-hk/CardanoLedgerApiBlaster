"""Process-level checks for stdout, exit codes, argument errors and supervision.

Functional acceptance, model replay and context tests live in Tests/Equivalence/*.lean.
"""

import hashlib
import json
import contextlib
import sys
import os
import re
from pathlib import Path
import selectors
import shutil
import signal
import subprocess
import tempfile
import time
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


@contextlib.contextmanager
def fake_z3(mode):
    """Protocol-level solver doubles make timeout/unknown tests deterministic."""
    with tempfile.TemporaryDirectory(prefix="uplc fake solver ") as directory:
        solver = Path(directory) / "z3"
        solver.write_text(f"#!{sys.executable}\n" + """
import sys
import time
if '-version' in sys.argv:
    print('Z3 version 5.3.4 - test solver')
    raise SystemExit(0)
mode = MODE
command = ''
balance = 0
for line in sys.stdin:
    command += line
    balance += line.count('(') - line.count(')')
    if balance > 0:
        continue
    if command.startswith('(check-sat'):
        if mode == 'error':
            print('(error "test solver failure")', flush=True)
            raise SystemExit(1)
        if mode == 'block':
            time.sleep(30)
        print('unknown', flush=True)
    elif command.startswith('(get-info :reason-unknown'):
        print('(:reason-unknown "' + mode + '")', flush=True)
    elif command.startswith('(set-simplifier'):
        pass  # Z3's set-simplifier extension does not print success.
    elif command.startswith('(exit'):
        break
    else:
        print('success', flush=True)
    command = ''
    balance = 0
""".replace('MODE', repr(mode)))
        solver.chmod(0o755)
        yield {**os.environ, 'PATH': directory + os.pathsep + os.environ.get('PATH', '')}


@contextlib.contextmanager
def portfolio_z3(default_mode, seeded_mode='real'):
    """Inject worker timing/failures through a proxy that retains real Z3 models."""
    real_z3 = shutil.which('z3')
    if real_z3 is None:
        raise RuntimeError('Portfolio tests require z3 on PATH')
    fixture = ROOT / 'equivalence/test_fixtures/z3_proxy.py'
    with tempfile.TemporaryDirectory(prefix='uplc portfolio solver ') as directory:
        solver = Path(directory) / 'z3'
        solver.write_text(f'#!{sys.executable}\n' + fixture.read_text())
        solver.chmod(0o755)
        yield {
            **os.environ,
            'PATH': directory + os.pathsep + os.environ.get('PATH', ''),
            'UPLC_TEST_Z3_REAL': real_z3,
            'UPLC_TEST_Z3_DEFAULT_MODE': default_mode,
            'UPLC_TEST_Z3_SEEDED_MODE': seeded_mode,
        }, Path(directory)


class CheckerProcess(unittest.TestCase):
    def test_blueprint_inputs_and_lean_export(self):
        script = ROOT / "equivalence/examples/fibonacci/Plinth_1.67.0.0_Unisay.cbor_hex"
        code = script.read_text().strip()
        validator = {
            "id": "fib",
            "title": "Fibonacci example",
            "redeemer": {"schema": {"dataType": "integer"}},
            "compiledCode": code,
            "hash": hashlib.blake2b(b"\x03" + bytes.fromhex(code), digest_size=28).hexdigest(),
        }
        blueprint = {
            "preamble": {"title": "Example", "version": "1.0.0", "plutusVersion": "v3"},
            "validators": [validator],
        }
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "plutus.json"
            named = Path(directory) / "blueprint.txt"
            emitted = Path(directory) / "check.lean"
            path.write_text(json.dumps(blueprint))

            def check(left, right, *args):
                result = subprocess.run(
                    [str(CLI), str(left), str(right), "--mode", "function", "--json", *args],
                    cwd=ROOT, capture_output=True, text=True, timeout=30,
                )
                return result.returncode, json.loads(result.stdout)

            status, report = check(path, script, "--emit-lean", str(emitted))
            self.assertEqual(status, 0, report)
            self.assertEqual(report["verdict"], "equivalent")
            checked = subprocess.run(
                ["lake", "env", "lean", str(emitted)],
                cwd=ROOT, capture_output=True, text=True, timeout=30,
            )
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

            other_code = (script.parent / "Plinth_1.61.0.0_Unisay.cbor_hex").read_text().strip()
            self.assertNotEqual(other_code, code)
            blueprint["validators"].insert(0, {
                **validator, "id": "other", "title": "Other example", "compiledCode": other_code,
                "hash": hashlib.blake2b(b"\x03" + bytes.fromhex(other_code), digest_size=28).hexdigest(),
            })
            named.write_text(json.dumps(blueprint))
            status, report = check(script, named, "--format-new", "blueprint")
            self.assertEqual(status, 3, report)
            self.assertIn("multiple validators with compiledCode", report["explanation"])
            for selector in ("fib", "Fibonacci example"):
                status, report = check(script, named, "--format-new", "blueprint",
                                       "--validator-new", selector)
                self.assertEqual(status, 0, report)
                self.assertEqual(report["derived_queries"]["function_equivalent"], "program_identity")

            export = Path(directory) / "evidence"
            named_bytes = named.read_bytes()
            status, report = check(path, named, "--format-new", "blueprint",
                                   "--validator-new", "fib", "--emit-assurance", str(export))
            self.assertEqual(status, 0, report)
            assurance_path = export / "assurance.json"
            assurance = json.loads(assurance_path.read_text())
            claim = assurance["properties"][0]
            evidence = claim["evidence"][0]
            self.assertEqual(claim["scope"]["validators"], ["fib"])
            self.assertEqual(evidence["outcome"], "verified")
            self.assertEqual(evidence["scriptHash"], validator["hash"])
            self.assertEqual(assurance["blueprint"]["hash"]["digest"],
                             hashlib.sha256(named_bytes).hexdigest())
            artifact = export / evidence["artifact"]["uri"]
            self.assertEqual(evidence["artifact"]["hash"]["digest"],
                             hashlib.sha256(artifact.read_bytes()).hexdigest())
            comparison = json.loads(artifact.read_text())
            self.assertEqual(comparison["old"]["scriptHash"], validator["hash"])
            self.assertEqual(comparison["new"]["scriptHash"], validator["hash"])
            self.assertEqual(comparison["result"], report)
            self.assertEqual(comparison["settings"]["inputs"], "integer")
            self.assertEqual(named.read_bytes(), named_bytes)
            self.assertEqual(path.read_text(), json.dumps({**blueprint, "validators": [validator]}))
            status, report = check(path, named, "--format-new", "blueprint",
                                   "--validator-new", "fib", "--emit-assurance", str(export))
            self.assertEqual(status, 3, report)
            self.assertIn("already exists", report["explanation"])
            self.assertEqual(json.loads(assurance_path.read_text()), assurance)

            verify = Path(directory) / "verify.lean"
            verify.write_text("import PlutusCore.UPLC\n"
                              f"#verify_blueprint Comparison {json.dumps(str(assurance_path))}\n")
            checked = subprocess.run(
                ["lake", "env", "lean", str(verify)], cwd=ROOT,
                capture_output=True, text=True, timeout=30,
            )
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            self.assertIn("natural-language only", checked.stdout + checked.stderr)

            status, report = check(path, script, "--language", "PlutusV2")
            self.assertEqual(status, 3, report)
            self.assertIn("this input uses PlutusV2", report["explanation"])

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
                self.assertFalse(report['bounded'])
                self.assertEqual(report['step_limit_kind'], 'analysis_guard')
                stages = ["Starting: loading OLD script", "Starting: loading NEW script",
                          "Starting: constructing a ledger-model-valid domain witness",
                          "Starting: preparing symbolic checker"]
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
                self.assertNotIn("[uplc_equiv]", result.stderr)
                times = []
                for line in result.stderr.splitlines():
                    match = re.match(r"^\[(\d+\.\d{3})s\] ", line)
                    self.assertIsNotNone(match, line)
                    times.append(float(match.group(1)))
                self.assertTrue(times, result.stderr)
                self.assertEqual(times, sorted(times))

    def solver_case(self, env, *, timeout=5, wall_timeout=10, json_output=True):
        with tempfile.TemporaryDirectory() as directory:
            paths = [Path(directory) / 'old.uplc', Path(directory) / 'new.uplc']
            for path, value in zip(paths, [42, 43]):
                term = reject_data_at([2, 1, 0], f"I {value}")
                path.write_text(f"(program 1.1.0 {term})")
            return subprocess.run([str(CLI), *(str(p) for p in paths),
                '--inputs', 'valid-context', '--bounded', '--steps', '1000', '--timeout', str(timeout),
                '--max-inputs', '1', '--max-outputs', '1', '--max-signers', '1',
                '--wall-timeout', str(wall_timeout), *(['--json'] if json_output else [])],
                cwd=ROOT, env=env, capture_output=True, text=True, timeout=wall_timeout+8)

    def test_solver_timeout_is_distinguished_from_other_unknown(self):
        for reason in ['timeout', 'incomplete']:
            with self.subTest(reason=reason), fake_z3(reason) as env:
                result = self.solver_case(env)
                report = json.loads(result.stdout)
                self.assertEqual(result.returncode, 2, report)
                diagnostic = report['query_diagnostics']['acceptance_preserved']
                self.assertEqual(diagnostic['phase'], 'z3')
                self.assertEqual(diagnostic['reason'], reason)
                self.assertEqual(diagnostic['status'], 'timeout' if reason == 'timeout' else 'unknown')
                if reason == 'timeout':
                    self.assertIn('Z3 timed out after 5s [acceptance_preserved]', result.stderr)
                else:
                    self.assertNotIn('timed out', result.stderr)
        with fake_z3('timeout') as env:
            result = self.solver_case(env, json_output=False)
            self.assertIn('acceptance_preserved: Z3 timed out after 5s', result.stdout)
            self.assertIn('Execution step bound: 1000', result.stdout)
        with fake_z3('error') as env:
            result = self.solver_case(env)
            report = json.loads(result.stdout)
            self.assertEqual(result.returncode, 3, report)
            self.assertIn('test solver failure', report['explanation'])
            self.assertNotIn('broken pipe', report['explanation'])

    def test_wall_timeout_identifies_z3(self):
        with fake_z3('block') as env:
            result = self.solver_case(env, timeout=15, wall_timeout=5)
        report = json.loads(result.stdout)
        self.assertEqual(result.returncode, 2, report)
        self.assertEqual(report['timeout']['phase'], 'z3')
        self.assertEqual(report['timeout']['query'], 'acceptance_preserved')
        self.assertIn('during Z3 solving', report['explanation'])

    def test_wall_timeout_identifies_preprocessing(self):
        with tempfile.TemporaryDirectory() as directory:
            old, new = Path(directory) / 'loop.uplc', Path(directory) / 'unit.uplc'
            old.write_text('(program 1.1.0 (lam c [(lam x [x x]) (lam x [x x])]))')
            new.write_text('(program 1.1.0 (lam c (con unit ())))')
            result = subprocess.run([str(CLI), str(old), str(new), '--input', 'valid-context',
                '--bounded', '--steps', '1000000000', '--wall-timeout', '4', '--json'],
                cwd=ROOT, capture_output=True, text=True, timeout=10)
        report = json.loads(result.stdout)
        self.assertEqual(result.returncode, 2, report)
        self.assertEqual(report['timeout']['phase'], 'preprocessing')
        self.assertEqual(report['timeout']['query'], 'acceptance_preserved')
        self.assertIn('during preprocessing', report['explanation'])

    def test_lean_export_embeds_binary_flat_input(self):
        cbor_path = ROOT / "equivalence/examples/fibonacci/Plinth_1.67.0.0_Unisay.cbor_hex"
        cbor = bytes.fromhex(cbor_path.read_text())
        self.assertEqual(cbor[:2], bytes([0x58, len(cbor) - 2]))
        flat = cbor[2:]
        with self.assertRaises(UnicodeDecodeError):
            flat.decode("utf-8")
        with tempfile.TemporaryDirectory() as directory:
            raw = Path(directory) / "fibonacci.flat"
            emitted = Path(directory) / "check.lean"
            raw.write_bytes(flat)
            result = subprocess.run(
                [str(CLI), str(raw), str(cbor_path), "--mode", "function",
                 "--format-old", "flat", "--emit-lean", str(emitted), "--json"],
                cwd=ROOT, capture_output=True, text=True, timeout=15)
            report = json.loads(result.stdout)
            self.assertEqual((result.returncode, report["verdict"]), (0, "equivalent"), report)
            raw.unlink()
            checked = subprocess.run(["lake", "env", "lean", str(emitted)], cwd=ROOT,
                                     capture_output=True, text=True, timeout=30)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_lean_export_rejects_input_paths(self):
        with tempfile.TemporaryDirectory() as directory:
            old, new = (Path(directory) / name for name in ["old.uplc", "new.uplc"])
            source = "(program 1.1.0 (lam c (con unit ())))"
            for script in [old, new]:
                script.write_text(source)
            for output in [str(old), os.path.join(directory, ".", new.name)]:
                with self.subTest(output=output):
                    result = subprocess.run(
                        [str(CLI), str(old), str(new), "--mode", "function",
                         "--emit-lean", output, "--json"],
                        cwd=ROOT, capture_output=True, text=True, timeout=10)
                    report = json.loads(result.stdout)
                    self.assertEqual((result.returncode, report["verdict"]), (3, "error"), report)
                    self.assertIn("--emit-lean would overwrite an input script", report["explanation"])
                    self.assertEqual(old.read_text(), source)
                    self.assertEqual(new.read_text(), source)

    def test_lean_export_replaces_hard_link_without_changing_input(self):
        with tempfile.TemporaryDirectory() as directory:
            old, new, emitted = (Path(directory) / name for name in ["old.uplc", "new.uplc", "check.lean"])
            source = "(program 1.1.0 (lam c (con unit ())))"
            old.write_text(source)
            new.write_text(source)
            os.link(old, emitted)
            result = subprocess.run(
                [str(CLI), str(old), str(new), "--mode", "function", "--emit-lean", str(emitted), "--json"],
                cwd=ROOT, capture_output=True, text=True, timeout=10)
            report = json.loads(result.stdout)
            self.assertEqual((result.returncode, report["verdict"]), (0, "equivalent"), report)
            self.assertEqual(old.read_text(), source)
            self.assertFalse(old.samefile(emitted))
            checked = subprocess.run(["lake", "env", "lean", str(emitted)], cwd=ROOT,
                                     capture_output=True, text=True, timeout=30)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_deferred_rejection_export(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            old, new, emitted = root / "old.uplc", root / "new.uplc", root / "rejects.lean"
            old.write_text("(program 1.1.0 (lam c (error)))")
            new.write_text(old.read_text())
            args = [str(CLI), str(old), str(new), "--format", "textual",
                    "--inputs", "valid-context", "--equivalence",
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
            self.assertIn("-- old_rejected\n", source)
            self.assertNotIn("-- new_rejected\n", source)
            self.assertNotIn("-- acceptance_preserved\n", source)
            self.assertNotIn("-- no_acceptance_regression\n", source)
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
                [str(CLI), "--inputs", "valid-context",
                 "--max-inputs", "1", "--max-outputs", "1", "--max-signers", "1",
                 *(str(path) for path in paths), "--format", "textual",
                 "--budget", "1000000", "10000",
                 "--wall-timeout", "30",
                 *(["--json"] if json_output else []), *flags],
                cwd=directory, capture_output=True, text=True, timeout=90)
            return result.returncode, json.loads(result.stdout) if json_output else result.stdout

    def test_generic_spending_witness_and_export(self):
        inspect = reject_data_at([0, 3], "I 42")
        for symmetric in [False, True]:
            with self.subTest(symmetric=symmetric), tempfile.TemporaryDirectory() as directory:
                emitted = Path(directory) / "acceptance.lean"
                old, new = Path(directory) / 'old "script".uplc', Path(directory) / "new.uplc"
                accept = "(lam c (con unit ()))"
                for path, term in [(old, inspect if symmetric else accept),
                                   (new, accept if symmetric else inspect)]:
                    path.write_text(f"(program 1.1.0 {term})")
                result = subprocess.run([str(CLI), str(old), str(new), "--format", "textual",
                    "--inputs", "valid-context", "--budget", "100000000", "1000000",
                    "--max-inputs", "1", "--max-outputs", "1", "--max-signers", "1",
                    *(["--equivalence"] if symmetric else []),
                    "--timeout", "15", "--wall-timeout", "60", "--emit-lean", str(emitted), "--json"],
                    cwd=ROOT, capture_output=True, text=True, timeout=70)
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

    def test_configured_context_export_and_scope(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            old, new, emitted = root / "old.uplc", root / "new.uplc", root / "context.lean"
            old.write_text("(program 1.1.0 (lam c (con unit ())))")
            new.write_text(old.read_text())
            result = subprocess.run([str(CLI), str(old), str(new), "--format", "textual",
                "--inputs", "valid-context", "--max-inputs", "3", "--max-outputs", "1",
                "--max-signers", "0", "--bounded", "--steps", "1000",
                "--timeout", "10", "--wall-timeout", "30", "--emit-lean", str(emitted), "--json"],
                cwd=ROOT, capture_output=True, text=True, timeout=40)
            report = json.loads(result.stdout)
            self.assertEqual((result.returncode, report["verdict"]), (0, "bounded_preserved"), report)
            self.assertEqual(report["context_limits"]["inputs_min"], 0)
            self.assertEqual(report["context_limits"]["inputs_max"], 3)
            self.assertEqual(report["context_limits"]["outputs_max"], 1)
            self.assertEqual(report["context_limits"]["signers_max"], 0)
            self.assertIsNone(report["context_limits"]["integer_bits"])
            self.assertTrue(report["old_acceptance_witness"]["replayed"])
            self.assertTrue(report["old_acceptance_witness"]["ledger_validity"]["valid"])
            self.assertIn("Equivalence.ValidContext", emitted.read_text())
            self.assertIn("Ledger.validArguments", emitted.read_text())
            self.assertIn("valid_context% 3 1 0", emitted.read_text())
            checked = subprocess.run(["lake", "env", "lean", "--memory=8192", str(emitted)],
                                     cwd=ROOT, capture_output=True, text=True, timeout=60)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_text_report_identifies_budget_model_and_witness(self):
        code, output = self.invoke("(lam c (con unit ()))", "(lam c (error))",
                                   json_output=False)
        self.assertEqual(code, 1, output)
        self.assertIn("regression:", output)
        self.assertIn('Analysis step guard: 100000 (exhaustion is inconclusive)', output)
        self.assertIn('Budget: {"cpu":1000000,"memory":10000}', output)
        self.assertIn("Cost model: bundled post-Conway E", output)
        self.assertIn("Counterexample:", output)
        self.assertIn("Replay: confirmed", output)
        self.assertIn("OLD: accepts (unit)", output)
        self.assertIn("NEW: rejects (error)", output)
        self.assertIn("Ledger validation: valid (ledger model)", output)
        self.assertIn("Context:", output)
        self.assertIn("Spending input:", output)
        self.assertIn("Fee:", output)
        self.assertIn("Inputs:", output)
        self.assertIn("Outputs:", output)
        self.assertNotIn('"fields":', output)

    def test_generic_export_contains_one_goal_per_query(self):
        for symmetric in [False, True]:
            with self.subTest(symmetric=symmetric), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                old, new, emitted = root / "old.uplc", root / "new.uplc", root / "check.lean"
                for path in [old, new]:
                    path.write_text("(program 1.1.0 (lam c (con unit ())))")
                result = subprocess.run([str(CLI), str(old), str(new), "--format", "textual",
                    "--inputs", "valid-context",
                    "--budget", "100000000", "1000000", "--wall-timeout", "30",
                    *(["--equivalence"] if symmetric else []),
                    "--emit-lean", str(emitted), "--json"],
                    cwd=ROOT, capture_output=True, text=True, timeout=60)
                report = json.loads(result.stdout)
                self.assertEqual((result.returncode, report["verdict"]),
                                 (0, "equivalent" if symmetric else "preserved"), report)
                # Each generic domain has one goal per query. Derived
                # no-regression and skipped rejection queries are omitted.
                source = emitted.read_text()
                names = ["acceptance_preserved"]
                if symmetric:
                    names += ["reverse_acceptance_preserved"]
                for name in names:
                    self.assertEqual(source.count(f"-- {name}\n"), 1)
                for name in ["no_acceptance_regression", "reverse_no_acceptance_regression",
                             "old_rejected", "new_rejected"]:
                    self.assertNotIn(f"-- {name}\n", source)
                checked = subprocess.run(["lake", "env", "lean", "--memory=8192", str(emitted)],
                                         cwd=ROOT, capture_output=True, text=True, timeout=60)
                self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def portfolio_case(self, env=None, jobs=('-j2',), timeout=5, seed=None, flags=()):
        return subprocess.run([str(CLI),
            'equivalence/examples/uplc-optimize/choose-list-empty.uplc',
            'equivalence/examples/uplc-optimize/choose-list-empty-opt.uplc',
            '--mode', 'function', '--timeout', str(timeout), '--wall-timeout', '10',
            *jobs, *([] if seed is None else ['--seed', str(seed)]), *flags, '--json'],
            cwd=ROOT, env=env, capture_output=True, text=True, timeout=15)

    def assert_portfolio_stopped(self, directory, workers):
        receipts = list(directory.glob('*.json'))
        # A fast winner can cancel a wrapper before its interpreter starts
        # and records its PID. Every wrapper that did start must be reaped.
        self.assertGreater(len(receipts), 0)
        self.assertLessEqual(len(receipts), workers)
        for receipt in receipts:
            for pid in json.loads(receipt.read_text()):
                with self.assertRaises(ProcessLookupError, msg=f'Portfolio process {pid} leaked'):
                    os.kill(pid, 0)

    def test_portfolio_starting_seed_single_worker(self):
        for seed in [0, 42, 4294967295]:
            with self.subTest(seed=seed), portfolio_z3('real', 'real') as (env, directory):
                emitted = directory / 'checked.lean'
                result = self.portfolio_case(env, jobs=('-j1',), seed=seed,
                                             flags=('--emit-lean', str(emitted)))
                report = json.loads(result.stdout)
                self.assertEqual(result.returncode, 1, report)
                self.assertTrue(report['counterexample']['replayed'])
                self.assertEqual((report['solver_seed'], report['solver_workers']), (seed, 1))
                self.assertEqual([int(p.read_text()) for p in directory.glob('*.seed')], [seed])
                self.assertIn(f'(random-seed: {seed})', emitted.read_text())
                self.assert_portfolio_stopped(directory, 1)

    def test_portfolio_starting_seed_offsets_every_worker(self):
        with portfolio_z3('unknown', 'unknown') as (env, directory):
            emitted = directory / 'checked.lean'
            result = self.portfolio_case(env, jobs=('-j4',), seed=42,
                                         flags=('--emit-lean', str(emitted)))
            report = json.loads(result.stdout)
            self.assertEqual((result.returncode, report['verdict']), (2, 'inconclusive'), report)
            self.assertEqual(report['solver_seed'], 42)
            self.assertEqual(sorted(int(p.read_text()) for p in directory.glob('*.seed')),
                             [42, 43, 44, 45])
            self.assertIn('-- function_equivalent', emitted.read_text())
            self.assertIn('-- #blaster', emitted.read_text())
            self.assertNotIn('(solve-result:', emitted.read_text())
            self.assert_portfolio_stopped(directory, 4)

    def test_portfolio_starting_seed_replays_the_winning_worker(self):
        with portfolio_z3('real', 'real') as (env, directory):
            result = self.portfolio_case(env, seed=42)
            report = json.loads(result.stdout)
            self.assertEqual(result.returncode, 1, report)
            self.assertTrue(report['counterexample']['replayed'])
            diagnostic = report['query_diagnostics']['function_equivalent']
            self.assertIn(diagnostic['winner_seed'], [42, 43])
            self.assertEqual(report['solver_seed'], 42)
            self.assert_portfolio_stopped(directory, 2)

    def test_portfolio_unknown_does_not_hide_replayed_seeded_winner(self):
        for jobs in [('-j2',), ('-j', '2')]:
            with self.subTest(jobs=jobs), portfolio_z3('unknown') as (env, directory):
                emitted = directory / 'checked.lean'
                result = self.portfolio_case(env, jobs, flags=('--emit-lean', str(emitted)))
                report = json.loads(result.stdout)
                self.assertEqual((result.returncode, report['verdict']), (1, 'inequivalent'), report)
                self.assertTrue(report['counterexample']['replayed'])
                self.assertEqual(report['solver_workers'], 2)
                diagnostic = report['query_diagnostics']['function_equivalent']
                self.assertEqual((diagnostic['status'], diagnostic['winner_seed']), ('falsified', 1))
                self.assertIn('(random-seed: 1) (solve-result: 1)', emitted.read_text())
                self.assertEqual(result.stderr.count('Phase: preprocessing [function_equivalent]'), 1)
                self.assert_portfolio_stopped(directory, 2)

    def test_portfolio_cancels_blocked_loser(self):
        with portfolio_z3('block') as (env, directory):
            result = self.portfolio_case(env)
            report = json.loads(result.stdout)
            self.assertEqual(result.returncode, 1, report)
            self.assertTrue(report['counterexample']['replayed'])
            self.assertEqual(report['query_diagnostics']['function_equivalent']['winner_seed'], 1)
            self.assert_portfolio_stopped(directory, 2)

    def test_portfolio_reaps_workers_after_model_replay(self):
        with portfolio_z3('real', 'real') as (env, directory):
            result = self.portfolio_case(env, jobs=('-j4',))
            report = json.loads(result.stdout)
            self.assertEqual(result.returncode, 1, report)
            self.assertTrue(report['counterexample']['replayed'])
            self.assert_portfolio_stopped(directory, 4)

    def test_portfolio_stalled_model_does_not_mask_healthy_worker(self):
        with portfolio_z3('block-model', 'real-after-model-request') as (env, directory):
            result = self.portfolio_case(env, timeout=2)
            report = json.loads(result.stdout)
            self.assertEqual((result.returncode, report["verdict"]), (1, "inequivalent"), report)
            self.assertTrue(report["counterexample"]["replayed"])
            self.assertEqual(report["query_diagnostics"]["function_equivalent"]["winner_seed"], 1)
            self.assertEqual(len(list(directory.glob('*.model'))), 2)
            self.assert_portfolio_stopped(directory, 2)

    def test_portfolio_has_one_deadline_and_reaps_all_workers(self):
        with portfolio_z3('block', 'block') as (env, directory):
            started = time.monotonic()
            result = self.portfolio_case(env, jobs=('-j4',), timeout=1)
            self.assertLess(time.monotonic() - started, 6)
            report = json.loads(result.stdout)
            self.assertEqual((result.returncode, report['verdict']), (2, 'inconclusive'), report)
            diagnostic = report['query_diagnostics']['function_equivalent']
            self.assertEqual((diagnostic['status'], diagnostic['limit_seconds']), ('timeout', 1))
            self.assert_portfolio_stopped(directory, 4)

    def test_solver_replays_quoted_parenthesis_in_data_model(self):
        with tempfile.TemporaryDirectory() as directory:
            old, new = (Path(directory) / name for name in ("old.uplc", "new.uplc"))
            old.write_text("(program 1.1.0 (lam c (con unit ())))")
            reject = reject_if("[[(builtin equalsData) c] (con data (B #28))]")
            new.write_text(f"(program 1.1.0 {reject})")
            for jobs in (1, 2):
                with self.subTest(jobs=jobs):
                    result = subprocess.run(
                        [str(CLI), str(old), str(new), "--mode", "function", "--inputs", "data",
                         f"-j{jobs}", "--timeout", "5", "--wall-timeout", "15", "--json"],
                        cwd=ROOT, capture_output=True, text=True, timeout=20)
                    report = json.loads(result.stdout)
                    self.assertEqual((result.returncode, report["verdict"]), (1, "inequivalent"), report)
                    self.assertTrue(report["counterexample"]["replayed"])
                    self.assertEqual(report["counterexample"]["input"], {"bytes": "28"})

    def test_solver_startup_uses_protocol_without_version_probe(self):
        with portfolio_z3('block-version', 'real') as (env, directory):
            result = self.portfolio_case(env)
            report = json.loads(result.stdout)
            self.assertEqual((result.returncode, report["verdict"]), (1, "inequivalent"), report)
            self.assertTrue(report["counterexample"]["replayed"])
            self.assert_portfolio_stopped(directory, 2)

    def test_lean_export_comments_out_timed_out_query(self):
        with portfolio_z3('block-options', 'block-options') as (env, directory):
            emitted = directory / 'timed-out.lean'
            result = self.portfolio_case(env, jobs=('-j1',), timeout=1,
                                         flags=('--emit-lean', str(emitted)))
            report = json.loads(result.stdout)
            self.assertEqual((result.returncode, report["verdict"]), (2, "inconclusive"), report)
            self.assertEqual(report["query_diagnostics"]["function_equivalent"]["status"], "timeout")
            source = emitted.read_text()
            self.assertIn("-- #blaster (timeout: 1)", source)
            self.assertNotIn("(solve-result:", source)
            checked = subprocess.run(["lake", "env", "lean", str(emitted)], cwd=ROOT,
                                     capture_output=True, text=True, timeout=15)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_solver_deadline_includes_submission_and_model_retrieval(self):
        for jobs, mode, receipt in [(1, 'block-options', '*.options'),
                                    (1, 'block-model', '*.model'), (2, 'block-model', '*.model')]:
            with self.subTest(jobs=jobs, mode=mode), portfolio_z3(mode, mode) as (env, directory):
                started = time.monotonic()
                result = self.portfolio_case(env, jobs=(f'-j{jobs}',), timeout=1)
                self.assertLess(time.monotonic() - started, 6)
                report = json.loads(result.stdout)
                self.assertEqual((result.returncode, report['verdict']), (2, 'inconclusive'), report)
                diagnostic = report['query_diagnostics']['function_equivalent']
                self.assertEqual((diagnostic['status'], diagnostic['limit_seconds']), ('timeout', 1))
                requests = len(list(directory.glob(receipt)))
                self.assertGreaterEqual(requests, 1)
                self.assertLessEqual(requests, jobs)
                self.assert_portfolio_stopped(directory, jobs)

    def test_portfolio_all_unknown_preserves_reason(self):
        with portfolio_z3('unknown', 'unknown') as (env, directory):
            result = self.portfolio_case(env)
            report = json.loads(result.stdout)
            self.assertEqual((result.returncode, report['verdict']), (2, 'inconclusive'), report)
            diagnostic = report['query_diagnostics']['function_equivalent']
            self.assertEqual((diagnostic['status'], diagnostic['reason']), ('unknown', 'incomplete'))
            self.assert_portfolio_stopped(directory, 2)

    def test_portfolio_worker_error_does_not_mask_winner(self):
        with portfolio_z3('error', 'real') as (env, directory):
            result = self.portfolio_case(env)
            report = json.loads(result.stdout)
            self.assertEqual((result.returncode, report["verdict"]), (1, "inequivalent"), report)
            self.assertTrue(report["counterexample"]["replayed"])
            self.assertEqual(report["query_diagnostics"]["function_equivalent"]["winner_seed"], 1)
            self.assert_portfolio_stopped(directory, 2)

    def test_portfolio_retries_model_read_on_worker_error(self):
        with portfolio_z3('error-model', 'error-model') as (env, directory):
            result = self.portfolio_case(env)
            report = json.loads(result.stdout)
            self.assertEqual((result.returncode, report["verdict"]), (3, "error"), report)
            self.assertIn("Unexpected EOF while reading SMT response", report["explanation"])
            self.assertEqual(len(list(directory.glob('*.model'))), 2)
            self.assert_portfolio_stopped(directory, 2)

    def test_portfolio_protocol_errors_remain_tool_errors(self):
        with portfolio_z3('error', 'block') as (env, directory):
            result = self.portfolio_case(env)
            report = json.loads(result.stdout)
            self.assertEqual(result.returncode, 3, report)
            self.assertIn('test solver failure', report['explanation'])
            self.assertNotIn('broken pipe', report['explanation'])
            self.assert_portfolio_stopped(directory, 2)

    def test_fixed_datum_restricts_queries_replay_and_export(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            old, new, emitted = (directory / name for name in
                                  ["old.uplc", "new.uplc", "fixed.lean"])
            old.write_text("(program 1.1.0 (lam c (con unit ())))")
            new.write_text("(program 1.1.0 " + reject_data_at([2, 1, 0], "I 7") + ")")
            for datum, code, verdict in [(7, 1, "bounded_regression"),
                                          (8, 0, "bounded_preserved")]:
                result = subprocess.run(
                    [str(CLI), str(old), str(new), "--bounded", "--steps", "1000",
                     "--max-inputs", "1", "--max-outputs", "1", "--max-signers", "1",
                     "--datum", f"I {datum}", "--timeout", "10", "--wall-timeout", "30",
                     "--emit-lean", str(emitted), "--json"],
                    cwd=ROOT, capture_output=True, text=True, timeout=40)
                report = json.loads(result.stdout)
                self.assertEqual(result.returncode, code, report)
                self.assertEqual(report["verdict"], verdict, report)
                self.assertEqual(report["fixed_datum"], {"int": datum})
                if datum == 7:
                    witness = report["counterexample"]
                    self.assertTrue(witness["replayed"])
                    self.assertEqual(witness["input"]["fields"][2]["fields"][1]
                                     ["fields"][0], {"int": 7})
                self.assertIn("valid_context_datum%", emitted.read_text())
            checked = subprocess.run(["lake", "env", "lean", str(emitted)], cwd=ROOT,
                                     capture_output=True, text=True, timeout=40)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            for flags in [["--datum", "I bogus"], ["--datum"],
                          ["--mode", "function", "--datum", "I 7"]]:
                result = subprocess.run([str(CLI), str(old), str(new), "--bounded",
                                         *flags, "--json"], cwd=ROOT,
                                        capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 3, result.stdout)

    def test_fixed_redeemer_restricts_queries_replay_and_export(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            old, new = directory / "old.uplc", directory / "new.uplc"
            old.write_text("(program 1.1.0 (lam c (con unit ())))")
            datum_matches = f"[[(builtin equalsData) {data_at([2, 1, 0])}] (con data (I 7))]"
            redeemer_matches = f"[[(builtin equalsData) {data_at([1])}] (con data (I 11))]"
            condition = (f"[[[(force (builtin ifThenElse)) {datum_matches}] "
                         f"{redeemer_matches}] (con bool False)]")
            new.write_text("(program 1.1.0 " + reject_if(condition) + ")")
            cases = [(None, 11, 1, "bounded_regression"),
                     (None, 12, 0, "bounded_preserved"),
                     (8, 11, 0, "bounded_preserved")]
            for index, (datum, redeemer, code, verdict) in enumerate(cases):
                emitted = directory / f"fixed-{index}.lean"
                flags = [] if datum is None else ["--datum", f"I {datum}"]
                result = subprocess.run(
                    [str(CLI), str(old), str(new), "--bounded", "--steps", "1000",
                     "--max-inputs", "1", "--max-outputs", "1", "--max-signers", "1",
                     "--redeemer", f"I {redeemer}", *flags, "--timeout", "10",
                     "--wall-timeout", "30", "--emit-lean", str(emitted), "--json"],
                    cwd=ROOT, capture_output=True, text=True, timeout=40)
                report = json.loads(result.stdout)
                self.assertEqual(result.returncode, code, report)
                self.assertEqual(report["verdict"], verdict, report)
                self.assertEqual(report["fixed_redeemer"], {"int": redeemer})
                if datum is not None:
                    self.assertEqual(report["fixed_datum"], {"int": datum})
                if code == 1:
                    witness = report["counterexample"]
                    self.assertTrue(witness["replayed"])
                    self.assertEqual(witness["input"]["fields"][1], {"int": redeemer})
                    self.assertEqual(witness["input"]["fields"][2]["fields"][1]
                                     ["fields"][0], {"int": 7})
                self.assertIn("valid_context_fixed%" if datum is not None else
                              "valid_context_redeemer%", emitted.read_text())
                checked = subprocess.run(["lake", "env", "lean", str(emitted)], cwd=ROOT,
                                         capture_output=True, text=True, timeout=40)
                self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            for flags in [["--redeemer", "I bogus"], ["--redeemer"],
                          ["--mode", "function", "--redeemer", "I 11"]]:
                result = subprocess.run([str(CLI), str(old), str(new), "--bounded",
                                         *flags, "--json"], cwd=ROOT,
                                        capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 3, result.stdout)

    def test_data_arguments_reach_report(self):
        with tempfile.TemporaryDirectory() as directory:
            script = Path(directory) / "unit.uplc"
            script.write_text("(program 1.1.0 (lam c (con unit ())))")
            cases = [("B#AB", "(I 42)", {"bytes": "ab"}, {"int": 42}),
                     ("List[I 0]", "Map[]", {"list": [{"int": 0}]}, {"map": []}),
                     ("42", "-7", {"int": 42}, {"int": -7})]
            for datum, redeemer, expected_datum, expected_redeemer in cases:
                result = subprocess.run(
                    [str(CLI), str(script), str(script), "--bounded", "--steps", "100",
                     "--max-inputs", "1", "--max-outputs", "1", "--max-signers", "0",
                     "--datum", datum, "--redeemer", redeemer, "--json"],
                    cwd=ROOT, capture_output=True, text=True, timeout=30)
                report = json.loads(result.stdout)
                self.assertEqual(result.returncode, 0, report)
                self.assertEqual(report["fixed_datum"], expected_datum)
                self.assertEqual(report["fixed_redeemer"], expected_redeemer)

    def test_mixed_language_lean_export(self):
        with tempfile.TemporaryDirectory() as directory:
            old = Path(directory) / "v2.uplc"
            new = Path(directory) / "v3.uplc"
            emitted = Path(directory) / "comparison.lean"
            old.write_text("(program 1.0.0 (lam datum (lam redeemer (lam ctx (con unit ())))))")
            new.write_text("(program 1.1.0 (lam ctx (con unit ())))")
            result = subprocess.run(
                [str(CLI), str(old), str(new), "--language-old", "PlutusV2", "--language-new", "PlutusV3",
                 "--bounded", "--steps", "300", "--max-inputs", "1", "--max-outputs", "1",
                 "--max-signers", "0", "--emit-lean", str(emitted), "--json"],
                cwd=ROOT, capture_output=True, text=True, timeout=30)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            source = emitted.read_text()
            self.assertIn("#import_uplc old PlutusV2", source)
            self.assertIn("#import_uplc new PlutusV3", source)
            self.assertIn("shared_context%", source)
            checked = subprocess.run(["lake", "env", "lean", str(emitted)], cwd=ROOT,
                                     capture_output=True, text=True, timeout=30)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_fixed_datum_and_redeemer_find_escrow_price(self):
        examples = ROOT / "equivalence/examples/two_party_escrow_old"
        result = subprocess.run(
            [str(CLI), str(examples / "Scalus_0.18.2_Unisay.cbor_hex"),
             str(examples / "Plinth_1.67.0.0_Unisay.cbor_hex"),
             "--datum", "Constr 0 [Constr 0 [], I 1000000]", "--redeemer", "1",
             "--bounded", "--steps", "5000", "--max-inputs", "1",
             "--max-outputs", "1", "--max-signers", "1",
             "--timeout", "20", "--wall-timeout", "60", "--json"],
            cwd=ROOT, capture_output=True, text=True, timeout=70)
        report = json.loads(result.stdout)
        self.assertEqual(result.returncode, 1, report)
        self.assertEqual(report["verdict"], "bounded_regression", report)
        witness = report["counterexample"]
        self.assertTrue(witness["replayed"])
        self.assertTrue(witness["ledger_validity"]["valid"])
        self.assertTrue(witness["old"]["accepts"])
        self.assertFalse(witness["new"]["accepts"])
        tx = witness["input"]["fields"][0]["fields"]
        output_ada = tx[2]["list"][0]["fields"][1]["map"][0]["v"]["map"][0]["v"]
        self.assertEqual(output_ada, {"int": 75000000})

    def dispatch_case(self, old_term, new_term, *flags):
        with tempfile.TemporaryDirectory() as directory:
            old, new = (Path(directory) / name for name in ["old.uplc", "new.uplc"])
            old.write_text("(program 1.1.0 " + old_term + ")")
            new.write_text("(program 1.1.0 " + new_term + ")")
            result = subprocess.run(
                [str(CLI), str(old), str(new), "--split-dispatch", "--bounded", "--steps", "1000",
                 "--max-inputs", "1", "--max-outputs", "1", "--max-signers", "1",
                 "--timeout", "5", "--wall-timeout", "60", *flags, "--json"],
                cwd=ROOT, capture_output=True, text=True, timeout=70)
            return result, json.loads(result.stdout)

    def test_dispatch_case_deadline_reaps_solver_and_recovers(self):
        for jobs, mode, seeded in [(1, 'block', 'real'), (1, 'block-model', 'block-model'),
                                    (2, 'block-model', 'block-model')]:
            with self.subTest(jobs=jobs, mode=mode), portfolio_z3(mode, seeded) as (env, directory):
                result = subprocess.run(
                    ["lake", "env", "lean", "equivalence/test_fixtures/dispatch_deadline.lean"],
                    cwd=ROOT, env={**env, 'UPLC_TEST_SOLVER_JOBS': str(jobs)},
                    capture_output=True, text=True, timeout=20)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("dispatch deadline recovered", result.stdout)
                if mode == 'block-model':
                    self.assertGreaterEqual(len(list(directory.glob('*.model'))), 1)
                self.assert_portfolio_stopped(directory, jobs + 1)

    def test_dispatch_catch_all_keeps_unlisted_values(self):
        redeemer = f"[(builtin unIData) {data_at([1])}]"
        first = f"[[(builtin equalsInteger) {redeemer}] (con integer 1)]"
        second = f"[[(builtin equalsInteger) {redeemer}] (con integer 2)]"
        condition = f"[[[(force (builtin ifThenElse)) {first}] (con bool True)] {second}]"
        result, report = self.dispatch_case(reject_if(condition), "(lam c (error))", "--dispatch-cases", "2")
        self.assertEqual(result.returncode, 1, report)
        self.assertEqual(report["verdict"], "bounded_regression", report)
        dispatch = report["dispatch"]
        self.assertTrue(dispatch["discovery_limited"])
        self.assertEqual(len(dispatch["cases"]), 3)
        self.assertTrue(dispatch["cases"][-1]["catch_all"])
        self.assertNotEqual(dispatch["cases"][-1]["queries"]["acceptance_preserved"], "valid")
        if dispatch["winning_case"] is not None:
            self.assertTrue(dispatch["winning_case"]["catch_all"])
        else:
            self.assertEqual(dispatch["proof_fallback"], "original full domain")
        witness = report["counterexample"]
        self.assertTrue(witness["replayed"])
        self.assertNotIn(witness["input"]["fields"][1], [{"int": 1}, {"int": 2}])

    def test_dispatch_catch_all_covers_other_data_kinds_and_reverse_direction(self):
        integer = f"[(builtin unIData) {data_at([1])}]"
        condition = f"[[(builtin equalsInteger) {integer}] (con integer 1)]"
        old = f"(lam c [[[(force (builtin ifThenElse)) {condition}] (con unit ())] (con unit ())])"
        result, report = self.dispatch_case(old, "(lam c (con unit ()))", "--equivalence")
        # All discovered integer cases agree. That cannot establish equivalence
        # for the remaining Data kinds, even if the full query times out.
        self.assertIn(result.returncode, [1, 2], report)
        self.assertIn(report["verdict"], ["bounded_inequivalent", "inconclusive"], report)
        self.assertTrue(report["dispatch"]["exhaustive"])
        if result.returncode == 2:
            self.assertEqual(report["dispatch"]["proof_fallback"], "original full domain")
        if result.returncode == 1:
            witness = report["counterexample"]
            self.assertTrue(witness["replayed"])
            self.assertEqual(witness["direction"], "new_to_old")
            self.assertNotIn("int", witness["input"]["fields"][1])
        else:
            self.assertEqual(report["queries"]["reverse_no_acceptance_regression"], "undetermined")

    def test_dispatch_proves_both_directions_including_capped_remainder(self):
        old = reject_data_at([1], "I 0")
        # The extra identity application changes the program without changing acceptance.
        body = old[len("(lam c "):-1]
        new = f"(lam c [(lam value value) {body}])"
        result, report = self.dispatch_case(old, new, "--equivalence", "--dispatch-cases", "1")
        self.assertEqual(result.returncode, 0, report)
        self.assertEqual(report["verdict"], "bounded_equivalent", report)
        dispatch = report["dispatch"]
        self.assertTrue(dispatch["discovery_limited"])
        self.assertTrue(dispatch["exhaustive"])
        self.assertEqual(dispatch["partition_cases"], 2)
        self.assertTrue(dispatch["cases"][-1]["catch_all"])
        self.assertEqual(dispatch["proved_queries"],
                         ["acceptance_preserved", "reverse_acceptance_preserved"])
        self.assertEqual(dispatch["proof_fallback"], "not needed")
        self.assertIn("Using dispatch evidence [acceptance_preserved]", result.stderr)
        self.assertIn("Using dispatch evidence [reverse_acceptance_preserved]", result.stderr)

    def test_dispatch_proof_retains_nondefault_acceptance_witness(self):
        condition = f"[[(builtin equalsData) {data_at([1])}] (con data (I 1))]"
        old = (f"(lam c (force [[[(force (builtin ifThenElse)) {condition}] "
               "(delay (con unit ()))] (delay (error))]))")
        body = old[len("(lam c "):-1]
        new = f"(lam c [(lam value value) {body}])"
        for flags in [(), ("--skip-old-rejected",)]:
            with self.subTest(flags=flags):
                result, report = self.dispatch_case(old, new, "--equivalence", *flags)
                self.assertEqual(result.returncode, 0, report)
                self.assertEqual(report["verdict"], "bounded_equivalent", report)
                self.assertEqual(report["old_acceptance_status"], "accepted")
                self.assertEqual(report["old_acceptance_witness"]["input"]["fields"][1], {"int": 1})
                self.assertEqual(report["dispatch"]["proof_fallback"], "not needed")
                if flags:
                    self.assertNotIn("old_rejected", report["queries"])
                else:
                    self.assertIn("Using dispatch evidence [old_rejected]", result.stderr)

    def test_dispatch_unknown_does_not_establish_equivalence(self):
        integer = f"[(builtin unIData) {data_at([1])}]"
        square = f"[[(builtin multiplyInteger) {integer}] {integer}]"
        old = reject_if(f"[[(builtin equalsInteger) {square}] {integer}]")
        zero = f"[[(builtin equalsInteger) {integer}] (con integer 0)]"
        one = f"[[(builtin equalsInteger) {integer}] (con integer 1)]"
        new = reject_if(f"[[[(force (builtin ifThenElse)) {zero}] (con bool True)] {one}]")
        with fake_z3("incomplete") as env, tempfile.TemporaryDirectory() as directory:
            left, right = (Path(directory) / name for name in ["old.uplc", "new.uplc"])
            left.write_text(f"(program 1.1.0 {old})")
            right.write_text(f"(program 1.1.0 {new})")
            result = subprocess.run(
                [str(CLI), str(left), str(right), "--split-dispatch", "--equivalence", "--bounded",
                 "--steps", "1000", "--dispatch-cases", "1", "--dispatch-timeout", "2",
                 "--max-inputs", "1", "--max-outputs", "1", "--max-signers", "1",
                 "--timeout", "2", "--wall-timeout", "30", "--json"],
                cwd=ROOT, env=env, capture_output=True, text=True, timeout=40)
        report = json.loads(result.stdout)
        self.assertEqual(result.returncode, 2, report)
        self.assertEqual(report["verdict"], "inconclusive", report)
        self.assertNotIn("reverse_acceptance_preserved", report["dispatch"]["proved_queries"])
        self.assertEqual(report["queries"]["reverse_acceptance_preserved"], "undetermined")
        self.assertTrue(any("undetermined" in case["queries"].values() or
                            "case_timeout" in case["queries"].values()
                            for case in report["dispatch"]["cases"]))
        self.assertEqual(report["dispatch"]["proof_fallback"], "original full domain")

    def test_dispatch_merges_compiler_traces_and_shares_literal_selectors(self):
        result, report = self.dispatch_case(reject_data_at([1], "I 0"), reject_data_at([1], "I 1"))
        self.assertEqual(result.returncode, 1, report)
        dispatch = report["dispatch"]
        self.assertEqual(dispatch["discovered_cases"], 3)  # 0, 1 and all other Data
        self.assertFalse(dispatch["discovery_limited"])
        self.assertEqual(dispatch["discovery_limits"], [])
        self.assertEqual(dispatch["winning_case"]["exclusions"], [])
        witness = report["counterexample"]
        self.assertTrue(witness["replayed"])
        self.assertEqual(witness["input"]["fields"][1], {"int": 1})

    def test_dispatch_solver_respects_else_exclusion(self):
        integer = f"[(builtin unIData) {data_at([1])}]"
        is_zero = f"[[(builtin equalsInteger) {integer}] (con integer 0)]"
        new = (f"(lam c (force [[[(force (builtin ifThenElse)) {is_zero}] "
               "(delay (con unit ()))] (delay (error))]))")
        result, report = self.dispatch_case("(lam c (con unit ()))", new)
        self.assertEqual(result.returncode, 1, report)
        winner = report["dispatch"]["winning_case"]
        self.assertIsNotNone(winner)
        self.assertIn("redeemer ≠ (I 0)", winner["exclusions"])
        self.assertFalse(winner.get("native_probe", False))
        witness = report["counterexample"]
        self.assertTrue(witness["replayed"])
        self.assertTrue(witness["ledger_validity"]["valid"])
        self.assertNotEqual(witness["input"]["fields"][1], {"int": 0})

    def test_dispatch_keeps_datum_and_payload_with_their_redeemer(self):
        def branch(condition, yes, no):
            return f"(force [[[(force (builtin ifThenElse)) {condition}] (delay {yes})] (delay {no})])"

        def datum_is(value):
            return branch(f"[[(builtin equalsData) {data_at([2, 1, 0])}] (con data ({value}))]",
                          "(con unit ())", "(error)")

        redeemer = data_at([1])
        tag = f"[(force (force (builtin fstPair))) [(builtin unConstrData) {redeemer}]]"
        fields = f"[(force (force (builtin sndPair))) [(builtin unConstrData) {redeemer}]]"
        payload = f"[(builtin unBData) [(force (builtin headList)) {fields}]]"
        is_zero = f"[[(builtin equalsInteger) {tag}] (con integer 0)]"
        is_one = f"[[(builtin equalsInteger) {tag}] (con integer 1)]"
        first = f"[(lam ignored {datum_is('I 10')}) {payload}]"
        old = f"(lam c {branch(is_zero, first, branch(is_one, datum_is('B #62'), '(error)'))})"
        result, report = self.dispatch_case(old, reject_if(is_one), "--dispatch-cases", "2")
        self.assertEqual(result.returncode, 1, report)
        winner = report["dispatch"]["winning_case"]
        self.assertIsNotNone(winner)
        self.assertEqual(winner["redeemer"], "Constr 1 []")
        self.assertEqual(winner["exclusions"], [])
        witness = report["counterexample"]
        self.assertTrue(witness["replayed"])
        self.assertTrue(witness["ledger_validity"]["valid"])
        self.assertEqual(witness["input"]["fields"][1], {"constructor": 1, "fields": []})
        self.assertEqual(witness["input"]["fields"][2]["fields"][1]["fields"][0], {"bytes": "62"})

    def test_dispatch_handles_map_datum_and_string_redeemer(self):
        datum = f"[[(builtin equalsData) {data_at([2, 1, 0])}] (con data (Map [(I 1, I 2)]))]"
        text = f"[(builtin decodeUtf8) [(builtin unBData) {data_at([1])}]]"
        redeemer = f'[[(builtin equalsString) {text}] (con string "go")]'
        condition = f"[[[(force (builtin ifThenElse)) {datum}] {redeemer}] (con bool False)]"
        # reject_if is inverted here so OLD accepts exactly this dispatch case.
        old = ("(lam c (force [[[(force (builtin ifThenElse)) " + condition +
               "] (delay (con unit ()))] (delay (error))]))")
        result, report = self.dispatch_case(old, "(lam c (error))")
        self.assertEqual(result.returncode, 1, report)
        self.assertIsNotNone(report["dispatch"]["winning_case"])
        witness = report["counterexample"]
        self.assertTrue(witness["replayed"])
        self.assertTrue(witness["ledger_validity"]["valid"])
        self.assertEqual(witness["input"]["fields"][1], {"bytes": "676f"})
        self.assertEqual(witness["input"]["fields"][2]["fields"][1]["fields"][0],
                         {"map": [{"k": {"int": 1}, "v": {"int": 2}}]})

    def test_dispatch_discovers_escrow_without_fixed_arguments(self):
        examples = ROOT / "equivalence/examples/two_party_escrow_old"
        result = subprocess.run(
            [str(CLI), str(examples / "Scalus_0.18.2_Unisay.cbor_hex"),
             str(examples / "Plinth_1.67.0.0_Unisay.cbor_hex"), "--split-dispatch",
             "--bounded", "--steps", "5000", "--max-inputs", "1", "--max-outputs", "1",
             "--max-signers", "1", "--timeout", "10", "--wall-timeout", "90", "--json"],
            cwd=ROOT, capture_output=True, text=True, timeout=100)
        report = json.loads(result.stdout)
        self.assertEqual(result.returncode, 1, report)
        self.assertEqual(report["verdict"], "bounded_regression", report)
        self.assertNotIn("fixed_datum", report)
        self.assertNotIn("fixed_redeemer", report)
        self.assertIsNotNone(report["dispatch"]["winning_case"])
        witness = report["counterexample"]
        self.assertTrue(witness["replayed"])
        self.assertTrue(witness["ledger_validity"]["valid"])
        tx = witness["input"]["fields"][0]["fields"]
        self.assertEqual(tx[2]["list"][0]["fields"][1]["map"][0]["v"]["map"][0]["v"],
                         {"int": 75000000})

    def test_help(self):
        for args in ([], ["-h"], ["--help"], ["old", "new", "--json", "--help"]):
            with self.subTest(args=args):
                result = subprocess.run([str(CLI), *args], cwd=ROOT,
                                        capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertTrue(result.stdout.startswith("Usage: "), result.stdout)

    def test_export_paths_require_explicit_dash_prefixed_names(self):
        with tempfile.TemporaryDirectory() as directory:
            script = Path(directory) / "identity.uplc"
            script.write_text("(program 1.1.0 (lam n n))")
            existing = Path(directory) / "--json"
            existing.write_text("existing content")
            args = [str(CLI), str(script), str(script), "--mode", "function"]
            for option in ("--emit-lean", "--emit-assurance"):
                for token in ("--json", "-h", "--help", ""):
                    with self.subTest(option=option, token=token):
                        flags = [option, token] if token == "--json" else [option, token, "--json"]
                        result = subprocess.run(
                            [*args, *flags], cwd=directory, capture_output=True,
                            text=True, timeout=10)
                        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
                        report = json.loads(result.stdout)
                        self.assertEqual(report["verdict"], "error")
                        self.assertIn(f"{option} expects a path", report["explanation"])
            self.assertEqual(existing.read_text(), "existing content")
            result = subprocess.run(
                [*args, "--emit-lean", "./--json", "--json"],
                cwd=directory, capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(json.loads(result.stdout)["verdict"], "equivalent")
            self.assertIn("import Equivalence", existing.read_text())

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
                    *[["old", "new", *args] for args in [
                        ["-j"], ["-j0"], ["-j", "0"], ["-j-1"], ["-jx"], ["-j", "-1"],
                        ["--seed"], ["--seed", "-1"], ["--seed", "nope"],
                        ["--dispatch-cases", "0"], ["--dispatch-timeout", "0"],
                        ["--dispatch-cases", "bad"], ["--dispatch-timeout", "-1"],
                        ["--seed", "4294967296"], ["--seed", "4294967295", "-j2"]]],
                    ["left", "right", "--inputs", "integer", "--case", "0"],
                    *[["left", "right", "--inputs", mode] for mode in [
                        "htlc-refund", "htlc-claim", "vesting-full", "vesting-partial",
                        "escrow-deposit", "escrow-accept", "escrow-refund",
                        "small-context", "medium-context", "integer", "data", "data3", "spending"]],
                    ["left", "right", "--inputs", "data", "--variation", "baseline"],
                    ["left", "right", "--raw-context"],
                    ["old", "new", "--datum", "-h"],
                    ["old", "new", "--redeemer", "--help"],
                    ["left", "right", "--bounded", "--max-inputs", "-1"],
                    ["left", "right", "--bounded", "--max-outputs"],
                    ["left", "right", "--bounded", "--max-signers", "not-a-number"],
                    ["left", "right", "--mode", "function", "--inputs", "integer", "--max-inputs", "2"]]:
                with self.subTest(args=args):
                    if args not in [["old", "new"], ["old", "new", "--equivalence"]] and "--budget" not in args:
                        args += ["--budget", "1", "1"]
                    args = [str(old_path) if a in ("old", "left") else
                            str(new_path) if a in ("new", "right") else a for a in args]
                    result = subprocess.run(
                        [str(CLI), "--inputs", "valid-context", *args, "--json"],
                        capture_output=True, text=True, timeout=10)
                    self.assertEqual(result.returncode, 3, result.stdout)
                    self.assertEqual(json.loads(result.stdout)["verdict"], "error")

    def test_malformed_script_is_tool_error(self):
        code, report = self.invoke("not uplc", "(lam n n)")
        self.assertEqual(code, 3, report)

    @unittest.skipUnless(os.name == "posix", "requires POSIX signals")
    def test_interrupt_stops_worker_and_solver(self):
        fixtures = ROOT / "equivalence/examples/uplc-optimize"
        for signum in (signal.SIGINT, signal.SIGTERM):
            with self.subTest(signum=signum), portfolio_z3("block-options", "real") as (env, directory):
                process = subprocess.Popen(
                    [str(CLI), str(fixtures / "choose-list-empty.uplc"),
                     str(fixtures / "choose-list-empty-opt.uplc"), "--mode", "function",
                     "--timeout", "20", "--wall-timeout", "30", "--json"],
                    cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
                worker = None
                try:
                    deadline = time.monotonic() + 8
                    while time.monotonic() < deadline and process.poll() is None:
                        if list(directory.glob("*.options")):
                            break
                        time.sleep(0.01)
                    receipts = list(directory.glob("*.json"))
                    if receipts:
                        solver, _ = json.loads(receipts[0].read_text())
                        worker = os.getpgid(solver)
                    self.assertTrue(list(directory.glob("*.options")), "Solver did not reach blocked setup")
                    self.assertIsNotNone(worker)
                    process.send_signal(signum)
                    stdout, stderr = process.communicate(timeout=8)
                    with self.assertRaises(ProcessLookupError):
                        os.kill(worker, 0)
                    self.assert_portfolio_stopped(directory, 1)
                    self.assertEqual(process.returncode, 128 + signum, stdout + stderr)
                finally:
                    if worker is not None:
                        with contextlib.suppress(ProcessLookupError):
                            os.killpg(worker, signal.SIGTERM)
                    if process.poll() is None:
                        process.kill()
                    process.communicate(timeout=10)

    @unittest.skipUnless(hasattr(os, "mkfifo"), "requires POSIX named pipes")
    def test_wall_timeout_stops_blocked_worker(self):
        with tempfile.TemporaryDirectory() as directory:
            blocked = Path(directory) / "blocked.uplc"
            os.mkfifo(blocked)
            with subprocess.Popen(
                [str(CLI), "--inputs", "valid-context", str(blocked), str(blocked), "--format", "textual",
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
                report = json.loads(stdout)
                self.assertEqual(report["verdict"], "inconclusive")
                self.assertEqual(report["timeout"]["phase"], "loading")
                self.assertIn("during loading scripts", report["explanation"])


if __name__ == "__main__":
    unittest.main()
