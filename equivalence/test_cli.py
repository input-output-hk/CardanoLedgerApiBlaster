"""Process-level checks for stdout, exit codes, argument errors and supervision.

Functional acceptance, model replay and context tests live in Tests/Equivalence/*.lean.
"""

import json
import contextlib
import sys
import os
import re
from pathlib import Path
import selectors
import shutil
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

    def solver_case(self, env, *, wall_timeout=10, json_output=True):
        with tempfile.TemporaryDirectory() as directory:
            paths = [Path(directory) / 'old.uplc', Path(directory) / 'new.uplc']
            for path, value in zip(paths, [42, 43]):
                term = reject_data_at([2, 1, 0], f"I {value}")
                path.write_text(f"(program 1.1.0 {term})")
            return subprocess.run([str(CLI), *(str(p) for p in paths),
                '--inputs', 'valid-context', '--bounded', '--steps', '1000', '--timeout', '5',
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
            result = self.solver_case(env, wall_timeout=15)
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
        self.assertIn('"replayed": true', output)
        self.assertIn('"input":', output)

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
            result = self.portfolio_case(env, jobs=('-j4',), seed=42)
            report = json.loads(result.stdout)
            self.assertEqual((result.returncode, report['verdict']), (2, 'inconclusive'), report)
            self.assertEqual(report['solver_seed'], 42)
            self.assertEqual(sorted(int(p.read_text()) for p in directory.glob('*.seed')),
                             [42, 43, 44, 45])
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
                result = self.portfolio_case(env, jobs)
                report = json.loads(result.stdout)
                self.assertEqual((result.returncode, report['verdict']), (1, 'inequivalent'), report)
                self.assertTrue(report['counterexample']['replayed'])
                self.assertEqual(report['solver_workers'], 2)
                diagnostic = report['query_diagnostics']['function_equivalent']
                self.assertEqual((diagnostic['status'], diagnostic['winner_seed']), ('falsified', 1))
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

    def test_portfolio_reads_only_one_model(self):
        with portfolio_z3('real', 'real') as (env, directory):
            result = self.portfolio_case(env, jobs=('-j4',))
            report = json.loads(result.stdout)
            self.assertEqual(result.returncode, 1, report)
            self.assertTrue(report['counterexample']['replayed'])
            self.assertEqual(len(list(directory.glob('*.model'))), 1)
            self.assert_portfolio_stopped(directory, 4)

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

    def test_portfolio_all_unknown_preserves_reason(self):
        with portfolio_z3('unknown', 'unknown') as (env, directory):
            result = self.portfolio_case(env)
            report = json.loads(result.stdout)
            self.assertEqual((result.returncode, report['verdict']), (2, 'inconclusive'), report)
            diagnostic = report['query_diagnostics']['function_equivalent']
            self.assertEqual((diagnostic['status'], diagnostic['reason']), ('unknown', 'incomplete'))
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

    def test_data_text_shorthand_reaches_report(self):
        with tempfile.TemporaryDirectory() as directory:
            script = Path(directory) / "unit.uplc"
            script.write_text("(program 1.1.0 (lam c (con unit ())))")
            cases = [("hello world", "é🚀", {"bytes": "68656c6c6f20776f726c64"},
                      {"bytes": "c3a9f09f9a80"}),
                     ("42", '\"42\"', {"int": 42}, {"bytes": "3432"})]
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

    def test_fixed_datum_and_redeemer_find_escrow_price(self):
        examples = ROOT / "equivalence/examples/two_party_escrow"
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
                        ["--seed", "4294967296"], ["--seed", "4294967295", "-j2"]]],
                    ["left", "right", "--inputs", "integer", "--case", "0"],
                    *[["left", "right", "--inputs", mode] for mode in [
                        "htlc-refund", "htlc-claim", "vesting-full", "vesting-partial",
                        "escrow-deposit", "escrow-accept", "escrow-refund",
                        "small-context", "medium-context", "integer", "data", "data3", "spending"]],
                    ["left", "right", "--inputs", "data", "--variation", "baseline"],
                    ["left", "right", "--raw-context"],
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
