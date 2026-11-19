"""Corpus coverage and native-worker watchdog/resource-accounting checks."""
import json
from pathlib import Path
import sys
import tempfile
import time
import unittest

import corpus
import compare_corpus


class CorpusTests(unittest.TestCase):
    def test_comparison_excludes_timeouts_errors_and_changed_outcomes(self):
        def row(name, verdict="bounded_preserved", timeout=False, seconds=2):
            return {"id": name, "scenario": "scenario", "request": {},
                    "report": {"verdict": verdict}, "wall_timeout": timeout,
                    "preprocessing_seconds": seconds, "max_rss_bytes": 100}
        before = [row("completed"), row("timed", timeout=True), row("error", "error"), row("changed")]
        after = [row("completed", seconds=1), row("timed"), row("error", "error"), row("changed", "bounded_regression")]
        report = compare_corpus.compare(before, after)
        group = report["scenarios"]["scenario"]
        self.assertEqual(group["common_complete"], 1)
        self.assertEqual(group["median_preprocessing_ratio"], 0.5)
        self.assertEqual(group["outcome_changes"], 1)
        self.assertEqual(len(report["transitions"]), 2)

    def test_every_fixture_is_included_once_and_pairs_are_nonidentical(self):
        inventory = corpus.inventory()
        aliases = [p for c in inventory["cases"] for p in c["aliases"]]
        actual = [str(p.relative_to(corpus.ROOT)) for p in
                  (corpus.ROOT / "equivalence/examples").glob("*/*.cbor_hex")]
        self.assertCountEqual(aliases, actual)
        self.assertEqual(len(aliases), len(set(aliases)))
        self.assertEqual(len(inventory["cases"]), len({c["binary_sha256"] for c in inventory["cases"]}))
        for c in inventory["cases"]:
            self.assertNotEqual(c["binary_sha256"], c["partner_binary_sha256"])
            self.assertEqual(Path(c["partner"]).parent.name, c["scenario"])

    def fake_worker(self, root, body):
        worker = root / "worker"
        worker.write_text(f"#!{sys.executable}\nimport sys, json\njson.load(sys.stdin)\n" + body)
        worker.chmod(0o755)
        return worker

    def case(self):
        return {"id": "fake", "scenario": "fake", "script": "unused", "partner": "unused",
                "validator": False, "ecd": False}

    def test_report_phase_and_per_child_resources(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            worker = self.fake_worker(root,
                "print('[corpus:phase] {\"phase\":\"preprocessing\",\"query\":\"q\"}', file=sys.stderr, flush=True)\n"
                "a=bytearray(4*1024*1024)\nprint('{\"verdict\":\"bounded_preserved\"}')\n")
            result = corpus.measure(worker, self.case(), root / "result", 2, 5000, 1)
            self.assertEqual(result["report"]["verdict"], "bounded_preserved")
            self.assertFalse(result["wall_timeout"])
            self.assertGreater(result["max_rss_bytes"], 0)
            self.assertTrue(any(p["phase"] == "preprocessing" for p in result["phase_intervals"]))
            self.assertEqual(json.loads((root / "result/stdout.json").read_text()), result["report"])

    def test_deadline_kills_the_owned_worker_and_solver_group(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            survivor = root / "survived"
            code = f"import time; from pathlib import Path; time.sleep(1.0); Path({str(survivor)!r}).touch()"
            worker = self.fake_worker(root,
                "import subprocess,time\n"
                "print('[corpus:phase] {\"phase\":\"preprocessing\",\"query\":\"q\"}', file=sys.stderr, flush=True)\n"
                f"subprocess.Popen([sys.executable,'-c',{code!r}])\ntime.sleep(20)\n")
            result = corpus.measure(worker, self.case(), root / "result", 0.5, 5000, 1)
            self.assertTrue(result["wall_timeout"])
            self.assertTrue(result["preprocessing_censored"])
            self.assertEqual(result["report"]["timeout"]["query"], "q")
            self.assertLess(result["elapsed_seconds"], 2)
            time.sleep(1.1)
            self.assertFalse(survivor.exists(), "Owned solver survived the watchdog")


if __name__ == "__main__":
    unittest.main()
