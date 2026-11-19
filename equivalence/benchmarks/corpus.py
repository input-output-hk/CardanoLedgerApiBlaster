#!/usr/bin/env python3
"""Measure each distinct collected UPLC binary against a different scenario implementation."""
import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import selectors
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
VALIDATORS = {"htlc", "linear_vesting", "two_party_escrow", "two_party_escrow_old"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory():
    groups = defaultdict(lambda: defaultdict(list))
    for path in sorted((ROOT / "equivalence/examples").glob("*/*.cbor_hex")):
        digest = hashlib.sha256(bytes.fromhex(path.read_text().strip())).hexdigest()
        groups[path.parent.name][digest].append(str(path.relative_to(ROOT)))
    cases = []
    for group, binaries in sorted(groups.items()):
        members = []
        for digest, aliases in binaries.items():
            preferred = next((p for p in aliases if Path(p).name == "Plinth_1.67.0.0_Unisay.cbor_hex"), aliases[0])
            members.append({"script": preferred, "binary_sha256": digest, "aliases": aliases})
        members.sort(key=lambda m: m["script"])
        reference = next((m for m in members if Path(m["script"]).name == "Plinth_1.67.0.0_Unisay.cbor_hex"), members[0])
        for member in members:
            candidates = [m for m in members if m["binary_sha256"] != member["binary_sha256"]]
            if not candidates:
                raise ValueError(f"No nonidentical comparison available in {group}")
            partner = reference if reference in candidates else next(
                (m for m in candidates if Path(m["script"]).name.split("_")[0] != Path(member["script"]).name.split("_")[0]), candidates[0])
            cases.append({"id": group + "--" + Path(member["script"]).stem, "scenario": group,
                          **member, "partner": partner["script"], "partner_binary_sha256": partner["binary_sha256"],
                          "validator": group in VALIDATORS, "ecd": group == "ecd"})
    return {"cases": cases, "file_count": sum(len(c["aliases"]) for c in cases),
            "distinct_binary_count": len(cases), "scenario_count": len(groups),
            "ecd_domain": "gcd(x, 462), with x an arbitrary integer; adapter replayed at five concrete inputs"}


def terminate(process, sig=signal.SIGTERM):
    try:
        os.killpg(process.pid, sig)
    except ProcessLookupError:
        pass


def measure(binary, case, directory, wall, steps, timeout):
    request = {"left": case["script"], "right": case["partner"], "validator": case["validator"],
               "ecd": case["ecd"], "steps": steps, "timeout": timeout}
    start = time.monotonic()
    process = subprocess.Popen([str(binary)], cwd=ROOT, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, start_new_session=True)
    process.stdin.write(json.dumps(request).encode())
    process.stdin.close()
    selector = selectors.DefaultSelector()
    for stream, label in [(process.stdout, "stdout"), (process.stderr, "stderr")]:
        os.set_blocking(stream.fileno(), False)
        selector.register(stream, selectors.EVENT_READ, label)
    captured = {"stdout": bytearray(), "stderr": bytearray()}
    stderr_pending = bytearray()
    phases = [{"seconds": 0.0, "phase": "startup", "query": None}]
    timed_out = False
    usage = None
    try:
        while True:
            elapsed = time.monotonic() - start
            if elapsed >= wall and not timed_out:
                timed_out = True
                terminate(process)
            if elapsed >= wall + 2:
                terminate(process, signal.SIGKILL)
            for key, _ in selector.select(timeout=0.02):
                data = os.read(key.fileobj.fileno(), 65536)
                if not data:
                    selector.unregister(key.fileobj)
                    continue
                captured[key.data].extend(data)
                if key.data == "stderr":
                    stderr_pending.extend(data)
                    while b"\n" in stderr_pending:
                        line, _, stderr_pending = stderr_pending.partition(b"\n")
                        marker = b"[corpus:phase] "
                        if marker in line:
                            phase = json.loads(line.split(marker, 1)[1])
                            phases.append({"seconds": time.monotonic() - start, **phase})
            pid, status, child_usage = os.wait4(process.pid, os.WNOHANG)
            if pid:
                process.returncode = os.waitstatus_to_exitcode(status)
                usage = child_usage
                break
    finally:
        if process.returncode is None:
            terminate(process, signal.SIGKILL)
            _, status, usage = os.wait4(process.pid, 0)
            process.returncode = os.waitstatus_to_exitcode(status)
        # Ensure a watchdog/cancellation leaves no solver in the owned session.
        terminate(process, signal.SIGKILL)
        for stream, label in [(process.stdout, "stdout"), (process.stderr, "stderr")]:
            while True:
                try:
                    data = os.read(stream.fileno(), 65536)
                except BlockingIOError:
                    break
                if not data:
                    break
                captured[label].extend(data)
            stream.close()
        selector.close()
    elapsed = time.monotonic() - start
    stdout = captured["stdout"].decode(errors="replace")
    stderr = captured["stderr"].decode(errors="replace")
    if timed_out:
        report = {"verdict": "inconclusive", "timeout": {"phase": phases[-1]["phase"],
                  "query": phases[-1]["query"], "limit_seconds": wall}}
    else:
        try:
            report = json.loads(stdout)
            if not isinstance(report, dict) or "verdict" not in report:
                raise ValueError("Missing report verdict")
        except ValueError as e:
            report = {"verdict": "runner_error", "explanation": str(e)}
    intervals = []
    for i, phase in enumerate(phases):
        end = phases[i + 1]["seconds"] if i + 1 < len(phases) else elapsed
        intervals.append({**phase, "duration_seconds": max(0, end - phase["seconds"])})
    result = {"id": case["id"], "scenario": case["scenario"], "request": request,
              "elapsed_seconds": elapsed, "preprocessing_seconds": sum(
                  p["duration_seconds"] for p in intervals if p["phase"] == "preprocessing"),
              "preprocessing_censored": timed_out and phases[-1]["phase"] == "preprocessing",
              "max_rss_bytes": usage.ru_maxrss * (1 if sys.platform == "darwin" else 1024),
              "cpu_seconds": usage.ru_utime + usage.ru_stime, "exit_code": process.returncode,
              "wall_timeout": timed_out, "phase_intervals": intervals, "report": report}
    directory.mkdir()
    (directory / "stdout.json").write_text(stdout)
    (directory / "stderr.log").write_text(stderr)
    (directory / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def grouped(results):
    groups = defaultdict(list)
    for result in results:
        groups[result["scenario"]].append(result)
    return {name: {"cases": len(rows), "verdicts": dict(Counter(r["report"]["verdict"] for r in rows)),
                   "preprocessing_timeouts": sum(r["preprocessing_censored"] for r in rows),
                   "preprocessing_seconds_total": sum(r["preprocessing_seconds"] for r in rows),
                   "max_rss_bytes": max(r["max_rss_bytes"] for r in rows)} for name, rows in groups.items()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--binary", type=Path, default=ROOT / ".lake/build/bin/equivalence_benchmark_worker")
    parser.add_argument("--wall-timeout", type=float, default=5)
    parser.add_argument("--steps", type=int, default=5000)
    parser.add_argument("--solver-timeout", type=int, default=1)
    parser.add_argument("--case", action="append")
    args = parser.parse_args()
    if min(args.wall_timeout, args.steps, args.solver_timeout) <= 0:
        parser.error("Limits must be positive")
    corpus = json.loads(args.manifest.read_text()) if args.manifest else inventory()
    cases = corpus["cases"]
    if args.case:
        unknown = set(args.case) - {c["id"] for c in cases}
        if unknown:
            parser.error(f"Unknown cases: {sorted(unknown)}")
        cases = [c for c in cases if c["id"] in args.case]
    for case in cases:
        for path, key in [(case["script"], "binary_sha256"), (case["partner"], "partner_binary_sha256")]:
            if hashlib.sha256(bytes.fromhex((ROOT / path).read_text().strip())).hexdigest() != case[key]:
                parser.error(f"Fixture changed: {path}")
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / "corpus.json").write_text(json.dumps(corpus, indent=2) + "\n")
    receipt = {"started_utc": datetime.now(timezone.utc).isoformat(), "binary": str(args.binary.resolve()),
               "binary_sha256": sha(args.binary), "runner_sha256": sha(Path(__file__)),
               "worker_source_sha256": sha(Path(__file__).with_name("CorpusWorker.lean")),
               "git_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
               "dependencies": {name: {"revision": subprocess.check_output(["git", "-C", str(ROOT / '.lake/packages' / name), "rev-parse", "HEAD"], text=True).strip(),
                                        "diff": subprocess.check_output(["git", "-C", str(ROOT / '.lake/packages' / name), "diff"], text=True)} for name in ["Blaster", "PlutusCore"]},
               "platform": platform.platform(), "wall_seconds": args.wall_timeout, "steps": args.steps,
               "solver_seconds": args.solver_timeout, "selected_cases": [c["id"] for c in cases],
               "memory_scope": "wait4 ru_maxrss for native worker (and OS-accounted waited descendants), not peak aggregate process-tree RSS"}
    (args.output / "provenance.json").write_text(json.dumps(receipt, indent=2) + "\n")
    results = []
    for i, case in enumerate(cases):
        result = measure(args.binary.resolve(), case, args.output / case["id"], args.wall_timeout, args.steps, args.solver_timeout)
        results.append(result)
        (args.output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        (args.output / "groups.json").write_text(json.dumps(grouped(results), indent=2) + "\n")
        print(f"{i+1}/{len(cases)} {case['id']}: {result['report']['verdict']}; "
              f"{result['elapsed_seconds']:.2f}s; {result['max_rss_bytes']/1024**2:.0f} MiB", flush=True)
    return int(any(r["report"]["verdict"] == "runner_error" or
                   (not r["wall_timeout"] and r["exit_code"] != 0) for r in results))


if __name__ == "__main__":
    raise SystemExit(main())
