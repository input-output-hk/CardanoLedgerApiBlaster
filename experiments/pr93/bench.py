#!/usr/bin/env python3
"""Compare complete #prep_uplc examples with and without PR #93's opt-in rules."""

import argparse
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
WORK = Path(__file__).resolve().parent / ".work"
CASES = {
    "sellnft": ("Tests/Scripts/SellNFT/SellNFT.lean", "appliedSellNFT"),
    "hello": ("Tests/Scripts/HelloWorld/HelloWorld.lean", "appliedHelloWorld"),
    "unlockpin": ("Tests/Scripts/UnlockPIN/UnlockPIN.lean", "appliedUnlockPIN"),
    "paramfeed": ("Tests/Scripts/ParamFeed/ParamFeed.lean", "appliedParamFeed"),
    "minting": ("Tests/Scripts/MintingPolicy/MintingPolicy.lean", "appliedMintingPolicy"),
    "governance": ("Tests/Scripts/Governance/Governance.lean", "appliedGovernance"),
}
MEASURE = """
partial def pr93Nodes (root : Lean.Expr) : Nat := Id.run do
  let mut seen : Std.HashSet Lean.Expr := {}
  let mut todo := [root]
  while !todo.isEmpty do
    let e := todo.head!
    todo := todo.tail!
    unless seen.contains e do
      seen := seen.insert e
      match e with
      | .app f a => todo := f :: a :: todo
      | .lam _ t b _ | .forallE _ t b _ => todo := t :: b :: todo
      | .letE _ t v b _ => todo := t :: v :: b :: todo
      | .mdata _ b | .proj _ _ b => todo := b :: todo
      | _ => pure ()
  return seen.size
run_cmd do
  let ci ← Lean.getConstInfo `{name}.prop
  let used := ci.value!.getUsedConstants
  let evaluator := used.contains `PlutusCore.UPLC.CekMachine.runSteps ||
    used.contains `PlutusCore.UPLC.CekMachine.runStepsPreservingState ||
    used.contains `PlutusCore.UPLC.CekMachine.step
  let summary := used.any (fun n =>
    n.toString.startsWith "PlutusCore.UPLC.Optimize.searchPlan" ||
    n.toString.startsWith "PlutusCore.UPLC.Optimize.traversalPlan")
  Lean.logInfo m!"MEASURE nodes={pr93Nodes ci.value!} summary={summary} evaluator={evaluator}"
"""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cases", nargs="+", choices=CASES, default=list(CASES))
    parser.add_argument("--modes", nargs="+", choices=["baseline", "generic"],
                        default=["baseline", "generic"])
    parser.add_argument("--timeout", type=int, default=90)
    args = parser.parse_args()
    WORK.mkdir(exist_ok=True)
    results = []
    for case in args.cases:
        relative, name = CASES[case]
        original = (ROOT / relative).read_text()
        for mode in args.modes:
            source = original
            if mode == "generic":
                marker = "import PlutusCore.UPLC\n"
                if marker not in source:
                    raise RuntimeError(f"missing import marker in {relative}")
                source = source.replace(marker, marker +
                    "import PlutusCore.UPLC.Optimize.Extension\n", 1)
            source += "\n" + MEASURE.replace("{name}", name)
            path = WORK / f"{case}-{mode}.lean"
            path.write_text(source)
            start = time.monotonic()
            with path.with_suffix(".log").open("w") as log:
                proc = subprocess.Popen(
                    ["lake", "lean", str(path), "--", "--threads=1"],
                    cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                    start_new_session=True)
                try:
                    proc.wait(timeout=args.timeout)
                    status = "ok" if proc.returncode == 0 else "error"
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
                    status = "timeout"
            output = path.with_suffix(".log").read_text()
            match = re.search(r"MEASURE nodes=(\d+) summary=(true|false) evaluator=(true|false)", output)
            result = dict(case=case, mode=mode, status=status,
                          wall_seconds=round(time.monotonic() - start, 3))
            if match:
                result.update(nodes=int(match[1]), summary=match[2] == "true",
                              evaluator=match[3] == "true")
            results.append(result)
            (WORK / "results.json").write_text(json.dumps(results, indent=2) + "\n")
            print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
