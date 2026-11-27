"""Compare corpus screens, excluding censored/error cases from speed ratios."""
import argparse
from collections import defaultdict
import json
from pathlib import Path
from statistics import median


def load_run(path):
    manifest = json.loads(path.with_name("corpus.json").read_text())
    provenance_name = "provenance.json" if path.name == "results.json" else f"{path.stem}-provenance.json"
    provenance = json.loads(path.with_name(provenance_name).read_text())
    cases = {case["id"]: case for case in manifest["cases"]}
    rows = json.loads(path.read_text())
    for row in rows:
        name = row["id"]
        if name not in cases:
            raise ValueError(f"Case missing from the manifest for {path}: {name}")
        case = cases[name]
        request = row["request"]
        if (request["left"], request["right"]) != (case["script"], case["partner"]):
            raise ValueError(f"Fixture paths differ from the manifest for {path}: {name}")
        row["fixture_hashes"] = (case["binary_sha256"], case["partner_binary_sha256"])
    return {"results": rows, "wall_seconds": float(provenance["wall_seconds"])}


def compare(before, after):
    if before["wall_seconds"] != after["wall_seconds"]:
        raise ValueError(f"Wall deadline changed: {before['wall_seconds']}s vs {after['wall_seconds']}s")
    left = {r["id"]: r for r in before["results"]}
    right = {r["id"]: r for r in after["results"]}
    if left.keys() != right.keys():
        raise ValueError("Case sets differ")
    groups = defaultdict(list)
    transitions = []
    for name, a in left.items():
        b = right[name]
        if a["request"] != b["request"]:
            raise ValueError(f"Request changed: {name}")
        if a["fixture_hashes"] != b["fixture_hashes"]:
            raise ValueError(f"Fixture hashes changed: {name}")
        same_outcome = (a["report"]["verdict"] == b["report"]["verdict"] and
                        a["report"].get("queries") == b["report"].get("queries"))
        common_complete = (a["exit_code"] == b["exit_code"] == 0 and
                           not a["wall_timeout"] and not b["wall_timeout"] and same_outcome and
                           a["report"]["verdict"] not in {"error", "runner_error"})
        row = {"id": name, "same_outcome": same_outcome,
               "common_complete": common_complete,
               "baseline_verdict": a["report"]["verdict"], "candidate_verdict": b["report"]["verdict"],
               "baseline_timeout": a["wall_timeout"], "candidate_timeout": b["wall_timeout"],
               "baseline_preprocessing_seconds": a["preprocessing_seconds"],
               "candidate_preprocessing_seconds": b["preprocessing_seconds"],
               "baseline_rss_bytes": a["max_rss_bytes"], "candidate_rss_bytes": b["max_rss_bytes"]}
        if common_complete and a["preprocessing_seconds"] > 0:
            row["preprocessing_ratio"] = b["preprocessing_seconds"] / a["preprocessing_seconds"]
            row["rss_ratio"] = b["max_rss_bytes"] / a["max_rss_bytes"]
        if not same_outcome or a["wall_timeout"] != b["wall_timeout"]:
            transitions.append(row)
        groups[a["scenario"]].append(row)
    summaries = {}
    for scenario, rows in groups.items():
        ratios = [r for r in rows if "preprocessing_ratio" in r]
        summaries[scenario] = {
            "cases": len(rows), "common_complete": len(ratios),
            "median_preprocessing_ratio": median(r["preprocessing_ratio"] for r in ratios) if ratios else None,
            "median_rss_ratio": median(r["rss_ratio"] for r in ratios) if ratios else None,
            "baseline_timeouts": sum(r["baseline_timeout"] for r in rows),
            "candidate_timeouts": sum(r["candidate_timeout"] for r in rows),
            "outcome_changes": sum(not r["same_outcome"] for r in rows), "rows": rows}
    return {"scenarios": summaries, "transitions": transitions,
            "limits": "Single-pass screens are exploratory. Ratios require successful worker exits on both "
                      "sides and matching verdict/query labels. Errors and all wall timeouts are excluded. "
                      "Equal inconclusive labels do not establish equal semantics. Timed-out RSS is "
                      "descriptive: faster expansion may increase memory at the same wall deadline. "
                      "Scenarios are reported separately; compiler versions are not independent applications."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before", type=Path)
    parser.add_argument("after", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        result = compare(load_run(args.before), load_run(args.after))
    except (OSError, ValueError, KeyError) as error:
        parser.error(str(error))
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    for scenario, summary in result["scenarios"].items():
        print(scenario, {k: v for k, v in summary.items() if k != "rows"})


if __name__ == "__main__":
    main()
