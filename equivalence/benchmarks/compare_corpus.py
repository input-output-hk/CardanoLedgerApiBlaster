"""Compare corpus screens, excluding censored/error cases from speed ratios."""
import argparse
from collections import defaultdict
import json
from pathlib import Path
from statistics import median


def compare(before, after):
    left = {r["id"]: r for r in before}
    right = {r["id"]: r for r in after}
    if left.keys() != right.keys():
        raise ValueError("Case sets differ")
    groups = defaultdict(list)
    transitions = []
    for name, a in left.items():
        b = right[name]
        if a["request"] != b["request"]:
            raise ValueError(f"Request changed: {name}")
        same_outcome = (a["report"]["verdict"] == b["report"]["verdict"] and
                        a["report"].get("queries") == b["report"].get("queries"))
        common_complete = (not a["wall_timeout"] and not b["wall_timeout"] and same_outcome and
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
            "limits": "Single-pass screens are exploratory. Ratios use only cases completed on both sides "
                      "with matching verdict/query labels; errors and all wall timeouts are excluded. "
                      "Equal inconclusive labels do not establish equal semantics. Timed-out RSS is "
                      "descriptive: faster expansion may increase memory at the same wall deadline. "
                      "Scenarios are reported separately; compiler versions are not independent applications."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before", type=Path)
    parser.add_argument("after", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = compare(json.loads(args.before.read_text()), json.loads(args.after.read_text()))
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    for scenario, summary in result["scenarios"].items():
        print(scenario, {k: v for k, v in summary.items() if k != "rows"})


if __name__ == "__main__":
    main()
