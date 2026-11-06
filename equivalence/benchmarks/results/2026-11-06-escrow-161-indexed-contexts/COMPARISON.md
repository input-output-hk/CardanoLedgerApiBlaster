# Indexed context lookups and constructor-cache ownership

The [design and patch instructions](../../optimizations/CONTEXT-INDEX.md) explain
both changes. The original constructor/selector patch is retained unchanged;
this run additionally applies `context-index-and-cache-ownership.patch`.
The two exact patches and their hashes are beside this report.

## Focused measurements

| Workload | Before (ms) | After (ms) |
|---|---:|---:|
| Constructor values: 1,000 | 7.732 | 1.072 |
| Constructor values: 2,000 | 35.682 | 2.012 |
| Constructor values: 4,000 | 124.058 | 3.741 |
| Constructor values: 8,000 | 707.996 | 7.904 |
| 2,000 lookups, 1,000 inactive entries | 3.266 | 0.079 |
| 2,000 lookups, 2,000 inactive entries | 5.248 | 0.083 |
| 2,000 lookups, 4,000 inactive entries | 13.871 | 0.091 |
| 2,000 lookups, 8,000 inactive entries | 22.762 | 0.115 |
| 2,000 lookups, 16,000 inactive entries | 43.948 | 0.155 |

These are individual synthetic measurements. Context-history construction is
excluded from lookup time. All lookup checksums are 84,000, confirming the
same visible root value. Ground-value recognition is isolated from normal
expression rewriting, so the context-map change does not explain that speedup.

A deterministic 1,000-update test compares the new index with the old list
semantics across active-scope changes, exact-scope queries, repeated writes,
ancestor writes and dormant-scope reuse. It also validates membership/path
consistency and absent keys. The index preserves newest-write precedence,
including when an ancestor has a smaller scope ID but a later write.

## Actual scripts

The native isolated 1.64 execution control now optimizes in 0.357 and 0.360 s,
compared with 0.467 and 0.452 s for the pre-fix both-enabled ablation binary.
These are two samples per version, not a general throughput claim. The before
binary contains disabled profiling hooks; the after binary has those hooks
removed. This control comparison therefore does not perfectly isolate the
fixes from disabled-hook overhead.
The isolated 1.61 execution still reaches its 20-second observation deadline.
The isolated controls are optimizer diagnostics; they omit ledger guards and
do not establish ledger-valid equivalence or discrepancy.

The full query retains the ledger-validity premise, 5,000 steps, maxima 1/1/1,
solver timeout 60 s and wall timeout 180 s. It still reaches the first
acceptance-preservation query's preprocessing wall deadline: 181.596 s overall.
No new solver result or discrepancy was obtained. See
[the full report](full-60-180/SUMMARY.md).

All temporary profiling hooks and ablation switches were removed before these
measurements. The dependency manifest pin is unchanged. Native reproducer
sources, raw timing logs, harness source and provenance receipts are saved here.
Baseline reproducer binary hashes were not captured before rebuilding; baseline
source and the exact prior patch are retained. After-fix executable hashes are
recorded in `provenance.json`.

Validation passed: full `Tests.Equivalence`, Blaster's `Tests.Optimize`,
`Tests.FixedIssues.Issue348`, `Tests.Smt.SmtList.SmtListGet`, and all 12 CLI tests
(including exported Lean compilation and witness replay, 329.992 s).
The patch applies cleanly after the original optimization patch.
