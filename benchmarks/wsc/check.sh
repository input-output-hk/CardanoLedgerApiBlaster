#!/usr/bin/env bash
# Run the original WSC containment goal against a selected solver revision.
set -euo pipefail
ulimit -c 0

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd -- "$script_dir"
mode="${1:-plain}"
blaster_dir=".lake/packages/Blaster"
if (( $# > 0 )); then shift; fi
case "$mode" in
  plain) proof=WscContainment/Plain.lean ;;
  auto) proof=WscContainment/Auto.lean ;;
  dx) proof=WscDx/Unshaped.lean ;;
  *) echo "usage: $0 [plain|auto|dx] [-KblasterRev=REF ...]" >&2; exit 2 ;;
esac
library=WscContainment
default_budget=1800
memory_max=8G
memory_high=7G
lean_memory=5000
if [[ "$mode" == dx ]]; then
  library=WscDx
  default_budget=120
  memory_max=4G
  memory_high=3G
  lean_memory=3000
fi
for argument in "$@"; do
  [[ "$argument" == -K* ]] || { echo "Expected a Lake -K configuration argument: $argument" >&2; exit 2; }
  if [[ "$argument" == -KblasterPath=* ]]; then
    blaster_dir="${argument#-KblasterPath=}"
  fi
done
budget="${WSC_TIMEOUT_SECONDS:-$default_budget}"
[[ "$budget" =~ ^[1-9][0-9]*$ ]] || { echo "WSC_TIMEOUT_SECONDS must be a positive integer" >&2; exit 2; }

# The scope includes Lean and its solver children. On hosts without systemd,
# use an equivalent container memory limit for comparisons (see README).
if [[ "${WSC_SCOPED:-0}" != 1 ]] && command -v systemd-run >/dev/null &&
    systemctl --user show-environment >/dev/null 2>&1; then
  exec systemd-run --user --scope --quiet --unit="wsc-tractability-$$" \
    -p "MemoryMax=$memory_max" -p "MemoryHigh=$memory_high" env WSC_SCOPED=1 \
    bash "$script_dir/check.sh" "$mode" "$@"
fi
if [[ "$mode" == dx && "${WSC_SCOPED:-0}" != 1 ]]; then
  echo "DX requires a hard memory scope; run with a user systemd manager or an equivalent container limit (see README)" >&2
  exit 2
fi

mkdir -p .lake
run_dir="$(mktemp -d "$script_dir/.lake/tractability.$mode.XXXXXX")"
echo "Results: $run_dir"
trap 'rm -f -- "$run_dir/libBlaster.so"' EXIT
{
  echo "mode=$mode"
  echo "wall_budget_seconds=$budget"
  echo "memory_max=$memory_max"
  echo "benchmark_commit=$(git -C ../.. rev-parse HEAD)"
  lean --version
  z3 --version
} > "$run_dir/environment.txt"
lake_command=(lake "$@")
deadline=$((SECONDS + budget))

run_stage() {
  local stage=$1
  shift
  local remaining=$((deadline - SECONDS))
  local result
  if (( remaining <= 0 )); then
    echo "TIMEOUT before $stage" | tee "$run_dir/result.txt"
    exit 124
  fi
  echo "Running $stage"
  if /usr/bin/time -v -o "$run_dir/$stage.time" \
      timeout --signal=TERM --kill-after=5s "${remaining}s" "$@" \
      > "$run_dir/$stage.log" 2>&1; then
    return
  else
    result=$?
  fi
  if [[ "$result" == 124 ]]; then
    echo "TIMEOUT during $stage" | tee "$run_dir/result.txt"
  else
    echo "FAILED during $stage (exit $result)" | tee "$run_dir/result.txt"
  fi
  tail -n 20 "$run_dir/$stage.log" >&2
  exit "$result"
}

# Refresh branch refs explicitly and record the commits actually tested.
run_stage update "${lake_command[@]}" -R update
cp lake-manifest.json "$run_dir/lake-manifest.json"
git -C "$blaster_dir" rev-parse HEAD > "$run_dir/blaster-commit.txt"
git -C "$blaster_dir" diff --stat > "$run_dir/blaster-dirty.txt"
run_stage build "${lake_command[@]}" build Blaster:shared "$library"
# A concurrent build must not replace a loaded shared library.
cp "$blaster_dir/.lake/build/lib/libBlaster.so" "$run_dir/libBlaster.so"
run_stage proof "${lake_command[@]}" env lean --plugin="$run_dir/libBlaster.so" \
  -j2 -s65536 "-M$lean_memory" "$proof"
if grep -q 'sorryAx' "$run_dir/proof.log"; then
  echo "FAILED: theorem depends on sorryAx" | tee "$run_dir/result.txt"
  exit 1
fi
echo "PASS: $mode containment proof compiled without sorryAx" | tee "$run_dir/result.txt"
cat "$run_dir/proof.log"
