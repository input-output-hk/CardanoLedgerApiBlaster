#!/usr/bin/env bash
# Collect the UPLC-CAPE submissions as `.cbor_hex` scripts for Lean Blaster.
#
# UPLC-CAPE (https://github.com/IntersectMBO/UPLC-CAPE) contains, per benchmark
# scenario, several compilations of the same functionality (Plinth, Scalus,
# Plutarch, Aiken, OpShin, ...) as textual UPLC in
# `submissions/<scenario>/<submission>/*.uplc`. Each one is converted with the
# official `uplc` tool to hex-encoded CBOR-wrapped flat (the format of
# `Tests/Scripts/Auction/auction.cbor_hex`) and written to
# `<out>/<scenario>/<submission>.cbor_hex`.
#
# Usage: equivalence/collect_cape_examples.sh [CAPE_DIR] [OUT_DIR]
#   CAPE_DIR defaults to ../UPLC-CAPE, OUT_DIR to equivalence/examples.
#
# Requires nix. The first run builds `uplc` from the Plutus flake (dependencies
# come from the IOG binary cache); later runs reuse it. Set UPLC to use another
# `uplc` binary instead.

set -euo pipefail

PLUTUS_REF=1.71.0.0

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cape="${1:-$here/../../UPLC-CAPE}"
out="${2:-$here/examples}"

if [[ ! -d "$cape/submissions" ]]; then
  echo "error: $cape/submissions not found" >&2
  exit 1
fi

if [[ -z "${UPLC:-}" ]]; then
  echo "building uplc from plutus $PLUTUS_REF ..." >&2
  UPLC="$(nix build --accept-flake-config --no-link --print-out-paths \
    "github:IntersectMBO/plutus/$PLUTUS_REF#uplc")/bin/uplc"
fi

converted=0
failed=0
for uplc_file in "$cape"/submissions/*/*/*.uplc; do
  submission_dir="$(dirname "$uplc_file")"
  submission="$(basename "$submission_dir")"
  scenario="$(basename "$(dirname "$submission_dir")")"
  [[ "$scenario" == TEMPLATE ]] && continue

  # Disambiguate submissions with more than one .uplc file
  name="$submission"
  uplc_files=("$submission_dir"/*.uplc)
  if (( ${#uplc_files[@]} > 1 )); then
    name="${submission}_$(basename "$uplc_file" .uplc)"
  fi

  mkdir -p "$out/$scenario"
  if hex="$("$UPLC" convert --if textual --of hex -i "$uplc_file")"; then
    printf '%s' "$hex" > "$out/$scenario/$name.cbor_hex"
    converted=$((converted + 1))
  else
    echo "FAILED ${uplc_file#"$cape"/}" >&2
    failed=$((failed + 1))
  fi
done

echo "converted $converted scripts into $out"
(( failed == 0 ))
