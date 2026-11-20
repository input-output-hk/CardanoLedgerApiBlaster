#!/bin/sh
set -eu

optimizer=${1:-uplc}
fixtures=$(dirname "$0")
"$optimizer" --version
"$optimizer" optimize --if textual --of textual \
  -i "$fixtures/ifthenelse.uplc" -o "$fixtures/ifthenelseopt.uplc"
for name in if-false-negative choose-list-empty choose-list-cons choose-data-integer \
  head-list-empty index-out-of-bounds un-i-data-bytes invalid-utf8 explicit-error \
  invalid-utf8-symbolic delayed-control unused-let case-field; do
  "$optimizer" optimize --if textual --of textual \
    -i "$fixtures/$name.uplc" -o "$fixtures/$name-opt.uplc"
done
