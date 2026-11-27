#!/bin/sh
set -eu

optimizer=${1:-uplc}
fixtures=$(CDPATH= cd "$(dirname "$0")" && pwd)
revision=261766ad1d582bce8c86bad1af7a3b0e5355b21c
version=$("$optimizer" --version)
printf '%s\n' "$version"
case "$version" in
  *"$revision"*) ;;
  *) printf '%s\n' "Expected historical uplc revision $revision; refusing to overwrite buggy fixtures." >&2
     printf '%s\n' "Use regenerate-fixed.sh for the patched outputs." >&2
     exit 1 ;;
esac
"$optimizer" optimize --if textual --of textual \
  -i "$fixtures/ifthenelse.uplc" -o "$fixtures/ifthenelseopt.uplc"
for name in if-false-negative choose-list-empty choose-list-cons choose-data-integer \
  head-list-empty index-out-of-bounds un-i-data-bytes invalid-utf8 explicit-error \
  invalid-utf8-symbolic delayed-control unused-let case-field; do
  "$optimizer" optimize --if textual --of textual \
    -i "$fixtures/$name.uplc" -o "$fixtures/$name-opt.uplc"
done

"$optimizer" optimize --if textual --of textual \
  -i "$fixtures/tutorial/validator.uplc" -o "$fixtures/tutorial/validator-buggy.uplc"
