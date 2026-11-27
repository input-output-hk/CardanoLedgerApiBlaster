#!/bin/sh
set -eu

optimizer=${1:-uplc}
fixtures=$(CDPATH= cd "$(dirname "$0")" && pwd)
revision=1ef5a0eef37772e35b1e587f7a3b0afa61be4358
version=$("$optimizer" --version)
printf '%s\n' "$version"
case "$version" in
  *"$revision"*) ;;
  *) printf '%s\n' "Expected patched uplc revision $revision; refusing to overwrite fixed fixtures." >&2
     exit 1 ;;
esac
"$optimizer" optimize --if textual --of textual \
  -i "$fixtures/ifthenelse.uplc" -o "$fixtures/ifthenelse-fixed.uplc"
"$optimizer" optimize --if textual --of textual \
  -i "$fixtures/tutorial/validator.uplc" -o "$fixtures/tutorial/validator-fixed.uplc"
