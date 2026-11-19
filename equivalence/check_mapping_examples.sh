#!/usr/bin/env bash
# Build the mapping examples and their editable Playground entry point.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
lake build MappingExamples
