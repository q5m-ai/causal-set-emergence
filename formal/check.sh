#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

# Optional task-local toolchain. Otherwise use the caller's Lean/elan install;
# lean-toolchain pins the required version. No global configuration is changed.
if [[ -x .tools/lean-4.19.0-linux/bin/lake ]]; then
  export PATH="$PWD/.tools/lean-4.19.0-linux/bin:$PATH"
fi

lake build
# Discover every local Lean source, including modules not yet imported by the
# library root. Never traverse downloaded dependencies or the local toolchain.
# Run the axiom audit last, after all sources have passed the warning gate.
# Use a checked pipeline, not process substitution: discovery errors must fail.
source_list=$(mktemp)
trap 'rm -f "$source_list"' EXIT
find . -type d \( -path ./.lake -o -path ./.tools -o -path ./.git \) -prune -o \
  -type f -name '*.lean' ! -path ./Audit.lean -print0 | sort -z > "$source_list"
while IFS= read -r -d '' source; do
  lake env lean -DwarningAsError=true "$source"
done < "$source_list"
lake env lean -DwarningAsError=true Audit.lean
