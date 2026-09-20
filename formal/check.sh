#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

# Optional task-local toolchain. Otherwise use the caller's Lean/elan install;
# lean-toolchain pins the required version. No global configuration is changed.
if [[ -x .tools/lean-4.19.0-linux/bin/lake ]]; then
  export PATH="$PWD/.tools/lean-4.19.0-linux/bin:$PATH"
fi

lake build
# Check local modules with warnings treated as errors, including proof holes.
for source in BoundaryDraft/Algebra.lean BoundaryDraft/AnalyticCore.lean \
    BoundaryDraft/Specification.lean BoundaryDraft.lean Audit.lean; do
  lake env lean -DwarningAsError=true "$source"
done
