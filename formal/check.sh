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
# Use a checked pipeline, not process substitution: discovery errors must fail.
source_list=$(mktemp)
audit_dir=$(mktemp -d)
cleanup() {
  rm -f "$source_list"
  rm -rf "$audit_dir"
}
trap cleanup EXIT
find . -type d \( -path ./.lake -o -path ./.tools -o -path ./.git \) -prune -o \
  -type f -name '*.lean' ! -path ./Audit.lean -print0 | sort -z > "$source_list"
while IFS= read -r -d '' source; do
  # Recheck the source in a fresh current module and audit every public
  # declaration created by that source. This catches custom axioms in files
  # that are deliberately not imported by the library root.
  audit_source="$audit_dir/SourceAudit.lean"
  cat > "$audit_source" <<'LEAN'
import Lean.Elab.Command
import Lean.Util.CollectAxioms
LEAN
  cat "$source" >> "$audit_source"
  cat >> "$audit_source" <<'LEAN'

run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  let declarations := env.constants.toList.filter fun (name, _) =>
    (env.getModuleIdxFor? name).isNone && !name.isInternalDetail
  for (declaration, _) in declarations do
    for dependency in (← Lean.collectAxioms declaration) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {declaration}"
LEAN
  lake env lean -DwarningAsError=true "$audit_source"
done < "$source_list"

# Run the aggregate library audit last as a readable inventory of the public
# BoundaryDraft API and a transitive check across imported module boundaries.
lake env lean -DwarningAsError=true Audit.lean
