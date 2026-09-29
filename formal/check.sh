#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

# Optional task-local toolchain; lean-toolchain pins the required version.
if [[ -x .tools/lean-4.19.0-linux/bin/lake ]]; then
  export PATH="$PWD/.tools/lean-4.19.0-linux/bin:$PATH"
fi

usage() {
  echo 'Usage: ./check.sh [--incremental --base <commit>] [--workers <positive integer>]' >&2
  exit 2
}
mode=full
base=
workers=2
while (($#)); do
  case "$1" in
    --incremental) [[ $mode == full ]] || usage; mode=incremental; shift ;;
    --base) [[ $# -ge 2 && -z $base ]] || usage; base=$2; shift 2 ;;
    --workers) [[ $# -ge 2 ]] || usage; workers=$2; shift 2 ;;
    *) usage ;;
  esac
done
[[ $workers =~ ^[1-9][0-9]*$ ]] || usage
[[ $mode == full && -z $base || $mode == incremental && -n $base ]] || usage

# Resolve the base before building. Never silently treat a missing or divergent
# base as an empty change set. The caller should fetch the intended base first.
if [[ $mode == incremental ]]; then
  git rev-parse --show-toplevel >/dev/null
  base=$(git rev-parse --verify "${base}^{commit}")
  git merge-base --is-ancestor "$base" HEAD || {
    echo 'Incremental base is not an ancestor of HEAD; run the full audit.' >&2
    exit 1
  }
fi

scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
# Discover all local sources, including ones not imported by BoundaryDraft.
find . -type d \( -path ./.lake -o -path ./.tools -o -path ./.git \) -prune -o \
  -type f -name '*.lean' ! -path ./Audit.lean -print0 | sort -z > "$scratch/sources"

if [[ $mode == incremental ]]; then
  # git diff COMMIT includes both staged and unstaged tracked changes, including
  # renames and deletions. --relative makes paths local to formal/.
  git diff --no-ext-diff --name-only --relative -z "$base" -- . > "$scratch/changed"
  git ls-files --others --exclude-standard -z -- . >> "$scratch/changed"
  # Ignored local Lean files cannot be reliably change-tracked: fail closed.
  git ls-files --others --ignored --exclude-standard -z -- . > "$scratch/ignored"
  while IFS= read -r -d '' path; do
    if [[ $path == *.lean && $path != Audit.lean && $path != .lake/* && $path != .tools/* ]]; then
      echo "Ignored local Lean source: $path; run the full audit." >&2
      exit 1
    fi
  done < "$scratch/ignored"
  # Any changed existing source must be discoverable by the full audit.
  declare -A discovered=() selected=()
  audit_changed=0
  while IFS= read -r -d '' path; do discovered["${path#./}"]=1; done < "$scratch/sources"
  while IFS= read -r -d '' path; do
    [[ $path == *.lean ]] || continue
    if [[ $path == Audit.lean ]]; then
      [[ -f $path ]] && audit_changed=1
      continue
    fi
    if [[ -f $path ]]; then
      if [[ ! -v discovered["$path"] ]]; then
        echo "Changed source not discovered: $path; run the full audit." >&2
        exit 1
      fi
      selected["$path"]=1
    fi
  done < "$scratch/changed"
fi

lake build

# Each source is compiled as a fresh module, auditing every public declaration
# it creates, even in modules not imported by the library root.
check_source() {
  local source=$1 directory=$2
  mkdir -p "$directory"
  local audit_source="$directory/SourceAudit.lean"
  printf '%s\n' 'import Lean.Elab.Command' 'import Lean.Util.CollectAxioms' > "$audit_source"
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
}

pids=() names=() logs=()
failed=0
finish_batch() {
  local index
  for index in "${!pids[@]}"; do
    if ! wait "${pids[index]}"; then
      printf 'Source audit failed: %s\n' "${names[index]}" >&2
      failed=1
    fi
    # Output in source order, regardless of worker completion order.
    if [[ -s ${logs[index]} ]]; then cat "${logs[index]}"; fi
  done
  pids=() names=() logs=()
}
index=0
while IFS= read -r -d '' source; do
  if [[ $mode == incremental && ! -v selected["${source#./}"] ]]; then continue; fi
  check_source "$source" "$scratch/$index" > "$scratch/$index.log" 2>&1 &
  pids+=("$!") names+=("$source") logs+=("$scratch/$index.log")
  ((index+=1))
  if ((${#pids[@]} == workers)); then finish_batch; fi
done < "$scratch/sources"
if ((${#pids[@]})); then finish_batch; fi
if ((failed)); then exit 1; fi

if [[ $mode == full ]]; then
  # The aggregate library audit runs only after every per-source check passes.
  lake env lean -DwarningAsError=true Audit.lean
else
  if ((audit_changed)); then lake env lean -DwarningAsError=true Audit.lean; fi
  echo 'Incremental developer check only; run ./check.sh for the full proof audit.'
fi
