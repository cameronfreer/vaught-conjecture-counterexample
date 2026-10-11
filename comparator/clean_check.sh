#!/usr/bin/env bash
# The Comparator check on a fresh clone of the current commit, after a clean build.
#
# Usage: bash comparator/clean_check.sh [--paranoid] WORK_DIR [DEPS_DIR]
#
# Clones the committed HEAD of this repository (`git clone --no-local`, so uncommitted changes
# are not included) into WORK_DIR/checkout, gives it the dependency directory DEPS_DIR
# (default: this checkout's `.lake/packages`) as `.lake/packages`, builds the root library from
# nothing (`lake build`; the clone has no `.lake/build`), and runs `comparator/check.sh` there
# with outputs in WORK_DIR/out.  check.sh verifies that every dependency is at its pinned
# revision with no modified tracked file; the dependencies' own build outputs are reused, not
# rebuilt (rebuilding the pinned Mathlib fork takes hours; CI does so on a new pin).
# WORK_DIR must not exist or must be empty.  Afterwards WORK_DIR/out holds the logs and the
# hashes of every input, `.olean` and export; WORK_DIR/checkout can be deleted.
set -euo pipefail
paranoid=()
if [[ ${1:-} == --paranoid ]]; then paranoid=(--paranoid); shift; fi
if (( $# < 1 || $# > 2 )); then
  printf 'Usage: bash comparator/clean_check.sh [--paranoid] WORK_DIR [DEPS_DIR]\n' >&2
  exit 2
fi
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
deps=$(readlink -f "${2:-$repo/.lake/packages}")
[[ -d $deps ]]
mkdir -p "$1"
work=$(readlink -f "$1")
[[ -z $(ls -A "$work") ]] || { printf 'WORK_DIR %s is not empty\n' "$work" >&2; exit 2; }
commit=$(git -C "$repo" rev-parse HEAD)
if [[ -n $(git -C "$repo" status --porcelain --untracked-files=no) ]]; then
  printf 'note: uncommitted changes are not checked; checking commit %s\n' "$commit"
fi
git clone --quiet --no-local --no-checkout "$repo" "${work:?}/checkout"
git -C "$work/checkout" switch --quiet --detach "$commit"
[[ $(git -C "$work/checkout" rev-parse HEAD) == "$commit" ]]
[[ ! -e "$work/checkout/.lake" ]]
mkdir -p "$work/checkout/.lake" "$work/out/logs"
ln -s "$deps" "$work/checkout/.lake/packages"
cd "$work/checkout"
printf '== clean build of the root library at %s\n' "$commit"
start=$(date +%s)
lake build > "$work/out/logs/lake-build.log" 2>&1 || {
  tail -n 40 "$work/out/logs/lake-build.log" >&2; exit 1; }
printf 'built in %s s: %s\n' "$(( $(date +%s) - start ))" \
  "$(tail -n 1 "$work/out/logs/lake-build.log")"
(cd .lake/build/lib/lean && find . -name '*.olean' -print0 | sort -z | xargs -0 sha256sum) \
  > "$work/out/ROOT-OLEAN-SHA256SUMS"
bash comparator/check.sh "${paranoid[@]}" "$work/out"
printf 'Clean check passed at %s; outputs in %s (the checkout %s can be deleted)\n' \
  "$commit" "$work/out" "$work/checkout"
