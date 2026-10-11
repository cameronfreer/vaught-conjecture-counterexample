#!/usr/bin/env bash
# The Comparator check on a fresh clone of the current commit, after a clean build.
#
# Usage: bash comparator/clean_check.sh [--paranoid] WORK_DIR [DEPS_DIR]
#
# WORK_DIR must not exist; it is created, and neither it nor any parent may be or pass through a
# symbolic link.  The script clones the committed HEAD of this repository (`git clone
# --no-local`, so uncommitted changes are not included) into WORK_DIR/checkout, gives it the
# dependency directory DEPS_DIR (default: this checkout's `.lake/packages`) as `.lake/packages`,
# builds the root library from nothing (`lake build`; the clone has no `.lake/build`), with the
# log and the hashes of its `.olean` files in WORK_DIR/clean-build, and runs
# `comparator/check.sh --exact` there with outputs in WORK_DIR/out.
#
# check.sh verifies that every dependency's git checkout is at its pinned revision with no
# modified tracked file.  The dependencies' cached build outputs are reused as they are: they
# are not rebuilt here and not authenticated against their sources (CI rebuilds them from
# source when a pin changes).  Nothing is deleted; afterwards WORK_DIR/checkout can be removed.
set -euo pipefail
set -o noclobber
fail() { printf 'FAILED: %s\n' "$*" >&2; exit 1; }
paranoid=()
if [[ ${1:-} == --paranoid ]]; then paranoid=(--paranoid); shift; fi
if (( $# < 1 || $# > 2 )); then
  printf 'Usage: bash comparator/clean_check.sh [--paranoid] WORK_DIR [DEPS_DIR]\n' >&2
  exit 2
fi
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
deps=$(readlink -f "${2:-$repo/.lake/packages}")
[[ -d $deps ]] || fail "dependency directory $deps does not exist"
work=$(realpath -s -m "$1")
[[ ! -e $work && ! -L $work ]] || fail "WORK_DIR $work already exists"
parent=$(dirname "$work")
[[ -d $parent ]] || fail "parent directory $parent does not exist"
[[ $(realpath -e "$parent") == "$(realpath -s -e "$parent")" ]] ||
  fail "WORK_DIR $work passes through a symbolic link"
mkdir -- "$work"
commit=$(git -C "$repo" rev-parse HEAD)
if [[ -n $(git -C "$repo" status --porcelain --untracked-files=all) ]]; then
  printf 'note: uncommitted changes and untracked files are not checked; checking commit %s\n' \
    "$commit"
fi
git clone --quiet --no-local --no-checkout "$repo" "$work/checkout"
git -C "$work/checkout" switch --quiet --detach "$commit"
[[ $(git -C "$work/checkout" rev-parse HEAD) == "$commit" ]] || fail "clone is not at $commit"
[[ ! -e "$work/checkout/.lake" ]] || fail "the fresh clone already has a .lake directory"
mkdir -- "$work/checkout/.lake" "$work/clean-build"
ln -s "$deps" "$work/checkout/.lake/packages"
cd "$work/checkout"
printf '== clean build of the root library at %s\n' "$commit"
start=$(date +%s)
lake build > "$work/clean-build/lake-build.log" 2>&1 || {
  tail -n 40 "$work/clean-build/lake-build.log" >&2
  fail "lake build failed"
}
printf 'built in %s s: %s\n' "$(( $(date +%s) - start ))" \
  "$(tail -n 1 "$work/clean-build/lake-build.log")"
(cd .lake/build/lib/lean && find . -name '*.olean' -print0 | sort -z | xargs -0 sha256sum) \
  > "$work/clean-build/ROOT-OLEAN-SHA256SUMS"
bash comparator/check.sh --exact "${paranoid[@]}" "$work/out"
printf 'Clean check passed at %s; outputs in %s and %s (the checkout %s can be removed)\n' \
  "$commit" "$work/out" "$work/clean-build" "$work/checkout"
