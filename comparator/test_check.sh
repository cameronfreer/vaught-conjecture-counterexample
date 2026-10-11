#!/usr/bin/env bash
# Tests of comparator/check.sh's refusals and of its input-change test.
#
# Usage: bash comparator/test_check.sh WORK_DIR
#
# Runs on a clone of the committed HEAD in WORK_DIR/checkout (WORK_DIR must not exist), so the
# working tree of this checkout is never modified.  The clone uses this checkout's
# `.lake/packages` and `.lake/build` through symbolic links, so this checkout's root library must
# be built and up to date for HEAD (`lake build`).  Each case runs check.sh and asserts its exit
# status and its `FAILED: …` message:
#
#  1. OUT_DIR exists (an empty directory)             -> "already exists";
#  2. OUT_DIR is a symbolic link                      -> "already exists";
#  3. OUT_DIR passes through a symbolic link          -> "passes through a symbolic link";
#  4. --exact with a modified tracked input           -> "--exact: the inputs have uncommitted …";
#  5. the input-change test: a working-tree run with `comparator/README.md` already modified, in
#     which the same file is modified again after the run has taken its inventory of the inputs
#     -> the run fails with "inputs changed during the check: comparator/README.md".
#
# Cases 1–4 take seconds; case 5 is a whole check (a few minutes).  CI does not run this script;
# its output for a commit is recorded on the pull request that introduces or changes check.sh.
# Nothing is deleted; WORK_DIR can be removed afterwards.
set -euo pipefail
set -o noclobber
fail() { printf 'TEST FAILED: %s\n' "$*" >&2; exit 1; }
(( $# == 1 )) || { printf 'Usage: bash comparator/test_check.sh WORK_DIR\n' >&2; exit 2; }
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
work=$(realpath -s -m "$1")
[[ ! -e $work && ! -L $work ]] || fail "WORK_DIR $work already exists"
mkdir -- "$work"
commit=$(git -C "$repo" rev-parse HEAD)
clone=$work/checkout
git clone --quiet --no-local --no-checkout "$repo" "$clone"
git -C "$clone" switch --quiet --detach "$commit"
mkdir -- "$clone/.lake"
ln -s "$(readlink -f "$repo/.lake/packages")" "$clone/.lake/packages"
ln -s "$(readlink -f "$repo/.lake/build")" "$clone/.lake/build"
check=("bash" "$clone/comparator/check.sh")
printf 'Testing comparator/check.sh at %s in %s\n' "$commit" "$clone"

# expect NAME MESSAGE -- COMMAND...: the command fails (exit 1) with MESSAGE on its output.
expect() {
  local name=$1 message=$2 status=0
  shift 3
  "$@" > "$work/$name.log" 2>&1 || status=$?
  if [[ $status != 1 ]] || ! grep -Fq -- "$message" "$work/$name.log"; then
    tail -n 20 "$work/$name.log" >&2
    fail "$name: exit $status, wanted 1 with: $message"
  fi
  printf 'ok: %s: %s\n' "$name" "$(grep -F -- "$message" "$work/$name.log" | head -n 1)"
}

mkdir -- "$work/existing"
expect existing-out-dir "already exists" -- "${check[@]}" "$work/existing"
ln -s "$work/existing" "$work/link"
expect linked-out-dir "already exists" -- "${check[@]}" "$work/link"
expect through-link-out-dir "passes through a symbolic link" -- \
  "${check[@]}" "$work/link/new"

# A modified tracked input that no compilation reads: the build stays up to date.
readme=$clone/comparator/README.md
printf '\nA change for the tests of check.sh.\n' >> "$readme"
expect exact-with-change "--exact: the inputs have uncommitted changes or untracked files" -- \
  "${check[@]}" --exact "$work/out-exact"

# The input-change test: a working-tree run, the same file modified again after the inventory.
"${check[@]}" "$work/out-change" > "$work/input-change.log" 2>&1 &
pid=$!
# Step 2 begins only after the inventory is complete.
until grep -q '^== 2\.' "$work/input-change.log" 2> /dev/null; do
  kill -0 "$pid" 2> /dev/null || fail "input-change: the check ended before its inventory"
  sleep 1
done
grep -Fq 'Mode: working tree' "$work/input-change.log" ||
  fail "input-change: the run is not in the working-tree mode"
printf 'A second change, made during the run.\n' >> "$readme"
status=0
wait "$pid" || status=$?
message="inputs changed during the check: comparator/README.md"
if [[ $status != 1 ]] || ! grep -Fq -- "$message" "$work/input-change.log"; then
  tail -n 20 "$work/input-change.log" >&2
  fail "input-change: exit $status, wanted 1 with: $message"
fi
printf 'ok: input-change: %s\n' "$(grep -F -- "$message" "$work/input-change.log")"
printf 'All tests of comparator/check.sh passed at %s\n' "$commit"
