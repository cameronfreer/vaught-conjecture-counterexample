#!/usr/bin/env bash
# Dependency manifest of the main theorem and its components, for reproducible cleanup audits.
#
# Usage: bash scripts/manifest.sh [OUT]   write the manifest to OUT
#                                          (default .lake/audit/manifest.txt)
#        bash scripts/manifest.sh --test  check that a missing theorem name fails with an error
#
# Run after `lake build`, on the checkout that was built.  The manifest records the checked commit,
# tree and toolchain, then (from `scripts/Manifest.lean`) for each theorem in TARGETS: its
# elaborated statement, its declaration dependency cone (constants reachable through types and
# proof terms; the library declarations among them are listed with their modules), and its axioms,
# checked to equal `collectAxioms`; and, separately, the import closure of TOP.  The import closure
# is what the top module imports; the cone is what the proofs actually use.  This is a record for
# review, not a check: the library-wide axiom audit stays in `scripts/check.sh`.  It fails (non-zero
# exit, nothing written) if a target name is not found.
set -euo pipefail
cd "$(dirname "$0")/.."

TOP=VaughtConjecture.MainTheorem.GrowthLevelRoute
TARGETS="VaughtConjecture.MainTheorem.densitySentence_hasThinAlephOneSpectrum_levels
VaughtConjecture.Realization.receivingResidualReceiving_of_padded
VaughtConjecture.Realization.hollowReceiving_levels
VaughtConjecture.Expansion.receivingStableCappedReceiving_levels
VaughtConjecture.StageType.hasLadderGrowthCarriersStableAtSeed_levels"

mkdir -p .lake/audit
DRIVER=.lake/audit/ManifestDriver.lean
{
  echo "import $TOP"
  sed -n '/^import Lean$/,$p' scripts/Manifest.lean
} > "$DRIVER"

# run TARGETS BODY_FILE: elaborate the driver, writing the per-target part of the manifest.
run() {
  VC_MANIFEST_TOP="$TOP" VC_MANIFEST_TARGETS="$1" VC_MANIFEST_OUT="$2" lake env lean "$DRIVER"
}

if [ "${1:-}" = "--test" ]; then
  echo "== manifest test: a missing theorem name must fail"
  body=.lake/audit/manifest-test.body
  rm -f "$body"
  missing=VaughtConjecture.MainTheorem.manifestTestMissingName
  if log=$(run "$TARGETS $missing" "$body" 2>&1); then
    echo "$log"
    echo "ERROR: the manifest accepted the missing theorem name $missing" >&2
    exit 1
  fi
  if ! grep -q "theorem $missing not found" <<<"$log" || [ -e "$body" ]; then
    echo "$log"
    echo "ERROR: the manifest failed on $missing without the expected message, or wrote output" >&2
    exit 1
  fi
  grep "not found" <<<"$log"
  echo "ok: a missing theorem name fails with a non-zero exit and writes nothing"
  exit 0
fi

OUT=${1:-.lake/audit/manifest.txt}
body="$OUT.body"
rm -f "$OUT" "$body"
run "$TARGETS" "$body"
{
  echo "VaughtConjecture dependency manifest"
  echo "commit: $(git rev-parse HEAD)"
  echo "tree: $(git rev-parse 'HEAD^{tree}')"
  if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
    echo "working tree: has uncommitted changes to tracked files (the manifest describes them)"
  else
    echo "working tree: clean (tracked files)"
  fi
  echo "lean-toolchain: $(cat lean-toolchain)"
  echo "lean --version: $(lake env lean --version)"
  echo "dependency pins (lake-manifest.json):"
  jq -r '.packages[] | "  \(.name) \(.rev)"' lake-manifest.json
  echo "top module: $TOP"
  echo
  cat "$body"
} > "$OUT"
rm -f "$body"
echo "manifest written to $OUT"
sed -n '/^== summary$/,/^$/p' "$OUT"
