#!/usr/bin/env bash
# Fetch the dependency build outputs (the Mathlib fork, InfinitaryLogic, ComputableModelTheory)
# from the public Lake artifact cache into $LAKE_CACHE_DIR, for the cold dependency path of CI.
# See docs/ci/remote-cache.md.
#
# Usage: CACHE_BASE=https://<public read host> LAKE_CACHE_DIR=<dir> bash scripts/ci/lake-cache-get.sh
#
# Reads are anonymous GETs (Lake cannot sign downloads), so no credential is involved.  The script
# never fails the job: a package whose lookup or download does not complete has its mappings
# removed again, so `lake build` compiles that package from source exactly as without the cache.
# Under GitHub Actions, `LAKE_CACHE_DIR` is exported to later steps only if at least one package
# was fetched completely; otherwise the directory is removed and nothing is exported.
set -euo pipefail

: "${LAKE_CACHE_DIR:?LAKE_CACHE_DIR must be set}"
base="${CACHE_BASE:-}"
base="${base%/}"
case "$base" in
  https://?*) ;;
  *)
    echo "::warning::CACHE_BASE is not an https URL; skipping the Lake artifact cache"
    exit 0
    ;;
esac

tmp="${RUNNER_TEMP:-$(mktemp -d)}"
cfg="$tmp/lake-cache-read.toml"
cat > "$cfg" <<TOML
[[cache.service]]
name = "vc-public"
kind = "s3"
artifactEndpoint = "$base/artifacts"
revisionEndpoint = "$base/revisions"
TOML
mkdir -p "$LAKE_CACHE_DIR"

# fetch <package> <GitHub repository> <max revisions>
# Looks up the mappings published for the package's checked-out revision (backtracking at most
# <max revisions> commits) and downloads every artifact they name.  Two attempts; the second only
# downloads what the first did not verify.  A missing publication is not retried.
fetch() {
  local pkg="$1" repo="$2" revs="$3" log="$tmp/lake-cache-get-$1.log" _
  for _ in 1 2; do
    if LAKE_CONFIG="$cfg" lake cache get --service vc-public --package "$pkg" \
        --repo "$repo" --max-revs="$revs" > "$log" 2>&1; then
      grep -E '^(warning|error)' "$log" || true
      echo "$pkg: $(grep -c 'downloaded artifact' "$log" || true) artifacts downloaded"
      return 0
    fi
    grep -E '^(warning|error)' "$log" | head -n 20 || true
    if grep -qE 'no outputs found|outputs not found' "$log"; then
      break
    fi
  done
  # `lake cache get` writes the mappings before it downloads the artifacts; drop them, so that no
  # mapping names an artifact that is not in the cache.
  rm -rf "${LAKE_CACHE_DIR:?}/outputs/$pkg" "${LAKE_CACHE_DIR:?}/revisions/$pkg"
  return 1
}

hits=()
misses=()
# The fork is published for its exact pinned revision only: an older fork revision would name
# about 1,700 artifacts of which few would match.
if fetch mathlib cameronfreer/mathlib4 1; then hits+=(mathlib); else misses+=(mathlib); fi
if fetch InfinitaryLogic cameronfreer/infinitary-logic 20; then
  hits+=(InfinitaryLogic)
else
  misses+=(InfinitaryLogic)
fi
if fetch ComputableModelTheory cameronfreer/computable-model-theory 20; then
  hits+=(ComputableModelTheory)
else
  misses+=(ComputableModelTheory)
fi

echo "::notice::Lake artifact cache: fetched [${hits[*]:-}], not available [${misses[*]:-}]"
if [ "${#hits[@]}" -gt 0 ]; then
  if [ -n "${GITHUB_ENV:-}" ]; then
    echo "LAKE_CACHE_DIR=$LAKE_CACHE_DIR" >> "$GITHUB_ENV"
  fi
else
  rm -rf "${LAKE_CACHE_DIR:?}"
fi
