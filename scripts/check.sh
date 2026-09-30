#!/usr/bin/env bash
# Repository checks: toolchain in sync with InfinitaryLogic, build, no placeholders, headers, no
# non-standard axioms.
# Usage: bash scripts/check.sh [--no-build]
set -euo pipefail
cd "$(dirname "$0")/.."

modules() { { echo VaughtConjecture.lean; find VaughtConjecture -name '*.lean' | sort; }; }

echo "== toolchain sync"
IL_TC=.lake/packages/InfinitaryLogic/lean-toolchain
if [ -f "$IL_TC" ]; then
  if ! diff -q lean-toolchain "$IL_TC" >/dev/null; then
    echo "ERROR: lean-toolchain ($(cat lean-toolchain)) differs from InfinitaryLogic's ($(cat "$IL_TC"))" >&2
    exit 1
  fi
  echo "ok: lean-toolchain matches InfinitaryLogic ($(cat lean-toolchain))"
else
  echo "ERROR: InfinitaryLogic not fetched (run lake build first)" >&2
  exit 1
fi

if [ "${1:-}" != "--no-build" ]; then
  lake build
fi

echo "== placeholder check"
# `sorry`, `admit`, and stopgap options are never allowed in library sources.
if modules | xargs grep -nE '\b(sorry|admit)\b|maxHeartbeats|set_option autoImplicit true'; then
  echo "ERROR: placeholder or forbidden option found in library sources" >&2
  exit 1
fi
echo "ok: no placeholders"

echo "== headers"
# Every library module carries the Mathlib copyright header (the in-build header linter is
# inert for modules absent from an empty root, so it is checked here).
bad=0
for f in $(find VaughtConjecture -name '*.lean' | sort); do
  if ! head -1 "$f" | grep -q '^/-$' || ! sed -n 2p "$f" | grep -q '^Copyright (c) '; then
    echo "ERROR: $f lacks the copyright header" >&2; bad=1
  fi
done
[ "$bad" = 0 ] || exit 1
echo "ok: headers"

echo "== axiom audit (every source module)"
if [ -z "$(find VaughtConjecture -name '*.lean')" ]; then
  echo "skip: no library modules yet"
  exit 0
fi
mkdir -p .lake/audit
{
  modules | sed -e 's#\.lean$##' -e 's#/#.#g' -e 's#^#import #'
  sed -n '/^open Lean in/,$p' scripts/AxiomAudit.lean
} > .lake/audit/AxiomAuditAll.lean
lake env lean .lake/audit/AxiomAuditAll.lean
echo "ok: axiom audit passed"
