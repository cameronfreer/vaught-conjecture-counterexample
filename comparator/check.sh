#!/usr/bin/env bash
# Comparator check of the solution module against the reference statement.
#
# Usage: bash comparator/check.sh [--paranoid] [OUT_DIR]
#
# Run at the root of a checkout whose root library is built (`lake build`) and whose
# dependencies are at the pinned revisions; `comparator/clean_check.sh` runs it on a fresh clone
# after a clean build of the root library.  Needs bwrap, jq, python3 and the pinned toolchain
# (whose `lake comparator`, `leanexport` and `nanoda_bin` are used).  Nothing is fetched and
# nothing in the checkout is written outside `.lake/comparator` (or OUT_DIR).
#
# Steps (each fails the script on error):
#  1. records the commit, the toolchain and the hashes of every input;
#  2. checks the dependency pins, and that the root library build is up to date;
#  3. checks that the declarations of comparator/Challenge.lean are those of the reviewed
#     specification (a SHA-256 of the comment-free text);
#  4. compiles the reference statement in a sandbox that sees only Mathlib and Mathlib's own
#     dependencies, and checks its transitive import closure;
#  5. compiles the solution module, its axiom test and the three expected failures in sandboxes
#     that do not see the compiled reference statement;
#  6. exports each with `leanexport` and runs `lake comparator` (Lean's kernel and nanoda) on the
#     solution, which must be accepted, and on each expected failure, which must be rejected with
#     its intended diagnostic.  With --paranoid, the solution is also checked by every external
#     checker bundled with the toolchain (`lake comparator --paranoid`: leanchecker-paranoid,
#     lean4lean, nanoda, con-leche and con-ron); this takes about ten minutes more.
set -euo pipefail
paranoid=()
if [[ ${1:-} == --paranoid ]]; then paranoid=(--paranoid); shift; fi
if (( $# > 1 )) || [[ ${1:-} == -* ]]; then
  printf 'Usage: bash comparator/check.sh [--paranoid] [OUT_DIR]\n' >&2
  exit 2
fi
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
if [[ -n ${1:-} ]]; then
  mkdir -p "$1"
  out=$(readlink -f "$1")
else
  mkdir -p .lake/comparator
  out=$(mktemp -d "$repo/.lake/comparator/run.XXXXXX")
fi
printf 'Outputs: %s\n' "$out"
src=$repo/comparator
log() { printf '== %s\n' "$*"; }

# The comment-free declarations of `Palomar/Challenge.lean` of
# cameronfreer/vaught-conjecture-palomar at commit 032ccb7 (`comparator/scripts/declarations.py`).
reviewed_declarations=37ea343194108b99620ce478081db4e0ee55f7375974205c2e31e1c3c735d3a2
# The upstream mathlib4 commit (leanprover-community/mathlib4, "chore: bump toolchain to
# v4.35.0-rc3 (#44172)") that the pinned fork extends with `Mathlib/ModelTheory/Infinitary`.
mathlib_upstream=c55e6e786f49471c72fbddbec5415808896aec1e
target=PalomarChallenge.independent_challenge

# ---------------------------------------------------------------------------------------------
log "1. inputs"
mkdir -p "$out/build" "$out/export" "$out/logs" "$out/tmp"
git rev-parse HEAD > "$out/commit.txt"
git status --porcelain --untracked-files=no > "$out/worktree-status.txt"
expected_toolchain=$(cat lean-toolchain)
tools=$(dirname "$(readlink -f "$(elan which lean)")")
toolchain_dir=${expected_toolchain//\//--}
[[ $(basename "$(dirname "$tools")") == "${toolchain_dir//:/---}" ]] || {
  printf 'toolchain %s does not match lean-toolchain %s\n' "$tools" "$expected_toolchain" >&2
  exit 1
}
{
  printf 'lean-toolchain: %s\n' "$expected_toolchain"
  "$tools/lean" --version
  "$tools/lake" --version
  "$tools/leanexport" --help 2>&1 | head -n 1 || true
  "$tools/nanoda_bin" --help 2>&1 | head -n 1 || true
  /usr/bin/bwrap --version
} > "$out/toolchain.txt"
(cd "$tools" && sha256sum lean lake leanexport nanoda_bin) > "$out/TOOL-SHA256SUMS"
(find comparator -type f \( -name '*.lean' -o -name '*.sh' -o -name '*.py' -o -name '*.json' \
    -o -name '*.md' \) -print0 | sort -z | xargs -0 sha256sum
  sha256sum lean-toolchain lakefile.toml lake-manifest.json) > "$out/SOURCE-SHA256SUMS"

# ---------------------------------------------------------------------------------------------
log "2. dependency pins and the root library build"
diff -q lean-toolchain .lake/packages/InfinitaryLogic/lean-toolchain
jq -er '.packages[] | if .type != "git" then error("git dependency required")
  else [.name, .rev] | @tsv end' lake-manifest.json > "$out/dependency-pins.tsv"
declare -A dep_root
while IFS=$'\t' read -r name rev; do
  [[ $name =~ ^[A-Za-z_][A-Za-z0-9_-]*$ && $rev =~ ^[0-9a-f]{40}$ ]]
  root=$(readlink -f ".lake/packages/$name")
  [[ $(git -C "$root" rev-parse HEAD) == "$rev" ]] || {
    printf 'dependency %s is not at its pinned revision %s\n' "$name" "$rev" >&2; exit 1; }
  git -C "$root" diff --quiet HEAD -- || {
    printf 'dependency %s has modified tracked files\n' "$name" >&2; exit 1; }
  dep_root[$name]=$root
done < "$out/dependency-pins.tsv"
# Up to date: Lake exits nonzero if any module of the root library would need rebuilding.
lake build --no-build > "$out/logs/lake-build-no-build.log" 2>&1 || {
  printf 'the root library build is missing or out of date; run lake build first\n' >&2
  cat "$out/logs/lake-build-no-build.log" >&2
  exit 1
}
# The pinned Mathlib is upstream mathlib4 plus new files only.
mathlib=${dep_root[mathlib]}
git -C "$mathlib" merge-base --is-ancestor "$mathlib_upstream" HEAD
git -C "$mathlib" diff --name-only "$mathlib_upstream" HEAD > "$out/mathlib-fork-changes.txt"
fork_files='^(Mathlib\.lean|Mathlib/ModelTheory/Infinitary/[A-Za-z]+\.lean|MathlibTest/[A-Za-z]+\.lean)$'
if grep -vE "$fork_files" \
    "$out/mathlib-fork-changes.txt"; then
  printf 'the pinned Mathlib changes upstream files beyond Mathlib/ModelTheory/Infinitary\n' >&2
  exit 1
fi
git -C "$mathlib" diff --diff-filter=A --name-only "$mathlib_upstream" HEAD -- \
  'Mathlib/ModelTheory/Infinitary' > "$out/tmp/added.txt"
git -C "$mathlib" diff --name-only "$mathlib_upstream" HEAD -- 'Mathlib/ModelTheory/Infinitary' \
  | cmp -s - "$out/tmp/added.txt"

# ---------------------------------------------------------------------------------------------
log "3. the reference declarations"
python3 comparator/scripts/declarations.py comparator/Challenge.lean \
  > "$out/challenge-declarations.lean"
actual=$(sha256sum < "$out/challenge-declarations.lean" | cut -d' ' -f1)
[[ $actual == "$reviewed_declarations" ]] || {
  printf 'comparator/Challenge.lean declarations changed: %s\n' "$actual" >&2; exit 1; }
printf 'ok: declarations of comparator/Challenge.lean match the reviewed specification\n'

# ---------------------------------------------------------------------------------------------
# Sandboxes: the whole file system read-only, home directories and /tmp hidden, no network, an
# empty environment.  Each compile sees the toolchain, the source directory `comparator/` and
# exactly the dependency roots passed to it, and writes only its own build directory.
base_sandbox=(/usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run/user
  --tmpfs /tmp --dev /dev --proc /proc --clearenv --unshare-all --die-with-parent --new-session
  --ro-bind "$(dirname "$tools")" "$(dirname "$tools")" --ro-bind "$src" "$src"
  --setenv PATH "$tools:/usr/bin:/bin" --setenv HOME /tmp --chdir "$src")
mathlib_deps=$(jq -r '.packages[].name' "$mathlib/lake-manifest.json")
reference_roots=("$mathlib")
for name in $mathlib_deps; do reference_roots+=("${dep_root[$name]}"); done
all_roots=("${dep_root[@]}")

# run_in ROOTS_VAR LEAN_PATH WRITABLE_DIR -- COMMAND...
run_in() {
  local -n roots=$1
  local lean_path=$2 writable=$3 binds=()
  shift 4
  for r in "${roots[@]}"; do binds+=(--ro-bind "$r" "$r"); done
  "${base_sandbox[@]}" "${binds[@]}" --bind "$writable" "$writable" \
    --setenv LEAN_PATH "$lean_path" -- "$@"
}
path_of() {  # the LEAN_PATH of the given dependency roots and extra directories
  local p="" r
  for r in "$@"; do
    if [[ -d "$r/.lake/build/lib/lean" ]]; then p+="$r/.lake/build/lib/lean:"; else p+="$r:"; fi
  done
  printf '%s%s' "$p" "$tools/../lib/lean"
}
# compile MODULE BUILD_DIR ROOTS_VAR LEAN_PATH [LEAN_OPTIONS...]
compile() {
  local module=$1 build=$2 roots=$3 lean_path=$4 file
  shift 4
  file=${module//.//}.lean
  mkdir -p "$(dirname "$build/$file")"
  run_in "$roots" "$lean_path" "$build" -- "$tools/lean" -R . -DautoImplicit=false \
    -DrelaxedAutoImplicit=false "$@" -o "$build/${file%.lean}.olean" "$file"
}
strict=(-DwarningAsError=true -Dweak.linter.mathlibStandardSet=true
  -Dweak.linter.style.longFile=1500 -Dweak.linter.style.longFileDefValue=1500)

# ---------------------------------------------------------------------------------------------
log "4. the reference statement, compiled against Mathlib alone"
challenge=$out/build/challenge
mkdir -p "$challenge"
reference_path=$(path_of "${reference_roots[@]}")
reference_path="$challenge:$reference_path"
compile Challenge "$challenge" reference_roots "$reference_path" > "$out/logs/challenge.log" 2>&1
# Exactly one diagnostic: the deliberate `sorry` of the reference theorem.
grep -c 'warning:' "$out/logs/challenge.log" | grep -qx 1
grep -q 'Challenge.lean:[0-9]*:[0-9]*: warning: declaration uses `sorry`' "$out/logs/challenge.log"
! grep -q 'error:' "$out/logs/challenge.log"
# The import closure, read from the compiled `.olean` headers in the same sandbox.
closure_runner=$out/build/closure
mkdir -p "$closure_runner"
cp comparator/scripts/ImportClosure.lean "$closure_runner/"
reference_read=("${reference_roots[@]}" "$challenge")
run_in reference_read "$reference_path" "$closure_runner" -- \
  "$tools/lean" --run "$closure_runner/ImportClosure.lean" Challenge \
  > "$out/challenge-import-closure.txt"
# Every module is in Init, Std, Lean, Mathlib or one of Mathlib's own dependencies, and none is
# in a part of Mathlib that the pinned fork adds.
allowed='^(Challenge|Init|Std|Lean|Mathlib|Batteries|Aesop|Qq|Plausible|ProofWidgets'
allowed+='|LeanSearchClient|ImportGraph)(\.|$)'
if grep -vE "$allowed" "$out/challenge-import-closure.txt"; then
  printf 'the reference statement imports a module outside Mathlib and its dependencies\n' >&2
  exit 1
fi
forbidden='^(Mathlib\.ModelTheory\.Infinitary|VaughtConjecture|InfinitaryLogic|ComputableModelTheory)(\.|$)'
if grep -E "$forbidden" \
    "$out/challenge-import-closure.txt"; then
  printf 'the reference statement imports a forbidden module\n' >&2
  exit 1
fi
sed -n 's#^\(Mathlib/.*\)\.lean$#\1#p' "$out/mathlib-fork-changes.txt" | tr / . \
  > "$out/tmp/fork-modules.txt"
printf 'Mathlib\n' >> "$out/tmp/fork-modules.txt"
if grep -Fxf "$out/tmp/fork-modules.txt" "$out/challenge-import-closure.txt"; then
  printf 'the reference statement imports a module the pinned Mathlib adds\n' >&2
  exit 1
fi
printf 'ok: reference closure of %s modules, all from upstream Mathlib %s and its dependencies\n' \
  "$(wc -l < "$out/challenge-import-closure.txt")" "$mathlib_upstream"

# ---------------------------------------------------------------------------------------------
log "5. the solution module and the expected failures, compiled without the reference"
solution=$out/build/solution
mkdir -p "$solution"
root_build=$repo/.lake/build/lib/lean
solution_roots=("${all_roots[@]}" "$repo")
solution_path="$solution:$root_build:$(path_of "${all_roots[@]}")"
compile SolutionDefinitions "$solution" solution_roots "$solution_path" "${strict[@]}" \
  > "$out/logs/solution-definitions.log" 2>&1
compile Solution "$solution" solution_roots "$solution_path" "${strict[@]}" \
  > "$out/logs/solution.log" 2>&1
compile Tests.SolutionAxioms "$solution" solution_roots "$solution_path" "${strict[@]}" \
  > "$out/logs/solution-axioms.log" 2>&1
cat "$out/logs/solution-axioms.log"
grep -q "axioms of $target: \[propext, Classical.choice, Quot.sound\]" \
  "$out/logs/solution-axioms.log"
solution_read=("${solution_roots[@]}" "$solution")
run_in solution_read "$solution_path" "$closure_runner" -- \
  "$tools/lean" --run "$closure_runner/ImportClosure.lean" Solution \
  > "$out/solution-import-closure.txt"
if grep -qx 'Challenge' "$out/solution-import-closure.txt"; then
  printf 'the solution module imports the reference statement\n' >&2
  exit 1
fi
# The expected failures: each in its own build directory, the solution's read-only.
expected_roots=("${all_roots[@]}" "$repo" "$solution")
for module in WeakenedStatement AlteredSemantics SorrySolution; do
  build=$out/build/$module
  mkdir -p "$build"
  options=("${strict[@]}")
  [[ $module == SorrySolution ]] && options=(-Dweak.linter.mathlibStandardSet=true)
  compile "ExpectedFailures.$module" "$build" expected_roots \
    "$build:$solution:$root_build:$(path_of "${all_roots[@]}")" "${options[@]}" \
    > "$out/logs/$module.log" 2>&1
done
grep -q 'warning: declaration uses `sorry`' "$out/logs/SorrySolution.log"

# ---------------------------------------------------------------------------------------------
log "6. exports and Comparator"
# The constants exported besides the target: those the kernel treats specially.
primitives=(propext Quot.sound Classical.choice
  Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble
  Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight
  String.ofList Char.ofNat List eagerReduce Nat String String.mk Char
  optParam autoParam semiOutParam outParam Quot Quot.mk Quot.lift Quot.ind)
export_module() {  # MODULE ROOTS_VAR LEAN_PATH
  run_in "$2" "$3" "$out/export" -- "$tools/leanexport" "$1" -- "$target" "${primitives[@]}"
}
export_module Challenge reference_read "$reference_path" > "$out/export/challenge.ndjson"
export_module Solution solution_read "$solution_path" > "$out/export/solution.ndjson"
for module in WeakenedStatement AlteredSemantics SorrySolution; do
  build=$out/build/$module
  expected_read=("${expected_roots[@]}" "$build")
  export_module "ExpectedFailures.$module" expected_read \
    "$build:$solution:$root_build:$(path_of "${all_roots[@]}")" \
    > "$out/export/$module.ndjson"
done
compare() {  # SOLUTION_EXPORT [OPTIONS...]
  local export=$1
  shift
  COMPARATOR_BWRAP=/usr/bin/bwrap PATH="$tools:/usr/bin:/bin" TMPDIR="$out/tmp" \
    "$tools/lake" comparator "$@" --config "$src/comparator.json" \
    --challenge-from-export "$out/export/challenge.ndjson" --solution-from-export "$export"
}
expect_rejection() {  # NAME DIAGNOSTIC
  local status=0
  compare "$out/export/$1.ndjson" > "$out/logs/comparator-$1.log" 2>&1 || status=$?
  if [[ $status != 1 ]] || ! grep -Fq "$2" "$out/logs/comparator-$1.log"; then
    printf 'expected failure %s: exit %s, wanted 1 with: %s\n' "$1" "$status" "$2" >&2
    cat "$out/logs/comparator-$1.log" >&2
    exit 1
  fi
  printf 'ok: %s rejected (exit 1): %s\n' "$1" "$(grep -F "$2" "$out/logs/comparator-$1.log")"
}
expect_rejection WeakenedStatement \
  "Challenge and solution theorem statement do not match: '$target'"
expect_rejection AlteredSemantics \
  "Const does not match between challenge and target 'PalomarChallenge.NoFiniteModels'"
expect_rejection SorrySolution "Illegal axiom detected: 'sorryAx'"
compare "$out/export/solution.ndjson" "${paranoid[@]}" > "$out/logs/comparator-solution.log" 2>&1 \
  || { cat "$out/logs/comparator-solution.log" >&2; exit 1; }
cat "$out/logs/comparator-solution.log"
accepted=("Lean default" nanoda)
(( ${#paranoid[@]} )) && accepted+=("Lean paranoid" lean4lean con-leche con-ron)
for kernel in "${accepted[@]}"; do
  grep -Fq "$kernel kernel accepts the solution" "$out/logs/comparator-solution.log"
done
grep -Fxq 'Your solution is okay!' "$out/logs/comparator-solution.log"

# ---------------------------------------------------------------------------------------------
(cd "$out" && sha256sum export/*.ndjson) > "$out/EXPORT-SHA256SUMS"
(cd "$out/build" && find . -name '*.olean' -print0 | sort -z | xargs -0 sha256sum) \
  > "$out/OLEAN-SHA256SUMS"
sha256sum --check --status "$out/SOURCE-SHA256SUMS"
rm -rf "${out:?}/tmp"
printf 'Comparator check passed at %s: %s\n' "$(cat "$out/commit.txt")" "$out"
