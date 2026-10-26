#!/usr/bin/env bash
# Comparator check of the solution module against the reference statement.
#
# Usage: bash comparator/check.sh [--exact] [--paranoid] [OUT_DIR]
#
# Run at the root of a checkout whose root library is built (`lake build`) and whose
# dependencies are at the pinned revisions; `comparator/clean_check.sh` runs it on a fresh clone
# after a clean build of the root library.  Needs bwrap, jq, python3 and the pinned toolchain
# (whose `lake comparator`, `leanexport` and `nanoda_bin` are used).  Nothing is fetched.
#
# Outputs go to OUT_DIR, which must not exist (it is created; an existing path, a symbolic link
# or a path through a symbolic link is refused), or by default to a new directory
# `.lake/comparator/run.XXXXXX`.  Every output file is created new (`noclobber`); the only
# deletion is of the temporary directory OUT_DIR/tmp that this run created.
#
# Two modes.  If the files that enter the check (`comparator/`, `VaughtConjecture/`,
# `VaughtConjecture.lean`, `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`) have no
# uncommitted change and no untracked file, the result is a check of the commit HEAD
# ("exact commit").  Otherwise it is a check of the working tree, and every output says so
# ("working tree"); with --exact, a working tree with such changes is refused instead.
#
# Steps (each fails the script with a message on error):
#  1. records the mode, the commit, the toolchain, an inventory of the inputs (every
#     `VaughtConjecture/**/*.lean`, `VaughtConjecture.lean`, every file under `comparator/`,
#     `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, with their SHA-256) and the SHA-256
#     of the tools listed at `TOOL-SHA256SUMS` below; at the end, the inventory and `HEAD` are
#     taken again and must be unchanged;
#  2. checks that each dependency's git checkout is at its pinned revision with no modified
#     tracked file (this says nothing about the dependencies' cached build outputs, which are
#     read as they are), and that the root library build is up to date;
#  3. checks that the declarations of comparator/Challenge.lean are those of the reviewed
#     specification (a SHA-256 of the comment-free text);
#  4. compiles the reference statement in a sandbox whose search path has only Mathlib and
#     Mathlib's own dependencies, and checks its transitive import closure;
#  5. compiles the solution module, its axiom test and the three expected failures, with search
#     paths that do not contain the reference's build directory, and checks that `Challenge` is
#     not in the solution's import closure;
#  6. exports each with `leanexport` and runs `lake comparator` (Lean's kernel and nanoda) on the
#     solution, which must be accepted, and on each expected failure, which must be rejected with
#     its intended diagnostic.  With --paranoid, the solution is also checked by every external
#     checker bundled with the toolchain (`lake comparator --paranoid`: leanchecker-paranoid,
#     lean4lean, nanoda, con-leche and con-ron); this takes about ten minutes more.
set -euo pipefail
set -o noclobber
usage() {
  printf 'Usage: bash comparator/check.sh [--exact] [--paranoid] [OUT_DIR]\n' >&2
  exit 2
}
fail() { printf 'FAILED: %s\n' "$*" >&2; exit 1; }
exact=0
paranoid=()
while [[ ${1:-} == --* ]]; do
  case $1 in
    --exact) exact=1 ;;
    --paranoid) paranoid=(--paranoid) ;;
    *) usage ;;
  esac
  shift
done
(( $# <= 1 )) || usage
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"

# A new output directory: the path must not exist, and neither it nor any parent may be or pass
# through a symbolic link.
new_dir() {
  local path=$1
  [[ ! -e $path && ! -L $path ]] || fail "output path $path already exists"
  local parent
  parent=$(dirname "$path")
  [[ -d $parent ]] || fail "parent directory $parent does not exist"
  [[ $(realpath -e "$parent") == "$(realpath -s -e "$parent")" ]] ||
    fail "output path $path passes through a symbolic link"
  mkdir -- "$path"
}
if [[ -n ${1:-} ]]; then
  new_dir "$(realpath -s -m "$1")"
  out=$(realpath -s -e "$1")
else
  [[ ! -L .lake && ! -L .lake/comparator ]] || fail ".lake/comparator is a symbolic link"
  mkdir -p .lake/comparator
  out=$(mktemp -d "$repo/.lake/comparator/run.XXXXXX")
fi
new_dir "$out/build"
new_dir "$out/export"
new_dir "$out/logs"
new_dir "$out/tmp"
created_tmp=$out/tmp
src=$repo/comparator
log() { printf '== %s\n' "$*"; }

# The comment-free declarations of `Palomar/Challenge.lean` of
# cameronfreer/vaught-conjecture-palomar at commit 032ccb7 (`comparator/scripts/declarations.py`).
reviewed_declarations=37ea343194108b99620ce478081db4e0ee55f7375974205c2e31e1c3c735d3a2
# The upstream mathlib4 commit (leanprover-community/mathlib4, "chore(GroupTheory/Commutator/Basic):
# golf `map_commutator_eq` (#44951)") against which the sources of the pinned Mathlib are checked.
# Since the InfinitaryLogic v7.0.0 pins, the pinned Mathlib is upstream mathlib4 itself at this
# commit, so step 2 finds no changed or added file and the import-closure checks of step 4 keep
# their full force (no module of `Mathlib.ModelTheory.Infinitary`, of this library or of
# InfinitaryLogic or ComputableModelTheory, and not the root module `Mathlib`).  The checks are
# kept as they are, so that a pinned Mathlib which extends upstream by new files under
# `Mathlib/ModelTheory/Infinitary` is checked the same way.  The reviewed declarations above are
# unchanged.  The reference reads the outputs of Mathlib and its dependencies only
# (`reference_roots`); TauCeti, which now provides `BoundedFormulaInf` and its `Realize`, is read
# only on the solution side (`all_roots`, step 5), together with InfinitaryLogic and
# ComputableModelTheory.
mathlib_upstream=2e318faecff7d70d4e0cf8cc875104424a737355
target=PalomarChallenge.independent_challenge

# ---------------------------------------------------------------------------------------------
log "1. inputs"
commit=$(git rev-parse HEAD)
inputs=(comparator VaughtConjecture VaughtConjecture.lean lean-toolchain lakefile.toml
  lake-manifest.json)
git status --porcelain --untracked-files=all -- "${inputs[@]}" > "$out/inputs-status.txt"
if [[ -s "$out/inputs-status.txt" ]]; then
  (( exact == 0 )) || {
    cat "$out/inputs-status.txt" >&2
    fail "--exact: the inputs have uncommitted changes or untracked files"
  }
  mode="working tree (uncommitted changes in the inputs; see inputs-status.txt) on $commit"
else
  mode="exact commit $commit"
fi
printf '%s\n' "$mode" > "$out/mode.txt"
printf '%s\n' "$commit" > "$out/commit.txt"
printf 'Mode: %s\nOutputs: %s\n' "$mode" "$out"
expected_toolchain=$(cat lean-toolchain)
tools=$(dirname "$(readlink -f "$(elan which lean)")")
toolchain_dir=${expected_toolchain//\//--}
[[ $(basename "$(dirname "$tools")") == "${toolchain_dir//:/---}" ]] ||
  fail "toolchain $tools does not match lean-toolchain $expected_toolchain"
{
  printf 'lean-toolchain: %s\n' "$expected_toolchain"
  "$tools/lean" --version
  "$tools/lake" --version
  "$tools/leanexport" --help 2>&1 | head -n 1 || true
  "$tools/nanoda_bin" --help 2>&1 | head -n 1 || true
  /usr/bin/bwrap --version
} > "$out/toolchain.txt"
# TOOL-SHA256SUMS: every executable file and every `*.so` directly in the toolchain's `bin/` and
# `lib/lean/` (in v4.36.0-rc1: lean, lake, leanexport, nanoda_bin, leanchecker,
# leanchecker-paranoid, lean4lean, con-leche, con-ron, leanc, leanir, leanmake, leantar, cadical,
# clang, ld.lld, llvm-ar; libleanshared.so, libleanshared_1.so, libleanshared_2.so,
# libInit_shared.so, libLake_shared.so), with paths relative to the toolchain, and one digest of
# the list of SHA-256 of the toolchain's `lib/lean/**/*.olean`.  SYSTEM-TOOL-SHA256SUMS (it
# differs between machines): /usr/bin/bwrap and the resolved jq, python3 and git.  Nothing else
# is hashed (in particular not the system's shared libraries, Python's standard library, or the
# dependencies' build outputs).
(
  cd "$tools/.."
  find bin lib/lean -maxdepth 1 -type f \( -perm -u+x -o -name '*.so' \) -print0 | sort -z |
    xargs -0 sha256sum
  printf '%s  %s\n' "$(cd lib/lean && find . -name '*.olean' -print0 | sort -z |
    xargs -0 sha256sum | sha256sum | cut -d' ' -f1)" "lib/lean/**/*.olean (digest of the list)"
) > "$out/TOOL-SHA256SUMS"
sha256sum /usr/bin/bwrap "$(readlink -f "$(command -v jq)")" \
  "$(readlink -f "$(command -v python3)")" "$(readlink -f "$(command -v git)")" \
  > "$out/SYSTEM-TOOL-SHA256SUMS"
# The inventory of the inputs, taken again at the end of the run.
inventory() {
  {
    find VaughtConjecture -type f -name '*.lean' -print0
    find comparator -type f -print0
    printf '%s\0' VaughtConjecture.lean lean-toolchain lakefile.toml lake-manifest.json
  } | sort -z | xargs -0 sha256sum
}
inventory > "$out/SOURCE-SHA256SUMS"

# ---------------------------------------------------------------------------------------------
log "2. dependency pins and the root library build"
diff -q lean-toolchain .lake/packages/InfinitaryLogic/lean-toolchain > /dev/null ||
  fail "lean-toolchain differs from InfinitaryLogic's"
jq -er '.packages[] | if .type != "git" then error("git dependency required")
  else [.name, .rev] | @tsv end' lake-manifest.json > "$out/dependency-pins.tsv"
declare -A dep_root
while IFS=$'\t' read -r name rev; do
  [[ $name =~ ^[A-Za-z_][A-Za-z0-9_-]*$ && $rev =~ ^[0-9a-f]{40}$ ]] ||
    fail "unexpected manifest entry $name $rev"
  root=$(readlink -f ".lake/packages/$name")
  [[ $(git -C "$root" rev-parse HEAD) == "$rev" ]] ||
    fail "dependency $name is not at its pinned revision $rev"
  git -C "$root" diff --quiet HEAD -- || fail "dependency $name has modified tracked files"
  dep_root[$name]=$root
done < "$out/dependency-pins.tsv"
printf 'ok: dependency sources at their pinned revisions (their cached build outputs are not\n'
printf '    authenticated against these sources)\n'
# Up to date: Lake exits nonzero if any module of the root library would need rebuilding.
lake build --no-build > "$out/logs/lake-build-no-build.log" 2>&1 || {
  cat "$out/logs/lake-build-no-build.log" >&2
  fail "the root library build is missing or out of date; run lake build first"
}
# The pinned Mathlib's sources are upstream mathlib4 plus new files only.
mathlib=${dep_root[mathlib]}
git -C "$mathlib" merge-base --is-ancestor "$mathlib_upstream" HEAD ||
  fail "the pinned Mathlib does not contain upstream mathlib4 $mathlib_upstream"
git -C "$mathlib" diff --name-only "$mathlib_upstream" HEAD > "$out/mathlib-fork-changes.txt"
fork_files='^(Mathlib\.lean|Mathlib/ModelTheory/Infinitary/[A-Za-z]+\.lean'
fork_files+='|MathlibTest/[A-Za-z]+\.lean)$'
if grep -vE "$fork_files" "$out/mathlib-fork-changes.txt"; then
  fail "the pinned Mathlib changes upstream files beyond Mathlib/ModelTheory/Infinitary"
fi
git -C "$mathlib" diff --diff-filter=A --name-only "$mathlib_upstream" HEAD -- \
  'Mathlib/ModelTheory/Infinitary' > "$created_tmp/added.txt"
git -C "$mathlib" diff --name-only "$mathlib_upstream" HEAD -- 'Mathlib/ModelTheory/Infinitary' \
  > "$created_tmp/changed.txt"
cmp -s "$created_tmp/added.txt" "$created_tmp/changed.txt" ||
  fail "the pinned Mathlib modifies (not only adds) files in Mathlib/ModelTheory/Infinitary"

# ---------------------------------------------------------------------------------------------
log "3. the reference declarations"
python3 comparator/scripts/declarations.py comparator/Challenge.lean \
  > "$out/challenge-declarations.lean"
actual=$(sha256sum < "$out/challenge-declarations.lean" | cut -d' ' -f1)
[[ $actual == "$reviewed_declarations" ]] ||
  fail "comparator/Challenge.lean declarations changed: $actual"
printf 'ok: declarations of comparator/Challenge.lean match the reviewed specification\n'

# ---------------------------------------------------------------------------------------------
# Sandboxes: the whole file system read-only, home directories and /tmp covered, no network, an
# empty environment.  Each command sees the toolchain, the source directory `comparator/`, the
# directories passed to it read-only and its one writable directory; its LEAN_PATH is set
# explicitly.  Paths below a directory passed to it stay visible: the property relied on is
# the search path, and for the solution its import closure, not the invisibility of files.
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
# compile_logged NAME MODULE BUILD_DIR ROOTS_VAR LEAN_PATH [LEAN_OPTIONS...]
compile_logged() {
  local name=$1
  shift
  compile "$@" > "$out/logs/$name.log" 2>&1 || {
    cat "$out/logs/$name.log" >&2
    fail "compilation of $2 failed"
  }
}

# ---------------------------------------------------------------------------------------------
log "4. the reference statement, compiled against Mathlib alone"
challenge=$out/build/challenge
new_dir "$challenge"
reference_path="$challenge:$(path_of "${reference_roots[@]}")"
compile_logged challenge Challenge "$challenge" reference_roots "$reference_path"
# Exactly one diagnostic: the deliberate `sorry` of the reference theorem.
warnings=$(grep -c 'warning:' "$out/logs/challenge.log" || true)
[[ $warnings == 1 ]] || fail "the reference statement has $warnings warnings, expected 1"
grep -q 'Challenge.lean:[0-9]*:[0-9]*: warning: declaration uses `sorry`' \
  "$out/logs/challenge.log" || fail "the reference statement's one warning is not its sorry"
if grep -q 'error:' "$out/logs/challenge.log"; then
  fail "the reference statement's compilation reports an error"
fi
# The import closure, read from the compiled `.olean` headers in the same sandbox.
closure_runner=$out/build/closure
new_dir "$closure_runner"
cp comparator/scripts/ImportClosure.lean "$closure_runner/"
reference_read=("${reference_roots[@]}" "$challenge")
run_in reference_read "$reference_path" "$closure_runner" -- \
  "$tools/lean" --run "$closure_runner/ImportClosure.lean" Challenge \
  > "$out/challenge-import-closure.txt" || fail "reading the reference's import closure failed"
# Every module is in Init, Std, Lean, Lake (all four from the toolchain), Mathlib or one of
# Mathlib's own dependencies, and none is in a part of Mathlib that the pinned fork changes or
# adds.  Lake modules enter only through Mathlib's dependency ImportGraph (see the README).
allowed='^(Challenge|Init|Std|Lean|Lake|Mathlib|Batteries|Aesop|Qq|Plausible|ProofWidgets'
allowed+='|LeanSearchClient|ImportGraph)(\.|$)'
if grep -vE "$allowed" "$out/challenge-import-closure.txt"; then
  fail "the reference statement imports a module outside Mathlib and its dependencies"
fi
forbidden='^(Mathlib\.ModelTheory\.Infinitary|VaughtConjecture|InfinitaryLogic'
forbidden+='|ComputableModelTheory)(\.|$)'
if grep -E "$forbidden" "$out/challenge-import-closure.txt"; then
  fail "the reference statement imports a forbidden module"
fi
{
  sed -n 's#^\(Mathlib/.*\)\.lean$#\1#p' "$out/mathlib-fork-changes.txt" | tr / .
  printf 'Mathlib\n'
} > "$created_tmp/fork-modules.txt"
if grep -Fxf "$created_tmp/fork-modules.txt" "$out/challenge-import-closure.txt"; then
  fail "the reference statement imports a module the pinned Mathlib changes or adds"
fi
printf 'ok: reference closure of %s modules, whose Mathlib sources are those of upstream %s\n' \
  "$(wc -l < "$out/challenge-import-closure.txt")" "$mathlib_upstream"

# ---------------------------------------------------------------------------------------------
log "5. the solution module and the expected failures, without the reference on the search path"
solution=$out/build/solution
new_dir "$solution"
root_build=$(readlink -f "$repo/.lake/build/lib/lean")
solution_roots=("${all_roots[@]}" "$repo" "$(readlink -f "$repo/.lake/build")")
solution_path="$solution:$root_build:$(path_of "${all_roots[@]}")"
[[ ":$solution_path:" != *":$challenge:"* ]] || fail "the reference build is on the search path"
compile_logged solution-definitions SolutionDefinitions "$solution" solution_roots \
  "$solution_path" "${strict[@]}"
compile_logged solution Solution "$solution" solution_roots "$solution_path" "${strict[@]}"
compile_logged solution-axioms Tests.SolutionAxioms "$solution" solution_roots \
  "$solution_path" "${strict[@]}"
cat "$out/logs/solution-axioms.log"
grep -q "axioms of $target: \[propext, Classical.choice, Quot.sound\]" \
  "$out/logs/solution-axioms.log" || fail "the solution's axioms are not the standard three"
solution_read=("${solution_roots[@]}" "$solution")
run_in solution_read "$solution_path" "$closure_runner" -- \
  "$tools/lean" --run "$closure_runner/ImportClosure.lean" Solution \
  > "$out/solution-import-closure.txt" || fail "reading the solution's import closure failed"
if grep -qx 'Challenge' "$out/solution-import-closure.txt"; then
  fail "the solution module imports the reference statement"
fi
printf 'ok: Challenge is not on the solution search path nor in its import closure (%s modules)\n' \
  "$(wc -l < "$out/solution-import-closure.txt")"
# The expected failures: each in its own build directory, the solution's read-only.
expected_roots=("${solution_roots[@]}" "$solution")
for module in WeakenedStatement AlteredSemantics SorrySolution; do
  build=$out/build/$module
  new_dir "$build"
  options=("${strict[@]}")
  [[ $module == SorrySolution ]] && options=(-Dweak.linter.mathlibStandardSet=true)
  compile_logged "$module" "ExpectedFailures.$module" "$build" expected_roots \
    "$build:$solution:$root_build:$(path_of "${all_roots[@]}")" "${options[@]}"
done
grep -q 'warning: declaration uses `sorry`' "$out/logs/SorrySolution.log" ||
  fail "SorrySolution does not report its sorry"

# ---------------------------------------------------------------------------------------------
log "6. exports and Comparator"
# The constants exported besides the target: those the kernel treats specially.
primitives=(propext Quot.sound Classical.choice
  Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble
  Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight
  String.ofList Char.ofNat List eagerReduce Nat String String.mk Char
  optParam autoParam semiOutParam outParam Quot Quot.mk Quot.lift Quot.ind)
export_module() {  # MODULE ROOTS_VAR LEAN_PATH NAME
  run_in "$2" "$3" "$out/export" -- "$tools/leanexport" "$1" -- "$target" "${primitives[@]}" \
    > "$out/export/$4.ndjson" || fail "exporting $1 failed"
}
export_module Challenge reference_read "$reference_path" challenge
export_module Solution solution_read "$solution_path" solution
for module in WeakenedStatement AlteredSemantics SorrySolution; do
  build=$out/build/$module
  expected_read=("${expected_roots[@]}" "$build")
  export_module "ExpectedFailures.$module" expected_read \
    "$build:$solution:$root_build:$(path_of "${all_roots[@]}")" "$module"
done
compare() {  # SOLUTION_EXPORT [OPTIONS...]
  local export=$1
  shift
  COMPARATOR_BWRAP=/usr/bin/bwrap PATH="$tools:/usr/bin:/bin" TMPDIR="$created_tmp" \
    "$tools/lake" comparator "$@" --config "$src/comparator.json" \
    --challenge-from-export "$out/export/challenge.ndjson" --solution-from-export "$export"
}
expect_rejection() {  # NAME DIAGNOSTIC
  local status=0
  compare "$out/export/$1.ndjson" > "$out/logs/comparator-$1.log" 2>&1 || status=$?
  if [[ $status != 1 ]] || ! grep -Fq "$2" "$out/logs/comparator-$1.log"; then
    cat "$out/logs/comparator-$1.log" >&2
    fail "expected failure $1: exit $status, wanted 1 with: $2"
  fi
  printf 'ok: %s rejected (exit 1): %s\n' "$1" "$(grep -F "$2" "$out/logs/comparator-$1.log")"
}
expect_rejection WeakenedStatement \
  "Challenge and solution theorem statement do not match: '$target'"
expect_rejection AlteredSemantics \
  "Const does not match between challenge and target 'PalomarChallenge.NoFiniteModels'"
expect_rejection SorrySolution "Illegal axiom detected: 'sorryAx'"
compare "$out/export/solution.ndjson" "${paranoid[@]}" > "$out/logs/comparator-solution.log" 2>&1 \
  || { cat "$out/logs/comparator-solution.log" >&2; fail "Comparator rejected the solution"; }
cat "$out/logs/comparator-solution.log"
accepted=("Lean default" nanoda)
(( ${#paranoid[@]} )) && accepted+=("Lean paranoid" lean4lean con-leche con-ron)
for kernel in "${accepted[@]}"; do
  grep -Fq "$kernel kernel accepts the solution" "$out/logs/comparator-solution.log" ||
    fail "no acceptance line for the $kernel kernel"
done
grep -Fxq 'Your solution is okay!' "$out/logs/comparator-solution.log" ||
  fail "no final acceptance line"

# ---------------------------------------------------------------------------------------------
(cd "$out" && sha256sum export/*.ndjson) > "$out/EXPORT-SHA256SUMS"
(cd "$out/build" && find . -name '*.olean' -print0 | sort -z | xargs -0 sha256sum) \
  > "$out/OLEAN-SHA256SUMS"
# The same inputs, with the same contents, and the same commit as at the start.
inventory > "$created_tmp/inputs-after.txt"
if ! cmp -s "$out/SOURCE-SHA256SUMS" "$created_tmp/inputs-after.txt"; then
  changed=$({ diff "$out/SOURCE-SHA256SUMS" "$created_tmp/inputs-after.txt" || true; } |
    sed -n 's/^[<>] [0-9a-f]\{64\}  //p' | sort -u | paste -sd ' ' -)
  fail "inputs changed during the check: $changed"
fi
[[ $(git rev-parse HEAD) == "$commit" ]] ||
  fail "HEAD changed during the check: $commit -> $(git rev-parse HEAD)"
git status --porcelain --untracked-files=all -- "${inputs[@]}" > "$created_tmp/status-after.txt"
cmp -s "$out/inputs-status.txt" "$created_tmp/status-after.txt" ||
  fail "the working tree of the inputs changed during the check"
rm -rf -- "${created_tmp:?}"
printf 'Comparator check passed (%s): %s\n' "$mode" "$out" > "$out/RESULT.txt"
cat "$out/RESULT.txt"
