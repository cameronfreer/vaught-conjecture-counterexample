# Comparator check of the main theorem

This directory checks the main theorem of the repository against an external statement with
[Comparator](https://github.com/leanprover/comparator), the proof judge bundled with the pinned
toolchain (`lake comparator`, Lean `v4.35.0-rc3`).  Comparator replays the exported proof through
Lean's kernel and through nanoda, allows only the axioms `propext`, `Quot.sound` and
`Classical.choice`, and checks that the solution's theorem has the same statement as the
reference, with every declaration that statement uses identical in both environments.

Nothing here is part of the mathematical construction: no file under `VaughtConjecture/` is
changed, the root library build (`lake build`) does not see these files, and the dependency pins
are those of `lakefile.toml` and `lake-manifest.json`.

**Comparator does not replace human review of the reference statement.**  It checks that the
solution proves the statement of `Challenge.lean`; whether that statement says what it is meant
to say is for a human reader of `Challenge.lean`.

## Files

| File | Role |
| --- | --- |
| `Challenge.lean` | The reference statement `PalomarChallenge.independent_challenge` (proof left open). |
| `SolutionDefinitions.lean` | The definitions of the reference statement, restated on the solution side, and its three clauses for `baseLanguage.densitySentence`. |
| `Solution.lean` | The solution module: the reference statement, from the three clauses. |
| `Tests/SolutionAxioms.lean` | The axioms of the solution's theorem and lemmas, in the elaborated environment. |
| `ExpectedFailures/WeakenedStatement.lean` | A valid proof of a weaker statement under the same name. |
| `ExpectedFailures/AlteredSemantics.lean` | A valid proof of the same statement text, with one definition altered. |
| `ExpectedFailures/SorrySolution.lean` | The same statement and definitions, proved by `sorry`. |
| `comparator.json` | The Comparator configuration. |
| `check.sh` | The check on the current checkout (requires `lake build` first). |
| `clean_check.sh` | The check on a fresh clone of the current commit, after a clean build. |
| `scripts/declarations.py` | The comment-free declarations of a Lean file (for the reference hash). |
| `scripts/ImportClosure.lean` | The transitive import closure of a compiled module. |

## The reference statement

```lean
theorem independent_challenge :
    ∃ (R : ℕ → Type 1) (_ : Countable (Σ n, R n)) (φ : (language R).Sentenceω),
      Cardinal.mk (IsoClasses R φ) = Cardinal.aleph 1 ∧
      NoFiniteModels R φ ∧ NoPerfectAntichain R φ
```

There are a countable relational language and an `L_{ω₁,ω}` sentence with exactly `ℵ₁`
isomorphism classes of models coded on `ℕ`, no model on any finite carrier (the empty one
included), and no nonempty perfect set of pairwise nonisomorphic coded models in the product
topology.  The declarations of `Challenge.lean` are character for character those of the reviewed
specification `Palomar/Challenge.lean` of `cameronfreer/vaught-conjecture-palomar` at commit
`032ccb7`; only comments and docstrings differ.  `check.sh` verifies this by the SHA-256
`37ea3431…` of the comment-free text (`scripts/declarations.py`).

**Imports.**  `Challenge.lean` imports five Mathlib modules, `Mathlib.ModelTheory.Semantics`,
`Mathlib.SetTheory.Cardinal.Aleph`, `Mathlib.Topology.Constructions`, `Mathlib.Topology.Order` and
`Mathlib.Topology.Perfect`, for first-order structures and terms, `Cardinal.aleph`, the product
topology and `Perfect`.  It does not import `InfinitaryLogic`: the syntax and semantics of
infinitary formulas (`FirstOrder.Language.BoundedFormulaInf` and its `Realize`, about thirty
lines) are restated in the file instead.  `check.sh` compiles it in a sandbox in which only
Mathlib and the dependencies of Mathlib's own manifest are visible, and then checks its whole
transitive import closure (2563 modules at the current pins): every module is in `Init`, `Std`,
`Lean`, `Mathlib` or a dependency of Mathlib, none is in `Mathlib.ModelTheory.Infinitary`,
`InfinitaryLogic`, `ComputableModelTheory` or `VaughtConjecture`, and none is a file that the
pinned Mathlib changes or adds.  The pinned Mathlib (`cameronfreer/mathlib4` at `346a4bd`) is
upstream mathlib4 at `c55e6e7` plus three commits that only add `Mathlib/ModelTheory/Infinitary`
(and its tests and the umbrella file `Mathlib.lean`); `check.sh` verifies this with git, so every
module the reference statement imports is byte for byte that of upstream mathlib4 `c55e6e7`.

**Compatibility with the density sentence.**  The reference statement is compatible with the
sentence `baseLanguage.densitySentence` of `VaughtConjecture/Language/Density.lean`:

* *language*: `language R` is `⟨fun _ => Empty, R⟩`; for `R := baseLanguage.{0}.Relations` this is
  definitionally `baseLanguage.{0} : Language.{0, 1}`, whose function symbols are `Empty`;
* *sentence*: `(language R).Sentenceω` is the restated `BoundedFormulaInf ℕ Empty 0`, which
  Comparator checks to be identical to the pinned Mathlib's (`Mathlib/ModelTheory/Infinitary`),
  the type of `densitySentence`; satisfaction `Satisfies` is the pinned Mathlib's `Realize` at the
  empty valuations, which is `Sentenceω.Realize` of `InfinitaryLogic` by `Iff.rfl`;
* *codes and topology*: `Code R ℕ` is `InfinitaryLogic`'s `StructureSpace` up to unfolding, with
  the same product topology (`Pi.topologicalSpace`);
* *isomorphism*: the reference uses permutations of `ℕ` preserving every relation coordinate,
  the library `Language.Equiv` of the decoded structures; they are proved equivalent in
  `SolutionDefinitions.lean` (`isomorphic_iff_structureIsoSetoid`);
* *no perfect antichain*: the reference states `c ≠ d → ¬ Isomorphic c d` on `P`, the library
  `r c d → c = d` (`HasPerfectAntichainOn`), the contrapositive;
* *no finite models*: the reference quantifies over codes on `Fin n`, the repository's statement
  over every structure on a carrier `M` (`Infinite M`), instantiated at `Fin n`.

The reference statement is existential: it does not name the density sentence (it cannot,
without importing this repository), and the solution provides `densitySentence` as the witness.
It also omits the clauses of `MainTheorem.vaughtCounterexample_allCarriers_densitySentence` about
all countable carriers (the count on carriers of every universe, the failure of the perfect-set
dichotomy on all coded tiers, every countable model isomorphic to a coded one), and it is not
stated through `HasThinAlephOneSpectrum`.  Comparator therefore checks the statement above and
nothing about those further clauses.

## The solution module

`Solution.lean` proves `PalomarChallenge.independent_challenge` with `R := baseLanguage.{0}.Relations`
and `φ := baseLanguage.densitySentence.{0}` from the three clauses of
`SolutionDefinitions.lean`, which come from `MainTheorem.vaughtCounterexample_allCarriers_densitySentence`
(`VaughtConjecture/MainTheorem/GrowthLevelRoute.lean`).  Neither file imports `Challenge.lean`
(they are compiled in a sandbox where its build is not visible, and `check.sh` checks that the
solution's import closure does not contain it), and `Challenge.lean` imports nothing of this
repository.  `SolutionDefinitions.lean` restates the definitions of the reference statement
declaration for declaration; Comparator checks each against the reference.

## Running the check

```bash
lake build
bash comparator/check.sh [--paranoid] [OUT_DIR]
```

or, from a fresh clone of the committed head with a clean build of the root library:

```bash
bash comparator/clean_check.sh [--paranoid] WORK_DIR [DEPS_DIR]
```

`check.sh` needs `bwrap`, `jq`, `python3` and the pinned toolchain, fetches nothing, and writes only
under `.lake/comparator` (or `OUT_DIR`).  In order, it

1. records the commit, the toolchain (and the SHA-256 of `lean`, `lake`, `leanexport`,
   `nanoda_bin`) and the SHA-256 of every input;
2. checks that each dependency is at its pinned revision with no modified tracked file, that the
   toolchain is that of `lean-toolchain` and of `InfinitaryLogic`, that the root library build is up
   to date (`lake build --no-build`), and the description of the pinned Mathlib above;
3. checks the hash of the reference declarations;
4. compiles `Challenge.lean` in a sandbox (bubblewrap: read-only file system, home directories
   hidden, no network, empty environment) that sees only Mathlib and its dependencies; it must
   compile with exactly one warning, ``declaration uses `sorry` `` for its theorem; then checks
   its import closure;
5. compiles `SolutionDefinitions.lean`, `Solution.lean` and `Tests/SolutionAxioms.lean` with the
   repository's options (warnings as errors, Mathlib's linter set), and each expected failure in
   its own build directory, all in sandboxes that do not see the reference's build;
6. exports each with `leanexport` (the theorem and the kernel's primitive constants with all their
   dependencies) and runs `lake comparator --challenge-from-export … --solution-from-export …`.

With `--paranoid`, the solution is also checked by every external checker bundled with the
toolchain (`leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`); this takes about
ten minutes more.  The outputs are `logs/`, `EXPORT-SHA256SUMS`, `OLEAN-SHA256SUMS`,
`SOURCE-SHA256SUMS`, `TOOL-SHA256SUMS`, `dependency-pins.tsv`, the two import closures, the list of
files the pinned Mathlib changes, and the exports themselves (about 650 MB; `clean_check.sh` adds
`ROOT-OLEAN-SHA256SUMS` and `logs/lake-build.log`).

### Expected results

| Solution | Comparator | Diagnostic asserted |
| --- | --- | --- |
| `Solution` | accepted (exit 0) | `Lean default kernel accepts the solution`, `nanoda kernel accepts the solution` |
| `WeakenedStatement` | rejected (exit 1) | `Challenge and solution theorem statement do not match: 'PalomarChallenge.independent_challenge'` |
| `AlteredSemantics` | rejected (exit 1) | `Const does not match between challenge and target 'PalomarChallenge.NoFiniteModels'` |
| `SorrySolution` | rejected (exit 1) | `Illegal axiom detected: 'sorryAx'` |

Each expected failure is otherwise valid: the first two compile with warnings as errors and use
the standard axioms only, so each is rejected for its intended reason alone.  `WeakenedStatement`
drops the clause `NoPerfectAntichain`; `AlteredSemantics` keeps the text of the statement but
lets `NoFiniteModels` quantify over `Fin (n + 1)`, no longer excluding the empty structure.

## What the check establishes

* The exported proof of `PalomarChallenge.independent_challenge` in the solution's environment is
  accepted by Lean's kernel and by nanoda (and, with `--paranoid`, by the other bundled
  checkers), and depends on no axiom beyond `propext`, `Quot.sound` and `Classical.choice`.
* Its statement, and every declaration that statement uses (the restated definitions,
  `BoundedFormulaInf` and its `Realize` from the pinned Mathlib, and the Mathlib and core
  declarations below them), are identical to those of the reference statement.
* The reference statement was compiled without access to anything but Mathlib and Mathlib's own
  dependencies, imports only modules identical to upstream mathlib4 `c55e6e7`, and has the
  declarations of the reviewed specification.
* With `clean_check.sh` (and in CI), all of this holds for a fresh clone of the exact commit whose
  root library was built from nothing.

## What it does not establish

* That the reference statement expresses the intended mathematics: that needs a human reading of
  `Challenge.lean` (and of the Mathlib definitions it uses, such as `Perfect`, `Cardinal.aleph`
  and the product topology).
* Anything about this repository's own statements beyond the reference statement:
  `HasThinAlephOneSpectrum`, the clauses on all countable carriers, and the identity of the
  witness sentence are not compared.  The other theorems of the repository are checked by
  `lake build` and the axiom audit of `scripts/check.sh`, not by Comparator.
* That the dependencies were built from their sources here: the build outputs of the pinned
  dependencies (Mathlib, `InfinitaryLogic`, `ComputableModelTheory`) are reused, after checking
  their revisions and tracked files.  The kernels re-check every exported proof term, so a wrong
  dependency output cannot make a false proof pass; but the reference statement's Mathlib
  declarations are read from those outputs too.  CI rebuilds them from source whenever a pin
  changes.
* The correctness of the toolchain binaries, of bubblewrap, or of the kernels themselves (Lean's
  kernel and nanoda are separate implementations; `--paranoid` adds four more).
* Any Palomar registration or review.

## CI

The job `comparator` of `.github/workflows/ci.yml` runs after the job `build`: it checks out the
exact commit, restores the dependency cache for the current pins, builds the root library without
restoring any root build output, and runs `comparator/check.sh`; the logs and hash lists (not the
exports) are uploaded as the artifact `comparator-check`.
