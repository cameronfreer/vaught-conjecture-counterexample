# Knight's counterexample to Vaught's conjecture for $L_{\omega_1,\omega}$

A Lean 4 formalization of Knight's construction: a countable relational language and an
$L_{\omega_1,\omega}$ sentence with exactly $\aleph_1$ countable models up to isomorphism and no
perfect set of pairwise non-isomorphic countable models.

It builds on [Mathlib](https://github.com/leanprover-community/mathlib4) and
[InfinitaryLogic](https://github.com/cameronfreer/infinitary-logic) (syntax and semantics of
$L_{\omega_1,\omega}$, Scott analysis, model-code spaces, Morley counting) and on nothing else.

## The roadmap

`roadmap/` is the human-owned specification and gates all new mathematics.

- [`roadmap/README.md`](roadmap/README.md) — the definitive roadmap: the expansion-domain
  interface to the endpoint, library conventions, and layers 0–6 with their summits.
- [`roadmap/SEMANTIC_CONTRACT.md`](roadmap/SEMANTIC_CONTRACT.md) — the ten meanings the
  formalization must preserve.  Completion means proving these concrete conditions and deriving the endpoint,
  not constructing a record whose fields assert them.
- [`roadmap/Suggested.lean`](roadmap/Suggested.lean) — selected interfaces and theorem targets.
  A target sketch with deliberate `sorry`s, outside the build; finishing it alone is not
  completion.
- [`roadmap/EXPOSITIONS.md`](roadmap/EXPOSITIONS.md), [`SIMPLIFICATIONS.md`](roadmap/SIMPLIFICATIONS.md),
  [`HULL_ALGEBRA.md`](roadmap/HULL_ALGEBRA.md) — informal accounts and what is proposal rather
  than result.
- [`roadmap/SOURCE_AUDIT.md`](roadmap/SOURCE_AUDIT.md) — the provenance labels `A1`–`A14` the
  other documents cite.
- [`roadmap/LITERATURE.md`](roadmap/LITERATURE.md), [`REFERENCES.bib`](roadmap/REFERENCES.bib).

## Layout

- `Knight/` — all the mathematics.  The `Knight` library's globs are authoritative: every module
  under `Knight/` is built and audited whether or not anything imports it.  `Knight.lean` is an
  intentionally empty root.
- `roadmap/` — human-owned; changes need a human.
- `scripts/`, `.github/`, `lakefile.toml`, `lean-toolchain` — infrastructure.

Organize `Knight/` by mathematical topic (closure geometry, observations, realizations, syntax,
suppliers, domains, …), not by roadmap layer; a layer is a dependency order, not a directory.

## Rules

- `main` is always green.  CI builds against the pinned dependencies and enforces: no `sorry` or
  `admit`, no `maxHeartbeats` overrides, no axioms beyond `propext`, `Classical.choice`, and
  `Quot.sound` (so no `native_decide`), Mathlib's linter set with warnings as errors, a 1500-line
  ceiling per file, 100-character lines, copyright headers, and no import outside Mathlib,
  InfinitaryLogic, and `Knight`.  Run `bash scripts/check.sh` locally.
- No backwards-compatibility surface: no aliases, wrappers, forwarding modules, or deprecated
  shims.  When a declaration moves or is replaced, update every use in the same change.
- Separate raw finite data from the propositions asserting their laws; a constructor returns
  concrete data and proves laws about them.  A record field asserting the existence of a receiver
  is not its construction (`roadmap/README.md`, "Library conventions").
- Reuse Mathlib and InfinitaryLogic before writing anything general.  Do not create a generic
  framework larger than its two or three real clients require (Summit 0).
- Keep face restriction, stage reduction, and capped observation as different operations.  Keep
  proper-value equality, literal-top equality, and above-threshold readback separate.

## Dependencies and pins

`lean-toolchain` and the `InfinitaryLogic` revision in `lakefile.toml` are the only pins.
Mathlib is inherited from InfinitaryLogic's manifest (currently the `cameronfreer/mathlib4` fork
carrying the ModelTheory/Infinitary and `Ordinal.lift` PR stack); the toolchain must equal
InfinitaryLogic's, which `scripts/check.sh` verifies.  To bump: change `rev`, run
`lake update InfinitaryLogic`, copy InfinitaryLogic's `lean-toolchain`, commit the manifest.

CI (`.github/workflows/ci.yml`) caches `.lake/packages` per pin and `.lake/build` per commit, and
fetches the public Mathlib cache only on a cold pin.  A warm run takes minutes.

## Workflow

Work lands in tranches of a few hundred to a thousand lines, each a single roadmap topic:

1. **Implementation** by AI agents from the roadmap and semantic contract, on a branch.
2. **Internal review** against the ten [TauCeti review rubrics](https://github.com/TauCetiProject/TauCetiReview/tree/main/rubrics)
   (correctness, reuse, scope, attribution, api-design, generality, placement, naming,
   documentation, proof-quality), used as guidance rather than a strict gate, plus the checks
   above.  The reviewer reads the actual definitions and checks the statements against
   `roadmap/SEMANTIC_CONTRACT.md`; fluent docstrings are evidence, not proof.
3. **External review** of the tranche before it is merged to `main`.

Every PR names the roadmap layer and summit it advances, or says `Roadmap: none` for
infrastructure.  Import audits and proof-dependency audits are separate: a small theorem can
import a large layer, and a small file count does not prove a small mathematical dependency.

## License

Apache 2.0; see [`LICENSE`](LICENSE).
