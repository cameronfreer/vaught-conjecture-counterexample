# Addendum: [AFK26] v1 and the statements cited by the abstract systems, 22 November 2026

A comparison, with the published version [AFK26] v1, of the statements of [AFK26] cited by the
files of `VaughtConjecture/Correspondence/Systems/` that the audit of 25 October 2026
([`2026-10-25-published-v1-audit.md`](2026-10-25-published-v1-audit.md)) did not cover, and, kept
separate, the differences between each printed statement and its formal counterpart.  The audit
of 25 October 2026 and the record of 27 October 2026
([`2026-10-27-abstract-section-2.md`](2026-10-27-abstract-section-2.md)) are unchanged; this note
qualifies the last-but-one bullet of the latter ("What is not claimed, at the pinned commit"),
which lists exactly the statements audited here, Definition 2.15 and Proposition 2.16 aside, as
corresponding to the pinned draft only.  No Lean statement, proof or theorem status changes.

This is a new note, not a section added to the audit of 25 October 2026: that record fixes its
scope, its sources and its repository commit (`1b8763e`, before the files of
`Correspondence/Systems/` existed), and `README.md` and `roadmap/IMPLEMENTATION.md` cite it for
the statements audited on that date.  As with the earlier records, a later note qualifies it and
leaves its verdicts as they stand.

## Sources

| Item | Value |
| --- | --- |
| Hash-pinned source draft | [AFK26], the draft of the audit of 25 October 2026 (not part of this repository), pinned by the SHA-256 of its source, `654b2780d08e9aee902d0553576c8f58f82730ccba7f4926757e45b1c02a755f` (hash verified) |
| Published version | [AFK26] v1, [hexagon:2610.00188v1](https://hexagonmath.org/2610.00188v1); the PDF of the audit of 25 October 2026, 26 pages, SHA-256 `2b3f3aa14c32174a8dae4e343f234cb08ea1027031a14dcd7c651ab6b7d8668d` (hash verified) |
| Text extraction of the PDF | `pdftotext -layout`, SHA-256 `a8a801df3e00e7c2d987fb5b547afaf0ac124945b6fb93214c2f4ea0b665a190`, the extraction recorded on 25 October 2026 |
| Repository | `main` at `ec3dfe6` for the citations and the location of the declarations |

## Method

1. **Scope.**  Every citation `[AFK26, …]` in the files of `Correspondence/Systems/`, including
   those broken across lines, was listed mechanically.  The statements cited there and absent
   from the coverage of 25 October 2026 are Convention 2.3; Definitions 2.1, 2.2, 2.4, 2.5, 2.15,
   2.24 and 2.26; Proposition 2.16; Lemma 2.22; Definition 4.17; and Theorem 4.23.  Definition
   2.15 and Proposition 2.16 are cited only to say that they are replaced, not formalized
   (`Systems/Targets.lean`, decision 4); they are compared here all the same.  The other
   citations are of statements covered by the audit of 25 October 2026 (Definitions 2.6–2.8,
   2.10, 2.17, 2.20, 2.21 and 2.23; Proposition 2.18; Theorems 2.19, 2.25, 2.27 and 4.36;
   Proposition 4.34), of the convention of nonempty domains (§1, its question (e)), or of whole
   sections (§§2, 2.4–2.6).
2. **Numbering.**  The numbering map of 25 October 2026 (the identity on §§1–4) contains every
   statement above.  Pages were read from the statement headers of the extraction, page by page.
3. **Prose.**  For each statement, the words of the source draft, with comments, formulas and
   macros removed, were checked mechanically to occur in the same order in the text of v1 (with
   words split at a line end rejoined).  No word is missing.  The remaining words of v1 were read:
   they are letters of formulas, the statement headers, the running page header, and the words
   inside formulas ("if and only if" in Definition 2.15 (c), "and" in Definition 4.17).  This
   repeats, for these statements, the whole-document comparison of 25 October 2026.
4. **Formulas.**  Every displayed and inline formula of each statement was compared by eye, the
   text of v1 against the source draft.

"Identical" below has the meaning of the audit of 25 October 2026: identical statement text, not a
byte-for-byte compilation of the pinned source.

## Coverage and result: v1 and the source draft

Every statement below has the same number and the same text in the hash-pinned source draft and
in v1; none is renumbered, reworded or changed in substance.  Pages are those of v1.

| Section | Statement | Page |
| --- | --- | --- |
| §2 | Definition 2.1 (`L_a`-geometry; closed tuples) | 4–5 |
| §2 | Definition 2.2 (structured geometry, clauses (a)–(d); invariants; lifts) | 5 |
| §2 | Convention 2.3 (the languages `L_a`, `L_b`, `L_c`) | 5 |
| §2 | Definition 2.4 (invariant diagram, clauses (a)–(c)) | 6 |
| §2 | Definition 2.5 (compatibility with an invariant diagram) | 6 |
| §2 | Definition 2.15 (back-and-forth system; `≡_α`) | 8 |
| §2 | Proposition 2.16 (antichains of `≡_β` and perfect sets) | 8 |
| §2 | Lemma 2.22 (a bound on the ranks of the lifts) | 10 |
| §2 | Definition 2.24 (Knight class) | 11 |
| §2 | Definition 2.26 (Knight sentence) | 11 |
| §4 | Definition 4.17 (`L_c[T]`) | 20 |
| §4 | Theorem 4.23 (`K[T]` and `σ[T]`) | 21 |

With the audit of 25 October 2026, every statement of [AFK26] cited by the files of
`Correspondence/Systems/` reads identically, in number and text, in the hash-pinned source draft
and in v1.

## The printed statements and the formal statements

This section compares the printed text with the Lean declarations; it does not concern v1 and the
draft, which do not differ.  The declarations are those that cite each statement in
`Correspondence/Systems/`, with the definitions they rest on.  A "convention" below is one of
[AFK26, §1.4] (v1, p. 4): relational languages, relation symbols of positive arity, "All
structures will be countable with non-empty domains."

| Statement | Printed (v1) | Lean | Difference from the printed statement |
| --- | --- | --- | --- |
| Lemma 2.22 | If `M` is eventually determined, there is `α_M < ω₁` with `rank_τ(M*) ≤ α_M` for every lift `M* ∈ K` of `M` | `WeakSystem.ExistsRankBoundTarget`, proved as `WeakSystem.existsRankBoundTarget`; used by the count of Theorem 2.25 (a) | `[Countable M]` on the carrier is explicit (the convention, which the proof uses).  The conclusion is `IsFixedAt α G` (`τ_α(G) = G`) for every lift at every level; `InvariantSystem.fixedAtIffRankLeTarget` proves it equivalent to rank at most `α`.  Eventual determination has the printed strict inequality.  None that changes what may be claimed |
| Theorem 4.23, first difference: the template system | For a template system `T`, `K[T]` is a weak Knight system whose class of `L_c`-reducts is the collection of models of `σ[T]` | `templateWeakSystemTarget`; `templateWeakSystem_isBaseSentenceOnCarriers` (from `templateBaseModelsTarget`); `templateQualifyingSentenceTarget` | **A specialization.**  The printed theorem is about an arbitrary template system `T` (Definition 4.11); the Lean construction is the concrete template system of legal templates, `K[L]` (`templateStageClass`), with `templateSentence`, the transcription of `σ[L]`, which is not identified with `baseLanguage.densitySentence`.  Verdict: Theorem 4.23 for an arbitrary template system is not stated; it is open, and is later work |
| Theorem 4.23, second difference: countable carriers | Claim 4.24 (in the proof): for `α < β` and `M ∈ K_β`, `τ_α(M) ∈ K_α`; no countability is written in Definition 4.21 or Theorem 4.23, and [AFK26, §1.4] makes all structures countable | `projectionTarget` (premise `Countable M`); the abstract field `WeakSystem.projection_mem` (premise `[Countable M]`); `templateWeakSystem` uses the first for the second | **A premise.**  The classes `templateStageClass M β` are defined on carriers of every cardinality, and closure under projection is proved only for countable carriers.  Read with the convention of §1.4, the printed theorem concerns countable structures only, so the statement proved is the printed one for `T = L`; read without that convention, closure under projection on uncountable carriers is not proved.  Verdict: the premise is present at `ec3dfe6`; a projection theorem without it is not stated |
| Definition 4.17 | `L_c[T] = L_a ∪ {R_t : t ∈ T, τ_0(Q_t) = Q_t}`, each `R_t` new, of the arity of `Q_t` | `templateBaseSublanguage`; on `baseTemplateLanguage` and `BaseSymbol` | **A specialization:** only for `T = L`.  `τ_0` is the projection to the block stage `ω + ω · 0 = ω`, as in Definition 4.16 of v1; the symbols `R_c` are new and disjoint from the invariants |
| Convention 2.3 | `L_a ⊆ L_c`, `L_b ∩ L_c = ∅`, `L_a^n = {P_n}`, `\|L_b^n\| > 0`, `\|L_c^n\| ≤ ω` | `GeometrySignature.BaseSublanguage`; `BaseSublanguage.CountableRelationsTarget`, proved as `countableRelationsTarget`; for `K[L]`, `templateBaseSublanguage` | `L_c` is a language with an injective inclusion whose range is exactly the symbols that are not invariants, so the ambient language is `L_b ∪ L_c`, the language of the printed structures; the conventions are fields of `GeometrySignature`.  None |
| Definition 2.1 | `Th_Geo(L_a)`: three clauses; closed tuples | `BaseSublanguage.IsClosedTuple`; `InvarianceDiagram.IsCompatible.injective_of_relMap_invariant`, `InvarianceDiagram.IsCompatible.exists_extension`; on `IsGeometry` | `IsGeometry` holds on carriers of every cardinality, a generalization.  None |
| Definition 2.2 | `Th_SGeo(L_a, L_b, L_c)`, clauses (a)–(d); invariants; lifts | `BaseSublanguage.reduct` (lifts), `BaseSublanguage.isClosedTuple_of_relMap_invariant` (b), `IsStructuredGeometry.eq_of_relMap` (c), `WeakSystem.IsLiftAt`; on `IsStructuredGeometry` | Carriers of every cardinality; the countability `\|L_c^n\| ≤ ω` of Convention 2.3, which Definition 2.2 does not assume, is part of the setting (as `Correspondence/InvariantSystem.lean` says).  Clause (b) is stated semantically (a disjunction over `ℵ₁` symbols).  None for the statements of `Correspondence/Systems/`, which all assume Convention 2.3 |
| Definition 2.4 | invariant diagram, clauses (a)–(c) | `InvarianceDiagram`; `InvarianceDiagram.IsCompatible.relMap_comp_iff` (clause (b)) | The structure of clause (c) is countable and has its carrier in universe `0`.  None |
| Definition 2.5 | compatibility with `I` | `InvarianceDiagram.IsCompatible`; the field `WeakSystem.isCompatible` | Carriers of every cardinality; the second clause is read as "every pair holds".  None |
| Definition 2.24 | `Φ` is a Knight class if `Φ = K_{-∞}` for some `I`, compatible `τ` and Knight system `K` | `WeakSystem.IsInBase` for a `QualifyingSystem`; `WeakSystem.IsBaseSentence`, `WeakSystem.IsBaseSentenceOnCarriers` | No predicate on classes: the class is the base of a qualifying system, and the statements quantify over the diagram, the invariant system and the system.  Ordinals in universe `0`; carriers in one universe.  None |
| Definition 2.26 | `σ ∈ L_{ω₁,ω}(L_c)` is a Knight sentence if its countable models form a Knight class | `QualifyingSystem.IsQualifyingSentence` (`= WeakSystem.IsBaseSentence`); `WeakSystem.IsBaseSentenceOnCarriers`; `templateQualifyingSystem_isQualifyingSentence` | `IsQualifyingSentence` constrains only the models coded on `ℕ`, so it is weaker than the printed condition, which also constrains the finite models; `IsBaseSentenceOnCarriers` is the printed condition on countable nonempty carriers in universe `0`.  The coded Theorem 2.27 that uses it adds `CountableMembersInfinite` and `L_c : Language.{0, 1}` (record of 27 October 2026) |
| Definition 2.15 | back-and-forth systems of closed tuples; `M ≡_α N` | none (replaced, not formalized) | InfinitaryLogic's `BFEquiv` and `bfEquivSetoid` stand in its place; no correspondence with `≡_α` is claimed or stated |
| Proposition 2.16 | for `Φ` closed under isomorphism with countable `≡_β`-antichains, no perfect set of non-isomorphic models | none (replaced, not formalized) | `MainTheorem.isThinOnNatModels_of_countable_bfClasses`, for the classes of `bfEquivSetoid` of the models coded on `ℕ`, stands in its place |

**What Theorem 4.23 is proved for, at `main` at `ec3dfe6`.**  For one template system, the legal
templates `L`, and in the following form; for no other template system.

1. `templateWeakSystemTarget`: `K[L]`, with the classes `K_β[L] = templateStageClass M β`, on
   carriers in any universe, is a weak system (`WeakSystem`) for the diagram `templateDiagram` and
   the invariant system `templateInvariantSystem`.  Its closure under isomorphism and under
   projection (Claim 4.24, `projectionTarget`) is asserted for countable carriers only.
2. `templateBaseModelsTarget`: on every countable nonempty carrier, a structure of `L_c[L]` is the
   reduct of a member of some `K_β[L]`, `β < ω₁`, exactly when it is a model of `templateSentence`.

So, for these statements: Lemma 2.22 is proved as printed, under the conventions of [AFK26, §1.4]
made explicit; Theorem 4.23 is proved for `K[L]` only, with projection closure on countable
carriers, and Definition 4.17 is formalized for `L` only; Definitions 2.24 and 2.26 are used in a
form coded on `ℕ` and in a form on all countable nonempty carriers; Definitions 2.1, 2.2, 2.4 and
2.5 and Convention 2.3 are transcribed clause by clause; Definition 2.15 and Proposition 2.16 are
not formalized.

## What this note does not change

- No verdict of the audit of 25 October 2026 changes, and no record is edited.
- The lists of audited statements in `README.md` and `roadmap/IMPLEMENTATION.md` name the
  statements audited on 25 October 2026; they do not yet name this note.
