# Addendum: the published version of [AFK26], 25 October 2026

A comparison of the statements of [AFK26] cited by this repository, in the hash-pinned source
draft, with the published version [AFK26] v1, and two corrections, by addendum, to the milestone
records of 15 October 2026.  The records
[`2026-10-15-proposition-4-34.md`](2026-10-15-proposition-4-34.md) and
[`2026-10-15-proposition-4-35.md`](2026-10-15-proposition-4-35.md) are unchanged; this note
qualifies them.  No Lean statement, proof or theorem status changes.

## Sources

| Item | Value |
| --- | --- |
| Hash-pinned source draft | [AFK26], the draft that the records of 15 October 2026 call "the current draft of 7 October 2026" (not part of this repository), pinned by the SHA-256 of its source, `654b2780d08e9aee902d0553576c8f58f82730ccba7f4926757e45b1c02a755f` (hash verified) |
| Published version | [AFK26] v1, [hexagon:2610.00188v1](https://hexagonmath.org/2610.00188v1); PDF retrieved 25 October 2026 from <https://hexagonmath.org/pdf/2610.00188v1>, 26 pages, SHA-256 `2b3f3aa14c32174a8dae4e343f234cb08ea1027031a14dcd7c651ab6b7d8668d` (hash verified) |
| Text extraction of the PDF | `pdftotext`, SHA-256 `a8a801df3e00e7c2d987fb5b547afaf0ac124945b6fb93214c2f4ea0b665a190` |
| Repository | `main` at `1b8763e` for the location of the declarations; the docstring corrections described below start from `main` at `424ea17` |

## Method

1. **Numbering.**  The numbered environments of the source draft were counted mechanically (one
   counter per section, shared by every numbered environment) and compared with the statement
   headers printed in v1; pages were read from the PDF page by page.
2. **Prose.**  A word-sequence comparison of the whole document: the source draft with comments,
   formulas and macros removed, against the text of v1.  Outside the title block, the contents
   list, the bibliography and the author addresses, the only differences are three artefacts of
   the PDF extraction ("all" read as "alls" from a merged `⋃` glyph; "that" and "where" displaced
   by the layout).  No word of the prose of any audited statement differs.
3. **Formulas.**  Every displayed and inline formula of each audited statement was compared by
   eye, the text of v1 (and the PDF where the layout was unclear) against the source draft.

"Identical" below means identical statement text: the prose word sequence verified mechanically
over the whole document, and the formulas compared for every audited statement.  It does not
assert that the PDF is byte for byte a compilation of the pinned source.

## Coverage and result

Every audited statement has the same number and the same text in the hash-pinned source draft and
in v1; none is renumbered, reworded or changed in substance.  Pages are those of v1.

| Section | Statement | Page |
| --- | --- | --- |
| §2 | Definition 2.6 (invariant system; rank of an invariant) | 6 |
| §2 | Definition 2.7 (projection; rank of a structure) | 7 |
| §2 | Definition 2.8 (compatibility of a diagram and a system) | 7 |
| §2 | Definition 2.10 (density theory) | 7 |
| §2 | Definition 2.17 (weak Knight system) | 9 |
| §2 | Proposition 2.18 (back-and-forth) | 9 |
| §2 | Theorem 2.19 (no perfect set) | 9–10 |
| §2 | Definition 2.20 (maximal at a level; few maximal models) | 10 |
| §2 | Definition 2.21 (eventually determined) | 10 |
| §2 | Definition 2.23 (Knight system, conditions (a)–(d)) | 11 |
| §2 | Theorem 2.25 (Knight classes) | 11 |
| §2 | Theorem 2.27 (Knight sentences) | 11 |
| §4 | Definition 4.6 (renaming) | 17 |
| §4 | Definition 4.11 (template system, clauses (a)–(g)) | 18 |
| §4 | Definition 4.13 (`Th_pl`, Singletons) | 19 |
| §4 | Definition 4.16 (`τ_β` on templates) | 19 |
| §4 | Definition 4.20 (`D[β]`) | 20 |
| §4 | Definition 4.21 (`K_β[T]`) | 20 |
| §4 | Definition 4.22 (`σ[T]`) | 20–21 |
| §4 | Definition 4.29 (legal templates) | 22–23 |
| §4 | Proposition 4.30 (a template system of legal templates) | 23 |
| §4 | Definition 4.31 (charts, `C_β[L]`) | 23 |
| §4 | Proposition 4.32 (hereditary, joint embedding, amalgamation) | 24 |
| §4 | Lemma 4.33 (universal model) | 24 |
| §4 | Proposition 4.34 (Boundedness, Reconstruction, Limits) | 24 |
| §4 | Proposition 4.35 (countably many maximal structures) | 24 |
| §4 | Theorem 4.36 (counterexample to Vaught's conjecture) | 24 |
| §4 | Claim 4.37 (unique maximal lift) | 24–25 |

The formal counterparts of these statements, as listed in the concordance of
`roadmap/IMPLEMENTATION.md`, need no revision on account of v1.

## The numbering map

The map from the source draft to v1 is the identity on §§1–4: every numbered environment appears
in the same order, with the same kind and the same number; none was added, removed, merged or
reordered.

| Section | Numbered statements (both documents) |
| --- | --- |
| §1 | Question 1.1, Conjecture 1.2 |
| §2 | Definitions 2.1, 2.2; Convention 2.3; Definitions 2.4–2.8; Lemma 2.9; Definition 2.10; Remark 2.11; Lemmas 2.12–2.14; Definition 2.15; Proposition 2.16; Definition 2.17; Proposition 2.18; Theorem 2.19; Definitions 2.20, 2.21; Lemma 2.22; Definitions 2.23, 2.24; Theorem 2.25; Definition 2.26; Theorem 2.27 |
| §3 | Definition 3.1; Lemma 3.2; Definitions 3.3–3.7; Lemma 3.8; Example 3.9; Definition 3.10; Lemma 3.11; Definitions 3.12, 3.13; Lemma 3.14; Definition 3.15; Lemma 3.16; Definition 3.17; Propositions 3.18, 3.19; Definition 3.20; Lemma 3.21; Definition 3.22; Propositions 3.23, 3.24; Theorem 3.25 |
| §4 | Definitions 4.1–4.13; Lemma 4.14; Definitions 4.15–4.18; Lemma 4.19; Definitions 4.20–4.22; Theorem 4.23; Claim 4.24; Theorem 4.25; Definitions 4.26–4.29; Proposition 4.30; Definition 4.31; Proposition 4.32; Lemma 4.33; Propositions 4.34, 4.35; Theorem 4.36; Claim 4.37 |

So every citation of the current numbering in this repository is also a citation of v1.  The
numbers of the version of 5 October 2026 are not: under v1 they point to other statements (v1's
2.19 is a theorem, 2.22 a lemma, 4.24 a claim, 4.25 a theorem, 4.29 the definition of legal
templates).  The docstrings that still used those numbers without saying so
(`MainTheorem/Niceness`, `MainTheorem/LowPaddedRoute`, `Correspondence/Template`,
`Correspondence/InvariantSystem`, `Correspondence/StageIndexing`) now mark them as such and give
the current statement and number beside them; where the earlier text differs in substance (the
truncation of a template acting on the rows, the order clause `≤` of Definition 4.18, `L_c` read
at `τ_ω`, the indexing `ω · β`, graded faces of grade `0`), the earlier text is kept as history.

## The specific questions

**(a) Propositions 4.32, 4.34 and 4.35 are stated without proof in v1.**  As in the source draft.
v1, p. 23: "This proof, which is substantial, has been formalized. We will now give a rough
outline of the approach. Specifically we will mention three propositions without proof and show
how to prove from them that K[L] is a Knight system."  §1.3 (p. 4): "They have been formally
verified in Lean, but their proofs are omitted here."  Lemma 4.33 has a short proof (from
Proposition 4.32 and the standard Fraïssé construction), and Claim 4.37 and Proposition 4.30 have
full proofs.

**(b) Definition 2.20 keeps the allowance for an unchanged higher lift.**  v1, p. 10: "M ∈ Kβ is
maximal at level β (for K) if whenever β∗ > β and M∗ ∈ Kβ∗ and τβ(M∗) = M, then M = M∗."  A lift
`M∗ = M` in `Kβ∗` satisfies the conclusion, so `M` may also lie in `Kβ∗` and still be maximal at
`β`.  `IsMaximalAt` transcribes this unchanged.

**(c) Definition 2.21 has the strict inequality.**  v1, p. 10: "Whenever α∗ > αa and M∗ is a lift
of M with M∗ ∈ Kα∗ then M∗ |= Q(a)."  The formal version holds at every stage `ζ` with `ξ ≤ ζ`,
which strengthens the printed `ζ > ξ`, as `README.md` says.

**(d) Definition 4.22 (d): rank-zero donors, cutoffs `n ∈ ω`, witnesses modulo renaming.**  v1,
pp. 20–21: "For all n ∈ ω, for all t, t∗ ∈ T, if Rt ∈ Lc[T] and Rt∗ ∈ R[T] with
(Qt(xy), Qt∗(x)) ∈ Itemp[T], then (∀x)[Rt∗(x) → (∃y) ⋁_{s∈T, Rs∈Lc[T], trn(s)≏trn(t)} Rs(xy)]."
The donor `t` has `R_t ∈ L_c[T]`, which by Definition 4.17 ("Rt : t ∈ T and τ0(Qt) = Qt") means
rank zero.

**(e) Nonempty domains.**  v1, §1.4 (p. 4): "All structures will be countable with non-empty
domains."  Definition 4.1 (p. 17) reads "A plan on a non-empty set A", and Definition 4.8 has
"∅ ≠ A0 ⊆ A".

**(f) "has been formalized".**  Verbatim in v1, p. 23: "This proof, which is substantial, has
been formalized."  v1 also says, in the abstract, "the proof has been formally verified in Lean",
and in §1.2 (p. 3), "not every line of this exposition has been formally verified".

## Corrections to the milestone records of 15 October 2026

These corrections are made here; the records themselves are unchanged.

1. **The convention for "limit" in Proposition 4.34.**  In
   [`2026-10-15-proposition-4-34.md`](2026-10-15-proposition-4-34.md), "The statements",
   "Hypotheses, explicitly", the words "`β` a nonzero limit (`Order.IsSuccLimit` excludes zero,
   the manuscript's convention)" should read "`β` a nonzero limit (`Order.IsSuccLimit` excludes
   zero, the convention of Claim 4.37 ('non-zero limit ordinal'))".  Neither the source draft nor
   v1 says whether "limit ordinal" in (Limits) of Proposition 4.34 includes `0`; the only explicit
   text is in the proof of Claim 4.37 (v1, p. 24): "If β is a non-zero limit ordinal and Mi has
   been defined for each i < β, then by Proposition 4.34 …".  Both readings are covered by the
   formal statements, since level zero is the separate theorem
   `exists_lift_zero_of_realize_templateSentence`.
2. **The statements of both records read identically in v1.**  Both records say: "The statements
   are relative to the pinned draft.  They are not an assertion that the pinned draft equals the
   published version of the paper, nor that the draft's text is final."  That remains a correct
   description of what each record verified.  In addition, the statements named in the
   correspondence sections of the two records read identically, in number and text, in v1:
   Definition 2.20 (p. 10), Definition 4.13 (p. 19), Definitions 4.20–4.22 (pp. 20–21) and
   Proposition 4.34 (p. 24), for the record of Proposition 4.34; Definition 2.20 (p. 10),
   Definition 4.21 (p. 20) and Proposition 4.35 (p. 24), for the record of Proposition 4.35.  The
   phrase "the manuscript's convention of nonempty domains" in the record of Proposition 4.35 is
   correct as it stands (v1, §1.4).
