/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.GatedExtension
import VaughtConjecture.Realization.Model

/-!
# The private context of the ordinary construction

Roadmap, Layer 3 (the private context of a receiving construction, with its private cap and its
reference cells); semantic contract, item 5 (the uniformity and high-arity-dominance clauses).

Let `R` be a model at stage `α`, let `x` be an occurrence of `R` (the **root**) on `m` points, and
let `d` be a stage type on `m + 1` points (the **donor**).  A **block** is an interval
`[μ, μ + ω)` of ordinals whose **block start** `μ` is zero or a limit; every ordinal `o` lies in
exactly one block, that of `μ = ω * (o / ω)`, as `μ + i` with `i = o % ω` its finite part.  The
**private context** of the ordinary construction is an occurrence `y` of `R`, on `n` points,
containing the root as a literal face, `f.trans y.tuple = x.tuple` for an embedding `f` of
coordinates, with

* a **private cap**: a cell `C` of `y` of full scope and full grade, graded index `(univ, n)`,
  labelled above a requested floor `γ`;
* for each proper label `μ + i` of the donor, a **reference cell** `z` of `y` (the roadmap's word;
  the anchoring condition of the gated extension calls it an **anchor** of the donor label, and
  this sense is unrelated to the anchor of the definition of hollowness).  It is labelled `μ + k`
  in the same block, with finite part `k < n`.  So its label is not self-visible at the threshold
  `n`, and visibility replacement at `n` with value `i` turns it into the donor label
  (`Label.visibilityReplace_coe_add_natCast`, `Label.not_isSelfVisible_coe_add_natCast`).  It is
  labelled strictly below the private cap;
* arity `n` above `m + 1` and above a requested bound `N₀`.

This is stronger than the anchoring condition of the gated extension, which asks, for each
non-bottom label of a new donor cell below the private cap, only for some cell `z` and some
`i ≤ n` with the donor label equal to `vr_n(i, label z)`, with no condition on `z`
(`VaughtConjecture.Realization.PrivateContextExamples`).

`IsModel.exists_privateContext` acquires the private context from the uniformity and
high-arity-dominance clauses alone ([Kni26, Definition 3.2.1], clauses 4(b) and 4(c)), with
`γ < α` the only hypothesis on the stage: neither generalized saturation, nor a marker, nor a
reference cell for the block of a cutoff is used.  The construction is in three steps.

* **Reference cells by uniformity** (`IsModel.exists_extend_uniformity`).  For a list of block
  starts below the stage, one uniformity step per block adds a point and a cell labelled in that
  block.  Labels of a literal face are labels of the larger occurrence
  (`Occurrence.exists_label_eq_of_trans_eq`), so the reference cells survive every later
  extension.  Their finite parts lie below a natural number `K`, and their labels are at most an
  ordinal `B < α` with `γ ≤ B`.
* **Padding by dominance** (`IsModel.exists_extend_dominance`).  Repeated dominance steps at the
  floor `B` raise the arity past `m + 1`, `N₀`, `K`, and the finite parts of the donor's labels,
  so the finite parts of the reference cells stay below the threshold.
* **The cap from the last step.**  The last dominance step gives a cell of grade equal to the new
  arity labelled above `B`; a cell of full grade has full scope
  (`StageType.gradedIndex_eq_univ_of_grade_eq`).

There is no reindexing: the root and the earlier occurrences are faces along existential
embeddings `f` with the tuple equation, and the literal face is the face map
(`Occurrence.restrictFace_eq_some_of_trans_eq`).  The block starts are those of the donor's
proper labels; a bottom or top label contributes the block start `0`, whose reference cell is not
used.  Uniformity at `0` needs `0 < α`, which follows from `γ < α`.

**The anchoring corollary** (`IsModel.exists_privateContext_isAnchored`) restates the private
context in the form of the anchoring condition of a gated extension (`StageType.IsAnchored`): a
non-bottom label of a new donor cell below the private cap is not the formal top, hence an
ordinal, and its reference cell is an anchor.  Of the clauses of a model it uses uniformity,
high-arity dominance, and exact consistency (for the literal face of the root).

This is the acquisition of the private context of the ordinary construction (R1) only.  The
gated scheme and the recovery of the donor from the gate are not here.  Finite-cut receiving for
all models, (R1) itself, is open: the universal gated extension hypothesis
`StageType.HasGatedPinnedExtensions` fails at every stage
(`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`), and the route through the coupled
gate (`IsModel.hasFiniteCutReceiving_of_hasCoupledGatedPinnedExtensions`) is conditional on a named
hypothesis that is false at every stage above `1`
(`CoupledGatedExtensionCounterexample.not_hasCoupledGatedPinnedExtensions`), so it is vacuous
there.  Nothing here concerns uniqueness or coherence of the context, or exact projected
receiving.

## References

The private context is that of [Kni26, Lemma 8.1.1], clauses 3 and 4; the proof of that lemma
cites high-arity dominance as clause 4(a) of [Kni26, Definition 3.2.1], where it is clause 4(c).
Only the private cap and the reference cells of the donor's blocks are produced here; the marker
and the reference cell of the block of the cutoff, which `roadmap/README.md` also lists, are not.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label
open scoped Ordinal

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-! ### Reference cells by uniformity -/

variable (hR : R.IsModel)
include hR

/-- **Reference cells by uniformity**: for a list `L` of block starts (ordinals that are zero or
limits) below the stage, an occurrence `y` containing `x` as a literal face along `f` with, for
every `μ ∈ L`, a reference cell: a cell labelled `μ + k` with finite part `k < K`.  These labels
are at most an ordinal `B < α` with `γ ≤ B`, for a given `γ < α`.  One uniformity step is taken
per block. -/
theorem IsModel.exists_extend_uniformity (x : R.Occurrence) {γ : Ordinal.{u}} (hγ : γ < α)
    (L : List Ordinal.{u}) (hL : ∀ μ ∈ L, Order.IsSuccPrelimit μ ∧ μ < α) :
    ∃ (y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity) (K : ℕ) (B : Ordinal.{u}),
      f.trans y.tuple = x.tuple ∧ γ ≤ B ∧ B < α ∧
        ∀ μ ∈ L, ∃ z, ∃ k < K,
          y.type.label z = ((μ + k : Ordinal.{u}) : Label.{u}) ∧ μ + k ≤ B := by
  induction L generalizing x with
  | nil => exact ⟨x, Function.Embedding.refl _, 0, γ, rfl, le_rfl, hγ, by simp⟩
  | cons μ L ih =>
    obtain ⟨hμ, hμα⟩ := hL μ List.mem_cons_self
    obtain ⟨u, hu, q, ⟨c, hc₁, hc₂⟩, he⟩ := hR.uniformity x μ hμ hμα
    obtain ⟨o, ho, hco⟩ : ∃ o < α, (o : Label.{u}) = q.label c := by
      rcases atStage_iff.mp (q.atStage c) with h | h | h
      · exact absurd hc₁ (by simp [h])
      · exact h
      · exact absurd hc₂ (by simp [h])
    rw [← hco] at hc₁ hc₂
    obtain ⟨k, rfl⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0
      (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hc₁))
      (WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hc₂))
    obtain ⟨y, f, K, B, hf, hγB, hBα, hanc⟩ :=
      ih ⟨_, u, q, he⟩ fun ν hν ↦ hL ν (List.mem_cons_of_mem _ hν)
    obtain ⟨z, hz⟩ := Occurrence.exists_label_eq_of_trans_eq hR.isConsistent hf c
    refine ⟨y, Fin.castSuccEmb.trans f, K + k + 1, max B (μ + k), ?_, le_max_of_le_left hγB,
      max_lt hBα ho, fun ν hν ↦ ?_⟩
    · rw [Function.Embedding.trans_assoc, hf, ← hu]
    rcases List.mem_cons.mp hν with rfl | hν
    · exact ⟨z, k, by omega, hz.trans hco.symm, le_max_right _ _⟩
    · obtain ⟨z', k', hk', hz', hB⟩ := hanc ν hν
      exact ⟨z', k', by omega, hz', le_max_of_le_left hB⟩

/-! ### Padding by dominance -/

/-- **Padding by dominance**: an extension `y` of `x` on `k + 1` more points with a cell of full
scope and full grade, graded index `(univ, y.arity)`, labelled above `γ < α`.  It is taken from
the last of `k + 1` dominance steps. -/
theorem IsModel.exists_extend_dominance (x : R.Occurrence) {γ : Ordinal.{u}} (hγ : γ < α)
    (k : ℕ) :
    ∃ (y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity), f.trans y.tuple = x.tuple ∧
      y.arity = x.arity + (k + 1) ∧ ∃ C : Fin y.type.card,
        y.type.toCellScheme.gradedIndex C = (univ, y.arity) ∧ (γ : Label.{u}) < y.type.label C := by
  have step (x : R.Occurrence) : ∃ (y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity),
      f.trans y.tuple = x.tuple ∧ y.arity = x.arity + 1 ∧ ∃ C : Fin y.type.card,
        y.type.toCellScheme.gradedIndex C = (univ, y.arity) ∧
          (γ : Label.{u}) < y.type.label C := by
    obtain ⟨u, hu, q, ⟨C, hC, hγC⟩, he⟩ := hR.dominance x γ hγ
    exact ⟨⟨_, u, q, he⟩, Fin.castSuccEmb, hu, rfl, C,
      StageType.gradedIndex_eq_univ_of_grade_eq q hC, hγC⟩
  induction k with
  | zero => exact step x
  | succ k ih =>
    obtain ⟨y', f', hf', hy', -⟩ := ih
    obtain ⟨y, g, hg, hy, hC⟩ := step y'
    exact ⟨y, f'.trans g, by rw [Function.Embedding.trans_assoc, hg, hf'], by omega, hC⟩

/-! ### The private context -/

/-- **The private context of the ordinary construction**, from the uniformity and dominance
clauses alone: over an occurrence `x` and for a donor `d` (on `x.arity + 1` points in the ordinary
construction; the donor enters only through its labels, so any number `m` of points is allowed),
an occurrence `y` containing `x` as a literal face along `f`, of arity above `x.arity + 1` and at
least `N₀`, with a private cap `C` of graded index `(univ, y.arity)` labelled above `γ < α`, and
for every proper donor label a reference cell `z`: the donor label is the visibility replacement at
the threshold `y.arity` of the label of `z` with a value `i < y.arity`, that label is not
self-visible at the threshold, and it lies strictly below the label of the cap.

The reference cells are taken by uniformity at the block starts of the donor's labels, the arity
is raised past their finite parts by dominance at a floor above the reference cells and `γ`, and
the cap comes from the last dominance step.  The only hypothesis on the stage is `γ < α`. -/
theorem IsModel.exists_privateContext (x : R.Occurrence) {m : ℕ} (d : StageType.{u} α m)
    {γ : Ordinal.{u}} (hγ : γ < α) (N₀ : ℕ) :
    ∃ (y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity) (C : Fin y.type.card),
      f.trans y.tuple = x.tuple ∧ x.arity + 1 < y.arity ∧ N₀ ≤ y.arity ∧
        y.type.toCellScheme.gradedIndex C = (univ, y.arity) ∧
        (γ : Label.{u}) < y.type.label C ∧
        ∀ (j : Fin d.card) (o : Ordinal.{u}), d.label j = o →
          ∃ z, ∃ i < y.arity, d.label j = visibilityReplace y.arity i (y.type.label z) ∧
            ¬ IsSelfVisible y.arity (y.type.label z) ∧ y.type.label z < y.type.label C := by
  -- the block start and a bound on the finite part of each label of the donor
  have hblock (j : Fin d.card) : ∃ μ : Ordinal.{u}, (Order.IsSuccPrelimit μ ∧ μ < α) ∧
      ∃ D : ℕ, ∀ o : Ordinal.{u}, d.label j = o → ∃ i < D, o = μ + i := by
    rcases atStage_iff.mp (d.atStage j) with h | ⟨o, ho, h⟩ | h
    · exact ⟨0, ⟨Ordinal.isSuccPrelimit_zero, zero_le.trans_lt hγ⟩, 0,
        fun o ho ↦ by simp [h] at ho⟩
    · obtain ⟨i, hi⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0
        (Ordinal.mul_div_le o ω) (Ordinal.lt_mul_div_add o Ordinal.omega0_ne_zero)
      refine ⟨ω * (o / ω), ⟨Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _),
        (Ordinal.mul_div_le o ω).trans_lt ho⟩, i + 1, fun o' ho' ↦ ⟨i, i.lt_succ_self, ?_⟩⟩
      rw [← h] at ho'
      exact (WithTop.coe_injective (WithBot.coe_injective ho')).symm.trans hi
    · exact ⟨0, ⟨Ordinal.isSuccPrelimit_zero, zero_le.trans_lt hγ⟩, 0,
        fun o ho ↦ by simp [h] at ho⟩
  choose μ hμ D hD using hblock
  obtain ⟨y₁, f₁, K, B, hf₁, hγB, hBα, hanc⟩ :=
    hR.exists_extend_uniformity x hγ (List.ofFn μ) fun ν hν ↦ by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hν
      exact hμ j
  obtain ⟨y, f₂, hf₂, hy, C, hC, hBC⟩ :=
    hR.exists_extend_dominance y₁ hBα (x.arity + 1 + N₀ + K + univ.sup D)
  refine ⟨y, f₁.trans f₂, C, by rw [Function.Embedding.trans_assoc, hf₂, hf₁], by omega,
    by omega, hC, lt_of_le_of_lt (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hγB)) hBC,
    fun j o ho ↦ ?_⟩
  obtain ⟨i, hi, rfl⟩ := hD j o ho
  obtain ⟨z₁, k, hk, hz₁, hkB⟩ := hanc (μ j) (List.mem_ofFn.mpr ⟨j, rfl⟩)
  obtain ⟨z, hz⟩ := Occurrence.exists_label_eq_of_trans_eq hR.isConsistent hf₂ z₁
  have hDj : D j ≤ univ.sup D := le_sup (mem_univ j)
  have hkn : k < y.arity := by omega
  refine ⟨z, i, by omega, ?_, ?_, ?_⟩ <;> rw [hz, hz₁]
  · rw [ho, visibilityReplace_coe_add_natCast (hμ j).1 hkn]
  · exact not_isSelfVisible_coe_add_natCast (hμ j).1 hkn
  · exact lt_of_le_of_lt (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hkB)) hBC

/-- **The private context, anchored**: over an occurrence `x` and for a donor `d` (on
`x.arity + 1` points in the ordinary construction, on any positive number `m + 1` of points here),
an occurrence `y` containing `x` as a literal face along `f` (with its type restricting along `f`
to that of `x`), of arity above `x.arity + 1`, with a cell `C` of graded index `(univ, y.arity)`
labelled above `γ < α`, below which `d` is anchored in the type of `y`.  Only the uniformity,
high-arity-dominance, and exact-consistency clauses are used. -/
theorem IsModel.exists_privateContext_isAnchored (x : R.Occurrence) {m : ℕ}
    (d : StageType.{u} α (m + 1)) {γ : Ordinal.{u}} (hγ : γ < α) :
    ∃ (y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity) (C : Fin y.type.card),
      f.trans y.tuple = x.tuple ∧ StageType.restrictFace f y.type = some x.type ∧
        x.arity + 1 < y.arity ∧ y.type.toCellScheme.gradedIndex C = (univ, y.arity) ∧
        (γ : Label.{u}) < y.type.label C ∧ StageType.IsAnchored y.type C d := by
  obtain ⟨y, f, C, hf, hn, -, hC, hγC, hanc⟩ := hR.exists_privateContext x d hγ 0
  refine ⟨y, f, C, hf, Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent hf, hn, hC,
    hγC, fun j _ hbot hlt ↦ ?_⟩
  induction hj : d.label j using recBotCoeTop with
  | bot => exact absurd hj hbot
  | coe o =>
    obtain ⟨z, i, hi, he, -, -⟩ := hanc j o hj
    exact ⟨z, i, hi.le, hj ▸ he⟩
  | top => exact absurd (hj ▸ hlt) not_top_lt

end Realization

end VaughtConjecture
