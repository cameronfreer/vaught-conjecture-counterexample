/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.StronglyCodedUniformity
import VaughtConjecture.MainTheorem.CodedLadderCutoffRecovery

/-!
# Calibrated contexts in the strongly coded receiving class

Roadmap, Layer 3 ((R4), the acquisition and evaluation steps) and Correspondence, item 1 (the
strongly coded legal stage types).

The acquisition of calibrated contexts for the margin calibration
(`Realization.IsModel.acquiresCalibratedContexts_gradedCapMargin`) assumes a model.  Its steps
use modelhood only for stable lawfulness, for reference cells by uniformity
(`Realization.IsModel.exists_extend_uniformity`), and for exact consistency and covering.  Here the
same acquisition is stated for a realization in the strongly coded receiving class: exactly
consistent and covering, with legal and strongly coded types and finite-cut receiving for the
cofaces with strongly coded rows.  Stable lawfulness is derived
(`Realization.isStablyLawful_of_hasLegalTypes`), and the reference cells come from strongly coded
receiving (`Realization.stronglyCodedReferenceCellsTarget`).

* `Realization.CalibratedContextAcquisitionTarget ξ M`: such a realization at `λ_ξ` that is not
  cover-hollow and has top-grade supremum `⊤` acquires calibrated contexts for the margin
  calibration (`Realization.AcquiresCalibratedContexts`, unchanged: every coface of the type of
  the occurrence, with no restriction on its rows).
* `Realization.StronglyCodedStablyReceivesAtTarget ξ M`: for such a realization, (R4) holds at
  every occurrence of the candidate of positive arity, every coface of its type with strongly coded
  rows and every `γ < λ_{ξ+1}`; the calibrated context is not a hypothesis.
* `Realization.acquiresCalibratedContexts_gradedCapMargin_of_exists_extend_uniformity`: the
  acquisition from exact consistency, covering, stable lawfulness and reference cells, with no other
  property of a model.
* `Realization.calibratedContextAcquisitionTarget` (from
  `Realization.acquiresCalibratedContexts_gradedCapMargin_of_isStronglyCoded`): the first target
  holds, for every coface.
* `Realization.stronglyCodedStablyReceivesAtTarget` (from
  `Realization.stablyReceivesAt_of_isStronglyCoded`): the second target holds; the acquired
  context is evaluated by
  `Realization.stablyReceivesAt_of_gradedCapMarginCalibration_of_isStronglyCoded`, which is where
  the strong coding of the coface is used.

All results here are native constructions of this repository.  Neither modelhood of the stable
candidate nor a terminal classification is concluded.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label StageType
open scoped Ordinal

namespace Realization

variable (ξ : Ordinal.{u}) (M : Type v)

/-- **Target: acquisition of calibrated contexts in the strongly coded receiving class**.  Let `R`
be a realization at `λ_ξ` on `M` that is exactly consistent (`hR`) and covering (`hc`), with legal
types (`hl`), strongly coded types (`hsc`) and finite-cut receiving for the cofaces with strongly
coded rows (`hrec`), not cover-hollow and with top-grade supremum `⊤`.  Then `R`, stably lawful by
`Realization.isStablyLawful_of_hasLegalTypes`, acquires calibrated contexts for the margin
calibration `StageType.GradedCapMarginCalibration ξ`.  The cofaces quantified in
`Realization.AcquiresCalibratedContexts` are all cofaces of the type of the occurrence. -/
def CalibratedContextAcquisitionTarget : Prop :=
  ∀ (R : Realization.{u, v} (blockStage ξ) M) (hR : R.IsConsistent) (hc : R.IsCovering)
    (hl : R.HasLegalTypes),
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} (blockStage ξ) n), R.eval t = some p →
      p.rows.IsStronglyCoded) →
    R.HasFiniteCutReceivingIn (fun t ↦ t.rows.IsStronglyCoded) →
    ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
      AcquiresCalibratedContexts ξ (GradedCapMarginCalibration ξ) R
        (isStablyLawful_of_hasLegalTypes hR hc hl)

/-- **Target: (R4) for strongly coded cofaces in the strongly coded receiving class**.  For `R` as
in `Realization.CalibratedContextAcquisitionTarget` (exactly consistent, covering, with legal and
strongly coded types, finite-cut receiving for the cofaces with strongly coded rows, not
cover-hollow, top-grade supremum `⊤`), (R4) holds at every occurrence `x` of the candidate of
positive arity, every coface `D` of its type with strongly coded rows and every `γ < λ_{ξ+1}`.
The calibrated context is not a hypothesis. -/
def StronglyCodedStablyReceivesAtTarget : Prop :=
  ∀ (R : Realization.{u, v} (blockStage ξ) M) (hR : R.IsConsistent) (hc : R.IsCovering)
    (hl : R.HasLegalTypes),
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} (blockStage ξ) n), R.eval t = some p →
      p.rows.IsStronglyCoded) →
    R.HasFiniteCutReceivingIn (fun t ↦ t.rows.IsStronglyCoded) →
    ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
      ∀ x : (R.stableCandidate (isStablyLawful_of_hasLegalTypes hR hc hl)).Occurrence,
        0 < x.arity → ∀ D ∈ x.type.cofaces, D.rows.IsStronglyCoded →
          ∀ γ : Ordinal.{u}, γ < blockStage (ξ + 1) →
            R.StablyReceivesAt (isStablyLawful_of_hasLegalTypes hR hc hl) x D γ

variable {ξ M} {R : Realization.{u, v} (blockStage ξ) M}

/-- **Acquisition of the margin calibration from reference cells** (native construction): the
argument of `Realization.IsModel.acquiresCalibratedContexts_gradedCapMargin`, with modelhood
replaced by its four uses: exact consistency (`hR`), covering (`hc`), stable lawfulness (`hlaw`, any
proof), and reference cells by uniformity (`huni`, the conclusion of
`Realization.IsModel.exists_extend_uniformity`).  For `R` at `λ_ξ` not cover-hollow and with
top-grade supremum `⊤`: over an occurrence `x` of the candidate, for a coface `D` of its type and
`γ ≤ λ_ξ + K`, `huni` gives reference cells for the blocks below `λ_ξ` of the labels of `D` in an
occurrence `y`, non-hollowness a marker in an occurrence `z₀`
(`Realization.exists_stableCandidate_label_eq_coe_add`), unbounded growth a cap of grade above every
finite part involved (`Realization.exists_coe_add_grade_le_stableCandidate_label`), and covering
one occurrence `w` containing them; exact consistency of `R` and of the candidate carries the labels
and the grades to the stable type of `w`.  The coface `D` enters only through its labels. -/
theorem acquiresCalibratedContexts_gradedCapMargin_of_exists_extend_uniformity
    (hR : R.IsConsistent) (hc : R.IsCovering) (hlaw : R.IsStablyLawful)
    (huni : ∀ (x : R.Occurrence) {γ : Ordinal.{u}}, γ < blockStage ξ → ∀ (L : List Ordinal.{u}),
      (∀ μ ∈ L, Order.IsSuccPrelimit μ ∧ μ < blockStage ξ) →
      ∃ (y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity) (K : ℕ) (B : Ordinal.{u}),
        f.trans y.tuple = x.tuple ∧ γ ≤ B ∧ B < blockStage ξ ∧
          ∀ μ ∈ L, ∃ z, ∃ k < K,
            y.type.label z = ((μ + k : Ordinal.{u}) : Label.{u}) ∧ μ + k ≤ B)
    (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤) :
    AcquiresCalibratedContexts ξ (GradedCapMarginCalibration ξ) R hlaw := by
  classical
  intro x hx D _ γ hγ
  have hlim := isSuccPrelimit_blockStage ξ
  have hpos : (0 : Ordinal.{u}) < blockStage ξ :=
    Ordinal.omega0_pos.trans_le (omega0_le_blockStage ξ)
  obtain ⟨K, hK⟩ := exists_le_blockStage_add_natCast hγ
  obtain ⟨t, ht, -⟩ := exists_eq_stableType_of_stableCandidate_eval x.eval_tuple
  -- the block of each label of `D`: below `λ_ξ` (a reference cell by uniformity) or `λ_ξ` itself
  have hblock (j : Fin D.card) : ∃ ν : Ordinal.{u}, (Order.IsSuccPrelimit ν ∧ ν < blockStage ξ) ∧
      ∃ B : ℕ, ∀ o : Ordinal.{u}, D.label j = o →
        ∃ n < B, o = ν + n ∨ o = blockStage ξ + n := by
    rcases atStage_iff.mp (D.atStage j) with h | ⟨o, ho, h⟩ | h
    · exact ⟨0, ⟨Ordinal.isSuccPrelimit_zero, hpos⟩, 0, fun o ho ↦ by simp [h] at ho⟩
    · rw [blockStage_add_one] at ho
      rcases lt_or_ge o (blockStage ξ) with hlt | hge
      · obtain ⟨n, hn⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0
          (Ordinal.mul_div_le o ω) (Ordinal.lt_mul_div_add o Ordinal.omega0_ne_zero)
        refine ⟨ω * (o / ω), ⟨Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _),
          (Ordinal.mul_div_le o ω).trans_lt hlt⟩, n + 1,
          fun o' ho' ↦ ⟨n, n.lt_succ_self, Or.inl ?_⟩⟩
        rw [← h] at ho'
        exact (WithTop.coe_injective (WithBot.coe_injective ho')).symm.trans hn
      · obtain ⟨n, hn⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0 hge ho
        refine ⟨0, ⟨Ordinal.isSuccPrelimit_zero, hpos⟩, n + 1,
          fun o' ho' ↦ ⟨n, n.lt_succ_self, Or.inr ?_⟩⟩
        rw [← h] at ho'
        exact (WithTop.coe_injective (WithBot.coe_injective ho')).symm.trans hn
    · exact ⟨0, ⟨Ordinal.isSuccPrelimit_zero, hpos⟩, 0, fun o ho ↦ by simp [h] at ho⟩
  choose ν hν B hB using hblock
  -- reference cells for the blocks below `λ_ξ`, in an occurrence `y` containing `x`
  obtain ⟨y, fy, K₁, B₁, hfy, -, -, hanc⟩ :=
    huni ⟨x.arity, x.tuple, t, ht⟩ hpos (List.ofFn ν) fun μ hμ ↦ by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hμ
      exact hν j
  -- a marker, in an occurrence `z₀` of the candidate
  obtain ⟨z₀, a₀, i₀, ha₀⟩ := exists_stableCandidate_label_eq_coe_add hnh hlaw
  -- a cap, in an occurrence `z₁` of the candidate, of grade above everything involved
  obtain ⟨z₁, b₁, hgb₁, hb₁⟩ := exists_coe_add_grade_le_stableCandidate_label hgrow
    hlaw (K + x.arity + K₁ + i₀ + univ.sup B + y.arity + z₀.arity)
  -- one occurrence `w` containing `y`, `z₀` and `z₁`
  obtain ⟨w, hw⟩ := hc.exists_subset_support
    (univ.map y.tuple ∪ univ.map z₀.tuple ∪ univ.map z₁.tuple)
  obtain ⟨g, hg⟩ := w.exists_trans_eq (subset_union_left.trans (subset_union_left.trans hw))
  obtain ⟨f₀, hf₀⟩ := w.exists_trans_eq (subset_union_right.trans (subset_union_left.trans hw))
  obtain ⟨f₁, hf₁⟩ := w.exists_trans_eq (subset_union_right.trans hw)
  -- the marker and the cap move to the stable type of `w` with their labels and grades
  have hcons := isConsistent_stableCandidate (hlaw := hlaw) hR hc
  let W : (R.stableCandidate hlaw).Occurrence :=
    ⟨w.arity, w.tuple, _, stableCandidate_eval_of_eval w.eval_tuple⟩
  obtain ⟨a', ha'l, ha'g⟩ := Occurrence.exists_label_grade_eq_of_trans_eq hcons (y := W) hf₀ a₀
  obtain ⟨b', hb'l, hb'g⟩ := Occurrence.exists_label_grade_eq_of_trans_eq hcons (y := W) hf₁ b₁
  have hN : K + x.arity + K₁ + i₀ + univ.sup B + y.arity + z₀.arity <
      W.type.toCellScheme.grade b' :=
    hgb₁.trans_eq hb'g.symm
  -- the bounds on the grade of the cap, stated for `W.type`, the stable type of `w`
  have hkN : x.arity < W.type.toCellScheme.grade b' := by omega
  have hRN : K + 1 < W.type.toCellScheme.grade b' := by omega
  have hBN : univ.sup B < W.type.toCellScheme.grade b' := by omega
  have hiN : i₀ < W.type.toCellScheme.grade b' := by omega
  have hK₁N : K₁ < W.type.toCellScheme.grade b' := by omega
  have hyN : y.arity < W.type.toCellScheme.grade b' := by omega
  have ha'N : W.type.toCellScheme.grade a' ≤ W.type.toCellScheme.grade b' := by
    have := z₀.type.grade_le a₀
    omega
  refine ⟨w, fy.trans g, by rw [Function.Embedding.trans_assoc, hg, hfy], b', ?_, hkN,
    ⟨K + 1, hRN, hK.trans_lt (add_lt_add_right (Nat.cast_lt.mpr (Nat.lt_succ_self K)) _)⟩,
    ⟨a', i₀, hiN, ha'N, ha'l.trans ha₀⟩, fun j o ho ↦ ?_⟩
  · -- the cap: its label in `W.type` is its label in `z₁.type`
    change _ ≤ W.type.label b'
    rw [hb'l, hb'g]
    exact hb₁
  · have hBj : B j ≤ univ.sup B := le_sup (mem_univ j)
    obtain ⟨n, hn, h | h⟩ := hB j o ho
    · -- a block below `λ_ξ`: the reference cell of `y`, moved to `w` with its label and grade
      obtain ⟨z, k, hk, hz, -⟩ := hanc (ν j) (List.mem_ofFn.mpr ⟨j, rfl⟩)
      obtain ⟨z', hz', hz'g⟩ := Occurrence.exists_label_grade_eq_of_trans_eq hR hg z
      have hne : w.type.label z' ≠ ⊤ := by
        rw [hz', hz]
        exact (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne
      refine ⟨ν j, n, k, z', (hν j).1, h, (hn.trans_le hBj).trans hBN,
        hk.trans hK₁N, hz'g.trans_le ((y.type.grade_le z).trans hyN.le), ?_⟩
      -- the label of the stable type at `z'` is the stable section there
      change R.stableSection w.tuple w.type z' = _
      rw [stableSection_of_ne_top hne, hz', hz]
    · -- the block `λ_ξ`: the marker
      exact ⟨blockStage ξ, n, i₀, a', hlim, h, (hn.trans_le hBj).trans hBN, hiN, ha'N,
        ha'l.trans ha₀⟩

/-- **Acquisition of calibrated contexts in the strongly coded receiving class** (native
construction): `Realization.acquiresCalibratedContexts_gradedCapMargin_of_exists_extend_uniformity`
with the reference cells from strongly coded receiving
(`Realization.stronglyCodedReferenceCellsTarget`, at the block stage `λ_ξ`, zero or a limit).  The
strong coding of the types and the receiving are used only there; the coface quantifier of
`Realization.AcquiresCalibratedContexts` is unrestricted. -/
theorem acquiresCalibratedContexts_gradedCapMargin_of_isStronglyCoded (hR : R.IsConsistent)
    (hc : R.IsCovering) (hl : R.HasLegalTypes)
    (hsc : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} (blockStage ξ) n), R.eval t = some p →
      p.rows.IsStronglyCoded)
    (hrec : R.HasFiniteCutReceivingIn fun t ↦ t.rows.IsStronglyCoded)
    (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤) :
    AcquiresCalibratedContexts ξ (GradedCapMarginCalibration ξ) R
      (isStablyLawful_of_hasLegalTypes hR hc hl) :=
  acquiresCalibratedContexts_gradedCapMargin_of_exists_extend_uniformity hR hc _
    (fun x _ hγ L hL ↦ stronglyCodedReferenceCellsTarget (blockStage ξ) M
      (isSuccPrelimit_blockStage ξ) R hR (fun _ t p h ↦ ⟨hl t p h, hsc t p h⟩) hrec x hγ L hL)
    hnh hgrow

/-- **Target: acquisition of calibrated contexts in the strongly coded receiving class** (native
construction): `Realization.acquiresCalibratedContexts_gradedCapMargin_of_isStronglyCoded`. -/
theorem calibratedContextAcquisitionTarget : CalibratedContextAcquisitionTarget ξ M :=
  fun _ hR hc hl hsc hrec hnh hgrow ↦
    acquiresCalibratedContexts_gradedCapMargin_of_isStronglyCoded hR hc hl hsc hrec hnh hgrow

/-- **(R4) for strongly coded cofaces in the strongly coded receiving class** (native
construction): the acquired calibrated context
(`Realization.acquiresCalibratedContexts_gradedCapMargin_of_isStronglyCoded`) evaluated by
`Realization.stablyReceivesAt_of_gradedCapMarginCalibration_of_isStronglyCoded`, which uses the
strong coding of the coface `D`. -/
theorem stablyReceivesAt_of_isStronglyCoded (hR : R.IsConsistent) (hc : R.IsCovering)
    (hl : R.HasLegalTypes)
    (hsc : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} (blockStage ξ) n), R.eval t = some p →
      p.rows.IsStronglyCoded)
    (hrec : R.HasFiniteCutReceivingIn fun t ↦ t.rows.IsStronglyCoded)
    (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤)
    {x : (R.stableCandidate (isStablyLawful_of_hasLegalTypes hR hc hl)).Occurrence}
    (hx : 0 < x.arity) {D : StageType.{u} (blockStage (ξ + 1)) (x.arity + 1)}
    (hD : D ∈ x.type.cofaces) (hDs : D.rows.IsStronglyCoded) {γ : Ordinal.{u}}
    (hγ : γ < blockStage (ξ + 1)) :
    R.StablyReceivesAt (isStablyLawful_of_hasLegalTypes hR hc hl) x D γ := by
  obtain ⟨w, f, hf, hC⟩ :=
    acquiresCalibratedContexts_gradedCapMargin_of_isStronglyCoded hR hc hl hsc hrec hnh hgrow
      x hx D hD γ hγ
  exact stablyReceivesAt_of_gradedCapMarginCalibration_of_isStronglyCoded hR hc hl hsc hrec hx hD
    hDs hγ w hf hC

/-- **Target: (R4) for strongly coded cofaces in the strongly coded receiving class** (native
construction): `Realization.stablyReceivesAt_of_isStronglyCoded`. -/
theorem stronglyCodedStablyReceivesAtTarget : StronglyCodedStablyReceivesAtTarget ξ M :=
  fun _ hR hc hl hsc hrec hnh hgrow _ hx _ hD hDs _ hγ ↦
    stablyReceivesAt_of_isStronglyCoded hR hc hl hsc hrec hnh hgrow hx hD hDs hγ

end Realization

end VaughtConjecture
