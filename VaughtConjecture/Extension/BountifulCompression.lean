/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.SectionTheorem
import VaughtConjecture.Label.BlockCompress
import VaughtConjecture.Scheme.Bountiful

/-!
# Bountifulness from capped lifts at one stage, by block compression

Bountifulness (`CellScheme.Rows.IsBountiful`) quantifies over all labels: the cap and the two
labellings may take any ordinal values.  This file shows that for a scheme with finitely many
cells it suffices to have the capped lifts for a cap and labellings with values at one stage `θ`
with `ω ^ 2 ≤ θ` (`CellScheme.Rows.isBountiful_of_forall_atStage`); the stage need not be a limit.

**The argument.**  Given a cap `c`, a labelling `p` lawful below `X`, and a labelling `q` lawful
below `Y ≥ X` with the capped observation of `p` below `X`, let `V` be the finite set of the
values of `p` and `q`, the cap, and the label `0`.  The block compression `ν` of `V` at the grade
of `Y` (`Label.blockCompress`) is a witness bounded by that grade with values on `V` below
`ω ^ 2`; since `0 ∈ V`, every block has a target strip and `ν` sends only `⊥` to `⊥`
(`Label.blockCompress_eq_bot_iff_of_zero_mem`).  So `ν ∘ p` and `ν ∘ q` are lawful
(`CellScheme.Rows.IsLawful.map_of_bot_reflecting`), the cap `ν c` is self-visible at the grade of
`Y`, and, `ν` being monotone, the capped observations still agree.  The capped lift at stage `θ`
gives a labelling `r` lawful below `Y`, equal to `ν ∘ p` below `X`, with the capped observation of
`ν ∘ q` at `ν c`.  The block expansion `ρ` of `V` (`Label.blockExpand`) is a witness bounded by
every grade sending only `⊥` to `⊥` and inverting `ν` on `V`, so `ρ ∘ r` is lawful below `Y`,
equal to `p` below `X`, and has the capped observation of `q` at `c`.

No hypothesis on the rows is used: the rows are not changed, only the labellings and the cap.

## References

Bountifulness is [Kni26, Definition 2.5.14]; witnesses are [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Ordinal

namespace Label

/-- **With the label `0` among `V`, the compression sends only `⊥` to `⊥`**: every block lies at
or above the block `0` of `V`, so every ordinal label has a target strip, and the formal top goes
to an ordinal. -/
theorem blockCompress_eq_bot_iff_of_zero_mem {V : Finset Label.{u}} (h0 : (0 : Label.{u}) ∈ V)
    (K : ℕ) {x : Label.{u}} : blockCompress V K x = ⊥ ↔ x = ⊥ := by
  induction x using recBotCoeTop with
  | bot => simp
  | top => simp [blockCompress_top]
  | coe a =>
    refine iff_of_false ?_ (by simp)
    have hS : (0 : Ordinal.{u}) ∈ blockSet V := by
      have := blockOf_mem_blockSet (a := 0) (by simpa using h0)
      simpa [blockOf] using this
    obtain ⟨l, hΛ⟩ : ∃ l, (compressCode V K).Λ (blockOf a) = some l := by
      refine Option.ne_none_iff_exists'.mp fun hn ↦ ?_
      have hn' : targetOf (blockSet V) (fun μ ↦ ω * (blockRank V μ : Ordinal.{u}))
          (blockOf a) = none := hn
      exact (targetOf_eq_none_iff _ _ _).mp hn'
        ⟨0, Finset.mem_filter.mpr ⟨hS, bot_le⟩⟩
    change (compressCode V K).codeOrd a ≠ ⊥
    rw [BlockCode.codeOrd_of_some _ hΛ]
    simp

end Label

namespace CellScheme.Rows

open Label

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}}

/-- **Bountifulness from capped lifts at one stage**: for a scheme with finitely many cells and a
stage `θ ≥ ω ^ 2`, the rows are bountiful if, for all graded faces `X ≤ Y`, every cap `c` at
stage `θ` self-visible at the grade of `Y`, every `p` lawful below `X` and every `q` lawful below
`Y`, both with values at stage `θ`, whose capped observations at `c` agree below `X`, some
labelling lawful below `Y` restricts to `p` and has the capped observation of `q` at `c`.  The
labelling given by the hypothesis may take any values. -/
theorem isBountiful_of_forall_atStage [Finite ι] {θ : Ordinal.{u}} (hθ : ω ^ 2 ≤ θ)
    (h : ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces →
      ∀ (hXY : X ≤ Y) (c : Label.{u}), AtStage θ c → IsSelfVisible Y.2 c →
        ∀ (p : D.below X → Label.{u}) (q : D.below Y → Label.{u}),
          (∀ d, AtStage θ (p d)) → (∀ d, AtStage θ (q d)) →
          R.IsLawfulBelow X p → R.IsLawfulBelow Y q →
          (∀ d, min (q (Set.inclusion (D.below_mono hXY) d)) c = min (p d) c) →
          ∃ q' : D.below Y → Label.{u}, R.IsLawfulBelow Y q' ∧
            (∀ d, min (q' d) c = min (q d) c) ∧
            ∀ d, q' (Set.inclusion (D.below_mono hXY) d) = p d) :
    R.IsBountiful := by
  classical
  rw [isBountiful_iff_forall_exists]
  intro X Y hX hY hXY c hc p q hp hq hpq
  -- The finitely many labels involved, with `0`.
  set V : Finset Label.{u} := insert 0 (insert c
    ((Set.finite_range p).toFinset ∪ (Set.finite_range q).toFinset)) with hV
  have h0V : (0 : Label.{u}) ∈ V := Finset.mem_insert_self _ _
  have hcV : c ∈ V := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hpV (d : D.below X) : p d ∈ V := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_union_left _ ((Set.finite_range p).mem_toFinset.mpr ⟨d, rfl⟩)))
  have hqV (d : D.below Y) : q d ∈ V := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_union_right _ ((Set.finite_range q).mem_toFinset.mpr ⟨d, rfl⟩)))
  set ν := blockCompress V Y.2 with hν
  set ρ := blockExpand V with hρ
  have hνw : IsWitness (stepSuppressor Y.2) ν := isWitness_blockCompress (V := V) Y.2
  have hνbot : ∀ x, ν x = ⊥ → x = ⊥ := fun x ↦ (blockCompress_eq_bot_iff_of_zero_mem h0V _).mp
  have hρw : IsWitness (stepSuppressor Y.2) ρ := isWitness_blockExpand (V := V) Y.2
  have hρbot : ∀ x, ρ x = ⊥ → x = ⊥ := fun x ↦ blockExpand_eq_bot_iff.mp
  have hθV {x : Label.{u}} (hx : x ∈ V) : AtStage θ (ν x) :=
    .inl ((blockCompress_lt_omega0_sq hx Y.2).trans_le
      (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hθ)))
  have hρν {x : Label.{u}} (hx : x ∈ V) : ρ (ν x) = x := blockExpand_blockCompress hx Y.2
  -- The compressed data.
  have hpl : R.IsLawfulBelow X (ν ∘ p) :=
    isLawfulBelow_iff.mpr ((isLawfulBelow_iff.mp hp).map_of_bot_reflecting
      (fun d ↦ d.2.2.trans hXY.2) hνw hνbot)
  have hql : R.IsLawfulBelow Y (ν ∘ q) :=
    isLawfulBelow_iff.mpr ((isLawfulBelow_iff.mp hq).map_of_bot_reflecting
      (fun d ↦ d.2.2) hνw hνbot)
  have hcv : IsSelfVisible Y.2 (ν c) :=
    hνw.isSelfVisible_apply hc (by rw [stepSuppressor_of_le le_rfl]; exact le_top)
  have hpq' (d : D.below X) :
      min ((ν ∘ q) (Set.inclusion (D.below_mono hXY) d)) (ν c) = min ((ν ∘ p) d) (ν c) := by
    simp only [Function.comp_apply]
    rw [← hνw.monotone.map_min, hpq d, hνw.monotone.map_min]
  obtain ⟨r, hrl, hrc, hrr⟩ := h hX hY hXY (ν c) (hθV hcV) hcv (ν ∘ p) (ν ∘ q)
    (fun d ↦ hθV (hpV d)) (fun d ↦ hθV (hqV d)) hpl hql hpq'
  -- The expansion of the lift.
  refine ⟨ρ ∘ r, isLawfulBelow_iff.mpr ((isLawfulBelow_iff.mp hrl).map_of_bot_reflecting
    (fun d ↦ d.2.2) hρw hρbot), fun d ↦ ?_, fun d ↦ ?_⟩
  · calc min ((ρ ∘ r) d) c = min (ρ (r d)) (ρ (ν c)) := by rw [hρν hcV]; rfl
      _ = ρ (min (r d) (ν c)) := (hρw.monotone.map_min).symm
      _ = ρ (min (ν (q d)) (ν c)) := by rw [hrc d]; rfl
      _ = min (q d) c := by rw [hρw.monotone.map_min, hρν (hqV d), hρν hcV]
  · simp only [Function.comp_apply]
    rw [hrr d, Function.comp_apply, hρν (hpV d)]

end CellScheme.Rows

end VaughtConjecture
