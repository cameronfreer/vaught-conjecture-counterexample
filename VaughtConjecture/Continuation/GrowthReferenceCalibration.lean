/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthExactCarrier

/-!
# The hollow reference calibration with donor offsets below the cap

Roadmap, Layer 3 ((R3), acquisition of calibrated contexts).  The recovery of a growth carrier
reads a proper donor label `μ + m` through a reference cell `μ + r` of the context, replacing its
finite part at the grade `N` of the cap: `visibilityReplace N m (μ + r) = μ + m` needs `r < N`, and
the cap-agreement step of the recovery needs `m ≤ N` (the offset of each exact request at most the
grade of the cap).  The first bound is the root offset bound of the acquired marked-cap contexts
(`StageType.RootOffsetsBelow`).  The second is **not** a consequence of the donor being a coface of
the root: a new cell of a coface can carry `μ + m` with `m` arbitrarily large (self-visibility at
its grade bounds `m` from below, not from above).  It is acquired here with no further hypothesis
and no further clause of a model: the root is first enlarged to an occurrence with more points
than every donor offset, and the cap of a marked-cap context along a root of `j` points has grade
above `j + 1`.

## Main definitions

* `StageType.HollowReferenceCalibration'`: `StageType.HollowReferenceCalibration` with the cap and
  marker named and every donor offset below the grade of the cap.

## Main statements

* `StageType.HollowReferenceCalibration'.hollowReferenceCalibration`: it is a reference
  calibration.
* `Realization.hollowGrowthAcquisition_reference'`: its acquisition, with no hypothesis.
* `Realization.hollowReceiving_of_hasExactGrowthCarriers_reference'`: (R3) for cover-hollowness at
  a block stage from exact growth carriers for it.

## References

Uniformity and generalized saturation are [Kni26, Definition 3.2.1, clauses 4(a)i and 4(b)].
-/

universe u w

namespace VaughtConjecture

open Finset Label StageType

namespace StageType

/-- The **hollow reference calibration with bounded donor offsets** of a context `t'` along `h` for
a donor `d`: `h` factors through an enlarged root `g` along which `t'` is a marked-cap context at
the cap `c` and marker `r`, with root offsets below the grade of `c` and root bottoms respected,
and every ordinal label `o` of `d` is `μ + m`, `μ` zero or a limit, with `m` below the grade of
`c` and a reference cell `μ + r'` of the enlarged root. -/
def HollowReferenceCalibration' {α : Ordinal.{u}} {n k : ℕ} (t' : StageType.{u} α k)
    (h : Fin n ↪ Fin k) (d : StageType.{u} α (n + 1)) : Prop :=
  ∃ (j : ℕ) (g : Fin j ↪ Fin k) (h₀ : Fin n ↪ Fin j) (c r : Fin t'.card), h₀.trans g = h ∧
    t'.IsMarkedCapContextAt g c r ∧ t'.RootOffsetsBelow g (t'.toCellScheme.grade c) ∧
    t'.RootBottomRespected g c ∧
    ∀ (i : Fin d.card) (o : Ordinal.{u}), d.label i = o →
      ∃ (μ : Ordinal.{u}) (m r' : ℕ) (a : Fin t'.card), Order.IsSuccPrelimit μ ∧
        o = μ + m ∧ m < t'.toCellScheme.grade c ∧ a ∈ t'.visibleCells g ∧
          t'.label a = ((μ + r' : Ordinal.{u}) : Label.{u})

/-- The calibration with bounded donor offsets is a reference calibration. -/
theorem HollowReferenceCalibration'.hollowReferenceCalibration {α : Ordinal.{u}} {n k : ℕ}
    {t' : StageType.{u} α k} {h : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)}
    (hC : HollowReferenceCalibration' t' h d) : HollowReferenceCalibration t' h d := by
  obtain ⟨j, g, h₀, c, r, hh, hmc, hoff, hbot, href⟩ := hC
  refine ⟨j, g, h₀, hh, ⟨c, r, hmc, hoff, hbot⟩, fun i o ho ↦ ?_⟩
  obtain ⟨μ, m, r', a, hμ, hm, -, ha, hal⟩ := href i o ho
  exact ⟨μ, m, r', a, hμ, hm, ha, hal⟩

/-- **Exact growth carriers are antitone in the calibration**: carriers for a calibration give
carriers for every stronger one. -/
theorem HasExactGrowthCarriers.mono
    {C C' : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop}
    (hcar : HasExactGrowthCarriers C)
    (hCC' : ∀ {α : Ordinal.{u}} {n k : ℕ} (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
      (d : StageType.{u} α (n + 1)), C' t' h d → C t' h d) :
    HasExactGrowthCarriers C' :=
  fun _ _ _ t' h hα ht' t ht d hd hC ↦ hcar t' h hα ht' t ht d hd (hCC' t' h d hC)

/-- **Blocks with a bound on the offsets**: at a limit stage every ordinal label of a stage type
is `μ + m` with `μ` zero or a limit below the stage and `m` below a bound depending on the cell. -/
theorem exists_block_bound {α : Ordinal.{u}} {n : ℕ} (hα : Order.IsSuccLimit α)
    (d : StageType.{u} α n) (i : Fin d.card) :
    ∃ μ : Ordinal.{u}, (Order.IsSuccPrelimit μ ∧ μ < α) ∧
      ∃ B : ℕ, ∀ o : Ordinal.{u}, d.label i = o → ∃ m < B, o = μ + m := by
  obtain ⟨μ, hμ, hm⟩ := exists_block hα d i
  rcases atStage_iff.mp (d.atStage i) with h | ⟨o, -, h⟩ | h
  · exact ⟨μ, hμ, 0, fun o ho ↦ by simp [h] at ho⟩
  · obtain ⟨m, hm'⟩ := hm o h.symm
    refine ⟨μ, hμ, m + 1, fun o' ho' ↦ ⟨m, m.lt_succ_self, ?_⟩⟩
    rw [← h] at ho'
    exact (WithTop.coe_injective (WithBot.coe_injective ho')).symm.trans hm'
  · exact ⟨μ, hμ, 0, fun o ho ↦ by simp [h] at ho⟩

end StageType

namespace Realization

/-- **Acquisition of the hollow reference calibration with bounded donor offsets**, with no
hypothesis.  Uniformity gives an occurrence `y` containing the cover with a reference cell in the
block of every ordinal label of the donor; covering gives an occurrence `w` containing `y` and an
occurrence with more points than every donor offset; the acquisition of marked-cap contexts over
`w` (`Realization.rootBottomAcquisition`) gives a cap of grade above the number of points of `w`,
hence above every donor offset. -/
theorem hollowGrowthAcquisition_reference' :
    HollowGrowthAcquisition.{u, w} IsCoverHollowAtBlock StageType.HollowReferenceCalibration' where
  exists_context α M R hα hR hH htop n t c hc d _ := by
    classical
    choose ν hν B hB using StageType.exists_block_bound hα d
    let x : R.Occurrence := ⟨n, ⟨c, hc.injective⟩, t, hc.eval_eq⟩
    obtain ⟨y, fy, K, B₁, hfy, -, -, href⟩ :=
      hR.exists_extend_uniformity x hα.bot_lt (List.ofFn ν) fun μ hμ ↦ by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hμ
        exact hν i
    obtain ⟨z, hz⟩ := hR.exists_le_arity hα.bot_lt (univ.sup B)
    obtain ⟨w, hw⟩ := hR.isCovering.exists_subset_support (univ.map y.tuple ∪ univ.map z.tuple)
    obtain ⟨gy, hgy⟩ := w.exists_trans_eq (subset_union_left.trans hw)
    obtain ⟨gz, -⟩ := w.exists_trans_eq (subset_union_right.trans hw)
    have hzw : z.arity ≤ w.arity := by simpa using Fintype.card_le_of_embedding gz
    obtain ⟨k, t', c', g, hc', hcg, ⟨cc, rr, hmc, hoff, hbot⟩⟩ :=
      rootBottomAcquisition.exists_context hα hR hH htop w.type w.tuple
        (covers_of_eval _ w.eval_tuple)
    have hface : restrictFace g t' = some w.type :=
      restrictFace_of_covers hR.isConsistent (covers_of_eval _ w.eval_tuple) hc' hcg
    have hgrade : w.arity + 1 < t'.toCellScheme.grade cc := hmc.2.2.1
    refine ⟨k, t', c', (fy.trans gy).trans g, hc', ?_, w.arity, g, fy.trans gy, cc, rr, rfl,
      hmc, hoff, hbot, fun i o ho ↦ ?_⟩
    · funext i
      change (c' ∘ g) (gy (fy i)) = c i
      rw [hcg]
      change (gy.trans w.tuple) (fy i) = c i
      rw [hgy]
      exact DFunLike.congr_fun hfy i
    · obtain ⟨m, hmB, hm⟩ := hB i o ho
      obtain ⟨zc, r', -, hzc, -⟩ := href (ν i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
      obtain ⟨zw, hzw', -⟩ := Occurrence.exists_label_grade_eq_of_trans_eq hR.isConsistent hgy zc
      obtain ⟨z', -, hz'l, -⟩ := exists_cellMap_of_restrictFace_eq hface zw
      have hmN : m < t'.toCellScheme.grade cc := by
        have := le_sup (f := B) (mem_univ i)
        omega
      exact ⟨ν i, m, r', t'.cellMap g z', (hν i).1, hm, hmN, t'.cellMap_mem g z',
        hz'l.trans (hzw'.trans hzc)⟩

/-- **(R3) from exact growth carriers for the reference calibration with bounded donor offsets**:
exact growth carriers for `StageType.HollowReferenceCalibration'`, a finite statement about stage
types (open), give (R3) for cover-hollowness at a block stage; the acquisition is compiled
(`Realization.hollowGrowthAcquisition_reference'`). -/
theorem hollowReceiving_of_hasExactGrowthCarriers_reference'
    (hcar : HasExactGrowthCarriers.{u} StageType.HollowReferenceCalibration') :
    HollowReceiving.{u, w} IsCoverHollowAtBlock :=
  hollowReceiving_of_hasExactGrowthCarriers hollowGrowthAcquisition_reference' hcar

/-- The receiving form: the third hypothesis of the three-hypothesis main theorem from exact
growth carriers for `StageType.HollowReferenceCalibration'` (open). -/
theorem receivingHollowReceiving_of_hasExactGrowthCarriers_reference'
    (hcar : HasExactGrowthCarriers.{u} StageType.HollowReferenceCalibration') :
    HollowReceiving.{u, w} IsReceivingCoverHollowAtBlock :=
  (hollowReceiving_of_hasExactGrowthCarriers_reference' hcar).receiving

end Realization

end VaughtConjecture
