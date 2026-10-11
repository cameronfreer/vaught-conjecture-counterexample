/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CappedDonorReading
import VaughtConjecture.Extension.Gate

/-!
# The capped reading at the private cells labelled in a requested block

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the capped reading of the donor on the
root); the reference data with the margin of `VaughtConjecture.Extension.CappedDonorReading`.

Let the reference data `P` have the margin (`CappedDonorReading.PrivateReference.HasMargin`), with
full grade `N`, for the rows `R` of the private cells and the actual labels `w`.

**The code of a private cell labelled in a requested block**
(`CappedDonorReading.PrivateReference.HasMargin.row_cap_eq_visibilityReplace`).  A private cell
`x` labelled `ω * b + i`, with `b` a requested block and `i < N`, is read by the row of the cap as
`vr_N(i, ·)` of the code of the reference cell of `b`.  The capped witness of the actual labels at
the cap reads the code of `x` as `ω * b + i` and that of the reference cell, `ω * r + j` with
`j < N`, as `ω * b + off b`; it is monotone and commutes with the replacements at `N`, so the code
of `x` can be neither in another code block nor at a finite part at least `N`.

**The root clause** (`CappedDonorReading.PrivateReference.HasMargin.min_cut_eq_reading`).  Hence
every lawful labelling `v` of the private cells reads such a cell as the capped reading of its
label: `min (v x) (cut v) = reading v (w x)`, the clause (ii) of the capped-donor lemma for the
cells labelled in a requested block with finite part below `N`.  For a cell labelled `⊤` the
clause is `cut v ≤ v x` (the reading of `⊤` is the cut), which holds when the cap is labelled
strictly above every `ω * b + N` (`CappedDonorReading.PrivateReference.HasMargin.cut_le_of_eq_top`).
For a cell labelled `⊥` the clause asks `v x = ⊥`, which lawfulness does not force: a lawful
labelling not `⊥` there is outside the clause, as in the activity condition of the reading.  For a
label with finite part `N` nothing is claimed: the cap may code such a cell anywhere above the code
of `ω * b + N` read through the reference cell (argued, not formalized); the private context of
`Realization.IsModel.exists_marginContext` has every finite part of the donor below `N`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`, beside
`VaughtConjecture.Extension.CappedDonorReading`.

## References

The private context is that of [Kni26, Lemma 8.1.1]; witnesses are [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture.CappedDonorReading.PrivateReference

open Finset Label Ordinal

variable {ι α : Type*} {P : PrivateReference.{u} ι} {D : CellScheme ι α} {R : D.Rows.{u}}
  {w v : ι → Label.{u}}

/-- **The code of a private cell labelled in a requested block.**  With the margin, a private
cell labelled `ω * b + i`, for a requested block `b` and `i < N`, is read by the row of the cap as
`vr_N(i, ·)` of the code of the reference cell of `b`. -/
theorem HasMargin.row_cap_eq_visibilityReplace (hP : P.HasMargin R w) {x : ι} {b : Ordinal.{u}}
    (hb : b ∈ P.blocks) {i : ℕ} (hi : i < P.fullGrade)
    (hx : w x = ((ω * b + i : Ordinal.{u}) : Label.{u})) :
    R.row P.cap ⟨x, hP.mem_below x⟩ =
      visibilityReplace P.fullGrade i (R.row P.cap ⟨P.ref b, hP.mem_below _⟩) := by
  set N := P.fullGrade
  obtain ⟨τ, hτ, -, hrow⟩ := hP.exists_isWitness_capped hP.isLawful
  obtain ⟨r, j, hcode, -⟩ := hP.exists_code
  obtain ⟨hj, hz⟩ := hcode b hb
  have hoff := hP.off_lt b hb
  -- The capped witness reads the code of the reference cell and the code of `x`.
  have hτz : τ (R.row P.cap ⟨P.ref b, hP.mem_below _⟩) =
      ((ω * b + P.off ⟨b, hb⟩ : Ordinal.{u}) : Label.{u}) := by
    rw [hrow, hP.label_ref b hb, min_eq_left (le_trans ?_ (hP.margin b hb))]
    exact coe_omega0_mul_add_le_coe_iff.mpr (.inr ⟨rfl, hoff.le⟩)
  have hτx : τ (R.row P.cap ⟨x, hP.mem_below x⟩) = ((ω * b + i : Ordinal.{u}) : Label.{u}) := by
    rw [hrow, hx, min_eq_left (le_trans ?_ (hP.margin b hb))]
    exact coe_omega0_mul_add_le_coe_iff.mpr (.inr ⟨rfl, hi.le⟩)
  -- The points of the code block of the reference cell, read by the witness.
  have hpt (k : ℕ) (hk : k ≤ N) : τ ((ω * r b + k : Ordinal.{u}) : Label.{u}) =
      ((ω * b + k : Ordinal.{u}) : Label.{u}) := by
    have hvr : ((ω * r b + k : Ordinal.{u}) : Label.{u}) =
        visibilityReplace N k ((ω * r b + j b : Ordinal.{u}) : Label.{u}) := by
      rw [visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast,
        ite_eq_left hj]
    rw [hvr, hτ.visibilityReplace_comm _ _ (by simp [N]) _ hk, ← hz, hτz, visibilityReplace_coe,
      Ordinal.visibilityReplace_omega0_mul_add_natCast, ite_eq_left hoff]
  have hN : 0 < N := by omega
  -- The code of `x`.
  rw [hz, visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast,
    ite_eq_left hj]
  have hcases : ∀ y : Label.{u}, y = ⊥ ∨ (∃ o : Ordinal.{u}, y = (o : Label.{u})) ∨ y = ⊤ :=
    fun y ↦ by induction y using recBotCoeTop <;> simp
  have hlow : ¬ ((ω * b + N : Ordinal.{u}) : Label.{u}) ≤ ((ω * b + i : Ordinal.{u}) : Label.{u}) :=
    fun h ↦ by
      rcases coe_omega0_mul_add_le_coe_iff.mp h with h | ⟨-, h⟩
      · exact lt_irrefl _ h
      · omega
  rcases hcases (R.row P.cap ⟨x, hP.mem_below x⟩) with hyb | ⟨o, hyo⟩ | hyt
  · rw [hyb, hτ.map_bot] at hτx
    exact absurd hτx.symm WithBot.coe_ne_bot
  · rw [hyo] at hτx ⊢
    obtain ⟨r', i', rfl⟩ : ∃ (r' : Ordinal.{u}) (i' : ℕ), o = ω * r' + i' :=
      ⟨o / ω, finitePart o, (omega0_mul_div_add_finitePart o).symm⟩
    rcases lt_trichotomy r' (r b) with hlt | rfl | hgt
    · -- A lower code block: `i = 0`, and the replacements of the code clash.
      have hle : ((ω * r' + i' : Ordinal.{u}) : Label.{u}) ≤
          ((ω * r b + (0 : ℕ) : Ordinal.{u}) : Label.{u}) :=
        coe_omega0_mul_add_le_coe_iff.mpr (.inl hlt)
      have h1 := hτ.monotone hle
      rw [hτx, hpt 0 (Nat.zero_le _)] at h1
      have hi0 : i = 0 := by
        rcases coe_omega0_mul_add_le_coe_iff.mp h1 with h | ⟨-, h⟩
        · exact absurd h (lt_irrefl _)
        · omega
      subst hi0
      by_cases hi' : i' < N
      · have hvr : ((ω * r' + N : Ordinal.{u}) : Label.{u}) =
            visibilityReplace N N ((ω * r' + i' : Ordinal.{u}) : Label.{u}) := by
          rw [visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast,
            ite_eq_left hi']
        have h2 := hτ.monotone (show ((ω * r' + N : Ordinal.{u}) : Label.{u}) ≤
            ((ω * r b + (0 : ℕ) : Ordinal.{u}) : Label.{u}) from
          coe_omega0_mul_add_le_coe_iff.mpr (.inl hlt))
        rw [hvr, hτ.visibilityReplace_comm _ _ (by simp [N]) _ le_rfl, hτx, hpt 0 (Nat.zero_le _),
          visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast,
          ite_eq_left hN] at h2
        rcases coe_omega0_mul_add_le_coe_iff.mp h2 with h | ⟨-, h⟩
        · exact absurd h (lt_irrefl _)
        · omega
      · have hsv : visibilityReplace N N ((ω * r' + i' : Ordinal.{u}) : Label.{u}) =
            ((ω * r' + i' : Ordinal.{u}) : Label.{u}) := by
          rw [visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast,
            ite_eq_right hi']
        have h2 := hτ.visibilityReplace_comm ((ω * r' + i' : Ordinal.{u}) : Label.{u}) N
          (by simp [N]) N le_rfl
        rw [hsv, hτx, visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast,
          ite_eq_left hN, WithBot.coe_inj, WithTop.coe_inj] at h2
        exact absurd (congrArg (· % ω) h2) (by
          simp only [omega0_mul_add_natCast_mod]
          exact_mod_cast hN.ne)
    · -- The same code block: the finite part is `i`.
      by_cases hi' : i' < N
      · have h1 := (hpt i' hi'.le).symm.trans hτx
        rw [WithBot.coe_inj, WithTop.coe_inj] at h1
        have h2 := congrArg (· % ω) h1
        simp only [omega0_mul_add_natCast_mod, Nat.cast_inj] at h2
        rw [h2]
      · refine absurd ?_ hlow
        rw [← hpt N le_rfl, ← hτx]
        exact hτ.monotone (coe_omega0_mul_add_le_coe_iff.mpr (.inr ⟨rfl, by omega⟩))
    · -- A higher code block.
      refine absurd ?_ hlow
      rw [← hpt N le_rfl, ← hτx]
      exact hτ.monotone (coe_omega0_mul_add_le_coe_iff.mpr (.inl hgt))
  · rw [hyt] at hτx
    refine absurd ?_ hlow
    rw [← hpt N le_rfl, ← hτx]
    exact hτ.monotone le_top


/-- **The root clause for a private cell labelled in a requested block.**  With the margin, every
lawful labelling `v` of the private cells reads a private cell labelled `ω * b + i`, `b` a
requested block and `i < N`, as the capped reading of that label, up to the cut:
`min (v x) (cut v) = reading v (w x)`. -/
theorem HasMargin.min_cut_eq_reading (hP : P.HasMargin R w) (hv : R.IsLawful v) {x : ι}
    {b : Ordinal.{u}} (hb : b ∈ P.blocks) {i : ℕ} (hi : i < P.fullGrade)
    (hx : w x = ((ω * b + i : Ordinal.{u}) : Label.{u})) :
    min (v x) (P.cut v) = P.reading v (w x) := by
  have hrow := hP.row_cap_eq_visibilityReplace hb hi hx
  have hg : D.grade P.cap = P.fullGrade := hP.grade_cap
  have h := hv.min_eq_visibilityReplace_of_row_eq (K := P.cap) (z := ⟨P.ref b, hP.mem_below _⟩)
    (e := ⟨x, hP.mem_below x⟩) (i := i) (hg ▸ hi.le) (by rw [hg]; exact hrow)
  rw [hg] at h
  have hcut : P.cut v ≤ v P.cap := min_le_left _ _
  rw [hx, reading_omega0_mul_add]
  calc min (v x) (P.cut v) = min (min (v x) (v P.cap)) (P.cut v) := by
        rw [min_assoc, min_eq_right hcut]
    _ = min (min (visibilityReplace P.fullGrade i (v (P.ref b))) (v P.cap)) (P.cut v) := by
        rw [h]
    _ = min (visibilityReplace P.fullGrade i (v (P.ref b))) (P.cut v) := by
        rw [min_assoc, min_eq_right hcut]


/-- **A private cell labelled `⊤` is at least the cut** in every lawful labelling, when the cap is
labelled strictly above every `ω * b + N`: the row of the cap codes it at least as the code
`vr_N(N, ·)` of every reference cell, so one witness at the cap reads it at least as every
`vr_N(N, v (ref b))`, capped at the cap. -/
theorem HasMargin.cut_le_of_eq_top (hP : P.HasMargin R w)
    (hstrict : ∀ b ∈ P.blocks, ((ω * b + P.fullGrade : Ordinal.{u}) : Label.{u}) < w P.cap)
    (hv : R.IsLawful v) {x : ι} (hx : w x = ⊤) : P.cut v ≤ v x := by
  obtain ⟨τ, hτ, -, hrow⟩ := hP.exists_isWitness_capped hP.isLawful
  obtain ⟨r, j, hcode, -⟩ := hP.exists_code
  obtain ⟨g, σ, hσ, hgN, heq⟩ := hv.exists_gateWitness P.cap
  have hg : D.grade P.cap = P.fullGrade := hP.grade_cap
  rw [hg] at hgN
  have hvC : IsSelfVisible P.fullGrade (v P.cap) := hg ▸ hv.orderly P.cap
  -- The code of `x` lies above `vr_N(N, ·)` of the code of every reference cell.
  have hcodex (b : Ordinal.{u}) (hb : b ∈ P.blocks) :
      visibilityReplace P.fullGrade P.fullGrade (R.row P.cap ⟨P.ref b, hP.mem_below _⟩) ≤
        R.row P.cap ⟨x, hP.mem_below x⟩ := by
    obtain ⟨hj, hz⟩ := hcode b hb
    have hoff := hP.off_lt b hb
    by_contra hlt
    rw [not_le] at hlt
    have h1 := hτ.monotone hlt.le
    rw [hτ.visibilityReplace_comm _ _ (by simp) _ le_rfl, hrow, hrow, hx, min_top_left,
      hP.label_ref b hb, min_eq_left (le_trans (coe_omega0_mul_add_le_coe_iff.mpr
        (.inr ⟨rfl, hoff.le⟩)) (hP.margin b hb)), visibilityReplace_coe,
      Ordinal.visibilityReplace_omega0_mul_add_natCast, ite_eq_left hoff] at h1
    exact (hstrict b hb).not_ge h1
  -- One witness at the cap reads each `vr_N(N, v (ref b))`, capped, below `v x`.
  have hb (b : Ordinal.{u}) (hb : b ∈ P.blocks) :
      min (visibilityReplace P.fullGrade P.fullGrade (v (P.ref b))) (v P.cap) ≤ v x := by
    have hz : min (σ (R.row P.cap ⟨P.ref b, hP.mem_below _⟩)) (v P.cap) =
        min (v (P.ref b)) (v P.cap) := (heq _).symm
    rw [← hσ.min_apply_visibilityReplace hvC hgN hz le_rfl]
    calc min (σ (visibilityReplace P.fullGrade P.fullGrade
          (R.row P.cap ⟨P.ref b, hP.mem_below _⟩))) (v P.cap)
        ≤ min (σ (R.row P.cap ⟨x, hP.mem_below x⟩)) (v P.cap) :=
          min_le_min_right _ (hσ.monotone (hcodex b hb))
      _ = min (v x) (v P.cap) := (heq _).symm
      _ ≤ v x := min_le_left _ _
  rw [cut, min_comm, Finset.sup_inf_distrib_right]
  exact Finset.sup_le fun b hb' ↦ hb b hb'

end VaughtConjecture.CappedDonorReading.PrivateReference
