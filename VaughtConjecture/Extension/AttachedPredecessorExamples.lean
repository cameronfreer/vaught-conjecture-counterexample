/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AttachedPredecessor
import VaughtConjecture.Geometry.IntervalPlan

/-!
# An attached predecessor with the bottom rows

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the attached predecessor); the attached
predecessor of `VaughtConjecture.Extension.AttachedPredecessor`.

**Non-vacuity** (`AttachedPredecessorExamples.nonempty_attachedPredecessor`).  For every stage `α`
and every `n`, some stage type `P` on `n` points and some donor `d` on one point have an attached
predecessor over the empty root.  The scheme (`AttachedPredecessorExamples.botScheme n`) lives on
`n + 1` points with the interval plan (`Geometry.intervalPlan`), one cell for each graded face not
above `(univ, n)`, and the bottom rows (`CellScheme.Rows.bot`), which are consistent and
bountiful; every cell of grade `n` is muted.  `P` and `d` are its restrictions along
`Fin.castSuccEmb` and along the last point, with every label `⊥`.  This shows only that the
fields of `StageType.AttachedPredecessor` are consistent with each other; at the private types
that a model acquires, with ordinal labels, no attached predecessor is constructed.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`, beside
`VaughtConjecture.Extension.AttachedPredecessor`.
-/

universe u

namespace VaughtConjecture.AttachedPredecessorExamples

open Finset Label

variable (n : ℕ)

open Classical in
/-- The graded faces of the interval plan on `n + 1` points that are not above `(univ, n)`. -/
noncomputable def faces : Finset (Finset (Fin (n + 1)) × ℕ) :=
  ((Geometry.intervalPlan univ) ×ˢ range (n + 2)).filter fun X ↦
    0 < X.2 ∧ X.2 ≤ #X.1 ∧ ¬ ((univ : Finset (Fin (n + 1))), n) ≤ X

/-- The cell of each such graded face. -/
noncomputable def cellFace (i : Fin #(faces n)) : Finset (Fin (n + 1)) × ℕ :=
  ((faces n).equivFin.symm i).1

/-- The face of a cell is one of the graded faces. -/
theorem cellFace_mem (i : Fin #(faces n)) : cellFace n i ∈ faces n :=
  ((faces n).equivFin.symm i).2

/-- The cell scheme: one cell per graded face of the interval plan not above `(univ, n)`. -/
noncomputable def cells : CellScheme (Fin #(faces n)) (Fin (n + 1)) :=
  ⟨univ, Geometry.intervalPlan univ, fun i ↦ (cellFace n i).1, fun i ↦ (cellFace n i).2⟩

/-- The scheme with the bottom rows. -/
noncomputable def botScheme : Scheme.{u} (n + 1) :=
  ⟨#(faces n), cells n, CellScheme.Rows.bot _⟩

/-- Membership in the graded faces not above `(univ, n)`. -/
theorem mem_faces {X : Finset (Fin (n + 1)) × ℕ} :
    X ∈ faces n ↔ X.1 ∈ Geometry.intervalPlan univ ∧ 0 < X.2 ∧ X.2 ≤ #X.1 ∧
      ¬ ((univ : Finset (Fin (n + 1))), n) ≤ X := by
  classical
  simp only [faces, mem_filter, mem_product, mem_range]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, ?_⟩, h2, h3, h4⟩
    have := card_le_univ X.1
    simp at this
    omega

/-- The scheme is well formed. -/
theorem isWellFormed_botScheme : (botScheme.{u} n).IsWellFormed where
  ground_eq := rfl
  isWellFormed := by
    refine ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun i ↦ ?_⟩
    obtain ⟨h1, h2, h3, -⟩ := (mem_faces n).mp (cellFace_mem n i)
    exact ⟨h1, h2, h3⟩

/-- The stage type with every label `⊥`. -/
noncomputable def botType (α : Ordinal.{u}) : StageType.{u} α (n + 1) where
  toScheme := botScheme n
  label _ := ⊥
  isWellFormed := isWellFormed_botScheme n
  isCoded _ _ := by simp [botScheme, CellScheme.Rows.bot]
  isLawful := CellScheme.Rows.isLawful_const_bot
  atStage _ := atStage_bot

/-- The private face is an interval. -/
theorem castSuccEmb_mem : univ.map (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) ∈
    Geometry.intervalPlan (univ : Finset (Fin (n + 1))) := by
  refine Geometry.mem_intervalPlan.mpr ⟨subset_univ _, fun x hx y hy z _ hxz hzy ↦ ?_⟩
  obtain ⟨y, -, rfl⟩ := mem_map.mp hy
  have hz : (z : ℕ) < n := lt_of_le_of_lt hzy (by simp)
  exact mem_map.mpr ⟨⟨z, hz⟩, mem_univ _, Fin.ext rfl⟩

/-- The empty root. -/
def emptyRoot : Fin 0 ↪ Fin n := ⟨Fin.elim0, fun x ↦ x.elim0⟩

/-- The last point is an interval. -/
theorem extendByLast_mem : univ.map (extendByLast (emptyRoot n)) ∈
    Geometry.intervalPlan (univ : Finset (Fin (n + 1))) := by
  refine Geometry.mem_intervalPlan.mpr ⟨subset_univ _, fun x hx y hy z _ hxz hzy ↦ ?_⟩
  obtain ⟨x, -, rfl⟩ := mem_map.mp hx
  obtain ⟨y, -, rfl⟩ := mem_map.mp hy
  obtain rfl : x = Fin.last 0 := Fin.ext (by have := x.isLt; simp)
  obtain rfl : y = Fin.last 0 := Fin.ext (by have := y.isLt; simp)
  rw [extendByLast_last] at hxz hzy
  exact mem_map.mpr ⟨Fin.last 0, mem_univ _, by rw [extendByLast_last]; exact le_antisymm hxz hzy⟩

/-- The private type: the restriction along `Fin.castSuccEmb`. -/
noncomputable def privateType (α : Ordinal.{u}) : StageType.{u} α n :=
  (botType n α).comap Fin.castSuccEmb (castSuccEmb_mem n)

/-- The donor: the restriction along the last point. -/
noncomputable def donor (α : Ordinal.{u}) : StageType.{u} α (0 + 1) :=
  (botType n α).comap (extendByLast (emptyRoot n)) (extendByLast_mem n)

/-- **An attached predecessor exists** for the private type and the donor with every label `⊥`:
the scheme with the bottom rows. -/
noncomputable def attachedPredecessor (α : Ordinal.{u}) :
    (privateType n α).AttachedPredecessor (emptyRoot n) (donor n α) where
  scheme := botScheme n
  isWellFormed := isWellFormed_botScheme n
  isCoded := (botType n α).isCoded
  isConsistent := CellScheme.Rows.isConsistent_bot
  mem_faces_castSuccEmb := castSuccEmb_mem n
  comap_castSuccEmb := rfl
  mem_faces_extendByLast := extendByLast_mem n
  comap_extendByLast := rfl
  mute _ _ _ := rfl
  grade_lt_of_scope_eq c hc := by
    obtain ⟨-, -, h3, h4⟩ := (mem_faces n).mp (cellFace_mem n c)
    have hs : (cellFace n c).1 = univ := hc
    by_contra hlt
    exact h4 ⟨hs ▸ Subset.rfl, not_lt.mp hlt⟩
  exists_gradedIndex_eq X hX hlow := by
    obtain ⟨i, hi⟩ := (faces n).equivFin.symm.surjective ⟨X, (mem_faces n).mpr ⟨hX.1, hX.2.1,
      hX.2.2, fun h ↦ by
        rcases hlow with h1 | h2
        · exact h1 (univ_subset_iff.mp h.1)
        · exact (not_le.mpr h2) h.2⟩⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  cappedLift _ _ hX hY h _ := CellScheme.Rows.isBountiful_bot hX hY h
  label _ := ⊥
  isLawful_label := CellScheme.Rows.isLawful_const_bot
  atStage_label _ := atStage_bot
  label_castSuccEmb _ _ _ := rfl
  label_extendByLast _ _ _ := rfl

/-- **Non-vacuity of the attached predecessor**: for every stage and every `n`, some private type
on `n` points and some donor over the empty root have an attached predecessor. -/
theorem nonempty_attachedPredecessor (α : Ordinal.{u}) :
    ∃ (P : StageType.{u} α n) (d : StageType.{u} α (0 + 1)),
      Nonempty (P.AttachedPredecessor (emptyRoot n) d) :=
  ⟨_, _, ⟨attachedPredecessor n α⟩⟩

end VaughtConjecture.AttachedPredecessorExamples
