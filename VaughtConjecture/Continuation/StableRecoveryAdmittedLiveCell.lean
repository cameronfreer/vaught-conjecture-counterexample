/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryAdmittedSelfSeed
import VaughtConjecture.Extension.CapRequests

/-!
# A live cell of grade `1`: the admitted layer over the doubled lower layer fails

Roadmap, Layer 3, 3.1, (R6) and 3.3; the gap of
`VaughtConjecture.Continuation.StableRecoveryAdmittedSelfSeed` (types with a live cell of
grade `1`).

**The obstruction** (`Seed.not_cappedLift_fieldLayerOn_left`, for any field layer over the doubled
lower layer on a sub-catalogue of entries satisfying `A`;
`Seed.not_cappedLift_admittedDoubledLower_left` and `Seed.not_isBountiful_admittedDoubledLower` for
the admitted layer).  Let `I` be a seed whose two
coatom types equal a type `T` on two points with a cell of graded index `(univ, 1)`, let `A` be an
admission holding at `⊥`, and suppose that every admitted lawful state not `⊥` on the private copy
where a lawful labelling `s` of `T` is not `⊥` reads the donor copy of a cell `y` of grade `1` at
least as the private copy of a cap `b` of grade `2` (the capped reading, which is what admission in
the bottom class with the marker at the cap gives).  If `s y < s b`, the admitted layer over the
doubled lower layer does not lift capped from the private coatom to the full face at the grade `2`,
at the cap `⊥`, for the prescription `s` on the private copy:

* availability from the private cap reaches a cell of full scope and grade `2` labelled at least
  `s b`; its entry is admitted and not `⊥` where `s` is not (locality), so by recognition the lift
  reads the donor copy of `y` at least `s b`;
* the doubled lower layer forces every labelling lawful below `(univ, 1)` to agree at the two copies
  of a cell of grade `1` (`Scheme.IsDoubling.eq_of_isLawfulBelow`), so the lift reads the donor copy
  of `y` as `s y < s b`.

The raise of the donor copy at a cell of grade `1` is impossible in the doubled lower layer.

**At the coupled-gate type** (`CoupledGatedExtensionCounterexample.not_isBountiful_admittedLayerCP`,
`CoupledGatedExtensionCounterexample.not_isLegalBelowFullGrade_admittedLayerCP`).
The type `P α` of `VaughtConjecture.Extension.CoupledGatedExtensionCounterexample` (a cell `z₁` of
graded index `(univ, 1)` labelled `1`, `z₂` at `(univ, 1)` labelled `⊤`, the full cell `C` labelled
`⊤`).  The (R4) cap requests of its self-seed (`requestsCP`, copied engine
`VaughtConjecture.Extension.CapRequests`): the cap and the marker the private copy of `C`
(`N = 2`, `R = 0`); `Z` the donor copy of the dead cell on the new point; `F` the donor copy of `z₁`
(label `1`), with reference the private copy of `z₁` and offset `1`; `T` the donor copies of `z₂`
and `C`; the bottom class `⊥` exactly at the private copies of the dead cells.  The admission
(`CapRequests.Admits`) satisfies the hypothesis, and the prescription is the row of `C` read as a
labelling, `(⊥, ⊥, 1, ω + 1, ω + 2)`, with `s z₂ = ω + 1 < ω + 2 = s C`.  So **the provision fails
at the private coatom, at the cap `⊥`, for the prescription `(⊥, ⊥, 1, ω + 1, ω + 2)`**, and the
admitted layer over the doubled lower layer is not bountiful there: NO-GO for that design.

This refutes the admitted layer over the doubled lower layer with the marker at the cap; it says
nothing of a lower layer that does not identify the two copies at the grade `1` (the canonical
lower layer of the full catalogue does not), nor of a marker other than the cap (with the marker
the private copy of `z₂`, the reading asks `ω + R ≤ s z₂'` with `R < 2`, which the symmetric value
`ω + 1` meets; argued, not compiled).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

namespace Seed

variable {α : Ordinal.{u}} (I : Seed.{u} α 1) (hLR : I.left = I.right)

/-- **A field layer over the doubled lower layer, on a sub-catalogue of entries satisfying `A`,
cannot raise the donor copy of a cell of grade `1`.** -/
theorem not_cappedLift_fieldLayerOn_left
    {C : Finset (Fin (I.doubledLower hLR).card → Label.{u})}
    (hC : C ⊆ (I.doubledLower hLR).catalogue 2)
    {A : (Fin (I.doubledLower hLR).card → Label.{u}) → Prop}
    (hCA : ∀ e ∈ C, A e) (hCne : C.Nonempty)
    {s : Fin I.left.card → Label.{u}} (hs : I.left.rows.IsLawful s) {b y : Fin I.left.card}
    (hb : I.left.toCellScheme.grade b = 2) (hy : I.left.toCellScheme.grade y = 1)
    (hlt : s y < s b) (hc1 : ∃ c, I.left.toCellScheme.gradedIndex c = ((univ : Finset (Fin 2)), 1))
    (hA : ∀ e, (I.doubledLower hLR).rows.IsLawful e → A e →
      (∀ z, s z ≠ ⊥ → I.privS hLR e z ≠ ⊥) → I.privS hLR e b ≤ I.donS hLR e y) :
    ¬ ((I.doubledLower hLR).fieldLayerOn 2 C (I.not_univ_two_le_doubledLower hLR)).rows.CappedLift
        (X := (univ.erase (Fin.last 2), 2)) (Y := ((univ : Finset (Fin 3)), 2))
          ⟨erase_subset _ _, le_rfl⟩ := by
  classical
  intro hlift
  have hD := I.isDoubling_doubledLower hLR
  have hw₀ : (I.doubledLower hLR).rows.IsLawful (s ∘ I.lowerCell hLR) := hD.isLawful_comp hs
  have hgr (d : Fin (I.doubledLower hLR).card) : (I.doubledLower hLR).toCellScheme.grade d ≤ 2 := by
    induction d using Fin.addCases with
    | left a =>
      rw [Scheme.appendFullCellsScheme_grade_castAdd]
      exact Nat.lt_succ_iff.mp (I.grade_lt a)
    | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
  have hU : ¬ ((univ : Finset (Fin 3)), 2) ≤ (univ.erase (Fin.last 2), 2) :=
    fun h ↦ Finset.notMem_erase _ univ (h.1 (mem_univ (Fin.last 2)))
  have hp := (Scheme.isLawfulBelow_appendFullCells_iff (S := I.doubledLower hLR) (k := 2)
    (M := C.card) (r := fun i ↦ (I.doubledLower hLR).fieldRowOn 2 C (Scheme.entryOn C i))
    (h := I.not_univ_two_le_doubledLower hLR) hU
    (v := Fin.append (s ∘ I.lowerCell hLR) fun _ ↦ ⊥)).mpr (by
      convert hw₀.isLawfulBelow (univ.erase (Fin.last 2), 2) using 1
      funext d
      exact Fin.append_left _ _ _)
  obtain ⟨r, hr, -, hrp⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists _).mp hlift ⊥
    (isSelfVisible_bot _) _ (fun _ ↦ ⊥) hp (CellScheme.Rows.isLawfulBelow_const_bot _)
    (fun _ ↦ by simp)
  -- the lift as a labelling of all cells (every cell lies below `(univ, 2)`)
  have hmem (d : Fin ((I.doubledLower hLR).fieldLayerOn 2 C
      (I.not_univ_two_le_doubledLower hLR)).card) :
      d ∈ ((I.doubledLower hLR).fieldLayerOn 2 C
        (I.not_univ_two_le_doubledLower hLR)).toCellScheme.below
          ((univ : Finset (Fin 3)), 2) := by
    refine ⟨subset_univ _, ?_⟩
    induction d using Fin.addCases with
    | left e => exact (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ e).trans_le (hgr e)
    | right i => exact (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le
  obtain ⟨R, hRdef⟩ : ∃ R : Fin ((I.doubledLower hLR).fieldLayerOn 2 C
      (I.not_univ_two_le_doubledLower hLR)).card → Label.{u}, ∀ d, R d = r ⟨d, hmem d⟩ :=
    ⟨fun d ↦ r ⟨d, hmem d⟩, fun _ ↦ rfl⟩
  have hR : ((I.doubledLower hLR).fieldLayerOn 2 C
      (I.not_univ_two_le_doubledLower hLR)).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2)
        (fun d ↦ R d) := by
    convert hr using 1
    funext d
    exact hRdef d.1
  -- the private copies read the prescription
  have hRL (z : Fin I.left.card) :
      R (Fin.castAdd _ (Fin.castAdd (I.nFull 1) (StageType.faceCell I.restrictFace_left z))) =
        s z := by
    have hz := I.left_mem_belowS (hLR := hLR) z
    have hzF : Fin.castAdd C.card (Fin.castAdd (I.nFull 1)
        (StageType.faceCell I.restrictFace_left z)) ∈ ((I.doubledLower hLR).fieldLayerOn 2 C
          (I.not_univ_two_le_doubledLower hLR)).toCellScheme.below
            (univ.erase (Fin.last 2), 2) := by
      rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
      exact hz
    rw [hRdef]
    refine (hrp ⟨_, hzF⟩).trans ?_
    change Fin.append (s ∘ I.lowerCell hLR) (fun _ ↦ ⊥) (Fin.castAdd C.card
      (Fin.castAdd (I.nFull 1) (StageType.faceCell I.restrictFace_left z))) = s z
    rw [Fin.append_left, Function.comp_apply, lowerCell, Fin.append_left,
      doublingCell_faceCell_left]
  -- availability from the private cap reaches a cell of full scope; recognition there
  obtain ⟨e₀, he₀⟩ := hCne
  obtain ⟨i₀, -⟩ := Scheme.exists_entryOn_eq he₀
  have hgradeLb : ((I.doubledLower hLR).fieldLayerOn 2 C
      (I.not_univ_two_le_doubledLower hLR)).toCellScheme.grade
        (Fin.castAdd _ (Fin.castAdd (I.nFull 1) (StageType.faceCell I.restrictFace_left b))) = 2 :=
    (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
      ((Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
        ((StageType.grade_faceCell _ b).trans hb))
  have hgy (z : Fin I.left.card) (hz : I.left.toCellScheme.grade z = 1) (x) (hx : x =
      Fin.castAdd C.card (Fin.castAdd (I.nFull 1) (StageType.faceCell I.restrictFace_left z)) ∨
      x = Fin.castAdd C.card (Fin.castAdd (I.nFull 1)
        (StageType.faceCell (I.restrictFace_right_left hLR) z))) :
      ((I.doubledLower hLR).fieldLayerOn 2 C
        (I.not_univ_two_le_doubledLower hLR)).toCellScheme.grade x = 1 := by
    rcases hx with rfl | rfl
    · exact (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
        ((Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
          ((StageType.grade_faceCell _ z).trans hz))
    · exact (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
        ((Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
          ((StageType.grade_faceCell _ z).trans hz))
  have hle := CellScheme.Rows.le_of_capped_readers hR (G := Fin.natAdd _ i₀) (hmem _)
    (c := Fin.castAdd _ (Fin.castAdd (I.nFull 1) (StageType.faceCell I.restrictFace_left b)))
    (y₃ := Fin.castAdd _ (Fin.castAdd (I.nFull 1)
      (StageType.faceCell (I.restrictFace_right_left hLR) y)))
    (y₄ := Fin.castAdd _ (Fin.castAdd (I.nFull 1)
      (StageType.faceCell (I.restrictFace_right_left hLR) y)))
    (by
      rw [show ((I.doubledLower hLR).fieldLayerOn 2 C
          (I.not_univ_two_le_doubledLower hLR)).toCellScheme.scope (Fin.natAdd _ i₀) = univ from
        Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i₀]
      exact subset_univ _)
    (hgradeLb.trans (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i₀).symm)
    fun u hu hbu ↦ by
      have hu' : ((I.doubledLower hLR).fieldLayerOn 2 C
          (I.not_univ_two_le_doubledLower hLR)).toCellScheme.gradedIndex u =
            ((univ : Finset (Fin 3)), 2) :=
        hu.trans (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀)
      obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq_fieldLayerOn hu'
      have hcm (d) : d ∈ ((I.doubledLower hLR).fieldLayerOn 2 C
          (I.not_univ_two_le_doubledLower hLR)).toCellScheme.below
            (((I.doubledLower hLR).fieldLayerOn 2 C
              (I.not_univ_two_le_doubledLower hLR)).toCellScheme.gradedIndex (Fin.natAdd _ i)) := by
        rw [CellScheme.mem_below, hu']
        exact hmem d
      have heC : Scheme.entryOn C i ∈ C := Scheme.entryOn_mem i
      have hrow (z : Fin (I.doubledLower hLR).card) (hz) :
          ((I.doubledLower hLR).fieldLayerOn 2 C (I.not_univ_two_le_doubledLower hLR)).rows.row
            (Fin.natAdd _ i) ⟨Fin.castAdd _ z, hz⟩ = Scheme.entryOn C i z :=
        Scheme.fieldLayerOn_row_castAdd i z hz
      have hloc := (CellScheme.Rows.isLawfulBelow_iff_forall.mp hR).2.1 (Fin.natAdd _ i)
        (hmem _)
      have hne (z : Fin I.left.card) (hz : s z ≠ ⊥) : I.privS hLR (Scheme.entryOn C i) z ≠ ⊥ := by
        intro he
        have h := hloc.eq_bot (d := ⟨_, hcm (Fin.castAdd _ (Fin.castAdd (I.nFull 1)
          (StageType.faceCell I.restrictFace_left z)))⟩) ((hrow _ _).trans he)
        simp only at h
        rcases min_eq_bot.mp h with h' | h'
        · exact hz ((hRL z).symm.trans h')
        · have h3 : s b ≤ ⊥ := (hRL b) ▸ (hbu.trans h'.le)
          exact (lt_of_le_of_lt bot_le hlt).ne' (le_bot_iff.mp h3)
      have hread := hA _ (Scheme.mem_catalogue.mp (hC heC)).1 (hCA _ heC) hne
      refine ⟨hcm _, hcm _, hcm _, ?_, ?_, ?_, ?_⟩
      · rw [hgy y hy _ (.inr rfl), hgradeLb]; omega
      · rw [hgy y hy _ (.inr rfl), hgradeLb]; omega
      · rw [hrow, hrow]; exact hread
      · rw [hrow, hrow]; exact hread
  -- the two copies of `y` agree below `(univ, 1)`
  have hsym : R (Fin.castAdd _ (Fin.castAdd (I.nFull 1)
      (StageType.faceCell (I.restrictFace_right_left hLR) y))) =
      R (Fin.castAdd _ (Fin.castAdd (I.nFull 1) (StageType.faceCell I.restrictFace_left y))) := by
    have h1 := hR.mono (X := ((univ : Finset (Fin 3)), 1)) ⟨subset_univ _, by omega⟩
    have h2 := (Scheme.isLawfulBelow_appendFullCells_iff (S := I.doubledLower hLR) (k := 2)
      (M := C.card) (r := fun i ↦ (I.doubledLower hLR).fieldRowOn 2 C (Scheme.entryOn C i))
      (h := I.not_univ_two_le_doubledLower hLR) (X := ((univ : Finset (Fin 3)), 1))
      (fun h ↦ absurd h.2 (by omega)) (v := R)).mp h1
    obtain ⟨c, hc⟩ := hc1
    obtain ⟨i₁, -⟩ := Scheme.exists_fullCell_eq hc
    have hfull : ∀ d ∈ (I.doubledLower hLR).toCellScheme.below ((univ : Finset (Fin 3)), 1),
        ∃ a, (I.doubledLower hLR).toCellScheme.gradedIndex a =
          (univ, (I.doubledLower hLR).toCellScheme.grade d) := by
      intro d hd
      have hpos : 0 < (I.doubledLower hLR).toCellScheme.grade d :=
        ((I.isWellFormed_doubledLower hLR).isWellFormed.gradedIndex_mem d).2.1
      have h1' : (I.doubledLower hLR).toCellScheme.grade d = 1 := le_antisymm hd.2 hpos
      exact ⟨Fin.natAdd _ i₁, (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₁).trans
        (by rw [h1'])⟩
    have hmemL : Fin.castAdd (I.nFull 1) (StageType.faceCell I.restrictFace_left y) ∈
        (I.doubledLower hLR).toCellScheme.below ((univ : Finset (Fin 3)), 1) := by
      rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
      exact ⟨subset_univ _, (StageType.grade_faceCell _ y).trans_le hy.le⟩
    have hmemR : Fin.castAdd (I.nFull 1) (StageType.faceCell (I.restrictFace_right_left hLR) y) ∈
        (I.doubledLower hLR).toCellScheme.below ((univ : Finset (Fin 3)), 1) := by
      rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
      exact ⟨subset_univ _, (StageType.grade_faceCell _ y).trans_le hy.le⟩
    have hπL : I.lowerCell hLR (Fin.castAdd (I.nFull 1)
        (StageType.faceCell I.restrictFace_left y)) = y := by
      rw [lowerCell, Fin.append_left, doublingCell_faceCell_left]
    have hπR : I.lowerCell hLR (Fin.castAdd (I.nFull 1)
        (StageType.faceCell (I.restrictFace_right_left hLR) y)) = y := by
      rw [lowerCell, Fin.append_left, doublingCell_faceCell_right]
    exact hD.eq_of_isLawfulBelow (w := fun d ↦ R (Fin.castAdd _ d)) h2 hfull hmemR hmemL
      (hπR.trans hπL.symm)
  have : s b ≤ s y := by
    rw [← hRL b, ← hRL y, ← hsym]
    exact hle.1
  exact absurd this (not_le.mpr hlt)

/-- **The admitted layer over the doubled lower layer cannot raise the donor copy of a cell of
grade `1`**: the field layer on the admitted catalogue. -/
theorem not_cappedLift_admittedDoubledLower_left
    {A : (Fin (I.doubledLower hLR).card → Label.{u}) → Prop} (hA0 : A fun _ ↦ ⊥)
    {s : Fin I.left.card → Label.{u}} (hs : I.left.rows.IsLawful s) {b y : Fin I.left.card}
    (hb : I.left.toCellScheme.grade b = 2) (hy : I.left.toCellScheme.grade y = 1)
    (hlt : s y < s b) (hc1 : ∃ c, I.left.toCellScheme.gradedIndex c = ((univ : Finset (Fin 2)), 1))
    (hA : ∀ e, (I.doubledLower hLR).rows.IsLawful e → A e →
      (∀ z, s z ≠ ⊥ → I.privS hLR e z ≠ ⊥) → I.privS hLR e b ≤ I.donS hLR e y) :
    ¬ ((I.doubledLower hLR).admittedFieldLayer 2 A
      (I.not_univ_two_le_doubledLower hLR)).rows.CappedLift
        (X := (univ.erase (Fin.last 2), 2)) (Y := ((univ : Finset (Fin 3)), 2))
          ⟨erase_subset _ _, le_rfl⟩ :=
  I.not_cappedLift_fieldLayerOn_left hLR Scheme.admittedCatalogue_subset
    (fun _ he ↦ (Scheme.mem_admittedCatalogue.mp he).2)
    ⟨_, Scheme.bot_mem_admittedCatalogue hA0⟩ hs hb hy hlt hc1 hA

/-- **Not bountiful**, hence not legal below the full grade. -/
theorem not_isBountiful_admittedDoubledLower
    {A : (Fin (I.doubledLower hLR).card → Label.{u}) → Prop} (hA0 : A fun _ ↦ ⊥)
    {s : Fin I.left.card → Label.{u}} (hs : I.left.rows.IsLawful s) {b y : Fin I.left.card}
    (hb : I.left.toCellScheme.grade b = 2) (hy : I.left.toCellScheme.grade y = 1)
    (hlt : s y < s b) (hc1 : ∃ c, I.left.toCellScheme.gradedIndex c = ((univ : Finset (Fin 2)), 1))
    (hA : ∀ e, (I.doubledLower hLR).rows.IsLawful e → A e →
      (∀ z, s z ≠ ⊥ → I.privS hLR e z ≠ ⊥) → I.privS hLR e b ≤ I.donS hLR e y) :
    ¬ ((I.doubledLower hLR).admittedFieldLayer 2 A
      (I.not_univ_two_le_doubledLower hLR)).rows.IsBountiful := by
  intro hB
  refine I.not_cappedLift_admittedDoubledLower_left hLR hA0 hs hb hy hlt hc1 hA (hB ?_ ?_ _)
  · refine ⟨I.erase_last_mem_faces, two_pos, ?_⟩
    rw [card_erase_of_mem (mem_univ _)]
    simp
  · exact ⟨I.amalgam.univ_mem_faces, two_pos, by simp⟩

/-- A cell of `T` reading itself at `⊥`: every lawful labelling of the doubled lower layer is `⊥`
at its private copy. -/
theorem eq_bot_privS_of_row_self {z : Fin I.left.card}
    (hz : I.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    {e : Fin (I.doubledLower hLR).card → Label.{u}} (he : (I.doubledLower hLR).rows.IsLawful e) :
    I.privS hLR e z = ⊥ := by
  have hD := I.isDoubling_doubledLower hLR
  set x := Fin.castAdd (I.nFull 1) (StageType.faceCell I.restrictFace_left z)
  have hrow : (I.doubledLower hLR).rows.row x ⟨x, CellScheme.mem_below_gradedIndex _ x⟩ = ⊥ := by
    rw [← Scheme.rowAt_of_mem, hD.rowAt_eq x x (CellScheme.mem_below_gradedIndex _ x)]
    have hπ : I.lowerCell hLR x = z := by
      rw [lowerCell, Fin.append_left, doublingCell_faceCell_left]
    rw [hπ, Scheme.rowAt_of_mem (CellScheme.mem_below_gradedIndex _ z)]
    exact hz
  have h := (he.locality x).eq_bot (d := ⟨x, CellScheme.mem_below_gradedIndex _ x⟩) hrow
  change e x = ⊥
  simpa using h

end Seed

/-! ### The coupled-gate type -/

namespace CoupledGatedExtensionCounterexample

variable (α : Ordinal.{u}) (hα : 1 < α)

/-- The face `{0}` of the coupled-gate type. -/
theorem mem_faces_castSuccEmb :
    univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∈ (P α hα).toCellScheme.faces := by
  change _ ∈ Geometry.intervalPlan univ
  decide

/-- The seed of the coupled-gate type with itself, along its face `{0}`. -/
noncomputable abbrev seedCP : Seed.{u} α 1 :=
  Seed.ofCoatoms (isLegal_P α hα) (isLegal_P α hα)
    (restrictFace_of_mem _ _ (mem_faces_castSuccEmb α hα))
    (restrictFace_of_mem _ _ (mem_faces_castSuccEmb α hα))

/-- The private copy of a cell, in the doubled lower layer. -/
noncomputable abbrev leftCP (z : Fin 5) : Fin ((seedCP α hα).doubledLower rfl).card :=
  Fin.castAdd _ (StageType.faceCell (seedCP α hα).restrictFace_left z)

/-- The donor copy of a cell, in the doubled lower layer. -/
noncomputable abbrev rightCP (z : Fin 5) : Fin ((seedCP α hα).doubledLower rfl).card :=
  Fin.castAdd _ (StageType.faceCell ((seedCP α hα).restrictFace_right_left rfl) z)

/-- **The (R4) cap requests of the self-seed of the coupled-gate type**: the cap and the marker the
private copy of the full cell `4` (`N = 2`, `R = 0`); `Z` the donor copy of the dead cell `1`; `F`
the donor copy of the live cell `z₁ = 2` (labelled `1`), with reference the private copy of `z₁`
and offset `1`; `T` the donor copies of `z₂ = 3` and of the full cell. -/
noncomputable def requestsCP : CapRequests (Fin ((seedCP α hα).doubledLower rfl).card) where
  cap := leftCP α hα 4
  N := 2
  R := 0
  R_lt_N := by omega
  Z := {rightCP α hα 1}
  F := {rightCP α hα 2}
  T := {rightCP α hα 3, rightCP α hα 4}
  ref _ := leftCP α hα 2
  off _ := 1
  marker := leftCP α hα 4

/-- The private copies: the cells of the bottom class. -/
def classCellsCP : Set (Fin ((seedCP α hα).doubledLower rfl).card) := Set.range (leftCP α hα)

/-- The bottom class: `⊥` exactly at the private copies of the dead cells. -/
def classBotCP : Set (Fin ((seedCP α hα).doubledLower rfl).card) :=
  {leftCP α hα 0, leftCP α hα 1}

private theorem lowerCell_leftCP (z : Fin 5) :
    (seedCP α hα).lowerCell rfl (leftCP α hα z) = z := by
  change Fin.append ((seedCP α hα).doublingCell rfl) _ (Fin.castAdd _ _) = z
  rw [Fin.append_left]
  exact (seedCP α hα).doublingCell_faceCell_left rfl _

private theorem omegaAdd_one_lt_two : omegaAdd.{u} 1 < omegaAdd 2 := by
  unfold omegaAdd
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
    ((add_lt_add_iff_left _).mpr
      ((Nat.cast_lt (α := Ordinal.{u})).mpr (by decide : (1 : ℕ) < 2))))

/-- **The provision fails at the coupled-gate type**: the admitted layer over the doubled lower
layer of its self-seed, for the (R4) cap requests with the marker at the cap, does not lift capped
from the private coatom at the cap `⊥` (prescription: the row of the full cell, `⊥, ⊥, 1, ω + 1,
ω + 2`, on the private copy), so it is not bountiful. -/
theorem not_isBountiful_admittedLayerCP :
    ¬ (((seedCP α hα).doubledLower rfl).admittedFieldLayer 2
      ((requestsCP α hα).Admits (classCellsCP α hα) (classBotCP α hα))
        ((seedCP α hα).not_univ_two_le_doubledLower rfl)).rows.IsBountiful := by
  have hg4 : (P α hα).toCellScheme.gradedIndex (4 : Fin 5) = ((univ : Finset (Fin 2)), 2) := rfl
  have hs := Scheme.isLawful_rowAt (isLegal_P α hα).isConsistent hg4
  have hrow (z : Fin 5) : (P α hα).rowAt (4 : Fin 5) z = code z := by
    rw [Scheme.rowAt_of_mem (show z ∈ (P α hα).toCellScheme.below
      ((P α hα).toCellScheme.gradedIndex (4 : Fin 5)) by
        rw [hg4]; exact ⟨subset_univ _, (P α hα).grade_le z⟩)]
    fin_cases z <;> rfl
  refine Seed.not_isBountiful_admittedDoubledLower (seedCP α hα) rfl
    (CapRequests.isCorrect_bot _).admits hs (b := (4 : Fin 5)) (y := (3 : Fin 5)) rfl rfl
    (by rw [hrow, hrow]; exact omegaAdd_one_lt_two) ⟨(2 : Fin 5), rfl⟩ ?_
  intro e he hadm hne
  -- the bottom class
  have hcl : InBottomClass (classCellsCP α hα) (classBotCP α hα) e := by
    rintro _ ⟨z, rfl⟩
    have hinj (z' : Fin 5) (h : leftCP α hα z = leftCP α hα z') : z = z' := by
      have := congrArg ((seedCP α hα).lowerCell rfl) h
      rwa [lowerCell_leftCP, lowerCell_leftCP] at this
    revert hinj
    fin_cases z
    · intro _
      exact ⟨fun _ ↦ Or.inl rfl, fun _ ↦ (seedCP α hα).eq_bot_privS_of_row_self rfl rfl he⟩
    · intro _
      exact ⟨fun _ ↦ Or.inr rfl, fun _ ↦ (seedCP α hα).eq_bot_privS_of_row_self rfl rfl he⟩
    all_goals
      intro hinj
      refine ⟨fun h ↦ absurd h (hne _ ?_), fun h ↦ ?_⟩
      · rw [hrow]
        exact WithBot.coe_ne_bot
      · rcases h with h | h <;> exact absurd (hinj _ h) (by decide)
  have hcorr := hadm hcl
  have hvis : IsSelfVisible 2 (e (leftCP α hα 4)) := by
    have h := he.orderly (leftCP α hα 4)
    have hgr : ((seedCP α hα).doubledLower rfl).toCellScheme.grade (leftCP α hα 4) = 2 :=
      (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
        (StageType.grade_faceCell (seedCP α hα).restrictFace_left
          ((4 : Fin 5) : Fin (seedCP α hα).left.card))
    exact hgr ▸ h
  have h3 := hcorr.markerValue_le (rightCP α hα 3) (Or.inl rfl)
  rw [CapRequests.markerValue_of_marker_eq_cap rfl hvis] at h3
  exact h3.trans (min_le_left _ _)

/-- **No admitted completion over the doubled lower layer at the coupled-gate type.** -/
theorem not_isLegalBelowFullGrade_admittedLayerCP :
    ¬ (((seedCP α hα).doubledLower rfl).admittedFieldLayer 2
      ((requestsCP α hα).Admits (classCellsCP α hα) (classBotCP α hα))
        ((seedCP α hα).not_univ_two_le_doubledLower rfl)).IsLegalBelowFullGrade :=
  fun h ↦ not_isBountiful_admittedLayerCP α hα h.isBountiful

end CoupledGatedExtensionCounterexample

end VaughtConjecture
