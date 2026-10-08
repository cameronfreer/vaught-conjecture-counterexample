/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapMixedEntry
import VaughtConjecture.Continuation.SourceGapDoubledAmalgam
import VaughtConjecture.Extension.SmallArityOne

/-!
# The mixed entry at the seed of the input with itself

Roadmap, Layer 3 ((R2) of the table of 3.4); the obstruction of
`VaughtConjecture.Continuation.SourceGapMixedEntry`, at the seed itself.

The obstruction `MixedEntry.not_exists_reading_markedLayer` is stated over the explicit amalgam
`MixedEntry.A`.  Here the seed of `SeparationObstruction.T α` with itself
(`MixedSeed.I α = Seed.ofCoatoms …`, whose two coatom types are equal) is shown to be a site of
the mixed labelling (`MixedSeed.isMixedSite`, compiled in this repository) through the cell map of
the doubling (`Seed.doublingCell`): the context cells are the copies of `y`, `z`, `o`, `r` along
the first coatom, the donor cells the copies of `z`, `o`, `r` along the second (the copies of `y`
coincide).  So the obstruction holds at the seed itself, with no identification argued:

* `MixedSeed.not_exists_reading_fieldLayerOne`: the canonical completion at the arity one
  (`Seed.fieldLayerOne`) of this seed does not read `o'` at its tops;
* `MixedSeed.not_exists_reading_markedLayer`: neither does any leaf-and-marked layer at grade `2`,
  with any marks marked-closed for its cap, over any layer of cells of full scope and grade `1`
  over the amalgam of this seed.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

namespace MixedSeed

open Finset Label StageType SeparationObstruction

/-- The kinds of the rows of the input. -/
def rowKindT : Fin 5 → Fin 5 → Fin 3 :=
  ![![1, 0, 1, 0, 0], fun _ ↦ 0, ![1, 0, 1, 0, 0], ![2, 0, 2, 2, 1], ![1, 0, 1, 1, 2]]

theorem rowValue_eq (s d : Fin 5) :
    SeparationObstruction.rowValue.{u} s d = MixedEntry.kindLabel (rowKindT s d) := by
  fin_cases s <;> fin_cases d <;> rfl

/-- The row of the input at `c` read at `d`. -/
theorem rowAt_T (α : Ordinal.{u}) (c d : Fin 5) :
    (T α).rowAt c d =
      MixedEntry.kindLabel (if cells.gradedIndex d ≤ cells.gradedIndex c then rowKindT c d else 0)
    := by
  by_cases h : cells.gradedIndex d ≤ cells.gradedIndex c
  · calc (T α).rowAt c d = SeparationObstruction.rowValue c d :=
          Scheme.rowAt_of_mem (S := (T α).toScheme) h
      _ = _ := by rw [ite_eq_left h]; exact rowValue_eq c d
  · calc (T α).rowAt c d = ⊥ := Scheme.rowAt_of_notMem (S := (T α).toScheme) h
      _ = _ := by rw [ite_eq_right h]; rfl

variable (α : Ordinal.{u})

theorem face_mem : univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∈ (T α).toCellScheme.faces := by
  -- the faces of the input are the interval plan
  change _ ∈ Geometry.intervalPlan univ
  decide

/-- The face of the input on `{0}`. -/
noncomputable def P : StageType.{u} α 1 := (T α).comap _ (face_mem α)

theorem restrictFace_P : restrictFace Fin.castSuccEmb (T α) = some (P α) :=
  restrictFace_of_mem _ _ (face_mem α)

/-- **The seed of the input with itself.** -/
noncomputable def I : Seed.{u} α 1 :=
  Seed.ofCoatoms (isLegal_T α) (isLegal_T α) (restrictFace_P α) (restrictFace_P α)

theorem hLR : (I α).left = (I α).right := rfl

/-- The copy of a cell of the input along the first coatom. -/
noncomputable abbrev lc (w : Fin 5) : Fin (I α).amalgam.card :=
  faceCell (I α).restrictFace_left (cellT α w)

/-- The copy of a cell of the input along the second coatom. -/
noncomputable abbrev rc (w : Fin 5) : Fin (I α).amalgam.card :=
  faceCell ((I α).restrictFace_right_left (hLR α)) (cellT α w)

theorem lc_injective : Function.Injective (lc α) := fun _ _ h ↦
  (I α).amalgam.toScheme.faceCell_injective _ h

theorem rc_injective : Function.Injective (rc α) := fun _ _ h ↦
  (I α).amalgam.toScheme.faceCell_injective _ h

/-- The two copies of `y` coincide. -/
theorem lc_zero : lc α 0 = rc α 0 := by
  refine ((I α).faceCell_right_eq_left (hLR α) ?_).symm
  simp only [Scheme.visibleCells, mem_filter, mem_univ, true_and]
  rw [show (I α).amalgam.toCellScheme.scope (lc α 0) = (cells.scope 0).map (Coatom.left 1) from
    StageType.scope_faceCell _ _]
  decide

variable {α}

theorem gradedIndex_lc (w : Fin 5) : (I α).amalgam.toCellScheme.gradedIndex (lc α w) =
    ((cells.scope w).map (Coatom.left 1), cells.grade w) :=
  Prod.ext (StageType.scope_faceCell (I α).restrictFace_left (cellT α w))
    (StageType.grade_faceCell (I α).restrictFace_left (cellT α w))

theorem gradedIndex_rc (w : Fin 5) : (I α).amalgam.toCellScheme.gradedIndex (rc α w) =
    ((cells.scope w).map (Coatom.right 1), cells.grade w) :=
  Prod.ext (StageType.scope_faceCell ((I α).restrictFace_right_left (hLR α)) (cellT α w))
    (StageType.grade_faceCell ((I α).restrictFace_right_left (hLR α)) (cellT α w))

/-- A cell below a copy along the first coatom is the copy of its cell. -/
theorem eq_lc_of_mem_below {w : Fin 5} {d : Fin (I α).amalgam.card}
    (hd : d ∈ (I α).amalgam.toCellScheme.below ((I α).amalgam.toCellScheme.gradedIndex (lc α w))) :
    lc α ((I α).doublingCell (hLR α) d) = d := by
  refine (I α).faceCell_left_of_subset (hLR α) (hd.1.trans ?_)
  rw [gradedIndex_lc]
  exact map_subset_map.mpr (subset_univ _)

/-- A cell below a copy along the second coatom is the copy of its cell. -/
theorem eq_rc_of_mem_below {w : Fin 5} {d : Fin (I α).amalgam.card}
    (hd : d ∈ (I α).amalgam.toCellScheme.below ((I α).amalgam.toCellScheme.gradedIndex (rc α w))) :
    rc α ((I α).doublingCell (hLR α) d) = d := by
  refine (I α).faceCell_right_of_subset (hLR α) (hd.1.trans ?_)
  rw [gradedIndex_rc]
  exact map_subset_map.mpr (subset_univ _)

/-- The rows of the amalgam at copies are the rows of the input. -/
theorem rowAt_copy {a d : Fin (I α).amalgam.card}
    (hd : d ∈ (I α).amalgam.toCellScheme.below ((I α).amalgam.toCellScheme.gradedIndex a)) :
    (I α).amalgam.rowAt a d =
      (T α).rowAt ((I α).doublingCell (hLR α) a) ((I α).doublingCell (hLR α) d) :=
  ((I α).isDoubling_amalgam (hLR α)).rowAt_eq a d hd

/-- The context rows read exactly `y`, `z`, `o`, `r`. -/
private theorem key_context : ∀ w₀ ∈ ({3, 4} : Finset (Fin 5)), ∀ w : Fin 5,
    (if cells.gradedIndex w ≤ cells.gradedIndex w₀ then rowKindT w₀ w else 0) ≠ 0 ↔
      w = 0 ∨ w = 2 ∨ w = 3 ∨ w = 4 := by decide

/-- The cells of grade `2` of the input are `o` and `r`. -/
private theorem key_grade : ∀ w : Fin 5, cells.grade w = 2 ↔ w = 3 ∨ w = 4 := by decide

/-- Every cell of the input lies below `o` and `r`. -/
private theorem key_below : ∀ w w₀ : Fin 5, w₀ = 3 ∨ w₀ = 4 →
    w = 0 ∨ w = 2 ∨ w = 3 ∨ w = 4 → cells.gradedIndex w ≤ cells.gradedIndex w₀ := by decide

/-- The cells of full scope of the input. -/
private theorem key_scope : ∀ w : Fin 5, w = 3 ∨ w = 4 → cells.scope w = univ := by decide

theorem lc_mem_below {w w₀ : Fin 5} (hw₀ : w₀ = 3 ∨ w₀ = 4) (hw : w = 0 ∨ w = 2 ∨ w = 3 ∨ w = 4) :
    lc α w ∈ (I α).amalgam.toCellScheme.below
      ((I α).amalgam.toCellScheme.gradedIndex (lc α w₀)) := by
  have h := key_below w w₀ hw₀ hw
  rw [CellScheme.mem_below, gradedIndex_lc, gradedIndex_lc]
  exact ⟨map_subset_map.mpr h.1, h.2⟩

theorem rc_mem_below {w w₀ : Fin 5} (hw₀ : w₀ = 3 ∨ w₀ = 4) (hw : w = 0 ∨ w = 2 ∨ w = 3 ∨ w = 4) :
    rc α w ∈ (I α).amalgam.toCellScheme.below
      ((I α).amalgam.toCellScheme.gradedIndex (rc α w₀)) := by
  have h := key_below w w₀ hw₀ hw
  rw [CellScheme.mem_below, gradedIndex_rc, gradedIndex_rc]
  exact ⟨map_subset_map.mpr h.1, h.2⟩

theorem doublingCell_lc (w : Fin 5) : (I α).doublingCell (hLR α) (lc α w) = w :=
  (I α).doublingCell_faceCell_left (hLR α) (cellT α w)

theorem doublingCell_rc (w : Fin 5) : (I α).doublingCell (hLR α) (rc α w) = w :=
  (I α).doublingCell_faceCell_right (hLR α) (cellT α w)

/-- **The seed of the input with itself is a site of the mixed labelling.** -/
theorem isMixedSite : (I α).amalgam.toScheme.IsMixedSite (lc α 0) (lc α 2) (lc α 3) (lc α 4)
    (rc α 2) (rc α 3) (rc α 4) := by
  have hD := (I α).isDoubling_amalgam (hLR α)
  refine ⟨fun d ↦ ?_, fun d ↦ ?_, ?_, ?_, fun c hc d ↦ ?_, fun c hc d ↦ ?_, ?_, ?_, ?_, ?_,
    fun s t hs ht ↦ ?_⟩
  · have := (I α).grade_lt d
    omega
  · constructor
    · intro h2
      have hg : cells.grade ((I α).doublingCell (hLR α) d) = 2 := (hD.grade_eq d).trans h2
      rcases (key_grade _).mp hg with h | h <;>
        rcases (I α).scope_eq_map (hLR α) d with ⟨hl, -⟩ | ⟨hr, -⟩
      · have he := (I α).faceCell_left_doublingCell (hLR α) hl
        rw [h] at he; exact .inl he.symm
      · have he := (I α).faceCell_right_doublingCell (hLR α) hr
        rw [h] at he; exact .inr (.inr (.inl he.symm))
      · have he := (I α).faceCell_left_doublingCell (hLR α) hl
        rw [h] at he; exact .inr (.inl he.symm)
      · have he := (I α).faceCell_right_doublingCell (hLR α) hr
        rw [h] at he; exact .inr (.inr (.inr he.symm))
    · rintro (rfl | rfl | rfl | rfl)
      exacts [StageType.grade_faceCell _ _, StageType.grade_faceCell _ _,
        StageType.grade_faceCell _ _, StageType.grade_faceCell _ _]
  · exact (StageType.grade_faceCell _ _).le
  · exact (StageType.grade_faceCell _ _).le
  · obtain ⟨w₀, hw₀, rfl⟩ : ∃ w₀ : Fin 5, (w₀ = 3 ∨ w₀ = 4) ∧ lc α w₀ = c := by
      rcases hc with rfl | rfl
      exacts [⟨3, .inl rfl, rfl⟩, ⟨4, .inr rfl, rfl⟩]
    by_cases hd : d ∈ (I α).amalgam.toCellScheme.below
        ((I α).amalgam.toCellScheme.gradedIndex (lc α w₀))
    · have he := eq_lc_of_mem_below hd
      rw [rowAt_copy hd, doublingCell_lc,
        show (T α).rowAt w₀ ((I α).doublingCell (hLR α) d) = _ from rowAt_T α w₀ _,
        MixedEntry.kindLabel_ne_bot_iff]
      refine (key_context w₀ (by rcases hw₀ with rfl | rfl <;> decide) _).trans ⟨?_, ?_⟩
      · rintro (h | h | h | h)
        · exact .inl (he.symm.trans (congrArg (lc α) h))
        · exact .inr (.inl (he.symm.trans (congrArg (lc α) h)))
        · exact .inr (.inr (.inl (he.symm.trans (congrArg (lc α) h))))
        · exact .inr (.inr (.inr (he.symm.trans (congrArg (lc α) h))))
      · rintro (h | h | h | h) <;> rw [h]
        exacts [.inl (doublingCell_lc 0), .inr (.inl (doublingCell_lc 2)),
          .inr (.inr (.inl (doublingCell_lc 3))), .inr (.inr (.inr (doublingCell_lc 4)))]
    · rw [Scheme.rowAt_of_notMem hd]
      simp only [ne_eq, not_true_eq_false, false_iff]
      rintro (h | h | h | h) <;> subst h
      exacts [hd (lc_mem_below hw₀ (.inl rfl)), hd (lc_mem_below hw₀ (.inr (.inl rfl))),
        hd (lc_mem_below hw₀ (.inr (.inr (.inl rfl)))),
        hd (lc_mem_below hw₀ (.inr (.inr (.inr rfl))))]
  · obtain ⟨w₀, hw₀, rfl⟩ : ∃ w₀ : Fin 5, (w₀ = 3 ∨ w₀ = 4) ∧ rc α w₀ = c := by
      rcases hc with rfl | rfl
      exacts [⟨3, .inl rfl, rfl⟩, ⟨4, .inr rfl, rfl⟩]
    rw [lc_zero]
    by_cases hd : d ∈ (I α).amalgam.toCellScheme.below
        ((I α).amalgam.toCellScheme.gradedIndex (rc α w₀))
    · have he := eq_rc_of_mem_below hd
      rw [rowAt_copy hd, doublingCell_rc,
        show (T α).rowAt w₀ ((I α).doublingCell (hLR α) d) = _ from rowAt_T α w₀ _,
        MixedEntry.kindLabel_ne_bot_iff]
      refine (key_context w₀ (by rcases hw₀ with rfl | rfl <;> decide) _).trans ⟨?_, ?_⟩
      · rintro (h | h | h | h)
        · exact .inl (he.symm.trans (congrArg (rc α) h))
        · exact .inr (.inl (he.symm.trans (congrArg (rc α) h)))
        · exact .inr (.inr (.inl (he.symm.trans (congrArg (rc α) h))))
        · exact .inr (.inr (.inr (he.symm.trans (congrArg (rc α) h))))
      · rintro (h | h | h | h) <;> rw [h]
        exacts [.inl (doublingCell_rc 0), .inr (.inl (doublingCell_rc 2)),
          .inr (.inr (.inl (doublingCell_rc 3))), .inr (.inr (.inr (doublingCell_rc 4)))]
    · rw [Scheme.rowAt_of_notMem hd]
      simp only [ne_eq, not_true_eq_false, false_iff]
      rintro (h | h | h | h) <;> subst h
      exacts [hd (rc_mem_below hw₀ (.inl rfl)), hd (rc_mem_below hw₀ (.inr (.inl rfl))),
        hd (rc_mem_below hw₀ (.inr (.inr (.inl rfl)))),
        hd (rc_mem_below hw₀ (.inr (.inr (.inr rfl))))]
  · rw [rowAt_copy (lc_mem_below (.inl rfl) (.inr (.inr (.inl rfl)))),
      rowAt_copy (lc_mem_below (.inl rfl) (.inl rfl)), doublingCell_lc, doublingCell_lc,
      rowAt_T, rowAt_T]
    exact le_of_eq (congrArg _ (by decide))
  · rw [rowAt_copy (lc_mem_below (.inl rfl) (.inr (.inr (.inl rfl)))),
      rowAt_copy (lc_mem_below (.inl rfl) (.inr (.inl rfl))), doublingCell_lc, doublingCell_lc,
      rowAt_T, rowAt_T]
    exact le_of_eq (congrArg _ (by decide))
  · rw [lc_zero, rowAt_copy (rc_mem_below (.inl rfl) (.inr (.inr (.inl rfl)))),
      rowAt_copy (rc_mem_below (.inl rfl) (.inl rfl)), doublingCell_rc, doublingCell_rc,
      rowAt_T, rowAt_T]
    exact le_of_eq (congrArg _ (by decide))
  · rw [rowAt_copy (rc_mem_below (.inl rfl) (.inr (.inr (.inl rfl)))),
      rowAt_copy (rc_mem_below (.inl rfl) (.inr (.inl rfl))), doublingCell_rc, doublingCell_rc,
      rowAt_T, rowAt_T]
    exact le_of_eq (congrArg _ (by decide))
  · obtain ⟨w, hw, rfl⟩ : ∃ w : Fin 5, (w = 3 ∨ w = 4) ∧ lc α w = s := by
      rcases hs with rfl | rfl
      exacts [⟨3, .inl rfl, rfl⟩, ⟨4, .inr rfl, rfl⟩]
    obtain ⟨w', hw', rfl⟩ : ∃ w' : Fin 5, (w' = 3 ∨ w' = 4) ∧ rc α w' = t := by
      rcases ht with rfl | rfl
      exacts [⟨3, .inl rfl, rfl⟩, ⟨4, .inr rfl, rfl⟩]
    rw [show (I α).amalgam.toCellScheme.scope (lc α w) = _ from
        congrArg Prod.fst (gradedIndex_lc w),
      show (I α).amalgam.toCellScheme.scope (rc α w') = _ from
        congrArg Prod.fst (gradedIndex_rc w')]
    rcases hw with rfl | rfl <;> rcases hw' with rfl | rfl <;> decide

section Completion

variable {M₁ : ℕ} {rr : Fin M₁ → Fin ((I α).amalgam.card + M₁) → Label.{u}}

/-- The site in any layer of cells of full scope and grade `1` over the amalgam of the seed. -/
theorem isMixedSite_appendFullCells :
    ((I α).amalgam.toScheme.appendFullCells 1 M₁ rr ((I α).not_univ_le 1)).IsMixedSite
      (Fin.castAdd M₁ (lc α 0)) (Fin.castAdd M₁ (lc α 2)) (Fin.castAdd M₁ (lc α 3))
      (Fin.castAdd M₁ (lc α 4)) (Fin.castAdd M₁ (rc α 2)) (Fin.castAdd M₁ (rc α 3))
      (Fin.castAdd M₁ (rc α 4)) :=
  isMixedSite.appendFullCells

/-- The top hypothesis at the old cells of grade `2`, transported to the lower layer. -/
private theorem htop_castAdd {N : ℕ} {q : Fin ((I α).amalgam.card + M₁ + N) → Label.{u}}
    (htop : ∀ c, (c = lc α 3 ∨ c = lc α 4 ∨ c = rc α 3 ∨ c = rc α 4) →
      q (Fin.castAdd _ (Fin.castAdd M₁ c)) = ⊤) (c : Fin ((I α).amalgam.card + M₁))
    (hc : c = Fin.castAdd M₁ (lc α 3) ∨ c = Fin.castAdd M₁ (lc α 4) ∨
      c = Fin.castAdd M₁ (rc α 3) ∨ c = Fin.castAdd M₁ (rc α 4)) :
    q (Fin.castAdd N c) = ⊤ := by
  rcases hc with rfl | rfl | rfl | rfl
  exacts [htop _ (.inl rfl), htop _ (.inr (.inl rfl)), htop _ (.inr (.inr (.inl rfl))),
    htop _ (.inr (.inr (.inr rfl)))]

private theorem hs_castAdd {s : Fin (I α).amalgam.card}
    (hsc : s = lc α 0 ∨ s = lc α 2 ∨ s = lc α 3 ∨ s = lc α 4) :
    Fin.castAdd M₁ s = Fin.castAdd M₁ (lc α 0) ∨ Fin.castAdd M₁ s = Fin.castAdd M₁ (lc α 2) ∨
      Fin.castAdd M₁ s = Fin.castAdd M₁ (lc α 3) ∨ Fin.castAdd M₁ s = Fin.castAdd M₁ (lc α 4) := by
  rcases hsc with rfl | rfl | rfl | rfl
  exacts [.inl rfl, .inr (.inl rfl), .inr (.inr (.inl rfl)), .inr (.inr (.inr rfl))]

/-- **No leaf-and-marked layer over the seed reads `o'` at its tops**: over any layer of cells of
full scope and grade `1` over the amalgam of the input with itself, in the leaf-and-marked layer
at grade `2` with any marks marked-closed for its cap, every lawful labelling `⊤` at `o`, `r`,
`o'`, `r'` labels `⊤` a cell of full scope and grade `2` reading `o'` strictly below each of `y`,
`z`, `o`, `r`. -/
theorem not_exists_reading_markedLayer
    (Mk : Finset (Fin ((I α).amalgam.toScheme.appendFullCells 1 M₁ rr
      ((I α).not_univ_le 1)).card → Label.{u}))
    (hMk : Mk ⊆ ((I α).amalgam.toScheme.appendFullCells 1 M₁ rr ((I α).not_univ_le 1)).catalogue 2)
    {κ : (Fin ((I α).amalgam.toScheme.appendFullCells 1 M₁ rr ((I α).not_univ_le 1)).card →
      Label.{u}) → Label.{u}}
    (hcl : ((I α).amalgam.toScheme.appendFullCells 1 M₁ rr
      ((I α).not_univ_le 1)).MarkedClosed 2 Mk κ)
    {hS : ∀ d, ¬ ((univ : Finset (Fin 3)), 2) ≤
      ((I α).amalgam.toScheme.appendFullCells 1 M₁ rr
        ((I α).not_univ_le 1)).toCellScheme.gradedIndex d}
    {q : Fin _ → Label.{u}}
    (hq : (((I α).amalgam.toScheme.appendFullCells 1 M₁ rr ((I α).not_univ_le 1)).markedLayer 2
      Mk κ hS).rows.IsLawful q)
    (htop : ∀ c, (c = lc α 3 ∨ c = lc α 4 ∨ c = rc α 3 ∨ c = rc α 4) →
      q (Fin.castAdd _ (Fin.castAdd M₁ c)) = ⊤) :
    ¬ ∃ s, (s = lc α 0 ∨ s = lc α 2 ∨ s = lc α 3 ∨ s = lc α 4) ∧ ∀ j, q (Fin.natAdd _ j) = ⊤ →
      (((I α).amalgam.toScheme.appendFullCells 1 M₁ rr ((I α).not_univ_le 1)).markedLayer 2
        Mk κ hS).rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd M₁ s)) ≤
      (((I α).amalgam.toScheme.appendFullCells 1 M₁ rr ((I α).not_univ_le 1)).markedLayer 2
        Mk κ hS).rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd M₁ (rc α 3))) := by
  rintro ⟨s, hsc, hread⟩
  exact (isMixedSite_appendFullCells (α := α) (M₁ := M₁) (rr := rr)).not_exists_reading
    (Scheme.markedEntry_mem hMk)
    (Scheme.exists_leaf_eq (Mk := Mk) (Scheme.orbitCode_splice_bot_mem_catalogue
      (p := fun _ ↦ ⊥) (CellScheme.Rows.isLawfulBelow_const_bot _))).choose
    (Scheme.servesAgreements_markedLayer hcl) hq (htop_castAdd htop) ⟨_, hs_castAdd hsc, hread⟩

/-- **No canonical field layer over the seed reads `o'` at its tops**: over any layer of cells of
full scope and grade `1` over the amalgam of the input with itself, in the canonical field layer
at grade `2`. -/
theorem not_exists_reading_fieldLayer
    {hS : ∀ d, ¬ ((univ : Finset (Fin 3)), 2) ≤
      ((I α).amalgam.toScheme.appendFullCells 1 M₁ rr
        ((I α).not_univ_le 1)).toCellScheme.gradedIndex d}
    {q : Fin _ → Label.{u}}
    (hq : (((I α).amalgam.toScheme.appendFullCells 1 M₁ rr ((I α).not_univ_le 1)).fieldLayer 2
      hS).rows.IsLawful q)
    (htop : ∀ c, (c = lc α 3 ∨ c = lc α 4 ∨ c = rc α 3 ∨ c = rc α 4) →
      q (Fin.castAdd _ (Fin.castAdd M₁ c)) = ⊤) :
    ¬ ∃ s, (s = lc α 0 ∨ s = lc α 2 ∨ s = lc α 3 ∨ s = lc α 4) ∧ ∀ j, q (Fin.natAdd _ j) = ⊤ →
      (((I α).amalgam.toScheme.appendFullCells 1 M₁ rr ((I α).not_univ_le 1)).fieldLayer 2
        hS).rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd M₁ s)) ≤
      (((I α).amalgam.toScheme.appendFullCells 1 M₁ rr ((I α).not_univ_le 1)).fieldLayer 2
        hS).rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd M₁ (rc α 3))) := by
  rintro ⟨s, hsc, hread⟩
  exact (isMixedSite_appendFullCells (α := α) (M₁ := M₁) (rr := rr)).not_exists_reading_of_eq
    (fun i ↦ Scheme.catalogueEntry_mem i)
    (Scheme.exists_catalogueEntry_eq (Scheme.orbitCode_splice_bot_mem_catalogue
      (p := fun _ ↦ ⊥) (CellScheme.Rows.isLawfulBelow_const_bot _))).choose
    (Scheme.servesAgreements_of_le (fun _ _ ↦ le_top) fun a ha ↦ Scheme.exists_catalogueEntry_eq ha)
    (Scheme.fieldRow_eq_sheetRow fun _ ↦ ⊤) hq (htop_castAdd htop) ⟨_, hs_castAdd hsc, hread⟩

end Completion

/-- **The canonical completion at the arity one of the seed does not read `o'` at its tops**
(`Seed.fieldLayerOne`, the scheme of the completion `Seed.completionBelowFullGradeOne`): every
lawful labelling `⊤` at `o`, `r`, `o'`, `r'` labels `⊤` a cell of full scope and grade `2` reading
`o'` strictly below each of `y`, `z`, `o`, `r`. -/
theorem not_exists_reading_fieldLayerOne {q : Fin (I α).fieldLayerOne.card → Label.{u}}
    (hq : (I α).fieldLayerOne.rows.IsLawful q)
    (htop : ∀ c, (c = lc α 3 ∨ c = lc α 4 ∨ c = rc α 3 ∨ c = rc α 4) →
      q (Fin.castAdd _ (Fin.castAdd _ c)) = ⊤) :
    ¬ ∃ s, (s = lc α 0 ∨ s = lc α 2 ∨ s = lc α 3 ∨ s = lc α 4) ∧ ∀ j, q (Fin.natAdd _ j) = ⊤ →
      (I α).fieldLayerOne.rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd _ s)) ≤
      (I α).fieldLayerOne.rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd _ (rc α 3))) :=
  not_exists_reading_fieldLayer (M₁ := ((I α).amalgam.toScheme.catalogue 1).card)
    (rr := fun i ↦ (I α).amalgam.toScheme.fieldRow 1 ((I α).amalgam.toScheme.catalogueEntry 1 i))
    (hS := (I α).not_univ_two_le_lowerFieldLayer) hq htop

end MixedSeed

end VaughtConjecture
