/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Gluing
import VaughtConjecture.Stage.Legal

/-!
# Muting the cells of full grade

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the attached predecessor, whose cells of
the full grade of the private context off the private face are muted); semantic contract,
items 3–4.

**Muting** (`StageType.muteTop t`).  For a stage type `t` on `k` points, replace the row of every
cell of grade `k` (the full grade) by the constant `⊥` and its label by `⊥`; keep everything else.
A muted cell is `⊥` in every lawful labelling (its row is `⊥` at itself).

* **Lawful** (the labels): the old cells of grade below `k` read only cells of grade below `k`, so
  their locality and availability are those of `t`; a muted cell has label `⊥`.
* **Legal** (`StageType.IsLegal.muteTop`): the new rows are consistent (the constant `⊥` is
  lawful, and the other rows read only cells of grade below `k`, whose rows are unchanged); the
  lifts between pairs of grade below `k` are those of `t`, since the rows agree below them
  (`CellScheme.Rows.cappedLift_congr`); and a lift to a pair of grade `k` starts at the full face.
* **The proper faces are unchanged** (`StageType.restrictFace_muteTop`): a cell visible through an
  embedding onto a proper subset has grade below `k`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`, beside
`VaughtConjecture.Extension.AttachedPredecessor`.  `CellScheme.Rows.isLawfulBelow_rows_congr` and
`CellScheme.Rows.cappedLift_congr` belong in `VaughtConjecture.Scheme.Bountiful`.

## References

Lawful sections are [Kni26, Definition 2.5.4] and bountifulness [Kni26, Definition 2.5.14].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R R' : D.Rows.{u}}

/-- **Lawfulness below a pair depends only on the rows of the cells below it.** -/
theorem isLawfulBelow_rows_congr {X : Finset α × ℕ} (h : ∀ s ∈ D.below X, R.row s = R'.row s)
    {r : D.below X → Label.{u}} : R.IsLawfulBelow X r ↔ R'.IsLawfulBelow X r := by
  rw [← isLawfulBelow_extendBot (R := R), ← isLawfulBelow_extendBot (R := R'),
    isLawfulBelow_iff_forall, isLawfulBelow_iff_forall]
  refine and_congr Iff.rfl (and_congr ⟨fun hl s hs ↦ ?_, fun hl s hs ↦ ?_⟩ Iff.rfl)
  · rw [← h s hs]; exact hl s hs
  · rw [h s hs]; exact hl s hs

/-- **Capped lifts depend only on the rows of the cells below the target.** -/
theorem cappedLift_congr {X Y : Finset α × ℕ} (hXY : X ≤ Y)
    (h : ∀ s ∈ D.below Y, R.row s = R'.row s) (hl : R.CappedLift hXY) : R'.CappedLift hXY := by
  have hX : ∀ s ∈ D.below X, R.row s = R'.row s := fun s hs ↦ h s (D.below_mono hXY hs)
  refine (cappedLift_iff_forall_exists hXY).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨q', hq', hq'c, hq'p⟩ := (cappedLift_iff_forall_exists hXY).mp hl c hc p q
    ((isLawfulBelow_rows_congr (R := R) (R' := R') hX).mpr hp)
    ((isLawfulBelow_rows_congr (R := R) (R' := R') h).mpr hq) hpq
  exact ⟨q', (isLawfulBelow_rows_congr (R := R) (R' := R') h).mp hq', hq'c, hq'p⟩

end CellScheme.Rows

namespace StageType

variable {α : Ordinal.{u}} {k m : ℕ} (t : StageType.{u} α k)

/-- The rows of `t` with every cell of grade `k` muted. -/
def muteRows : t.toCellScheme.Rows.{u} :=
  ⟨fun s x ↦ if t.toCellScheme.grade s = k then ⊥ else t.rows.row s x⟩

/-- The labels of `t` with every cell of grade `k` labelled `⊥`. -/
def muteLabel (c : Fin t.card) : Label.{u} :=
  if t.toCellScheme.grade c = k then ⊥ else t.label c

variable {t}

/-- A cell below a cell of grade below `k` has grade below `k`. -/
theorem grade_lt_of_mem_below {s : Fin t.card} (hs : t.toCellScheme.grade s ≠ k)
    (d : t.toCellScheme.below (t.toCellScheme.gradedIndex s)) : t.toCellScheme.grade d ≠ k := by
  have h1 : t.toCellScheme.grade d ≤ t.toCellScheme.grade s := d.2.2
  have h2 := t.grade_le s
  omega

theorem muteRows_row_of_ne {s : Fin t.card} (hs : t.toCellScheme.grade s ≠ k) :
    t.muteRows.row s = t.rows.row s :=
  funext fun _ ↦ ite_eq_right hs

theorem muteRows_row_of_eq {s : Fin t.card} (hs : t.toCellScheme.grade s = k) :
    t.muteRows.row s = fun _ ↦ ⊥ :=
  funext fun _ ↦ ite_eq_left hs

theorem muteLabel_of_ne {c : Fin t.card} (hc : t.toCellScheme.grade c ≠ k) :
    t.muteLabel c = t.label c :=
  ite_eq_right hc

theorem muteLabel_of_eq {c : Fin t.card} (hc : t.toCellScheme.grade c = k) :
    t.muteLabel c = ⊥ :=
  ite_eq_left hc

/-- The muted labels are lawful for the muted rows. -/
theorem isLawful_muteLabel : t.muteRows.IsLawful t.muteLabel where
  orderly d := by
    by_cases hd : t.toCellScheme.grade d = k
    · rw [muteLabel_of_eq hd]; exact isSelfVisible_bot _
    · rw [muteLabel_of_ne hd]; exact t.isLawful.orderly d
  locality s := by
    by_cases hs : t.toCellScheme.grade s = k
    · rw [muteRows_row_of_eq hs]
      have heq : (fun d : t.toCellScheme.below (t.toCellScheme.gradedIndex s) ↦
          min (t.muteLabel d) (t.muteLabel s)) = fun _ ↦ ⊥ :=
        funext fun d ↦ by rw [muteLabel_of_eq hs, min_bot_right]
      rw [heq]
      exact TransformsTo.bot _ _
    · rw [muteRows_row_of_ne hs]
      have heq : (fun d : t.toCellScheme.below (t.toCellScheme.gradedIndex s) ↦
          min (t.muteLabel d) (t.muteLabel s)) =
            fun d : t.toCellScheme.below (t.toCellScheme.gradedIndex s) ↦
              min (t.label d) (t.label s) :=
        funext fun d ↦ by rw [muteLabel_of_ne (grade_lt_of_mem_below hs d), muteLabel_of_ne hs]
      rw [heq]
      exact t.isLawful.locality s
  availability s u hsu hg := by
    by_cases hu : t.toCellScheme.grade u = k
    · exact ⟨u, rfl, by rw [muteLabel_of_eq (hg.trans hu)]; exact bot_le⟩
    · obtain ⟨v, hv, hle⟩ := t.isLawful.availability s u hsu hg
      have hvk : t.toCellScheme.grade v ≠ k := by
        rw [show t.toCellScheme.grade v = (t.toCellScheme.gradedIndex v).2 from rfl, hv]
        exact hu
      exact ⟨v, hv, by rw [muteLabel_of_ne (hg ▸ hu), muteLabel_of_ne hvk]; exact hle⟩

variable (t) in
/-- **Muting the cells of full grade**: the rows of the cells of grade `k` become the constant `⊥`
and their labels `⊥`. -/
def muteTop : StageType.{u} α k where
  toScheme := ⟨t.card, t.toCellScheme, t.muteRows⟩
  label := t.muteLabel
  isWellFormed := ⟨t.isWellFormed.ground_eq, t.isWellFormed.isWellFormed⟩
  isCoded s x := by
    -- The rows of the muted type are `muteRows` (by definition).
    change (if t.toCellScheme.grade s = k then ⊥ else t.rows.row s x) < _
    split_ifs
    · exact WithBot.bot_lt_coe _
    · exact t.isCoded s x
  isLawful := isLawful_muteLabel
  atStage c := by
    unfold muteLabel
    split_ifs
    · exact atStage_bot
    · exact t.atStage c

/-- A cell of grade `k` of the muted type is muted: its row is `⊥` at itself. -/
theorem muteTop_row_self {c : Fin (t.muteTop).card} (hc : (t.muteTop).toCellScheme.grade c = k) :
    (t.muteTop).rows.row c ⟨c, (t.muteTop).toCellScheme.mem_below_gradedIndex c⟩ = ⊥ :=
  ite_eq_left hc

/-- **Muting keeps legality.** -/
theorem IsLegal.muteTop (ht : t.IsLegal) : (t.muteTop).IsLegal := by
  refine isLegal_iff.mpr ⟨fun s ↦ ?_, ?_, ht.isComplete⟩
  · by_cases hs : t.toCellScheme.grade s = k
    · -- The rows of the muted type are `muteRows` (by definition).
      change t.muteRows.IsLawfulBelow _ (t.muteRows.row s)
      rw [muteRows_row_of_eq hs]
      exact CellScheme.Rows.isLawfulBelow_const_bot _
    · -- The rows of the muted type are `muteRows` (by definition).
      change t.muteRows.IsLawfulBelow _ (t.muteRows.row s)
      rw [muteRows_row_of_ne hs]
      refine (CellScheme.Rows.isLawfulBelow_rows_congr (R := t.rows) (R' := t.muteRows)
        fun c hc ↦ ?_).mp (ht.isConsistent s)
      exact (muteRows_row_of_ne (grade_lt_of_mem_below hs ⟨c, hc⟩)).symm
  · refine CellScheme.Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
    have hY' : (Y.1, X.2) ∈ t.toCellScheme.gradedFaces :=
      ⟨hY.1, hX.2.1, hX.2.2.trans (card_le_card h.1)⟩
    by_cases hXk : X.2 = k
    · -- At the full grade the pair is on the full face.
      have hX1 : X.1 = univ := eq_of_subset_of_card_le (subset_univ _) (by
        have := hX.2.2
        simp only [card_univ, Fintype.card_fin]
        omega)
      exact CellScheme.Rows.cappedLift_of_fst_eq _
        (hX1.trans (univ_subset_iff.mp (hX1 ▸ h.1)).symm)
    · refine CellScheme.Rows.cappedLift_congr _ (fun s hs ↦ ?_)
        (ht.isBountiful hX hY' ⟨h.1, le_rfl⟩)
      have h1 : t.toCellScheme.grade s ≤ X.2 := hs.2
      have h2 : X.2 ≤ k := hX.2.2.trans ((card_le_univ _).trans_eq (Fintype.card_fin k))
      exact (muteRows_row_of_ne (by omega)).symm

/-- **The proper faces of the muted type are those of `t`**: a cell visible through an embedding
onto a proper subset has grade below `k`. -/
theorem restrictFace_muteTop (g : Fin m ↪ Fin k) (hg : univ.map g ≠ univ) :
    restrictFace g t.muteTop = restrictFace g t := by
  have hvis : ∀ s : Fin t.card, (t.toCellScheme.scope s : Set (Fin k)) ⊆ Set.range g →
      t.toCellScheme.grade s ≠ k := fun s hs hsk ↦ by
    have hsub : t.toCellScheme.scope s ⊆ univ.map g := fun x hx ↦ by
      obtain ⟨y, rfl⟩ := hs (mem_coe.mpr hx)
      exact mem_map_of_mem _ (mem_univ y)
    have hlt : #(univ.map g) < k := by
      have := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, hg⟩)
      simpa using this
    have := t.isWellFormed.isWellFormed.grade_le_card s
    have := card_le_card hsub
    omega
  by_cases hf : univ.map g ∈ t.toCellScheme.faces
  · rw [restrictFace_of_mem t.muteTop g hf, restrictFace_of_mem t g hf]
    refine congrArg some (ext ?_ fun i j hij ↦ ?_)
    · refine Scheme.comap_mk_congr g fun s hs ↦ muteRows_row_of_ne (hvis s ?_)
      intro x hx
      exact Scheme.mem_visibleCells.mp hs hx
    · obtain rfl : i = j := Fin.ext hij
      -- The labels of a restriction are those of the visible cells (by definition).
      change t.muteLabel _ = t.label _
      refine muteLabel_of_ne (hvis _ ?_)
      intro x hx
      exact Scheme.mem_visibleCells.mp (t.toScheme.cellMap_mem g i) hx
  · rw [restrictFace_of_notMem t.muteTop g hf, restrictFace_of_notMem t g hf]

end StageType

end VaughtConjecture
