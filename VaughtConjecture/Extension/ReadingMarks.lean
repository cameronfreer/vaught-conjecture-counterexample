/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.MarkedCatalogueCompletion

/-!
# The reading marks: compatibility with the leaf-and-marked engine

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7, and (R3) of the table of 3.4.

The engine (`VaughtConjecture.Extension.MarkedCatalogue`) takes a marked subset of the catalogue
and a cap, and asks two compatibility conditions of them: the cap respects capped agreement
(`Scheme.CapRespects`) and the marked subset is closed above the cap (`Scheme.MarkedClosed`).  This
file proves them for the **reading marks** (`Scheme.readingMarks S k r X`): the catalogue entries
that read every cell of `X` at least as the cell `r`.  These are compatibility statements only; the
existence of the completion is the engine theorem (`TowerProfile.markedCompletion`), and nothing
here proves a top-reading carrier.

* **Marked closure above the reading** (`Scheme.markedClosed_readingMarks`, compiled in this
  repository (theorem named)): for a cap at least the value at `r` of every reading mark, a
  catalogue entry agreeing with a reading mark capped above the cap reads `X` at least as `r`: its
  value at `r` is that of the mark (below the cap), and its values on `X` are at least it.
* **The ceiling cap** (`Scheme.markedClosed_readingMarks_ceiling`, `Scheme.capRespects_const`):
  the constant cap at the ceiling `ω * (2 N + 2) + k` of the field grid lies in the grid and bounds
  every catalogue value, so it satisfies both conditions.
* **The reading specification** (`TowerProfile.MarkedSpec.reading`): the reading marks with the
  ceiling cap, a marked specification of every seed on five points; every marked cell of its marked
  top reads `X` at least as `r` (`TowerProfile.MarkedSpec.reading_mark_reads`).

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Scheme

variable {n : ℕ} (S : Scheme.{u} n) (k : ℕ)

/-- The **reading marks**: the catalogue entries that read every cell of `X` at least as `r`. -/
noncomputable def readingMarks (r : Fin S.card) (X : Finset (Fin S.card)) :
    Finset (Fin S.card → Label.{u}) :=
  (S.catalogue k).filter fun e ↦ ∀ x ∈ X, e r ≤ e x

variable {S k}

/-- The reading marks lie in the catalogue. -/
theorem readingMarks_subset (r : Fin S.card) (X : Finset (Fin S.card)) :
    S.readingMarks k r X ⊆ S.catalogue k :=
  filter_subset _ _

/-- A reading mark reads every cell of `X` at least as `r`. -/
theorem le_of_mem_readingMarks {r : Fin S.card} {X : Finset (Fin S.card)}
    {e : Fin S.card → Label.{u}} (he : e ∈ S.readingMarks k r X) {x : Fin S.card} (hx : x ∈ X) :
    e r ≤ e x :=
  (mem_filter.mp he).2 x hx

/-- **Marked closure of the reading marks**, for a cap at least the value at `r` of every reading
mark. -/
theorem markedClosed_readingMarks {r : Fin S.card} {X : Finset (Fin S.card)}
    {κ : (Fin S.card → Label.{u}) → Label.{u}} (hκ : ∀ e ∈ S.readingMarks k r X, e r ≤ κ e) :
    MarkedClosed S k (S.readingMarks k r X) κ := by
  intro e he b hb h _ _ _ hκh hag
  have hlt : e r < h := (hκ e he).trans_lt (not_le.mp hκh)
  -- below the cap, `b` reads `r` as `e` does
  have hbr : b r = e r := by
    have := hag r
    rw [min_eq_left hlt.le] at this
    rcases le_or_gt h (b r) with hle | hgt
    · rw [min_eq_right hle] at this
      exact absurd this hlt.ne'
    · rwa [min_eq_left hgt.le] at this
  refine mem_filter.mpr ⟨hb, fun x hx ↦ ?_⟩
  rw [hbr]
  have hx' := hag x
  calc e r = min (e r) h := (min_eq_left hlt.le).symm
    _ ≤ min (e x) h := min_le_min_right h (le_of_mem_readingMarks he hx)
    _ = min (b x) h := hx'.symm
    _ ≤ b x := min_le_left _ _

/-- **Marked closure with the ceiling cap**: the ceiling of the field grid bounds every catalogue
value. -/
theorem markedClosed_readingMarks_ceiling (r : Fin S.card) (X : Finset (Fin S.card)) :
    MarkedClosed S k (S.readingMarks k r X) fun _ ↦ gridPoint k (2 * S.card + 2) :=
  markedClosed_readingMarks fun e he ↦
    (le_gridPoint_of_mem_codeGrid (mem_codeGrid_of_mem_catalogue
      (readingMarks_subset r X he) r)).trans (gridPoint_le_gridPoint.mpr (by omega))

end Scheme

namespace TowerProfile

variable {α : Ordinal.{u}} (I : Seed.{u} α 3)

/-- **The reading specification**: the reading marks of `r` over `X` at the grade `4`, with the
ceiling cap. -/
noncomputable def MarkedSpec.reading (r : Fin (scheme I).card) (X : Finset (Fin (scheme I).card)) :
    MarkedSpec I where
  marks := (scheme I).readingMarks 4 r X
  cap _ := gridPoint 4 (2 * (scheme I).card + 2)
  marks_subset := Scheme.readingMarks_subset r X
  cap_mem _ := gridPoint_mem_grid le_rfl
  capRespects := Scheme.capRespects_const _
  closed := Scheme.markedClosed_readingMarks_ceiling r X

variable {I}

/-- **Every marked cell of the reading specification reads `X` at least as `r`**, in every lawful
labelling (`TowerProfile.forall_isLawful_mark_reads`). -/
theorem MarkedSpec.reading_mark_reads (r : Fin (scheme I).card)
    (X : Finset (Fin (scheme I).card)) :
    ∀ q : Fin (markedTop I (MarkedSpec.reading I r X)).card → Label.{u},
      (markedTop I (MarkedSpec.reading I r X)).rows.IsLawful q →
      ∀ m : Fin (MarkedSpec.reading I r X).marks.card, ∀ x ∈ X,
        (scheme I).sheetRow 4 ((scheme I).markedEntry 4 (MarkedSpec.reading I r X).marks)
          (Scheme.markedSheet _ _) (MarkedSpec.reading I r X).cap (Fin.natAdd _ m)
            (Fin.castAdd _ r) ≤
        (scheme I).sheetRow 4 ((scheme I).markedEntry 4 (MarkedSpec.reading I r X).marks)
          (Scheme.markedSheet _ _) (MarkedSpec.reading I r X).cap (Fin.natAdd _ m)
            (Fin.castAdd _ x) :=
  forall_isLawful_mark_reads (P := fun e ↦ ∀ x ∈ X, e r ≤ e x) _
    (fun _ he _ hx ↦ Scheme.le_of_mem_readingMarks he hx)

end TowerProfile

end VaughtConjecture
