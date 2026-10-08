/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.FieldLayer

/-!
# The field layer on a sub-catalogue, and the admitted field layer

Roadmap, Layer 3, 3.1, (R6), the completion below the full grade with a restricted catalogue at the
reading grades.

Let `S` be a scheme on `n` points none of whose cells lies above `(univ, k)`, and `C` a finite set
of labellings of the cells of `S`.  The **field layer on `C`** (`Scheme.fieldLayerOn S k C hS`)
appends to `S` one cell of scope `univ` and grade `k` for each member of `C`; the row of the new
cell of `a` is its **field row on `C`** (`Scheme.fieldRowOn`): `a` on the old cells, and at the new
cell of `b` the agreement height of `a` and `b` in the grid of the field layer
(`Scheme.fieldGrid`).  On the full canonical catalogue it is the canonical field layer
(`Scheme.fieldLayerOn_catalogue`, by definition).

* **Per-entry legality** (`Scheme.isLawful_fieldRowOn`): the field row on `C` of a member of `C`
  that lies in the canonical catalogue is a lawful section of the layer on `C`: on the old cells
  it is the entry, at a new cell its locality is the identity capped at the agreement height, and
  availability holds at its own cell, whose diagonal entry is the ceiling of the grid.
* For a sub-catalogue `C ⊆ S.catalogue k` the layer is consistent, well formed (when `(univ, k)`
  is a graded face), coded, and its new rows are short at `k` and never the formal top
  (`Scheme.isConsistent_fieldLayerOn`, `Scheme.isWellFormed_fieldLayerOn`,
  `Scheme.isCoded_fieldLayerOn`, `Scheme.isShort_ne_top_row_fieldLayerOn`).

**The admitted field layer.**  For a predicate `A` on the labellings of the cells of `S`, the
**admitted catalogue** (`Scheme.admittedCatalogue S k A`) is the set of entries of the canonical
catalogue satisfying `A`, and the **admitted field layer** (`Scheme.admittedFieldLayer`) is the
field layer on it.  Its laws are those of the field layer on a sub-catalogue; when `A` holds at
the constant `⊥`, it carries a cell at `(univ, k)` (`Scheme.bot_mem_admittedCatalogue`); the row
of every new cell reads, on the old cells, an entry satisfying `A`
(`Scheme.exists_admitted_row_admittedFieldLayer`); and for `A` everywhere true it is the canonical
field layer (`Scheme.admittedFieldLayer_true`).  Bountifulness of an admitted layer is not proved
here: the lifts of the canonical field layer (`Scheme.exists_isLawfulBelow_fieldLayer`,
`Scheme.exists_extension_fieldLayer`) use the entry of the orbit code of the whole boundary
labelling, which need not satisfy `A`.

## Placement

The engine of the restricted catalogue at the reading grades (`roadmap/README.md`, Layer 3, 3.1,
under "(R6)"); first piece.
-/

universe u

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} (S : Scheme.{u} n) (k : ℕ) (C : Finset (Fin S.card → Label.{u}))

/-! ### The field layer on a sub-catalogue -/

variable {S} in
/-- The member of `C` of the new cell `i`. -/
noncomputable def entryOn (i : Fin C.card) : Fin S.card → Label.{u} := (C.equivFin.symm i).1

variable {S k C}

/-- The member of the new cell `i` lies in `C`. -/
theorem entryOn_mem (i : Fin C.card) : entryOn C i ∈ C := (C.equivFin.symm i).2

/-- Every member of `C` is the member of some new cell. -/
theorem exists_entryOn_eq {a : Fin S.card → Label.{u}} (ha : a ∈ C) : ∃ i, entryOn C i = a :=
  ⟨C.equivFin ⟨a, ha⟩, by simp [entryOn]⟩

variable (S k C) in
/-- The **field row on `C`** of a labelling `a` of the old cells: `a` on the old cells, and on the
new cell `j` the agreement height of `a` with the member of `j`. -/
noncomputable def fieldRowOn (a : Fin S.card → Label.{u}) : Fin (S.card + C.card) → Label.{u} :=
  Fin.append a fun j ↦ agreementHeight (S.fieldGrid k) a (entryOn C j)

/-- The field row on `C` reads the labelling on the old cells. -/
@[simp] theorem fieldRowOn_castAdd (a : Fin S.card → Label.{u}) (d : Fin S.card) :
    S.fieldRowOn k C a (Fin.castAdd _ d) = a d :=
  Fin.append_left _ _ d

/-- The field row on `C` reads an agreement height on the new cells. -/
@[simp] theorem fieldRowOn_natAdd (a : Fin S.card → Label.{u}) (j : Fin C.card) :
    S.fieldRowOn k C a (Fin.natAdd _ j) = agreementHeight (S.fieldGrid k) a (entryOn C j) :=
  Fin.append_right _ _ j

/-- On the canonical catalogue the field row on `C` is the field row. -/
theorem fieldRowOn_catalogue (a : Fin S.card → Label.{u}) :
    S.fieldRowOn k (S.catalogue k) a = S.fieldRow k a := rfl

/-- The field row on `C` of a catalogue entry takes its values in the code grid with block bound
`2 N + 2`. -/
theorem fieldRowOn_mem_codeGrid {a : Fin S.card → Label.{u}} (ha : a ∈ S.catalogue k)
    (x : Fin (S.card + C.card)) : S.fieldRowOn k C a x ∈ codeGrid k (2 * S.card + 2) := by
  induction x using Fin.addCases with
  | left d =>
    rw [fieldRowOn_castAdd]
    exact codeGrid_mono (by omega) (mem_codeGrid_of_mem_catalogue ha d)
  | right j =>
    rw [fieldRowOn_natAdd]
    exact grid_subset_codeGrid _ _ (agreementHeight_spec (bot_mem_grid _ _) _ _).1

/-- Two field rows on `C` agree capped at the agreement height of their labellings. -/
theorem min_fieldRowOn_agreementHeight (a b : Fin S.card → Label.{u}) (x : Fin (S.card + C.card)) :
    min (S.fieldRowOn k C a x) (agreementHeight (S.fieldGrid k) a b) =
      min (S.fieldRowOn k C b x) (agreementHeight (S.fieldGrid k) a b) := by
  induction x using Fin.addCases with
  | left d =>
    rw [fieldRowOn_castAdd, fieldRowOn_castAdd]
    exact (agreementHeight_spec (bot_mem_grid _ _) a b).2 d
  | right j =>
    rw [fieldRowOn_natAdd, fieldRowOn_natAdd]
    exact agreementHeight_tri (bot_mem_grid _ _) a b _

variable (S k C) in
/-- **The field layer on `C`** at grade `k`: the cells of `S`, followed by one cell of scope
`univ` and grade `k` for each member of `C`, whose row is the field row on `C` of the member. -/
noncomputable abbrev fieldLayerOn
    (hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d) : Scheme.{u} n :=
  S.appendFullCells k C.card (fun i ↦ S.fieldRowOn k C (entryOn C i)) hS

variable {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- **On the canonical catalogue, the field layer on `C` is the canonical field layer.** -/
theorem fieldLayerOn_catalogue : S.fieldLayerOn k (S.catalogue k) hS = S.fieldLayer k hS := rfl

/-- The row of a new cell is the field row on `C` of its member. -/
theorem fieldLayerOn_row_natAdd (i : Fin C.card) (t) :
    (S.fieldLayerOn k C hS).rows.row (Fin.natAdd S.card i) t =
      S.fieldRowOn k C (entryOn C i) t.1 :=
  appendFullCells_row_natAdd i t

/-- **Per-entry legality**: the field row on `C` of a member of `C` that lies in the canonical
catalogue is a lawful section of the field layer on `C`.  On the old cells it is the entry, lawful
in `S`; at a new cell its locality is the identity capped at the agreement height, by the
ultrametric inequality; availability at the full face holds at the cell of the entry itself, whose
diagonal entry is the ceiling of the grid. -/
theorem isLawful_fieldRowOn {a : Fin S.card → Label.{u}} (ha : a ∈ S.catalogue k) (haC : a ∈ C) :
    (S.fieldLayerOn k C hS).rows.IsLawful (S.fieldRowOn k C a) := by
  refine isLawful_appendFullCells ?_ (fun i ↦ ?_) (fun i ↦ ?_) fun s _ ↦ ?_
  · convert (mem_catalogue.mp ha).1 using 1
    exact funext fun d ↦ fieldRowOn_castAdd a d
  · rw [fieldRowOn_natAdd]
    exact isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid _ _) _ _).1
  · have hc := isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid k (2 * S.card + 2))
      a (entryOn C i)).1
    convert (TransformsTo.refl (fun t : (S.appendFullCellsScheme k C.card).below
      ((S.appendFullCellsScheme k C.card).gradedIndex (Fin.natAdd S.card i)) ↦
        (S.appendFullCellsScheme k C.card).grade t)
          fun t ↦ S.fieldRowOn k C (entryOn C i) t.1)
      |>.min_const (K := k) (fun t ↦ t.2.2.trans (appendFullCellsScheme_grade_natAdd S k _ i).le)
        hc using 1
    funext t
    rw [fieldRowOn_natAdd]
    exact min_fieldRowOn_agreementHeight a _ t.1
  · obtain ⟨i, hi⟩ := exists_entryOn_eq haC
    refine ⟨i, ?_⟩
    rw [fieldRowOn_natAdd, hi, agreementHeight_self (gridPoint_mem_grid le_rfl)
      fun x hx ↦ le_gridPoint_of_mem_grid hx]
    exact le_gridPoint_of_mem_codeGrid (fieldRowOn_mem_codeGrid ha s)

/-- **The field layer on a sub-catalogue is consistent**: the old rows are those of `S`, and the
new rows are field rows of catalogue entries in `C`. -/
theorem isConsistent_fieldLayerOn (hcons : S.rows.IsConsistent) (hC : C ⊆ S.catalogue k) :
    (S.fieldLayerOn k C hS).rows.IsConsistent :=
  isConsistent_appendFullCells hcons fun i ↦
    isLawful_fieldRowOn (hC (entryOn_mem i)) (entryOn_mem i)

/-- **The field layer on `C` is well formed** when `(univ, k)` is a graded face. -/
theorem isWellFormed_fieldLayerOn (hwf : S.IsWellFormed) (hk0 : 0 < k) (hkn : k ≤ n) :
    (S.fieldLayerOn k C hS).IsWellFormed :=
  isWellFormed_appendFullCells hwf hk0 hkn

/-- **The field layer on a sub-catalogue is coded.** -/
theorem isCoded_fieldLayerOn (hc : S.IsCoded) (hC : C ⊆ S.catalogue k) :
    (S.fieldLayerOn k C hS).IsCoded :=
  isCoded_appendFullCells hc fun i x ↦
    lt_omega0_sq_of_mem_codeGrid (fieldRowOn_mem_codeGrid (hC (entryOn_mem i)) x)

/-- **The new rows of the field layer on a sub-catalogue are short at `k` and never the formal
top.** -/
theorem isShort_ne_top_row_fieldLayerOn (hC : C ⊆ S.catalogue k) (i : Fin C.card) (t) :
    IsShort k ((S.fieldLayerOn k C hS).rows.row (Fin.natAdd S.card i) t) ∧
      (S.fieldLayerOn k C hS).rows.row (Fin.natAdd S.card i) t ≠ ⊤ := by
  rw [fieldLayerOn_row_natAdd]
  exact ⟨isShort_of_mem_codeGrid (fieldRowOn_mem_codeGrid (hC (entryOn_mem i)) t.1),
    ne_top_of_mem_codeGrid (fieldRowOn_mem_codeGrid (hC (entryOn_mem i)) t.1)⟩

/-- A cell of the field layer on `C` of graded index `(univ, k)` is new. -/
theorem exists_natAdd_eq_fieldLayerOn {u : Fin (S.fieldLayerOn k C hS).card}
    (hu : (S.fieldLayerOn k C hS).toCellScheme.gradedIndex u = (univ, k)) :
    ∃ i, Fin.natAdd S.card i = u := by
  by_cases hlt : (u : ℕ) < S.card
  · refine absurd ?_ (hS ⟨u, hlt⟩)
    rw [← appendFullCellsScheme_gradedIndex_of_lt hlt]
    exact hu.ge
  · have hu' : (u : ℕ) < S.card + C.card := u.2
    exact ⟨⟨u - S.card, by omega⟩, Fin.ext (by simp; omega)⟩

/-- The row of a new cell, read at an old cell, is the member of the new cell. -/
theorem fieldLayerOn_row_castAdd (i : Fin C.card) (d : Fin S.card)
    (hd : Fin.castAdd C.card d ∈ (S.fieldLayerOn k C hS).toCellScheme.below
      ((S.fieldLayerOn k C hS).toCellScheme.gradedIndex (Fin.natAdd S.card i))) :
    (S.fieldLayerOn k C hS).rows.row (Fin.natAdd S.card i) ⟨_, hd⟩ = entryOn C i d := by
  rw [fieldLayerOn_row_natAdd, fieldRowOn_castAdd]

/-! ### The admitted catalogue and the admitted field layer -/

variable (S k) in
open Classical in
/-- The **admitted catalogue** at grade `k` for a predicate `A`: the entries of the canonical
catalogue satisfying `A`. -/
noncomputable def admittedCatalogue (A : (Fin S.card → Label.{u}) → Prop) :
    Finset (Fin S.card → Label.{u}) :=
  (S.catalogue k).filter A

variable {A : (Fin S.card → Label.{u}) → Prop}

/-- Membership in the admitted catalogue: an entry of the canonical catalogue satisfying `A`. -/
theorem mem_admittedCatalogue {a : Fin S.card → Label.{u}} :
    a ∈ S.admittedCatalogue k A ↔ a ∈ S.catalogue k ∧ A a := by
  classical
  simp only [admittedCatalogue, Finset.mem_filter]

/-- The admitted catalogue is a sub-catalogue. -/
theorem admittedCatalogue_subset : S.admittedCatalogue k A ⊆ S.catalogue k :=
  fun _ ha ↦ (mem_admittedCatalogue.mp ha).1

/-- **The constant `⊥` is admitted when `A` holds there**, so that the admitted layer carries a
cell at `(univ, k)`. -/
theorem bot_mem_admittedCatalogue (hA : A fun _ ↦ ⊥) :
    (fun _ ↦ ⊥ : Fin S.card → Label.{u}) ∈ S.admittedCatalogue k A :=
  mem_admittedCatalogue.mpr ⟨bot_mem_catalogue S k, hA⟩

/-- **When `A` holds everywhere, the admitted catalogue is the canonical catalogue.** -/
theorem admittedCatalogue_of_forall (hA : ∀ a, A a) : S.admittedCatalogue k A = S.catalogue k := by
  ext a
  rw [mem_admittedCatalogue]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hA a⟩⟩

/-- **For `A` everywhere true the admitted catalogue is the canonical catalogue.** -/
theorem admittedCatalogue_true : S.admittedCatalogue k (fun _ ↦ True) = S.catalogue k :=
  admittedCatalogue_of_forall fun _ ↦ trivial

variable (S k A) in
/-- **The admitted field layer** at grade `k`: the field layer on the admitted catalogue. -/
noncomputable abbrev admittedFieldLayer
    (hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d) : Scheme.{u} n :=
  S.fieldLayerOn k (S.admittedCatalogue k A) hS

/-- **When `A` holds everywhere, the admitted field layer is the canonical field layer.** -/
theorem admittedFieldLayer_of_forall (hA : ∀ a, A a) :
    S.admittedFieldLayer k A hS = S.fieldLayer k hS := by
  rw [admittedFieldLayer, admittedCatalogue_of_forall hA, fieldLayerOn_catalogue]

/-- **For `A` everywhere true the admitted field layer is the canonical field layer.** -/
theorem admittedFieldLayer_true :
    S.admittedFieldLayer k (fun _ ↦ True) hS = S.fieldLayer k hS :=
  admittedFieldLayer_of_forall fun _ ↦ trivial

/-- **The admitted field layer is consistent.** -/
theorem isConsistent_admittedFieldLayer (hcons : S.rows.IsConsistent) :
    (S.admittedFieldLayer k A hS).rows.IsConsistent :=
  isConsistent_fieldLayerOn hcons admittedCatalogue_subset

/-- **The admitted field layer is coded.** -/
theorem isCoded_admittedFieldLayer (hc : S.IsCoded) : (S.admittedFieldLayer k A hS).IsCoded :=
  isCoded_fieldLayerOn hc admittedCatalogue_subset

/-- **The admitted field layer carries a cell at `(univ, k)`** when `A` holds at the constant `⊥`.
-/
theorem exists_gradedIndex_eq_admittedFieldLayer (hA : A fun _ ↦ ⊥) :
    ∃ u, (S.admittedFieldLayer k A hS).toCellScheme.gradedIndex u = (univ, k) := by
  obtain ⟨i, -⟩ := exists_entryOn_eq (bot_mem_admittedCatalogue (S := S) (k := k) hA)
  exact ⟨Fin.natAdd _ i, appendFullCellsScheme_gradedIndex_natAdd _ _ _ i⟩

/-- **Every row of the admitted field layer at `(univ, k)` reads, on the old cells, an entry
satisfying `A`.** -/
theorem exists_admitted_row_admittedFieldLayer {u : Fin (S.admittedFieldLayer k A hS).card}
    (hu : (S.admittedFieldLayer k A hS).toCellScheme.gradedIndex u = (univ, k)) :
    ∃ a, a ∈ S.catalogue k ∧ A a ∧ ∀ d (hd : Fin.castAdd _ d ∈
        (S.admittedFieldLayer k A hS).toCellScheme.below
          ((S.admittedFieldLayer k A hS).toCellScheme.gradedIndex u)),
      (S.admittedFieldLayer k A hS).rows.row u ⟨_, hd⟩ = a d := by
  obtain ⟨i, rfl⟩ := exists_natAdd_eq_fieldLayerOn hu
  exact ⟨entryOn _ i, mem_admittedCatalogue.mp (entryOn_mem i) |>.1,
    mem_admittedCatalogue.mp (entryOn_mem i) |>.2, fun d hd ↦ fieldLayerOn_row_castAdd i d hd⟩

end VaughtConjecture.Scheme
