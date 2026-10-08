/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.FieldLayer
import VaughtConjecture.Extension.Gate

/-!
# Sheet layers: leaves and marked cells of full scope

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.5 (one layer of cells of full scope over a scheme), in
the form with two kinds of new cells: **leaves**, whose rows are the field rows of the canonical
catalogue and serve availability as in the canonical field layer, and **marked cells**, whose rows
read the old cells by a chosen family of catalogue entries and read the leaves only up to a cap.

## Sheet layers

Let `S` be a scheme on `n` points none of whose cells lies above `(univ, k)`.  A **sheet layer**
(`Scheme.sheetLayer S k ε σ κ hS`) appends `M` cells of scope `univ` and grade `k`; the new cell
`i` has an **entry** `ε i` (a labelling of the old cells), a **sheet** `σ i` (a boolean), and the
**cap** `κ (ε i)` of its entry.  Its row (`Scheme.sheetRow`) reads the old cells by its entry and
the new cell `j` at the **cross height** (`Scheme.crossHeight`): the agreement height of the two
entries, capped at `κ (ε i)` when the two sheets differ.  With one sheet this is the field row of
the canonical field layer.

* **The agreement of two rows capped at `h`** (`Scheme.min_sheetRow_eq`): two rows agree capped at
  `h` when their entries and their agreement heights do, their caps agree capped at `h`, and the
  two cells lie in one sheet or `h` is at most the cap of the second.  At the cross height of two
  cells all four hold, which gives locality.
* **The rows are lawful** (`Scheme.isLawful_sheetRow`) when the entries lie in the canonical
  catalogue, the caps lie in the field grid, and the cap respects capped agreement of entries (the
  hypothesis `Scheme.CapRespects`).  So the layer is consistent (`Scheme.isConsistent_sheetLayer`);
  it is well formed, coded, and its new rows are short at `k` and never the formal top.
* **Extension at the cap `⊥`** (`Scheme.exists_isLawfulBelow_sheetLayer`): every labelling
  lawful below `(univ, k)` extends through the new cells by the row of any new cell whose entry is
  the orbit code of its splice (the **template**), read by the orbit decoder at the least grid
  point.
* **Extension at a short positive cap** (`Scheme.exists_extension_sheetLayer`): along the row of a
  new cell `j`, by the row of a template `j₀` that lies in the sheet of `j` or whenever the cap is
  at most the cap of `j`.  At a cap above the cap of `j` and with the template in the other sheet,
  the row of `j₀` reads the cells of the sheet of `j` uncapped while that of `j` caps them, and the
  two rows differ capped at `h`; so a lift along a marked cell above its cap needs a marked
  template.
* **Extension from the boundary** (`Scheme.extendsFromBoundary_bot_sheetLayer`,
  `Scheme.extendsFromBoundary_sheetLayer_of_fill`), as for the canonical field layer.

## Leaves and marked cells

**The leaf-and-marked layer** (`Scheme.markedLayer S k Mk κ hS`) is the sheet layer with one leaf
(sheet `false`) for every entry of the canonical catalogue and one marked cell (sheet `true`) for
every member of a subset `Mk` of the catalogue.  The leaves are templates for every extension at
`⊥` and for every lift along a leaf, and for a lift along a marked cell at a cap at most its cap
(`Scheme.exists_template_markedLayer`).  A lift along a marked cell `m` at a cap `h` above its cap
needs the orbit code of the boundary labelling, which agrees with the entry of `m` capped at `h`,
to lie in `Mk`: the closure hypothesis `Scheme.MarkedClosed`.  Every marked cell reads the old
cells by its member of `Mk` (`Scheme.markedLayer_row_mark_castAdd`): a predicate on the reading of
the old cells holds at every marked cell when it holds on `Mk`.

## Placement

Checkpoint 2.5 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} (S : Scheme.{u} n) (k : ℕ) {M : ℕ}

/-! ### Cross heights and sheet rows -/

/-- The cap of the reading of the new cell `j` by the new cell `i`: none (`⊤`) in one sheet, and
the cap of the entry of `i` across the sheets. -/
noncomputable def sheetCap (ε : Fin M → Fin S.card → Label.{u}) (σ : Fin M → Bool)
    (κ : (Fin S.card → Label.{u}) → Label.{u}) (i j : Fin M) : Label.{u} :=
  if σ i = σ j then ⊤ else κ (ε i)

/-- The **cross height** of the new cells `i` and `j`: the agreement height of their entries in the
field grid, capped by `sheetCap`. -/
noncomputable def crossHeight (ε : Fin M → Fin S.card → Label.{u}) (σ : Fin M → Bool)
    (κ : (Fin S.card → Label.{u}) → Label.{u}) (i j : Fin M) : Label.{u} :=
  min (agreementHeight (S.fieldGrid k) (ε i) (ε j)) (S.sheetCap ε σ κ i j)

/-- The **sheet row** of the new cell `i`: its entry on the old cells and the cross heights on the
new cells. -/
noncomputable def sheetRow (ε : Fin M → Fin S.card → Label.{u}) (σ : Fin M → Bool)
    (κ : (Fin S.card → Label.{u}) → Label.{u}) (i : Fin M) : Fin (S.card + M) → Label.{u} :=
  Fin.append (ε i) fun j ↦ S.crossHeight k ε σ κ i j

variable {S k} {ε : Fin M → Fin S.card → Label.{u}} {σ : Fin M → Bool}
  {κ : (Fin S.card → Label.{u}) → Label.{u}}

/-- The sheet row reads the old cells by the entry. -/
@[simp] theorem sheetRow_castAdd (i : Fin M) (d : Fin S.card) :
    S.sheetRow k ε σ κ i (Fin.castAdd M d) = ε i d :=
  Fin.append_left _ _ d

/-- The sheet row reads the new cells at the cross heights. -/
@[simp] theorem sheetRow_natAdd (i j : Fin M) :
    S.sheetRow k ε σ κ i (Fin.natAdd S.card j) = S.crossHeight k ε σ κ i j :=
  Fin.append_right _ _ j

/-- In one sheet the cross height is the agreement height. -/
theorem crossHeight_of_eq {i j : Fin M} (h : σ i = σ j) :
    S.crossHeight k ε σ κ i j = agreementHeight (S.fieldGrid k) (ε i) (ε j) := by
  rw [crossHeight, sheetCap, ite_eq_left h, min_top_right]

/-- Across the sheets the cross height is the agreement height capped at the cap of the first
entry. -/
theorem crossHeight_of_ne {i j : Fin M} (h : σ i ≠ σ j) :
    S.crossHeight k ε σ κ i j = min (agreementHeight (S.fieldGrid k) (ε i) (ε j)) (κ (ε i)) := by
  rw [crossHeight, sheetCap, ite_eq_right h]

/-- The cross height of a new cell with itself is the ceiling of the field grid. -/
theorem crossHeight_self (i : Fin M) :
    S.crossHeight k ε σ κ i i = gridPoint k (2 * S.card + 2) := by
  rw [crossHeight_of_eq rfl, agreementHeight_self (gridPoint_mem_grid le_rfl)
    fun x hx ↦ le_gridPoint_of_mem_grid hx]

/-- The cross heights lie in the field grid when the caps do. -/
theorem crossHeight_mem_fieldGrid (hκ : ∀ e, κ e ∈ S.fieldGrid k) (i j : Fin M) :
    S.crossHeight k ε σ κ i j ∈ S.fieldGrid k := by
  have hA := (agreementHeight_spec (bot_mem_grid k (2 * S.card + 2)) (ε i) (ε j)).1
  by_cases h : σ i = σ j
  · rw [crossHeight_of_eq h]
    exact hA
  · rw [crossHeight_of_ne h]
    rcases min_choice (agreementHeight (S.fieldGrid k) (ε i) (ε j)) (κ (ε i)) with h' | h' <;>
      rw [h']
    exacts [hA, hκ _]

/-- The sheet row of an entry of the catalogue takes its values in the code grid with block bound
`2 N + 2`. -/
theorem sheetRow_mem_codeGrid (hε : ∀ i, ε i ∈ S.catalogue k) (hκ : ∀ e, κ e ∈ S.fieldGrid k)
    (i : Fin M) (x : Fin (S.card + M)) :
    S.sheetRow k ε σ κ i x ∈ codeGrid k (2 * S.card + 2) := by
  induction x using Fin.addCases with
  | left d =>
    rw [sheetRow_castAdd]
    exact codeGrid_mono (by omega) (mem_codeGrid_of_mem_catalogue (hε i) d)
  | right j =>
    rw [sheetRow_natAdd]
    exact grid_subset_codeGrid _ _ (crossHeight_mem_fieldGrid hκ i j)

/-- Capping distributes over a minimum. -/
private theorem min_min_distrib (a b c : Label.{u}) :
    min (min a b) c = min (min a c) (min b c) := by
  rw [min_assoc, min_assoc a c, min_left_comm c b c, min_self]

/-- The caps of two cells agree capped at `h` when one sheet holds both, or when `h` is at most
the cap of the second and the caps of the entries agree capped at `h`. -/
private theorem min_sheetCap_eq {i j l : Fin M} {h : Label.{u}}
    (hκ : min (κ (ε i)) h = min (κ (ε j)) h) (hσ : σ i = σ j ∨ h ≤ κ (ε j)) :
    min (S.sheetCap ε σ κ i l) h = min (S.sheetCap ε σ κ j l) h := by
  have hκj : σ i ≠ σ j → min (κ (ε j)) h = h := fun hne ↦ min_eq_right (hσ.resolve_left hne)
  unfold sheetCap
  by_cases hil : σ i = σ l <;> by_cases hjl : σ j = σ l
  · rw [ite_eq_left hil, ite_eq_left hjl]
  · rw [ite_eq_left hil, ite_eq_right hjl, min_top_left, hκj (fun h' ↦ hjl (h'.symm.trans hil))]
  · rw [ite_eq_right hil, ite_eq_left hjl, min_top_left, hκ, hκj (fun h' ↦ hil (h'.trans hjl))]
  · rw [ite_eq_right hil, ite_eq_right hjl, hκ]

/-- **Two sheet rows agree capped at `h`** when their entries agree capped at `h`, so do their
agreement heights with every labelling and their caps, and the two cells lie in one sheet or `h`
is at most the cap of the second. -/
theorem min_sheetRow_eq {i j : Fin M} {h : Label.{u}}
    (hold : ∀ d, min (ε i d) h = min (ε j d) h)
    (hA : ∀ c, min (agreementHeight (S.fieldGrid k) (ε i) c) h =
      min (agreementHeight (S.fieldGrid k) (ε j) c) h)
    (hκ : min (κ (ε i)) h = min (κ (ε j)) h) (hσ : σ i = σ j ∨ h ≤ κ (ε j))
    (x : Fin (S.card + M)) :
    min (S.sheetRow k ε σ κ i x) h = min (S.sheetRow k ε σ κ j x) h := by
  induction x using Fin.addCases with
  | left d => rw [sheetRow_castAdd, sheetRow_castAdd]; exact hold d
  | right l =>
    rw [sheetRow_natAdd, sheetRow_natAdd, crossHeight, crossHeight, min_min_distrib,
      min_min_distrib (agreementHeight _ (ε j) _), hA (ε l), min_sheetCap_eq hκ hσ]

/-! ### The sheet layer -/

/-- **A cap respects capped agreement** of the catalogue entries: two entries that agree capped at
a cap `h` self-visible and short at `k` have caps that agree capped at `h`.  A constant cap
respects capped agreement. -/
def CapRespects (S : Scheme.{u} n) (k : ℕ) (κ : (Fin S.card → Label.{u}) → Label.{u}) : Prop :=
  ∀ a ∈ S.catalogue k, ∀ b ∈ S.catalogue k, ∀ h : Label.{u}, IsSelfVisible k h → IsShort k h →
    (∀ d, min (a d) h = min (b d) h) → min (κ a) h = min (κ b) h

/-- A constant cap respects capped agreement. -/
theorem capRespects_const (c : Label.{u}) : CapRespects S k fun _ ↦ c :=
  fun _ _ _ _ _ _ _ _ ↦ rfl

variable (S k ε σ κ) in
/-- **The sheet layer** at grade `k`: the cells of `S`, followed by `M` cells of scope `univ` and
grade `k`, the `i`-th with the sheet row of `i`. -/
noncomputable abbrev sheetLayer
    (hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d) : Scheme.{u} n :=
  S.appendFullCells k M (S.sheetRow k ε σ κ) hS

variable {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- The row of a new cell is its sheet row. -/
theorem sheetLayer_row_natAdd (i : Fin M) (t) :
    (S.sheetLayer k ε σ κ hS).rows.row (Fin.natAdd S.card i) t = S.sheetRow k ε σ κ i t.1 :=
  appendFullCells_row_natAdd i t

/-- **The sheet row of a cell is a lawful section of the sheet layer.**  On the old cells it is the
entry, lawful in `S`; at a new cell `i` its locality is the identity capped at the cross height
(`Scheme.min_sheetRow_eq`); availability at the full face holds at the cell itself, whose
diagonal entry is the ceiling of the grid. -/
theorem isLawful_sheetRow (hε : ∀ i, ε i ∈ S.catalogue k) (hκ : ∀ e, κ e ∈ S.fieldGrid k)
    (hκr : CapRespects S k κ) (j : Fin M) :
    (S.sheetLayer k ε σ κ hS).rows.IsLawful (S.sheetRow k ε σ κ j) := by
  have hG : (⊥ : Label.{u}) ∈ S.fieldGrid k := bot_mem_grid _ _
  refine isLawful_appendFullCells ?_ (fun i ↦ ?_) (fun i ↦ ?_) fun s _ ↦ ?_
  · convert (mem_catalogue.mp (hε j)).1 using 1
    exact funext fun d ↦ sheetRow_castAdd j d
  · rw [sheetRow_natAdd]
    exact isSelfVisible_of_mem_grid (crossHeight_mem_fieldGrid hκ j i)
  · set c := S.crossHeight k ε σ κ j i
    have hc := isSelfVisible_of_mem_grid (crossHeight_mem_fieldGrid (ε := ε) (σ := σ) hκ j i)
    -- the cross height is at most the agreement height of the two entries
    have hcA : c ≤ agreementHeight (S.fieldGrid k) (ε i) (ε j) := by
      rw [agreementHeight_comm]
      exact min_le_left _ _
    obtain ⟨hAG, hAs⟩ := agreementHeight_spec hG (ε i) (ε j)
    have hrow : ∀ x, min (S.sheetRow k ε σ κ i x) c = min (S.sheetRow k ε σ κ j x) c := by
      refine min_sheetRow_eq (fun d ↦ min_eq_min_of_le (hAs d) hcA) (fun e ↦ ?_) ?_ ?_
      · exact min_eq_min_of_le (agreementHeight_tri hG (ε i) (ε j) e) hcA
      · exact min_eq_min_of_le (hκr _ (hε i) _ (hε j) _ (isSelfVisible_of_mem_grid hAG)
          (isShort_of_mem_grid hAG) hAs) hcA
      · by_cases hij : σ i = σ j
        · exact .inl hij
        · refine .inr ?_
          change S.crossHeight k ε σ κ j i ≤ _
          rw [crossHeight_of_ne fun h ↦ hij h.symm]
          exact min_le_right _ _
    convert (TransformsTo.refl (fun t : (S.appendFullCellsScheme k M).below
      ((S.appendFullCellsScheme k M).gradedIndex (Fin.natAdd S.card i)) ↦
        (S.appendFullCellsScheme k M).grade t)
          fun t ↦ S.sheetRow k ε σ κ i t.1)
      |>.min_const (K := k) (fun t ↦ t.2.2.trans (appendFullCellsScheme_grade_natAdd S k _ i).le)
        hc using 1
    funext t
    rw [sheetRow_natAdd]
    exact (hrow t.1).symm
  · refine ⟨j, ?_⟩
    rw [sheetRow_natAdd, crossHeight_self]
    exact le_gridPoint_of_mem_codeGrid (sheetRow_mem_codeGrid hε hκ j s)

/-- **The sheet layer is consistent**: the old rows are those of `S`, and the new rows are lawful
sheet rows. -/
theorem isConsistent_sheetLayer (hcons : S.rows.IsConsistent) (hε : ∀ i, ε i ∈ S.catalogue k)
    (hκ : ∀ e, κ e ∈ S.fieldGrid k) (hκr : CapRespects S k κ) :
    (S.sheetLayer k ε σ κ hS).rows.IsConsistent :=
  isConsistent_appendFullCells hcons fun i ↦ isLawful_sheetRow hε hκ hκr i

/-- **The sheet layer is well formed.** -/
theorem isWellFormed_sheetLayer (hwf : S.IsWellFormed) (hk0 : 0 < k) (hkn : k ≤ n) :
    (S.sheetLayer k ε σ κ hS).IsWellFormed :=
  isWellFormed_appendFullCells hwf hk0 hkn

/-- **The sheet layer is coded**: the new rows take values in the code grid, below `ω ^ 2`. -/
theorem isCoded_sheetLayer (hc : S.IsCoded) (hε : ∀ i, ε i ∈ S.catalogue k)
    (hκ : ∀ e, κ e ∈ S.fieldGrid k) : (S.sheetLayer k ε σ κ hS).IsCoded :=
  isCoded_appendFullCells hc fun i x ↦
    lt_omega0_sq_of_mem_codeGrid (sheetRow_mem_codeGrid hε hκ i x)

/-- **The new rows are short at `k` and never the formal top.** -/
theorem isShort_ne_top_row_sheetLayer (hε : ∀ i, ε i ∈ S.catalogue k)
    (hκ : ∀ e, κ e ∈ S.fieldGrid k) (i : Fin M) (t) :
    IsShort k ((S.sheetLayer k ε σ κ hS).rows.row (Fin.natAdd S.card i) t) ∧
      (S.sheetLayer k ε σ κ hS).rows.row (Fin.natAdd S.card i) t ≠ ⊤ := by
  rw [sheetLayer_row_natAdd]
  exact ⟨isShort_of_mem_codeGrid (sheetRow_mem_codeGrid hε hκ i t.1),
    ne_top_of_mem_codeGrid (sheetRow_mem_codeGrid hε hκ i t.1)⟩

/-! ### Cells of the sheet layer -/

/-- An old cell of grade at most `k` lies below `(univ, k)` in the sheet layer. -/
theorem castAdd_mem_below_sheetLayer {d : Fin S.card} (hd : S.toCellScheme.grade d ≤ k) :
    Fin.castAdd M d ∈ (S.sheetLayer k ε σ κ hS).toCellScheme.below (univ, k) :=
  ⟨subset_univ _, (appendFullCellsScheme_grade_castAdd S k _ d).trans_le hd⟩

/-- A new cell lies below `(univ, k)` in the sheet layer. -/
theorem natAdd_mem_below_sheetLayer (i : Fin M) :
    Fin.natAdd S.card i ∈ (S.sheetLayer k ε σ κ hS).toCellScheme.below (univ, k) :=
  (appendFullCellsScheme_gradedIndex_natAdd S k _ i).le

variable (S k ε σ κ hS) in
/-- **`S` is a source prefix of its sheet layer** at every pair that is not above `(univ, k)`. -/
theorem isSourcePrefix_sheetLayer {Y : Finset (Fin n) × ℕ}
    (hY : ¬ ((univ : Finset (Fin n)), k) ≤ Y) :
    S.toCellScheme.IsSourcePrefix (S.sheetLayer k ε σ κ hS).toCellScheme (Fin.castAdd _) Y :=
  ⟨isLowerEmbedding_castAdd _ _ _ _, appendFullCellsScheme_scope_castAdd S k _,
    fun d hd ↦ ⟨⟨d, lt_card_of_mem_below hY hd⟩, rfl⟩⟩

/-- **The rows of the sheet layer pull back to those of `S`** along the old cells. -/
theorem comap_rows_sheetLayer :
    (S.sheetLayer k ε σ κ hS).rows.comap (isLowerEmbedding_castAdd k M _ hS) = S.rows :=
  comap_rows_castAdd

/-- A cell of the sheet layer of graded index `(univ, k)` is new. -/
theorem exists_natAdd_eq_sheetLayer {u : Fin (S.sheetLayer k ε σ κ hS).card}
    (hu : (S.sheetLayer k ε σ κ hS).toCellScheme.gradedIndex u = (univ, k)) :
    ∃ i, Fin.natAdd S.card i = u := by
  by_cases hlt : (u : ℕ) < S.card
  · refine absurd ?_ (hS ⟨u, hlt⟩)
    rw [← appendFullCellsScheme_gradedIndex_of_lt hlt]
    exact hu.ge
  · have hu' : (u : ℕ) < S.card + M := u.2
    exact ⟨⟨u - S.card, by omega⟩, Fin.ext (by simp; omega)⟩

/-- A cell of the sheet layer below a pair that is not above `(univ, k)` is old. -/
theorem exists_castAdd_eq_sheetLayer {X : Finset (Fin n) × ℕ}
    (hX : ¬ ((univ : Finset (Fin n)), k) ≤ X)
    {d : Fin (S.sheetLayer k ε σ κ hS).card}
    (hd : d ∈ (S.sheetLayer k ε σ κ hS).toCellScheme.below X) :
    ∃ e, Fin.castAdd _ e = d :=
  ⟨⟨d, lt_card_of_mem_below hX hd⟩, rfl⟩

/-! ### Extension through the new cells -/

/-- **Extension at the cap `⊥`, below `(univ, k)`**, by a template: every labelling `p` lawful
below `(univ, k)` in `S` extends, unchanged at the old cells of grade at most `k`, to a labelling
lawful below `(univ, k)` in the sheet layer, given a new cell `j₀` whose entry is the orbit code
`b` of the splice of `p`.  It is the sheet row of `j₀` read by the orbit decoder at the least grid
point. -/
theorem exists_isLawfulBelow_sheetLayer (hε : ∀ i, ε i ∈ S.catalogue k)
    (hκ : ∀ e, κ e ∈ S.fieldGrid k) (hκr : CapRespects S k κ) {p : Fin S.card → Label.{u}}
    {j₀ : Fin M} (hj₀ : ε j₀ = orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) p)) :
    ∃ r : (S.sheetLayer k ε σ κ hS).toCellScheme.below (univ, k) → Label.{u},
      (S.sheetLayer k ε σ κ hS).rows.IsLawfulBelow (univ, k) r ∧
        (∀ d (hd : S.toCellScheme.grade d ≤ k),
          r ⟨Fin.castAdd _ d, castAdd_mem_below_sheetLayer hd⟩ = p d) ∧
        ∀ x, r x = orbitDecoder k (S.toCellScheme.splice k (fun _ ↦ ⊥) p) (gridPoint k 0)
          (S.sheetRow k ε σ κ j₀ x) := by
  set t := S.toCellScheme.splice k (fun _ ↦ ⊥) p
  refine ⟨fun x ↦ orbitDecoder k t (gridPoint k 0) (S.sheetRow k ε σ κ j₀ x),
    ((isLawful_sheetRow (hS := hS) hε hκ hκr j₀).isLawfulBelow _).map_of_apply_eq_bot
      (fun x ↦ x.2.2)
      (isWitness_orbitDecoder (isSelfVisible_gridPoint k 0) (gridPoint_ne_bot k 0))
      fun _ ↦ eq_bot_of_orbitDecoder_eq_bot (gridPoint_ne_bot k 0), fun d hd ↦ ?_,
    fun _ ↦ rfl⟩
  -- The extension at the old cell `d` is the decoder applied to its code.
  change orbitDecoder k t (gridPoint k 0) (S.sheetRow k ε σ κ j₀ (Fin.castAdd _ d)) = p d
  rw [sheetRow_castAdd, hj₀, orbitDecoder_orbitCode (fun e ↦ min_orbitCode_gridPoint_zero e)]
  exact CellScheme.splice_of_le hd

/-- **Extension through the new cells at a short positive cap**, by a template.  Let `p` be lawful
below `(univ, k)` in `S`, `j` a new cell, and `h` self-visible and short at `k` with `⊥ < h`,
such that `p` agrees with the entry of `j` capped at `h` at the cells of grade at most `k`.  Let
`j₀` be a new cell whose entry is the orbit code `b` of the splice of `p`, in the sheet of `j` or
with `h` at most the cap of `j`.  Then some labelling lawful below `(univ, k)` in the sheet layer
reads `p` at the old cells of grade at most `k` and agrees with the sheet row of `j` capped at `h`
at every cell below `(univ, k)`.  It is the sheet row of `j₀` read by the orbit decoder at `h`:
relative room makes `b` agree with the entry of `j` capped at `h`, the agreement heights and caps
follow, and `Scheme.min_sheetRow_eq` gives the agreement of the two rows. -/
theorem exists_extension_sheetLayer (hε : ∀ i, ε i ∈ S.catalogue k)
    (hκ : ∀ e, κ e ∈ S.fieldGrid k) (hκr : CapRespects S k κ) {p : Fin S.card → Label.{u}}
    {j : Fin M} {h : Label.{u}}
    (hh : IsSelfVisible k h) (hs : IsShort k h) (hbot : ⊥ < h)
    (hag : ∀ d, S.toCellScheme.grade d ≤ k → min (p d) h = min (ε j d) h) {j₀ : Fin M}
    (hj₀ : ε j₀ = orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) p))
    (hσ : σ j₀ = σ j ∨ h ≤ κ (ε j)) :
    ∃ r : (S.sheetLayer k ε σ κ hS).toCellScheme.below (univ, k) → Label.{u},
      (S.sheetLayer k ε σ κ hS).rows.IsLawfulBelow (univ, k) r ∧
        (∀ d (hd : S.toCellScheme.grade d ≤ k),
          r ⟨Fin.castAdd _ d, castAdd_mem_below_sheetLayer hd⟩ = p d) ∧
          ∀ x, min (r x) h = min (S.sheetRow k ε σ κ j x) h := by
  set t := S.toCellScheme.splice k (fun _ ↦ ⊥) p with ht_def
  have htle (d : Fin S.card) (hd : S.toCellScheme.grade d ≤ k) : t d = p d :=
    CellScheme.splice_of_le hd
  have htgt (d : Fin S.card) (hd : ¬ S.toCellScheme.grade d ≤ k) : t d = ⊥ :=
    CellScheme.splice_of_lt (not_le.mp hd)
  set b := orbitCode k t
  set a := ε j
  have hb : b ∈ S.catalogue k := hj₀ ▸ hε j₀
  have ha : a ∈ S.catalogue k := hε j
  obtain ⟨-, haup, haa⟩ := mem_catalogue.mp ha
  -- The splice agrees with `a` capped at `h` at every cell.
  have hagt (d : Fin S.card) : min (t d) h = min (a d) h := by
    by_cases hd : S.toCellScheme.grade d ≤ k
    · rw [htle d hd]
      exact hag d hd
    · rw [htgt d hd, haup d (not_le.mp hd)]
  -- Relative room, and its transfer to the agreement heights and the caps.
  have hba (d : Fin S.card) : min (b d) h = min (a d) h := min_orbitCode_eq hh hs haa hagt d
  have hht (c : Fin S.card → Label.{u}) :
      min (agreementHeight (S.fieldGrid k) b c) h = min (agreementHeight (S.fieldGrid k) a c) h :=
    min_agreementHeight_eq_of_isShort hh hs
      (fun d ↦ ⟨codeGrid_mono (by omega) (mem_codeGrid_of_mem_catalogue hb d),
        codeGrid_mono (by omega) (mem_codeGrid_of_mem_catalogue ha d)⟩) hba c
  have hrowh (x : Fin (S.card + M)) :
      min (S.sheetRow k ε σ κ j₀ x) h = min (S.sheetRow k ε σ κ j x) h :=
    min_sheetRow_eq (fun d ↦ by rw [hj₀]; exact hba d) (fun c ↦ by rw [hj₀]; exact hht c)
      (by rw [hj₀]; exact hκr _ hb _ ha h hh hs hba) hσ x
  -- The decoder reads the old cells literally and keeps the cap at the cross heights.
  have hread (d : Fin S.card) : orbitDecoder k t h (b d) = t d :=
    orbitDecoder_orbitCode (fun e ↦ (hba e).trans (hagt e).symm) d
  have hcapr (x : Fin (S.card + M)) :
      min (orbitDecoder k t h (S.sheetRow k ε σ κ j₀ x)) h = min (S.sheetRow k ε σ κ j x) h := by
    induction x using Fin.addCases with
    | left d =>
      rw [sheetRow_castAdd, sheetRow_castAdd, hj₀, hread]
      exact hagt d
    | right l =>
      rw [min_orbitDecoder_eq (by
          rw [sheetRow_natAdd]
          exact isSelfVisible_of_mem_grid (crossHeight_mem_fieldGrid hκ j₀ l))]
      exact hrowh _
  refine ⟨fun x ↦ orbitDecoder k t h (S.sheetRow k ε σ κ j₀ x),
    ((isLawful_sheetRow (hS := hS) hε hκ hκr j₀).isLawfulBelow _).map_of_min_eq
      ((isLawful_sheetRow (hS := hS) hε hκ hκr j).isLawfulBelow _) (fun x ↦ x.2.2)
      (isWitness_orbitDecoder hh hbot.ne') hbot.ne' fun x ↦ hcapr x.1, fun d hd ↦ ?_,
    fun x ↦ hcapr x.1⟩
  -- The extension at the old cell `d` is the decoder applied to its code.
  change orbitDecoder k t h (S.sheetRow k ε σ κ j₀ (Fin.castAdd _ d)) = p d
  rw [sheetRow_castAdd, hj₀, hread, htle d hd]

/-! ### Extension from the boundary -/

variable {U V : Finset (Fin n) × ℕ}

/-- **The boundary labelling is lawful below `(univ, k)` in `S`**, as for the field layer. -/
theorem isLawfulBelow_castAdd_of_boundary_sheetLayer
    (hU : ¬ ((univ : Finset (Fin n)), k) ≤ U) (hV : ¬ ((univ : Finset (Fin n)), k) ≤ V)
    (hcover : ∀ d, S.toCellScheme.grade d ≤ k →
      S.toCellScheme.gradedIndex d ≤ U ∨ S.toCellScheme.gradedIndex d ≤ V)
    {w : Fin (S.sheetLayer k ε σ κ hS).card → Label.{u}}
    (hwU : (S.sheetLayer k ε σ κ hS).rows.IsLawfulBelow U (fun d ↦ w d))
    (hwV : (S.sheetLayer k ε σ κ hS).rows.IsLawfulBelow V (fun d ↦ w d)) :
    S.rows.IsLawfulBelow (univ, k) fun d ↦ w (Fin.castAdd _ d) :=
  CellScheme.Rows.IsLawfulBelow.glue (w := fun e ↦ w (Fin.castAdd _ e))
    ((isLawfulBelow_appendFullCells_iff hU).mp hwU)
    ((isLawfulBelow_appendFullCells_iff hV).mp hwV) fun d hd ↦ hcover d hd.2

/-- A boundary cell below `(univ, k)` is an old cell of grade at most `k`. -/
theorem exists_castAdd_eq_of_boundary_sheetLayer (hU : ¬ ((univ : Finset (Fin n)), k) ≤ U)
    (hV : ¬ ((univ : Finset (Fin n)), k) ≤ V)
    {d : (S.sheetLayer k ε σ κ hS).toCellScheme.below (univ, k)}
    (hd : (d : Fin (S.sheetLayer k ε σ κ hS).card) ∈
        (S.sheetLayer k ε σ κ hS).toCellScheme.below U ∨
      (d : Fin (S.sheetLayer k ε σ κ hS).card) ∈ (S.sheetLayer k ε σ κ hS).toCellScheme.below V) :
    ∃ e, ∃ he : S.toCellScheme.grade e ≤ k,
      d = ⟨Fin.castAdd _ e, castAdd_mem_below_sheetLayer he⟩ := by
  obtain ⟨e, he⟩ := hd.elim (exists_castAdd_eq_sheetLayer hU) (exists_castAdd_eq_sheetLayer hV)
  have hge : S.toCellScheme.grade e ≤ k := by
    have := d.2.2
    rw [← he] at this
    exact (appendFullCellsScheme_grade_castAdd S k _ e).symm.trans_le this
  exact ⟨e, hge, Subtype.ext he.symm⟩

/-- **Extension from the boundary at the cap `⊥`**, when every orbit code of a labelling lawful
below `(univ, k)` is the entry of a new cell. -/
theorem extendsFromBoundary_bot_sheetLayer (hε : ∀ i, ε i ∈ S.catalogue k)
    (hκ : ∀ e, κ e ∈ S.fieldGrid k) (hκr : CapRespects S k κ)
    (htemp : ∀ b ∈ S.catalogue k, ∃ j₀, ε j₀ = b)
    (hU : ¬ ((univ : Finset (Fin n)), k) ≤ U) (hV : ¬ ((univ : Finset (Fin n)), k) ≤ V)
    (hcover : ∀ d, S.toCellScheme.grade d ≤ k →
      S.toCellScheme.gradedIndex d ≤ U ∨ S.toCellScheme.gradedIndex d ≤ V) :
    (S.sheetLayer k ε σ κ hS).rows.ExtendsFromBoundary U V (univ, k) ⊥ fun _ ↦ ⊥ := by
  intro w hwU hwV _
  have hp := isLawfulBelow_castAdd_of_boundary_sheetLayer hU hV hcover hwU hwV
  obtain ⟨j₀, hj₀⟩ := htemp _
    (orbitCode_splice_bot_mem_catalogue (p := fun d ↦ w (Fin.castAdd _ d)) hp)
  obtain ⟨r, hr, hre, -⟩ := exists_isLawfulBelow_sheetLayer (hS := hS) (σ := σ) hε hκ hκr hj₀
  refine ⟨r, hr, fun d hd ↦ ?_, fun _ ↦ by simp⟩
  obtain ⟨e, he, rfl⟩ := exists_castAdd_eq_of_boundary_sheetLayer hU hV hd
  exact hre e he

/-- **Extension from the boundary through a sheet layer at a short positive cap, from a fill below
it**, along the row of a new cell `j`, given for every fill a template in the sheet of `j` or a cap
at most that of `j` (as `Scheme.extendsFromBoundary_fieldLayer_of_fill`). -/
theorem extendsFromBoundary_sheetLayer_of_fill (hε : ∀ i, ε i ∈ S.catalogue k)
    (hκ : ∀ e, κ e ∈ S.fieldGrid k) (hκr : CapRespects S k κ)
    (hU : ¬ ((univ : Finset (Fin n)), k) ≤ U) (hV : ¬ ((univ : Finset (Fin n)), k) ≤ V)
    (hUk : U.2 ≤ k) (hVk : V.2 ≤ k)
    {h : Label.{u}} (hh : IsSelfVisible k h) (hs : IsShort k h) (hbot : ⊥ < h)
    {u : Fin (S.sheetLayer k ε σ κ hS).card}
    (hu : (S.sheetLayer k ε σ κ hS).toCellScheme.gradedIndex u = (univ, k))
    (hfill : ∀ a ∈ S.catalogue k, ∀ w : Fin S.card → Label.{u},
      S.rows.IsLawfulBelow U (fun e ↦ w e) → S.rows.IsLawfulBelow V (fun e ↦ w e) →
      (∀ e, e ∈ S.toCellScheme.below U ∨ e ∈ S.toCellScheme.below V →
        min (w e) h = min (a e) h) →
      ∃ g : Fin S.card → Label.{u}, S.rows.IsLawfulBelow (univ, k) (fun e ↦ g e) ∧
        (∀ e, e ∈ S.toCellScheme.below U ∨ e ∈ S.toCellScheme.below V → g e = w e) ∧
        ∀ e ∈ S.toCellScheme.below (univ, k), min (g e) h = min (a e) h)
    (htemp : ∀ j, Fin.natAdd S.card j = u → ∀ g : Fin S.card → Label.{u},
      S.rows.IsLawfulBelow (univ, k) (fun e ↦ g e) →
      (∀ e ∈ S.toCellScheme.below (univ, k), min (g e) h = min (ε j e) h) →
      ∃ j₀, ε j₀ = orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) g) ∧
        (σ j₀ = σ j ∨ h ≤ κ (ε j))) :
    (S.sheetLayer k ε σ κ hS).rows.ExtendsFromBoundary U V (univ, k) h
      ((S.sheetLayer k ε σ κ hS).rows.rowBelow u hu) := by
  intro w hwU hwV hwS
  obtain ⟨j, rfl⟩ := exists_natAdd_eq_sheetLayer hu
  set a := ε j
  have ha : a ∈ S.catalogue k := hε j
  have hrowBelow (d : (S.sheetLayer k ε σ κ hS).toCellScheme.below (univ, k)) :
      (S.sheetLayer k ε σ κ hS).rows.rowBelow (Fin.natAdd _ j) hu d =
        S.sheetRow k ε σ κ j d.1 :=
    sheetLayer_row_natAdd (hS := hS) j _
  have hw₁U : S.rows.IsLawfulBelow U fun e ↦ w (Fin.castAdd _ e) :=
    (isLawfulBelow_appendFullCells_iff (S := S) (k := k) (h := hS) (v := w) hU).mp hwU
  have hw₁V : S.rows.IsLawfulBelow V fun e ↦ w (Fin.castAdd _ e) :=
    (isLawfulBelow_appendFullCells_iff (S := S) (k := k) (h := hS) (v := w) hV).mp hwV
  have hmem {X : Finset (Fin n) × ℕ} (e : Fin S.card) :
      Fin.castAdd M e ∈ (S.sheetLayer k ε σ κ hS).toCellScheme.below X ↔
        e ∈ S.toCellScheme.below X := by
    rw [CellScheme.mem_below, CellScheme.mem_below, appendFullCellsScheme_gradedIndex_castAdd]
  have hag (e : Fin S.card)
      (he : e ∈ S.toCellScheme.below U ∨ e ∈ S.toCellScheme.below V) :
      min (w (Fin.castAdd _ e)) h = min (a e) h := by
    have hle : S.toCellScheme.grade e ≤ k :=
      he.elim (fun h' ↦ h'.2.trans hUk) fun h' ↦ h'.2.trans hVk
    have := hwS ⟨_, castAdd_mem_below_sheetLayer (hS := hS) hle⟩
      (he.imp (hmem e).mpr (hmem e).mpr)
    rwa [hrowBelow, sheetRow_castAdd] at this
  obtain ⟨g, hg, hgw, hga⟩ := hfill a ha (fun e ↦ w (Fin.castAdd _ e)) hw₁U hw₁V hag
  obtain ⟨j₀, hj₀, hσ⟩ := htemp j rfl g hg hga
  obtain ⟨r, hr, hrg, hrS⟩ := exists_extension_sheetLayer (hS := hS) hε hκ hκr hh hs hbot
    (fun d hd ↦ hga d ⟨subset_univ _, hd⟩) hj₀ hσ
  refine ⟨r, hr, fun d hd ↦ ?_, fun d ↦ by rw [hrowBelow]; exact hrS d⟩
  obtain ⟨e, he, rfl⟩ := exists_castAdd_eq_of_boundary_sheetLayer (hS := hS) hU hV hd
  rw [hrg e he]
  exact hgw e (hd.imp (hmem e).mp (hmem e).mp)

/-! ### Leaves and marked cells -/

variable (S k) in
/-- The members of a set `Mk` of labellings of the old cells, in the order of `Finset.equivFin`. -/
noncomputable def markEntry (Mk : Finset (Fin S.card → Label.{u})) (m : Fin Mk.card) :
    Fin S.card → Label.{u} :=
  (Mk.equivFin.symm m).1

/-- A mark entry lies in its set. -/
theorem markEntry_mem (Mk : Finset (Fin S.card → Label.{u})) (m : Fin Mk.card) :
    S.markEntry Mk m ∈ Mk :=
  (Mk.equivFin.symm m).2

/-- Every member of `Mk` is a mark entry. -/
theorem exists_markEntry_eq {Mk : Finset (Fin S.card → Label.{u})} {e : Fin S.card → Label.{u}}
    (he : e ∈ Mk) : ∃ m, S.markEntry Mk m = e :=
  ⟨Mk.equivFin ⟨e, he⟩, by simp [markEntry]⟩

variable (S k) in
/-- The entries of the leaf-and-marked layer: the catalogue entries (the leaves), then the members
of `Mk` (the marked cells). -/
noncomputable def markedEntry (Mk : Finset (Fin S.card → Label.{u})) :
    Fin ((S.catalogue k).card + Mk.card) → Fin S.card → Label.{u} :=
  Fin.append (S.catalogueEntry k) (S.markEntry Mk)

/-- The sheets of the leaf-and-marked layer: `false` at the leaves, `true` at the marked cells. -/
def markedSheet (C m : ℕ) : Fin (C + m) → Bool :=
  Fin.append (fun _ ↦ false) fun _ ↦ true

@[simp] theorem markedEntry_castAdd (Mk : Finset (Fin S.card → Label.{u}))
    (i : Fin (S.catalogue k).card) :
    S.markedEntry k Mk (Fin.castAdd Mk.card i) = S.catalogueEntry k i :=
  Fin.append_left _ _ i

@[simp] theorem markedEntry_natAdd (Mk : Finset (Fin S.card → Label.{u})) (m : Fin Mk.card) :
    S.markedEntry k Mk (Fin.natAdd (S.catalogue k).card m) = S.markEntry Mk m :=
  Fin.append_right _ _ m

@[simp] theorem markedSheet_castAdd {C m : ℕ} (i : Fin C) :
    markedSheet C m (Fin.castAdd m i) = false :=
  Fin.append_left _ _ i

@[simp] theorem markedSheet_natAdd {C m : ℕ} (i : Fin m) :
    markedSheet C m (Fin.natAdd C i) = true :=
  Fin.append_right _ _ i

/-- The entries of the leaf-and-marked layer lie in the catalogue when `Mk` does. -/
theorem markedEntry_mem {Mk : Finset (Fin S.card → Label.{u})} (hMk : Mk ⊆ S.catalogue k)
    (i : Fin ((S.catalogue k).card + Mk.card)) : S.markedEntry k Mk i ∈ S.catalogue k := by
  induction i using Fin.addCases with
  | left i => rw [markedEntry_castAdd]; exact catalogueEntry_mem i
  | right m => rw [markedEntry_natAdd]; exact hMk (markEntry_mem Mk m)

variable (S k) in
/-- **The leaf-and-marked layer** at grade `k`: a leaf for every entry of the canonical catalogue
and a marked cell for every member of `Mk`, the cross readings of leaves and marked cells capped by
`κ`. -/
noncomputable abbrev markedLayer (Mk : Finset (Fin S.card → Label.{u}))
    (κ : (Fin S.card → Label.{u}) → Label.{u})
    (hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d) : Scheme.{u} n :=
  S.sheetLayer k (S.markedEntry k Mk) (markedSheet _ _) κ hS

/-- **Every marked cell reads the old cells by its member of `Mk`.** -/
theorem markedLayer_row_mark_castAdd {Mk : Finset (Fin S.card → Label.{u})} (m : Fin Mk.card)
    (d : Fin S.card) :
    S.sheetRow k (S.markedEntry k Mk) (markedSheet _ _) κ (Fin.natAdd _ m) (Fin.castAdd _ d) =
      S.markEntry Mk m d := by
  rw [sheetRow_castAdd, markedEntry_natAdd]

/-- **A predicate on the reading of the old cells holds at every marked cell** when it holds on
`Mk`. -/
theorem markedLayer_mark_reads {Mk : Finset (Fin S.card → Label.{u})}
    {P : (Fin S.card → Label.{u}) → Prop} (hP : ∀ e ∈ Mk, P e) (m : Fin Mk.card) :
    P fun d ↦
      S.sheetRow k (S.markedEntry k Mk) (markedSheet _ _) κ (Fin.natAdd _ m) (Fin.castAdd _ d) := by
  simp only [markedLayer_row_mark_castAdd]
  exact hP _ (markEntry_mem Mk m)

/-- Every catalogue entry is the entry of a leaf. -/
theorem exists_leaf_eq {Mk : Finset (Fin S.card → Label.{u})} {b : Fin S.card → Label.{u}}
    (hb : b ∈ S.catalogue k) :
    ∃ j₀, S.markedEntry k Mk j₀ = b ∧ markedSheet _ Mk.card j₀ = false := by
  obtain ⟨i, rfl⟩ := exists_catalogueEntry_eq hb
  exact ⟨Fin.castAdd _ i, markedEntry_castAdd Mk i, markedSheet_castAdd i⟩

/-- Every member of `Mk` is the entry of a marked cell. -/
theorem exists_mark_eq {Mk : Finset (Fin S.card → Label.{u})} {b : Fin S.card → Label.{u}}
    (hb : b ∈ Mk) :
    ∃ j₀, S.markedEntry k Mk j₀ = b ∧ markedSheet (S.catalogue k).card Mk.card j₀ = true := by
  obtain ⟨m, rfl⟩ := exists_markEntry_eq hb
  exact ⟨Fin.natAdd _ m, markedEntry_natAdd Mk m, markedSheet_natAdd m⟩

/-- **Marked closure**: a catalogue entry that agrees with a member `e` of `Mk` capped at a short
positive cap above the cap of `e` lies in `Mk`.  It is what a lift along a marked cell above its
cap asks; at the caps at most the cap the leaves serve. -/
def MarkedClosed (S : Scheme.{u} n) (k : ℕ) (Mk : Finset (Fin S.card → Label.{u}))
    (κ : (Fin S.card → Label.{u}) → Label.{u}) : Prop :=
  ∀ e ∈ Mk, ∀ b ∈ S.catalogue k, ∀ h : Label.{u}, IsSelfVisible k h → IsShort k h → ⊥ < h →
    ¬ h ≤ κ e → (∀ d, min (b d) h = min (e d) h) → b ∈ Mk

/-- **Templates in the leaf-and-marked layer.**  For a lift along the new cell `j` at a short
positive cap `h` of a labelling `g` lawful below `(univ, k)` that agrees with the entry of `j`
capped at `h`, the orbit code of the splice of `g` is the entry of a new cell in the sheet of `j`
or `h` is at most the cap of `j`: a leaf along a leaf or at a cap at most the cap, and a marked
cell by marked closure otherwise. -/
theorem exists_template_markedLayer {Mk : Finset (Fin S.card → Label.{u})}
    (hMk : Mk ⊆ S.catalogue k) (hcl : MarkedClosed S k Mk κ) {h : Label.{u}}
    (hh : IsSelfVisible k h) (hs : IsShort k h) (hbot : ⊥ < h)
    (j : Fin ((S.catalogue k).card + Mk.card)) {g : Fin S.card → Label.{u}}
    (hg : S.rows.IsLawfulBelow (univ, k) fun e ↦ g e)
    (hga : ∀ e ∈ S.toCellScheme.below (univ, k), min (g e) h = min (S.markedEntry k Mk j e) h) :
    ∃ j₀, S.markedEntry k Mk j₀ = orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) g) ∧
      (markedSheet _ _ j₀ = markedSheet _ _ j ∨ h ≤ κ (S.markedEntry k Mk j)) := by
  set t := S.toCellScheme.splice k (fun _ ↦ ⊥) g
  have hb : orbitCode k t ∈ S.catalogue k := orbitCode_splice_bot_mem_catalogue hg
  induction j using Fin.addCases with
  | left i =>
    obtain ⟨j₀, hj₀, hσ⟩ := exists_leaf_eq (Mk := Mk) hb
    exact ⟨j₀, hj₀, .inl (by rw [hσ, markedSheet_castAdd])⟩
  | right m =>
    by_cases hκm : h ≤ κ (S.markedEntry k Mk (Fin.natAdd _ m))
    · obtain ⟨j₀, hj₀, -⟩ := exists_leaf_eq (Mk := Mk) hb
      exact ⟨j₀, hj₀, .inr hκm⟩
    -- Above the cap, the orbit code lies in `Mk` by marked closure.
    set e := S.markedEntry k Mk (Fin.natAdd _ m) with he_def
    have he : e ∈ Mk := by rw [he_def, markedEntry_natAdd]; exact markEntry_mem Mk m
    obtain ⟨-, heup, hee⟩ := mem_catalogue.mp (hMk he)
    have hagt (d : Fin S.card) : min (t d) h = min (e d) h := by
      by_cases hd : S.toCellScheme.grade d ≤ k
      · have htd : t d = g d := CellScheme.splice_of_le hd
        rw [htd]
        exact hga d ⟨subset_univ _, hd⟩
      · have htd : t d = ⊥ := CellScheme.splice_of_lt (not_le.mp hd)
        rw [htd, heup d (not_le.mp hd)]
    have hba (d : Fin S.card) : min (orbitCode k t d) h = min (e d) h :=
      min_orbitCode_eq hh hs hee hagt d
    obtain ⟨j₀, hj₀, hσ⟩ := exists_mark_eq (k := k) (hcl e he _ hb h hh hs hbot hκm hba)
    exact ⟨j₀, hj₀, .inl (by rw [hσ, markedSheet_natAdd])⟩

end VaughtConjecture.Scheme

/-! ### A separating fill in a sheet layer -/

namespace VaughtConjecture.Scheme

open Finset Label

variable {n k M : ℕ} {S : Scheme.{u} n} {ε : Fin M → Fin S.card → Label.{u}}
  {σ : Fin M → Bool} {κ : (Fin S.card → Label.{u}) → Label.{u}}
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- **A separating fill forces a top reading the marker above `x` in a sheet layer.**  Let `q` be a
lawful section of a sheet layer, `j` a new cell labelled `⊤` whose entry has `ε j r ≤ ε j x`, with
`r` an old cell of grade `k` labelled `⊤`, `x` one of grade at most `k`, and `ε j r ≠ ⊥`.
Given a fill `p` of the old cells agreeing with `ε j` capped at `ε j r` at the cells of grade at
most `k`, with `p x < p r`, and a template for the lift along `j` at that cap, some new cell `j''`
labelled `⊤` has `ε j'' x < ε j'' r`. -/
theorem exists_top_sheetRow_lt (hε : ∀ i, ε i ∈ S.catalogue k) (hκ : ∀ e, κ e ∈ S.fieldGrid k)
    (hκr : CapRespects S k κ) {q : Fin (S.sheetLayer k ε σ κ hS).card → Label.{u}}
    (hq : (S.sheetLayer k ε σ κ hS).rows.IsLawful q) {j : Fin M} {x r : Fin S.card}
    (hgr : S.toCellScheme.grade r = k) (hgx : S.toCellScheme.grade x ≤ k)
    (hqj : q (Fin.natAdd S.card j) = ⊤) (hqr : q (Fin.castAdd M r) = ⊤)
    (hread : ε j r ≤ ε j x) (hτ : ⊥ < ε j r) {p : Fin S.card → Label.{u}}
    (hag : ∀ d, S.toCellScheme.grade d ≤ k → min (p d) (ε j r) = min (ε j d) (ε j r))
    (hlt : p x < p r) {j₀ : Fin M}
    (hj₀ : ε j₀ = orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) p))
    (hσ : σ j₀ = σ j ∨ ε j r ≤ κ (ε j)) :
    ∃ j'', q (Fin.natAdd S.card j'') = ⊤ ∧ ε j'' x < ε j'' r := by
  set τ := ε j r
  have hh : IsSelfVisible k τ := by
    have h := (mem_catalogue.mp (hε j)).1.orderly r
    rwa [hgr] at h
  have hs : IsShort k τ := isShort_of_mem_codeGrid (mem_codeGrid_of_mem_catalogue (hε j) r)
  obtain ⟨w₀, hw₀, hw₀p, hw₀S⟩ := exists_extension_sheetLayer (hS := hS) hε hκ hκr hh hs hτ hag
    hj₀ hσ
  have hb : (S.sheetLayer k ε σ κ hS).toCellScheme.gradedIndex (Fin.natAdd S.card j) =
      ((univ : Finset (Fin n)), k) :=
    appendFullCellsScheme_gradedIndex_natAdd S k _ j
  have hmem (y : Fin (S.sheetLayer k ε σ κ hS).card)
      (hy : y ∈ (S.sheetLayer k ε σ κ hS).toCellScheme.below
        ((S.sheetLayer k ε σ κ hS).toCellScheme.gradedIndex (Fin.natAdd S.card j))) :
      y ∈ (S.sheetLayer k ε σ κ hS).toCellScheme.below (univ, k) := hb ▸ hy
  have hxb : Fin.castAdd M x ∈ (S.sheetLayer k ε σ κ hS).toCellScheme.below
      ((S.sheetLayer k ε σ κ hS).toCellScheme.gradedIndex (Fin.natAdd S.card j)) := by
    rw [hb]
    exact castAdd_mem_below_sheetLayer hgx
  have hrb : Fin.castAdd M r ∈ (S.sheetLayer k ε σ κ hS).toCellScheme.below
      ((S.sheetLayer k ε σ κ hS).toCellScheme.gradedIndex (Fin.natAdd S.card j)) := by
    rw [hb]
    exact castAdd_mem_below_sheetLayer hgr.le
  set w := CellScheme.Rows.extendBot ((univ : Finset (Fin n)), k) w₀
  have hwy (y) (hy : y ∈ (S.sheetLayer k ε σ κ hS).toCellScheme.below (univ, k)) :
      w y = w₀ ⟨y, hy⟩ := CellScheme.Rows.extendBot_of_mem w₀ hy
  have hw : (S.sheetLayer k ε σ κ hS).rows.IsLawfulBelow
      ((S.sheetLayer k ε σ κ hS).toCellScheme.gradedIndex (Fin.natAdd S.card j))
      fun d ↦ w d := by
    rw [hb]
    exact CellScheme.Rows.isLawfulBelow_extendBot.mpr hw₀
  have hrowj (y) (hy) : (S.sheetLayer k ε σ κ hS).rows.row (Fin.natAdd S.card j) ⟨y, hy⟩ =
      S.sheetRow k ε σ κ j y := sheetLayer_row_natAdd j _
  obtain ⟨v, hxv, hrv, hv, hqv, hlt'⟩ := hq.exists_top_row_lt hxb hrb
    (by rw [appendFullCellsScheme_grade_castAdd, appendFullCellsScheme_grade_natAdd, hgr])
    (by rw [appendFullCellsScheme_grade_castAdd, appendFullCellsScheme_grade_castAdd, hgr]
        exact hgx)
    hqj hqr (by rw [hrowj, hrowj, sheetRow_castAdd, sheetRow_castAdd]; exact hread) hw
    (fun y hy ↦ by
      rw [hrowj, hrowj, sheetRow_castAdd, hwy y (hmem y hy)]
      exact hw₀S _)
    (by
      rw [hwy _ (hmem _ hxb), hwy _ (hmem _ hrb), hw₀p x hgx, hw₀p r hgr.le]
      exact hlt)
  obtain ⟨j'', rfl⟩ := exists_natAdd_eq_sheetLayer (hb ▸ hv : _ = ((univ : Finset (Fin n)), k))
  refine ⟨j'', hqv, ?_⟩
  rwa [sheetLayer_row_natAdd, sheetLayer_row_natAdd, sheetRow_castAdd, sheetRow_castAdd] at hlt'

end VaughtConjecture.Scheme

/-! ### A marked cell read as `⊥` at every leaf -/

namespace VaughtConjecture.Scheme

open Finset Label CellScheme

variable {n k : ℕ} {S : Scheme.{u} n} {Mk : Finset (Fin S.card → Label.{u})}
  {κ : (Fin S.card → Label.{u}) → Label.{u}}
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- **A marked cell whose row is `⊥` at every leaf has cap `⊥`.**  The leaf with the entry of the
marked cell is read at the cross height `min (agreement height) (cap)`, and the agreement height of
an entry with itself is the top point `gridPoint k (2 * S.card + 2)` of the field grid, above every
cap in the field grid. -/
theorem markedLayer_cap_eq_bot_of_row_leaf (hMk : Mk ⊆ S.catalogue k)
    (hκ : ∀ e, κ e ∈ S.fieldGrid k) (m : Fin Mk.card)
    (hleaf : ∀ (i : Fin (S.catalogue k).card) (t), (S.markedLayer k Mk κ hS).rows.row
      (Fin.natAdd S.card (Fin.natAdd _ m)) t = ⊥ ∨
        t.1 ≠ Fin.natAdd S.card (Fin.castAdd Mk.card i)) :
    κ (S.markEntry Mk m) = ⊥ := by
  obtain ⟨j₀, hj₀, hσ⟩ := exists_leaf_eq (Mk := Mk) (hMk (markEntry_mem Mk m))
  obtain ⟨i, rfl⟩ : ∃ i, Fin.castAdd Mk.card i = j₀ := by
    induction j₀ using Fin.addCases with
    | left i => exact ⟨i, rfl⟩
    | right m' => rw [markedSheet_natAdd] at hσ; exact absurd hσ (by decide)
  have hmem : Fin.natAdd S.card (Fin.castAdd Mk.card i) ∈
      (S.markedLayer k Mk κ hS).toCellScheme.below
        ((S.markedLayer k Mk κ hS).toCellScheme.gradedIndex
          (Fin.natAdd S.card (Fin.natAdd _ m))) := by
    rw [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_natAdd,
      appendFullCellsScheme_gradedIndex_natAdd]
  rcases hleaf i ⟨_, hmem⟩ with h | h
  · rw [sheetLayer_row_natAdd, sheetRow_natAdd, crossHeight_of_ne (by simp), hj₀,
      markedEntry_natAdd, agreementHeight_self (gridPoint_mem_grid le_rfl)
        fun x hx ↦ le_gridPoint_of_mem_grid hx,
      min_eq_right (le_gridPoint_of_mem_grid (hκ _))] at h
    exact h
  · exact absurd rfl h

/-- **A marked cell that reads only marked cells has cap `⊥`**: its row is `⊥` at every leaf
(`Scheme.markedLayer_cap_eq_bot_of_row_leaf`). -/
theorem markedLayer_cap_eq_bot_of_readsOnly (hMk : Mk ⊆ S.catalogue k)
    (hκ : ∀ e, κ e ∈ S.fieldGrid k) (m : Fin Mk.card) {T : Set (Fin (S.markedLayer k Mk κ hS).card)}
    (honly : (S.markedLayer k Mk κ hS).rows.ReadsOnly (Fin.natAdd S.card (Fin.natAdd _ m)) T)
    (hT : ∀ i : Fin (S.catalogue k).card, Fin.natAdd S.card (Fin.castAdd Mk.card i) ∉ T) :
    κ (S.markEntry Mk m) = ⊥ := by
  refine markedLayer_cap_eq_bot_of_row_leaf (hS := hS) hMk hκ m fun i t ↦ ?_
  by_cases ht : t.1 = Fin.natAdd S.card (Fin.castAdd Mk.card i)
  · left
    have hgi : (S.markedLayer k Mk κ hS).toCellScheme.gradedIndex t.1 =
        (S.markedLayer k Mk κ hS).toCellScheme.gradedIndex
          (Fin.natAdd S.card (Fin.natAdd _ m)) := by
      rw [ht, appendFullCellsScheme_gradedIndex_natAdd, appendFullCellsScheme_gradedIndex_natAdd]
    have hne : t.1 ≠ Fin.natAdd S.card (Fin.natAdd _ m) := by
      rw [ht]
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    have h := honly t.1 hgi hne (ht ▸ hT i)
    exact (S.markedLayer k Mk κ hS).rows.row_congr rfl rfl |>.trans h
  · exact .inr ht

/-- **A marked cell of cap `⊥` is `⊥` in a lawful extension of every labelling**: every labelling
`p` lawful below `(univ, k)` in `S` extends, unchanged at the old cells of grade at most `k`, to a
labelling lawful below `(univ, k)` in the leaf-and-marked layer that is `⊥` at the marked cell.  It
is the extension at `⊥` through the leaf of the orbit code of the splice of `p`. -/
theorem exists_isLawfulBelow_markedLayer_eq_bot (hMk : Mk ⊆ S.catalogue k)
    (hκ : ∀ e, κ e ∈ S.fieldGrid k) (hκr : CapRespects S k κ) (m : Fin Mk.card)
    (hm : κ (S.markEntry Mk m) = ⊥) {p : Fin S.card → Label.{u}}
    (hp : S.rows.IsLawfulBelow (univ, k) fun d ↦ p d) :
    ∃ r : (S.markedLayer k Mk κ hS).toCellScheme.below (univ, k) → Label.{u},
      (S.markedLayer k Mk κ hS).rows.IsLawfulBelow (univ, k) r ∧
        (∀ d (hd : S.toCellScheme.grade d ≤ k),
          r ⟨Fin.castAdd _ d, castAdd_mem_below_sheetLayer hd⟩ = p d) ∧
        r ⟨Fin.natAdd S.card (Fin.natAdd _ m), natAdd_mem_below_sheetLayer _⟩ = ⊥ := by
  set b := orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) p)
  have hb : b ∈ S.catalogue k := orbitCode_splice_bot_mem_catalogue hp
  obtain ⟨j₀, hj₀, hσ⟩ := exists_leaf_eq (Mk := Mk) hb
  obtain ⟨r, hr, hrp, hrx⟩ := exists_isLawfulBelow_sheetLayer (hS := hS)
    (markedEntry_mem hMk) hκ hκr (σ := markedSheet _ _) hj₀
  refine ⟨r, hr, hrp, ?_⟩
  rw [hrx, sheetRow_natAdd, crossHeight_of_ne (by rw [hσ, markedSheet_natAdd]; decide), hj₀,
    markedEntry_natAdd]
  -- the cross height of the leaf and the marked cell is `⊥`
  set e := S.markEntry Mk m
  have he : e ∈ S.catalogue k := hMk (markEntry_mem Mk m)
  obtain ⟨hA, hAag⟩ := agreementHeight_spec (bot_mem_grid k (2 * S.card + 2)) b e
  have hcross : min (agreementHeight (S.fieldGrid k) b e) (κ b) = ⊥ := by
    rcases eq_or_ne (agreementHeight (S.fieldGrid k) b e) ⊥ with h0 | h0
    · rw [h0]
      exact min_eq_left bot_le
    have hcap := hκr b hb e he _ (isSelfVisible_of_mem_grid hA) (isShort_of_mem_grid hA) hAag
    rw [hm, min_bot_left, min_comm] at hcap
    exact hcap
  rw [hcross]
  exact orbitDecoder_bot

end VaughtConjecture.Scheme
