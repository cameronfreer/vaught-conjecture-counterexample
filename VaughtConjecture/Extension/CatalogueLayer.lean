/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.FieldLayer

/-!
# A layer of full-scope cells over an arbitrary catalogue

Roadmap, Layer 3 (the controller layers of the growth and LOW constructions).

Let `S` be a scheme on `n` points with no cell above `(univ, k)`, `F` a finite type of **fields**
with a map `read : Fin S.card → F` from the cells of `S`, `G` a finite set of labels, and `C` a
finite **catalogue** of labellings of the fields.  The **catalogue layer**
(`Scheme.catalogueLayer S k read G C hS`) appends to `S` one cell of scope `univ` and grade `k`
for each entry `a` of `C`, whose row (`Scheme.layerRow`) reads `a ∘ read` on the old cells and,
at the new cell of an entry `b`, the agreement height of `a` and `b` in `G`.  This is the field
row of `VaughtConjecture.Extension.FieldLayer` over any catalogue and any fields: the cells of `S`
(`read` the identity) for the activation layer of the growth construction, and the cells of `S`
with a cutoff (`read = Sum.inl`) for the LOW layer.

## Main statements

* `Scheme.isLawful_layerRow`, `Scheme.isConsistent_catalogueLayer`: the row of an entry lawful on
  the old cells, bounded by the largest member of `G`, is a lawful section of the layer; so the
  layer is consistent when every entry is.
* `Scheme.isWellFormed_catalogueLayer`, `Scheme.isCoded_catalogueLayer`: well formed, and coded
  when the entries and `G` lie below `ω ^ 2`.
* `Scheme.exists_gradedIndex_eq_catalogueLayer`: completeness at `(univ, k)` for a nonempty
  catalogue.
* `Scheme.exists_eq_natAdd_of_gradedIndex_catalogueLayer`: the cells at `(univ, k)` are exactly
  the new cells; `Scheme.rowAt_catalogueLayer_castAdd`: a new cell reads its entry at the old
  cells of grade at most `k`.

## References

Agreement heights and field rows are those of the coatom extension construction [Kni26, §4.4].
-/

universe u

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} (S : Scheme.{u} n) (k : ℕ) {F : Type*} (read : Fin S.card → F)
  (G : Finset Label.{u}) (C : Finset (F → Label.{u}))

/-- The entry of the `i`-th new cell. -/
noncomputable def layerEntry (i : Fin C.card) : F → Label.{u} :=
  (C.equivFin.symm i).1

variable {C} in
theorem layerEntry_mem (i : Fin C.card) : layerEntry C i ∈ C := (C.equivFin.symm i).2

variable {C} in
theorem exists_layerEntry_eq {a : F → Label.{u}} (ha : a ∈ C) : ∃ i, layerEntry C i = a :=
  ⟨C.equivFin ⟨a, ha⟩, by simp [layerEntry]⟩

variable [Fintype F]

/-- The **layer row** of an entry `a`: `a ∘ read` on the old cells, and on the new cell of an
entry `b` the agreement height of `a` and `b` in `G`. -/
noncomputable def layerRow (a : F → Label.{u}) : Fin (S.card + C.card) → Label.{u} :=
  Fin.append (fun d ↦ a (read d)) fun j ↦ agreementHeight G a (layerEntry C j)

variable {S read G C}

@[simp] theorem layerRow_castAdd (a : F → Label.{u}) (d : Fin S.card) :
    layerRow S read G C a (Fin.castAdd _ d) = a (read d) :=
  Fin.append_left _ _ d

@[simp] theorem layerRow_natAdd (a : F → Label.{u}) (j : Fin C.card) :
    layerRow S read G C a (Fin.natAdd _ j) = agreementHeight G a (layerEntry C j) :=
  Fin.append_right _ _ j

variable (S read G C) in
/-- **The catalogue layer**: `S` with one cell of scope `univ` and grade `k` for each entry of
`C`, whose row is the layer row of the entry. -/
noncomputable abbrev catalogueLayer
    (hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d) : Scheme.{u} n :=
  S.appendFullCells k C.card (fun i ↦ layerRow S read G C (layerEntry C i)) hS

variable {k} {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- **Two layer rows agree capped at the agreement height of their entries.** -/
theorem min_layerRow_agreementHeight (hG : ⊥ ∈ G) (a b : F → Label.{u})
    (x : Fin (S.card + C.card)) :
    min (layerRow S read G C a x) (agreementHeight G a b) =
      min (layerRow S read G C b x) (agreementHeight G a b) := by
  induction x using Fin.addCases with
  | left d =>
    rw [layerRow_castAdd, layerRow_castAdd]
    exact (agreementHeight_spec hG a b).2 _
  | right j =>
    rw [layerRow_natAdd, layerRow_natAdd]
    exact agreementHeight_tri hG a b _

/-- **The layer row of an entry is a lawful section of the layer**, for an entry `a` of `C` with
`a ∘ read` lawful on the old cells, when `⊥ ∈ G`, the members of `G` are self-visible at `k`, and
some member `y` of `G` lies above every member of `G` and every value of `a`. -/
theorem isLawful_layerRow (hG : ⊥ ∈ G) (hvis : ∀ x ∈ G, IsSelfVisible k x) {y : Label.{u}}
    (hy : y ∈ G) (hmax : ∀ x ∈ G, x ≤ y) {a : F → Label.{u}} (ha : a ∈ C)
    (hlaw : S.rows.IsLawful fun d ↦ a (read d)) (hay : ∀ f, a f ≤ y) :
    (S.catalogueLayer k read G C hS).rows.IsLawful (layerRow S read G C a) := by
  refine isLawful_appendFullCells ?_ (fun i ↦ ?_) (fun i ↦ ?_) fun s _ ↦ ?_
  · convert hlaw using 1
    exact funext fun d ↦ layerRow_castAdd a d
  · rw [layerRow_natAdd]
    exact hvis _ (agreementHeight_spec hG _ _).1
  · have hc := hvis _ (agreementHeight_spec hG a (layerEntry C i)).1
    convert (TransformsTo.refl (fun t : (S.appendFullCellsScheme k C.card).below
      ((S.appendFullCellsScheme k C.card).gradedIndex (Fin.natAdd S.card i)) ↦
        (S.appendFullCellsScheme k C.card).grade t)
          fun t ↦ layerRow S read G C (layerEntry C i) t.1)
      |>.min_const (K := k) (fun t ↦ t.2.2.trans (appendFullCellsScheme_grade_natAdd S k _ i).le)
        hc using 1
    funext t
    rw [layerRow_natAdd]
    exact min_layerRow_agreementHeight hG a _ t.1
  · obtain ⟨i, hi⟩ := exists_layerEntry_eq ha
    refine ⟨i, ?_⟩
    rw [layerRow_natAdd, hi, agreementHeight_self hy hmax]
    induction s using Fin.addCases with
    | left d => rw [layerRow_castAdd]; exact hay _
    | right j => rw [layerRow_natAdd]; exact hmax _ (agreementHeight_spec hG _ _).1

/-- **The catalogue layer is consistent**, under the hypotheses of `Scheme.isLawful_layerRow` for
every entry of `C`. -/
theorem isConsistent_catalogueLayer (hcons : S.rows.IsConsistent) (hG : ⊥ ∈ G)
    (hvis : ∀ x ∈ G, IsSelfVisible k x) {y : Label.{u}} (hy : y ∈ G) (hmax : ∀ x ∈ G, x ≤ y)
    (hC : ∀ a ∈ C, S.rows.IsLawful (fun d ↦ a (read d)) ∧ ∀ f, a f ≤ y) :
    (S.catalogueLayer k read G C hS).rows.IsConsistent :=
  isConsistent_appendFullCells hcons fun i ↦ isLawful_layerRow hG hvis hy hmax
    (layerEntry_mem i) (hC _ (layerEntry_mem i)).1 (hC _ (layerEntry_mem i)).2

/-- **The catalogue layer is well formed** when `(univ, k)` is a graded face. -/
theorem isWellFormed_catalogueLayer (hwf : S.IsWellFormed) (hk0 : 0 < k) (hkn : k ≤ n) :
    (S.catalogueLayer k read G C hS).IsWellFormed :=
  isWellFormed_appendFullCells hwf hk0 hkn

/-- **The catalogue layer is coded** when the entries and `G` lie below `ω ^ 2`. -/
theorem isCoded_catalogueLayer (hc : S.IsCoded) (hG : ⊥ ∈ G)
    (hGω : ∀ x ∈ G, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hCω : ∀ a ∈ C, ∀ f, a f < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})) :
    (S.catalogueLayer k read G C hS).IsCoded :=
  isCoded_appendFullCells hc fun i x ↦ by
    induction x using Fin.addCases with
    | left d => rw [layerRow_castAdd]; exact hCω _ (layerEntry_mem i) _
    | right j => rw [layerRow_natAdd]; exact hGω _ (agreementHeight_spec hG _ _).1

/-- **Completeness at the layer**: for a nonempty catalogue, `(univ, k)` is the graded index of a
new cell. -/
theorem exists_gradedIndex_eq_catalogueLayer (hC : C.Nonempty) :
    ∃ s, (S.catalogueLayer k read G C hS).toCellScheme.gradedIndex s = (univ, k) := by
  obtain ⟨a, ha⟩ := hC
  obtain ⟨i, -⟩ := exists_layerEntry_eq ha
  exact ⟨Fin.natAdd S.card i, appendFullCellsScheme_gradedIndex_natAdd S k _ i⟩

/-- **The cells at `(univ, k)` are the new cells.** -/
theorem exists_eq_natAdd_of_gradedIndex_catalogueLayer {s : Fin (S.card + C.card)}
    (hs : (S.catalogueLayer k read G C hS).toCellScheme.gradedIndex s = (univ, k)) :
    ∃ i, s = Fin.natAdd S.card i := by
  induction s using Fin.addCases with
  | left d =>
    exact absurd (by rw [appendFullCellsScheme_gradedIndex_castAdd] at hs; rw [hs]) (hS d)
  | right i => exact ⟨i, rfl⟩

/-- **A new cell reads its entry** at every old cell of grade at most `k`. -/
theorem rowAt_catalogueLayer_castAdd (i : Fin C.card) {d : Fin S.card}
    (hd : S.toCellScheme.grade d ≤ k) :
    (S.catalogueLayer k read G C hS).rowAt (Fin.natAdd S.card i) (Fin.castAdd C.card d) =
      layerEntry C i (read d) := by
  have hmem : Fin.castAdd C.card d ∈ (S.catalogueLayer k read G C hS).toCellScheme.below
      ((S.catalogueLayer k read G C hS).toCellScheme.gradedIndex (Fin.natAdd S.card i)) := by
    rw [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_natAdd,
      appendFullCellsScheme_gradedIndex_castAdd, CellScheme.gradedIndex_le_iff]
    exact ⟨subset_univ _, hd⟩
  rw [rowAt_of_mem hmem, appendFullCells_row_natAdd_eq]
  exact layerRow_castAdd _ d

end VaughtConjecture.Scheme
