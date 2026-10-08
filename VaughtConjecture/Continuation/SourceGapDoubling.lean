/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.FieldLayer
import VaughtConjecture.Extension.Gluing

/-!
# Doublings: schemes read through a scheme on one point fewer

Roadmap, Layer 3 ((R2) of the table of 3.4, the reading of the new tops at the cells labelled `⊤`);
the obstruction of `VaughtConjecture.Continuation.SourceGapMixedEntry`.

**The requirement.**  A completion of the amalgam of two coatom types at which every cell of full
scope reads each new top at its tops cannot carry, at the reading grade, a cell for every lawful
labelling of the cells below (`MixedEntry.not_exists_reading_markedLayer`): the mixed labelling,
`⊤` on the context and lowered on the donor, is lawful below the cells of full scope, its code is a
catalogue entry, and a cell carrying it is forced to `⊤` within the cross height of a reading cell.
When the two coatom types are **the same type** `T`, there is a completion without that cell: the
**doubling** of `T`, whose cells over a cell `c` of `T` are the copies of `c` on the two coatoms
(the left and right copies) and, when `c` has full scope, one copy of full scope; every cell reads
every cell through `T`.  In the doubling:

* **entries admitted**: the row of a cell of full scope is the row of a cell of `T`, read through
  the collapse of the two last points; there is no other cell of full scope.  So every cell of full
  scope reads the two copies of a cell alike (`Scheme.IsDoubling.rowAt_eq`);
* **lawful labellings below a full pair are symmetric** (`Scheme.IsDoubling.eq_of_isLawfulBelow`):
  availability puts each copy below a cell of full scope at least as large, which reads the two
  copies alike, so they agree.  The mixed labelling, which separates the two copies of the cells of
  grade `2`, is not lawful below `(univ, 2)`: no lawful labelling below a pair of full scope ever
  needs the extension of a labelling that is not symmetric;
* **bountifulness from symmetric fills** (`Scheme.IsDoubling.cappedLift_coatom`): a labelling
  lawful below a coatom is a labelling of `T` (its copies), lawful there, and its pullback through
  the collapse is lawful below the full pair (`Scheme.IsDoubling.isLawful_comp`): it extends the
  labelling, and it agrees with every lawful labelling below the full pair at each cap at which the
  restrictions agree, since that labelling is symmetric too.

**The structure** (`Scheme.IsDoubling D T π`), for a scheme `D` on `m + 2` points, a scheme `T` on
`m + 1` points and a map `π` of the cells: grades are kept; the scope of `π d` is the image of the
scope of `d` under the **collapse** `Scheme.collapseLast m` (the point `m + 1` sent to `m`); the
rows of `D` are those of `T` through `π`; and every cell of `T` has a cell over it at the graded
index of any cell of `D` whose collapsed graded index is its own (the targets of availability).

* `Scheme.IsDoubling.isLawful_comp` (compiled in this repository): the pullback of a lawful
  labelling of `T` is lawful.
* `Scheme.IsDoubling.eq_of_isLawfulBelow` (compiled): with cells of full scope at the grades below
  `j`, a labelling lawful below `(univ, j)` agrees at two cells over one cell of `T`.
* `Scheme.IsDoubling.cappedLift_coatom` (compiled): with the copies along a section `f` of the
  collapse (the left or the right coatom), unique at their scopes, and cells of full scope at the
  grades `1, …, j`, the rows lift capped from `(univ.map f, j)` to `(univ, j)`.
* `Scheme.IsDoubling.appendFullCells` (compiled): appending, at grade `k`, one cell of full scope
  for each cell of `T` of graded index `(univ, k)`, with its row read through `π`, keeps the
  structure.

The doubling of a seed whose two coatom types are equal is built from these in
`VaughtConjecture.Continuation.SourceGapDoubledCompletion`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Scheme

variable {m : ℕ}

/-- The **collapse** of the last two points of `Fin (m + 2)`: the point `m + 1` goes to `m`, and
the other points are kept. -/
def collapseLast (m : ℕ) (i : Fin (m + 2)) : Fin (m + 1) :=
  Fin.lastCases (Fin.last m) id i

@[simp] theorem collapseLast_castSucc (i : Fin (m + 1)) : collapseLast m i.castSucc = i := by
  simp [collapseLast]

@[simp] theorem collapseLast_last : collapseLast m (Fin.last (m + 1)) = Fin.last m := by
  simp [collapseLast]

/-- The collapse is a retraction of the right coatom. -/
@[simp] theorem collapseLast_extendByLast (i : Fin (m + 1)) :
    collapseLast m (extendByLast Fin.castSuccEmb i) = i := by
  induction i using Fin.lastCases with
  | last => rw [extendByLast_last, collapseLast_last]
  | cast i => rw [extendByLast_castSucc, Fin.castSuccEmb_apply, collapseLast_castSucc]

/-- The collapse of the image of a section is the set itself. -/
theorem image_collapseLast_map {f : Fin (m + 1) ↪ Fin (m + 2)}
    (hf : ∀ i, collapseLast m (f i) = i) (B : Finset (Fin (m + 1))) :
    (B.map f).image (collapseLast m) = B := by
  ext i
  simp only [mem_image, mem_map]
  exact ⟨fun ⟨_, ⟨j, hj, hji⟩, he⟩ ↦ by rw [← he, ← hji, hf]; exact hj,
    fun hi ↦ ⟨f i, ⟨i, hi, rfl⟩, hf i⟩⟩

/-- The collapse of the full set is the full set. -/
theorem image_collapseLast_univ : (univ : Finset (Fin (m + 2))).image (collapseLast m) = univ :=
  eq_univ_of_forall fun i ↦ mem_image.mpr ⟨i.castSucc, mem_univ _, collapseLast_castSucc i⟩

/-- A scheme `D` on `m + 2` points is a **doubling** of a scheme `T` on `m + 1` points along `π`:
grades are kept, scopes collapse to scopes, the rows of `D` are those of `T` through `π`, and every
cell of `T` has a cell over it at the graded index of every cell of `D` with the collapsed graded
index of that cell. -/
structure IsDoubling (D : Scheme.{u} (m + 2)) (T : Scheme.{u} (m + 1))
    (π : Fin D.card → Fin T.card) : Prop where
  grade_eq (d : Fin D.card) : T.toCellScheme.grade (π d) = D.toCellScheme.grade d
  scope_eq (d : Fin D.card) :
    T.toCellScheme.scope (π d) = (D.toCellScheme.scope d).image (collapseLast m)
  rowAt_eq (a d : Fin D.card) : d ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex a) →
    D.rowAt a d = T.rowAt (π a) (π d)
  exists_lift (c : Fin T.card) (e : Fin D.card) :
    T.toCellScheme.gradedIndex c =
      ((D.toCellScheme.scope e).image (collapseLast m), D.toCellScheme.grade e) →
    ∃ a, π a = c ∧ D.toCellScheme.gradedIndex a = D.toCellScheme.gradedIndex e

namespace IsDoubling

variable {D : Scheme.{u} (m + 2)} {T : Scheme.{u} (m + 1)} {π : Fin D.card → Fin T.card}
  (hD : D.IsDoubling T π)
include hD

theorem gradedIndex_eq (d : Fin D.card) : T.toCellScheme.gradedIndex (π d) =
    ((D.toCellScheme.scope d).image (collapseLast m), D.toCellScheme.grade d) :=
  Prod.ext (hD.scope_eq d) (hD.grade_eq d)

/-- A cell below `a` lies, through `π`, below `π a`. -/
theorem mem_below {a d : Fin D.card}
    (hd : d ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex a)) :
    π d ∈ T.toCellScheme.below (T.toCellScheme.gradedIndex (π a)) := by
  rw [CellScheme.mem_below, hD.gradedIndex_eq, hD.gradedIndex_eq]
  exact ⟨image_subset_image hd.1, hd.2⟩

/-- **The pullback of a lawful labelling of `T` is lawful.** -/
theorem isLawful_comp {w : Fin T.card → Label.{u}} (hw : T.rows.IsLawful w) :
    D.rows.IsLawful (w ∘ π) where
  orderly d := by
    rw [Function.comp_apply, ← hD.grade_eq]
    exact hw.orderly (π d)
  locality a := by
    have h := (hw.locality (π a)).reindex
      (fun d : D.toCellScheme.below (D.toCellScheme.gradedIndex a) ↦
        (⟨π d, hD.mem_below d.2⟩ : T.toCellScheme.below (T.toCellScheme.gradedIndex (π a))))
    convert h using 1
    · funext d
      exact (hD.grade_eq d).symm
    · funext d
      rw [Function.comp_apply, ← rowAt_of_mem d.2, ← rowAt_of_mem (hD.mem_below d.2)]
      exact hD.rowAt_eq a d d.2
    · rfl
  availability s e hse hg := by
    have hsc : T.toCellScheme.scope (π s) ⊆ T.toCellScheme.scope (π e) := by
      rw [hD.scope_eq, hD.scope_eq]
      exact image_subset_image hse
    obtain ⟨c, hc, hle⟩ := hw.availability (π s) (π e) hsc
      (by rw [hD.grade_eq, hD.grade_eq, hg])
    obtain ⟨a, rfl, ha⟩ := hD.exists_lift c e (hc.trans (hD.gradedIndex_eq e))
    exact ⟨a, ha, hle⟩

/-- **Lawful labellings below a full pair are symmetric**: with a cell of full scope at the grade
of every cell below `(univ, j)`, a labelling lawful below `(univ, j)` agrees at two cells over one
cell of `T`.  Each is below a cell of full scope at least as large (availability), which reads the
two alike. -/
theorem eq_of_isLawfulBelow {j : ℕ} {w : Fin D.card → Label.{u}}
    (hw : D.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) fun d ↦ w d)
    (hfull : ∀ d ∈ D.toCellScheme.below ((univ : Finset (Fin (m + 2))), j),
      ∃ a, D.toCellScheme.gradedIndex a = (univ, D.toCellScheme.grade d))
    {d d' : Fin D.card} (hd : d ∈ D.toCellScheme.below ((univ : Finset (Fin (m + 2))), j))
    (hd' : d' ∈ D.toCellScheme.below ((univ : Finset (Fin (m + 2))), j)) (hπ : π d = π d') :
    w d = w d' := by
  obtain ⟨-, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hw
  have key (d d' : Fin D.card) (hd : d ∈ D.toCellScheme.below ((univ : Finset (Fin (m + 2))), j))
      (hπ : π d = π d') : w d ≤ w d' := by
    obtain ⟨a₀, ha₀⟩ := hfull d hd
    have ha₀m : a₀ ∈ D.toCellScheme.below ((univ : Finset (Fin (m + 2))), j) := by
      rw [CellScheme.mem_below, ha₀]
      exact ⟨subset_univ _, hd.2⟩
    obtain ⟨a, ha, hle⟩ := havail d a₀ ha₀m
      (by rw [show D.toCellScheme.scope a₀ = univ from congrArg Prod.fst ha₀]; exact subset_univ _)
      (congrArg Prod.snd ha₀).symm
    have hga : D.toCellScheme.gradedIndex a = (univ, D.toCellScheme.grade d) := ha.trans ha₀
    have hgd : D.toCellScheme.grade d' = D.toCellScheme.grade d := by
      rw [← hD.grade_eq, ← hD.grade_eq, hπ]
    have hda : d ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex a) := by
      rw [CellScheme.mem_below, hga]
      exact ⟨subset_univ _, le_rfl⟩
    have hd'a : d' ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex a) := by
      rw [CellScheme.mem_below, hga]
      exact ⟨subset_univ _, hgd.le⟩
    have ham : a ∈ D.toCellScheme.below ((univ : Finset (Fin (m + 2))), j) := by
      rw [CellScheme.mem_below, ha]
      exact ha₀m
    have hrow : D.rows.row a ⟨d, hda⟩ ≤ D.rows.row a ⟨d', hd'a⟩ := by
      rw [← rowAt_of_mem hda, ← rowAt_of_mem hd'a, hD.rowAt_eq a d hda, hD.rowAt_eq a d' hd'a, hπ]
    have h := (hloc a ham).le_of_le hrow hgd.le
    simp only at h
    calc w d = min (w d) (w a) := (min_eq_left hle).symm
      _ ≤ min (w d') (w a) := h
      _ ≤ w d' := min_le_left _ _
  exact le_antisymm (key d d' hd hπ) (key d' d hd' hπ.symm)

/-- **The lift from a coatom to the full face**, by the symmetric fill.  Let `f` be a section of
the collapse (`Coatom.left m` or `Coatom.right m`), `cp` the copies of the cells of `T` along `f`
(over each cell, at the image of its graded index, and the only cells over their cells at their
scopes inside `univ.map f`), and suppose `D` has a cell of full scope at every grade `1, …, j` and
no cell of grade `0`.  Then the rows lift capped from `(univ.map f, j)` to `(univ, j)`: a labelling
lawful below the coatom is a lawful labelling of `T` through the copies, and its pullback is the
lift. -/
theorem cappedLift_coatom {f : Fin (m + 1) ↪ Fin (m + 2)} (hf : ∀ i, collapseLast m (f i) = i)
    {cp : Fin T.card → Fin D.card} (hcpπ : ∀ z, π (cp z) = z)
    (hcpg : ∀ z, D.toCellScheme.gradedIndex (cp z) =
      ((T.toCellScheme.scope z).map f, T.toCellScheme.grade z))
    (hcpu : ∀ d, D.toCellScheme.scope d ⊆ univ.map f → cp (π d) = d) {j : ℕ}
    (hfull : ∀ i, 0 < i → i ≤ j → ∃ a, D.toCellScheme.gradedIndex a = (univ, i))
    (hpos : ∀ d, 0 < D.toCellScheme.grade d) :
    D.rows.CappedLift (X := (univ.map f, j)) (Y := ((univ : Finset (Fin (m + 2))), j))
      ⟨subset_univ _, le_rfl⟩ := by
  set X : Finset (Fin (m + 2)) × ℕ := (univ.map f, j)
  set Y : Finset (Fin (m + 2)) × ℕ := ((univ : Finset (Fin (m + 2))), j)
  have hXY : X ≤ Y := ⟨subset_univ _, le_rfl⟩
  rw [CellScheme.Rows.cappedLift_iff_forall_exists]
  intro c _ p q hp hq hpq
  classical
  -- the labellings as functions on all cells
  obtain ⟨pe, hpe'⟩ : ∃ pe : Fin D.card → Label.{u},
      ∀ d (hd : d ∈ D.toCellScheme.below X), pe d = p ⟨d, hd⟩ :=
    ⟨fun d ↦ if hd : d ∈ D.toCellScheme.below X then p ⟨d, hd⟩ else ⊥, fun d hd ↦ dite_eq_left hd⟩
  obtain ⟨qe, hqe'⟩ : ∃ qe : Fin D.card → Label.{u},
      ∀ d (hd : d ∈ D.toCellScheme.below Y), qe d = q ⟨d, hd⟩ :=
    ⟨fun d ↦ if hd : d ∈ D.toCellScheme.below Y then q ⟨d, hd⟩ else ⊥, fun d hd ↦ dite_eq_left hd⟩
  have hpe : p = fun d ↦ pe d.1 := funext fun d ↦ (hpe' d.1 d.2).symm
  have hqe : q = fun d ↦ qe d.1 := funext fun d ↦ (hqe' d.1 d.2).symm
  have hcpX (z : Fin T.card) (hz : T.toCellScheme.grade z ≤ j) :
      cp z ∈ D.toCellScheme.below X := by
    rw [CellScheme.mem_below, hcpg]
    exact ⟨map_subset_map.mpr (subset_univ _), hz⟩
  -- the labelling of `T` read through the copies
  set P : Fin T.card → Label.{u} := fun z ↦ pe (cp z)
  have hP : T.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), j) fun z ↦ P z := by
    rw [hpe] at hp
    obtain ⟨hord, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hp
    refine CellScheme.Rows.isLawfulBelow_iff_forall.mpr ⟨fun z hz ↦ ?_, fun z hz ↦ ?_,
      fun z₁ z₂ hz₂ hsc hg ↦ ?_⟩
    · have h := hord (cp z) (hcpX z hz.2)
      rwa [show D.toCellScheme.grade (cp z) = T.toCellScheme.grade z from
        congrArg Prod.snd (hcpg z)] at h
    · have hψ (e : T.toCellScheme.below (T.toCellScheme.gradedIndex z)) :
          cp e ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex (cp z)) := by
        rw [CellScheme.mem_below, hcpg, hcpg]
        exact ⟨map_subset_map.mpr e.2.1, e.2.2⟩
      have h := (hloc (cp z) (hcpX z hz.2)).reindex
        fun e : T.toCellScheme.below (T.toCellScheme.gradedIndex z) ↦ (⟨cp e.1, hψ e⟩ :
          D.toCellScheme.below (D.toCellScheme.gradedIndex (cp z)))
      convert h using 1
      · funext e
        exact (congrArg Prod.snd (hcpg e)).symm
      · funext e
        rw [Function.comp_apply, ← rowAt_of_mem e.2, ← rowAt_of_mem (hψ e),
          hD.rowAt_eq _ _ (hψ e), hcpπ, hcpπ]
      · rfl
    · have hz₁ : T.toCellScheme.grade z₁ ≤ j := hg ▸ hz₂.2
      have hs (z : Fin T.card) : D.toCellScheme.scope (cp z) = (T.toCellScheme.scope z).map f :=
        congrArg Prod.fst (hcpg z)
      have hgr (z : Fin T.card) : D.toCellScheme.grade (cp z) = T.toCellScheme.grade z :=
        congrArg Prod.snd (hcpg z)
      obtain ⟨a, ha, hle⟩ := havail (cp z₁) (cp z₂) (hcpX z₂ hz₂.2)
        (by rw [hs, hs]; exact map_subset_map.mpr hsc) (by rw [hgr, hgr]; exact hg)
      have hsa' : D.toCellScheme.scope a = (T.toCellScheme.scope z₂).map f := by
        rw [← hs]; exact congrArg Prod.fst ha
      have hga : D.toCellScheme.grade a = T.toCellScheme.grade z₂ := by
        rw [← hgr]; exact congrArg Prod.snd ha
      have hsa : D.toCellScheme.scope a ⊆ univ.map f := by
        rw [hsa']
        exact map_subset_map.mpr (subset_univ _)
      refine ⟨π a, ?_, ?_⟩
      · rw [hD.gradedIndex_eq, hsa', hga, image_collapseLast_map hf]
        rfl
      · change pe (cp z₁) ≤ pe (cp (π a))
        rwa [hcpu a hsa]
  -- the symmetric fill: the pullback of the spliced labelling
  have hPs := T.isLawful_splice_bot hP
  set Ps := T.toCellScheme.splice j (fun _ ↦ ⊥) P
  have hpull := hD.isLawful_comp hPs
  have hPsπ (d : Fin D.card) (hd : D.toCellScheme.grade d ≤ j) : Ps (π d) = pe (cp (π d)) := by
    change T.toCellScheme.splice j (fun _ ↦ ⊥) P (π d) = _
    rw [CellScheme.splice_of_le (by rw [hD.grade_eq]; exact hd)]
  -- the symmetry of `q`
  have hqsym (d : Fin D.card) (hd : d ∈ D.toCellScheme.below Y) : qe (cp (π d)) = qe d := by
    rw [hqe] at hq
    refine hD.eq_of_isLawfulBelow hq (fun e he ↦ hfull _ (hpos e) he.2) ?_ hd (hcpπ _)
    rw [CellScheme.mem_below, hcpg, hD.grade_eq]
    exact ⟨subset_univ _, hd.2⟩
  refine ⟨fun d ↦ Ps (π d.1), hpull.isLawfulBelow Y, fun d ↦ ?_, fun d ↦ ?_⟩
  · -- the capped agreement with `q`
    have hdg : D.toCellScheme.grade d.1 ≤ j := d.2.2
    have hmem := hcpX (π d.1) (by rw [hD.grade_eq]; exact hdg)
    have h := hpq ⟨cp (π d.1), hmem⟩
    calc min (Ps (π d.1)) c = min (p ⟨cp (π d.1), hmem⟩) c := by rw [hPsπ d.1 hdg, hpe' _ hmem]
      _ = min (qe (cp (π d.1))) c := by
        rw [← h]
        congr 1
        exact (hqe' _ _).symm
      _ = min (qe d.1) c := by rw [hqsym d.1 d.2]
      _ = min (q d) c := by
        congr 1
        exact hqe' d.1 d.2
  · -- the extension of `p`
    have hdg : D.toCellScheme.grade d.1 ≤ j := d.2.2
    change Ps (π d.1) = p d
    rw [hPsπ d.1 hdg, hcpu d.1 d.2.1]
    exact hpe' d.1 d.2

end IsDoubling

/-! ### Appending the cells of full scope -/

section Append

variable {D : Scheme.{u} (m + 2)} {T : Scheme.{u} (m + 1)} {π : Fin D.card → Fin T.card}
  {k M : ℕ} {r : Fin M → Fin (D.card + M) → Label.{u}}
  {h : ∀ d, ¬ ((univ : Finset (Fin (m + 2))), k) ≤ D.toCellScheme.gradedIndex d}

/-- **Appending the copies of full scope keeps the doubling**: at grade `k`, one new cell for each
cell `e i` of `T` of graded index `(univ, k)`, every such cell having a new cell, with the row of
`e i` read through `π` and `e`. -/
theorem IsDoubling.appendFullCells (hD : D.IsDoubling T π) {e : Fin M → Fin T.card}
    (he : ∀ i, T.toCellScheme.gradedIndex (e i) = (univ, k))
    (hsurj : ∀ c, T.toCellScheme.gradedIndex c = (univ, k) → ∃ i, e i = c)
    (hr : ∀ i x, r i x = T.rowAt (e i) (Fin.append π e x)) :
    (D.appendFullCells k M r h).IsDoubling T (Fin.append π e) where
  grade_eq d := by
    induction d using Fin.addCases with
    | left d => rw [Fin.append_left, appendFullCellsScheme_grade_castAdd]; exact hD.grade_eq d
    | right i =>
      rw [Fin.append_right, appendFullCellsScheme_grade_natAdd]
      exact congrArg Prod.snd (he i)
  scope_eq d := by
    induction d using Fin.addCases with
    | left d => rw [Fin.append_left, appendFullCellsScheme_scope_castAdd]; exact hD.scope_eq d
    | right i =>
      rw [Fin.append_right, appendFullCellsScheme_scope_natAdd, image_collapseLast_univ]
      exact congrArg Prod.fst (he i)
  rowAt_eq a d hd := by
    induction a using Fin.addCases with
    | right i =>
      rw [rowAt_of_mem hd, appendFullCells_row_natAdd, hr, Fin.append_right]
    | left a =>
      have hlt := lt_card_of_mem_below (by
        rw [appendFullCellsScheme_gradedIndex_castAdd]; exact h a) hd
      obtain ⟨d', rfl⟩ : ∃ d' : Fin D.card, Fin.castAdd M d' = d := ⟨⟨d, hlt⟩, rfl⟩
      have hd' : d' ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex a) := by
        rwa [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_castAdd,
          appendFullCellsScheme_gradedIndex_castAdd] at hd
      rw [rowAt_appendFullCells_castAdd, Fin.append_left, Fin.append_left, hD.rowAt_eq a d' hd']
  exists_lift c b hc := by
    induction b using Fin.addCases with
    | left b =>
      rw [appendFullCellsScheme_scope_castAdd, appendFullCellsScheme_grade_castAdd] at hc
      obtain ⟨a, ha, hab⟩ := hD.exists_lift c b hc
      exact ⟨Fin.castAdd M a, by rw [Fin.append_left, ha], by
        rw [appendFullCellsScheme_gradedIndex_castAdd, appendFullCellsScheme_gradedIndex_castAdd,
          hab]⟩
    | right i =>
      rw [appendFullCellsScheme_scope_natAdd, appendFullCellsScheme_grade_natAdd,
        image_collapseLast_univ] at hc
      obtain ⟨i', rfl⟩ := hsurj c hc
      exact ⟨Fin.natAdd D.card i', Fin.append_right _ _ _, by
        rw [appendFullCellsScheme_gradedIndex_natAdd, appendFullCellsScheme_gradedIndex_natAdd]⟩

end Append

end Scheme

end VaughtConjecture
