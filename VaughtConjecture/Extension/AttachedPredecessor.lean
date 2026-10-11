/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Apex
import VaughtConjecture.Extension.FieldLayer
import VaughtConjecture.Extension.LayerLift
import VaughtConjecture.Extension.OwnerCappedLift
import VaughtConjecture.Extension.PartBelowFullGrade
import VaughtConjecture.Extension.Restoration

/-!
# The attached predecessor and its layer at the full grade of the private context

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the scheme over the private context and the
donor) and 3.1 (the completion of a seed below the full grade, whose analogue this is); semantic
contract, items 2–4.

Let `P` be a stage type on `n` points (the **private type**), `f` a face of it on `m` points (the
**root**), and `d` a stage type on `m + 1` points (the **donor**).  The scheme of (R1) lives on
`n + 1` points, with faces `P` along `Fin.castSuccEmb` and `d` along `extendByLast f`.

**The attached predecessor** (`StageType.AttachedPredecessor P f d`) is the part of that scheme
below the full grade `n` of the private context: a scheme on `n + 1` points whose restrictions
along `Fin.castSuccEmb` and `extendByLast f` are the schemes of `P` and `d`, whose cells of full
scope all have grade below `n`, which is well formed, coded, consistent, complete at every graded
face other than `(univ, n)` and `(univ, n + 1)`, and whose rows lift capped between graded faces at
every target that is a proper face or has grade below `n`; whose cells of grade `n` off the private
face are **muted** (row `⊥` at themselves); and a lawful labelling at the stage, literally the
labels of `P` and of `d` on their cells.  A plan on `n + 1` points has two coatoms
(`Geometry.IsPlan`); one is the private face, and the other, through the new point, carries cells
of grade `n` by completeness, which the predecessor mutes.  **Status: open; a completion-type
statement.**  It exists under the coatom extension property
(`StageType.AttachedPredecessor.nonempty_of_hasCoatomExtensions`, in
`VaughtConjecture.Extension.AttachedPredecessorFromCoatoms`), itself open; no implication from an
attached predecessor to `StageType.HasCoatomExtensions` is compiled.  It is a structure (data), not
a universal hypothesis; the theorems here are about a given predecessor.

**The layer** (`StageType.AttachedPredecessor.layerScheme`): the predecessor with `M` cells of full
scope and grade `n` appended (`Scheme.appendFullCells`), the `i`-th with a given row.

* **Legality below the full grade** (`StageType.AttachedPredecessor.isLegalBelowFullGrade`): if
  `2 ≤ n`, `0 < M`, every new row is lawful and coded, and the rows lift capped from the private
  face `(univ.map Fin.castSuccEmb, n)` to `(univ, n)`, the layer scheme is legal below its full
  grade `n + 1` (`Scheme.IsLegalBelowFullGrade`).  Bountifulness reduces to the lifts from the two
  coatoms at the grade `n` (`CellScheme.Rows.isBountiful_of_cappedLift_full`); the other lifts are
  those of the predecessor, transported along the old cells
  (`CellScheme.Rows.CappedLift.of_comap`), and the lift from the coatom through the new point is
  below the cap, its cells of grade `n` being muted
  (`StageType.AttachedPredecessor.cappedLift_coatom_layerScheme`, by
  `CellScheme.Rows.exists_lift_of_le_cap`).
* **The private lift from its active part**
  (`StageType.AttachedPredecessor.cappedLift_private_of_active`): the lift from the private face
  holds for every prescription at most the cap at the private cells of grade `n`
  (`CellScheme.Rows.exists_lift_of_le_cap`, the lift at the lower grade alone), so it holds once it
  holds for the **active** prescriptions, those above the cap at some private cell of grade `n`.

**The canonical field layer over the predecessor** (`Scheme.fieldLayer`, one cell of full scope
and grade `n` per orbit-canonical lawful labelling of the predecessor, whose row is its field
row).  Its rows lift capped from the private face
(`StageType.AttachedPredecessor.cappedLift_private_fieldLayer`): the one-grade lift
(`CellScheme.Rows.cappedLift_of_boundary_short`) with the boundary made of the private face at the
grade `n` and the full face at the grade `n - 1`.  Off the boundary, below `(univ, n)`, lie the
muted cells of the other coatom.  A labelling of the boundary extended by `⊥` there is lawful
(`CellScheme.Rows.isLawfulBelow_ite_bot`), which gives the extension from the boundary at the cap
`⊥` (`Scheme.extendsFromBoundary_bot_fieldLayer_of_closed`) and, since every catalogue entry is
`⊥` at a muted cell, at a positive cap short at `n` along every new row
(`Scheme.extendsFromBoundary_fieldLayer_of_isShort_of_mute`, from the field layer's extension
through the new cells at a short cap, `Scheme.exists_extension_fieldLayer`).  The owner-local
alignment asks for the extension only at the short caps, so caps that are not short need nothing
more.  Hence the field layer is legal below its full grade
(`StageType.AttachedPredecessor.isLegalBelowFullGrade_fieldLayer`), and with the apex added it is a
**legal coface of `P` carrying `d`** (`StageType.AttachedPredecessor.exists_isLegal_coface`,
at a stage that is zero or a limit, `2 ≤ n`, `m < n`): an attached predecessor gives a pinned
extension of `P` with the donor `d`.

**The converse** (`StageType.AttachedPredecessor.ofIsLegal`).  The cells not above `(univ, n)` of a
legal stage type on `n + 1` points with faces `P` and `d` whose cells of grade `n` off the private
and the full face are muted form an attached predecessor
(`StageType.AttachedPredecessor.cutBelowLayer`).  The pinned extension of the coatom extension
property, with its last coface muted at the full grade, is such a coface
(`StageType.exists_pinned_extension_muted`), so the coatom extension property gives an attached
predecessor.

**What is not here: the gate.**  The coface has no gate: no cell of graded index `(univ, n)` whose
non-`⊥` value forces, in every lawful labelling with the literal private labels, a reading of the
donor through the private cells.  A gated layer has to give the cells of the catalogue entries that
read the donor (in the capped reading of `VaughtConjecture.Extension.CappedGate`) a pattern of `⊥`
values that the bottom-pattern clause transfers, and its extension at a short cap along such an
entry must produce an entry that reads the donor again; the extension of the field layer takes the
orbit code of an arbitrary boundary labelling, which need not read the donor (argued, not
formalized).  The gated layer is **open**.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`, beside
`VaughtConjecture.Extension.CompletionBelowFullGrade`.

## References

Lawful sections are [Kni26, Definition 2.5.4], bountifulness [Kni26, Definition 2.5.14] and
completeness [Kni26, Definition 2.5.15].
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Extension by `⊥` at muted cells -/

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}}

open Classical in
/-- **Extension by `⊥` off two pairs.**  Let `w` be lawful below `U` and below `V`.  If a cell with
scope inside that of a cell below `Y` outside `U` and `V`, and of the same grade, is again outside
`U` and `V`, then `w` on the cells below `U` or `V`, and `⊥` elsewhere, is lawful below `Y`.
Locality at a cell labelled `⊥` holds for every row. -/
theorem isLawfulBelow_ite_bot {U V Y : Finset α × ℕ}
    {w : ι → Label.{u}} (hwU : R.IsLawfulBelow U (fun d ↦ w d))
    (hwV : R.IsLawfulBelow V (fun d ↦ w d))
    (hclosed : ∀ s t, t ∈ D.below Y → t ∉ D.below U → t ∉ D.below V →
      D.scope s ⊆ D.scope t → D.grade s = D.grade t → s ∉ D.below U ∧ s ∉ D.below V) :
    R.IsLawfulBelow Y (fun d ↦ if d.1 ∈ D.below U ∨ d.1 ∈ D.below V then w d else ⊥) := by
  set p : ι → Label.{u} := fun d ↦ if d ∈ D.below U ∨ d ∈ D.below V then w d else ⊥
  have hpU : ∀ d ∈ D.below U, p d = w d := fun d hd ↦ ite_eq_left (.inl hd)
  have hpV : ∀ d ∈ D.below V, p d = w d := fun d hd ↦ ite_eq_left (.inr hd)
  have hpo : ∀ d, d ∉ D.below U → d ∉ D.below V → p d = ⊥ := fun d h₁ h₂ ↦
    ite_eq_right (not_or.mpr ⟨h₁, h₂⟩)
  obtain ⟨hoU, hlU, haU⟩ := isLawfulBelow_iff_forall.mp hwU
  obtain ⟨hoV, hlV, haV⟩ := isLawfulBelow_iff_forall.mp hwV
  have hbelow : ∀ {s : ι} {X : Finset α × ℕ}, s ∈ D.below X →
      ∀ d : D.below (D.gradedIndex s), d.1 ∈ D.below X := fun hs d ↦
    show D.gradedIndex d.1 ≤ _ from le_trans d.2 hs
  have hsub : ∀ {s t : ι} {X : Finset α × ℕ}, t ∈ D.below X → D.scope s ⊆ D.scope t →
      D.grade s = D.grade t → s ∈ D.below X := fun ht hst hg ↦
    (D.gradedIndex_le_iff).mpr ⟨hst.trans (D.mem_below.mp ht).1, hg ▸ (D.mem_below.mp ht).2⟩
  change R.IsLawfulBelow Y (fun d ↦ p d)
  refine isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · by_cases h₁ : d ∈ D.below U
    · rw [hpU d h₁]; exact hoU d h₁
    by_cases h₂ : d ∈ D.below V
    · rw [hpV d h₂]; exact hoV d h₂
    · rw [hpo d h₁ h₂]; exact isSelfVisible_bot _
  · by_cases h₁ : s ∈ D.below U
    · have heq : (fun d : D.below (D.gradedIndex s) ↦ min (p d) (p s)) =
          fun d : D.below (D.gradedIndex s) ↦ min (w d) (w s) := funext fun d ↦ by
        rw [hpU _ (hbelow h₁ d), hpU s h₁]
      rw [heq]; exact hlU s h₁
    by_cases h₂ : s ∈ D.below V
    · have heq : (fun d : D.below (D.gradedIndex s) ↦ min (p d) (p s)) =
          fun d : D.below (D.gradedIndex s) ↦ min (w d) (w s) := funext fun d ↦ by
        rw [hpV _ (hbelow h₂ d), hpV s h₂]
      rw [heq]; exact hlV s h₂
    · have heq : (fun d : D.below (D.gradedIndex s) ↦ min (p d) (p s)) = fun _ ↦ ⊥ :=
        funext fun d ↦ by rw [hpo s h₁ h₂, min_bot_right]
      rw [heq]
      exact TransformsTo.bot _ _
  · by_cases h₁ : t ∈ D.below U
    · obtain ⟨u, hu, hle⟩ := haU s t h₁ hst hg
      have huU : u ∈ D.below U := by rw [CellScheme.mem_below, hu]; exact h₁
      exact ⟨u, hu, by rw [hpU s (hsub h₁ hst hg), hpU u huU]; exact hle⟩
    by_cases h₂ : t ∈ D.below V
    · obtain ⟨u, hu, hle⟩ := haV s t h₂ hst hg
      have huV : u ∈ D.below V := by rw [CellScheme.mem_below, hu]; exact h₂
      exact ⟨u, hu, by rw [hpV s (hsub h₂ hst hg), hpV u huV]; exact hle⟩
    · obtain ⟨hs₁, hs₂⟩ := hclosed s t ht h₁ h₂ hst hg
      exact ⟨t, rfl, by rw [hpo s hs₁ hs₂]; exact bot_le⟩

end CellScheme.Rows

/-! ### Extension through the field layer at a short cap -/

namespace Scheme

variable {N k : ℕ} {S : Scheme.{u} N}
  {hS : ∀ d, ¬ ((univ : Finset (Fin N)), k) ≤ S.toCellScheme.gradedIndex d}
  {U V : Finset (Fin N) × ℕ}

open Classical in
/-- **Extension from the boundary at the cap `⊥`, off the boundary by `⊥`.**  The boundary is the
cells below `U` and `V`; a cell with scope
inside that of a cell off the boundary and of the same grade is again off the boundary.  Every
labelling lawful below `U` and `V` extends, unchanged on the boundary, to a labelling lawful below
`(univ, k)`: `⊥` off the boundary (`CellScheme.Rows.isLawfulBelow_ite_bot`), then through the
new cells (`Scheme.exists_isLawfulBelow_fieldLayer`). -/
theorem extendsFromBoundary_bot_fieldLayer_of_closed
    (hU : ¬ ((univ : Finset (Fin N)), k) ≤ U) (hV : ¬ ((univ : Finset (Fin N)), k) ≤ V)
    (hclosed : ∀ s t, t ∈ S.toCellScheme.below (univ, k) → t ∉ S.toCellScheme.below U →
      t ∉ S.toCellScheme.below V → S.toCellScheme.scope s ⊆ S.toCellScheme.scope t →
        S.toCellScheme.grade s = S.toCellScheme.grade t →
          s ∉ S.toCellScheme.below U ∧ s ∉ S.toCellScheme.below V) :
    (S.fieldLayer k hS).rows.ExtendsFromBoundary U V (univ, k) ⊥ fun _ ↦ ⊥ := by
  intro w hwU hwV _
  have hwU' := (isLawfulBelow_appendFullCells_iff hU).mp hwU
  have hwV' := (isLawfulBelow_appendFullCells_iff hV).mp hwV
  have hp := CellScheme.Rows.isLawfulBelow_ite_bot (Y := ((univ : Finset (Fin N)), k))
    (w := fun d ↦ w (Fin.castAdd _ d)) hwU' hwV' hclosed
  obtain ⟨r, hr, hre⟩ := exists_isLawfulBelow_fieldLayer (hS := hS)
    (p := fun d ↦ if d ∈ S.toCellScheme.below U ∨ d ∈ S.toCellScheme.below V then
      w (Fin.castAdd _ d) else ⊥) hp
  refine ⟨r, hr, fun d hd ↦ ?_, fun _ ↦ by simp⟩
  obtain ⟨e, he, rfl⟩ := exists_castAdd_eq_of_boundary hU hV hd
  rw [hre e he]
  have hcov : e ∈ S.toCellScheme.below U ∨ e ∈ S.toCellScheme.below V := by
    simpa [CellScheme.mem_below] using hd
  exact ite_eq_left hcov

open Classical in
/-- **Extension from the boundary at a short positive cap along a new row, with muted cells.**
As `Scheme.extendsFromBoundary_bot_fieldLayer_of_closed`, at a cap `h` self-visible and short at
`k`, along the row of a new cell, when every old cell of grade at most `k` off the boundary is
**muted** (its row is `⊥` at itself): the catalogue entry of the cell is `⊥` at the muted cells,
so the labelling extended by `⊥` agrees with it there (`Scheme.exists_extension_fieldLayer`). -/
theorem extendsFromBoundary_fieldLayer_of_isShort_of_mute
    (hU : ¬ ((univ : Finset (Fin N)), k) ≤ U) (hV : ¬ ((univ : Finset (Fin N)), k) ≤ V)
    (hmute : ∀ d ∈ S.toCellScheme.below (univ, k), d ∉ S.toCellScheme.below U →
      d ∉ S.toCellScheme.below V →
        S.rows.row d ⟨d, S.toCellScheme.mem_below_gradedIndex d⟩ = ⊥)
    (hclosed : ∀ s t, t ∈ S.toCellScheme.below (univ, k) → t ∉ S.toCellScheme.below U →
      t ∉ S.toCellScheme.below V → S.toCellScheme.scope s ⊆ S.toCellScheme.scope t →
        S.toCellScheme.grade s = S.toCellScheme.grade t →
          s ∉ S.toCellScheme.below U ∧ s ∉ S.toCellScheme.below V)
    {u : Fin (S.fieldLayer k hS).card}
    (hu : (S.fieldLayer k hS).toCellScheme.gradedIndex u = (univ, k)) {h : Label.{u}}
    (hh : IsSelfVisible k h) (hsh : IsShort k h) (hbot : ⊥ < h) :
    (S.fieldLayer k hS).rows.ExtendsFromBoundary U V (univ, k) h
      ((S.fieldLayer k hS).rows.rowBelow u hu) := by
  intro w hwU hwV hwS
  obtain ⟨i, rfl⟩ := exists_natAdd_eq hu
  have hrowBelow (d : (S.fieldLayer k hS).toCellScheme.below (univ, k)) :
      (S.fieldLayer k hS).rows.rowBelow (Fin.natAdd S.card i) hu d =
        S.fieldRow k (S.catalogueEntry k i) d :=
    fieldLayer_row_natAdd i _
  have hwU' := (isLawfulBelow_appendFullCells_iff hU).mp hwU
  have hwV' := (isLawfulBelow_appendFullCells_iff hV).mp hwV
  have hp := CellScheme.Rows.isLawfulBelow_ite_bot (Y := ((univ : Finset (Fin N)), k))
    (w := fun d ↦ w (Fin.castAdd _ d)) hwU' hwV' hclosed
  have hentry := (mem_catalogue.mp (catalogueEntry_mem (S := S) (k := k) i)).1
  have hag (d : Fin S.card) (hd : S.toCellScheme.grade d ≤ k) :
      min (if d ∈ S.toCellScheme.below U ∨ d ∈ S.toCellScheme.below V then
        w (Fin.castAdd _ d) else ⊥) h = min (S.catalogueEntry k i d) h := by
    by_cases hcov : d ∈ S.toCellScheme.below U ∨ d ∈ S.toCellScheme.below V
    · rw [ite_eq_left hcov]
      have hbd : Fin.castAdd (S.catalogue k).card d ∈ (S.fieldLayer k hS).toCellScheme.below U ∨
          Fin.castAdd (S.catalogue k).card d ∈ (S.fieldLayer k hS).toCellScheme.below V := by
        simpa [CellScheme.mem_below] using hcov
      have := hwS ⟨_, castAdd_mem_below hd⟩ hbd
      rwa [hrowBelow, fieldRow_castAdd] at this
    · rw [ite_eq_right hcov, hentry.eq_bot_of_row_self_eq_bot d (hmute d ⟨subset_univ _, hd⟩
        (not_or.mp hcov).1 (not_or.mp hcov).2)]
  obtain ⟨r, hr, hrp, hrS⟩ := exists_extension_fieldLayer (hS := hS)
    (p := fun d ↦ if d ∈ S.toCellScheme.below U ∨ d ∈ S.toCellScheme.below V then
      w (Fin.castAdd _ d) else ⊥) hp (catalogueEntry_mem i) hh hbot (.inl hsh) hag
  refine ⟨r, hr, fun d hd ↦ ?_, fun d ↦ by rw [hrowBelow]; exact hrS d⟩
  obtain ⟨e, he, rfl⟩ := exists_castAdd_eq_of_boundary hU hV hd
  rw [hrp e he]
  have hcov : e ∈ S.toCellScheme.below U ∨ e ∈ S.toCellScheme.below V := by
    simpa [CellScheme.mem_below] using hd
  exact ite_eq_left hcov

end Scheme

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-- **The attached predecessor** of the scheme of (R1) for the private type `P` on `n` points, the
root `f` and the donor `d`: a scheme on `n + 1` points with literal faces `P` and `d` and cells
of full scope only below the grade `n`, legal at every graded face other than `(univ, n)` and
`(univ, n + 1)`, the private face its only face of at least `n` points other than the full one,
with a lawful labelling at the stage that is literally the labels of `P` and `d`.

**Status: open; a completion-type statement.**  It exists under `StageType.HasCoatomExtensions α`
(`StageType.AttachedPredecessor.nonempty_of_hasCoatomExtensions`); no converse is compiled. -/
structure AttachedPredecessor (P : StageType.{u} α n) (f : Fin m ↪ Fin n)
    (d : StageType.{u} α (m + 1)) where
  /-- The scheme. -/
  scheme : Scheme.{u} (n + 1)
  /-- The scheme is well formed. -/
  isWellFormed : scheme.IsWellFormed
  /-- The rows are coded. -/
  isCoded : scheme.IsCoded
  /-- The rows are consistent. -/
  isConsistent : scheme.rows.IsConsistent
  /-- The private face is a face. -/
  mem_faces_castSuccEmb : univ.map Fin.castSuccEmb ∈ scheme.toCellScheme.faces
  /-- The private face is literally the scheme of `P`. -/
  comap_castSuccEmb : scheme.comap Fin.castSuccEmb = P.toScheme
  /-- The donor face is a face. -/
  mem_faces_extendByLast : univ.map (extendByLast f) ∈ scheme.toCellScheme.faces
  /-- The donor face is literally the scheme of `d`. -/
  comap_extendByLast : scheme.comap (extendByLast f) = d.toScheme
  /-- Every cell of grade `n` off the private face is **muted**: its row is `⊥` at itself. -/
  mute : ∀ c, scheme.toCellScheme.grade c = n →
    scheme.toCellScheme.scope c ≠ univ.map Fin.castSuccEmb →
      scheme.rows.row c ⟨c, scheme.toCellScheme.mem_below_gradedIndex c⟩ = ⊥
  /-- Every cell of full scope has grade below `n`. -/
  grade_lt_of_scope_eq : ∀ c, scheme.toCellScheme.scope c = univ → scheme.toCellScheme.grade c < n
  /-- Completeness at every graded face other than `(univ, n)` and `(univ, n + 1)`. -/
  exists_gradedIndex_eq : ∀ X ∈ scheme.toCellScheme.gradedFaces, X.1 ≠ univ ∨ X.2 < n →
    ∃ c, scheme.toCellScheme.gradedIndex c = X
  /-- The rows lift capped at every target that is a proper face or has grade below `n`. -/
  cappedLift : ∀ ⦃X Y : Finset (Fin (n + 1)) × ℕ⦄, X ∈ scheme.toCellScheme.gradedFaces →
    Y ∈ scheme.toCellScheme.gradedFaces → ∀ h : X ≤ Y, Y.1 ≠ univ ∨ Y.2 < n →
      scheme.rows.CappedLift h
  /-- The labels. -/
  label : Fin scheme.card → Label.{u}
  /-- The labels are lawful. -/
  isLawful_label : scheme.rows.IsLawful label
  /-- The labels are at the stage. -/
  atStage_label : ∀ c, AtStage α (label c)
  /-- The labels of the private cells are those of `P`. -/
  label_castSuccEmb : ∀ (i : Fin (scheme.comap Fin.castSuccEmb).card) (j : Fin P.card),
    (i : ℕ) = j → label (scheme.cellMap Fin.castSuccEmb i) = P.label j
  /-- The labels of the donor cells are those of `d`. -/
  label_extendByLast : ∀ (i : Fin (scheme.comap (extendByLast f)).card) (j : Fin d.card),
    (i : ℕ) = j → label (scheme.cellMap (extendByLast f) i) = d.label j

namespace AttachedPredecessor

variable {P : StageType.{u} α n} {f : Fin m ↪ Fin n} {d : StageType.{u} α (m + 1)}
  (A : AttachedPredecessor P f d)

/-- No cell of the predecessor lies above `(univ, n)`. -/
theorem not_le (c : Fin A.scheme.card) :
    ¬ ((univ : Finset (Fin (n + 1))), n) ≤ A.scheme.toCellScheme.gradedIndex c := fun h ↦ by
  have hs : A.scheme.toCellScheme.scope c = univ := eq_univ_of_forall fun x ↦ h.1 (mem_univ x)
  exact (A.grade_lt_of_scope_eq c hs).not_ge h.2

/-- The private face has `n` points. -/
theorem card_castSuccEmb : #(univ.map (Fin.castSuccEmb : Fin n ↪ Fin (n + 1))) = n := by simp

/-- The private face is not the full face. -/
theorem castSuccEmb_ne_univ : univ.map (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) ≠ univ :=
  fun h ↦ by
    have := congrArg Finset.card h
    simp at this

/-- A face other than the full one has at most `n` points. -/
theorem card_le_of_ne_univ {B : Finset (Fin (n + 1))} (hB : B ≠ univ) : #B ≤ n := by
  have := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ B, hB⟩)
  simpa using this

/-- A cell of the predecessor of grade `n` has a scope of `n` points. -/
theorem card_scope_of_grade_eq {c : Fin A.scheme.card} (hc : A.scheme.toCellScheme.grade c = n) :
    #(A.scheme.toCellScheme.scope c) = n := by
  have hs : A.scheme.toCellScheme.scope c ≠ univ := fun hs ↦
    (A.grade_lt_of_scope_eq c hs).ne hc
  exact le_antisymm (card_le_of_ne_univ hs)
    ((le_of_eq hc.symm).trans (A.isWellFormed.isWellFormed.grade_le_card c))

variable (M : ℕ) (r : Fin M → Fin (A.scheme.card + M) → Label.{u})

/-- **The layer**: the predecessor with `M` cells of full scope and grade `n` appended, the `i`-th
with row `r i`. -/
abbrev layerScheme : Scheme.{u} (n + 1) := A.scheme.appendFullCells n M r A.not_le

/-- **The lifts of the predecessor in the layer scheme**: at every target that is a proper face
or has grade below `n`, the lifts are those of the predecessor. -/
theorem cappedLift_layerScheme {X Y : Finset (Fin (n + 1)) × ℕ}
    (hX : X ∈ (A.layerScheme M r).toCellScheme.gradedFaces)
    (hY : Y ∈ (A.layerScheme M r).toCellScheme.gradedFaces) (h : X ≤ Y)
    (hlow : Y.1 ≠ univ ∨ Y.2 < n) : (A.layerScheme M r).rows.CappedLift h := by
  have hnot : ∀ Z : Finset (Fin (n + 1)) × ℕ, Z ≤ Y → ¬ ((univ : Finset (Fin (n + 1))), n) ≤ Z :=
    fun Z hZ hle ↦ by
      rcases hlow with h1 | h2
      · exact h1 (eq_univ_of_forall fun x ↦ (hle.trans hZ).1 (mem_univ x))
      · exact h2.not_ge (hle.trans hZ).2
  refine CellScheme.Rows.CappedLift.of_comap (Scheme.isLowerEmbedding_castAdd n M r A.not_le)
    (Scheme.image_castAdd_below (hnot X h)) (Scheme.image_castAdd_below (hnot Y le_rfl)) le_rfl
    (X' := X) (Y' := Y) (h' := h) ?_
  rw [Scheme.comap_rows_castAdd]
  exact A.cappedLift hX hY h hlow

/-- **The lift from the other coatoms is below the cap.**  From a face `B` of `n` points other
than the private face, the rows of the layer scheme lift capped to `(univ, n)`: every prescribed
cell of grade `n` below `(B, n)` is a muted cell of the predecessor, so `⊥`, and the lift at the
lower grade suffices (`CellScheme.Rows.exists_lift_of_le_cap`). -/
theorem cappedLift_coatom_layerScheme (hn : 2 ≤ n) {B : Finset (Fin (n + 1))}
    (hB : B ∈ A.scheme.toCellScheme.faces) (hBu : B ≠ univ) (hBc : #B = n)
    (hBp : B ≠ univ.map Fin.castSuccEmb) :
    (A.layerScheme M r).rows.CappedLift (X := (B, n)) (Y := ((univ : Finset (Fin (n + 1))), n))
      ⟨subset_univ _, le_rfl⟩ := by
  refine (CellScheme.Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  have hlift : (A.layerScheme M r).rows.CappedLift
      (X := (B, n - 1)) (Y := ((univ : Finset (Fin (n + 1))), n - 1)) ⟨subset_univ _, le_rfl⟩ :=
    A.cappedLift_layerScheme M r (X := (B, n - 1)) (Y := ((univ : Finset (Fin (n + 1))), n - 1))
      ⟨hB, by omega, by simp only [hBc]; omega⟩
      ⟨A.isWellFormed.univ_mem_faces, by omega, by simp; omega⟩ _ (.inr (by omega))
  suffices hhigh : ∀ e : (A.layerScheme M r).toCellScheme.below (B, n),
      n - 1 < (A.layerScheme M r).toCellScheme.grade e.1 → p e ≤ c by
    obtain ⟨r', hr', hr'c, hr'p⟩ := CellScheme.Rows.exists_lift_of_le_cap
      (X := (B, n)) (Y := ((univ : Finset (Fin (n + 1))), n)) ⟨subset_univ _, le_rfl⟩
      (j := n - 1) (Nat.sub_le n 1) hlift hp hq hc hpq hhigh
    exact ⟨r', hr', hr'c, hr'p⟩
  intro e he
  -- A prescribed cell of grade `n` below `(B, n)` is an old cell, muted.
  have hBn : ¬ ((univ : Finset (Fin (n + 1))), n) ≤ (B, n) := fun h ↦
    hBu (univ_subset_iff.mp h.1)
  have hlt := Scheme.lt_card_of_mem_below (S := A.scheme) (k := n) (M := M) hBn e.2
  set e₀ : Fin A.scheme.card := ⟨e.1, hlt⟩
  have he₀ : Fin.castAdd M e₀ = e.1 := Fin.ext rfl
  have hge : A.scheme.toCellScheme.grade e₀ = n := by
    have h1 : (A.layerScheme M r).toCellScheme.grade e.1 ≤ n := e.2.2
    rw [← he₀, Scheme.appendFullCellsScheme_grade_castAdd] at h1 he
    omega
  have hse : A.scheme.toCellScheme.scope e₀ = B := by
    have h1 : (A.layerScheme M r).toCellScheme.scope e.1 ⊆ B := e.2.1
    rw [← he₀, Scheme.appendFullCellsScheme_scope_castAdd] at h1
    exact eq_of_subset_of_card_le h1 (by rw [hBc, A.card_scope_of_grade_eq hge])
  have hrow : (A.layerScheme M r).rows.row e.1
      ⟨e.1, (A.layerScheme M r).toCellScheme.mem_below_gradedIndex e.1⟩ = ⊥ := by
    rw [← A.mute e₀ hge (hse ▸ hBp)]
    exact Scheme.appendFullCells_row_castAdd (r' := r) (h := A.not_le) e₀ _
  have h0 := (CellScheme.Rows.isLawfulBelow_extendBot.mpr hp).eq_bot_of_row_self_eq_bot e.2 hrow
  rw [CellScheme.Rows.extendBot_of_mem p e.2] at h0
  rw [h0]
  exact bot_le

/-- **The private lift from its active part.**  The rows of the layer scheme lift capped from the
private face `(univ.map Fin.castSuccEmb, n)` to `(univ, n)` once every **active** prescription,
one above the cap at some private cell of grade `n`, lifts. -/
theorem cappedLift_private_of_active (hn : 2 ≤ n)
    (hact : ∀ c : Label.{u}, IsSelfVisible n c →
      ∀ (p : (A.layerScheme M r).toCellScheme.below (univ.map Fin.castSuccEmb, n) → Label.{u})
        (q : (A.layerScheme M r).toCellScheme.below (univ, n) → Label.{u}),
        (A.layerScheme M r).rows.IsLawfulBelow _ p →
        (A.layerScheme M r).rows.IsLawfulBelow _ q →
        (∀ e, min (q (Set.inclusion ((A.layerScheme M r).toCellScheme.below_mono
          (show (univ.map Fin.castSuccEmb, n) ≤ ((univ : Finset (Fin (n + 1))), n) from
            ⟨subset_univ _, le_rfl⟩)) e)) c = min (p e) c) →
        (∃ e, (A.layerScheme M r).toCellScheme.grade e.1 = n ∧ c < p e) →
        ∃ q' : (A.layerScheme M r).toCellScheme.below (univ, n) → Label.{u},
          (A.layerScheme M r).rows.IsLawfulBelow _ q' ∧ (∀ e, min (q' e) c = min (q e) c) ∧
          ∀ e, q' (Set.inclusion ((A.layerScheme M r).toCellScheme.below_mono
            (show (univ.map Fin.castSuccEmb, n) ≤ ((univ : Finset (Fin (n + 1))), n) from
              ⟨subset_univ _, le_rfl⟩)) e) = p e) :
    (A.layerScheme M r).rows.CappedLift
      (X := (univ.map Fin.castSuccEmb, n)) (Y := ((univ : Finset (Fin (n + 1))), n))
      ⟨subset_univ _, le_rfl⟩ := by
  refine (CellScheme.Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  by_cases hhigh : ∃ e, (A.layerScheme M r).toCellScheme.grade e.1 = n ∧ c < p e
  · exact hact c hc p q hp hq hpq hhigh
  push Not at hhigh
  have hwf := A.isWellFormed.isWellFormed
  have hF : univ.map Fin.castSuccEmb ∈ (A.layerScheme M r).toCellScheme.faces :=
    A.mem_faces_castSuccEmb
  have hlift : (A.layerScheme M r).rows.CappedLift
      (X := (univ.map Fin.castSuccEmb, n - 1)) (Y := ((univ : Finset (Fin (n + 1))), n - 1))
      ⟨subset_univ _, le_rfl⟩ :=
    A.cappedLift_layerScheme M r (X := (univ.map Fin.castSuccEmb, n - 1))
      (Y := ((univ : Finset (Fin (n + 1))), n - 1))
      ⟨hF, by omega, by rw [card_castSuccEmb]; omega⟩
      ⟨A.isWellFormed.univ_mem_faces, by omega, by simp; omega⟩ _ (.inr (by omega))
  obtain ⟨r', hr', hr'c, hr'p⟩ := CellScheme.Rows.exists_lift_of_le_cap
    (X := (univ.map Fin.castSuccEmb, n)) (Y := ((univ : Finset (Fin (n + 1))), n))
    ⟨subset_univ _, le_rfl⟩ (j := n - 1) (Nat.sub_le n 1) hlift hp hq hc hpq fun e he ↦
      hhigh e (le_antisymm e.2.2 (by omega))
  exact ⟨r', hr', hr'c, hr'p⟩

/-- **Legality of the layer scheme below its full grade** `n + 1`, for `2 ≤ n`, from lawful and
coded new rows and the lift from the private face into `(univ, n)`; the lift from the other coatom
is `StageType.AttachedPredecessor.cappedLift_coatom_layerScheme`. -/
theorem isLegalBelowFullGrade (hn : 2 ≤ n) (hM : 0 < M)
    (hr : ∀ i, (A.layerScheme M r).rows.IsLawful (r i))
    (hcoded : ∀ i x, r i x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hpriv : (A.layerScheme M r).rows.CappedLift
      (X := (univ.map Fin.castSuccEmb, n)) (Y := ((univ : Finset (Fin (n + 1))), n))
      ⟨subset_univ _, le_rfl⟩) :
    (A.layerScheme M r).IsLegalBelowFullGrade where
  isWellFormed := Scheme.isWellFormed_appendFullCells A.isWellFormed (by omega) (Nat.le_succ n)
  isCoded := Scheme.isCoded_appendFullCells A.isCoded hcoded
  isConsistent := Scheme.isConsistent_appendFullCells A.isConsistent hr
  isBountiful := CellScheme.Rows.isBountiful_of_cappedLift_full (A := univ) (N := n)
    (fun B _ ↦ subset_univ B) (fun _ _ hB ↦ card_le_of_ne_univ hB)
    (fun _ _ hX hY h hlow ↦ A.cappedLift_layerScheme M r hX hY h hlow) fun B hB hBu hBc ↦ by
      by_cases hBp : B = univ.map Fin.castSuccEmb
      · subst hBp
        exact hpriv
      · exact A.cappedLift_coatom_layerScheme M r hn hB hBu hBc hBp
  grade_lt c := by
    induction c using Fin.addCases with
    | right i =>
      rw [Scheme.appendFullCellsScheme_grade_natAdd]
      exact Nat.lt_succ_self n
    | left c =>
      rw [Scheme.appendFullCellsScheme_grade_castAdd]
      by_cases hs : A.scheme.toCellScheme.scope c = univ
      · exact (A.grade_lt_of_scope_eq c hs).trans (Nat.lt_succ_self n)
      · have h1 := A.isWellFormed.isWellFormed.grade_le_card c
        have h2 : #(A.scheme.toCellScheme.scope c) < n + 1 := by
          have := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, hs⟩)
          simpa using this
        omega
  exists_gradedIndex_eq X hX hXn := by
    by_cases hXu : X = ((univ : Finset (Fin (n + 1))), n)
    · exact ⟨Fin.natAdd A.scheme.card ⟨0, hM⟩, by
        rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd, hXu]⟩
    · have hlow : X.1 ≠ univ ∨ X.2 < n := by
        by_contra hcon
        push Not at hcon
        exact hXu (Prod.ext hcon.1 (by omega))
      obtain ⟨c, hc⟩ := A.exists_gradedIndex_eq X hX hlow
      exact ⟨Fin.castAdd M c, by rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, hc]⟩


/-! ### The field layer over the predecessor -/

/-- The cells of the predecessor of grade at most `n` lie below the private face at the grade `n`,
or below the full face at the grade `n - 1`, or are muted cells of grade `n` off the private
face. -/
theorem le_or_le_or_mute (c : Fin A.scheme.card) (hc : A.scheme.toCellScheme.grade c ≤ n) :
    A.scheme.toCellScheme.gradedIndex c ≤ (univ.map Fin.castSuccEmb, n) ∨
      A.scheme.toCellScheme.gradedIndex c ≤ ((univ : Finset (Fin (n + 1))), n - 1) ∨
        (A.scheme.toCellScheme.grade c = n ∧
          A.scheme.toCellScheme.scope c ≠ univ.map Fin.castSuccEmb) := by
  rcases hc.lt_or_eq with hlt | heq
  · -- The grade of the graded index is the grade of the cell.
    exact .inr (.inl ⟨subset_univ _, by change A.scheme.toCellScheme.grade c ≤ n - 1; omega⟩)
  · by_cases hs : A.scheme.toCellScheme.scope c = univ.map Fin.castSuccEmb
    · exact .inl ⟨hs.le, heq.le⟩
    · exact .inr (.inr ⟨heq, hs⟩)

/-- **The lift from the private face through the canonical field layer.**  The rows of the
canonical field layer of the predecessor at the grade `n` lift capped from the private face
`(univ.map Fin.castSuccEmb, n)` to `(univ, n)`: the one-grade lift
(`CellScheme.Rows.cappedLift_of_boundary_short`) with the boundary the private face at the grade
`n` and the full face at the grade `n - 1`, the lifts of the predecessor, the extension from the
boundary at the cap `⊥` (`Scheme.extendsFromBoundary_bot_fieldLayer_of_closed`) and at the
positive short caps along every new row
(`Scheme.extendsFromBoundary_fieldLayer_of_isShort_of_mute`); off the boundary lie the muted cells
of the other coatom. -/
theorem cappedLift_private_fieldLayer (hn : 2 ≤ n) :
    (A.scheme.fieldLayer n A.not_le).rows.CappedLift
      (X := (univ.map Fin.castSuccEmb, n)) (Y := ((univ : Finset (Fin (n + 1))), n))
      ⟨subset_univ _, le_rfl⟩ := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  set S := A.scheme
  set C : Finset (Fin (j + 1 + 1)) := univ.map Fin.castSuccEmb
  have hCne : ¬ (univ : Finset (Fin (j + 1 + 1))) ⊆ C := fun h ↦
    castSuccEmb_ne_univ (univ_subset_iff.mp h)
  have hF : C ∈ (S.fieldLayer (j + 1) A.not_le).toCellScheme.faces := A.mem_faces_castSuccEmb
  have hFu : (univ : Finset (Fin (j + 1 + 1))) ∈
      (S.fieldLayer (j + 1) A.not_le).toCellScheme.faces :=
    A.isWellFormed.univ_mem_faces
  -- The lift of the predecessor from the private face to the full face at the grade `j`.
  have hlow : (S.fieldLayer (j + 1) A.not_le).rows.CappedLift
      (X := (C, j)) (Y := ((univ : Finset (Fin (j + 1 + 1))), j)) ⟨subset_univ _, le_rfl⟩ :=
    A.cappedLift_layerScheme _ _ (X := (C, j)) (Y := ((univ : Finset (Fin (j + 1 + 1))), j))
      ⟨hF, by omega, by rw [card_castSuccEmb]; omega⟩ ⟨hFu, by omega, by simp; omega⟩ _
      (.inr (by omega))
  -- The cells of grade at most `j + 1` off the boundary: muted, and closed under smaller scopes.
  have hoff : ∀ t, S.toCellScheme.gradedIndex t ≤ ((univ : Finset (Fin (j + 1 + 1))), j + 1) →
      ¬ S.toCellScheme.gradedIndex t ≤ (C, j + 1) →
      ¬ S.toCellScheme.gradedIndex t ≤ ((univ : Finset (Fin (j + 1 + 1))), j) →
        S.toCellScheme.grade t = j + 1 ∧ S.toCellScheme.scope t ≠ C := fun t ht h₁ h₂ ↦ by
    rcases A.le_or_le_or_mute t ht.2 with h | h | h
    · exact absurd h h₁
    · exact absurd h h₂
    · exact h
  have hmute : ∀ t ∈ S.toCellScheme.below ((univ : Finset (Fin (j + 1 + 1))), j + 1),
      t ∉ S.toCellScheme.below (C, j + 1) →
      t ∉ S.toCellScheme.below ((univ : Finset (Fin (j + 1 + 1))), j) →
        S.rows.row t ⟨t, S.toCellScheme.mem_below_gradedIndex t⟩ = ⊥ := fun t ht h₁ h₂ ↦ by
    obtain ⟨hg, hs⟩ := hoff t ht h₁ h₂
    exact A.mute t hg hs
  have hclosed : ∀ s t, t ∈ S.toCellScheme.below ((univ : Finset (Fin (j + 1 + 1))), j + 1) →
      t ∉ S.toCellScheme.below (C, j + 1) →
      t ∉ S.toCellScheme.below ((univ : Finset (Fin (j + 1 + 1))), j) →
      S.toCellScheme.scope s ⊆ S.toCellScheme.scope t →
      S.toCellScheme.grade s = S.toCellScheme.grade t →
        s ∉ S.toCellScheme.below (C, j + 1) ∧
          s ∉ S.toCellScheme.below ((univ : Finset (Fin (j + 1 + 1))), j) := by
    intro s t ht h₁ h₂ hst hg
    obtain ⟨htg, hts⟩ := hoff t ht h₁ h₂
    refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
    · -- The scope of `s` has the `j + 1` points of the scope of `t`, so it is that scope.
      have hss : S.toCellScheme.scope s = S.toCellScheme.scope t :=
        eq_of_subset_of_card_le hst (by
          rw [A.card_scope_of_grade_eq htg]
          exact (le_of_eq (hg.trans htg).symm).trans
            (A.isWellFormed.isWellFormed.grade_le_card s))
      have hsC : S.toCellScheme.scope s ⊆ C := ((S.toCellScheme.gradedIndex_le_iff).mp hs).1
      exact hts (eq_of_subset_of_card_le (hss ▸ hsC)
        (by rw [card_castSuccEmb, A.card_scope_of_grade_eq htg]))
    · have := ((S.toCellScheme.gradedIndex_le_iff).mp hs).2
      omega
  have hU : ¬ ((univ : Finset (Fin (j + 1 + 1))), j + 1) ≤ (C, j + 1) := fun h ↦ hCne h.1
  have hV : ¬ ((univ : Finset (Fin (j + 1 + 1))), j + 1) ≤ ((univ : Finset (Fin (j + 1 + 1))), j) :=
    fun h ↦ by
      have := h.2
      -- The second components of the pairs.
      change j + 1 ≤ j at this
      omega
  obtain ⟨c₀, hc₀⟩ := A.exists_gradedIndex_eq (C, j + 1)
    ⟨A.mem_faces_castSuccEmb, by omega, by rw [card_castSuccEmb]⟩ (.inl castSuccEmb_ne_univ)
  obtain ⟨i₀, -⟩ := Scheme.exists_catalogueEntry_eq (S := S) (k := j + 1)
    (Scheme.orbitCode_splice_bot_mem_catalogue (A.isLawful_label.isLawfulBelow _))
  refine CellScheme.Rows.cappedLift_of_boundary_short (U := (C, j + 1))
    (V := ((univ : Finset (Fin (j + 1 + 1))), j)) (O := (C, j)) (subset_univ _)
    ⟨Fin.castAdd _ c₀, by rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, hc₀]⟩ hlow le_rfl
    ⟨Subset.rfl, by omega⟩ ⟨subset_univ _, le_rfl⟩ ⟨subset_univ _, le_rfl⟩
    ⟨subset_univ _, by omega⟩ (fun d hdU hdV ↦ ⟨hdU.1, hdV.2⟩)
    (CellScheme.Rows.cappedLift_refl _) hlow
    (Scheme.extendsFromBoundary_bot_fieldLayer_of_closed hU hV hclosed)
    ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _⟩ fun u hu ↦ ?_
  obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq (hS := A.not_le) hu
  refine ⟨Scheme.isConsistent_fieldLayer A.isConsistent _, fun d ↦ ?_, fun d ↦ ?_,
    fun h hh hsh hbot ↦ Scheme.extendsFromBoundary_fieldLayer_of_isShort_of_mute hU hV hmute
      hclosed hu hh hsh hbot⟩
  · exact (Scheme.isShort_ne_top_row_fieldLayer i _).1
  · exact (Scheme.isShort_ne_top_row_fieldLayer i _).2


/-- **The canonical field layer of the predecessor is legal below its full grade** `n + 1`, for
`2 ≤ n`: its new rows are the field rows of the catalogue entries, lawful and coded, the catalogue
is not empty, and the rows lift capped from the private face
(`StageType.AttachedPredecessor.cappedLift_private_fieldLayer`). -/
theorem isLegalBelowFullGrade_fieldLayer (hn : 2 ≤ n) :
    (A.scheme.fieldLayer n A.not_le).IsLegalBelowFullGrade := by
  obtain ⟨i₀, -⟩ := Scheme.exists_catalogueEntry_eq (S := A.scheme) (k := n)
    (Scheme.orbitCode_splice_bot_mem_catalogue (A.isLawful_label.isLawfulBelow _))
  exact A.isLegalBelowFullGrade _ _ hn (Fin.pos i₀)
    (fun i ↦ Scheme.isLawful_fieldRow (Scheme.catalogueEntry_mem i))
    (fun i x ↦ lt_omega0_sq_of_mem_codeGrid
      (Scheme.fieldRow_mem_codeGrid (Scheme.catalogueEntry_mem i) x))
    (A.cappedLift_private_fieldLayer hn)


/-! ### The legal coface carrying the donor -/

/-- The predecessor as a stage type on `n + 1` points, with its labels. -/
def toStageType : StageType.{u} α (n + 1) where
  toScheme := A.scheme
  label := A.label
  isWellFormed := A.isWellFormed
  isCoded := A.isCoded
  isLawful := A.isLawful_label
  atStage := A.atStage_label

/-- The private face of the predecessor is `P`. -/
theorem restrictFace_castSuccEmb_toStageType :
    restrictFace Fin.castSuccEmb A.toStageType = some P :=
  (restrictFace_eq_some_iff _ _).mpr ⟨A.mem_faces_castSuccEmb,
    ext A.comap_castSuccEmb fun i j h ↦ A.label_castSuccEmb i j h⟩

/-- The donor face of the predecessor is `d`. -/
theorem restrictFace_extendByLast_toStageType :
    restrictFace (extendByLast f) A.toStageType = some d :=
  (restrictFace_eq_some_iff _ _).mpr ⟨A.mem_faces_extendByLast,
    ext A.comap_extendByLast fun i j h ↦ A.label_extendByLast i j h⟩

include A in
/-- **The legal coface carrying the donor.**  At a stage that is zero or a limit, for `2 ≤ n` and
`m < n`, an attached predecessor gives a legal stage type on `n + 1` points whose faces along
`Fin.castSuccEmb` and `extendByLast f` are literally `P` and `d`: the canonical field layer of the
predecessor at the grade `n`, labelled by an extension of the labels of the predecessor
(`Scheme.exists_isLawful_fieldLayer`) reduced to the stage, with the apex added
(`StageType.addApex`).  The faces are those of the predecessor
(`StageType.restrictFace_eq_of_strictMono`, `StageType.restrictFace_addApex`).  No gate is
built here. -/
theorem exists_isLegal_coface (hα : Order.IsSuccPrelimit α) (hn : 2 ≤ n) (hm : m < n) :
    ∃ Q : StageType.{u} α (n + 1), Q.IsLegal ∧ restrictFace Fin.castSuccEmb Q = some P ∧
      restrictFace (extendByLast f) Q = some d ∧
      Q.toCellScheme.faces = A.scheme.toCellScheme.faces := by
  have hL : (A.scheme.fieldLayer n A.not_le).IsLegalBelowFullGrade :=
    A.isLegalBelowFullGrade_fieldLayer hn
  obtain ⟨ρ, hρ, hρA⟩ := Scheme.exists_isLawful_fieldLayer (hS := A.not_le) A.isLawful_label
  have ht : (ofIsLawful hα (A.scheme.fieldLayer n A.not_le) hL.isWellFormed hL.isCoded ρ
      hρ).IsLegalBelowFullGrade := hL
  -- The faces of the layer type along proper faces are those of the predecessor.
  have hface : ∀ {k : ℕ} (g : Fin k ↪ Fin (n + 1)), univ.map g ≠ univ →
      restrictFace g (ofIsLawful hα (A.scheme.fieldLayer n A.not_le) hL.isWellFormed hL.isCoded
        ρ hρ) = restrictFace g A.toStageType := by
    intro k g hg
    refine restrictFace_eq_of_strictMono g (s := A.toStageType)
      (t := ofIsLawful hα (A.scheme.fieldLayer n A.not_le) hL.isWellFormed hL.isCoded ρ hρ)
      (φ := Fin.castAdd _) (Fin.strictMono_castAdd _)
      (Scheme.isLowerEmbedding_castAdd n (A.scheme.catalogue n).card
        (fun i ↦ A.scheme.fieldRow n (A.scheme.catalogueEntry n i)) A.not_le)
      (Scheme.appendFullCellsScheme_scope_castAdd _ _ _)
      (Scheme.comap_rows_castAdd (S := A.scheme) (k := n) (M := (A.scheme.catalogue n).card)
        (r := fun i ↦ A.scheme.fieldRow n (A.scheme.catalogueEntry n i)) (h := A.not_le)) rfl rfl
      (fun c ↦ ?_) fun z hz ↦ ?_
    · -- The labels of `ofIsLawful` are the reduced labels (by definition).
      change Label.reduce α (ρ (Fin.castAdd _ c)) = A.label c
      rw [hρA c]
      exact (A.atStage_label c).reduce_eq
    · induction z using Fin.addCases with
      | left c => exact ⟨c, rfl⟩
      | right i =>
        refine absurd (eq_univ_of_forall fun x ↦ ?_) hg
        have hx : x ∈ (A.scheme.fieldLayer n A.not_le).toCellScheme.scope (Fin.natAdd _ i) := by
          rw [Scheme.appendFullCellsScheme_scope_natAdd]; exact mem_univ x
        obtain ⟨y, rfl⟩ := hz (mem_coe.mpr hx)
        exact mem_map_of_mem _ (mem_univ y)
  have hdn : univ.map (extendByLast f) ≠ (univ : Finset (Fin (n + 1))) := fun h ↦ by
    have := congrArg Finset.card h
    simp at this
    omega
  refine ⟨_, isLegal_addApex ht (by omega), ?_, ?_, rfl⟩
  · rw [restrictFace_addApex ht _ _ castSuccEmb_ne_univ, hface _ castSuccEmb_ne_univ,
      A.restrictFace_castSuccEmb_toStageType]
  · rw [restrictFace_addApex ht _ _ hdn, hface _ hdn, A.restrictFace_extendByLast_toStageType]


/-! ### The converse: the part of a legal coface below the layer -/

section Cut

variable {Q : StageType.{u} α (n + 1)}

/-- The cells of `Q` not above `(univ, n)`. -/
def cellsBelowLayer (Q : StageType.{u} α (n + 1)) : Finset (Fin Q.card) :=
  {c | ¬ ((univ : Finset (Fin (n + 1))), n) ≤ Q.toCellScheme.gradedIndex c}

/-- The enumeration in increasing order of the cells of `Q` not above `(univ, n)`. -/
noncomputable def embBelowLayer (Q : StageType.{u} α (n + 1)) :
    Fin #(cellsBelowLayer Q) ↪o Fin Q.card :=
  (cellsBelowLayer Q).orderEmbOfFin rfl

theorem not_le_embBelowLayer (i : Fin #(cellsBelowLayer Q)) :
    ¬ ((univ : Finset (Fin (n + 1))), n) ≤ Q.toCellScheme.gradedIndex (embBelowLayer Q i) := by
  have h := (cellsBelowLayer Q).orderEmbOfFin_mem rfl i
  simp only [cellsBelowLayer, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h

theorem mem_range_embBelowLayer {c : Fin Q.card}
    (hc : ¬ ((univ : Finset (Fin (n + 1))), n) ≤ Q.toCellScheme.gradedIndex c) :
    c ∈ Set.range (embBelowLayer Q) := by
  rw [embBelowLayer, range_orderEmbOfFin]
  exact mem_coe.mpr (by simpa [cellsBelowLayer] using hc)

/-- The cells not above `(univ, n)` form a lower embedding. -/
theorem isLowerEmbedding_embBelowLayer :
    (Q.toCellScheme.reindex (embBelowLayer Q)).IsLowerEmbedding Q.toCellScheme
      (embBelowLayer Q) where
  injective := (embBelowLayer Q).injective
  grade_eq _ := rfl
  le_iff _ _ := Iff.rfl
  mem_range t _ hd := mem_range_embBelowLayer fun h ↦ not_le_embBelowLayer t (h.trans hd)

/-- Below a pair not above `(univ, n)`, the cells of the cut are those of `Q`. -/
theorem image_embBelowLayer_below {X : Finset (Fin (n + 1)) × ℕ}
    (hX : ¬ ((univ : Finset (Fin (n + 1))), n) ≤ X) :
    embBelowLayer Q '' (Q.toCellScheme.reindex (embBelowLayer Q)).below X =
      Q.toCellScheme.below X := by
  ext c
  refine ⟨fun ⟨i, hi, hic⟩ ↦ hic ▸ hi, fun hc ↦ ?_⟩
  obtain ⟨i, rfl⟩ := mem_range_embBelowLayer (Q := Q) fun h ↦ hX (h.trans hc)
  exact ⟨i, hc, rfl⟩

/-- **The cut of `Q` below the layer**, as a stage type: the cells not above `(univ, n)`, with
their scopes, grades, rows, and labels, and the faces of `Q`. -/
noncomputable def cutBelowLayer (Q : StageType.{u} α (n + 1)) : StageType.{u} α (n + 1) where
  toScheme := ⟨#(cellsBelowLayer Q), Q.toCellScheme.reindex (embBelowLayer Q),
    Q.rows.comap isLowerEmbedding_embBelowLayer⟩
  label := Q.label ∘ embBelowLayer Q
  isWellFormed := ⟨Q.isWellFormed.ground_eq, Q.isWellFormed.isWellFormed.reindex _⟩
  isCoded _ _ := Q.isCoded _ _
  isLawful := Q.isLawful.comap isLowerEmbedding_embBelowLayer
  atStage _ := Q.atStage _

/-- The proper faces of the cut are those of `Q`. -/
theorem restrictFace_cutBelowLayer {k : ℕ} (g : Fin k ↪ Fin (n + 1)) (hg : univ.map g ≠ univ) :
    restrictFace g (cutBelowLayer Q) = restrictFace g Q := by
  refine (restrictFace_eq_of_strictMono (t := Q) (s := cutBelowLayer Q) g
    (φ := embBelowLayer Q) (embBelowLayer Q).strictMono isLowerEmbedding_embBelowLayer
    (fun _ ↦ rfl) rfl rfl rfl (fun _ ↦ rfl) fun z hz ↦ ?_).symm
  refine mem_range_embBelowLayer fun h ↦ hg (eq_univ_of_forall fun x ↦ ?_)
  obtain ⟨y, rfl⟩ := hz (mem_coe.mpr (h.1 (mem_univ x)))
  exact mem_map_of_mem _ (mem_univ y)

/-- **An attached predecessor from a legal coface with muted cells.**  A legal stage type on `n + 1`
points whose faces along `Fin.castSuccEmb` and `extendByLast f` are `P` and `d`, and whose cells
of grade `n` off the private face and off the full face are muted (row `⊥` at themselves), gives
an attached predecessor: its cells not above `(univ, n)`.  Conversely
`StageType.AttachedPredecessor.exists_isLegal_coface` turns an attached predecessor into a legal
coface. -/
noncomputable def ofIsLegal (hQ : Q.IsLegal) (hP : restrictFace Fin.castSuccEmb Q = some P)
    (hd : restrictFace (extendByLast f) Q = some d) (hm : m < n)
    (hmute : ∀ c, Q.toCellScheme.grade c = n → Q.toCellScheme.scope c ≠ univ →
      Q.toCellScheme.scope c ≠ univ.map Fin.castSuccEmb →
        Q.rows.row c ⟨c, Q.toCellScheme.mem_below_gradedIndex c⟩ = ⊥) :
    AttachedPredecessor P f d :=
  have hdn : univ.map (extendByLast f) ≠ (univ : Finset (Fin (n + 1))) := fun h ↦ by
    have := congrArg Finset.card h
    simp at this
    omega
  have hP' : restrictFace Fin.castSuccEmb (cutBelowLayer Q) = some P :=
    (restrictFace_cutBelowLayer _ castSuccEmb_ne_univ).trans hP
  have hd' : restrictFace (extendByLast f) (cutBelowLayer Q) = some d :=
    (restrictFace_cutBelowLayer _ hdn).trans hd
  { scheme := (cutBelowLayer Q).toScheme
    isWellFormed := (cutBelowLayer Q).isWellFormed
    isCoded := (cutBelowLayer Q).isCoded
    isConsistent := hQ.isConsistent.comap isLowerEmbedding_embBelowLayer
    mem_faces_castSuccEmb := ((restrictFace_eq_some_iff _ _).mp hP').1
    comap_castSuccEmb := congrArg StageType.toScheme ((restrictFace_eq_some_iff _ _).mp hP').2
    mem_faces_extendByLast := ((restrictFace_eq_some_iff _ _).mp hd').1
    comap_extendByLast := congrArg StageType.toScheme ((restrictFace_eq_some_iff _ _).mp hd').2
    mute := fun c hc hs ↦ hmute (embBelowLayer Q c) hc (fun hu ↦ not_le_embBelowLayer (Q := Q) c
      ⟨fun x _ ↦ show x ∈ Q.toCellScheme.scope (embBelowLayer Q c) by rw [hu]; exact mem_univ x,
        hc.ge⟩) hs
    grade_lt_of_scope_eq := fun c hc ↦ by
      have h := not_le_embBelowLayer (Q := Q) c
      by_contra hn
      exact h ⟨fun x _ ↦ by
        -- The scope of a cell of the cut is its scope in `Q` (reindexing).
        change x ∈ Q.toCellScheme.scope (embBelowLayer Q c)
        have : (cutBelowLayer Q).toCellScheme.scope c = univ := hc
        exact this ▸ mem_univ x, not_lt.mp hn⟩
    exists_gradedIndex_eq := fun X hX hlow ↦ by
      obtain ⟨c, hc⟩ := hQ.isComplete X hX
      have hnot : ¬ ((univ : Finset (Fin (n + 1))), n) ≤ Q.toCellScheme.gradedIndex c := by
        rw [hc]
        rintro ⟨h1, h2⟩
        rcases hlow with h | h
        · exact h (univ_subset_iff.mp h1)
        · exact (_root_.not_le.mpr h) h2
      obtain ⟨i, rfl⟩ := mem_range_embBelowLayer hnot
      exact ⟨i, hc⟩
    cappedLift := fun X Y hX hY h hlow ↦ by
      have hnot : ∀ Z : Finset (Fin (n + 1)) × ℕ, Z ≤ Y →
          ¬ ((univ : Finset (Fin (n + 1))), n) ≤ Z := fun Z hZ hle ↦ by
        rcases hlow with h1 | h2
        · exact h1 (eq_univ_of_forall fun x ↦ (hle.trans hZ).1 (mem_univ x))
        · exact h2.not_ge (hle.trans hZ).2
      exact (hQ.isBountiful hX hY h).comap isLowerEmbedding_embBelowLayer
        (image_embBelowLayer_below (hnot X h)) (image_embBelowLayer_below (hnot Y le_rfl)) le_rfl
    label := (cutBelowLayer Q).label
    isLawful_label := (cutBelowLayer Q).isLawful
    atStage_label := (cutBelowLayer Q).atStage
    label_castSuccEmb := fun i j h ↦ by
      obtain ⟨hf, heq⟩ := (restrictFace_eq_some_iff _ _).mp hP'
      exact label_congr heq (i := i) (j := j) h
    label_extendByLast := fun i j h ↦ by
      obtain ⟨hf, heq⟩ := (restrictFace_eq_some_iff _ _).mp hd'
      exact label_congr heq (i := i) (j := j) h }

end Cut


end AttachedPredecessor

end StageType

end VaughtConjecture
