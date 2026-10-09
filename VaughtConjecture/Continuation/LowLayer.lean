/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowDisplay
import VaughtConjecture.Continuation.LowProfile

/-!
# LOW controller layers

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3); semantic contract,
items 4 and 8.

The cells of full scope and grade `K` of a LOW display are its **controllers** [Kni26, §3.3].
Each controller carries a **LOW profile** (`Label.IsLowAt`): a labelling of the **fields** of the
display, which are its cells and one more field, the cutoff (`Fin D.card ⊕ Unit`).  The row of a
controller reads every other cell of grade at most `K` at its profile, and every controller at the
**agreement height** (`Label.agreementHeight`, in a finite set of labels `G`) of the two profiles:
the shape of the field rows of `VaughtConjecture.Extension.FieldLayer`, with the cutoff as an
extra field.  The fields are designated from the LOW family: the proper donor fields and the donor
tops are the donor cells whose donor label is, or is not, `⊤`; the owner and the lost top are the
private cells of the owner and of the lost top; the cutoff is the extra field.

**LOW layers** (`StageType.IsLowLayer`).  A display `D` of the LOW family `(t', tb)` has a LOW layer
at grade `K` when every controller carries a LOW profile read by its row as above, and two
controllers, the separator `lo` and `hi`, carry the partner of a profile `s` and `s` itself
(`Label.partner`), with the cutoff cut of `s` below the cutoff of `s` and in `G`.

**The controller reading from a LOW layer** (`StageType.IsLowLayer.isControllerReading`, compiled
in this repository).  For a controller `w` and a witness `(g, σ)` with `g K = ⊤`: the row of `w`
reads the private owner, the lost top and the donor tops at the profile of `w`, and the separator
at the agreement heights of that profile with the partner of `s` and with `s`.  So a strict
reading of the separator activates the LOW clause of the profile of `w`
(`Label.eq_top_of_agreementHeight_partner_lt`), and the donor tops are read as `⊤`.  The private
and donor cells are not controllers: their scopes miss a point
(`StageType.gradedIndex_faceCell_ne`).

**LOW layers at source-gap contexts** (`StageType.HasLowLayers`, in
`VaughtConjecture.MainTheorem.LowDisplayRoute`; open): every LOW family has a legal display with a
LOW layer at `K` whose separator is labelled by a proper label and `⊤`.  It gives controlled LOW
displays (`StageType.HasLowLayers.hasControlledLowDisplays`), hence (R2) for receiving models.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.StageType

open Finset Label

variable {α : Ordinal.{u}} {n m k : ℕ}

/-- **A face cell along a map that is not onto is not of full scope.** -/
theorem gradedIndex_faceCell_ne {D : StageType.{u} α n} {f : Fin m ↪ Fin n}
    {t : StageType.{u} α m} (h : restrictFace f D = some t) (hf : ¬ Function.Surjective f)
    (i : Fin t.card) (K : ℕ) : D.toCellScheme.gradedIndex (faceCell h i) ≠ (univ, K) := by
  intro he
  apply hf
  intro y
  have hy : y ∈ D.toCellScheme.scope (faceCell h i) := by
    rw [show D.toCellScheme.scope (faceCell h i) = univ from congrArg Prod.fst he]
    exact mem_univ y
  rw [scope_faceCell, mem_map] at hy
  obtain ⟨x, -, rfl⟩ := hy
  exact ⟨x, rfl⟩

/-- The initial segment of `k + 1` points is not onto. -/
theorem not_surjective_castSuccEmb : ¬ Function.Surjective (Fin.castSuccEmb : Fin (k + 1) ↪ _) :=
  fun hs ↦ by
    obtain ⟨x, hx⟩ := hs (Fin.last (k + 1))
    exact (Fin.castSucc_lt_last x).ne hx

/-- The extension of the initial segment by the last point misses the lost point. -/
theorem not_surjective_extendByLast_castSuccEmb :
    ¬ Function.Surjective (extendByLast (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) := fun hs ↦ by
  obtain ⟨x, hx⟩ := hs (Fin.castSucc (Fin.last k))
  induction x using Fin.lastCases with
  | last =>
    rw [extendByLast_last] at hx
    exact (Fin.castSucc_lt_last _).ne hx.symm
  | cast x =>
    rw [extendByLast_castSucc] at hx
    exact (Fin.castSucc_lt_last x).ne (Fin.castSucc_injective _ hx)

variable {t' tb : StageType.{u} α (k + 1)} {D : StageType.{u} α (k + 2)}

/-! ### The designated fields -/

/-- The fields of a display: its cells and the cutoff. -/
abbrev LowField (D : StageType.{u} α m) : Type := Fin D.card ⊕ Unit

/-- The proper donor fields: the donor cells whose donor label is not `⊤`. -/
noncomputable def properDonorFields (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some tb) :
    Finset (LowField D) :=
  (univ.filter fun y ↦ tb.label y ≠ ⊤).image fun y ↦ Sum.inl (faceCell h₂ y)

/-- The donor tops: the donor cells whose donor label is `⊤`. -/
def donorTopFields (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some tb) :
    Set (LowField D) :=
  {f | ∃ y, tb.label y = ⊤ ∧ f = Sum.inl (faceCell h₂ y)}

/-! ### LOW layers -/

/-- A **LOW layer** of a display `D` of `(t', tb)` at grade `K`, for the owner `o` and the lost top
`r` of `t'`: a finite set `G` of labels with `⊥`, a LOW profile at every controller (a cell of
graded index `(univ, K)`), read by its row at the other cells of grade at most `K` and, at the
controllers, at agreement heights in `G`; and two controllers `lo` and `hi` carrying the partner
of a profile `s` and `s`, with the cutoff cut of `s` in `G` and below the cutoff of `s`. -/
structure IsLowLayer (K : ℕ) (h₁ : restrictFace Fin.castSuccEmb D = some t')
    (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some tb) (o r : Fin t'.card)
    (G : Finset Label.{u}) (entry : Fin D.card → LowField D → Label.{u})
    (s : LowField D → Label.{u}) (lo hi : Fin D.card) : Prop where
  /-- The grid contains `⊥`. -/
  bot_mem : ⊥ ∈ G
  /-- The profile of every controller is LOW. -/
  isLowAt : ∀ w, D.toCellScheme.gradedIndex w = (univ, K) →
    IsLowAt K (properDonorFields h₂) (donorTopFields h₂) (Sum.inl (faceCell h₁ o))
      (Sum.inl (faceCell h₁ r)) (Sum.inr ()) (entry w)
  /-- A controller reads the other cells of grade at most `K` at its profile. -/
  rowAt_old : ∀ w, D.toCellScheme.gradedIndex w = (univ, K) → ∀ d,
    D.toCellScheme.gradedIndex d ≠ (univ, K) → D.toCellScheme.grade d ≤ K →
      D.rowAt w d = entry w (Sum.inl d)
  /-- A controller reads a controller at the agreement height of their profiles. -/
  rowAt_controller : ∀ w x, D.toCellScheme.gradedIndex w = (univ, K) →
    D.toCellScheme.gradedIndex x = (univ, K) → D.rowAt w x = agreementHeight G (entry w) (entry x)
  /-- The lower separator cell is a controller. -/
  gradedIndex_lo : D.toCellScheme.gradedIndex lo = (univ, K)
  /-- The upper separator cell is a controller. -/
  gradedIndex_hi : D.toCellScheme.gradedIndex hi = (univ, K)
  /-- The upper separator cell carries `s`. -/
  entry_hi : entry hi = s
  /-- The lower separator cell carries the partner of `s`. -/
  entry_lo : entry lo = partner K (properDonorFields h₂) (Sum.inr ()) s
  /-- The cutoff cut of `s` is in the grid. -/
  cutoffCut_mem : cutoffCut K (properDonorFields h₂) s ∈ G
  /-- The cutoff cut of `s` is below its cutoff. -/
  cutoffCut_lt : cutoffCut K (properDonorFields h₂) s < s (Sum.inr ())

/-- **The controller reading of a LOW layer**: the private owner of grade `K`, the lost top and the
donor tops of grade at most `K` are read at the profiles, and the separator at the agreement
heights with the partner of `s` and with `s`; a strict reading of the separator activates the LOW
clause (`Label.eq_top_of_agreementHeight_partner_lt`). -/
theorem IsLowLayer.isControllerReading {K : ℕ} {h₁ : restrictFace Fin.castSuccEmb D = some t'}
    {h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some tb} {o r : Fin t'.card}
    {G : Finset Label.{u}} {entry : Fin D.card → LowField D → Label.{u}}
    {s : LowField D → Label.{u}} {lo hi : Fin D.card}
    (hL : IsLowLayer K h₁ h₂ o r G entry s lo hi)
    (ho : t'.toCellScheme.grade o ≤ K) (hr : t'.toCellScheme.grade r ≤ K)
    (htbK : tb.topGrade ≤ K) :
    IsControllerReading D K (faceCell h₁ o) (faceCell h₁ r) lo hi
      {i | ∃ x, tb.label x = ⊤ ∧ faceCell h₂ x = i} := by
  intro w hw g σ hσ hgK hσo hσr hsep x hx
  have hold₁ (z : Fin t'.card) (hz : t'.toCellScheme.grade z ≤ K) :
      D.rowAt w (faceCell h₁ z) = entry w (Sum.inl (faceCell h₁ z)) :=
    hL.rowAt_old w hw _ (gradedIndex_faceCell_ne h₁ not_surjective_castSuccEmb z K)
      (by rw [grade_faceCell]; exact hz)
  rw [hold₁ o ho] at hσo
  rw [hold₁ r hr] at hσr
  rw [hL.rowAt_controller w lo hw hL.gradedIndex_lo, hL.rowAt_controller w hi hw hL.gradedIndex_hi,
    hL.entry_lo, hL.entry_hi] at hsep
  obtain ⟨y, hy, rfl⟩ := hx
  rw [hL.rowAt_old w hw _ (gradedIndex_faceCell_ne h₂ not_surjective_extendByLast_castSuccEmb y K)
    (by rw [grade_faceCell]; exact topGrade_le_iff.mp htbK y hy)]
  exact eq_top_of_agreementHeight_partner_lt hL.bot_mem hL.cutoffCut_mem hL.cutoffCut_lt
    (hL.isLowAt w hw) hσ hgK hsep hσo hσr _ ⟨y, hy, rfl⟩

end VaughtConjecture.StageType
