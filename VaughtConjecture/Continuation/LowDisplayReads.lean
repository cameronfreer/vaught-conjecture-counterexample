/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowDisplayActual

/-!
# The reading from a level that reads the actual state

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the levels above the
controllers); semantic contract, items 3, 4 and 8.

The acquired contexts carry ordinal labels above their grade
(`Realization.exists_acquired_not_lowBotClass`), and over the canonical levels the separator
cannot be labelled `⊤` then (`ProfileTower.lowDisplay_label_eq_bot`).  This file states what a
level above the LOW layer must provide instead, and proves the reading from it.

**A level reading the actual state** (`ProfileTower.ReadsActual`).  Over a seed `I` on `m + 2`
points, a good level `L` at the grade `g` and the LOW catalogue at `K = g + 1`, a good level `N`
at the grade `m` in which the LOW layer over `L` is a grade prefix at `K` along a cell map `ψ`
keeping the old cells, with a cell `u` of graded index `(univ, m)`, a witness `θ` bounded by `m`
reflecting `⊥`, and two controllers `ilo`, `ihi` (a profile of the catalogue and its partner over
all proper donor cells, the cutoff cut in the grid and below the cutoff), such that `θ` applied to
the row of `u` reads every old cell of grade at most `m` as its glued label, the controller `ihi`
as `⊤`, and the controller `ilo` below the stage.  Every cell of full scope of grade above `K`
then reads the separator above `⊥` somewhere below `u`, which the canonical levels never do
(`ProfileTower.Lvl.iter_read_eq_bot`); no condition on the glued labels above `K` enters.

**The reading** (`ProfileTower.ReadsActual.exists_isLowLayer`, compiled in this repository).  At
a stage that is zero or a limit, when `N` extends at `⊥`, a level reading the actual state gives a
legal display with faces the private context and the donor, literally, a LOW layer at `K`
(`ProfileTower.isLowLayer_of_isGradePrefix`), and its separator labelled by a proper label and
`⊤`: the labels are the decoded row of `u` (`ProfileTower.decodedLabels` at the grade `m`, lawful
by `ProfileTower.isLawful_decodedLabels` with no condition above `m`), extended through the top
layer and reduced to the stage.

When the LOW layer is the level at `m` itself (`K = m`), the controller of the actual profile reads
the actual state (`ProfileTower.lowReading_of_bot`).  Over the canonical levels with `K < m` no
cell of grade `m` reads it unless the faces are `⊥` above `K`.  A level reading the actual state for
`K < m` needs sections indexed by profiles with a cutoff, reading every controller through the
cutoff of the profile itself, with the LOW clause imposed at every grade above `K`; their capped
lift from the two coatoms at each grade above `K` is the LOW step at that grade, not proved here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme StageType

variable {α : Ordinal.{u}} {m g : ℕ} {I : Seed.{u} α m} {o r : Fin I.left.card}

local notation "𝒞" => lowCat I (g + 1) (lowN I (g + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

variable (o r) in
/-- **A level reading the actual state** (see the module docstring): a good level `N` at the grade
`m` above the LOW layer over `L`, with a cell `u` of graded index `(univ, m)` whose row, read by a
witness `θ` bounded by `m` reflecting `⊥`, is the glued labels at the old cells of grade at most
`m`, `⊤` at the controller of a profile `s` of the LOW catalogue, and below the stage at the
controller of its partner. -/
def ReadsActual (L : Lvl I g) (N : Lvl I m) (ψ : Fin (L.catS 𝒞).card → Fin N.S.card) : Prop :=
  ∃ (u : Fin N.S.card) (θ : Label.{u} → Label.{u}) (ilo ihi : Fin (𝒞).card),
    N.S.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), m) ∧
    IsWitness (stepSuppressor m) θ ∧ (∀ x, θ x = ⊥ → x = ⊥) ∧
    (∀ d, I.amalgam.toCellScheme.grade d ≤ m →
      θ (N.S.rowAt u (N.embed d)) = I.amalgam.label d) ∧
    ((𝒞).equivFin.symm ilo).1 = Function.update ((𝒞).equivFin.symm ihi).1 (Sum.inr ())
      (cutoffCut (g + 1) (lowNAll I) ((𝒞).equivFin.symm ihi).1) ∧
    cutoffCut (g + 1) (lowNAll I) ((𝒞).equivFin.symm ihi).1 ∈ grid (g + 1) (bound I) ∧
    cutoffCut (g + 1) (lowNAll I) ((𝒞).equivFin.symm ihi).1 <
      ((𝒞).equivFin.symm ihi).1 (Sum.inr ()) ∧
    θ (N.S.rowAt u (ψ (Fin.natAdd L.S.card ihi))) = ⊤ ∧
    θ (N.S.rowAt u (ψ (Fin.natAdd L.S.card ilo))) < α

/-- **The reading from a level reading the actual state**: at a stage that is zero or a limit, a
good level at the grade `m ≥ 1` above the LOW layer (a grade prefix at `g + 1 ≤ m` keeping the old
cells) that extends at `⊥` and reads the actual state gives a legal display with faces the private
context and the donor, literally, with a LOW layer at `g + 1` whose separator is labelled by a
proper label and `⊤`. -/
theorem ReadsActual.exists_isLowLayer (hα : Order.IsSuccPrelimit α) {L : Lvl I g} (hL : L.Good)
    {N : Lvl I m} (hN : N.Good) (hB : N.HasBotExtension) (hm : 1 ≤ m) (hgm : g + 1 ≤ m)
    {ψ : Fin (L.catS 𝒞).card → Fin N.S.card}
    (hψ : Scheme.IsGradePrefix (L.catS 𝒞) N.S ψ (g + 1))
    (hembed : ∀ d, N.embed d = ψ (Fin.castAdd _ (L.embed d))) (h : ReadsActual o r L N ψ) :
    ∃ (D : StageType.{u} α (m + 2)) (h₁ : restrictFace Fin.castSuccEmb D = some I.left)
      (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some I.right)
      (G : Finset Label.{u}) (entry : Fin D.card → LowField D → Label.{u})
      (s : LowField D → Label.{u}) (lo hi : Fin D.card), D.IsLegal ∧ D.label lo ≠ ⊤ ∧
        D.label hi = ⊤ ∧ IsLowLayer (g + 1) h₁ h₂ o r G entry s lo hi := by
  classical
  obtain ⟨u, θ, ilo, ihi, hu, hθ, hθb, hold, hsep, hmem, hlt, hhi, hlo⟩ := h
  set F := hN.completion hB hm with hF
  have hq₀ := isLawful_decodedLabels hN hθ hθb hu hold fun _ h1 h2 ↦ absurd h2 (by omega)
  obtain ⟨r₁, hr₁, hr₁q⟩ := Scheme.exists_isLawful_fieldLayer (S := N.S) (k := m + 1)
    (hS := N.not_le) hq₀
  have hq : F.scheme.rows.IsLawful (Label.reduce α ∘ r₁) := hr₁.reduce hα
  have hqα (d : Fin F.scheme.card) : AtStage α ((Label.reduce α ∘ r₁) d) := atStage_reduce α _
  have hqe (d : Fin I.amalgam.card) : (Label.reduce α ∘ r₁) (F.embed d) = I.amalgam.label d := by
    change Label.reduce α (r₁ (Fin.castAdd _ (N.embed d))) = _
    rw [hr₁q, decodedLabels_embed hN hold, (I.amalgam.atStage d).reduce_eq]
  have hP : Scheme.IsGradePrefix (L.catS 𝒞) (F.display hq hqα).toScheme
      (Fin.castSucc ∘ Fin.castAdd _ ∘ ψ) (g + 1) :=
    ((F.isGradePrefix_display hq hqα (by omega)).comp
      (Scheme.IsGradePrefix.castAdd (S := N.S) (k := m + 1)
        (M := (N.S.catalogue (m + 1)).card)
        (r := fun i ↦ N.S.fieldRow (m + 1) (N.S.catalogueEntry (m + 1) i))
        (h := N.not_le) (by omega))).comp hψ
  have hface {k : ℕ} {f : Fin k ↪ Fin (m + 2)} (hf : univ.map f ≠ univ)
      {t : StageType.{u} α k} (h : restrictFace f (F.display hq hqα) = some t)
      (h' : restrictFace f I.amalgam = some t) (i : Fin t.card) :
      faceCell h i = (Fin.castSucc ∘ Fin.castAdd _ ∘ ψ)
        (Fin.castAdd (𝒞).card (L.embed (faceCell h' i))) := by
    rw [CompletionBelowFullGrade.faceCell_display _ hf h h']
    change Fin.castSucc (Fin.castAdd _ (N.embed _)) = _
    rw [hembed]
    rfl
  have hgr (i : Fin (𝒞).card) : N.S.toCellScheme.grade (ψ (Fin.natAdd L.S.card i)) ≤ m := by
    rw [hψ.lowerEmb.grade_eq]
    exact (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le.trans hgm
  refine ⟨F.display hq hqα, _, _, _, _, _, _, _, F.isLegal_display hq hqα, fun h' ↦ ?_, ?_,
    isLowLayer_of_isGradePrefix hL hP (F.restrictFace_left_display hqe)
      (F.restrictFace_right_display hqe)
      (hface Coatom.univ_map_left_ne _ I.restrictFace_left)
      (hface Coatom.univ_map_right_ne _ I.restrictFace_right) hsep hmem hlt⟩
  · have h2 := (CompletionBelowFullGrade.display_label_castSucc F hq hqα _).symm.trans h'
    change Label.reduce α (r₁ (Fin.castAdd _ (ψ (Fin.natAdd L.S.card ilo)))) = ⊤ at h2
    rw [hr₁q, decodedLabels_of_le (hgr ilo), reduce_of_lt hlo] at h2
    exact ne_top_of_lt hlo h2
  · refine (CompletionBelowFullGrade.display_label_castSucc F hq hqα _).trans ?_
    change Label.reduce α (r₁ (Fin.castAdd _ (ψ (Fin.natAdd L.S.card ihi)))) = ⊤
    rw [hr₁q, decodedLabels_of_le (hgr ihi), hhi, reduce_top]

end VaughtConjecture.ProfileTower
