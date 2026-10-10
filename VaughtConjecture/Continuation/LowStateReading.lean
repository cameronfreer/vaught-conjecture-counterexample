/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateTower
import VaughtConjecture.Continuation.LowDisplayActual

/-!
# LOW layers from a level reading the actual state

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the display above the
controllers when the faces carry labels other than `⊥` above `K`); semantic contract, items 3, 4
and 8.

**LOW layers from any catalogue of LOW states** (`ProfileTower.ReadsActualOn`,
`ProfileTower.ReadsActualOn.exists_isLowLayer_all`, compiled in this repository, for states LOW
over the proper donor fields of every grade).  The LOW layer of a display
(`ProfileTower.isLowLayer_of_isGradePrefix_all`, `VaughtConjecture.Continuation.LowDisplayLayer`)
uses of the catalogue only that its states lie in the code grid and are LOW; the reading holds for
every such catalogue, in particular for the
state catalogue of the LOW clause (`ProfileTower.sCat`), whose states are normalized by the orbit
code over all fields, not by that of the amalgam part (`ProfileTower.orbitCode_update_cutoffCut`
keeps the partner in it).

**The actual state** (`ProfileTower.actState`: the glued labels with the cutoff `⊤`) is separated
(`ProfileTower.sepInv_actState`).  The padded tower reads it with no hypothesis
(`ProfileTower.exists_isLowLayer_pTower`, `VaughtConjecture.Continuation.LowPaddedReading`).  The
reading of the actual state by the state tower given its lifts
(`ProfileTower.readsActualOn_sTower`), with its chain bounds, remains on the research branch
`research/port-low-padded`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme StageType

variable {α : Ordinal.{u}} {m g : ℕ} {I : Seed.{u} α m} {L : Lvl I g}

/-! ### LOW layers from any catalogue of LOW states -/

section Layer

variable {D : StageType.{u} α (m + 2)} {o r : Fin I.left.card} {C : Finset (CProf I)}

local notation "𝒜all" => lowPred (g + 1) (lowNAll I) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

variable (C) in
/-- **A level reading the actual state, over a catalogue `C` of LOW states**: a good level `N` at
the grade `m` above the LOW layer over `L`, with a cell `u` of graded index `(univ, m)` whose row,
read by a witness `θ` bounded by `m` reflecting `⊥`, is the glued labels at the old cells of grade
at most `m`, `⊤` at the controller of a state `s` of `C`, and below the stage at the controller of
its partner. -/
def ReadsActualOn (L : Lvl I g) (N : Lvl I m) (ψ : Fin (L.catS C).card → Fin N.S.card) : Prop :=
  ∃ (u : Fin N.S.card) (θ : Label.{u} → Label.{u}) (ilo ihi : Fin C.card),
    N.S.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), m) ∧
    IsWitness (stepSuppressor m) θ ∧ (∀ x, θ x = ⊥ → x = ⊥) ∧
    (∀ d, I.amalgam.toCellScheme.grade d ≤ m →
      θ (N.S.rowAt u (N.embed d)) = I.amalgam.label d) ∧
    (C.equivFin.symm ilo).1 = Function.update (C.equivFin.symm ihi).1 (Sum.inr ())
      (cutoffCut (g + 1) (lowNAll I) (C.equivFin.symm ihi).1) ∧
    cutoffCut (g + 1) (lowNAll I) (C.equivFin.symm ihi).1 ∈ grid (g + 1) (bound I) ∧
    cutoffCut (g + 1) (lowNAll I) (C.equivFin.symm ihi).1 <
      (C.equivFin.symm ihi).1 (Sum.inr ()) ∧
    θ (N.S.rowAt u (ψ (Fin.natAdd L.S.card ihi))) = ⊤ ∧
    θ (N.S.rowAt u (ψ (Fin.natAdd L.S.card ilo))) < α

/-- **The reading from a level reading the actual state over a catalogue of states LOW over the
proper donor fields of every grade**: at a stage that is zero or a limit, a good level at the grade
`m ≥ 1` above the LOW layer (a grade prefix at `g + 1 ≤ m` keeping the old cells) that extends at
`⊥` and reads the actual state gives a legal display with faces the private context and the donor,
literally, with a LOW layer at `g + 1` whose separator is labelled by a proper label and `⊤`. -/
theorem ReadsActualOn.exists_isLowLayer_all (hα : Order.IsSuccPrelimit α) (hL : L.Good)
    (hC : ∀ P ∈ C, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧ 𝒜all P)
    {N : Lvl I m} (hN : N.Good) (hB : N.HasBotExtension) (hm : 1 ≤ m) (hgm : g + 1 ≤ m)
    {ψ : Fin (L.catS C).card → Fin N.S.card}
    (hψ : Scheme.IsGradePrefix (L.catS C) N.S ψ (g + 1))
    (hembed : ∀ d, N.embed d = ψ (Fin.castAdd _ (L.embed d)))
    (h : ReadsActualOn C L N ψ) :
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
    -- the label of the completion at an old cell is the reduced row of the decoded labels
    change Label.reduce α (r₁ (Fin.castAdd _ (N.embed d))) = _
    rw [hr₁q, decodedLabels_embed hN hold, (I.amalgam.atStage d).reduce_eq]
  have hP : Scheme.IsGradePrefix (L.catS C) (F.display hq hqα).toScheme
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
        (Fin.castAdd C.card (L.embed (faceCell h' i))) := by
    rw [CompletionBelowFullGrade.faceCell_display _ hf h h']
    -- the face cells of the completion are the images of the old cells
    change Fin.castSucc (Fin.castAdd _ (N.embed _)) = _
    rw [hembed]
    rfl
  have hgr (i : Fin C.card) : N.S.toCellScheme.grade (ψ (Fin.natAdd L.S.card i)) ≤ m := by
    rw [hψ.lowerEmb.grade_eq]
    exact (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le.trans hgm
  refine ⟨F.display hq hqα, _, _, _, _, _, _, _, F.isLegal_display hq hqα, fun h' ↦ ?_, ?_,
    isLowLayer_of_isGradePrefix_all hL hC hP (F.restrictFace_left_display hqe)
      (F.restrictFace_right_display hqe)
      (hface Coatom.univ_map_left_ne _ I.restrictFace_left)
      (hface Coatom.univ_map_right_ne _ I.restrictFace_right) hsep hmem hlt⟩
  · have h2 := (CompletionBelowFullGrade.display_label_castSucc F hq hqα _).symm.trans h'
    -- the label of the completion at the lower separator cell
    change Label.reduce α (r₁ (Fin.castAdd _ (ψ (Fin.natAdd L.S.card ilo)))) = ⊤ at h2
    rw [hr₁q, decodedLabels_of_le (hgr ilo), reduce_of_lt hlo] at h2
    exact ne_top_of_lt hlo h2
  · refine (CompletionBelowFullGrade.display_label_castSucc F hq hqα _).trans ?_
    -- the label of the completion at the upper separator cell
    change Label.reduce α (r₁ (Fin.castAdd _ (ψ (Fin.natAdd L.S.card ihi)))) = ⊤
    rw [hr₁q, decodedLabels_of_le (hgr ihi), hhi, reduce_top]

end Layer

/-! ### Rows of a state layer -/

/-- A cell of a state layer reads a cell of the level of grade at most its own through the section
of the level at its state. -/
theorem rowAt_sS_natAdd_castAdd {N : SLvl I g} {C : Finset (CProf I)} (i : Fin C.card)
    {e : Fin N.S.card} (he : N.S.toCellScheme.grade e ≤ g + 1) :
    (N.sS C).rowAt (Fin.natAdd N.S.card i) (Fin.castAdd C.card e) =
      N.σs (C.equivFin.symm i).1 e := by
  have hmem : Fin.castAdd C.card e ∈ (N.sS C).toCellScheme.below
      ((N.sS C).toCellScheme.gradedIndex (Fin.natAdd N.S.card i)) := by
    rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_natAdd,
      Scheme.appendFullCellsScheme_gradedIndex_castAdd]
    exact ⟨subset_univ _, he⟩
  rw [Scheme.rowAt_of_mem hmem, Scheme.appendFullCells_row_natAdd, SLvl.Φs_castAdd]

/-! ### Separated states -/

/-- **A separated state with its cutoff lowered is LOW** for the designations of its fields. -/
theorem lowPred_update_of_sepInv {K : ℕ} {N N' : Finset (Fin I.amalgam.card ⊕ Unit)}
    {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card}
    (hT : ∀ f ∈ T, ∃ d, f = Sum.inl d) {P : CProf I} (h : SepInv N' T o P) {c : Label.{u}}
    (hc : c ≤ P (Sum.inr ())) : lowPred K N T o r (Function.update P (Sum.inr ()) c) := by
  intro _ x hx
  obtain ⟨d, rfl⟩ := hT x hx
  rw [Function.update_self, Function.update_of_ne Sum.inl_ne_inr, h.2.2.1 _ hx]
  refine max_le hc ((min_le_left _ _).trans ?_)
  rw [Function.update_of_ne Sum.inl_ne_inr, h.2.1]

/-! ### The actual state -/

section Actual

variable {J : ℕ} {I : Seed.{u} α (g + J + 2)} {o r : Fin I.left.card}

variable (I) in
/-- The **actual state**: the glued labels with the cutoff `⊤`. -/
abbrev actState : CProf I := withCut (fun d ↦ I.amalgam.label d) ⊤

/-- **The actual state is separated.** -/
theorem sepInv_actState
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last (g + J + 2)) o r) :
    SepInv (lowNAll I) (lowT I) (StageType.faceCell I.restrictFace_left o) (actState I) := by
  classical
  refine ⟨top_ne_bot, (owner_copy hs).1, fun x hx ↦ ?_, fun f hf _ k ↦ ?_⟩
  · obtain ⟨t, ht, rfl⟩ := hx
    exact (StageType.label_faceCell _ t).trans ht
  · obtain ⟨t, ht, rfl⟩ := mem_image.mp hf
    change visibilityReplace k k (I.amalgam.label _) < visibilityReplace k k ⊤
    rw [StageType.label_faceCell, visibilityReplace_top, lt_top_iff_ne_top, Ne,
      visibilityReplace_eq_top_iff]
    exact (mem_filter.mp ht).2

end Actual

end VaughtConjecture.ProfileTower
