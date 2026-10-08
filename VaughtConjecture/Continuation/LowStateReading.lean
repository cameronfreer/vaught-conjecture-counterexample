/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateTower
import VaughtConjecture.Continuation.LowDisplayReads

/-!
# The state tower reads the actual state

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the display above the
controllers when the faces carry labels other than `⊥` above `K`); semantic contract, items 3, 4
and 8.

**LOW layers from any catalogue of LOW states** (`ProfileTower.isLowLayer_of_isGradePrefix_of`,
`ProfileTower.ReadsActualOn`, `ProfileTower.ReadsActualOn.exists_isLowLayer`, compiled in this
repository).  The LOW layer of a display (`ProfileTower.isLowLayer_of_isGradePrefix`) and the
reading from a level reading the actual state (`ProfileTower.ReadsActual.exists_isLowLayer`) use
of the LOW catalogue only that its states lie in the code grid and are LOW; they hold for every
such catalogue, in particular for the state catalogue of the LOW clause at `K`
(`ProfileTower.sCat`), whose states are not normalized.

**The state tower reads the actual state** (`ProfileTower.readsActualOn_sTower`, compiled in this
repository).  Let `I` be the seed of a LOW family at `K = g + 1 < m` (the private context a
source-gap context of grade `K` with the lost point last, the donor of top grade at most `K`), `L`
the level from the grade `0` at `g`, and `N` the forgetful level of the state tower of the LOW
clause at the grade `m`.  Given the lifts of the state tower (`ProfileTower.STowerLifts`), `N` is
a good level extending at `⊥` in which the layer of controllers is a grade prefix, and it reads the
actual state: the cell `u` of the state code at `m` of the **actual state** (the glued labels with
the cutoff `⊤`), its row read by the upper decoder of the actual state, reads every old cell of
grade at most `m` as its glued label, the controller of the bottom state code `s` as `⊤` (the first
chain bound, `ProfileTower.le_sTower_hi`, at the cutoff `⊤`), and the controller of the partner of
`s` at most at the cutoff cut of the glued labels, below the stage (the second chain bound,
`ProfileTower.sTower_lo_le`).  The actual state is separated (`ProfileTower.SepInv`), and so is
`s`: its cutoff cut lies in the grid and below its cutoff, and `s` and its partner are LOW states of
the catalogue at `K`.  No condition on the labels of the faces above `K` enters.

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

local notation "𝒜" => lowPred (g + 1) (lowN I (g + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

/-- **The LOW layer of a display in which a catalogue layer of LOW states over a good level is a
grade prefix at `g + 1`** (`ProfileTower.isLowLayer_of_isGradePrefix` for any catalogue of LOW
states in the code grid). -/
theorem isLowLayer_of_isGradePrefix_of (hL : L.Good)
    (hC : ∀ P ∈ C, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧ 𝒜 P)
    {ψ : Fin (L.catS C).card → Fin D.card}
    (hψ : Scheme.IsGradePrefix (L.catS C) D.toScheme ψ (g + 1))
    (h₁ : restrictFace Fin.castSuccEmb D = some I.left)
    (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some I.right)
    (hface₁ : ∀ i, faceCell h₁ i =
      ψ (Fin.castAdd C.card (L.embed (faceCell I.restrictFace_left i))))
    (hface₂ : ∀ i, faceCell h₂ i =
      ψ (Fin.castAdd C.card (L.embed (faceCell I.restrictFace_right i))))
    {ilo ihi : Fin C.card}
    (hsep : (C.equivFin.symm ilo).1 = Function.update (C.equivFin.symm ihi).1 (Sum.inr ())
      (cutoffCut (g + 1) (lowNAll I) (C.equivFin.symm ihi).1))
    (hmem : cutoffCut (g + 1) (lowNAll I) (C.equivFin.symm ihi).1 ∈ grid (g + 1) (bound I))
    (hlt : cutoffCut (g + 1) (lowNAll I) (C.equivFin.symm ihi).1 <
      (C.equivFin.symm ihi).1 (Sum.inr ())) :
    IsLowLayer (g + 1) h₁ h₂ o r (grid (g + 1) (bound I)) (lowEntry ψ)
      (lowFields ψ (C.equivFin.symm ihi).1) (ψ (Fin.natAdd L.S.card ilo))
      (ψ (Fin.natAdd L.S.card ihi)) := by
  classical
  have hinj := hψ.lowerEmb.injective
  have hctrl (i : Fin C.card) : D.toCellScheme.gradedIndex (ψ (Fin.natAdd L.S.card i)) =
      ((univ : Finset (Fin (m + 2))), g + 1) :=
    (hψ.gradedIndex_eq _).trans (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i)
  have hcut := cutoffCut_lowFields (C := C) hL hinj hface₂ (g + 1) (C.equivFin.symm ihi).1
  refine
    { bot_mem := bot_mem_grid _ _
      isLowAt := fun w hw ↦ ?_
      rowAt_old := fun w hw d hd hdK ↦ ?_
      rowAt_controller := fun w x hw hx ↦ ?_
      gradedIndex_lo := hctrl ilo
      gradedIndex_hi := hctrl ihi
      entry_hi := lowEntry_natAdd hinj ihi
      entry_lo := ?_
      cutoffCut_mem := by rw [hcut]; exact hmem
      cutoffCut_lt := by rw [hcut, lowFields_inr]; exact hlt }
  · obtain ⟨i, rfl⟩ := exists_ctrl_eq hψ hw
    rw [lowEntry_natAdd hinj]
    exact isLowAt_lowFields hL hinj hface₁ hface₂ (hC _ (C.equivFin.symm i).2).2
  · obtain ⟨i, rfl⟩ := exists_ctrl_eq hψ hw
    obtain ⟨e, rfl⟩ := exists_old_eq hψ hdK hd
    have he : L.S.toCellScheme.grade e ≤ g + 1 := by
      rwa [hψ.lowerEmb.grade_eq, Scheme.appendFullCellsScheme_grade_castAdd] at hdK
    rw [hψ.rowAt_eq, rowAt_catS_natAdd_castAdd i he, lowEntry_natAdd hinj, lowFields_castAdd hinj]
  · obtain ⟨i, rfl⟩ := exists_ctrl_eq hψ hw
    obtain ⟨i', rfl⟩ := exists_ctrl_eq hψ hx
    rw [hψ.rowAt_eq, rowAt_catS_natAdd_natAdd, lowEntry_natAdd hinj, lowEntry_natAdd hinj,
      agreementHeight_lowFields hL hinj (hC _ (C.equivFin.symm i).2).1]
  · rw [lowEntry_natAdd hinj, hsep]
    funext f
    rcases f with c | z
    · have hc : camal (Function.update (C.equivFin.symm ihi).1 (Sum.inr ())
          (cutoffCut (g + 1) (lowNAll I) (C.equivFin.symm ihi).1)) =
          camal (C.equivFin.symm ihi).1 :=
        funext fun d ↦ Function.update_of_ne (Sum.inl_ne_inr) _ _
      rw [partner_of_ne _ Sum.inl_ne_inr]
      simp only [lowFields, Sum.elim_inl, hc]
    · rw [partner, Function.update_self, hcut]
      simp only [lowFields, Sum.elim_inr, Function.update_self]

variable (C) in
/-- **A level reading the actual state, over a catalogue `C` of LOW states**: the statement of
`ProfileTower.ReadsActual` with the controllers indexed by `C`. -/
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

/-- **The reading from a level reading the actual state over a catalogue of LOW states**
(`ProfileTower.ReadsActual.exists_isLowLayer` for any catalogue of LOW states). -/
theorem ReadsActualOn.exists_isLowLayer (hα : Order.IsSuccPrelimit α) (hL : L.Good)
    (hC : ∀ P ∈ C, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧ 𝒜 P)
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
    change Fin.castSucc (Fin.castAdd _ (N.embed _)) = _
    rw [hembed]
    rfl
  have hgr (i : Fin C.card) : N.S.toCellScheme.grade (ψ (Fin.natAdd L.S.card i)) ≤ m := by
    rw [hψ.lowerEmb.grade_eq]
    exact (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le.trans hgm
  refine ⟨F.display hq hqα, _, _, _, _, _, _, _, F.isLegal_display hq hqα, fun h' ↦ ?_, ?_,
    isLowLayer_of_isGradePrefix_of hL hC hP (F.restrictFace_left_display hqe)
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

/-! ### Chains through the bottom state -/

/-- The old cells of the layers of the state tower are the old cells of `L`, through the layer of
controllers. -/
theorem sTower_embed {A : CProf I → Prop} :
    ∀ (J : ℕ) (d : Fin I.amalgam.card),
      (sTower L A (J + 1)).embed d = sEmb (L := L) (A := A) J (Fin.castAdd _ (L.embed d))
  | 0, _ => rfl
  | J + 1, d => congrArg (Fin.castAdd _) (sTower_embed J d)

/-- **The bottom state of a state with amalgam part lawful on the cut has amalgam part lawful on
the cut at `g + 1`.** -/
theorem isCutLawful_sBot : ∀ (J : ℕ) (P : CProf I), IsCutLawful I (g + J + 1) (camal P) →
    IsCutLawful I (g + 1) (camal (sBot g J P))
  | 0, _, h => h
  | J + 1, P, h => isCutLawful_sBot J _ (by
      obtain ⟨hC, hD⟩ := isCutLawful_camal_scode (k := g + J + 2) (P := P) h
      exact ⟨hC.mono (X := (_, g + J + 1)) ⟨subset_rfl, by omega⟩,
        hD.mono (X := (_, g + J + 1)) ⟨subset_rfl, by omega⟩⟩)

/-- **The bottom state of a separated state is separated.** -/
theorem sepInv_sBot {N : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
    {o : Fin I.amalgam.card}
    (hT : ∀ f ∈ T, ∃ d, f = Sum.inl d ∧ I.amalgam.toCellScheme.grade d ≤ g + 1)
    (ho : I.amalgam.toCellScheme.grade o ≤ g + 1) :
    ∀ (J : ℕ) (P : CProf I), SepInv N T o P → SepInv N T o (sBot g J P)
  | 0, _, h => h
  | J + 1, P, h => sepInv_sBot hT ho J _ (sepInv_scode hT ho (by omega) h)

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

/-- **The cutoff cut of a state code lies in the grid.** -/
theorem cutoffCut_scode_mem_grid (k : ℕ) (N : Finset (Fin I.amalgam.card ⊕ Unit)) (P : CProf I) :
    cutoffCut k N (scode k P) ∈ grid k (bound I) := by
  rcases N.eq_empty_or_nonempty with he | hne
  · rw [cutoffCut, donorMax, he, sup_empty, visibilityReplace_bot]; exact bot_mem_grid _ _
  obtain ⟨f, -, hfeq⟩ := exists_mem_eq_sup _ hne (scode k P)
  rw [cutoffCut, donorMax, hfeq]
  by_cases hf0 : hatS k P f = ⊥
  · change visibilityReplace k k (orbitMap k (hatS k P) (hatS k P f)) ∈ _
    rw [hf0, orbitMap_bot, visibilityReplace_bot]; exact bot_mem_grid _ _
  · change visibilityReplace k k (orbitMap k (hatS k P) (hatS k P f)) ∈ _
    rw [visibilityReplace_orbitMap hf0]
    refine gridPoint_mem_grid ((codeBlock_le _ _ _).trans ?_)
    have := keyRank_le_card k (hatS k P) (hatS k P f)
    rw [card_fields] at this
    simp only [bound]
    omega

/-! ### The state tower over the LOW clause reads the actual state -/

section Actual

variable {J : ℕ} {I : Seed.{u} α (g + J + 2)} {o r : Fin I.left.card}

local notation "𝒜" => lowPred (g + 1) (lowN I (g + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

local notation "𝒦" => sCat I (g + 1) (lowPred (g + 1) (lowN I (g + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r))

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

/-- **The state tower of the LOW clause over the levels from the grade `0` reads the actual
state**, given its lifts, for a LOW family at `K = g + 1 < m = g + J + 2`. -/
theorem readsActualOn_sTower (hα : Order.IsSuccPrelimit α)
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last (g + J + 2)) o r)
    (htb : I.right.topGrade ≤ g + 1)
    (hlift : STowerLifts (lvlZero I g) 𝒜 (J + 2)) :
    ∃ (D : StageType.{u} α (g + J + 2 + 2)) (h₁ : restrictFace Fin.castSuccEmb D = some I.left)
      (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some I.right)
      (G : Finset Label.{u}) (entry : Fin D.card → LowField D → Label.{u})
      (s : LowField D → Label.{u}) (lo hi : Fin D.card), D.IsLegal ∧ D.label lo ≠ ⊤ ∧
        D.label hi = ⊤ ∧ IsLowLayer (g + 1) h₁ h₂ o r G entry s lo hi := by
  classical
  set L := lvlZero I g with hLdef
  have hL : L.Good := lvlZero_good g (by omega)
  have hF := fieldsLE_low hs htb
  have hr : I.amalgam.toCellScheme.grade (StageType.faceCell I.restrictFace_left r) ≤ g + 1 :=
    (lost_copy hs).2
  have hAc : ∀ j, g + 1 ≤ j → ∀ P : CProf I, 𝒜 P → 𝒜 (scode j P) :=
    fun j hj P h ↦ lowPred_scode hF hr hj h
  have hA0 : ∀ W : Prof I, 𝒜 (withCut W ⊥) := fun W ↦ lowPred_withCut_bot W
  have hgood (J' : ℕ) (hJ' : J' ≤ J + 2) : (sTower L 𝒜 J').Good 𝒜 :=
    sTower_good hL hA0 hAc hlift J' hJ' (by omega)
  have hT' : ∀ f ∈ lowT I, ∃ d, f = Sum.inl d ∧ I.amalgam.toCellScheme.grade d ≤ g + 1 :=
    hF.2.1
  have hTi : ∀ f ∈ lowT I, ∃ d, f = Sum.inl d := fun f hf ↦ by
    obtain ⟨d, h, -⟩ := hT' f hf; exact ⟨d, h⟩
  -- the actual state, its code at the top, the bottom state
  set P := actState I with hP
  have hPlow : 𝒜 P := isLowAt_of_forall_top fun x hx ↦ by
    obtain ⟨t, ht, rfl⟩ := hx
    exact (StageType.label_faceCell _ t).trans ht
  set Q := scode (g + J + 2) P with hQ
  have hQs : SepInv (lowNAll I) (lowT I) (StageType.faceCell I.restrictFace_left o) Q :=
    sepInv_scode hT' hF.2.2 (by omega) (sepInv_actState hs)
  have hQc : IsCutLawful I (g + J + 2) (camal Q) := isCutLawful_camal_scode (isCutLawful_label _)
  have hQ𝒮 : Q ∈ sCat I (g + (J + 1) + 1) 𝒜 :=
    scode_mem_sCat (isCutLawful_label _) (hAc _ (by omega) P hPlow)
  obtain ⟨iu, hiu⟩ := exists_equivFin_eq hQ𝒮
  set S := sBot g J Q with hS
  set s := scode (g + 1) S with hsdef
  have hSs := sepInv_sBot hT' hF.2.2 J Q hQs
  have hss : SepInv (lowNAll I) (lowT I) (StageType.faceCell I.restrictFace_left o) s :=
    sepInv_scode hT' hF.2.2 le_rfl hSs
  have hSc : IsCutLawful I (g + 1) (camal S) := isCutLawful_sBot J Q (by
    obtain ⟨hC, hD⟩ := hQc
    exact ⟨hC.mono (X := (_, g + J + 1)) ⟨subset_rfl, by omega⟩,
      hD.mono (X := (_, g + J + 1)) ⟨subset_rfl, by omega⟩⟩)
  set c := cutoffCut (g + 1) (lowNAll I) s with hc
  have hclt : c < s (Sum.inr ()) := cutoffCut_lt_of_sepInv hss
  have hcmem : c ∈ grid (g + 1) (bound I) := cutoffCut_scode_mem_grid _ _ _
  have hsK : s ∈ 𝒦 := by
    refine mem_sCat.mpr ⟨scode_mem_codeGrid _ _, isCutLawful_camal_scode hSc, ?_⟩
    have := lowPred_update_of_sepInv (K := g + 1) (N := lowN I (g + 1))
      (r := StageType.faceCell I.restrictFace_left r) hTi hss le_rfl
    rwa [Function.update_eq_self] at this
  have hpK : Function.update s (Sum.inr ()) c ∈ 𝒦 := by
    refine mem_sCat.mpr ⟨fun f ↦ ?_, ?_, lowPred_update_of_sepInv hTi hss hclt.le⟩
    · rcases f with d | z
      · rw [Function.update_of_ne Sum.inl_ne_inr]; exact scode_mem_codeGrid _ _ _
      · rw [Function.update_self]; exact grid_subset_codeGrid _ _ hcmem
    · have hcam : camal (Function.update s (Sum.inr ()) c) = camal s :=
        funext fun _ ↦ Function.update_of_ne Sum.inl_ne_inr _ _
      rw [hcam]; exact isCutLawful_camal_scode hSc
  obtain ⟨ihi, hihi⟩ := exists_equivFin_eq hsK
  obtain ⟨ilo, hilo⟩ := exists_equivFin_eq hpK
  -- the top state level, its layer below, and the reading
  set N₁ := sTower L 𝒜 (J + 1) with hN₁
  have hN₁ : N₁.Good 𝒜 := hgood (J + 1) (by omega)
  have hN₂ : (sTower L 𝒜 (J + 2)).Good 𝒜 := hgood (J + 2) le_rfl
  set θ := upperDecoderAt (g + J + 2) (g + J + 2 + 1) (bound I) (hatS (g + J + 2) P) with hθ
  have hθw : IsWitness (stepSuppressor (g + J + 2)) θ := isWitness_upperDecoderAt (by omega)
  have hgrK (i : Fin (𝒦).card) :
      N₁.S.toCellScheme.grade (sEmb J (Fin.natAdd L.S.card i)) = g + 1 :=
    ((isGradePrefix_sEmb J).lowerEmb.grade_eq _).trans
      (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i)
  have hrow (i : Fin (𝒦).card) :
      (sTower L 𝒜 (J + 2)).S.rowAt (Fin.natAdd N₁.S.card iu)
        (sEmb (J + 1) (Fin.natAdd L.S.card i)) = N₁.σs Q (sEmb J (Fin.natAdd L.S.card i)) := by
    have h := rowAt_sS_natAdd_castAdd (N := N₁) (C := sCat I (g + (J + 1) + 1) 𝒜) iu
      (e := sEmb J (Fin.natAdd L.S.card i)) (by rw [hgrK]; omega)
    rw [hiu] at h
    exact h
  refine ReadsActualOn.exists_isLowLayer hα hL
    (fun R hR ↦ ⟨(mem_sCat.mp hR).1, (mem_sCat.mp hR).2.2⟩) (N := (sTower L 𝒜 (J + 2)).forget)
    (hN₂.forget hA0) (hN₁.hasBotExtension_next hA0) (by omega) (by omega)
    (ψ := sEmb (J + 1)) (isGradePrefix_sEmb (J + 1)) (fun d ↦ sTower_embed (J + 1) d)
    ⟨Fin.natAdd N₁.S.card iu, θ, ilo, ihi, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _,
      hθw, fun _ ↦ eq_bot_of_upperDecoderAt_eq_bot, fun d hd ↦ ?_, by rw [hilo, hihi],
      by rw [hihi]; exact hcmem, by rw [hihi]; exact hclt, ?_, ?_⟩
  · -- the old cells
    change θ ((N₁.sS (sCat I (g + (J + 1) + 1) 𝒜)).rowAt (Fin.natAdd N₁.S.card iu)
      (Fin.castAdd _ (N₁.embed d))) = _
    rw [rowAt_sS_natAdd_castAdd iu (by rw [hN₁.lowerEmb.grade_eq]; omega), hiu, hN₁.literal]
    change upperDecoderAt (g + J + 2) (g + J + 2 + 1) (bound I) (hatS (g + J + 2) P)
      (orbitCode (g + J + 2) (hatS (g + J + 2) P) (Sum.inl d)) = _
    rw [upperDecoderAt_orbitCode]
    exact hat_of_le hd
  · -- the controller of `s` is read as `⊤`
    change θ ((sTower L 𝒜 (J + 2)).S.rowAt (Fin.natAdd N₁.S.card iu)
      (sEmb (J + 1) (Fin.natAdd L.S.card ihi))) = ⊤
    rw [hrow]
    have h1 := le_sTower_hi (L := L) (A := 𝒜) J Q ihi hihi
    have h2 : θ (Q (Sum.inr ())) = ⊤ := upperDecoderAt_orbitCode _
    exact top_le_iff.mp (h2 ▸ hθw.monotone h1)
  · -- the controller of the partner is read below the stage
    change θ ((sTower L 𝒜 (J + 2)).S.rowAt (Fin.natAdd N₁.S.card iu)
      (sEmb (J + 1) (Fin.natAdd L.S.card ilo))) < α
    rw [hrow]
    have h1 := sTower_lo_le (L := L) (A := 𝒜) (lowNAll I) J Q ilo hilo hclt
    have h2 := upperDecoder_cutoff_le (K := g + 1) (k := g + J + 2) (by omega) (lowNAll I) P
    refine (hθw.monotone h1).trans_lt (h2.trans_lt ?_)
    change visibilityReplace (g + 1) (g + 1) (donorMax (lowNAll I) P) < α
    rw [visibilityReplace_lt_iff hα]
    refine Finset.sup_lt_iff (WithBot.bot_lt_coe _) |>.mpr fun f hf ↦ ?_
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hf
    change I.amalgam.label _ < α
    rw [StageType.label_faceCell]
    exact (I.right.atStage t).resolve_right (mem_filter.mp ht).2

end Actual

end VaughtConjecture.ProfileTower
