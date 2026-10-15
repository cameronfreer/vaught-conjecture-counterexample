/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.StronglyCodedLowDonor

/-!
# The strongly coded LOW display, and restricted (R2)

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3) and Layer 4 (the residual
comparison), in the strongly coded receiving class; Correspondence, item 1 (the strongly coded
legal stage types).

The three constructions of the LOW layer (`ProfileTower.exists_isLowLayer_pTower` for `K < k`,
`ProfileTower.LowReading.exists_isLowLayer` for the faces `⊥` above `K`, used at `K = k`, and
`ProfileTower.exists_isLowLayer_top` for `K = k + 1`) build their display as
`CompletionBelowFullGrade.display`, whose apex (`StageType.addApex`) has a row that is not strongly
coded in general.  Here each is repeated with the strongly coded display, and each operation that
creates rows is shown to keep strong coding.  The results are native constructions of this
repository; no correspondence with [AFK26] is claimed.

**The operations creating rows, and their strong coding** (each proved; inputs: the private
context `t'` and the donor `tb` strongly coded):

* the amalgam of the seed `Seed.ofCoatoms`: `Seed.isStronglyCoded_amalgam` (compiled before);
* the tower at the grade `0` and the next levels (`ProfileTower.lvlZero`):
  `ProfileTower.isStronglyCoded_lvlZero`, from `Seed.isStronglyCoded_tower` and
  `ProfileTower.Lvl.Good.isStronglyCoded_next`;
* the catalogue layers (`ProfileTower.Lvl.catS`, `ProfileTower.Lvl.catNext`):
  `ProfileTower.Lvl.Good.isStronglyCoded_catS`, `ProfileTower.Lvl.Good.isStronglyCoded_catNext`;
  the new rows are the section of the level and agreement heights in the grid, both in the code
  grid at the grade of the layer (`ProfileTower.Lvl.Good.Φcat_mem_codeGrid`);
* the canonical levels above a level (`ProfileTower.Lvl.iter`):
  `ProfileTower.Lvl.Good.isStronglyCoded_iter`;
* the state levels (`ProfileTower.SLvl.sS`): `ProfileTower.SLvl.Good.isStronglyCoded_sS`, from
  `ProfileTower.SLvl.Good.Φs_mem_codeGrid`, for a state catalogue in the code grid;
* the padded tower (`ProfileTower.pTower`): `ProfileTower.isStronglyCoded_pTower`, while its levels
  are good; its state catalogues lie in the code grid (`ProfileTower.mem_sCat`);
* the completions: the canonical field layer (`ProfileTower.Lvl.Good.isStronglyCoded_completion`,
  from `Scheme.isStronglyCoded_fieldLayer`); the completion at the full grade
  (`ProfileTower.Lvl.Good.completionSucc`) creates no row;
* the apex: `StageType.addStrongApex` (`StageType.isStronglyCoded_addStrongApex`) in place of
  `StageType.addApex`, in `CompletionBelowFullGrade.strongDisplay`
  (`CompletionBelowFullGrade.isStronglyCoded_strongDisplay`);
* the relabelling of the route (`StageType.isStronglyCoded_reindex`) and the bounded pinned
  extension (`StageType.exists_stronglyCoded_pinned_extension_topGrade_le`), in
  `VaughtConjecture.MainTheorem.StronglyCodedLowDonor`.

**The clauses of the display contract and the apex row.**  Each entry: the clause; whether the apex
row enters; its status for the strongly coded display.

* legality: consistency enters the apex row (its lawfulness); proved,
  `CompletionBelowFullGrade.isLegal_strongDisplay` (`StageType.isLegal_addStrongApex`, with
  `StageType.isLawful_strongApexRow`);
* the private and donor faces: the apex has full scope, so it is in no proper face; proved,
  `CompletionBelowFullGrade.restrictFace_left_strongDisplay`,
  `CompletionBelowFullGrade.restrictFace_right_strongDisplay`,
  `CompletionBelowFullGrade.faceCell_strongDisplay`;
* the labels of the old cells and the separator labels: the apex row does not enter; proved,
  `CompletionBelowFullGrade.strongDisplay_label_castSucc`;
* the LOW layer at `K` (rows of the controllers, of graded index `(univ, K)` with `K < m + 2`): the
  apex, of grade `m + 2`, is not a controller and not below one; the layer is read through the grade
  prefix below the full grade (`CompletionBelowFullGrade.isGradePrefix_strongDisplay`), by the
  general `ProfileTower.isLowLayer_of_isGradePrefix_all` and
  `ProfileTower.isLowLayer_of_isGradePrefix`; proved;
* recovery and determination (`StageType.IsLowDisplay`, used by
  `Realization.BoundedCoatomCutoffDetermination.of_hasLowDisplays`): obtained for any legal display
  from the controller reading (`StageType.IsSeparatedLowDisplay.of_controllerReading`,
  `StageType.exists_isLowDisplay_of_separated`); lawful sections enter only through the controllers
  of grade `K` (`StageType.exists_controller`), not through the apex row; proved,
  `StageType.HasStronglyCodedLowLayersOn.hasStronglyCodedLowDisplays`.

**Results.**  The three LOW-layer targets (`StageType.stronglyCodedPaddedLowLayersTarget`,
`StageType.stronglyCodedLowBotLowLayersTarget`, `StageType.stronglyCodedFullGradeLowLayersTarget`),
strongly coded LOW displays (`StageType.hasStronglyCodedLowDisplays`), the strongly coded LOW-donor
contract (`Realization.stronglyCodedLowDonorTarget`), and restricted (R2)
(`Realization.stronglyCodedResidualReceiving`).  Restricted (R2) is closed: both the construction
(here) and the acquisition of source-gap contexts in the class
(`Realization.stronglyCodedSourceGapAcquisitionTarget`) are proved.  It is restricted (R2): in the
strongly coded receiving class, for strongly coded cofaces; (R2) for models
(`Realization.ResidualReceiving`) is not addressed.  `ForcingDonorsIn` is not used.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u w

/-! ### Strong coding of the levels -/

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme StageType

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The levels from the grade `0` are strongly coded** when the amalgam is: the tower at the
grade `0` (`Seed.isStronglyCoded_tower`) and the next levels
(`ProfileTower.Lvl.Good.isStronglyCoded_next`). -/
theorem isStronglyCoded_lvlZero (h : I.amalgam.rows.IsStronglyCoded) :
    ∀ g, g ≤ m → (lvlZero I g).S.rows.IsStronglyCoded
  | 0, _ => I.isStronglyCoded_tower h 0
  | g + 1, hg => (lvlZero_good g (by omega)).isStronglyCoded_next
      (isStronglyCoded_lvlZero h g (by omega))

/-- **The canonical levels above a good strongly coded level are strongly coded**, up to the grade
`m` (`ProfileTower.Lvl.Good.isStronglyCoded_next`). -/
theorem Lvl.Good.isStronglyCoded_iter {g' : ℕ} {N : Lvl I g'} (hN : N.Good)
    (h : N.S.rows.IsStronglyCoded) : ∀ j, g' + j ≤ m → (N.iter j).S.rows.IsStronglyCoded
  | 0, _ => h
  | j + 1, hj => (hN.iter j (by omega)).isStronglyCoded_next
      (Lvl.Good.isStronglyCoded_iter hN h j (by omega))

/-- **The catalogue layer over a good strongly coded level is strongly coded**, for a catalogue in
the code grid at its grade: the new rows are the section of the level and the agreement heights in
the grid, in the code grid (`ProfileTower.Lvl.Good.Φcat_mem_codeGrid`). -/
theorem Lvl.Good.isStronglyCoded_catS {g : ℕ} {L : Lvl I g} (hL : L.Good)
    (h : L.S.rows.IsStronglyCoded) {C : Finset (CProf I)}
    (hC : ∀ R ∈ C, ∀ f, R f ∈ codeGrid (g + 1) (bound I)) : (L.catS C).rows.IsStronglyCoded :=
  Scheme.isStronglyCoded_appendFullCells h fun i d ↦
    isStronglyCoded_of_mem_codeGrid (hL.Φcat_mem_codeGrid (hC _ (C.equivFin.symm i).2) d)

/-- **The catalogue layer as a level is strongly coded** over a good strongly coded level: its
catalogue lies in the code grid (`ProfileTower.mem_predCat`). -/
theorem Lvl.Good.isStronglyCoded_catNext {g : ℕ} {L : Lvl I g} (hL : L.Good)
    (h : L.S.rows.IsStronglyCoded) (A : CProf I → Prop) : (L.catNext A).S.rows.IsStronglyCoded :=
  hL.isStronglyCoded_catS h fun _ hR ↦ (mem_predCat.mp hR).1

/-- **The next state level over a good strongly coded state level is strongly coded**, for a
catalogue of states in the code grid at its grade: the new rows are the section of the level and
the agreement heights in the grid (`ProfileTower.SLvl.Good.Φs_mem_codeGrid`). -/
theorem SLvl.Good.isStronglyCoded_sS {g : ℕ} {N : SLvl I g} {A : CProf I → Prop}
    (hN : N.Good A) (h : N.S.rows.IsStronglyCoded) {C : Finset (CProf I)}
    (hC : ∀ R ∈ C, ∀ f, R f ∈ codeGrid (g + 1) (bound I)) : (N.sS C).rows.IsStronglyCoded :=
  Scheme.isStronglyCoded_appendFullCells h fun i d ↦
    isStronglyCoded_of_mem_codeGrid (hN.Φs_mem_codeGrid (hC _ (C.equivFin.symm i).2) d)

/-- **The padded tower over a strongly coded level is strongly coded** while its levels are good:
each padded level has the scheme of the next state level on a state catalogue in the code grid
(`ProfileTower.mem_sCat`). -/
theorem isStronglyCoded_pTower {g : ℕ} {L : Lvl I g} {A : CProf I → Prop}
    (h : L.S.rows.IsStronglyCoded) :
    ∀ J, (∀ J' < J, (pTower L A J').Good A) → (pTower L A J).S.rows.IsStronglyCoded
  | 0, _ => h
  | J + 1, hg => SLvl.Good.isStronglyCoded_sS (hg J (by omega))
      (isStronglyCoded_pTower h J fun J' hJ' ↦ hg J' (by omega)) fun _ hR ↦ (mem_sCat.mp hR).1

/-- **The completion over a good strongly coded level at the grade `m` is strongly coded**: its
scheme is the canonical field layer (`Scheme.isStronglyCoded_fieldLayer`). -/
theorem Lvl.Good.isStronglyCoded_completion {N : Lvl I m} (hN : N.Good) (hB : N.HasBotExtension)
    (hm : 1 ≤ m) (h : N.S.rows.IsStronglyCoded) :
    (hN.completion hB hm).scheme.rows.IsStronglyCoded :=
  Scheme.isStronglyCoded_fieldLayer (hS := N.not_le) h

end VaughtConjecture.ProfileTower

/-! ### The display with the strongly coded apex -/

namespace VaughtConjecture.CompletionBelowFullGrade

open Finset Label StageType

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)
  {q : Fin F.scheme.card → Label.{u}} (hq : F.scheme.rows.IsLawful q) (hqα : ∀ d, AtStage α (q d))

/-- **The strongly coded display of a completion below the full grade** over a lawful labelling
`q` at the stage: the completed scheme labelled by `q`, with the strongly coded apex
(`StageType.addStrongApex`) in place of the apex of `CompletionBelowFullGrade.display`. -/
noncomputable def strongDisplay : StageType.{u} α (m + 2) :=
  (F.withLabel hq hqα).addStrongApex F.isLegalBelowFullGrade (Nat.succ_pos _)

/-- **The strongly coded display is legal** (`StageType.isLegal_addStrongApex`). -/
theorem isLegal_strongDisplay : (F.strongDisplay hq hqα).IsLegal :=
  StageType.isLegal_addStrongApex _ _

/-- **The strongly coded display is strongly coded** when the completed scheme is
(`StageType.isStronglyCoded_addStrongApex`). -/
theorem isStronglyCoded_strongDisplay (h : F.scheme.rows.IsStronglyCoded) :
    (F.strongDisplay hq hqα).rows.IsStronglyCoded :=
  StageType.isStronglyCoded_addStrongApex _ _ h

/-- The labels of the strongly coded display are `q` on the completed scheme. -/
theorem strongDisplay_label_castSucc (d : Fin F.scheme.card) :
    (F.strongDisplay hq hqα).label (Fin.castSucc d) = q d :=
  apexLabel_castSucc (t := F.withLabel hq hqα) d

/-- **The completed scheme is a grade prefix of the strongly coded display** at every grade below
`m + 2`. -/
theorem isGradePrefix_strongDisplay {K : ℕ} (hK : K < m + 2) :
    Scheme.IsGradePrefix F.scheme (F.strongDisplay hq hqα).toScheme Fin.castSucc K :=
  Scheme.IsGradePrefix.castSucc (h := F.isLegalBelowFullGrade.not_le) hK

variable {hq hqα}

/-- **The faces of the strongly coded display along a proper face are those of the amalgam**, when
`q` extends the glued labels (`StageType.restrictFace_addStrongApex`). -/
theorem restrictFace_strongDisplay (hqe : ∀ d, q (F.embed d) = I.amalgam.label d) {k : ℕ}
    (f : Fin k ↪ Fin (m + 2)) (hf : univ.map f ≠ univ) :
    restrictFace f (F.strongDisplay hq hqα) = restrictFace f I.amalgam :=
  (StageType.restrictFace_addStrongApex _ _ _ hf).trans
    (F.restrictFace_withLabel hq hqα hqe f hf)

/-- **The private face of the strongly coded display is the first coatom type**, literally. -/
theorem restrictFace_left_strongDisplay (hqe : ∀ d, q (F.embed d) = I.amalgam.label d) :
    restrictFace Fin.castSuccEmb (F.strongDisplay hq hqα) = some I.left :=
  (F.restrictFace_strongDisplay hqe _ Coatom.univ_map_left_ne).trans I.restrictFace_left

/-- **The donor face of the strongly coded display is the second coatom type**, literally. -/
theorem restrictFace_right_strongDisplay (hqe : ∀ d, q (F.embed d) = I.amalgam.label d) :
    restrictFace (extendByLast Fin.castSuccEmb) (F.strongDisplay hq hqα) = some I.right :=
  (F.restrictFace_strongDisplay hqe _ Coatom.univ_map_right_ne).trans I.restrictFace_right

/-- **The cells of a proper face of the strongly coded display are the old cells** of the amalgam
at the same positions. -/
theorem faceCell_strongDisplay {k : ℕ} {f : Fin k ↪ Fin (m + 2)} (hf : univ.map f ≠ univ)
    {t : StageType.{u} α k} (h : restrictFace f (F.strongDisplay hq hqα) = some t)
    (h' : restrictFace f I.amalgam = some t) (i : Fin t.card) :
    faceCell h i = Fin.castSucc (F.embed (faceCell h' i)) := by
  have hmono : StrictMono (Fin.castSucc ∘ F.embed) :=
    Fin.strictMono_castSucc.comp F.embed.strictMono
  have hscope (d : Fin I.amalgam.card) : (F.strongDisplay hq hqα).toCellScheme.scope
      ((Fin.castSucc ∘ F.embed) d) = I.amalgam.toCellScheme.scope d :=
    (Scheme.appendFullCellScheme_scope_castSucc _ _ _).trans (F.scope_embed d)
  have hvis (z : Fin (F.strongDisplay hq hqα).card)
      (hz : ((F.strongDisplay hq hqα).toCellScheme.scope z : Set (Fin (m + 2))) ⊆ Set.range f) :
      z ∈ Set.range (Fin.castSucc ∘ F.embed) := by
    have hne : (F.strongDisplay hq hqα).toCellScheme.scope z ≠ univ := fun he ↦ hf
      (eq_univ_of_forall fun x ↦ by
        obtain ⟨y, rfl⟩ : x ∈ Set.range f := hz (mem_coe.mpr (he.symm ▸ mem_univ x))
        exact mem_map_of_mem _ (mem_univ y))
    induction z using Fin.lastCases with
    | last => exact absurd (Scheme.appendFullCellScheme_scope_last _ _) hne
    | cast z =>
      rw [show (F.strongDisplay hq hqα).toCellScheme.scope (Fin.castSucc z) =
        F.scheme.toCellScheme.scope z from Scheme.appendFullCellScheme_scope_castSucc _ _ _]
        at hne
      obtain ⟨d, rfl⟩ := F.mem_range_embed z hne
      exact ⟨d, rfl⟩
  exact Scheme.cellMap_eq_of_strictMono_of_mem_range (S := I.amalgam.toScheme)
    (T := (F.strongDisplay hq hqα).toScheme) (φ := Fin.castSucc ∘ F.embed) f hmono hscope hvis rfl

end VaughtConjecture.CompletionBelowFullGrade

/-! ### LOW layers on strongly coded displays -/

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme StageType

variable {α : Ordinal.{u}} {m g : ℕ} {I : Seed.{u} α m} {L : Lvl I g}

section Layer

variable {o r : Fin I.left.card} {C : Finset (CProf I)}

local notation "𝒜all" => lowPred (g + 1) (lowNAll I) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

/-- **The strongly coded reading from a level reading the actual state**: the argument of
`ProfileTower.ReadsActualOn.exists_isLowLayer_all` with the strongly coded display
(`CompletionBelowFullGrade.strongDisplay`) in place of `CompletionBelowFullGrade.display`; over a
strongly coded level the display is strongly coded. -/
theorem ReadsActualOn.exists_isStronglyCodedLowLayer_all (hα : Order.IsSuccPrelimit α) (hL : L.Good)
    (hC : ∀ P ∈ C, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧ 𝒜all P)
    {N : Lvl I m} (hN : N.Good) (hB : N.HasBotExtension) (hm : 1 ≤ m) (hgm : g + 1 ≤ m)
    {ψ : Fin (L.catS C).card → Fin N.S.card}
    (hψ : Scheme.IsGradePrefix (L.catS C) N.S ψ (g + 1))
    (hembed : ∀ d, N.embed d = ψ (Fin.castAdd _ (L.embed d)))
    (hNs : N.S.rows.IsStronglyCoded) (h : ReadsActualOn C L N ψ) :
    ∃ (D : StageType.{u} α (m + 2)) (h₁ : restrictFace Fin.castSuccEmb D = some I.left)
      (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some I.right)
      (G : Finset Label.{u}) (entry : Fin D.card → LowField D → Label.{u})
      (s : LowField D → Label.{u}) (lo hi : Fin D.card), D.IsLegal ∧ D.rows.IsStronglyCoded ∧
        D.label lo ≠ ⊤ ∧
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
  have hP : Scheme.IsGradePrefix (L.catS C) (F.strongDisplay hq hqα).toScheme
      (Fin.castSucc ∘ Fin.castAdd _ ∘ ψ) (g + 1) :=
    ((F.isGradePrefix_strongDisplay hq hqα (by omega)).comp
      (Scheme.IsGradePrefix.castAdd (S := N.S) (k := m + 1)
        (M := (N.S.catalogue (m + 1)).card)
        (r := fun i ↦ N.S.fieldRow (m + 1) (N.S.catalogueEntry (m + 1) i))
        (h := N.not_le) (by omega))).comp hψ
  have hface {k : ℕ} {f : Fin k ↪ Fin (m + 2)} (hf : univ.map f ≠ univ)
      {t : StageType.{u} α k} (h : restrictFace f (F.strongDisplay hq hqα) = some t)
      (h' : restrictFace f I.amalgam = some t) (i : Fin t.card) :
      faceCell h i = (Fin.castSucc ∘ Fin.castAdd _ ∘ ψ)
        (Fin.castAdd C.card (L.embed (faceCell h' i))) := by
    rw [CompletionBelowFullGrade.faceCell_strongDisplay _ hf h h']
    -- the face cells of the completion are the images of the old cells
    change Fin.castSucc (Fin.castAdd _ (N.embed _)) = _
    rw [hembed]
    rfl
  have hgr (i : Fin C.card) : N.S.toCellScheme.grade (ψ (Fin.natAdd L.S.card i)) ≤ m := by
    rw [hψ.lowerEmb.grade_eq]
    exact (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le.trans hgm
  refine ⟨F.strongDisplay hq hqα, _, _, _, _, _, _, _, F.isLegal_strongDisplay hq hqα,
    F.isStronglyCoded_strongDisplay hq hqα (hN.isStronglyCoded_completion hB hm hNs),
    fun h' ↦ ?_, ?_,
    isLowLayer_of_isGradePrefix_all hL hC hP (F.restrictFace_left_strongDisplay hqe)
      (F.restrictFace_right_strongDisplay hqe)
      (hface Coatom.univ_map_left_ne _ I.restrictFace_left)
      (hface Coatom.univ_map_right_ne _ I.restrictFace_right) hsep hmem hlt⟩
  · have h2 := (CompletionBelowFullGrade.strongDisplay_label_castSucc F hq hqα _).symm.trans h'
    -- the label of the completion at the lower separator cell
    change Label.reduce α (r₁ (Fin.castAdd _ (ψ (Fin.natAdd L.S.card ilo)))) = ⊤ at h2
    rw [hr₁q, decodedLabels_of_le (hgr ilo), reduce_of_lt hlo] at h2
    exact ne_top_of_lt hlo h2
  · refine (CompletionBelowFullGrade.strongDisplay_label_castSucc F hq hqα _).trans ?_
    -- the label of the completion at the upper separator cell
    change Label.reduce α (r₁ (Fin.castAdd _ (ψ (Fin.natAdd L.S.card ihi)))) = ⊤
    rw [hr₁q, decodedLabels_of_le (hgr ihi), hhi, reduce_top]

end Layer

section Actual

variable {J : ℕ} {I : Seed.{u} α (g + J + 2)} {o r : Fin I.left.card}

local notation "𝒜all" => lowPred (g + 1) (lowNAll I) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

local notation "𝒦" => sCat I (g + 1) (lowPred (g + 1) (lowNAll I) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r))

/-- **The padded tower gives a strongly coded LOW display** at `K = g + 1 < m = g + J + 2`, when
the amalgam of the seed is strongly coded: the argument of `ProfileTower.exists_isLowLayer_pTower`
through `ProfileTower.ReadsActualOn.exists_isStronglyCodedLowLayer_all`; the padded tower is
strongly coded (`ProfileTower.isStronglyCoded_pTower`). -/
theorem exists_isStronglyCodedLowLayer_pTower (hα : Order.IsSuccPrelimit α)
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last (g + J + 2)) o r)
    (htb : I.right.topGrade ≤ g + 1) (hIs : I.amalgam.rows.IsStronglyCoded) :
    ∃ (D : StageType.{u} α (g + J + 2 + 2)) (h₁ : restrictFace Fin.castSuccEmb D = some I.left)
      (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some I.right)
      (G : Finset Label.{u}) (entry : Fin D.card → LowField D → Label.{u})
      (s : LowField D → Label.{u}) (lo hi : Fin D.card), D.IsLegal ∧ D.rows.IsStronglyCoded ∧
        D.label lo ≠ ⊤ ∧
        D.label hi = ⊤ ∧ IsLowLayer (g + 1) h₁ h₂ o r G entry s lo hi := by
  classical
  set L := lvlZero I g with hLdef
  have hL : L.Good := lvlZero_good g (by omega)
  have hF := fieldsLE_low hs htb
  have hA0 : ∀ W : Prof I, 𝒜all (withCut W ⊥) := fun W ↦ lowPred_withCut_bot W
  have hAo : ∀ j, g + 1 ≤ j → ∀ P : CProf I, 𝒜all P → 𝒜all (orbitCode j P) :=
    fun j hj P h ↦ lowPred_orbitCode hj h
  have hlift := pTowerLifts_lowAll hs htb
  have hgood (J' : ℕ) (hJ' : J' ≤ J + 2) : (pTower L 𝒜all J').Good 𝒜all :=
    pTower_good hL hA0 hAo hlift J' hJ' (by omega)
  have hT' : ∀ f ∈ lowT I, ∃ d, f = Sum.inl d ∧ I.amalgam.toCellScheme.grade d ≤ g + 1 :=
    hF.2.1
  have hTi : ∀ f ∈ lowT I, ∃ d, f = Sum.inl d := fun f hf ↦ by
    obtain ⟨d, h, -⟩ := hT' f hf; exact ⟨d, h⟩
  -- the actual state, its code at the top, the padded bottom state
  set P := actState I with hP
  have hPlow : 𝒜all P := isLowAt_of_forall_top fun x hx ↦ by
    obtain ⟨t, ht, rfl⟩ := hx
    exact (StageType.label_faceCell _ t).trans ht
  set Q := orbitCode (g + J + 2) P with hQ
  have hQs : SepInv (lowNAll I) (lowT I) (StageType.faceCell I.restrictFace_left o) Q :=
    sepInv_orbitCode (sepInv_actState hs)
  have hQc : IsCutLawful I (g + J + 2) (camal Q) :=
    ⟨(isCutLawful_label (I := I) (g + J + 2)).1.map_of_apply_eq_bot (fun d ↦ d.2.2)
        (isWitness_orbitMap (g + J + 2) P) fun _ ↦ orbitMap_eq_bot_iff.mp,
      (isCutLawful_label (I := I) (g + J + 2)).2.map_of_apply_eq_bot (fun d ↦ d.2.2)
        (isWitness_orbitMap (g + J + 2) P) fun _ ↦ orbitMap_eq_bot_iff.mp⟩
  have hQ𝒮 : Q ∈ sCat I (g + (J + 1) + 1) 𝒜all :=
    orbitCode_mem_sCat (g := g + (J + 1)) (isCutLawful_label _) (hAo _ (by omega) P hPlow)
  obtain ⟨iu, hiu⟩ := exists_equivFin_eq hQ𝒮
  set S := pBot g J Q with hS
  set s := orbitCode (g + 1) S with hsdef
  have hSs := sepInv_pBot (g := g) J Q hQs
  have hss : SepInv (lowNAll I) (lowT I) (StageType.faceCell I.restrictFace_left o) s :=
    sepInv_orbitCode hSs
  have hSc : IsCutLawful I (g + 1) (camal S) := isCutLawful_pBot J Q (by
    obtain ⟨hC, hD⟩ := hQc
    exact ⟨hC.mono (X := (_, g + J + 1)) ⟨subset_rfl, by omega⟩,
      hD.mono (X := (_, g + J + 1)) ⟨subset_rfl, by omega⟩⟩)
  have hsc : IsCutLawful I (g + 1) (camal s) :=
    ⟨hSc.1.map_of_apply_eq_bot (fun d ↦ d.2.2) (isWitness_orbitMap (g + 1) S)
        fun _ ↦ orbitMap_eq_bot_iff.mp,
      hSc.2.map_of_apply_eq_bot (fun d ↦ d.2.2) (isWitness_orbitMap (g + 1) S)
        fun _ ↦ orbitMap_eq_bot_iff.mp⟩
  set c := cutoffCut (g + 1) (lowNAll I) s with hc
  have hclt : c < s (Sum.inr ()) := cutoffCut_lt_of_sepInv hss
  have hcmem : c ∈ grid (g + 1) (bound I) := cutoffCut_orbitCode_mem_grid _ _ _
  have hsK : s ∈ 𝒦 := by
    refine mem_sCat.mpr ⟨orbitCode_mem_codeGrid _ _, hsc, orbitCode_orbitCode, ?_⟩
    have := lowPred_update_of_sepInv (K := g + 1) (N := lowNAll I)
      (r := StageType.faceCell I.restrictFace_left r) hTi hss le_rfl
    rwa [Function.update_eq_self] at this
  have hpK : Function.update s (Sum.inr ()) c ∈ 𝒦 := by
    refine mem_sCat.mpr ⟨fun f ↦ ?_, ?_,
      orbitCode_update_cutoffCut inr_notMem_lowNAll orbitCode_orbitCode hss.2.1,
      lowPred_update_of_sepInv hTi hss hclt.le⟩
    · rcases f with d | z
      · rw [Function.update_of_ne Sum.inl_ne_inr]; exact orbitCode_mem_codeGrid _ _ _
      · rw [Function.update_self]; exact grid_subset_codeGrid _ _ hcmem
    · have hcam : camal (Function.update s (Sum.inr ()) c) = camal s :=
        funext fun _ ↦ Function.update_of_ne Sum.inl_ne_inr _ _
      rw [hcam]; exact hsc
  obtain ⟨ihi, hihi⟩ := exists_equivFin_eq hsK
  obtain ⟨ilo, hilo⟩ := exists_equivFin_eq hpK
  -- the top state level, its layer below, and the reading
  set N₁ := pTower L 𝒜all (J + 1) with hN₁
  have hN₁ : N₁.Good 𝒜all := hgood (J + 1) (by omega)
  have hN₂ : (pTower L 𝒜all (J + 2)).Good 𝒜all := hgood (J + 2) le_rfl
  set θ := upperDecoderAt (g + J + 2) (g + J + 2 + 1) (bound I) P with hθ
  have hθw : IsWitness (stepSuppressor (g + J + 2)) θ := isWitness_upperDecoderAt (by omega)
  have hgrK (i : Fin (𝒦).card) :
      N₁.S.toCellScheme.grade (pEmb J (Fin.natAdd L.S.card i)) = g + 1 :=
    ((isGradePrefix_pEmb J).lowerEmb.grade_eq _).trans
      (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i)
  have hrow (i : Fin (𝒦).card) :
      (pTower L 𝒜all (J + 2)).S.rowAt (Fin.natAdd N₁.S.card iu)
        (pEmb (J + 1) (Fin.natAdd L.S.card i)) = N₁.σs Q (pEmb J (Fin.natAdd L.S.card i)) := by
    have h := rowAt_sS_natAdd_castAdd (N := N₁) (C := sCat I (g + (J + 1) + 1) 𝒜all) iu
      (e := pEmb J (Fin.natAdd L.S.card i)) (by rw [hgrK]; omega)
    rw [hiu] at h
    exact h
  have hNs : (pTower L 𝒜all (J + 2)).forget.S.rows.IsStronglyCoded :=
    isStronglyCoded_pTower (isStronglyCoded_lvlZero hIs g (by omega)) (J + 2)
      fun J' hJ' ↦ hgood J' hJ'.le
  refine ReadsActualOn.exists_isStronglyCodedLowLayer_all hα hL
    (fun R hR ↦ ⟨(mem_sCat.mp hR).1, (mem_sCat.mp hR).2.2.2⟩)
    (N := (pTower L 𝒜all (J + 2)).forget)
    (hN₂.forget hA0) (hN₁.hasBotExtension_pnext hA0) (by omega) (by omega)
    (ψ := pEmb (J + 1)) (isGradePrefix_pEmb (J + 1)) (fun d ↦ pTower_embed (J + 1) d) hNs
    ⟨Fin.natAdd N₁.S.card iu, θ, ilo, ihi, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _,
      hθw, fun _ ↦ eq_bot_of_upperDecoderAt_eq_bot, fun d hd ↦ ?_, by rw [hilo, hihi],
      by rw [hihi]; exact hcmem, by rw [hihi]; exact hclt, ?_, ?_⟩
  · -- the old cells
    -- the row of the cell of the actual code at an old cell, through the scheme of the layer
    change θ ((N₁.sS (sCat I (g + (J + 1) + 1) 𝒜all)).rowAt (Fin.natAdd N₁.S.card iu)
      (Fin.castAdd _ (N₁.embed d))) = _
    rw [rowAt_sS_natAdd_castAdd iu (by rw [hN₁.lowerEmb.grade_eq]; omega), hiu, hN₁.literal]
    exact upperDecoderAt_orbitCode _
  · -- the controller of `s` is read as `⊤`
    -- the row of the cell of the actual code at the controller of `s`
    change θ ((pTower L 𝒜all (J + 2)).S.rowAt (Fin.natAdd N₁.S.card iu)
      (pEmb (J + 1) (Fin.natAdd L.S.card ihi))) = ⊤
    rw [hrow]
    have h1 := le_pTower_hi (L := L) (A := 𝒜all) J Q ihi hihi
    have h2 : θ (Q (Sum.inr ())) = ⊤ := upperDecoderAt_orbitCode _
    exact top_le_iff.mp (h2 ▸ hθw.monotone h1)
  · -- the controller of the partner is read below the stage
    -- the row of the cell of the actual code at the controller of the partner of `s`
    change θ ((pTower L 𝒜all (J + 2)).S.rowAt (Fin.natAdd N₁.S.card iu)
      (pEmb (J + 1) (Fin.natAdd L.S.card ilo))) < α
    rw [hrow]
    have h1 := pTower_lo_le (L := L) (A := 𝒜all) (lowNAll I) J Q ilo hilo hclt
    have h2 := upperDecoder_cutoff_orbitCode (K := g + 1) (k := g + J + 2) (by omega)
      (lowNAll I) P
    refine (hθw.monotone h1).trans_lt (h2.trans_lt ?_)
    rw [visibilityReplace_lt_iff hα]
    refine Finset.sup_lt_iff (WithBot.bot_lt_coe _) |>.mpr fun f hf ↦ ?_
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hf
    -- a proper donor field reads the glued label of a donor cell
    change I.amalgam.label _ < α
    rw [StageType.label_faceCell]
    exact (I.right.atStage t).resolve_right (mem_filter.mp ht).2

end Actual

end VaughtConjecture.ProfileTower

/-! ### The LOW layer with the faces `⊥` above `K`, and at the full grade -/

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme StageType

variable {α : Ordinal.{u}}

section Reading

variable {g j : ℕ} {I : Seed.{u} α (g + 1 + j)} {o r : Fin I.left.card}

local notation "𝒜" => lowPred (g + 1) (lowN I (g + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

local notation "𝒞" => lowCat I (g + 1) (lowN I (g + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

/-- **The reading gives a strongly coded display with a LOW layer**: the argument of
`ProfileTower.LowReading.exists_isLowLayer` (through `ProfileTower.isLowLayer_of_isGradePrefix`)
with the strongly coded display; over a strongly coded level `L` the completion over the catalogue
layer is strongly coded (`ProfileTower.Lvl.Good.isStronglyCoded_catNext`,
`ProfileTower.Lvl.Good.isStronglyCoded_iter`, `Scheme.isStronglyCoded_fieldLayer`). -/
theorem LowReading.exists_isStronglyCodedLowLayer {L : Lvl I g} {hL : L.Good}
    {hN : (L.catNext 𝒜).Good} (h : LowReading o r L hL hN) (hLs : L.S.rows.IsStronglyCoded) :
    ∃ (D : StageType.{u} α (g + 1 + j + 2)) (h₁ : restrictFace Fin.castSuccEmb D = some I.left)
      (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some I.right)
      (G : Finset Label.{u}) (entry : Fin D.card → LowField D → Label.{u})
      (s : LowField D → Label.{u}) (lo hi : Fin D.card), D.IsLegal ∧ D.rows.IsStronglyCoded ∧
        D.label lo ≠ ⊤ ∧ D.label hi = ⊤ ∧ IsLowLayer (g + 1) h₁ h₂ o r G entry s lo hi := by
  obtain ⟨q, hq, hqα, hqe, ilo, ihi, hsep, hmem, hlt, hlo, hhi⟩ := h
  have hFs : (lowCompletion hL hN lowPred_withCut_bot).scheme.rows.IsStronglyCoded :=
    Scheme.isStronglyCoded_fieldLayer (hS := ((L.catNext 𝒜).iter j).not_le)
      (hN.isStronglyCoded_iter (hL.isStronglyCoded_catNext hLs 𝒜) j le_rfl)
  have hP : Scheme.IsGradePrefix (L.catS 𝒞)
      ((lowCompletion hL hN lowPred_withCut_bot).strongDisplay hq hqα).toScheme
      (Fin.castSucc ∘ lowCellMap j 𝒜 L) (g + 1) :=
    ((lowCompletion hL hN lowPred_withCut_bot).isGradePrefix_strongDisplay hq hqα
      (by omega)).comp (isGradePrefix_lowCompletion hL hN lowPred_withCut_bot)
  have h₁ := (lowCompletion hL hN lowPred_withCut_bot).restrictFace_left_strongDisplay
    (hq := hq) (hqα := hqα) hqe
  have h₂ := (lowCompletion hL hN lowPred_withCut_bot).restrictFace_right_strongDisplay
    (hq := hq) (hqα := hqα) hqe
  refine ⟨_, h₁, h₂, _, _, _, _, _,
    (lowCompletion hL hN lowPred_withCut_bot).isLegal_strongDisplay hq hqα,
    (lowCompletion hL hN lowPred_withCut_bot).isStronglyCoded_strongDisplay hq hqα hFs, ?_, ?_,
    isLowLayer_of_isGradePrefix hL hP h₁ h₂ (fun i ↦ ?_) (fun i ↦ ?_) hsep hmem hlt⟩
  · exact fun h' ↦ hlo ((CompletionBelowFullGrade.strongDisplay_label_castSucc
      (lowCompletion hL hN lowPred_withCut_bot) hq hqα _).symm.trans h')
  · exact (CompletionBelowFullGrade.strongDisplay_label_castSucc
      (lowCompletion hL hN lowPred_withCut_bot) hq hqα _).trans hhi
  · rw [CompletionBelowFullGrade.faceCell_strongDisplay _ Coatom.univ_map_left_ne _
      I.restrictFace_left, lowCompletion_embed]
    rfl
  · rw [CompletionBelowFullGrade.faceCell_strongDisplay _ Coatom.univ_map_right_ne _
      I.restrictFace_right, lowCompletion_embed]
    rfl

end Reading

section Top

variable {m : ℕ} {I : Seed.{u} α m} {o r : Fin I.left.card} {L : Lvl I m}

local notation "𝒜" => lowPred (m + 1) (lowN I (m + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

local notation "𝒞" => lowCat I (m + 1) (lowN I (m + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

/-- **The strongly coded LOW layer at the top**: the argument of
`ProfileTower.exists_isLowLayer_top` with the strongly coded display; the completion is the
catalogue layer itself, strongly coded over a strongly coded level
(`ProfileTower.Lvl.Good.isStronglyCoded_catNext`). -/
theorem exists_isStronglyCodedLowLayer_top (hα : Order.IsSuccPrelimit α) (hL : L.Good)
    (hs : I.left.IsSourceGapContextAt (m + 1) Fin.castSuccEmb (Fin.last m) o r)
    (htb : I.right.topGrade ≤ m + 1) (hN : (L.catNext 𝒜).Good)
    (hLs : L.S.rows.IsStronglyCoded) :
    ∃ (D : StageType.{u} α (m + 2)) (h₁ : restrictFace Fin.castSuccEmb D = some I.left)
      (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some I.right)
      (G : Finset Label.{u}) (entry : Fin D.card → LowField D → Label.{u})
      (s : LowField D → Label.{u}) (lo hi : Fin D.card), D.IsLegal ∧ D.rows.IsStronglyCoded ∧
        D.label lo ≠ ⊤ ∧
        D.label hi = ⊤ ∧ IsLowLayer (m + 1) h₁ h₂ o r G entry s lo hi := by
  classical
  obtain ⟨ihi, hihi⟩ := exists_equivFin_eq (sepHi_mem (o := o) (r := r) hs htb)
  obtain ⟨ilo, hilo⟩ := exists_equivFin_eq (sepLo_mem (o := o) (r := r) hs htb)
  set u : Fin (L.catS 𝒞).card := Fin.natAdd L.S.card ihi with hu_def
  have hu : (L.catS 𝒞).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), m + 1) :=
    Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _
  have hall (z : Fin (L.catS 𝒞).card) :
      z ∈ (L.catS 𝒞).toCellScheme.below ((univ : Finset (Fin (m + 2))), m + 1) :=
    ⟨subset_univ _, Nat.lt_succ_iff.mp (hN.grade_lt_succ z)⟩
  -- the decoded row of the controller of the actual profile
  have hK : (L.catS 𝒞).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), m + 1)
      (fun d ↦ sepDecoder I m ((L.catS 𝒞).rowAt u d)) :=
    (Scheme.isLawfulBelow_rowAt hN.consistent hu).map_of_apply_eq_bot (fun z ↦ z.2.2)
      isWitness_sepDecoder fun _ ↦ eq_bot_of_upperDecoderAt_eq_bot
  have hq₀ : (L.catS 𝒞).rows.IsLawful fun d ↦ sepDecoder I m ((L.catS 𝒞).rowAt u d) :=
    hK.isLawful hall
  set q : Fin (L.catS 𝒞).card → Label.{u} :=
    fun d ↦ Label.reduce α (sepDecoder I m ((L.catS 𝒞).rowAt u d)) with hq_def
  have hq : (L.catS 𝒞).rows.IsLawful q := hq₀.reduce hα
  have hqα (d : Fin (L.catS 𝒞).card) : AtStage α (q d) := atStage_reduce α _
  -- the old cells read the glued labels
  have hold (d : Fin I.amalgam.card) :
      sepDecoder I m ((L.catS 𝒞).rowAt u (Fin.castAdd _ (L.embed d))) = I.amalgam.label d := by
    have hd : I.amalgam.toCellScheme.grade d ≤ m + 1 := Nat.lt_succ_iff.mp (I.grade_lt d)
    rw [hu_def, rowAt_catS_natAdd_castAdd ihi (by rw [hL.lowerEmb.grade_eq]; exact hd),
      hL.literal, hihi]
    change upperDecoderAt (m + 1) (m + 2) (bound I) (hat I (m + 1) I.amalgam.label)
      (orbitCode (m + 1) (hat I (m + 1) I.amalgam.label) d) = _
    rw [upperDecoderAt_orbitCode, hat_of_le hd]
  have hqe (d : Fin I.amalgam.card) : q ((L.catNext 𝒜).embed d) = I.amalgam.label d := by
    change Label.reduce α (sepDecoder I m ((L.catS 𝒞).rowAt u (Fin.castAdd _ (L.embed d)))) = _
    rw [hold d, (I.amalgam.atStage d).reduce_eq]
  set F := hN.completionSucc (q := q) hq hqe with hF_def
  have hqF : F.scheme.rows.IsLawful q := hq
  -- the separator
  have hlo : q (Fin.natAdd L.S.card ilo) ≠ ⊤ := by
    change Label.reduce α (sepDecoder I m ((L.catS 𝒞).rowAt u (Fin.natAdd _ ilo))) ≠ ⊤
    rw [hu_def, rowAt_catS_natAdd_natAdd (L := L) ihi ilo, hihi, hilo,
      agreementHeight_sepHi_sepLo_top hs, reduce_of_lt (sepDecoder_cutoffCut_lt hα)]
    exact ne_top_of_lt (sepDecoder_cutoffCut_lt hα)
  have hhi : q (Fin.natAdd L.S.card ihi) = ⊤ := by
    change Label.reduce α (sepDecoder I m ((L.catS 𝒞).rowAt u (Fin.natAdd _ ihi))) = ⊤
    rw [hu_def, rowAt_catS_natAdd_natAdd (L := L) ihi ihi, hihi,
      agreementHeight_self (gridPoint_mem_grid le_rfl) (fun _ hx ↦ le_gridPoint_of_mem_grid hx),
      sepDecoder_ceiling hs, reduce_top]
  have hP := F.isGradePrefix_strongDisplay hqF hqα (K := m + 1) (by omega)
  refine ⟨F.strongDisplay hqF hqα, F.restrictFace_left_strongDisplay hqe,
    F.restrictFace_right_strongDisplay hqe, _, _, _, _, _, F.isLegal_strongDisplay hqF hqα,
    F.isStronglyCoded_strongDisplay hqF hqα (hL.isStronglyCoded_catNext hLs 𝒜), ?_, ?_,
    isLowLayer_of_isGradePrefix (o := o) (r := r) (ilo := ilo) (ihi := ihi) hL
      (ψ := Fin.castSucc) (show Scheme.IsGradePrefix (L.catS 𝒞) (F.strongDisplay hqF hqα).toScheme
        Fin.castSucc (m + 1) from hP) _ _
      (fun i ↦ F.faceCell_strongDisplay Coatom.univ_map_left_ne _ I.restrictFace_left i)
      (fun i ↦ F.faceCell_strongDisplay Coatom.univ_map_right_ne _ I.restrictFace_right i)
      (by rw [hilo, hihi]; rfl) (by rw [hihi]; exact cutoffCut_sepHi_mem)
      (by rw [hihi]; exact cutoffCut_sepHi_lt hs)⟩
  · exact fun h' ↦ hlo ((F.strongDisplay_label_castSucc hqF hqα _).symm.trans h')
  · exact (F.strongDisplay_label_castSucc hqF hqα _).trans hhi

end Top

end VaughtConjecture.ProfileTower

/-! ### The three LOW-layer targets, the LOW-donor contract, and restricted (R2) -/

namespace VaughtConjecture

namespace StageType

/-- **Target: strong coding of the padded LOW layer** (`K < k`), proved: the argument of
`StageType.hasLowLayersOn_lt` through `ProfileTower.exists_isStronglyCodedLowLayer_pTower`; the
seed of the family is strongly coded (`Seed.isStronglyCoded_amalgam`). -/
theorem stronglyCodedPaddedLowLayersTarget : StronglyCodedPaddedLowLayersTarget.{u} := by
  intro α K k t' tb p o r hα hF hKk ht' htb
  have hK0 := hF.grade_pos
  obtain ⟨g, rfl⟩ : ∃ g, K = g + 1 := ⟨K - 1, by omega⟩
  obtain ⟨J, rfl⟩ : ∃ J, k = g + J + 2 := ⟨k - (g + 2), by omega⟩
  exact ProfileTower.exists_isStronglyCodedLowLayer_pTower
    (I := Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private hF.face_donor)
    hα.isSuccPrelimit hF.isSourceGapContextAt hF.topGrade_donor
    (Seed.isStronglyCoded_amalgam _ ht' htb)

/-- **Target: strong coding of the LOW layer with the faces `⊥` above `K`**, proved: the argument
of `StageType.hasLowLayersOn_lowBotAll` through
`ProfileTower.LowReading.exists_isStronglyCodedLowLayer`; the level from the grade `0` is strongly
coded (`ProfileTower.isStronglyCoded_lvlZero`). -/
theorem stronglyCodedLowBotLowLayersTarget : StronglyCodedLowBotLowLayersTarget.{u} := by
  intro α K k t' tb p o r hα hF ⟨hKk, hl, hr⟩ ht' htb
  have hK0 := hF.grade_pos
  obtain ⟨g, rfl⟩ : ∃ g, K = g + 1 := ⟨K - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = g + 1 + j := ⟨k - (g + 1), by omega⟩
  exact ProfileTower.LowReading.exists_isStronglyCodedLowLayer
    (ProfileTower.lowReading_of_bot
      (I := Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private hF.face_donor)
      hα.isSuccPrelimit hF.isSourceGapContextAt hF.topGrade_donor
      (ProfileTower.lvlZero_good g (by omega))
      ((ProfileTower.lvlZero_good g (by omega)).lowNext' (by omega) hF.isSourceGapContextAt
        hF.topGrade_donor)
      (ProfileTower.amalgam_label_eq_bot hl hr))
    (ProfileTower.isStronglyCoded_lvlZero (Seed.isStronglyCoded_amalgam _ ht' htb) g (by omega))

/-- **Target: strong coding of the LOW layer at the full grade** (`K = k + 1`), proved: the
argument of `StageType.hasLowLayersOn_fullGradeAll` through
`ProfileTower.exists_isStronglyCodedLowLayer_top`. -/
theorem stronglyCodedFullGradeLowLayersTarget : StronglyCodedFullGradeLowLayersTarget.{u} := by
  intro α K k t' tb p o r hα hF hKk ht' htb
  subst hKk
  exact ProfileTower.exists_isStronglyCodedLowLayer_top
    (I := Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private hF.face_donor)
    hα.isSuccPrelimit (ProfileTower.lvlZero_good k le_rfl) hF.isSourceGapContextAt
    hF.topGrade_donor ((ProfileTower.lvlZero_good k le_rfl).lowNext_top' hF.isSourceGapContextAt
      hF.topGrade_donor)
    (ProfileTower.isStronglyCoded_lvlZero (Seed.isStronglyCoded_amalgam _ ht' htb) k le_rfl)

/-- **Strong-coding preservation by the three constructions of the LOW layer** (proved). -/
theorem stronglyCodedLowLayersPreservationTarget :
    StronglyCodedLowLayersPreservationTarget.{u} :=
  ⟨stronglyCodedPaddedLowLayersTarget, stronglyCodedLowBotLowLayersTarget,
    stronglyCodedFullGradeLowLayersTarget⟩

/-- **Strongly coded LOW displays for every LOW family with strongly coded faces** (proved). -/
theorem hasStronglyCodedLowDisplays : HasStronglyCodedLowDisplays.{u} :=
  (hasStronglyCodedLowLayersOn_of_targets
    stronglyCodedLowLayersPreservationTarget).hasStronglyCodedLowDisplays

end StageType

namespace Realization

/-- **The strongly coded LOW-donor contract** (proved): strongly coded LOW displays
(`StageType.hasStronglyCodedLowDisplays`) through
`Realization.stronglyCodedLowDonorTarget_of_hasStronglyCodedLowDisplays`. -/
theorem stronglyCodedLowDonorTarget : StronglyCodedLowDonorTarget.{u} :=
  stronglyCodedLowDonorTarget_of_hasStronglyCodedLowDisplays StageType.hasStronglyCodedLowDisplays

/-- **Restricted (R2)** (proved): a realization in the strongly coded receiving class at `λ_ξ`
with the residual property `K` has exact one-point receiving of the strongly coded cofaces of top
grade at most `K`.  It is `Realization.stronglyCodedResidualDerivationTarget` with the three
premises proved: the acquisition (`Realization.stronglyCodedSourceGapAcquisitionTarget`), the
relabelling (`Realization.stronglyCodedRelabelTarget`) and the LOW-donor contract
(`Realization.stronglyCodedLowDonorTarget`). -/
theorem stronglyCodedResidualReceiving (ξ : Ordinal.{0}) (M : Type w) :
    StronglyCodedResidualReceiving ξ M :=
  stronglyCodedResidualDerivationTarget ξ M stronglyCodedSourceGapAcquisitionTarget
    stronglyCodedRelabelTarget stronglyCodedLowDonorTarget

end Realization

end VaughtConjecture
