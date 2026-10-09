/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowDisplayTower
import VaughtConjecture.Continuation.LowLayer

/-!
# The LOW layer of the completed display

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the LOW layer of the
display); semantic contract, items 3, 4 and 8.

Let `I` be a seed, `L` a good level at the grade `g`, `C` the LOW catalogue at `K = g + 1` for the
designations of the seed (`ProfileTower.lowN`, `ProfileTower.lowT`, the copies of the owner `o`
and the lost top `r` of the private context), and `D` a stage type on `m + 2` points with the
private context and the donor as faces, in which the LOW layer over `L` is a grade prefix at `K`
along a cell map `ψ` (`Scheme.IsGradePrefix`), the cells of the two faces being the images of the
old cells.  The completed display (`CompletionBelowFullGrade.display` over
`ProfileTower.lowCompletion`) is such a `D` (`ProfileTower.isGradePrefix_lowDisplay`,
`ProfileTower.faceCell_lowDisplay`).

**The controllers of `D`** are the images of the controllers of the LOW layer
(`ProfileTower.exists_ctrl_eq`): every cell of `D` of grade at most `K` is an image, and the
images of graded index `(univ, K)` are the new cells.

**The entries** (`ProfileTower.lowFields`, `ProfileTower.lowEntry`).  The fields of `D` are its
cells and the cutoff.  The entry of the profile `P` reads, at the image of a cell `e` of `L`, the
section `σ (camal P) e` of `L`; at the other cells `⊥`; at the cutoff the cutoff of `P`.  At the
old cells the section is literal, so the entry reads `P` there
(`ProfileTower.lowFields_old`).  The entry of a controller is the entry of its profile.

**The LOW layer** (`ProfileTower.isLowLayer_of_isGradePrefix`, compiled in this repository):

* `rowAt_old`: a controller reads a cell of grade at most `K` that is not a controller at its
  entry, since that cell is the image of a cell of `L`, read by the row of the profile through the
  section of `L` (rows are read through the grade prefix, `Scheme.IsGradePrefix.rowAt_eq`);
* `rowAt_controller`: the agreement height in the grid at `K` of two entries, over all fields of
  `D`, is that of the two profiles over the profile fields
  (`ProfileTower.agreementHeight_lowFields`): the old cells carry the profiles literally
  (`ProfileTower.Lvl.Good.literal`), and the sections of profiles agreeing capped at a grid
  member agree capped there (`ProfileTower.Lvl.Good.capAgree`; grid members are self-visible and
  short);
* `isLowAt`: the donor maximum of the entry over all proper donor cells bounds the donor maximum
  of the profile over the proper donor cells of grade at most `K`, and the donor tops, the owner,
  the lost top and the cutoff are read literally (`ProfileTower.isLowAt_lowFields`);
* the separator: two controllers whose profiles are a profile `P` of the catalogue and its partner
  over all proper donor cells (`ProfileTower.lowNAll`), with the cutoff cut in the grid and below
  the cutoff (`ProfileTower.cutoffCut_lowFields`).

The labels of `D` do not enter `IsLowLayer`; the separator labels asked by
`StageType.HasLowLayers` are a statement about the labelling of `D` (see
`VaughtConjecture.Continuation.LowDisplayReading`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme StageType

variable {α : Ordinal.{u}} {m g : ℕ} {I : Seed.{u} α m} {L : Lvl I g}

variable (I) in
open Classical in
/-- The **proper donor fields of all grades** of a seed: the copies of the donor cells not
labelled `⊤`. -/
noncomputable def lowNAll : Finset (Fin I.amalgam.card ⊕ Unit) :=
  (univ.filter fun t ↦ I.right.label t ≠ ⊤).image
    fun t ↦ Sum.inl (StageType.faceCell I.restrictFace_right t)

/-- The proper donor fields of grade at most `K` are proper donor fields. -/
theorem lowN_subset_lowNAll (K : ℕ) : lowN I K ⊆ lowNAll I := by
  classical
  intro f hf
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hf
  exact mem_image.mpr ⟨t, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ht).2.1⟩, rfl⟩

/-- The cutoff is not a proper donor field. -/
theorem inr_notMem_lowNAll : Sum.inr () ∉ lowNAll I := fun hf ↦ by
  obtain ⟨t, -, ht⟩ := mem_image.mp hf
  cases ht

section Fields

variable {D : StageType.{u} α (m + 2)} {C : Finset (CProf I)}
  (ψ : Fin (L.catS C).card → Fin D.card)

open Classical in
/-- The **entry of a profile** over the fields of `D`: the section of `L` at the images of the
cells of `L`, `⊥` at the other cells, and the cutoff of the profile at the cutoff. -/
noncomputable def lowFields (P : CProf I) : LowField D → Label.{u} :=
  Sum.elim (Function.extend (ψ ∘ Fin.castAdd C.card) (L.σ (camal P)) fun _ ↦ ⊥)
    fun _ ↦ P (Sum.inr ())

open Classical in
/-- The **profile of a cell of `D`**: the profile of the controller of the LOW layer it is the
image of, `⊥` at the other cells. -/
noncomputable def ctrlProf (w : Fin D.card) : CProf I :=
  Function.extend (ψ ∘ Fin.natAdd L.S.card) (fun i ↦ (C.equivFin.symm i).1) (fun _ _ ↦ ⊥) w

/-- The **entry of a cell of `D`**: the entry of its profile. -/
noncomputable def lowEntry (w : Fin D.card) : LowField D → Label.{u} :=
  lowFields ψ (ctrlProf ψ w)

variable {ψ}

theorem lowFields_castAdd (hψ : Function.Injective ψ) (P : CProf I) (e : Fin L.S.card) :
    lowFields ψ P (Sum.inl (ψ (Fin.castAdd C.card e))) = L.σ (camal P) e :=
  (hψ.comp (Fin.castAdd_injective _ _)).extend_apply (L.σ (camal P)) (fun _ ↦ ⊥) e

theorem lowFields_of_notMem (P : CProf I) {c : Fin D.card}
    (hc : ¬ ∃ e, ψ (Fin.castAdd C.card e) = c) : lowFields ψ P (Sum.inl c) = ⊥ :=
  Function.extend_apply' (L.σ (camal P)) (fun _ ↦ ⊥) c hc

@[simp] theorem lowFields_inr (P : CProf I) (z : Unit) :
    lowFields ψ P (Sum.inr z) = P (Sum.inr ()) :=
  rfl

/-- **The entry reads the profile literally at the old cells.** -/
theorem lowFields_old (hL : L.Good) (hψ : Function.Injective ψ) (P : CProf I)
    (d : Fin I.amalgam.card) :
    lowFields ψ P (Sum.inl (ψ (Fin.castAdd C.card (L.embed d)))) = P (Sum.inl d) := by
  rw [lowFields_castAdd hψ, hL.literal]

theorem ctrlProf_natAdd (hψ : Function.Injective ψ) (i : Fin C.card) :
    ctrlProf ψ (ψ (Fin.natAdd L.S.card i)) = (C.equivFin.symm i).1 :=
  (hψ.comp (Fin.natAdd_injective _ _)).extend_apply _ _ i

theorem lowEntry_natAdd (hψ : Function.Injective ψ) (i : Fin C.card) :
    lowEntry ψ (ψ (Fin.natAdd L.S.card i)) = lowFields ψ (C.equivFin.symm i).1 := by
  rw [lowEntry, ctrlProf_natAdd hψ]

/-- **The agreement height of two entries** in the grid at `g + 1`, over all fields of `D`, is the
agreement height of the two profiles, for profiles with values in the code grid. -/
theorem agreementHeight_lowFields (hL : L.Good) (hψ : Function.Injective ψ) {P P' : CProf I}
    (hPB : ∀ f, P f ∈ codeGrid (g + 1) (bound I)) :
    agreementHeight (grid (g + 1) (bound I)) (lowFields ψ P) (lowFields ψ P') =
      agreementHeight (grid (g + 1) (bound I)) P P' := by
  classical
  have hG : (⊥ : Label.{u}) ∈ grid (g + 1) (bound I) := bot_mem_grid _ _
  refine le_antisymm (le_agreementHeight (agreementHeight_spec hG _ _).1 fun f ↦ ?_)
    (le_agreementHeight (agreementHeight_spec hG _ _).1 fun f ↦ ?_)
  · have hs := (agreementHeight_spec hG (lowFields ψ P) (lowFields ψ P')).2
    rcases f with d | z
    · have := hs (Sum.inl (ψ (Fin.castAdd C.card (L.embed d))))
      rwa [lowFields_old hL hψ, lowFields_old hL hψ] at this
    · exact hs (Sum.inr z)
  · set h := agreementHeight (grid (g + 1) (bound I)) P P'
    have hs := (agreementHeight_spec hG P P').2
    have hmem := (agreementHeight_spec hG P P').1
    rcases f with c | z
    · by_cases hc : ∃ e, ψ (Fin.castAdd C.card e) = c
      · obtain ⟨e, rfl⟩ := hc
        rw [lowFields_castAdd hψ, lowFields_castAdd hψ]
        exact hL.capAgree (camal P) (camal P') (fun d ↦ hPB _) h (isSelfVisible_of_mem_grid hmem)
          (isShort_of_mem_grid hmem) (fun d ↦ hs (Sum.inl d)) e
      · rw [lowFields_of_notMem P hc, lowFields_of_notMem P' hc]
    · exact hs (Sum.inr ())

/-! ### Controllers and old cells of `D` -/

/-- **The controllers of `D` are the images of the controllers of the LOW layer.** -/
theorem exists_ctrl_eq (hψ : Scheme.IsGradePrefix (L.catS C) D.toScheme ψ (g + 1))
    {w : Fin D.card}
    (hw : D.toCellScheme.gradedIndex w = ((univ : Finset (Fin (m + 2))), g + 1)) :
    ∃ i, ψ (Fin.natAdd L.S.card i) = w := by
  obtain ⟨u, rfl⟩ := hψ.mem_range w (congrArg Prod.snd hw).le
  rw [hψ.gradedIndex_eq] at hw
  obtain ⟨i, rfl⟩ := L.exists_natAdd_eq_catS hw
  exact ⟨i, rfl⟩

/-- **The other cells of `D` of grade at most `g + 1` are the images of the cells of `L`.** -/
theorem exists_old_eq (hψ : Scheme.IsGradePrefix (L.catS C) D.toScheme ψ (g + 1))
    {d : Fin D.card} (hd : D.toCellScheme.grade d ≤ g + 1)
    (hne : D.toCellScheme.gradedIndex d ≠ ((univ : Finset (Fin (m + 2))), g + 1)) :
    ∃ e, ψ (Fin.castAdd C.card e) = d := by
  obtain ⟨u, rfl⟩ := hψ.mem_range d hd
  rw [hψ.gradedIndex_eq] at hne
  induction u using Fin.addCases with
  | left e => exact ⟨e, rfl⟩
  | right i => exact absurd (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i) hne

/-- A controller of the LOW layer reads a cell of `L` of grade at most `g + 1` through the
section of `L` at its profile. -/
theorem rowAt_catS_natAdd_castAdd (i : Fin C.card) {e : Fin L.S.card}
    (he : L.S.toCellScheme.grade e ≤ g + 1) :
    (L.catS C).rowAt (Fin.natAdd L.S.card i) (Fin.castAdd C.card e) =
      L.σ (camal (C.equivFin.symm i).1) e := by
  have hmem : Fin.castAdd C.card e ∈ (L.catS C).toCellScheme.below
      ((L.catS C).toCellScheme.gradedIndex (Fin.natAdd L.S.card i)) := by
    rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_natAdd,
      Scheme.appendFullCellsScheme_gradedIndex_castAdd]
    exact ⟨subset_univ _, he⟩
  rw [Scheme.rowAt_of_mem hmem, Scheme.appendFullCells_row_natAdd, Lvl.Φcat_castAdd]

/-- A controller of the LOW layer reads a controller at the agreement height of their profiles. -/
theorem rowAt_catS_natAdd_natAdd (i i' : Fin C.card) :
    (L.catS C).rowAt (Fin.natAdd L.S.card i) (Fin.natAdd L.S.card i') =
      agreementHeight (grid (g + 1) (bound I)) (C.equivFin.symm i).1 (C.equivFin.symm i').1 := by
  have hmem : Fin.natAdd L.S.card i' ∈ (L.catS C).toCellScheme.below
      ((L.catS C).toCellScheme.gradedIndex (Fin.natAdd L.S.card i)) := by
    rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_natAdd,
      Scheme.appendFullCellsScheme_gradedIndex_natAdd]
  rw [Scheme.rowAt_of_mem hmem, Scheme.appendFullCells_row_natAdd, Lvl.Φcat_natAdd]

/-! ### The designated fields -/

variable {h₁ : restrictFace Fin.castSuccEmb D = some I.left}
  {h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some I.right}

/-- **The donor maximum of an entry over all proper donor cells** is that of the profile over the
copies of the proper donor cells, when the donor face reads the old cells. -/
theorem donorMax_lowFields (hL : L.Good) (hψ : Function.Injective ψ)
    (hface₂ : ∀ i, faceCell h₂ i =
      ψ (Fin.castAdd C.card (L.embed (faceCell I.restrictFace_right i)))) (P : CProf I) :
    donorMax (properDonorFields h₂) (lowFields ψ P) = donorMax (lowNAll I) P := by
  classical
  have hd₂ (y : Fin I.right.card) : lowFields ψ P (Sum.inl (faceCell h₂ y)) =
      P (Sum.inl (faceCell I.restrictFace_right y)) := by
    rw [hface₂, lowFields_old hL hψ]
  refine le_antisymm (Finset.sup_le fun f hf ↦ ?_) (Finset.sup_le fun f hf ↦ ?_)
  · obtain ⟨y, hy, rfl⟩ := mem_image.mp hf
    rw [hd₂]
    exact le_donorMax (mem_image.mpr ⟨y, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2⟩, rfl⟩)
  · obtain ⟨y, hy, rfl⟩ := mem_image.mp hf
    rw [← hd₂]
    exact le_donorMax (mem_image.mpr ⟨y, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2⟩, rfl⟩)

/-- **The cutoff cut of an entry** is the cutoff cut of the profile over all proper donor cells. -/
theorem cutoffCut_lowFields (hL : L.Good) (hψ : Function.Injective ψ)
    (hface₂ : ∀ i, faceCell h₂ i =
      ψ (Fin.castAdd C.card (L.embed (faceCell I.restrictFace_right i)))) (K : ℕ) (P : CProf I) :
    cutoffCut K (properDonorFields h₂) (lowFields ψ P) = cutoffCut K (lowNAll I) P := by
  rw [cutoffCut, cutoffCut, donorMax_lowFields hL hψ hface₂]

/-- **The entry of a state LOW over the proper donor fields of every grade is LOW** for the
designations of `D`: the donor maximum of the entry over all proper donor cells is that of the
state over all proper donor fields (`ProfileTower.donorMax_lowFields`), and the donor tops, the
owner, the lost top and the cutoff are read literally. -/
theorem isLowAt_lowFields_all (hL : L.Good) (hψ : Function.Injective ψ)
    (hface₁ : ∀ i, faceCell h₁ i =
      ψ (Fin.castAdd C.card (L.embed (faceCell I.restrictFace_left i))))
    (hface₂ : ∀ i, faceCell h₂ i =
      ψ (Fin.castAdd C.card (L.embed (faceCell I.restrictFace_right i))))
    {o r : Fin I.left.card} {P : CProf I}
    (hP : IsLowAt (g + 1) (lowNAll I) (lowT I) (Sum.inl (faceCell I.restrictFace_left o))
      (Sum.inl (faceCell I.restrictFace_left r)) (Sum.inr ()) P) :
    IsLowAt (g + 1) (properDonorFields h₂) (donorTopFields h₂) (Sum.inl (faceCell h₁ o))
      (Sum.inl (faceCell h₁ r)) (Sum.inr ()) (lowFields ψ P) := by
  classical
  have hd₁ (y : Fin I.left.card) : lowFields ψ P (Sum.inl (faceCell h₁ y)) =
      P (Sum.inl (faceCell I.restrictFace_left y)) := by
    rw [hface₁, lowFields_old hL hψ]
  have hd₂ (y : Fin I.right.card) : lowFields ψ P (Sum.inl (faceCell h₂ y)) =
      P (Sum.inl (faceCell I.restrictFace_right y)) := by
    rw [hface₂, lowFields_old hL hψ]
  intro hact x hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [donorMax_lowFields hL hψ hface₂, lowFields_inr] at hact
  have h := hP hact _ ⟨y, hy, rfl⟩
  have hfr : Label.frontier (g + 1) (Sum.inl (faceCell h₁ o)) (Sum.inl (faceCell h₁ r))
      (lowFields ψ P) = Label.frontier (g + 1) (Sum.inl (faceCell I.restrictFace_left o))
        (Sum.inl (faceCell I.restrictFace_left r)) P := by
    unfold Label.frontier
    rw [hd₁, hd₁]
  rw [hfr, lowFields_inr, hd₂]
  exact h

/-- **The entry of a LOW profile is LOW** for the designations of `D`: a profile LOW over the
proper donor fields of grade at most `g + 1` is LOW over all of them (`Label.IsLowAt.of_subset`),
and `ProfileTower.isLowAt_lowFields_all` applies. -/
theorem isLowAt_lowFields (hL : L.Good) (hψ : Function.Injective ψ)
    (hface₁ : ∀ i, faceCell h₁ i =
      ψ (Fin.castAdd C.card (L.embed (faceCell I.restrictFace_left i))))
    (hface₂ : ∀ i, faceCell h₂ i =
      ψ (Fin.castAdd C.card (L.embed (faceCell I.restrictFace_right i))))
    {o r : Fin I.left.card} {P : CProf I}
    (hP : IsLowAt (g + 1) (lowN I (g + 1)) (lowT I) (Sum.inl (faceCell I.restrictFace_left o))
      (Sum.inl (faceCell I.restrictFace_left r)) (Sum.inr ()) P) :
    IsLowAt (g + 1) (properDonorFields h₂) (donorTopFields h₂) (Sum.inl (faceCell h₁ o))
      (Sum.inl (faceCell h₁ r)) (Sum.inr ()) (lowFields ψ P) :=
  isLowAt_lowFields_all hL hψ hface₁ hface₂ (hP.of_subset (lowN_subset_lowNAll _))

end Fields

/-! ### The LOW layer -/

section Layer

variable {D : StageType.{u} α (m + 2)} {o r : Fin I.left.card}

local notation "𝒞" => lowCat I (g + 1) (lowN I (g + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

/-- **The LOW layer of a display in which the LOW layer over a good level is a grade prefix at
`g + 1`**, with the cells of the two faces the images of the old cells: the entries of the
controllers are the entries of their profiles (`ProfileTower.lowEntry`), and the separator is a
pair of controllers whose profiles are a profile `s` of the catalogue and its partner over all
proper donor cells, with the cutoff cut of `s` in the grid at `g + 1` and below the cutoff of
`s`. -/
theorem isLowLayer_of_isGradePrefix (hL : L.Good) {ψ : Fin (L.catS 𝒞).card → Fin D.card}
    (hψ : Scheme.IsGradePrefix (L.catS 𝒞) D.toScheme ψ (g + 1))
    (h₁ : restrictFace Fin.castSuccEmb D = some I.left)
    (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some I.right)
    (hface₁ : ∀ i, faceCell h₁ i =
      ψ (Fin.castAdd (𝒞).card (L.embed (faceCell I.restrictFace_left i))))
    (hface₂ : ∀ i, faceCell h₂ i =
      ψ (Fin.castAdd (𝒞).card (L.embed (faceCell I.restrictFace_right i))))
    {ilo ihi : Fin (𝒞).card}
    (hsep : ((𝒞).equivFin.symm ilo).1 = Function.update ((𝒞).equivFin.symm ihi).1 (Sum.inr ())
      (cutoffCut (g + 1) (lowNAll I) ((𝒞).equivFin.symm ihi).1))
    (hmem : cutoffCut (g + 1) (lowNAll I) ((𝒞).equivFin.symm ihi).1 ∈ grid (g + 1) (bound I))
    (hlt : cutoffCut (g + 1) (lowNAll I) ((𝒞).equivFin.symm ihi).1 <
      ((𝒞).equivFin.symm ihi).1 (Sum.inr ())) :
    IsLowLayer (g + 1) h₁ h₂ o r (grid (g + 1) (bound I)) (lowEntry ψ)
      (lowFields ψ ((𝒞).equivFin.symm ihi).1) (ψ (Fin.natAdd L.S.card ilo))
      (ψ (Fin.natAdd L.S.card ihi)) := by
  classical
  have hinj := hψ.lowerEmb.injective
  have hctrl (i : Fin (𝒞).card) : D.toCellScheme.gradedIndex (ψ (Fin.natAdd L.S.card i)) =
      ((univ : Finset (Fin (m + 2))), g + 1) :=
    (hψ.gradedIndex_eq _).trans (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i)
  have hcut := cutoffCut_lowFields (C := 𝒞) hL hinj hface₂ (g + 1) ((𝒞).equivFin.symm ihi).1
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
    exact isLowAt_lowFields hL hinj hface₁ hface₂ (mem_lowCat.mp ((𝒞).equivFin.symm i).2).2.2.2
  · obtain ⟨i, rfl⟩ := exists_ctrl_eq hψ hw
    obtain ⟨e, rfl⟩ := exists_old_eq hψ hdK hd
    have he : L.S.toCellScheme.grade e ≤ g + 1 := by
      rwa [hψ.lowerEmb.grade_eq, Scheme.appendFullCellsScheme_grade_castAdd] at hdK
    rw [hψ.rowAt_eq, rowAt_catS_natAdd_castAdd i he, lowEntry_natAdd hinj, lowFields_castAdd hinj]
  · obtain ⟨i, rfl⟩ := exists_ctrl_eq hψ hw
    obtain ⟨i', rfl⟩ := exists_ctrl_eq hψ hx
    rw [hψ.rowAt_eq, rowAt_catS_natAdd_natAdd, lowEntry_natAdd hinj, lowEntry_natAdd hinj,
      agreementHeight_lowFields hL hinj (mem_lowCat.mp ((𝒞).equivFin.symm i).2).1]
  · rw [lowEntry_natAdd hinj, hsep]
    funext f
    rcases f with c | z
    · have hc : camal (Function.update ((𝒞).equivFin.symm ihi).1 (Sum.inr ())
          (cutoffCut (g + 1) (lowNAll I) ((𝒞).equivFin.symm ihi).1)) =
          camal ((𝒞).equivFin.symm ihi).1 :=
        funext fun d ↦ Function.update_of_ne (Sum.inl_ne_inr) _ _
      rw [partner_of_ne _ Sum.inl_ne_inr]
      simp only [lowFields, Sum.elim_inl, hc]
    · rw [partner, Function.update_self, hcut]
      simp only [lowFields, Sum.elim_inr, Function.update_self]

end Layer

end VaughtConjecture.ProfileTower

/-! ### The completed display -/

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme StageType

section Display

variable {α : Ordinal.{u}} {g j : ℕ} {I : Seed.{u} α (g + 1 + j)} {L : Lvl I g}
  {o r : Fin I.left.card}

local notation "𝒜" => lowPred (g + 1) (lowN I (g + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

local notation "𝒞" => lowCat I (g + 1) (lowN I (g + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

variable (hL : L.Good) (hN : (L.catNext (lowPred (g + 1) (lowN I (g + 1)) (lowT I)
    (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r))).Good)
  {q : Fin (lowCompletion hL hN lowPred_withCut_bot).scheme.card → Label.{u}}
  (hq : (lowCompletion hL hN lowPred_withCut_bot).scheme.rows.IsLawful q)
  (hqα : ∀ d, AtStage α (q d))

/-- The cells of the LOW layer among those of the completed display. -/
noncomputable abbrev lowDisplayMap : Fin (L.catS 𝒞).card →
    Fin ((lowCompletion hL hN lowPred_withCut_bot).display hq hqα).card :=
  Fin.castSucc ∘ lowCellMap j 𝒜 L

/-- **The LOW layer is a grade prefix of the completed display** at the grade `g + 1`. -/
theorem isGradePrefix_lowDisplay :
    Scheme.IsGradePrefix (L.catS 𝒞) ((lowCompletion hL hN lowPred_withCut_bot).display hq
      hqα).toScheme (lowDisplayMap hL hN hq hqα) (g + 1) :=
  ((lowCompletion hL hN lowPred_withCut_bot).isGradePrefix_display hq hqα
    (by omega)).comp (isGradePrefix_lowCompletion hL hN lowPred_withCut_bot)

variable {hq hqα}

/-- **The cells of a proper face of the completed display are the images of the old cells** of the
LOW layer. -/
theorem faceCell_lowDisplay {k : ℕ} {f : Fin k ↪ Fin (g + 1 + j + 2)} (hf : univ.map f ≠ univ)
    {t : StageType.{u} α k}
    (h : restrictFace f ((lowCompletion hL hN lowPred_withCut_bot).display hq hqα) = some t)
    (h' : restrictFace f I.amalgam = some t) (i : Fin t.card) :
    faceCell h i = lowDisplayMap hL hN hq hqα (Fin.castAdd (𝒞).card (L.embed (faceCell h' i))) := by
  rw [CompletionBelowFullGrade.faceCell_display _ hf h h', lowCompletion_embed]
  rfl

/-- **The LOW layer of the completed display**: for the profile `s` of a controller and its partner
over all proper donor cells at another, with the cutoff cut of `s` in the grid at `g + 1` and
below the cutoff of `s` (`ProfileTower.isLowLayer_of_isGradePrefix`).  The faces are the private
context and the donor, literally (`CompletionBelowFullGrade.restrictFace_left_display`,
`CompletionBelowFullGrade.restrictFace_right_display`). -/
theorem isLowLayer_lowDisplay
    (hqe : ∀ d, q ((lowCompletion hL hN lowPred_withCut_bot).embed d) = I.amalgam.label d)
    {ilo ihi : Fin (𝒞).card}
    (hsep : ((𝒞).equivFin.symm ilo).1 = Function.update ((𝒞).equivFin.symm ihi).1 (Sum.inr ())
      (cutoffCut (g + 1) (lowNAll I) ((𝒞).equivFin.symm ihi).1))
    (hmem : cutoffCut (g + 1) (lowNAll I) ((𝒞).equivFin.symm ihi).1 ∈ grid (g + 1) (bound I))
    (hlt : cutoffCut (g + 1) (lowNAll I) ((𝒞).equivFin.symm ihi).1 <
      ((𝒞).equivFin.symm ihi).1 (Sum.inr ())) :
    IsLowLayer (g + 1) ((lowCompletion hL hN lowPred_withCut_bot).restrictFace_left_display hqe)
      ((lowCompletion hL hN lowPred_withCut_bot).restrictFace_right_display hqe) o r
      (grid (g + 1) (bound I)) (lowEntry (lowDisplayMap hL hN hq hqα))
      (lowFields (lowDisplayMap hL hN hq hqα) ((𝒞).equivFin.symm ihi).1)
      (lowDisplayMap hL hN hq hqα (Fin.natAdd L.S.card ilo))
      (lowDisplayMap hL hN hq hqα (Fin.natAdd L.S.card ihi)) :=
  isLowLayer_of_isGradePrefix hL (isGradePrefix_lowDisplay hL hN hq hqα) _ _
    (faceCell_lowDisplay hL hN Coatom.univ_map_left_ne _ I.restrictFace_left)
    (faceCell_lowDisplay hL hN Coatom.univ_map_right_ne _ I.restrictFace_right) hsep hmem hlt

end Display

end VaughtConjecture.ProfileTower
