/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowFullGradeStep
import VaughtConjecture.Continuation.LowDisplayActual
import VaughtConjecture.MainTheorem.LowDisplayReadingRoute

/-!
# LOW displays at the full grade `K = k + 1`

Roadmap, Layer 3 ((R2), the LOW construction at the grade `K = k + 1`).

At a LOW family on `k + 1` points with `K = k + 1`, the owner is the cell of full scope and full
grade of the private context, and the seed `I` of the family lives on `k + 2` points.  The LOW
layer is the catalogue layer at the grade `k + 1` over the good level at the grade `k`
(`ProfileTower.Lvl.Good.lowNext_top`), and it is itself the top layer below the apex: no canonical
level and no field layer is placed above it.

* **The completion from a good level at the grade `m + 1`**
  (`ProfileTower.Lvl.Good.completionSucc`): a good level at the grade `m + 1` on `m + 2` points is
  legal below the full grade (`ProfileTower.Lvl.Good.isLegalBelowFullGrade_succ`: its lifts from
  the coatoms reach every grade up to `m + 1`, and off the full face the lifts are those of the
  amalgam), and with a lawful labelling extending the glued labels it is a completion below the
  full grade.
* **The reading at the top** (`ProfileTower.exists_isLowLayer_top`): the labels are the decoded
  row of the controller of the actual profile (`ProfileTower.sepHi`), reduced to the stage.  Every
  cell lies below that controller, so no condition on labels above `K` arises (there are no grades
  above `K` below the apex); the controller reads itself at the ceiling of the grid, `⊤`, and the
  controller of its partner (`ProfileTower.sepLo`) below the stage.  The display (the apex added)
  is legal, has literal faces, and carries a LOW layer with this separator
  (`ProfileTower.isLowLayer_of_isGradePrefix`).
* **The route** (`StageType.hasLowLayersOn_fullGrade`, `StageType.hasLowDisplaysOn_fullGrade`):
  LOW displays on the class `StageType.LowFullGradeClass` (a donor top of grade `K`, `K = k + 1`):
  (R2) for these LOW families, with no condition on labels.

## References

The LOW layer is the step of [AFK26] at the owner's grade; generalized saturation and the display
are those of [Kni26, §4.3].
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme StageType

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-! ### The completion from a good level at the grade `m + 1` -/

section Completion

variable {N : Lvl I (m + 1)}

/-- Every cell of a good level at the grade `m + 1` has grade below `m + 2`. -/
theorem Lvl.Good.grade_lt_succ (hN : N.Good) (z : Fin N.S.card) :
    N.S.toCellScheme.grade z < m + 2 := by
  rcases N.inv z with h | h
  · omega
  · obtain ⟨d, rfl⟩ := hN.mem_range z h
    rw [hN.lowerEmb.grade_eq]
    exact I.grade_lt d

/-- **A good level at the grade `m + 1` is legal below the full grade**: well formed, coded and
consistent by goodness; bountiful (`CellScheme.Rows.isBountiful_of_coatoms`), the lifts from the
coatoms into the full face at every grade up to `m + 1` being those of the level and the other
lifts those of the amalgam; complete below `m + 2`. -/
theorem Lvl.Good.isLegalBelowFullGrade_succ (hN : N.Good) : N.S.IsLegalBelowFullGrade where
  isWellFormed := hN.wf
  isCoded := hN.coded
  isConsistent := hN.consistent
  isBountiful := by
    have hfull {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2))))
        (j : ℕ) (hj : j ≤ #(univ.erase x)) :
        N.S.rows.CappedLift (X := (univ.erase x, j)) (Y := ((univ : Finset (Fin (m + 2))), j))
          ⟨erase_subset _ _, le_rfl⟩ := by
      rw [Seed.card_erase] at hj
      exact hN.lift x hx j hj
    have hfaces : N.S.toCellScheme.faces = I.amalgam.toCellScheme.faces := hN.faces
    have hgf : N.S.toCellScheme.gradedFaces = I.amalgam.toCellScheme.gradedFaces := by
      unfold CellScheme.gradedFaces
      rw [hfaces]
    exact Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last (m + 1))
      (b := Fin.castSucc (Fin.last m)) (mem_univ _) (mem_univ _)
      (fun B hB hne ↦ I.subset_or_subset B (hfaces ▸ hB) hne)
      (hfaces ▸ I.erase_last_mem_faces)
      (hfaces ▸ I.erase_castSucc_mem_faces)
      (fun X Y hX hY h hYne ↦ hN.cappedLift_old (hgf ▸ hX) (hgf ▸ hY) hYne h)
      (hfull (by simp)) (hfull (by simp))
  grade_lt := hN.grade_lt_succ
  exists_gradedIndex_eq X hX hX2 := by
    obtain ⟨B, j⟩ := X
    by_cases hB : B = univ
    · subst hB
      exact hN.complete j hX.2.1 (by simp only at hX2; omega)
    · have hfaces : N.S.toCellScheme.faces = I.amalgam.toCellScheme.faces := hN.faces
      obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq (B, j) ⟨hfaces ▸ hX.1, hX.2⟩ hB
      exact ⟨N.embed d, (hN.gradedIndex_embed d).trans hd⟩

/-- **The completion below the full grade from a good level at the grade `m + 1`** and a lawful
labelling extending the glued labels: the level itself, with no layer above it. -/
noncomputable def Lvl.Good.completionSucc (hN : N.Good) {q : Fin N.S.card → Label.{u}}
    (hq : N.S.rows.IsLawful q) (hqe : ∀ d, q (N.embed d) = I.amalgam.label d) :
    CompletionBelowFullGrade I where
  scheme := N.S
  embed := N.embed
  isLowerEmbedding := hN.lowerEmb
  scope_embed := hN.scope_embed
  comap_rows := hN.comap_rows
  mem_range_embed := hN.mem_range
  faces_eq := hN.faces
  isLegalBelowFullGrade := hN.isLegalBelowFullGrade_succ
  label := q
  isLawful := hq
  label_embed := hqe

end Completion

/-! ### The reading at the top -/

section Top

variable {o r : Fin I.left.card} {L : Lvl I m}

local notation "𝒜" => lowPred (m + 1) (lowN I (m + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

local notation "𝒞" => lowCat I (m + 1) (lowN I (m + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

/-- **The actual profile and its partner agree up to the cutoff cut** (as
`ProfileTower.agreementHeight_sepHi_sepLo`, on a seed of any arity). -/
theorem agreementHeight_sepHi_sepLo_top
    (hs : I.left.IsSourceGapContextAt (m + 1) Fin.castSuccEmb (Fin.last m) o r) :
    agreementHeight (grid (m + 1) (bound I)) (sepHi I m) (sepLo I m) =
      cutoffCut (m + 1) (lowNAll I) (sepHi I m) := by
  have hG : (⊥ : Label.{u}) ∈ grid (m + 1) (bound I) := bot_mem_grid _ _
  have hlt := cutoffCut_sepHi_lt hs
  refine le_antisymm (not_lt.mp fun hgt ↦ ?_) (le_agreementHeight cutoffCut_sepHi_mem fun f ↦ ?_)
  · have h := (agreementHeight_spec hG (sepHi I m) (sepLo I m)).2 (Sum.inr ())
    have h2 : sepLo I m (Sum.inr ()) = cutoffCut (m + 1) (lowNAll I) (sepHi I m) :=
      Function.update_self _ _ _
    rw [h2, min_eq_left hgt.le] at h
    exact (lt_min hlt hgt).ne' h
  · rcases f with d | z
    · rw [sepLo, Function.update_of_ne Sum.inl_ne_inr]
    · cases z
      rw [sepLo, Function.update_self, min_eq_right hlt.le, min_self]

/-- **The LOW layer at the top of a legal display**: at a stage that is zero or a limit, for the
seed of a LOW family at `K = m + 1` (the private context a source-gap context of grade `m + 1` with
the lost point last, the donor of top grade at most `m + 1`), over a good level at the grade `m`
whose LOW layer is a good level (`ProfileTower.Lvl.Good.lowNext_top`), the decoded row of the
controller of the actual profile, reduced to the stage, completes the LOW layer to a legal display
with literal faces, carrying a LOW layer whose separator is labelled by a proper label and by
`⊤`. -/
theorem exists_isLowLayer_top (hα : Order.IsSuccPrelimit α) (hL : L.Good)
    (hs : I.left.IsSourceGapContextAt (m + 1) Fin.castSuccEmb (Fin.last m) o r)
    (htb : I.right.topGrade ≤ m + 1) (hN : (L.catNext 𝒜).Good) :
    ∃ (D : StageType.{u} α (m + 2)) (h₁ : restrictFace Fin.castSuccEmb D = some I.left)
      (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some I.right)
      (G : Finset Label.{u}) (entry : Fin D.card → LowField D → Label.{u})
      (s : LowField D → Label.{u}) (lo hi : Fin D.card), D.IsLegal ∧ D.label lo ≠ ⊤ ∧
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
  have hP := F.isGradePrefix_display hqF hqα (K := m + 1) (by omega)
  refine ⟨F.display hqF hqα, F.restrictFace_left_display hqe, F.restrictFace_right_display hqe,
    _, _, _, _, _, F.isLegal_display hqF hqα, ?_, ?_,
    isLowLayer_of_isGradePrefix (o := o) (r := r) (ilo := ilo) (ihi := ihi) hL
      (ψ := Fin.castSucc) (show Scheme.IsGradePrefix (L.catS 𝒞) (F.display hqF hqα).toScheme
        Fin.castSucc (m + 1) from hP) _ _
      (fun i ↦ F.faceCell_display Coatom.univ_map_left_ne _ I.restrictFace_left i)
      (fun i ↦ F.faceCell_display Coatom.univ_map_right_ne _ I.restrictFace_right i)
      (by rw [hilo, hihi]; rfl) (by rw [hihi]; exact cutoffCut_sepHi_mem)
      (by rw [hihi]; exact cutoffCut_sepHi_lt hs)⟩
  · exact fun h' ↦ hlo ((F.display_label_castSucc hqF hqα _).symm.trans h')
  · exact (F.display_label_castSucc hqF hqα _).trans hhi

end Top

end VaughtConjecture.ProfileTower

/-! ### The route at the full grade -/

namespace VaughtConjecture.StageType

open Finset

variable (α : Ordinal.{u}) in
/-- **The class of the full grade**: the LOW families with a donor top of grade `K` and
`K = k + 1` (the owner is the cell of full scope and full grade of the private context).  No
condition on labels: there is no grade above `K` below the apex. -/
def LowFullGradeClass (K k : ℕ) (t' tb : StageType.{u} α (k + 1)) (_ : StageType.{u} α k)
    (_ _ : Fin t'.card) : Prop :=
  (∃ z, tb.label z = ⊤ ∧ tb.toCellScheme.grade z = K) ∧ K = k + 1

/-- **LOW layers on the class of the full grade** (`ProfileTower.exists_isLowLayer_top`, over the
good level at the grade `k` of the seed of the family). -/
theorem hasLowLayersOn_fullGrade : HasLowLayersOn.{u} LowFullGradeClass := by
  intro α K k t' tb p o r hα hF ⟨⟨z, hz, hzK⟩, hKk⟩
  subst hKk
  exact ProfileTower.exists_isLowLayer_top
    (I := Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private hF.face_donor)
    hα.isSuccPrelimit (ProfileTower.lvlZero_good k le_rfl) hF.isSourceGapContextAt
    hF.topGrade_donor ((ProfileTower.lvlZero_good k le_rfl).lowNext_top hF.isSourceGapContextAt
      hF.topGrade_donor hz hzK)

/-- **LOW displays on the class of the full grade**: (R2) for the LOW families with `K = k + 1`
and a donor top of grade `K`. -/
theorem hasLowDisplaysOn_fullGrade : HasLowDisplaysOn.{u} LowFullGradeClass :=
  hasLowLayersOn_fullGrade.hasLowDisplaysOn

/-- **LOW displays on the union of the class of the faces `⊥` above `K` and the class of the full
grade**: with a donor top of grade `K`, every LOW family with `K ≤ k` and the faces `⊥` above `K`,
or with `K = k + 1`, has a LOW display (`StageType.hasLowDisplaysOn_lowBot`,
`StageType.hasLowDisplaysOn_fullGrade`). -/
theorem hasLowDisplaysOn_lowBot_or_fullGrade :
    HasLowDisplaysOn.{u} fun α K k t' tb p o r ↦ LowBotClass α K k t' tb p o r ∨
      LowFullGradeClass α K k t' tb p o r := by
  intro α K k t' tb p o r hα hF hS
  rcases hS with hS | hS
  · exact hasLowDisplaysOn_lowBot t' tb p o r hα hF hS
  · exact hasLowDisplaysOn_fullGrade t' tb p o r hα hF hS

end VaughtConjecture.StageType
