/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryAdmittedLiveCell

/-!
# A separate marker: the admitted completion at the coupled-gate type

Roadmap, Layer 3, 3.1, (R6) and 3.3; the live cell of
`VaughtConjecture.Continuation.StableRecoveryAdmittedLiveCell`.

**Generic pieces for a seed whose two coatom types are equal** (`T` on two points).

* `Seed.cappedLift_doubledLower_left`, `Seed.cappedLift_doubledLower_right`: the lifts of the
  doubled lower layer from the coatoms at the grade `1`, by the symmetric fill of the doubling
  (`Scheme.IsDoubling.cappedLift_coatom`).
* `Seed.eq_of_isLawfulBelow_lower`: a labelling of the doubled lower layer lawful below `(univ, 1)`
  agrees at the two copies of a cell of grade `1`, and at the copy of full scope.
* `Seed.exists_glueSym`: two lawful labellings of `T` agreeing at the cells of grade `1` glue to a
  lawful labelling of the doubled lower layer (the new cells read as the cells under them).
* `StageType.exists_lift_one_two`: the capped lift of a legal `T` from `(univ, 1)` to `(univ, 2)`,
  as labellings of all cells.

**At the coupled-gate type** (`CoupledGatedExtensionCounterexample`).  The (R4) cap requests
`requestsM` of the self-seed of `P α` are those of `requestsCP` with the marker moved from the cap
(the private copy of the full cell `C`) to the private copy of `z₂`, at an offset `R < 2`.

* `isCorrect_requestsM`: a lawful state is correct as soon as the donor copy of `C` reads at least
  the replaced marker capped at the cap; the requests at the cells of grade `1` hold by the
  symmetry of the doubled lower layer there (`sym_CP`).
* `exists_admits_donS_lt_privS`: the hypothesis `hA` of the obstruction
  `Seed.not_isBountiful_admittedDoubledLower` fails for this marker: the pullback of the row of `C`
  is lawful, admitted, and reads the private copy of `C` strictly above the donor copy of `z₂`.
* `exists_donorFill`, `exists_privateFill`, `exists_capGlue`: the fills at a positive cap.
* `botProvisionM_left`, `capProvisionM_left`, `botProvisionM_right`, `capProvisionM_right`: the
  four lift provisions of `Scheme.cappedLift_admittedFieldLayer`.
* `isLegalBelowFullGrade_admittedLayerM`: **the admitted layer at the grade `2` over the doubled
  lower layer is legal below the full grade**, for every `R < 2`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

namespace StageType

variable {α : Ordinal.{u}}

/-- **The capped lift of a legal type on two points from `(univ, 1)` to `(univ, 2)`**: a lawful `p`
and a lawful `q` agreeing capped at `h` at the cells of grade `1` have a lawful `r` equal to `p` at
the cells of grade `1` and agreeing with `q` capped at `h` everywhere. -/
theorem exists_lift_one_two {T : StageType.{u} α 2} (hT : T.IsLegal)
    {p q : Fin T.card → Label.{u}} (hp : T.rows.IsLawful p) (hq : T.rows.IsLawful q)
    {h : Label.{u}} (hh : IsSelfVisible 2 h)
    (hag : ∀ z, T.toCellScheme.grade z = 1 → min (p z) h = min (q z) h) :
    ∃ r : Fin T.card → Label.{u}, T.rows.IsLawful r ∧
      (∀ z, T.toCellScheme.grade z = 1 → r z = p z) ∧ ∀ z, min (r z) h = min (q z) h := by
  have hX : ((univ : Finset (Fin 2)), 1) ∈ T.toCellScheme.gradedFaces :=
    ⟨T.univ_mem_faces, one_pos, by simp⟩
  have hY : ((univ : Finset (Fin 2)), 2) ∈ T.toCellScheme.gradedFaces :=
    ⟨T.univ_mem_faces, two_pos, by simp⟩
  have hl := hT.isBountiful hX hY ⟨subset_univ _, by omega⟩
  have hmem (z : Fin T.card) : z ∈ T.toCellScheme.below ((univ : Finset (Fin 2)), 2) :=
    ⟨subset_univ _, T.grade_le z⟩
  obtain ⟨r', hr', hrq, hrp⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists _).mp hl h hh
    (fun d ↦ p d.1) (fun d ↦ q d.1) (hp.isLawfulBelow _) (hq.isLawfulBelow _) fun d ↦ by
      have hd1 : T.toCellScheme.grade d.1 = 1 :=
        le_antisymm d.2.2 ((T.isWellFormed.isWellFormed.gradedIndex_mem d.1).2.1)
      exact (hag d.1 hd1).symm
  refine ⟨fun z ↦ r' ⟨z, hmem z⟩, ?_, fun z hz ↦ ?_, fun z ↦ hrq ⟨z, hmem z⟩⟩
  · have : T.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 2) fun d ↦ r' ⟨d.1, hmem d.1⟩ := by
      convert hr' using 1
    exact this.isLawful hmem
  · exact hrp ⟨z, ⟨subset_univ _, hz.le⟩⟩

end StageType

namespace Seed

variable {α : Ordinal.{u}} {I : Seed.{u} α 1} {hLR : I.left = I.right}

/-- The cell map of the doubled lower layer at a private copy. -/
theorem lowerCell_left (z : Fin I.left.card) :
    I.lowerCell hLR (Fin.castAdd _ (StageType.faceCell I.restrictFace_left z)) = z := by
  rw [lowerCell, Fin.append_left, doublingCell_faceCell_left]

/-- The cell map of the doubled lower layer at a donor copy. -/
theorem lowerCell_right (z : Fin I.left.card) :
    I.lowerCell hLR (Fin.castAdd _ (StageType.faceCell (I.restrictFace_right_left hLR) z)) = z := by
  rw [lowerCell, Fin.append_left, doublingCell_faceCell_right]

/-- The cell map of the doubled lower layer at a copy of full scope. -/
theorem lowerCell_natAdd (i : Fin (I.nFull 1)) :
    I.lowerCell hLR (Fin.natAdd _ i) = I.left.toScheme.fullCell 1 i := by
  rw [lowerCell, Fin.append_right]

/-- A cell of `T` at `(univ, 1)` gives a copy of full scope at every positive grade at most `1`. -/
theorem exists_full_lower (hI : I.left.IsLegal) {i : ℕ} (hi : 0 < i) (hi1 : i ≤ 1) :
    ∃ a, (I.doubledLower hLR).toCellScheme.gradedIndex a = ((univ : Finset (Fin 3)), i) := by
  obtain ⟨c, hc⟩ := hI.isComplete ((univ : Finset (Fin 2)), 1)
    ⟨I.left.univ_mem_faces, one_pos, by simp⟩
  obtain ⟨i₀, -⟩ := Scheme.exists_fullCell_eq hc
  obtain rfl : i = 1 := by omega
  exact ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩

/-- Every cell of the doubled lower layer has positive grade. -/
theorem grade_pos_lower (d : Fin (I.doubledLower hLR).card) :
    0 < (I.doubledLower hLR).toCellScheme.grade d :=
  ((I.isWellFormed_doubledLower hLR).isWellFormed.gradedIndex_mem d).2.1

/-- **The lift of the doubled lower layer from the first coatom at the grade `1`**, by the
symmetric fill. -/
theorem cappedLift_doubledLower_left (hI : I.left.IsLegal) :
    (I.doubledLower hLR).rows.CappedLift (X := (univ.erase (Fin.last 2), 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  have hL := I.restrictFace_left
  have h := (I.isDoubling_doubledLower hLR).cappedLift_coatom (f := Coatom.left 1)
    collapseLast_left (cp := fun z ↦ Fin.castAdd _ (StageType.faceCell hL z))
    (fun z ↦ lowerCell_left z)
    (fun z ↦ by
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd]
      exact Prod.ext (StageType.scope_faceCell _ _) (StageType.grade_faceCell _ _))
    (fun d hd ↦ by
      induction d using Fin.addCases with
      | right i =>
        exfalso
        rw [Scheme.appendFullCellsScheme_scope_natAdd] at hd
        exact Coatom.univ_map_left_ne (subset_antisymm (subset_univ _) hd)
      | left a =>
        rw [Scheme.appendFullCellsScheme_scope_castAdd] at hd
        simp only
        rw [lowerCell, Fin.append_left, I.faceCell_left_of_subset hLR hd])
    (j := 1) (fun i hi hij ↦ exists_full_lower hI hi hij) grade_pos_lower
  rw [Coatom.univ_map_left] at h
  exact h

/-- **The lift of the doubled lower layer from the second coatom at the grade `1`.** -/
theorem cappedLift_doubledLower_right (hI : I.left.IsLegal) :
    (I.doubledLower hLR).rows.CappedLift (X := (univ.erase (Fin.castSucc (Fin.last 1)), 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  have hR := I.restrictFace_right_left hLR
  have h := (I.isDoubling_doubledLower hLR).cappedLift_coatom (f := Coatom.right 1)
    collapseLast_right (cp := fun z ↦ Fin.castAdd _ (StageType.faceCell hR z))
    (fun z ↦ lowerCell_right z)
    (fun z ↦ by
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd]
      exact Prod.ext (StageType.scope_faceCell _ _) (StageType.grade_faceCell _ _))
    (fun d hd ↦ by
      induction d using Fin.addCases with
      | right i =>
        exfalso
        rw [Scheme.appendFullCellsScheme_scope_natAdd] at hd
        exact Coatom.univ_map_right_ne (subset_antisymm (subset_univ _) hd)
      | left a =>
        rw [Scheme.appendFullCellsScheme_scope_castAdd] at hd
        simp only
        rw [lowerCell, Fin.append_left, I.faceCell_right_of_subset hLR hd])
    (j := 1) (fun i hi hij ↦ exists_full_lower hI hi hij) grade_pos_lower
  rw [Coatom.univ_map_right] at h
  exact h

/-- **Symmetry below `(univ, 1)`**: a labelling of the doubled lower layer lawful below `(univ, 1)`
takes one value on the cells over one cell of `T`. -/
theorem eq_of_isLawfulBelow_lower (hI : I.left.IsLegal)
    {w : Fin (I.doubledLower hLR).card → Label.{u}}
    (hw : (I.doubledLower hLR).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 1) fun d ↦ w d)
    {d d' : Fin (I.doubledLower hLR).card}
    (hd : (I.doubledLower hLR).toCellScheme.grade d = 1)
    (hd' : (I.doubledLower hLR).toCellScheme.grade d' = 1)
    (hπ : I.lowerCell hLR d = I.lowerCell hLR d') : w d = w d' :=
  (I.isDoubling_doubledLower hLR).eq_of_isLawfulBelow hw
    (fun e he ↦ exists_full_lower hI (grade_pos_lower e) he.2) ⟨subset_univ _, hd.le⟩
    ⟨subset_univ _, hd'.le⟩ hπ

/-- **Gluing two lawful labellings agreeing at the cells of grade `1`** on the doubled lower layer:
the new cells read as the cells of `T` under them. -/
theorem exists_glueSym (hI : I.left.IsLegal) {sL D : Fin I.left.card → Label.{u}}
    (hL : I.left.rows.IsLawful sL) (hD : I.left.rows.IsLawful D)
    (hag : ∀ z, I.left.toCellScheme.grade z = 1 → D z = sL z) :
    ∃ g : Fin (I.doubledLower hLR).card → Label.{u}, (I.doubledLower hLR).rows.IsLawful g ∧
      I.privS hLR g = sL ∧ I.donS hLR g = D ∧
        ∀ i, g (Fin.natAdd _ i) = sL (I.left.toScheme.fullCell 1 i) := by
  obtain ⟨w, hw, hwL, hwR⟩ := I.exists_isLawful_glue hLR hL hD fun z hz ↦
    (hag z (grade_eq_one_of_last_notMem hz)).symm
  have hDb := I.isDoubling_doubledLower hLR
  have hP := hDb.isLawful_comp hL
  set g : Fin (I.doubledLower hLR).card → Label.{u} :=
    Fin.append w fun i ↦ sL (I.left.toScheme.fullCell 1 i)
  -- `g` is the pullback of `sL` at the cells of grade `1`
  have hgP (t : Fin (I.doubledLower hLR).card)
      (ht : (I.doubledLower hLR).toCellScheme.grade t = 1) :
      g t = (sL ∘ I.lowerCell hLR) t := by
    induction t using Fin.addCases with
    | right i => simp only [g, Fin.append_right, Function.comp_apply, lowerCell_natAdd]
    | left a =>
      have ha : I.amalgam.toCellScheme.grade a = 1 := by
        rw [← Scheme.appendFullCellsScheme_grade_castAdd]; exact ht
      simp only [g, Fin.append_left, Function.comp_apply, lowerCell]
      rcases I.eq_faceCell_or hLR a with h | h
      · rw [← h, hwL, doublingCell_faceCell_left]
      · rw [← h, hwR, doublingCell_faceCell_right]
        rw [← h, StageType.grade_faceCell] at ha
        exact hag _ ha
  have hgrade1 (t : Fin (I.doubledLower hLR).card) (i : Fin (I.nFull 1))
      (ht : t ∈ (I.doubledLower hLR).toCellScheme.below
        ((I.doubledLower hLR).toCellScheme.gradedIndex (Fin.natAdd _ i))) :
      (I.doubledLower hLR).toCellScheme.grade t = 1 := by
    have h2 := ht.2
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd] at h2
    exact le_antisymm h2 (grade_pos_lower t)
  refine ⟨g, Scheme.isLawful_appendFullCells (h := I.not_univ_le 1) ?_ (fun i ↦ ?_) (fun i ↦ ?_)
    fun s hs ↦ ?_, ?_, ?_, fun i ↦ Fin.append_right _ _ i⟩
  · convert hw using 1
    funext d
    exact Fin.append_left _ _ d
  · rw [show g (Fin.natAdd _ i) = sL (I.left.toScheme.fullCell 1 i) from Fin.append_right _ _ i]
    have := hL.orderly (I.left.toScheme.fullCell 1 i)
    rwa [show I.left.toCellScheme.grade (I.left.toScheme.fullCell 1 i) = 1 from
      congrArg Prod.snd (Scheme.gradedIndex_fullCell 1 i)] at this
  · have hloc := hP.locality (Fin.natAdd _ i)
    convert hloc using 1
    · funext t
      exact (Scheme.appendFullCells_row_natAdd i t).symm
    · funext t
      rw [hgP t.1 (hgrade1 t.1 i t.2), hgP _ (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i)]
  · obtain ⟨a₀, ha₀⟩ := exists_full_lower (hLR := hLR) hI one_pos le_rfl
    obtain ⟨u, hu, hle⟩ := hP.availability s a₀
      (by rw [show (I.doubledLower hLR).toCellScheme.scope a₀ = univ from
        congrArg Prod.fst ha₀]; exact subset_univ _)
      (hs.trans (congrArg Prod.snd ha₀).symm)
    have hu' : (I.doubledLower hLR).toCellScheme.gradedIndex u = ((univ : Finset (Fin 3)), 1) :=
      hu.trans ha₀
    induction u using Fin.addCases with
    | left a =>
      exfalso
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd] at hu'
      exact I.scope_ne_univ a (congrArg Prod.fst hu')
    | right i =>
      refine ⟨i, ?_⟩
      rw [hgP s hs, hgP _ (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i)]
      exact hle
  · funext z
    exact (Fin.append_left _ _ _).trans (hwL z)
  · funext z
    exact (Fin.append_left _ _ _).trans (hwR z)

end Seed

/-! ### Visibility replacement at the threshold `2` of labels self-visible at `1` -/

namespace Label

private theorem mod_eq_one_of {o : Ordinal.{u}} (h1 : ((1 : ℕ) : Ordinal.{u}) ≤ o % ω)
    (h2 : o % ω < ((2 : ℕ) : Ordinal.{u})) : o % ω = ((1 : ℕ) : Ordinal.{u}) := by
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (Ordinal.mod_lt o omega0_ne_zero)
  rw [hn] at h1 h2 ⊢
  have a := Nat.cast_le.mp h1
  have b := Nat.cast_lt.mp h2
  rw [show n = 1 by omega]

/-- Visibility replacement at the threshold `2` with value `1` fixes a label self-visible at `1`. -/
theorem visibilityReplace_two_one {x : Label.{u}} (hx : IsSelfVisible 1 x) :
    visibilityReplace 2 1 x = x := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe o =>
    rw [visibilityReplace_coe]
    have h1 := isSelfVisible_coe.mp hx
    by_cases hlt : o % ω < ((2 : ℕ) : Ordinal.{u})
    · rw [Ordinal.visibilityReplace_of_lt hlt, ← mod_eq_one_of h1 hlt, Ordinal.div_add_mod]
    · rw [Ordinal.visibilityReplace_of_le (not_lt.mp hlt) 1]

/-- Visibility replacement at the threshold `2` with a value at most `1` lowers a label
self-visible at `1`. -/
theorem visibilityReplace_two_le {x : Label.{u}} (hx : IsSelfVisible 1 x) {R : ℕ} (hR : R ≤ 1) :
    visibilityReplace 2 R x ≤ x := by
  induction x using recBotCoeTop with
  | bot => exact le_rfl
  | top => exact le_rfl
  | coe o =>
    rw [visibilityReplace_coe]
    refine WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ?_)
    have h1 := isSelfVisible_coe.mp hx
    by_cases hlt : o % ω < ((2 : ℕ) : Ordinal.{u})
    · rw [Ordinal.visibilityReplace_of_lt hlt]
      conv_rhs => rw [← Ordinal.div_add_mod o ω]
      exact (add_le_add_iff_left _).mpr ((Nat.cast_le.mpr hR).trans h1)
    · exact (Ordinal.visibilityReplace_of_le (not_lt.mp hlt) R).le

/-- Visibility replacement at the threshold `2` keeps an agreement capped at a label self-visible
at `2`. -/
theorem min_visibilityReplace_two_eq {h x y : Label.{u}} (hh : IsSelfVisible 2 h) {R : ℕ}
    (hR : R ≤ 2) (hxy : min x h = min y h) :
    min (visibilityReplace 2 R x) h = min (visibilityReplace 2 R y) h := by
  have hmono := monotone_visibilityReplace (k := 2) (i := R) hR
  have key (z : Label.{u}) :
      min (visibilityReplace 2 R z) h = min (visibilityReplace 2 R (min z h)) h := by
    rcases le_total z h with hz | hz
    · rw [min_eq_left hz]
    · rw [min_eq_right hz, hh.visibilityReplace_eq R, min_self,
        min_eq_right ((hh.visibilityReplace_eq R).symm.le.trans (hmono hz))]
  rw [key x, key y, hxy]

end Label

/-! ### The coupled-gate type with the marker at the private copy of `z₂` -/

namespace CoupledGatedExtensionCounterexample

variable (α : Ordinal.{u}) (hα : 1 < α)

/-- **The (R4) cap requests with a separate marker**: as `requestsCP`, with the marker the private
copy of `z₂ = 3` and the marker offset `R < 2`. -/
noncomputable def requestsM (R : ℕ) (hR : R < 2) :
    CapRequests (Fin ((seedCP α hα).doubledLower rfl).card) where
  cap := leftCP α hα 4
  N := 2
  R := R
  R_lt_N := hR
  Z := {rightCP α hα 1}
  F := {rightCP α hα 2}
  T := {rightCP α hα 3, rightCP α hα 4}
  ref _ := leftCP α hα 2
  off _ := 1
  marker := leftCP α hα 3

/-- The bottom class on the cells of the coupled-gate type: `⊥` exactly at the dead cells. -/
def ClassCP (s : Fin 5 → Label.{u}) : Prop := ∀ z, s z = ⊥ ↔ (z = 0 ∨ z = 1)

variable {α hα}

/-- The bottom class of a state is that of its private copy. -/
theorem inBottomClass_iff {e : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u}} :
    InBottomClass (classCellsCP α hα) (classBotCP α hα) e ↔
      ClassCP (fun z ↦ (seedCP α hα).privS rfl e z) := by
  have hl (z : Fin 5) : (seedCP α hα).lowerCell rfl (leftCP α hα z) = z :=
    Seed.lowerCell_left (I := seedCP α hα) (hLR := rfl) z
  have hinj (z z' : Fin 5) (h : leftCP α hα z = leftCP α hα z') : z = z' := by
    have := congrArg ((seedCP α hα).lowerCell rfl) h
    rwa [hl, hl] at this
  constructor
  · intro hcl z
    refine (hcl _ ⟨z, rfl⟩).trans ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rcases h with h | h
      · exact Or.inl (hinj _ _ h)
      · exact Or.inr (hinj _ _ h)
    · rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  · rintro hcl _ ⟨z, rfl⟩
    refine (hcl z).trans ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rcases h with h | h
      · exact Or.inl (hinj _ _ h)
      · exact Or.inr (hinj _ _ h)

/-- The bottom class passes along an agreement capped at a positive cap. -/
theorem classCP_of_min_eq {s t : Fin 5 → Label.{u}} {h : Label.{u}} (hh : ⊥ < h)
    (hst : ∀ z, min (s z) h = min (t z) h) (hs : ClassCP s) : ClassCP t := by
  intro z
  rw [← hs z]
  have e := hst z
  constructor
  · intro ht
    rw [ht, min_bot_left] at e
    rcases min_eq_bot.mp e with h' | h'
    · exact h'
    · exact absurd h' hh.ne'
  · intro hs'
    rw [hs', min_bot_left] at e
    rcases min_eq_bot.mp e.symm with h' | h'
    · exact h'
    · exact absurd h' hh.ne'

/-! ### Correctness with the separate marker -/

variable {R : ℕ} {hR : R < 2}

private theorem cases_grade (z : Fin 5) : cellGrade z = 1 ∨ z = 4 := by
  fin_cases z <;> simp [cellGrade]

private theorem grade_leftCP (z : Fin 5) :
    ((seedCP α hα).doubledLower rfl).toCellScheme.grade (leftCP α hα z) = cellGrade z :=
  (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
    (StageType.grade_faceCell (seedCP α hα).restrictFace_left (z : Fin (seedCP α hα).left.card))

private theorem grade_rightCP (z : Fin 5) :
    ((seedCP α hα).doubledLower rfl).toCellScheme.grade (rightCP α hα z) = cellGrade z :=
  (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
    (StageType.grade_faceCell ((seedCP α hα).restrictFace_right_left rfl)
      (z : Fin (seedCP α hα).left.card))

/-- **Symmetry at the grade `1`**: a lawful state reads the two copies of a cell of grade `1`
alike. -/
theorem sym_CP {e : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u}}
    (he : ((seedCP α hα).doubledLower rfl).rows.IsLawful e) {z : Fin 5} (hz : cellGrade z = 1) :
    e (rightCP α hα z) = e (leftCP α hα z) :=
  Seed.eq_of_isLawfulBelow_lower (isLegal_P α hα) (he.isLawfulBelow _)
    ((grade_rightCP z).trans hz) ((grade_leftCP z).trans hz)
    ((Seed.lowerCell_right (I := seedCP α hα) (hLR := rfl) z).trans
      (Seed.lowerCell_left (I := seedCP α hα) (hLR := rfl) z).symm)

/-- A lawful state is self-visible at `1` at the copies of the cells of grade `1`. -/
private theorem isSelfVisible_leftCP {e : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u}}
    (he : ((seedCP α hα).doubledLower rfl).rows.IsLawful e) {z : Fin 5} (hz : cellGrade z = 1) :
    IsSelfVisible 1 (e (leftCP α hα z)) :=
  ((grade_leftCP z).trans hz) ▸ he.orderly (leftCP α hα z)

/-- **Correctness from the reading of the full cell**: a lawful state reading the donor copy of the
full cell at least as the replaced marker capped at the cap is correct (the requests at the cells
of grade `1` hold by symmetry). -/
theorem isCorrect_requestsM {e : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u}}
    (he : ((seedCP α hα).doubledLower rfl).rows.IsLawful e)
    (h4 : min (visibilityReplace 2 R (e (leftCP α hα 3))) (e (leftCP α hα 4)) ≤
      e (rightCP α hα 4)) : (requestsM α hα R hR).IsCorrect e where
  eq_bot z hz := by
    have hz' : z = rightCP α hα 1 := hz
    subst hz'
    change min (e (rightCP α hα 1)) (e (leftCP α hα 4)) = ⊥
    have h1 : e (leftCP α hα 1) = ⊥ :=
      (seedCP α hα).eq_bot_privS_of_row_self rfl (z := (1 : Fin 5)) rfl he
    rw [sym_CP he (z := 1) rfl, h1, min_bot_left]
  eq_refValue f hf := by
    have hf' : f = rightCP α hα 2 := hf
    subst hf'
    change min (e (rightCP α hα 2)) (e (leftCP α hα 4)) =
      min (visibilityReplace 2 1 (e (leftCP α hα 2))) (e (leftCP α hα 4))
    rw [sym_CP he (z := 2) rfl, Label.visibilityReplace_two_one (isSelfVisible_leftCP he rfl)]
  markerValue_le y hy := by
    change min (visibilityReplace 2 R (e (leftCP α hα 3))) (e (leftCP α hα 4)) ≤
      min (e y) (e (leftCP α hα 4))
    rcases hy with rfl | hy
    · rw [sym_CP he (z := 3) rfl]
      exact min_le_min (Label.visibilityReplace_two_le (isSelfVisible_leftCP he rfl) (by omega))
        le_rfl
    · have hy' : y = rightCP α hα 4 := hy
      subst hy'
      exact le_min h4 (min_le_right _ _)

/-- Correctness gives the reading of the full cell. -/
theorem le_of_isCorrect_requestsM {e : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u}}
    (hc : (requestsM α hα R hR).IsCorrect e) :
    min (visibilityReplace 2 R (e (leftCP α hα 3))) (e (leftCP α hα 4)) ≤ e (rightCP α hα 4) :=
  (hc.markerValue_le _ (Or.inr rfl)).trans (min_le_left _ _)

private theorem grade_le_two_CP (d : Fin ((seedCP α hα).doubledLower rfl).card) :
    ((seedCP α hα).doubledLower rfl).toCellScheme.grade d ≤ 2 := by
  induction d using Fin.addCases with
  | left a =>
    rw [Scheme.appendFullCellsScheme_grade_castAdd]
    exact Nat.lt_succ_iff.mp ((seedCP α hα).grade_lt a)
  | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega

/-- **The orbit code of an admitted state is admitted.** -/
theorem admits_orbitCode {W : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u}}
    (hadm : (requestsM α hα R hR).Admits (classCellsCP α hα) (classBotCP α hα) W) :
    (requestsM α hα R hR).Admits (classCellsCP α hα) (classBotCP α hα)
      (orbitCode 2 (((seedCP α hα).doubledLower rfl).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsp : ((seedCP α hα).doubledLower rfl).toCellScheme.splice 2 (fun _ ↦ ⊥) W = W :=
    funext fun d ↦ CellScheme.splice_of_le (grade_le_two_CP d)
  rw [hsp]
  have hcode : orbitCode 2 W = orbitMap 2 W ∘ W := funext fun d ↦ orbitCode_apply d
  intro hcl
  have hcl' : InBottomClass (classCellsCP α hα) (classBotCP α hα) W := by
    intro d hd
    rw [← hcl d hd, hcode, Function.comp_apply, orbitMap_eq_bot_iff]
  rw [hcode]
  exact (hadm hcl').comp (isWitness_orbitMap 2 W) le_rfl fun _ _ ↦ by
    change 1 ≤ 2
    omega

/-- A state outside the bottom class is admitted. -/
theorem admits_of_not {W : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u}}
    (hn : ¬ ClassCP (fun z ↦ (seedCP α hα).privS rfl W z)) :
    (requestsM α hα R hR).Admits (classCellsCP α hα) (classBotCP α hα) W :=
  fun hcl ↦ absurd (inBottomClass_iff.mp hcl) hn

/-- A lawful state agrees with its private copy at the copies of full scope. -/
private theorem natAdd_eq_left {e : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u}}
    (he : ((seedCP α hα).doubledLower rfl).rows.IsLawful e) (i : Fin ((seedCP α hα).nFull 1)) :
    e (Fin.natAdd _ i) =
      e (Fin.castAdd _ (StageType.faceCell (seedCP α hα).restrictFace_left
        ((seedCP α hα).left.toScheme.fullCell 1 i))) := by
  have hg1 : (seedCP α hα).left.toCellScheme.grade ((seedCP α hα).left.toScheme.fullCell 1 i) =
      1 := congrArg Prod.snd (Scheme.gradedIndex_fullCell 1 i)
  refine Seed.eq_of_isLawfulBelow_lower (isLegal_P α hα) (he.isLawfulBelow _)
    (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i)
    ((Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
      ((StageType.grade_faceCell _ _).trans hg1))
    ((Seed.lowerCell_natAdd (I := seedCP α hα) (hLR := rfl) i).trans
      (Seed.lowerCell_left (I := seedCP α hα) (hLR := rfl) _).symm)

/-! ### The lift provisions with the separate marker -/

private theorem min_eq_of_min_eq_lt {m ma h : Label.{u}} (hm : min m h = min ma h)
    (hlt : h < m) : h ≤ ma := by
  rw [min_eq_right hlt.le] at hm
  exact min_eq_right_iff.mp hm.symm

/-- **The lift provision at the cap `⊥` from the private coatom**: the symmetric fill. -/
theorem botProvisionM_left {f : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u}}
    (hf : ((seedCP α hα).doubledLower rfl).rows.IsLawfulBelow (univ.erase (Fin.last 2), 2)
      (fun d ↦ f d)) :
    ∃ W : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u},
      ((seedCP α hα).doubledLower rfl).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2)
        (fun d ↦ W d) ∧
      (∀ d ∈ ((seedCP α hα).doubledLower rfl).toCellScheme.below (univ.erase (Fin.last 2), 2),
        W d = f d) ∧
      (requestsM α hα R hR).Admits (classCellsCP α hα) (classBotCP α hα)
        (orbitCode 2 (((seedCP α hα).doubledLower rfl).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsL := Seed.isLawful_privS hf
  obtain ⟨g, hg, hgL, hgR, -⟩ := Seed.exists_glueSym (isLegal_P α hα) hsL hsL fun _ _ ↦ rfl
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := Seed.exists_left_of_mem_belowS hd
    exact congrFun hgL z
  · refine admits_orbitCode (isCorrect_requestsM hg ?_).admits
    have e1 : g (rightCP α hα 4) = g (leftCP α hα 4) :=
      (congrFun hgR (4 : Fin 5)).trans (congrFun hgL (4 : Fin 5)).symm
    rw [e1]
    exact min_le_right _ _

theorem leftCP_mem_below (z : Fin 5) :
    leftCP α hα z ∈ ((seedCP α hα).doubledLower rfl).toCellScheme.below
      (univ.erase (Fin.last 2), 2) :=
  Seed.left_mem_belowS (I := seedCP α hα) (hLR := rfl) z

theorem rightCP_mem_below (z : Fin 5) :
    rightCP α hα z ∈ ((seedCP α hα).doubledLower rfl).toCellScheme.below
      (univ.erase (Fin.castSucc (Fin.last 1)), 2) :=
  Seed.right_mem_belowS (I := seedCP α hα) (hLR := rfl) z

/-- **The donor copy of the fill at a positive cap.**  It is the prescription `sL` when `sL` is in
the bottom class and reads the replaced marker above `h`; otherwise the lift of `T` from
`(univ, 1)` to `(univ, 2)` of `sL` at the cells of grade `1` against the donor copy `eR` of the
entry. -/
theorem exists_donorFill (hR2 : R ≤ 2) {h : Label.{u}} (hh : IsSelfVisible 2 h) (hbh : ⊥ < h)
    {sL eL eR : Fin 5 → Label.{u}} (hsL : (P α hα).rows.IsLawful sL)
    (heR : (P α hα).rows.IsLawful eR) (hagL : ∀ z, min (sL z) h = min (eL z) h)
    (hsym : ∀ z, cellGrade z = 1 → eR z = eL z)
    (hA : ClassCP eL → min (visibilityReplace 2 R (eL 3)) (eL 4) ≤ eR 4) :
    ∃ D : Fin 5 → Label.{u}, (P α hα).rows.IsLawful D ∧
      (∀ z, cellGrade z = 1 → D z = sL z) ∧ (∀ z, min (D z) h = min (eR z) h) ∧
      (ClassCP sL → min (visibilityReplace 2 R (sL 3)) (sL 4) ≤ D 4) := by
  have hm : min (min (visibilityReplace 2 R (sL 3)) (sL 4)) h =
      min (min (visibilityReplace 2 R (eL 3)) (eL 4)) h := by
    rw [inf_inf_distrib_right, inf_inf_distrib_right (visibilityReplace 2 R (eL 3)),
      Label.min_visibilityReplace_two_eq hh hR2 (hagL 3), hagL 4]
  obtain ⟨r, hr, hrsL, hreR⟩ : ∃ r : Fin 5 → Label.{u}, (P α hα).rows.IsLawful r ∧
      (∀ z, cellGrade z = 1 → r z = sL z) ∧ ∀ z, min (r z) h = min (eR z) h :=
    StageType.exists_lift_one_two (isLegal_P α hα) hsL heR hh
      fun z hz ↦ (hagL z).trans (by rw [hsym z hz])
  by_cases hc : ClassCP sL ∧ h < min (visibilityReplace 2 R (sL 3)) (sL 4)
  · have hcorr := hA (classCP_of_min_eq hbh hagL hc.1)
    have hma := min_eq_of_min_eq_lt hm hc.2
    refine ⟨sL, hsL, fun _ _ ↦ rfl, fun z ↦ ?_, fun _ ↦ min_le_right _ _⟩
    rcases cases_grade z with hz | rfl
    · rw [hagL z, hsym z hz]
    · rw [min_eq_right (hc.2.le.trans (min_le_right _ _)), min_eq_right (hma.trans hcorr)]
  · refine ⟨r, hr, hrsL, hreR, fun hcl ↦ ?_⟩
    have hle : min (visibilityReplace 2 R (sL 3)) (sL 4) ≤ h :=
      not_lt.mp fun hlt ↦ hc ⟨hcl, hlt⟩
    calc min (visibilityReplace 2 R (sL 3)) (sL 4)
        = min (min (visibilityReplace 2 R (sL 3)) (sL 4)) h := (min_eq_left hle).symm
      _ = min (min (visibilityReplace 2 R (eL 3)) (eL 4)) h := hm
      _ ≤ min (eR 4) h := min_le_min_right _ (hA (classCP_of_min_eq hbh hagL hcl))
      _ = min (r 4) h := (hreR 4).symm
      _ ≤ r 4 := min_le_left _ _

/-- **The private copy of the fill at a positive cap.**  It is the prescription `fR` when the
entry's private copy `eL` is in the bottom class and the replaced marker of the lift of `T` lies
above `h`; otherwise that lift, of `fR` at the cells of grade `1` against `eL`. -/
theorem exists_privateFill (hR2 : R ≤ 2) {h : Label.{u}} (hh : IsSelfVisible 2 h) (hbh : ⊥ < h)
    {fR eL eR : Fin 5 → Label.{u}} (hfR : (P α hα).rows.IsLawful fR)
    (heL : (P α hα).rows.IsLawful eL) (hagR : ∀ z, min (fR z) h = min (eR z) h)
    (hsym : ∀ z, cellGrade z = 1 → eR z = eL z)
    (hA : ClassCP eL → min (visibilityReplace 2 R (eL 3)) (eL 4) ≤ eR 4) :
    ∃ L : Fin 5 → Label.{u}, (P α hα).rows.IsLawful L ∧
      (∀ z, cellGrade z = 1 → fR z = L z) ∧ (∀ z, min (L z) h = min (eL z) h) ∧
      (ClassCP L → min (visibilityReplace 2 R (L 3)) (L 4) ≤ fR 4) := by
  obtain ⟨r, hr, hrfR, hreL⟩ : ∃ r : Fin 5 → Label.{u}, (P α hα).rows.IsLawful r ∧
      (∀ z, cellGrade z = 1 → r z = fR z) ∧ ∀ z, min (r z) h = min (eL z) h :=
    StageType.exists_lift_one_two (isLegal_P α hα) hfR heL hh
      fun z hz ↦ (hagR z).trans (by rw [hsym z hz])
  have hm : min (min (visibilityReplace 2 R (r 3)) (r 4)) h =
      min (min (visibilityReplace 2 R (eL 3)) (eL 4)) h := by
    rw [inf_inf_distrib_right, inf_inf_distrib_right (visibilityReplace 2 R (eL 3)),
      Label.min_visibilityReplace_two_eq hh hR2 (hreL 3), hreL 4]
  by_cases hc : ClassCP eL ∧ h < min (visibilityReplace 2 R (r 3)) (r 4)
  · have hcorr := hA hc.1
    have hma := min_eq_of_min_eq_lt hm hc.2
    refine ⟨fR, hfR, fun _ _ ↦ rfl, fun z ↦ ?_, fun _ ↦ min_le_right _ _⟩
    rcases cases_grade z with hz | rfl
    · rw [hagR z, hsym z hz]
    · rw [hagR 4, min_eq_right (hma.trans hcorr), ← hreL 4,
        min_eq_right (hc.2.le.trans (min_le_right _ _))]
  · refine ⟨r, hr, fun z hz ↦ (hrfR z hz).symm, hreL, fun hcl ↦ ?_⟩
    have hclE := classCP_of_min_eq hbh hreL hcl
    have hle : min (visibilityReplace 2 R (r 3)) (r 4) ≤ h :=
      not_lt.mp fun hlt ↦ hc ⟨hclE, hlt⟩
    calc min (visibilityReplace 2 R (r 3)) (r 4)
        = min (min (visibilityReplace 2 R (r 3)) (r 4)) h := (min_eq_left hle).symm
      _ = min (min (visibilityReplace 2 R (eL 3)) (eL 4)) h := hm
      _ ≤ min (eR 4) h := min_le_min_right _ (hA hclE)
      _ = min (fR 4) h := (hagR 4).symm
      _ ≤ fR 4 := min_le_left _ _

/-- **The glued fill at a positive cap**: gluing a private copy `sL` and a donor copy `D` that
agree at the cells of grade `1`, each agreeing with the entry below `h`, and with the donor copy
reading the replaced marker of `sL` when `sL` is in the bottom class. -/
theorem exists_capGlue {h : Label.{u}} {a : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u}}
    (ha : ((seedCP α hα).doubledLower rfl).rows.IsLawful a) {sL D : Fin 5 → Label.{u}}
    (hsL : (P α hα).rows.IsLawful sL) (hD : (P α hα).rows.IsLawful D)
    (hDag : ∀ z, cellGrade z = 1 → D z = sL z)
    (hLa : ∀ z, min (sL z) h = min (a (leftCP α hα z)) h)
    (hDa : ∀ z, min (D z) h = min (a (rightCP α hα z)) h)
    (hT : ClassCP sL → min (visibilityReplace 2 R (sL 3)) (sL 4) ≤ D 4) :
    ∃ g : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u},
      ((seedCP α hα).doubledLower rfl).rows.IsLawful g ∧
      (seedCP α hα).privS rfl g = sL ∧ (seedCP α hα).donS rfl g = D ∧
      (∀ d, min (g d) h = min (a d) h) ∧
      (requestsM α hα R hR).Admits (classCellsCP α hα) (classBotCP α hα)
        (orbitCode 2 (((seedCP α hα).doubledLower rfl).toCellScheme.splice 2 (fun _ ↦ ⊥) g)) := by
  obtain ⟨g, hg, hgL, hgR, hgN⟩ :=
    Seed.exists_glueSym (I := seedCP α hα) (hLR := rfl) (isLegal_P α hα) hsL hD hDag
  refine ⟨g, hg, hgL, hgR, fun d ↦ ?_, ?_⟩
  · induction d using Fin.addCases with
    | right i =>
      rw [hgN, natAdd_eq_left ha i]
      exact hLa _
    | left e =>
      rcases (seedCP α hα).eq_faceCell_or rfl e with he | he
      · rw [← he]
        exact (congrArg (min · h) (congrFun hgL _)).trans (hLa _)
      · rw [← he]
        exact (congrArg (min · h) (congrFun hgR _)).trans (hDa _)
  · by_cases hcl : ClassCP sL
    · refine admits_orbitCode (isCorrect_requestsM hg ?_).admits
      have e3 : g (leftCP α hα 3) = sL 3 := congrFun hgL (3 : Fin 5)
      have e4 : g (leftCP α hα 4) = sL 4 := congrFun hgL (4 : Fin 5)
      have e4' : g (rightCP α hα 4) = D 4 := congrFun hgR (4 : Fin 5)
      rw [e3, e4, e4']
      exact hT hcl
    · exact admits_orbitCode (admits_of_not (by rw [hgL]; exact hcl))

/-- The (R4) request at the full cell, for an admitted entry in the bottom class. -/
theorem le_of_admits {a : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u}}
    (hA : (requestsM α hα R hR).Admits (classCellsCP α hα) (classBotCP α hα) a)
    (hc : ClassCP fun z ↦ a (leftCP α hα z)) :
    min (visibilityReplace 2 R (a (leftCP α hα 3))) (a (leftCP α hα 4)) ≤
      a (rightCP α hα 4) :=
  le_of_isCorrect_requestsM (hA (inBottomClass_iff.mpr hc))

/-- **The lift provision at a positive cap from the private coatom**: the private copy of the
prescription glued to `exists_donorFill`. -/
theorem capProvisionM_left {h : Label.{u}} (hh : IsSelfVisible 2 h) (hbh : ⊥ < h)
    {a : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u}}
    (ha : ((seedCP α hα).doubledLower rfl).rows.IsLawful a)
    (hA : (requestsM α hα R hR).Admits (classCellsCP α hα) (classBotCP α hα) a)
    {f : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u}}
    (hf : ((seedCP α hα).doubledLower rfl).rows.IsLawfulBelow (univ.erase (Fin.last 2), 2)
      (fun d ↦ f d))
    (hfa : ∀ d ∈ ((seedCP α hα).doubledLower rfl).toCellScheme.below
      (univ.erase (Fin.last 2), 2), min (f d) h = min (a d) h) :
    ∃ W : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u},
      ((seedCP α hα).doubledLower rfl).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2)
        (fun d ↦ W d) ∧
      (∀ d ∈ ((seedCP α hα).doubledLower rfl).toCellScheme.below (univ.erase (Fin.last 2), 2),
        W d = f d) ∧
      (∀ d, ((seedCP α hα).doubledLower rfl).toCellScheme.grade d ≤ 2 →
        min (W d) h = min (a d) h) ∧
      (requestsM α hα R hR).Admits (classCellsCP α hα) (classBotCP α hα)
        (orbitCode 2 (((seedCP α hα).doubledLower rfl).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsL : (P α hα).rows.IsLawful fun z ↦ f (leftCP α hα z) := Seed.isLawful_privS hf
  have heR : (P α hα).rows.IsLawful fun z ↦ a (rightCP α hα z) :=
    Seed.isLawful_donS (ha.isLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2))
  obtain ⟨D, hD, hDag, hDa, hDT⟩ := exists_donorFill (R := R) (by omega) hh hbh
    (sL := fun z ↦ f (leftCP α hα z)) (eL := fun z ↦ a (leftCP α hα z))
    (eR := fun z ↦ a (rightCP α hα z)) hsL heR (fun z ↦ hfa _ (leftCP_mem_below z))
    (fun z hz ↦ sym_CP ha hz) (le_of_admits hA)
  obtain ⟨g, hg, hgL, -, hga, hgA⟩ := exists_capGlue (R := R) (hR := hR) ha hsL hD hDag
    (fun z ↦ hfa _ (leftCP_mem_below z)) hDa hDT
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_, fun d _ ↦ hga d, hgA⟩
  obtain ⟨z, rfl⟩ := Seed.exists_left_of_mem_belowS hd
  exact congrFun hgL z

/-- **The lift provision at the cap `⊥` from the donor coatom**: the symmetric fill. -/
theorem botProvisionM_right {f : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u}}
    (hf : ((seedCP α hα).doubledLower rfl).rows.IsLawfulBelow
      (univ.erase (Fin.castSucc (Fin.last 1)), 2) (fun d ↦ f d)) :
    ∃ W : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u},
      ((seedCP α hα).doubledLower rfl).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2)
        (fun d ↦ W d) ∧
      (∀ d ∈ ((seedCP α hα).doubledLower rfl).toCellScheme.below
        (univ.erase (Fin.castSucc (Fin.last 1)), 2), W d = f d) ∧
      (requestsM α hα R hR).Admits (classCellsCP α hα) (classBotCP α hα)
        (orbitCode 2 (((seedCP α hα).doubledLower rfl).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsR := Seed.isLawful_donS hf
  obtain ⟨g, hg, hgL, hgR, -⟩ := Seed.exists_glueSym (isLegal_P α hα) hsR hsR fun _ _ ↦ rfl
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := Seed.exists_right_of_mem_belowS hd
    exact congrFun hgR z
  · refine admits_orbitCode (isCorrect_requestsM hg ?_).admits
    have e1 : g (rightCP α hα 4) = g (leftCP α hα 4) :=
      (congrFun hgR (4 : Fin 5)).trans (congrFun hgL (4 : Fin 5)).symm
    rw [e1]
    exact min_le_right _ _

/-- **The lift provision at a positive cap from the donor coatom**: `exists_privateFill` glued to
the donor copy of the prescription. -/
theorem capProvisionM_right {h : Label.{u}} (hh : IsSelfVisible 2 h) (hbh : ⊥ < h)
    {a : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u}}
    (ha : ((seedCP α hα).doubledLower rfl).rows.IsLawful a)
    (hA : (requestsM α hα R hR).Admits (classCellsCP α hα) (classBotCP α hα) a)
    {f : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u}}
    (hf : ((seedCP α hα).doubledLower rfl).rows.IsLawfulBelow
      (univ.erase (Fin.castSucc (Fin.last 1)), 2) (fun d ↦ f d))
    (hfa : ∀ d ∈ ((seedCP α hα).doubledLower rfl).toCellScheme.below
      (univ.erase (Fin.castSucc (Fin.last 1)), 2), min (f d) h = min (a d) h) :
    ∃ W : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u},
      ((seedCP α hα).doubledLower rfl).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2)
        (fun d ↦ W d) ∧
      (∀ d ∈ ((seedCP α hα).doubledLower rfl).toCellScheme.below
        (univ.erase (Fin.castSucc (Fin.last 1)), 2), W d = f d) ∧
      (∀ d, ((seedCP α hα).doubledLower rfl).toCellScheme.grade d ≤ 2 →
        min (W d) h = min (a d) h) ∧
      (requestsM α hα R hR).Admits (classCellsCP α hα) (classBotCP α hα)
        (orbitCode 2 (((seedCP α hα).doubledLower rfl).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hfR : (P α hα).rows.IsLawful fun z ↦ f (rightCP α hα z) := Seed.isLawful_donS hf
  have heL : (P α hα).rows.IsLawful fun z ↦ a (leftCP α hα z) :=
    Seed.isLawful_privS (ha.isLawfulBelow (univ.erase (Fin.last 2), 2))
  obtain ⟨L, hL, hLag, hLa, hLT⟩ := exists_privateFill (R := R) (by omega) hh hbh
    (fR := fun z ↦ f (rightCP α hα z)) (eL := fun z ↦ a (leftCP α hα z))
    (eR := fun z ↦ a (rightCP α hα z)) hfR heL (fun z ↦ hfa _ (rightCP_mem_below z))
    (fun z hz ↦ sym_CP ha hz) (le_of_admits hA)
  obtain ⟨g, hg, -, hgR, hga, hgA⟩ := exists_capGlue (R := R) (hR := hR) ha hL hfR hLag
    hLa (fun z ↦ hfa _ (rightCP_mem_below z)) hLT
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_, fun d _ ↦ hga d, hgA⟩
  obtain ⟨z, rfl⟩ := Seed.exists_right_of_mem_belowS hd
  exact congrFun hgR z

/-! ### Legality of the admitted layer with the separate marker -/

private theorem erase_ne_univM (x : Fin 3) : univ.erase x ≠ univ :=
  fun he ↦ Finset.notMem_erase x univ (he.symm ▸ mem_univ x)

/-- **The lift from the private coatom into the admitted layer** with the separate marker. -/
theorem cappedLift_admittedLayerM_left :
    (((seedCP α hα).doubledLower rfl).admittedFieldLayer 2
      ((requestsM α hα R hR).Admits (classCellsCP α hα) (classBotCP α hα))
        ((seedCP α hα).not_univ_two_le_doubledLower rfl)).rows.CappedLift
      (X := (univ.erase (Fin.last 2), 2)) (Y := ((univ : Finset (Fin 3)), 2))
        ⟨erase_subset _ _, le_rfl⟩ :=
  Scheme.cappedLift_admittedFieldLayer (j := 1)
    (hS := (seedCP α hα).not_univ_two_le_doubledLower rfl)
    ((seedCP α hα).isConsistent_doubledLower rfl (isLegal_P α hα))
    (CapRequests.admits_bot _ _ _) (erase_ne_univM _)
    ⟨_, Seed.gradedIndex_left_cap (I := seedCP α hα) (hLR := rfl) (b := (4 : Fin 5)) rfl⟩
    (Seed.cappedLift_doubledLower_left (isLegal_P α hα))
    (fun _ hf ↦ botProvisionM_left hf)
    (fun _ hh _ hbh _ ha hA _ hf hfa ↦ capProvisionM_left hh hbh ha hA hf hfa)

/-- **The lift from the donor coatom into the admitted layer** with the separate marker. -/
theorem cappedLift_admittedLayerM_right :
    (((seedCP α hα).doubledLower rfl).admittedFieldLayer 2
      ((requestsM α hα R hR).Admits (classCellsCP α hα) (classBotCP α hα))
        ((seedCP α hα).not_univ_two_le_doubledLower rfl)).rows.CappedLift
      (X := (univ.erase (Fin.castSucc (Fin.last 1)), 2)) (Y := ((univ : Finset (Fin 3)), 2))
        ⟨erase_subset _ _, le_rfl⟩ :=
  Scheme.cappedLift_admittedFieldLayer (j := 1)
    (hS := (seedCP α hα).not_univ_two_le_doubledLower rfl)
    ((seedCP α hα).isConsistent_doubledLower rfl (isLegal_P α hα))
    (CapRequests.admits_bot _ _ _) (erase_ne_univM _)
    ⟨_, Seed.gradedIndex_right_cap (I := seedCP α hα) (hLR := rfl) (b := (4 : Fin 5)) rfl⟩
    (Seed.cappedLift_doubledLower_right (isLegal_P α hα))
    (fun _ hf ↦ botProvisionM_right hf)
    (fun _ hh _ hbh _ ha hA _ hf hfa ↦ capProvisionM_right hh hbh ha hA hf hfa)

variable (α hα R hR) in
/-- **The admitted completion at the coupled-gate type with the separate marker.**  For the (R4)
cap requests of the self-seed of `P α` with the cap the private copy of the full cell `C` and the
marker the private copy of `z₂`, at any offset `R < 2`, the admitted layer at the grade `2` over
the doubled lower layer is legal below the full grade. -/
theorem isLegalBelowFullGrade_admittedLayerM :
    (((seedCP α hα).doubledLower rfl).admittedFieldLayer 2
      ((requestsM α hα R hR).Admits (classCellsCP α hα) (classBotCP α hα))
        ((seedCP α hα).not_univ_two_le_doubledLower rfl)).IsLegalBelowFullGrade :=
  (seedCP α hα).isLegalBelowFullGrade_admittedDoubledLower rfl (isLegal_P α hα)
    (CapRequests.admits_bot _ _ _)
    ((seedCP α hα).isBountiful_admittedDoubledLower rfl
      (Seed.cappedLift_doubledLower_left (isLegal_P α hα))
      (Seed.cappedLift_doubledLower_right (isLegal_P α hα))
      cappedLift_admittedLayerM_left cappedLift_admittedLayerM_right)

/-! ### The marker survives the obstruction -/

private theorem omegaAdd_one_lt_two' : omegaAdd.{u} 1 < omegaAdd 2 := by
  unfold omegaAdd
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
    ((add_lt_add_iff_left _).mpr
      ((Nat.cast_lt (α := Ordinal.{u})).mpr (by norm_num : (1 : ℕ) < 2))))

variable (α hα R hR) in
/-- **The hypothesis of the obstruction fails for the separate marker**
(`Seed.not_isBountiful_admittedDoubledLower`, at the cap `b = C` and `y = z₂`, prescription the
row of `C`).  The pullback of the row of the full cell, `(⊥, ⊥, 1, ω + 1, ω + 2)`, to the doubled
lower layer is lawful and admitted, is nonzero at the private copy wherever the row is, and reads
the private copy of `C` strictly above the donor copy of `z₂`. -/
theorem exists_admits_donS_lt_privS :
    ∃ e : Fin ((seedCP α hα).doubledLower rfl).card → Label.{u},
      ((seedCP α hα).doubledLower rfl).rows.IsLawful e ∧
      (requestsM α hα R hR).Admits (classCellsCP α hα) (classBotCP α hα) e ∧
      (∀ z, (P α hα).rowAt (4 : Fin 5) z ≠ ⊥ → e (leftCP α hα z) ≠ ⊥) ∧
      e (rightCP α hα 3) < e (leftCP α hα 4) := by
  have hg4 : (P α hα).toCellScheme.gradedIndex (4 : Fin 5) = ((univ : Finset (Fin 2)), 2) := rfl
  have hs := Scheme.isLawful_rowAt (isLegal_P α hα).isConsistent hg4
  have hrow (z : Fin 5) : (P α hα).rowAt (4 : Fin 5) z = code z := by
    rw [Scheme.rowAt_of_mem (show z ∈ (P α hα).toCellScheme.below
      ((P α hα).toCellScheme.gradedIndex (4 : Fin 5)) by
        rw [hg4]; exact ⟨subset_univ _, (P α hα).grade_le z⟩)]
    fin_cases z <;> rfl
  have he := ((seedCP α hα).isDoubling_doubledLower rfl).isLawful_comp hs
  have hL (z : Fin 5) : ((P α hα).rowAt (4 : Fin 5) ∘ (seedCP α hα).lowerCell rfl)
      (leftCP α hα z) = (P α hα).rowAt (4 : Fin 5) z :=
    congrArg ((P α hα).rowAt (4 : Fin 5)) (Seed.lowerCell_left (I := seedCP α hα) (hLR := rfl) z)
  have hR (z : Fin 5) : ((P α hα).rowAt (4 : Fin 5) ∘ (seedCP α hα).lowerCell rfl)
      (rightCP α hα z) = (P α hα).rowAt (4 : Fin 5) z :=
    congrArg ((P α hα).rowAt (4 : Fin 5)) (Seed.lowerCell_right (I := seedCP α hα) (hLR := rfl) z)
  refine ⟨_, he, (isCorrect_requestsM he ?_).admits, fun z hz ↦ (hL z).trans_ne hz, ?_⟩
  · exact (min_le_right _ _).trans_eq ((hL 4).trans (hR 4).symm)
  · calc _ = (P α hα).rowAt (4 : Fin 5) (3 : Fin 5) := hR 3
      _ = omegaAdd 1 := hrow 3
      _ < omegaAdd 2 := omegaAdd_one_lt_two'
      _ = (P α hα).rowAt (4 : Fin 5) (4 : Fin 5) := (hrow 4).symm
      _ = _ := (hL 4).symm

end CoupledGatedExtensionCounterexample



end VaughtConjecture
