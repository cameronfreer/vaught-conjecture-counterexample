/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryDonorBlock
import VaughtConjecture.Extension.AdmittedFieldLayerCells

/-!
# Both coatoms prescribed at grade one: the lift on the canonical lower layer

Roadmap, Layer 3, 3.1, (R6) and 3.3 (the (R4) cap); the admitted layer with a donor of
`VaughtConjecture.Continuation.StableRecoveryDonorBlock`, with live cells of grade `1` on both
coatoms.

Reading back a label `μ + 1` of a cell of `D` needs a reference of grade `1` in `T` that is not
dead (`StageType.visibilityReplace_ne_one`), so both coatoms are live at grade `1`.  The lift at
grade `1` must then be prescribed on both coatoms at once.

* **Root agreement** (`Seed.RootAgree sT sD`): labellings of `T` and `D` agreeing at the cells of
  the common face.
* **Gluing** (`Seed.exists_isLawful_glue₂`): two lawful labellings with root agreement glue to a
  lawful labelling of the amalgam; **the extension at the cap `⊥`**
  (`Seed.exists_isLawful_lower_two`): it extends through the lower layer.
* **The two-coatom lift** (`Seed.HasTwoCoatomLift I`, a hypothesis): at every positive cap `h`
  self-visible at `2`, lawful `sT`, `sD` with root agreement, both agreeing capped at `h` with the
  copies of a lawful ambient `a` of the lower layer, extend to a lawful labelling of the lower
  layer agreeing with `a` capped at `h` everywhere, the cells of the field layer at grade `1`
  included.  The one-coatom lift `Seed.cappedLift_lowerFieldLayer` fixes one coatom literally and
  the other only capped at `h`; the two-coatom lift is not derived from it here.
* **The lift from the common face** (`Seed.exists_lift_root`): within a coatom type, a labelling
  of the common face extends to a lawful labelling agreeing capped with a lawful ambient.
* `Seed.isLegalBelowFullGrade_donorLayer_live`: with `T` live at grade `1`, legality of the
  admitted layer with a donor from the raise and the capped exact lift **with root agreement** and
  the two-coatom lift.  The provisions at the cap `⊥` need no hypothesis beyond the raise
  (`Seed.exists_isLawful_lower_two`).
* **Reading back a block label** (`Seed.donCell_eq_of_isCorrect`): under the cap `⊤` a correct
  state reads the copy of a cell of `D` labelled in a block as the replacement at the offset `1` of
  the copy of its reference; with a live reference labelled `1` this is `1`.
* **A recovered block label** (`CoupledGatedExtensionCounterexample.recovers_z₁_capSepCP`): over
  the doubled lower layer of the coupled-gate type with itself (its copies of full scope at grade
  `1` read the two copies of a cell alike, tying the donor copy of `z₁` to its reference, the
  private copy of `z₁`), every stage type on the marked coface with face `T` has the donor copy of
  `z₁` labelled `1`: the label `1` of `z₁` is recovered.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

namespace Seed

variable {α : Ordinal.{u}} {I : Seed.{u} α 1} {c : I.DonorCap}

variable (I) in
/-- **Root agreement**: labellings of `T` and `D` agreeing at the cells of the common face. -/
def RootAgree (sT : Fin I.left.card → Label.{u}) (sD : Fin I.right.card → Label.{u}) : Prop :=
  ∀ zT zD, StageType.faceCell I.restrictFace_left zT = StageType.faceCell I.restrictFace_right zD →
    sT zT = sD zD

theorem faceCell_injective' {f : Fin 2 ↪ Fin 3} {E : StageType.{u} α 2}
    (hE : restrictFace f I.amalgam = some E) :
    Function.Injective (StageType.faceCell hE) :=
  I.amalgam.toScheme.faceCell_injective (StageType.comap_toScheme_of_restrictFace hE)

/-- An amalgam labelling from a labelling of a coatom type (`⊥` off the coatom). -/
theorem exists_amalgam_of_coatom {f : Fin 2 ↪ Fin 3} {E : StageType.{u} α 2}
    (hE : restrictFace f I.amalgam = some E) {y : Fin 3} (hfy : univ.map f = univ.erase y)
    {s : Fin E.card → Label.{u}} (hs : E.rows.IsLawful s) :
    ∃ x : Fin I.amalgam.card → Label.{u},
      I.amalgam.rows.IsLawfulBelow (univ.erase y, 2) (fun d ↦ x d) ∧
        ∀ i, x (StageType.faceCell hE i) = s i := by
  classical
  set x : Fin I.amalgam.card → Label.{u} := fun d ↦
    if hd : ∃ i, StageType.faceCell hE i = d then s hd.choose else ⊥ with hxdef
  have hx (i : Fin E.card) : x (StageType.faceCell hE i) = s i := by
    have hd : ∃ j, StageType.faceCell hE j = StageType.faceCell hE i := ⟨i, rfl⟩
    rw [hxdef]
    exact (dite_eq_left hd).trans (congrArg s (faceCell_injective' hE hd.choose_spec))
  refine ⟨x, ?_, hx⟩
  have hpair : ((univ.erase y, 2) : Finset (Fin 3) × ℕ) =
      Prod.map (Finset.map f) id ((univ : Finset (Fin 2)), 2) := by
    simp only [Prod.map, id, hfy]
  rw [hpair]
  refine (Scheme.isLawfulBelow_faceCell_iff (StageType.comap_toScheme_of_restrictFace hE)
    (univ, 2) (fun d ↦ x d)).mp ?_
  convert hs.isLawfulBelow ((univ : Finset (Fin 2)), 2) using 1
  exact funext fun i ↦ hx i.1

open Classical in
/-- **Gluing a labelling of `T` and one of `D`** agreeing at the common face. -/
theorem exists_isLawful_glue₂ {sT : Fin I.left.card → Label.{u}}
    {sD : Fin I.right.card → Label.{u}} (hsT : I.left.rows.IsLawful sT)
    (hsD : I.right.rows.IsLawful sD) (hroot : I.RootAgree sT sD) :
    ∃ w : Fin I.amalgam.card → Label.{u}, I.amalgam.rows.IsLawful w ∧
      (∀ z, w (StageType.faceCell I.restrictFace_left z) = sT z) ∧
      ∀ z, w (StageType.faceCell I.restrictFace_right z) = sD z := by
  set w : Fin I.amalgam.card → Label.{u} := fun d ↦
    if hd : ∃ i, StageType.faceCell I.restrictFace_left i = d then sT hd.choose
    else if hd' : ∃ i, StageType.faceCell I.restrictFace_right i = d then sD hd'.choose
    else ⊥ with hwdef
  have hwL (z : Fin I.left.card) : w (StageType.faceCell I.restrictFace_left z) = sT z := by
    have hd : ∃ i, StageType.faceCell I.restrictFace_left i =
        StageType.faceCell I.restrictFace_left z := ⟨z, rfl⟩
    rw [hwdef]
    exact (dite_eq_left hd).trans
      (congrArg sT (faceCell_injective' I.restrictFace_left hd.choose_spec))
  have hwR (z : Fin I.right.card) : w (StageType.faceCell I.restrictFace_right z) = sD z := by
    by_cases hd : ∃ i, StageType.faceCell I.restrictFace_left i =
        StageType.faceCell I.restrictFace_right z
    · rw [hwdef]
      exact (dite_eq_left hd).trans (hroot _ _ hd.choose_spec)
    · have hd' : ∃ i, StageType.faceCell I.restrictFace_right i =
          StageType.faceCell I.restrictFace_right z := ⟨z, rfl⟩
      rw [hwdef]
      exact (dite_eq_right hd).trans ((dite_eq_left hd').trans
        (congrArg sD (faceCell_injective' I.restrictFace_right hd'.choose_spec)))
  have hU : I.amalgam.rows.IsLawfulBelow ((univ : Finset (Fin 2)).map (Coatom.left 1), 2)
      fun d ↦ w d := by
    refine (Scheme.isLawfulBelow_faceCell_iff
      (StageType.comap_toScheme_of_restrictFace I.restrictFace_left) (univ, 2) w).mp ?_
    convert hsT.isLawfulBelow ((univ : Finset (Fin 2)), 2) using 1
    funext i
    exact hwL i
  have hV : I.amalgam.rows.IsLawfulBelow ((univ : Finset (Fin 2)).map (Coatom.right 1), 2)
      fun d ↦ w d := by
    refine (Scheme.isLawfulBelow_faceCell_iff
      (StageType.comap_toScheme_of_restrictFace I.restrictFace_right) (univ, 2) w).mp ?_
    convert hsD.isLawfulBelow ((univ : Finset (Fin 2)), 2) using 1
    funext i
    exact hwR i
  have hgrade (d : Fin I.amalgam.card) : I.amalgam.toCellScheme.grade d ≤ 2 :=
    Nat.lt_succ_iff.mp (I.grade_lt d)
  have hY : I.amalgam.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) fun d ↦ w d := by
    refine CellScheme.Rows.IsLawfulBelow.glue hU hV fun d _ ↦ ?_
    rcases I.mem_visibleCells_or d with hd | hd
    · refine Or.inl ⟨fun x hx ↦ ?_, hgrade d⟩
      obtain ⟨y, hy⟩ := Scheme.mem_visibleCells.mp hd hx
      exact mem_map.mpr ⟨y, mem_univ _, hy⟩
    · refine Or.inr ⟨fun x hx ↦ ?_, hgrade d⟩
      obtain ⟨y, hy⟩ := Scheme.mem_visibleCells.mp hd hx
      exact mem_map.mpr ⟨y, mem_univ _, hy⟩
  exact ⟨w, hY.isLawful fun d ↦ ⟨subset_univ _, hgrade d⟩, hwL, hwR⟩

/-- **The extension at the cap `⊥` with both coatoms prescribed**: lawful labellings of `T` and
`D` with root agreement extend to a lawful labelling of the lower layer. -/
theorem exists_isLawful_lower_two {sT : Fin I.left.card → Label.{u}}
    {sD : Fin I.right.card → Label.{u}} (hsT : I.left.rows.IsLawful sT)
    (hsD : I.right.rows.IsLawful sD) (hroot : I.RootAgree sT sD) :
    ∃ W : Fin I.lowerFieldLayer.card → Label.{u}, I.lowerFieldLayer.rows.IsLawful W ∧
      (∀ z, W (I.privCell z) = sT z) ∧ ∀ z, W (I.donCell z) = sD z := by
  obtain ⟨w, hw, hwL, hwR⟩ := exists_isLawful_glue₂ hsT hsD hroot
  obtain ⟨r, hr, hrp⟩ := Scheme.exists_isLawful_fieldLayer (S := I.amalgam.toScheme) (k := 1)
    (hS := I.not_univ_le 1) hw
  exact ⟨r, hr, fun z ↦ (hrp _).trans (hwL z), fun z ↦ (hrp _).trans (hwR z)⟩

variable (I) in
/-- **The two-coatom lift on the lower layer** (a hypothesis). -/
def HasTwoCoatomLift : Prop :=
  ∀ h : Label.{u}, IsSelfVisible 2 h → ⊥ < h →
    ∀ (sT : Fin I.left.card → Label.{u}) (sD : Fin I.right.card → Label.{u}),
      I.left.rows.IsLawful sT → I.right.rows.IsLawful sD → I.RootAgree sT sD →
      ∀ a : Fin I.lowerFieldLayer.card → Label.{u}, I.lowerFieldLayer.rows.IsLawful a →
        (∀ z, min (sT z) h = min (a (I.privCell z)) h) →
        (∀ z, min (sD z) h = min (a (I.donCell z)) h) →
        ∃ W : Fin I.lowerFieldLayer.card → Label.{u}, I.lowerFieldLayer.rows.IsLawful W ∧
          (∀ z, W (I.privCell z) = sT z) ∧ (∀ z, W (I.donCell z) = sD z) ∧
            ∀ d, min (W d) h = min (a d) h

/-! ### The common face -/

private theorem root_point {y : Fin 2} {x : Fin 2} (hx : Coatom.right 1 x = Coatom.left 1 y) :
    y = 0 := by
  revert x y
  decide

/-- A cell of `T` on the common face has grade `1`. -/
theorem grade_left_of_root {zT : Fin I.left.card} {zD : Fin I.right.card}
    (h : StageType.faceCell I.restrictFace_left zT = StageType.faceCell I.restrictFace_right zD) :
    I.left.toCellScheme.grade zT = 1 := by
  have hs := congrArg (fun d ↦ I.amalgam.toCellScheme.scope d) h
  simp only [StageType.scope_faceCell] at hs
  have hsub : I.left.toCellScheme.scope zT ⊆ {0} := by
    intro y hy
    have hm : Coatom.left 1 y ∈ (I.right.toCellScheme.scope zD).map (Coatom.right 1) :=
      hs ▸ mem_map_of_mem _ hy
    obtain ⟨x, -, hx⟩ := mem_map.mp hm
    exact mem_singleton.mpr (root_point hx)
  have h0 : 0 < I.left.toCellScheme.grade zT :=
    (I.left.isWellFormed.isWellFormed.gradedIndex_mem zT).2.1
  have hc := (I.left.isWellFormed.isWellFormed.grade_le_card zT).trans (card_le_card hsub)
  rw [card_singleton] at hc
  omega

theorem grade_right_of_root {zT : Fin I.left.card} {zD : Fin I.right.card}
    (h : StageType.faceCell I.restrictFace_left zT = StageType.faceCell I.restrictFace_right zD) :
    I.right.toCellScheme.grade zD = 1 := by
  have hg := congrArg (fun d ↦ I.amalgam.toCellScheme.grade d) h
  simp only [StageType.grade_faceCell] at hg
  rw [← hg]
  exact grade_left_of_root h

/-! ### The hypotheses with root agreement -/

/-- **The raise from `T` into `D` with root agreement.** -/
def DonorCap.HasRaiseFromLive (c : I.DonorCap) : Prop :=
  ∀ sT : Fin I.left.card → Label.{u}, I.left.rows.IsLawful sT → ∃ sD : Fin I.right.card → Label.{u},
    I.right.rows.IsLawful sD ∧ I.RootAgree sT sD ∧ (∀ z, I.right.label z = ⊥ → sD z = ⊥) ∧
      (∀ y, I.right.label y = ⊤ → c.value sT ≤ sD y) ∧ c.DonorExact sT sD

/-- **The capped exact lift into `D` with root agreement.** -/
def DonorCap.HasExactLiftLive (c : I.DonorCap) : Prop :=
  ∀ h : Label.{u}, IsSelfVisible 2 h → ⊥ < h →
    ∀ sT eT : Fin I.left.card → Label.{u}, I.left.rows.IsLawful sT → I.left.rows.IsLawful eT →
      (∀ z, min (sT z) h = min (eT z) h) → c.value sT ≤ h → h < sT c.cap →
      ∀ eD : Fin I.right.card → Label.{u}, I.right.rows.IsLawful eD → c.DonorExact eT eD →
        ∃ sD : Fin I.right.card → Label.{u}, I.right.rows.IsLawful sD ∧ I.RootAgree sT sD ∧
          (∀ z, min (sD z) h = min (eD z) h) ∧ c.DonorExact sT sD

theorem hasExactLiftLive_of_marker_eq_cap (hb : I.left.toCellScheme.grade c.cap = 2)
    (hm : c.marker = c.cap) : c.HasExactLiftLive := by
  intro h _ _ sT _ hsT _ _ hval hcap
  have hvs : IsSelfVisible 2 (sT c.cap) := hb ▸ hsT.orderly c.cap
  have : c.value sT = sT c.cap := by
    unfold DonorCap.value
    rw [hm, hvs.visibilityReplace_eq, min_self]
  exact absurd (hval.trans_lt hcap) (by rw [this]; exact lt_irrefl _)

private theorem hxyV : (Fin.last 2 : Fin 3) ≠ Fin.castSucc (Fin.last 1) := by decide
private theorem hxV : (Fin.last 2 : Fin 3) ≠ 0 := by decide
private theorem hyV : (Fin.castSucc (Fin.last 1) : Fin 3) ≠ 0 := by decide

theorem isLawfulBelow_donOf_one {v : Fin I.lowerFieldLayer.card → Label.{u}}
    (hv : I.lowerFieldLayer.rows.IsLawfulBelow (univ, 1) fun d ↦ v d) :
    I.right.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 1) fun i ↦ v (I.donCell i.1) :=
  (isLawfulBelow_coatom_iff I.restrictFace_right (Coatom.univ_map_right (m := 1)) 1).mp
    (hv.mono (X := (univ.erase (Fin.castSucc (Fin.last 1)), 1)) ⟨subset_univ _, le_rfl⟩)

theorem donCell_mem_below_one {z : Fin I.right.card} (hz : I.right.toCellScheme.grade z ≤ 1) :
    I.donCell z ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1) := by
  rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
  exact ⟨subset_univ _, (StageType.grade_faceCell I.restrictFace_right z).trans_le hz⟩

/-! ### The provisions with both coatoms live -/

/-- **The lift provision at a positive cap from the coatom of `T`**, both coatoms live. -/
theorem capProvisionL_left (hD : I.right.IsLegal) (hraise : c.HasRaiseFromLive)
    (hexact : c.HasExactLiftLive) (htwo : I.HasTwoCoatomLift)
    {h : Label.{u}} (hh : IsSelfVisible 2 h) (hbh : ⊥ < h)
    {a : Fin I.lowerFieldLayer.card → Label.{u}} (ha : I.lowerFieldLayer.rows.IsLawful a)
    (hA : I.admD c a) {f : Fin I.lowerFieldLayer.card → Label.{u}}
    (hf : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) (fun d ↦ f d))
    (hfa : ∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.last 2), 2),
      min (f d) h = min (a d) h) :
    ∃ W : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.last 2), 2), W d = f d) ∧
      (∀ d, I.lowerFieldLayer.toCellScheme.grade d ≤ 2 → min (W d) h = min (a d) h) ∧
      I.admD c (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  classical
  have hsT := isLawful_privOf hf
  have heT := isLawful_privOf (ha.isLawfulBelow (univ.erase (Fin.last 2), 2))
  have heD := isLawful_donOf (ha.isLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2))
  have hagT (z : Fin I.left.card) : min (f (I.privCell z)) h = min (a (I.privCell z)) h :=
    hfa _ (privCell_mem_below z)
  have hm := DonorCap.min_value_eq (c := c) hh hagT
  have hvR (z : Fin I.left.card) :
      min (visibilityReplace 2 1 (f (I.privCell z))) h =
        min (visibilityReplace 2 1 (a (I.privCell z))) h :=
    Label.min_visibilityReplace_two_eq hh (by omega) (hagT z)
  obtain ⟨w, -, hwV, hwf, hwa⟩ := exists_gradeOne hxyV hxV hyV hh hf ha hfa
  -- the copy on `D`
  obtain ⟨sD, hsD, hroot, hsDa, hsDT⟩ : ∃ sD : Fin I.right.card → Label.{u},
      I.right.rows.IsLawful sD ∧ I.RootAgree (fun z ↦ f (I.privCell z)) sD ∧
      (∀ i, min (sD i) h = min (a (I.donCell i)) h) ∧
      (c.InClass (fun z ↦ f (I.privCell z)) →
        (∀ z, I.right.label z = ⊥ → min (sD z) (f (I.privCell c.cap)) = ⊥) ∧
          c.DonorExact (fun z ↦ f (I.privCell z)) sD ∧
            ∀ y, I.right.label y = ⊤ → c.value (fun z ↦ f (I.privCell z)) ≤ sD y) := by
    by_cases hc : c.InClass (fun z ↦ f (I.privCell z)) ∧
        h < c.value (fun z ↦ f (I.privCell z))
    · have hclE := hc.1.of_min_eq hbh hagT
      have hcorr := hA (inBottomClass_iffD.mpr hclE)
      have hma : h ≤ c.value (fun z ↦ a (I.privCell z)) := by
        have e1 := hm
        rw [min_eq_right hc.2.le] at e1
        exact min_eq_right_iff.mp e1.symm
      have hcapE : h ≤ a (I.privCell c.cap) := hma.trans (DonorCap.value_le_cap _)
      have hcapS : h ≤ f (I.privCell c.cap) := hc.2.le.trans (DonorCap.value_le_cap _)
      obtain ⟨sD, hsD, hroot, hZ, hTT, hFF⟩ := hraise _ hsT
      refine ⟨sD, hsD, hroot, fun i ↦ ?_, fun _ ↦ ⟨fun z hz ↦ by rw [hZ z hz, min_bot_left],
        hFF, hTT⟩⟩
      by_cases hi0 : I.right.label i = ⊥
      · have h0 := eq_bot_of_isCorrectD hcorr hi0
        have hai : a (I.donCell i) = ⊥ := by
          rcases min_eq_bot.mp h0 with h' | h'
          · exact h'
          · exact absurd h' (ne_bot_of_gt (hbh.trans_le hcapE))
        rw [hZ i hi0, hai]
      by_cases hiT : I.right.label i = ⊤
      · have h1 : h ≤ sD i := hc.2.le.trans (hTT i hiT)
        have h2 : h ≤ a (I.donCell i) := hma.trans (le_of_isCorrectD hcorr hiT)
        rw [min_eq_right h1, min_eq_right h2]
      · have hE := donorExact_of_isCorrect hcorr i hi0 hiT
        calc min (sD i) h = min (min (sD i) (f (I.privCell c.cap))) h := by
              rw [min_assoc, min_eq_right hcapS]
          _ = min (min (visibilityReplace 2 1 (f (I.privCell (c.ref i))))
              (f (I.privCell c.cap))) h := by rw [hFF i hi0 hiT]
          _ = min (visibilityReplace 2 1 (f (I.privCell (c.ref i)))) h := by
              rw [min_assoc, min_eq_right hcapS]
          _ = min (visibilityReplace 2 1 (a (I.privCell (c.ref i)))) h := hvR _
          _ = min (min (visibilityReplace 2 1 (a (I.privCell (c.ref i))))
              (a (I.privCell c.cap))) h := by rw [min_assoc, min_eq_right hcapE]
          _ = min (min (a (I.donCell i)) (a (I.privCell c.cap))) h := by rw [hE]
          _ = min (a (I.donCell i)) h := by rw [min_assoc, min_eq_right hcapE]
    by_cases hc2 : c.InClass (fun z ↦ f (I.privCell z)) ∧ h < f (I.privCell c.cap)
    · have hle : c.value (fun z ↦ f (I.privCell z)) ≤ h := not_lt.mp fun hlt ↦ hc ⟨hc2.1, hlt⟩
      have hclE := hc2.1.of_min_eq hbh hagT
      have hcorr := hA (inBottomClass_iffD.mpr hclE)
      obtain ⟨sD, hsD, hroot, hsDa, hFF⟩ := hexact h hh hbh _ _ hsT heT hagT hle hc2.2 _ heD
        (donorExact_of_isCorrect hcorr)
      have hcapE : h ≤ a (I.privCell c.cap) := by
        have e := hagT c.cap
        rw [min_eq_right hc2.2.le] at e
        exact min_eq_right_iff.mp e.symm
      refine ⟨sD, hsD, hroot, hsDa, fun _ ↦ ⟨fun z hz ↦ ?_, hFF, fun y hy ↦ ?_⟩⟩
      · have h0 := eq_bot_of_isCorrectD hcorr hz
        have hai : a (I.donCell z) = ⊥ := by
          rcases min_eq_bot.mp h0 with h' | h'
          · exact h'
          · exact absurd h' (ne_bot_of_gt (hbh.trans_le hcapE))
        have e := hsDa z
        rw [hai, min_bot_left] at e
        rw [(min_eq_bot.mp e).resolve_right hbh.ne', min_bot_left]
      · calc c.value (fun z ↦ f (I.privCell z))
            = min (c.value (fun z ↦ f (I.privCell z))) h := (min_eq_left hle).symm
          _ = min (c.value fun z ↦ a (I.privCell z)) h := hm
          _ ≤ min (a (I.donCell y)) h := min_le_min_right _ (le_of_isCorrectD hcorr hy)
          _ = min (sD y) h := (hsDa y).symm
          _ ≤ sD y := min_le_left _ _
    · -- the lift of `D` from its cells of grade `1` read by the lift at grade `1`
      obtain ⟨r, hr, hrp, hra⟩ := StageType.exists_lift_from_one hD (isLawfulBelow_donOf_one hwV)
        heD hh fun d ↦ (hwa _ (donCell_mem_below_one d.2.2)).symm
      refine ⟨r, hr, fun zT zD hz ↦ ?_, hra, fun hcl ↦ ?_⟩
      · have hg := grade_right_of_root hz
        have hpz : I.privCell zT = I.donCell zD := congrArg (Fin.castAdd _) hz
        rw [hrp ⟨zD, ⟨subset_univ _, hg.le⟩⟩]
        change f (I.privCell zT) = w (I.donCell zD)
        rw [← hpz, hwf _ (privCell_mem_below zT)]
      have hsle : f (I.privCell c.cap) ≤ h := not_lt.mp fun hlt ↦ hc2 ⟨hcl, hlt⟩
      have hclE := hcl.of_min_eq hbh hagT
      have hcorr := hA (inBottomClass_iffD.mpr hclE)
      have hsE : f (I.privCell c.cap) ≤ a (I.privCell c.cap) := by
        have e := hagT c.cap
        rw [min_eq_left hsle] at e
        exact e ▸ min_le_left _ _
      have hred (x y : Label.{u}) (hxy : min x h = min y h) :
          min x (f (I.privCell c.cap)) = min y (f (I.privCell c.cap)) := by
        rw [← min_eq_right hsle, ← min_assoc, hxy, min_assoc]
      refine ⟨fun z hz ↦ le_bot_iff.mp ?_, fun g' h1 h2 ↦ ?_, fun y hy ↦ ?_⟩
      · rw [hred _ _ (hra z)]
        calc min (a (I.donCell z)) (f (I.privCell c.cap))
            ≤ min (a (I.donCell z)) (a (I.privCell c.cap)) := min_le_min_left _ hsE
          _ = ⊥ := eq_bot_of_isCorrectD hcorr hz
          _ ≤ ⊥ := le_rfl
      · have hE := donorExact_of_isCorrect hcorr g' h1 h2
        rw [hred _ _ (hra g'), hred _ _ (hvR (c.ref g'))]
        calc min (a (I.donCell g')) (f (I.privCell c.cap))
            = min (min (a (I.donCell g')) (a (I.privCell c.cap))) (f (I.privCell c.cap)) := by
              rw [min_assoc, min_eq_right hsE]
          _ = min (min (visibilityReplace 2 1 (a (I.privCell (c.ref g'))))
              (a (I.privCell c.cap))) (f (I.privCell c.cap)) := by rw [hE]
          _ = min (visibilityReplace 2 1 (a (I.privCell (c.ref g')))) (f (I.privCell c.cap)) := by
              rw [min_assoc, min_eq_right hsE]
      · have hle := (DonorCap.value_le_cap (c := c) fun z ↦ f (I.privCell z)).trans hsle
        calc c.value (fun z ↦ f (I.privCell z))
            = min (c.value (fun z ↦ f (I.privCell z))) h := (min_eq_left hle).symm
          _ = min (c.value fun z ↦ a (I.privCell z)) h := hm
          _ ≤ min (a (I.donCell y)) h := min_le_min_right _ (le_of_isCorrectD hcorr hy)
          _ = min (r y) h := (hra y).symm
          _ ≤ r y := min_le_left _ _
  -- the two-coatom lift
  obtain ⟨W, hW, hWT, hWD, hWa⟩ := htwo h hh hbh _ sD hsT hsD hroot a ha hagT hsDa
  refine ⟨W, hW.isLawfulBelow _, fun d hd ↦ ?_, fun d _ ↦ hWa d, admD_orbitCode_block fun hcl ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := exists_faceCell_of_mem_below I.restrictFace_left
      (Coatom.univ_map_left (m := 1)) hd
    exact hWT z
  · have e : (fun z ↦ W (I.privCell z)) = fun z ↦ f (I.privCell z) := funext hWT
    have e' : (fun z ↦ W (I.donCell z)) = sD := funext hWD
    rw [e] at hcl ⊢
    rw [e']
    obtain ⟨hZ, hFF, hTT⟩ := hsDT hcl
    refine ⟨fun z hz ↦ ?_, hFF, fun y hy ↦ ?_⟩
    · rw [hWD, hWT]
      exact hZ z hz
    · rw [hWD]
      exact hTT y hy

/-- **The lift provision at the cap `⊥` from the coatom of `T`**, both coatoms live. -/
theorem botProvisionL_left (hraise : c.HasRaiseFromLive)
    {f : Fin I.lowerFieldLayer.card → Label.{u}}
    (hf : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) (fun d ↦ f d)) :
    ∃ W : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.last 2), 2), W d = f d) ∧
      I.admD c (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsT := isLawful_privOf hf
  obtain ⟨sD, hsD, hroot, hZ, hTT, hFF⟩ := hraise _ hsT
  obtain ⟨W, hW, hWT, hWD⟩ := exists_isLawful_lower_two hsT hsD hroot
  refine ⟨W, hW.isLawfulBelow _, fun d hd ↦ ?_, admD_orbitCode_block fun _ ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := exists_faceCell_of_mem_below I.restrictFace_left
      (Coatom.univ_map_left (m := 1)) hd
    exact hWT z
  · have e : (fun z ↦ W (I.privCell z)) = fun z ↦ f (I.privCell z) := funext hWT
    have e' : (fun z ↦ W (I.donCell z)) = sD := funext hWD
    rw [e, e']
    refine ⟨fun z hz ↦ ?_, hFF, fun y hy ↦ by rw [hWD]; exact hTT y hy⟩
    rw [hWD, hZ z hz, min_bot_left]

/-- **The lift provision at a positive cap from the coatom of `D`**, both coatoms live. -/
theorem capProvisionL_right (hT : I.left.IsLegal) (htwo : I.HasTwoCoatomLift)
    (hb : I.left.toCellScheme.grade c.cap = 2)
    {h : Label.{u}} (hh : IsSelfVisible 2 h) (hbh : ⊥ < h)
    {a : Fin I.lowerFieldLayer.card → Label.{u}} (ha : I.lowerFieldLayer.rows.IsLawful a)
    (hA : I.admD c a) {f : Fin I.lowerFieldLayer.card → Label.{u}}
    (hf : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2)
      (fun d ↦ f d))
    (hfa : ∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2),
      min (f d) h = min (a d) h) :
    ∃ W : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2),
        W d = f d) ∧
      (∀ d, I.lowerFieldLayer.toCellScheme.grade d ≤ 2 → min (W d) h = min (a d) h) ∧
      I.admD c (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  classical
  have hsD := isLawful_donOf hf
  have heT := isLawful_privOf (ha.isLawfulBelow (univ.erase (Fin.last 2), 2))
  have hagD (i : Fin I.right.card) : min (f (I.donCell i)) h = min (a (I.donCell i)) h :=
    hfa _ (donCell_mem_below i)
  obtain ⟨w, -, hwV, hwf, hwa⟩ := exists_gradeOne hxyV.symm hyV hxV hh hf ha hfa
  obtain ⟨r, hr, hrp, hra⟩ := StageType.exists_lift_from_one hT (isLawfulBelow_privOf_one hwV)
    heT hh fun d ↦ (hwa _ (privCell_mem_below_one d.2.2)).symm
  have hsT := StageType.isLawful_capTwo hr hh
  set sT : Fin I.left.card → Label.{u} :=
    fun z ↦ if I.left.toCellScheme.grade z = 2 then min (r z) h else r z with hsTdef
  have hsTa (i : Fin I.left.card) : min (sT i) h = min (a (I.privCell i)) h := by
    change min (if I.left.toCellScheme.grade i = 2 then min (r i) h else r i) h = _
    split_ifs
    · rw [min_assoc, min_self, hra]
    · exact hra i
  have hroot : I.RootAgree sT fun z ↦ f (I.donCell z) := by
    intro zT zD hz
    have hg := grade_left_of_root hz
    have hpz : I.privCell zT = I.donCell zD := congrArg (Fin.castAdd _) hz
    rw [hsTdef]
    simp only [show I.left.toCellScheme.grade zT ≠ 2 by omega, ↓reduceIte]
    rw [hrp ⟨zT, ⟨subset_univ _, hg.le⟩⟩]
    change w (I.privCell zT) = f (I.donCell zD)
    rw [hpz, hwf _ (donCell_mem_below zD)]
  obtain ⟨W, hW, hWT, hWD, hWa⟩ := htwo h hh hbh sT _ hsT hsD hroot a ha hsTa hagD
  refine ⟨W, hW.isLawfulBelow _, fun d hd ↦ ?_, fun d _ ↦ hWa d,
    admD_orbitCode_block fun hcl ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := exists_faceCell_of_mem_below I.restrictFace_right
      (Coatom.univ_map_right (m := 1)) hd
    exact hWD z
  · have e : (fun z ↦ W (I.privCell z)) = sT := funext hWT
    have e' : (fun z ↦ W (I.donCell z)) = fun z ↦ f (I.donCell z) := funext hWD
    rw [e] at hcl ⊢
    rw [e']
    have hclE := hcl.of_min_eq hbh hsTa
    have hcorr := hA (inBottomClass_iffD.mpr hclE)
    have hcapL : sT c.cap ≤ h := by
      rw [hsTdef]
      simp only [hb, ↓reduceIte]
      exact min_le_right _ _
    have hcapE : sT c.cap ≤ a (I.privCell c.cap) := by
      have e1 := hsTa c.cap
      rw [min_eq_left hcapL] at e1
      exact e1.symm ▸ min_le_left _ _
    have hvR (z : Fin I.left.card) :
        min (visibilityReplace 2 1 (sT z)) h = min (visibilityReplace 2 1 (a (I.privCell z))) h :=
      Label.min_visibilityReplace_two_eq hh (by omega) (hsTa z)
    have hred (x y : Label.{u}) (hxy : min x h = min y h) :
        min x (sT c.cap) = min y (sT c.cap) := by
      rw [← min_eq_right hcapL, ← min_assoc, hxy, min_assoc]
    refine ⟨fun z hz ↦ ?_, fun g' h1 h2 ↦ ?_, fun y hy ↦ ?_⟩
    · rw [hWD, hWT, hred _ _ (hagD z)]
      refine le_bot_iff.mp ?_
      calc min (a (I.donCell z)) (sT c.cap)
          ≤ min (a (I.donCell z)) (a (I.privCell c.cap)) := min_le_min_left _ hcapE
        _ = ⊥ := eq_bot_of_isCorrectD hcorr hz
        _ ≤ ⊥ := le_rfl
    · have hE := donorExact_of_isCorrect hcorr g' h1 h2
      change min (f (I.donCell g')) (sT c.cap) =
        min (visibilityReplace 2 1 (sT (c.ref g'))) (sT c.cap)
      rw [hred _ _ (hagD g'), hred _ _ (hvR (c.ref g'))]
      calc min (a (I.donCell g')) (sT c.cap)
          = min (min (a (I.donCell g')) (a (I.privCell c.cap))) (sT c.cap) := by
            rw [min_assoc, min_eq_right hcapE]
        _ = min (min (visibilityReplace 2 1 (a (I.privCell (c.ref g'))))
            (a (I.privCell c.cap))) (sT c.cap) := by rw [hE]
        _ = min (visibilityReplace 2 1 (a (I.privCell (c.ref g')))) (sT c.cap) := by
            rw [min_assoc, min_eq_right hcapE]
    · rw [hWD]
      have hle := (DonorCap.value_le_cap (c := c) sT).trans hcapL
      calc c.value sT = min (c.value sT) h := (min_eq_left hle).symm
        _ = min (c.value fun z ↦ a (I.privCell z)) h := DonorCap.min_value_eq hh hsTa
        _ ≤ min (a (I.donCell y)) h := min_le_min_right _ (le_of_isCorrectD hcorr hy)
        _ = min (f (I.donCell y)) h := (hagD y).symm
        _ ≤ f (I.donCell y) := min_le_left _ _

/-- **The lift provision at the cap `⊥` from the coatom of `D`**, both coatoms live. -/
theorem botProvisionL_right (hT : I.left.IsLegal) (hb : I.left.toCellScheme.grade c.cap = 2)
    {f : Fin I.lowerFieldLayer.card → Label.{u}}
    (hf : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2)
      (fun d ↦ f d)) :
    ∃ W : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2),
        W d = f d) ∧
      I.admD c (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  classical
  have hsD := isLawful_donOf hf
  obtain ⟨w, -, hwV, hwf, -⟩ := exists_gradeOne hxyV.symm hyV hxV (isSelfVisible_bot 2) hf
    (CellScheme.Rows.isLawful_const_bot (R := I.lowerFieldLayer.rows))
    fun _ _ ↦ by rw [min_bot_right, min_bot_right]
  obtain ⟨r, hr, hrp, -⟩ := StageType.exists_lift_from_one hT (isLawfulBelow_privOf_one hwV)
    (CellScheme.Rows.isLawful_const_bot (R := I.left.rows)) (isSelfVisible_bot 2)
    fun _ ↦ by rw [min_bot_right, min_bot_right]
  have hsT := StageType.isLawful_capTwo hr (isSelfVisible_bot 2)
  have hroot : I.RootAgree (fun z ↦ if I.left.toCellScheme.grade z = 2 then min (r z) ⊥ else r z)
      fun z ↦ f (I.donCell z) := by
    intro zT zD hz
    have hg := grade_left_of_root hz
    have hpz : I.privCell zT = I.donCell zD := congrArg (Fin.castAdd _) hz
    simp only [show I.left.toCellScheme.grade zT ≠ 2 by omega, ↓reduceIte]
    rw [hrp ⟨zT, ⟨subset_univ _, hg.le⟩⟩]
    change w (I.privCell zT) = f (I.donCell zD)
    rw [hpz, hwf _ (donCell_mem_below zD)]
  obtain ⟨W, hW, hWT, hWD⟩ := exists_isLawful_lower_two hsT hsD hroot
  have hcap : W (I.privCell c.cap) = ⊥ := by
    rw [hWT]
    simp only [hb, ↓reduceIte, min_bot_right]
  refine ⟨W, hW.isLawfulBelow _, fun d hd ↦ ?_, admD_orbitCode_block fun _ ↦
    ⟨fun z _ ↦ by rw [hcap, min_bot_right], fun _ _ _ ↦ ?_, fun y _ ↦ ?_⟩⟩
  · obtain ⟨z, rfl⟩ := exists_faceCell_of_mem_below I.restrictFace_right
      (Coatom.univ_map_right (m := 1)) hd
    exact hWD z
  · change min _ (W (I.privCell c.cap)) = min _ (W (I.privCell c.cap))
    rw [hcap, min_bot_right, min_bot_right]
  · exact ((DonorCap.value_le_cap (c := c) _).trans hcap.le).trans bot_le

/-! ### Legality with both coatoms live -/

private theorem erase_ne_univV (x : Fin 3) : univ.erase x ≠ univ :=
  fun he ↦ Finset.notMem_erase x univ (he.symm ▸ mem_univ x)

private theorem exists_gradedIndex_left_twoV :
    ∃ c, I.lowerFieldLayer.toCellScheme.gradedIndex c = (univ.erase (Fin.last 2), 2) := by
  obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq (univ.erase (Fin.last 2), 2)
    ⟨I.erase_last_mem_faces, two_pos, by decide⟩ (erase_ne_univV _)
  exact ⟨Fin.castAdd _ d, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd⟩

private theorem exists_gradedIndex_right_twoV :
    ∃ c, I.lowerFieldLayer.toCellScheme.gradedIndex c =
      (univ.erase (Fin.castSucc (Fin.last 1)), 2) := by
  obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq (univ.erase (Fin.castSucc (Fin.last 1)), 2)
    ⟨I.erase_castSucc_mem_faces, two_pos, by decide⟩ (erase_ne_univV _)
  exact ⟨Fin.castAdd _ d, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd⟩

/-- **The admitted completion with a donor, both coatoms live at grade `1`.**  For a seed with
coatom types `T` and `D` (both legal), donor data with the cap of grade `2` in `T`, the raise and
the capped exact lift with root agreement, and the two-coatom lift on the lower layer, the admitted
layer at the grade `2` over the canonical lower layer is legal below the full grade. -/
theorem isLegalBelowFullGrade_donorLayer_live (hT : I.left.IsLegal) (hD : I.right.IsLegal)
    (hb : I.left.toCellScheme.grade c.cap = 2) (hraise : c.HasRaiseFromLive)
    (hexact : c.HasExactLiftLive) (htwo : I.HasTwoCoatomLift) :
    (I.donorLayer c).IsLegalBelowFullGrade :=
  let L1 := Scheme.cappedLift_admittedFieldLayer (j := 1)
    (hS := I.not_univ_two_le_lowerFieldLayer) I.isConsistent_lowerFieldLayer
    (CapRequests.admits_bot _ _ _) (erase_ne_univV _) exists_gradedIndex_left_twoV
    (I.cappedLift_lowerFieldLayer hxyV hxV hyV)
    (fun _ hf ↦ botProvisionL_left (c := c) hraise hf)
    (fun _ hh _ hbh _ ha hA _ hf hfa ↦
      capProvisionL_left hD hraise hexact htwo hh hbh ha hA hf hfa)
  let L2 := Scheme.cappedLift_admittedFieldLayer (j := 1)
    (hS := I.not_univ_two_le_lowerFieldLayer) I.isConsistent_lowerFieldLayer
    (CapRequests.admits_bot _ _ _) (erase_ne_univV _) exists_gradedIndex_right_twoV
    (I.cappedLift_lowerFieldLayer hxyV.symm hyV hxV)
    (fun _ hf ↦ botProvisionL_right (c := c) hT hb hf)
    (fun _ hh _ hbh _ ha hA _ hf hfa ↦ capProvisionL_right hT htwo hb hh hbh ha hA hf hfa)
  { isWellFormed := Scheme.isWellFormed_fieldLayerOn (hS := I.not_univ_two_le_lowerFieldLayer)
      I.isWellFormed_lowerFieldLayer two_pos (by omega)
    isCoded := Scheme.isCoded_admittedFieldLayer (Scheme.isCoded_fieldLayer I.amalgam.isCoded)
    isConsistent := Scheme.isConsistent_admittedFieldLayer I.isConsistent_lowerFieldLayer
    isBountiful := isBountiful_donorLayer L1 L2
    grade_lt := fun d ↦ by
      induction d using Fin.addCases with
      | left e =>
        exact (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ e).trans_lt
          ((I.lowerFieldLayer_grade_le e).trans_lt (by omega))
      | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
    exists_gradedIndex_eq := fun X hX hX2 ↦ by
      obtain ⟨C, j⟩ := X
      have hj0 : 0 < j := hX.2.1
      by_cases hC : C = univ
      · subst hC
        rcases (show j = 1 ∨ j = 2 by simp only at hX2; omega) with rfl | rfl
        · obtain ⟨i, -⟩ := Scheme.exists_catalogueEntry_eq
            (Scheme.orbitCode_splice_bot_mem_catalogue (S := I.amalgam.toScheme) (k := 1)
              (p := fun _ ↦ ⊥) (CellScheme.Rows.isLawfulBelow_const_bot _))
          exact ⟨Fin.castAdd _ (Fin.natAdd _ i),
            (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
              (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i)⟩
        · exact Scheme.exists_gradedIndex_eq_admittedFieldLayer (CapRequests.admits_bot _ _ _)
      · obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq _ hX hC
        exact ⟨Fin.castAdd _ (Fin.castAdd _ d),
          (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
            ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd)⟩ }

/-! ### Reading back a block label -/

/-- **Reading back a block label**: under the cap `⊤`, a correct state reads the copy of a cell of
`D` labelled in a block as the replacement at the offset `1` of the copy of its reference. -/
theorem donCell_eq_of_isCorrect {g : Fin I.lowerFieldLayer.card → Label.{u}}
    (hc : (I.requestsD c).IsCorrect g) (hcap : g (I.privCell c.cap) = ⊤) {f : Fin I.right.card}
    (h1 : I.right.label f ≠ ⊥) (h2 : I.right.label f ≠ ⊤) :
    g (I.donCell f) = visibilityReplace 2 1 (g (I.privCell (c.ref f))) := by
  have hE := donorExact_of_isCorrect hc f h1 h2
  change min (g (I.donCell f)) (g (I.privCell c.cap)) =
    min (visibilityReplace 2 1 (g (I.privCell (c.ref f)))) (g (I.privCell c.cap)) at hE
  rwa [hcap, min_top_right, min_top_right] at hE

end Seed

namespace CoupledGatedExtensionCounterexample

private theorem one_lt_blockStage₂ (ξ : Ordinal.{u}) : 1 < blockStage ξ :=
  Ordinal.one_lt_omega0.trans_le (omega0_le_blockStage ξ)

/-- **A recovered block label.**  Over the doubled lower layer of the coupled-gate type with itself,
with the separate marker (`capSepCP`: the donor copy of `z₁` read exactly through its reference,
the private copy of `z₁`, a live cell labelled `1`), every stage type on the marked coface with face
`T` along the first coatom has, along the second coatom, a face labelling `z₁` with `1`. -/
theorem recovers_z₁_capSepCP (ξ : Ordinal.{u}) (R : ℕ) (hR : R < 2)
    {Q' : StageType.{u} (blockStage (ξ + 1)) (2 + 1)}
    (hQ' : Q'.toScheme = (Seed.markedApex (seedCP (blockStage (ξ + 1)) (one_lt_blockStage₂ _)) rfl
      (capSepCP (blockStage (ξ + 1)) (one_lt_blockStage₂ _) R hR)
      (markedHyp_capSepCP ξ R hR)).toScheme)
    (hf : restrictFace Fin.castSuccEmb Q' =
      some (seedCP (blockStage (ξ + 1)) (one_lt_blockStage₂ _)).left) :
    ∃ Q, restrictFace (extendByLast Fin.castSuccEmb) Q' = some Q ∧
      ∀ i : Fin Q.card, (i : ℕ) = 2 → Q.label i = (1 : Label.{u}) := by
  obtain ⟨Q, hQ, -, hl⟩ := (isStableRecoveryScheme_markedApex_capSepCP ξ R hR 0).2 Q' hQ' hf
  refine ⟨Q, hQ, fun i hi ↦ ?_⟩
  have h1 : (seedCP (blockStage (ξ + 1)) (one_lt_blockStage₂ _)).left.label
      ((2 : Fin 5) : Fin (P (blockStage (ξ + 1)) (one_lt_blockStage₂ _)).card) = (1 : Label.{u}) :=
    rfl
  refine ((hl i _ hi).1 ?_).trans h1
  rw [h1]
  exact fun h ↦ WithTop.coe_ne_top (WithBot.coe_injective h)

end CoupledGatedExtensionCounterexample

end VaughtConjecture
