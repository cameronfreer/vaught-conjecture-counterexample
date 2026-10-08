/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryDonorInstance

/-!
# Marked caps with a donor whose cells are labelled in a block

Roadmap, Layer 3, 3.1, (R6) and 3.3 (the (R4) cap); the admitted layer with a donor of
`VaughtConjecture.Continuation.StableRecoveryDonorMarked`, now with cells of `D` labelled in a block
(the requests `F`) and live cells of grade `1` in `D`.

Here the cells of grade `1` of `T` are dead (`StageType.HasDeadLowCells`), and those of `D` need not
be.  The lift at grade `1` is taken from the coatom of `D` (with the copy on `D` prescribed), and
the copy on `T` is assembled to it; the deadness of `T` makes the two agree at grade `1`.

**Exactness** (`Seed.DonorCap.DonorExact c sT sD`): the copy `sD` reads every cell of `D`
labelled in a block as the visibility replacement at the offset `1` of its reference under `sT`,
under the cap `sT b`.

**The two hypotheses on `D`.**

* `Seed.DonorCap.HasRaiseFromD c` (the raise): every lawful `sT` has a lawful `sD`, `⊥` at the
  cells of `D` labelled `⊥`, at least the marker value of `sT` at those labelled `⊤`, and exact.
* `Seed.DonorCap.HasExactLiftD c` (the capped exact lift): for every cap `h` (self-visible at `2`,
  positive), every lawful `sT` with marker value at most `h` and cap above `h`, every lawful `eT`
  agreeing with `sT` capped at `h`, and every lawful `eD` exact for `eT`, some lawful `sD` agrees
  with `eD` capped at `h` and is exact for `sT`.  The agreement with the entry `eD` is part of the
  statement: an exact `sD` alone would not keep the observation of the entry at `h`.  With the
  marker at the cap the hypothesis holds vacuously (`Seed.hasExactLiftD_of_marker_eq_cap`): the
  marker value is then the cap value.

**Results.**

* `Seed.isLegalBelowFullGrade_donorLayer_block`: for `T` and `D` legal, the cap of grade `2`, `T`
  with dead cells of grade `1`, the raise and the capped exact lift, the admitted layer with a donor
  is legal below the full grade.  The fills from the coatom of `T`: the raise when the prescription
  is in the bottom class with its marker value above `h`; the capped exact lift when its marker
  value is at most `h` and its cap above `h`; the copy of the entry on `D` otherwise.
* Instance with a live cell labelled in a block
  (`DonorPair.isLegalBelowFullGrade_donorLayer_DT`): `T` the private type `P` (dead cells of grade
  `1`) and `D` the coupled-gate type (its cell `z₁` of grade `1` labelled `1`), cap and marker the
  full cell `4` of `T`, the reference of every cell the cap.  The raise is the constant labelling
  `⊥, ⊥, ⊤, ⊤, ⊤` of `D` (`DonorPair.isLawful_lab_top`).
* **No recovery of the block label there** (`DonorPair.donCell_ne_one_DT`): every correct state with
  the cap `⊤` reads the copy of `z₁` other than `1`, because a reference on a type with dead cells
  of grade `1` is `⊥` or self-visible at `2`, and its replacement at the offset `1` is never `1`.
  Reading a label `μ + 1` back needs a reference of grade `1` that is not dead.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

namespace Seed

variable {α : Ordinal.{u}} {I : Seed.{u} α 1} {c : I.DonorCap}

private theorem hxyB : (Fin.last 2 : Fin 3) ≠ Fin.castSucc (Fin.last 1) := by decide
private theorem hxB : (Fin.last 2 : Fin 3) ≠ 0 := by decide
private theorem hyB : (Fin.castSucc (Fin.last 1) : Fin 3) ≠ 0 := by decide

/-- **Exactness**: `sD` reads every cell of `D` labelled in a block as the replacement at the
offset `1` of its reference under `sT`, under the cap `sT b`. -/
def DonorCap.DonorExact (c : I.DonorCap) (sT : Fin I.left.card → Label.{u})
    (sD : Fin I.right.card → Label.{u}) : Prop :=
  ∀ f, I.right.label f ≠ ⊥ → I.right.label f ≠ ⊤ →
    min (sD f) (sT c.cap) = min (visibilityReplace 2 1 (sT (c.ref f))) (sT c.cap)

/-- **The raise from `T` into `D`** with exactness and the marker value. -/
def DonorCap.HasRaiseFromD (c : I.DonorCap) : Prop :=
  ∀ sT : Fin I.left.card → Label.{u}, I.left.rows.IsLawful sT → ∃ sD : Fin I.right.card → Label.{u},
    I.right.rows.IsLawful sD ∧ (∀ z, I.right.label z = ⊥ → sD z = ⊥) ∧
      (∀ y, I.right.label y = ⊤ → c.value sT ≤ sD y) ∧ c.DonorExact sT sD

/-- **The capped exact lift into `D`**. -/
def DonorCap.HasExactLiftD (c : I.DonorCap) : Prop :=
  ∀ h : Label.{u}, IsSelfVisible 2 h → ⊥ < h →
    ∀ sT eT : Fin I.left.card → Label.{u}, I.left.rows.IsLawful sT → I.left.rows.IsLawful eT →
      (∀ z, min (sT z) h = min (eT z) h) → c.value sT ≤ h → h < sT c.cap →
      ∀ eD : Fin I.right.card → Label.{u}, I.right.rows.IsLawful eD → c.DonorExact eT eD →
        ∃ sD : Fin I.right.card → Label.{u}, I.right.rows.IsLawful sD ∧
          (∀ z, min (sD z) h = min (eD z) h) ∧ c.DonorExact sT sD

/-- **With the marker at the cap, the capped exact lift holds vacuously**: for a lawful `sT` the
marker value is the cap value (self-visible at `2`). -/
theorem hasExactLiftD_of_marker_eq_cap (hb : I.left.toCellScheme.grade c.cap = 2)
    (hm : c.marker = c.cap) : c.HasExactLiftD := by
  intro h _ _ sT _ hsT _ _ hval hcap
  have hvs : IsSelfVisible 2 (sT c.cap) := hb ▸ hsT.orderly c.cap
  have : c.value sT = sT c.cap := by
    unfold DonorCap.value
    rw [hm, hvs.visibilityReplace_eq, min_self]
  exact absurd (hval.trans_lt hcap) (by rw [this]; exact lt_irrefl _)

/-! ### Requests with block labels -/

theorem ref_donCell (f : Fin I.right.card) :
    (I.requestsD c).ref (I.donCell f) = I.privCell (c.ref f) := by
  classical
  have he : ∃ i, I.donCell i = I.donCell f := ⟨f, rfl⟩
  change (if h : ∃ i, I.donCell i = I.donCell f then I.privCell (c.ref h.choose)
    else I.donCell f) = _
  rw [dite_eq_left he]
  exact congrArg (fun i ↦ I.privCell (c.ref i))
    (faceCell_castAdd_injective I.restrictFace_right he.choose_spec)

/-- **Correctness with a donor**: `⊥` at the copies of the cells labelled `⊥`, exact at those
labelled in a block, and at least the marker value at those labelled `⊤`, under the cap. -/
theorem isCorrect_requestsD_block {g : Fin I.lowerFieldLayer.card → Label.{u}}
    (hZ : ∀ z, I.right.label z = ⊥ → min (g (I.donCell z)) (g (I.privCell c.cap)) = ⊥)
    (hF : c.DonorExact (fun z ↦ g (I.privCell z)) fun z ↦ g (I.donCell z))
    (hT : ∀ y, I.right.label y = ⊤ → c.value (fun z ↦ g (I.privCell z)) ≤ g (I.donCell y)) :
    (I.requestsD c).IsCorrect g where
  eq_bot := by
    rintro _ ⟨z, hz, rfl⟩
    exact hZ z hz
  eq_refValue := by
    rintro _ ⟨f, ⟨h1, h2⟩, rfl⟩
    change _ = min (visibilityReplace 2 1 (g ((I.requestsD c).ref (I.donCell f))))
      (g (I.privCell c.cap))
    rw [ref_donCell]
    exact hF f h1 h2
  markerValue_le := by
    rintro _ ⟨y, hy, rfl⟩
    exact le_min (hT y hy) (DonorCap.value_le_cap (c := c) fun z ↦ g (I.privCell z))

theorem donorExact_of_isCorrect {g : Fin I.lowerFieldLayer.card → Label.{u}}
    (hc : (I.requestsD c).IsCorrect g) :
    c.DonorExact (fun z ↦ g (I.privCell z)) fun z ↦ g (I.donCell z) := by
  intro f h1 h2
  have := hc.eq_refValue _ ⟨f, ⟨h1, h2⟩, rfl⟩
  change _ = min (visibilityReplace 2 1 (g ((I.requestsD c).ref (I.donCell f))))
    (g (I.privCell c.cap)) at this
  rw [ref_donCell] at this
  exact this

/-- The admission of a lawful state whose copies satisfy the requests in the bottom class. -/
theorem admD_orbitCode_block {g : Fin I.lowerFieldLayer.card → Label.{u}}
    (h4 : c.InClass (fun z ↦ g (I.privCell z)) →
      (∀ z, I.right.label z = ⊥ → min (g (I.donCell z)) (g (I.privCell c.cap)) = ⊥) ∧
        c.DonorExact (fun z ↦ g (I.privCell z)) (fun z ↦ g (I.donCell z)) ∧
          ∀ y, I.right.label y = ⊤ → c.value (fun z ↦ g (I.privCell z)) ≤ g (I.donCell y)) :
    I.admD c (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) g)) := by
  by_cases hcl : c.InClass fun z ↦ g (I.privCell z)
  · obtain ⟨hZ, hF, hT⟩ := h4 hcl
    exact admD_orbitCode (isCorrect_requestsD_block hZ hF hT).admits
  · exact admD_orbitCode (admD_of_not hcl)

/-! ### Copies and dead cells -/

/-- A lawful labelling of a coatom type is the copy of a labelling of the lower layer lawful below
that coatom. -/
theorem exists_coatom_labelling {f : Fin 2 ↪ Fin 3} {E : StageType.{u} α 2}
    (hE : restrictFace f I.amalgam = some E) {y : Fin 3} (hfy : univ.map f = univ.erase y)
    {s : Fin E.card → Label.{u}} (hs : E.rows.IsLawful s) :
    ∃ v : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase y, 2) (fun d ↦ v d) ∧
        ∀ i, v (Fin.castAdd _ (StageType.faceCell hE i)) = s i := by
  classical
  set v : Fin I.lowerFieldLayer.card → Label.{u} := fun e ↦
    if he : ∃ i, e = Fin.castAdd _ (StageType.faceCell hE i) then s he.choose else ⊥ with hvdef
  have hv (i : Fin E.card) : v (Fin.castAdd _ (StageType.faceCell hE i)) = s i := by
    have he : ∃ j, (Fin.castAdd _ (StageType.faceCell hE i) : Fin I.lowerFieldLayer.card) =
        Fin.castAdd _ (StageType.faceCell hE j) := ⟨i, rfl⟩
    rw [hvdef]
    exact (dite_eq_left he).trans
      (congrArg s (faceCell_castAdd_injective hE he.choose_spec).symm)
  refine ⟨v, (isLawfulBelow_coatom_iff hE hfy 2).mpr ?_, hv⟩
  convert hs.isLawfulBelow ((univ : Finset (Fin 2)), 2) using 1
  exact funext fun i ↦ hv i.1

/-- A labelling lawful below `(univ, 1)` is `⊥` at the copies of the dead cells of `T`. -/
theorem eq_bot_privCell_of_dead (hd : I.left.HasDeadLowCells)
    {v : Fin I.lowerFieldLayer.card → Label.{u}}
    (hv : I.lowerFieldLayer.rows.IsLawfulBelow (univ, 1) fun d ↦ v d) {z : Fin I.left.card}
    (hz : I.left.toCellScheme.grade z = 1) : v (I.privCell z) = ⊥ :=
  (isLawfulBelow_privOf_one hv).eq_bot_of_row_self (w := fun i ↦ v (I.privCell i))
    ⟨subset_univ _, hz.le⟩ (hd z hz)

theorem donCell_mem_below' (z : Fin I.right.card) :
    I.donCell z ∈
      I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2) :=
  donCell_mem_below z

/-! ### The provisions -/

/-- **The lift provision at a positive cap from the coatom of `T`**, with block labels. -/
theorem capProvisionB_left (hdT : I.left.HasDeadLowCells) (hraise : c.HasRaiseFromD)
    (hexact : c.HasExactLiftD) {h : Label.{u}} (hh : IsSelfVisible 2 h) (hbh : ⊥ < h)
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
  -- the copy on `D`
  obtain ⟨sD, hsD, hsDa, hsDT⟩ : ∃ sD : Fin I.right.card → Label.{u}, I.right.rows.IsLawful sD ∧
      (∀ i, min (sD i) h = min (a (I.donCell i)) h) ∧
      (c.InClass (fun z ↦ f (I.privCell z)) →
        (∀ z, I.right.label z = ⊥ → min (sD z) (f (I.privCell c.cap)) = ⊥) ∧
          c.DonorExact (fun z ↦ f (I.privCell z)) sD ∧
            ∀ y, I.right.label y = ⊤ → c.value (fun z ↦ f (I.privCell z)) ≤ sD y) := by
    by_cases hc : c.InClass (fun z ↦ f (I.privCell z)) ∧
        h < c.value (fun z ↦ f (I.privCell z))
    · -- the raise
      have hclE := hc.1.of_min_eq hbh hagT
      have hcorr := hA (inBottomClass_iffD.mpr hclE)
      have hma : h ≤ c.value (fun z ↦ a (I.privCell z)) := by
        have e1 := hm
        rw [min_eq_right hc.2.le] at e1
        exact min_eq_right_iff.mp e1.symm
      have hcapE : h ≤ a (I.privCell c.cap) := hma.trans (DonorCap.value_le_cap _)
      have hcapS : h ≤ f (I.privCell c.cap) := hc.2.le.trans (DonorCap.value_le_cap _)
      obtain ⟨sD, hsD, hZ, hTT, hFF⟩ := hraise _ hsT
      refine ⟨sD, hsD, fun i ↦ ?_, fun _ ↦ ⟨fun z hz ↦ by rw [hZ z hz, min_bot_left], hFF,
        hTT⟩⟩
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
    · -- the capped exact lift
      have hle : c.value (fun z ↦ f (I.privCell z)) ≤ h := not_lt.mp fun hlt ↦ hc ⟨hc2.1, hlt⟩
      have hclE := hc2.1.of_min_eq hbh hagT
      have hcorr := hA (inBottomClass_iffD.mpr hclE)
      obtain ⟨sD, hsD, hsDa, hFF⟩ := hexact h hh hbh _ _ hsT heT hagT hle hc2.2 _ heD
        (donorExact_of_isCorrect hcorr)
      have hcapE : h ≤ a (I.privCell c.cap) := by
        have e := hagT c.cap
        rw [min_eq_right hc2.2.le] at e
        exact min_eq_right_iff.mp e.symm
      refine ⟨sD, hsD, hsDa, fun _ ↦ ⟨fun z hz ↦ ?_, hFF, fun y hy ↦ ?_⟩⟩
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
    · -- the copy of the entry
      refine ⟨fun i ↦ a (I.donCell i), heD, fun _ ↦ rfl, fun hcl ↦ ?_⟩
      have hsle : f (I.privCell c.cap) ≤ h := not_lt.mp fun hlt ↦ hc2 ⟨hcl, hlt⟩
      have hclE := hcl.of_min_eq hbh hagT
      have hcorr := hA (inBottomClass_iffD.mpr hclE)
      have hsE : f (I.privCell c.cap) ≤ a (I.privCell c.cap) := by
        have e := hagT c.cap
        rw [min_eq_left hsle] at e
        exact e ▸ min_le_left _ _
      refine ⟨fun z hz ↦ le_bot_iff.mp ?_, fun g' h1 h2 ↦ ?_, fun y hy ↦ ?_⟩
      · calc min (a (I.donCell z)) (f (I.privCell c.cap))
            ≤ min (a (I.donCell z)) (a (I.privCell c.cap)) := min_le_min_left _ hsE
          _ = ⊥ := eq_bot_of_isCorrectD hcorr hz
          _ ≤ ⊥ := le_rfl
      · have hE := donorExact_of_isCorrect hcorr g' h1 h2
        calc min (a (I.donCell g')) (f (I.privCell c.cap))
            = min (min (a (I.donCell g')) (a (I.privCell c.cap))) (f (I.privCell c.cap)) := by
              rw [min_assoc, min_eq_right hsE]
          _ = min (min (visibilityReplace 2 1 (a (I.privCell (c.ref g'))))
              (a (I.privCell c.cap))) (f (I.privCell c.cap)) := by rw [hE]
          _ = min (visibilityReplace 2 1 (a (I.privCell (c.ref g')))) (f (I.privCell c.cap)) := by
              rw [min_assoc, min_eq_right hsE]
          _ = min (min (visibilityReplace 2 1 (a (I.privCell (c.ref g')))) h)
              (f (I.privCell c.cap)) := by rw [min_assoc, min_eq_right hsle]
          _ = min (min (visibilityReplace 2 1 (f (I.privCell (c.ref g')))) h)
              (f (I.privCell c.cap)) := by rw [hvR]
          _ = min (visibilityReplace 2 1 (f (I.privCell (c.ref g')))) (f (I.privCell c.cap)) := by
              rw [min_assoc, min_eq_right hsle]
      · have hle := (DonorCap.value_le_cap (c := c) fun z ↦ f (I.privCell z)).trans hsle
        calc c.value (fun z ↦ f (I.privCell z))
            = min (c.value (fun z ↦ f (I.privCell z))) h := (min_eq_left hle).symm
          _ = min (c.value fun z ↦ a (I.privCell z)) h := hm
          _ ≤ min (a (I.donCell y)) h := min_le_min_right _ (le_of_isCorrectD hcorr hy)
          _ ≤ a (I.donCell y) := min_le_left _ _
  -- the lift at grade `1` from the coatom of `D`, with the copy on `D` prescribed
  obtain ⟨v, hv, hvs⟩ := exists_coatom_labelling I.restrictFace_right
    (Coatom.univ_map_right (m := 1)) hsD
  have hva : ∀ d ∈ I.lowerFieldLayer.toCellScheme.below
      (univ.erase (Fin.castSucc (Fin.last 1)), 2), min (v d) h = min (a d) h := by
    intro d hd
    obtain ⟨i, rfl⟩ := exists_faceCell_of_mem_below I.restrictFace_right
      (Coatom.univ_map_right (m := 1)) hd
    rw [hvs]
    exact hsDa i
  obtain ⟨w, hwU, hwV, hwv, hwa⟩ := exists_gradeOne hxyB.symm hyB hxB hh hv ha hva
  have hsw (i : Fin I.left.card) (hi : I.left.toCellScheme.grade i = 1) :
      f (I.privCell i) = w (I.privCell i) :=
    (hdT.eq_bot hsT hi).trans (eq_bot_privCell_of_dead hdT hwV hi).symm
  obtain ⟨g, hg, hgw, hgs⟩ := exists_assemble hxyB.symm hyB hxB I.restrictFace_left
    (Coatom.univ_map_left (m := 1)) hwU hwV hsT hsw
  have hdon (z : Fin I.right.card) : g (I.donCell z) = sD z :=
    (hgw _ (.inl (donCell_mem_below z))).trans ((hwv _ (donCell_mem_below z)).trans (hvs z))
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_, fun d _ ↦ ?_, admD_orbitCode_block fun hcl ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := exists_faceCell_of_mem_below I.restrictFace_left
      (Coatom.univ_map_left (m := 1)) hd
    exact hgs z
  · by_cases hb : d ∈ I.lowerFieldLayer.toCellScheme.below
        (univ.erase (Fin.castSucc (Fin.last 1)), 2) ∨
        d ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1)
    · rw [hgw d hb]
      rcases hb with hb | hb
      · rw [hwv d hb]
        exact hva d hb
      · exact hwa d hb
    · obtain ⟨i, rfl⟩ := exists_faceCell_of_mem_below I.restrictFace_left
        (Coatom.univ_map_left (m := 1))
        (((mem_below_three hxyB.symm hyB hxB d).resolve_left fun h' ↦ hb (.inl h')).resolve_left
          fun h' ↦ hb (.inr h'))
      rw [hgs]
      exact hagT i
  · have e : (fun z ↦ g (I.privCell z)) = fun z ↦ f (I.privCell z) := funext hgs
    have e' : (fun z ↦ g (I.donCell z)) = sD := funext hdon
    rw [e] at hcl ⊢
    rw [e']
    obtain ⟨hZ, hFF, hTT⟩ := hsDT hcl
    refine ⟨fun z hz ↦ ?_, hFF, fun y hy ↦ ?_⟩
    · rw [hdon, hgs]
      exact hZ z hz
    · rw [hdon]
      exact hTT y hy

/-- **The lift provision at the cap `⊥` from the coatom of `T`**, with block labels: the raise. -/
theorem botProvisionB_left (hdT : I.left.HasDeadLowCells) (hraise : c.HasRaiseFromD)
    {f : Fin I.lowerFieldLayer.card → Label.{u}}
    (hf : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) (fun d ↦ f d)) :
    ∃ W : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.last 2), 2), W d = f d) ∧
      I.admD c (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsT := isLawful_privOf hf
  obtain ⟨sD, hsD, hZ, hTT, hFF⟩ := hraise _ hsT
  obtain ⟨v, hv, hvs⟩ := exists_coatom_labelling I.restrictFace_right
    (Coatom.univ_map_right (m := 1)) hsD
  obtain ⟨w, hwU, hwV, hwv, -⟩ := exists_gradeOne hxyB.symm hyB hxB (isSelfVisible_bot 2) hv
    (CellScheme.Rows.isLawful_const_bot (R := I.lowerFieldLayer.rows))
    fun _ _ ↦ by rw [min_bot_right, min_bot_right]
  have hsw (i : Fin I.left.card) (hi : I.left.toCellScheme.grade i = 1) :
      f (I.privCell i) = w (I.privCell i) :=
    (hdT.eq_bot hsT hi).trans (eq_bot_privCell_of_dead hdT hwV hi).symm
  obtain ⟨g, hg, hgw, hgs⟩ := exists_assemble hxyB.symm hyB hxB I.restrictFace_left
    (Coatom.univ_map_left (m := 1)) hwU hwV hsT hsw
  have hdon (z : Fin I.right.card) : g (I.donCell z) = sD z :=
    (hgw _ (.inl (donCell_mem_below z))).trans ((hwv _ (donCell_mem_below z)).trans (hvs z))
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_, admD_orbitCode_block fun _ ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := exists_faceCell_of_mem_below I.restrictFace_left
      (Coatom.univ_map_left (m := 1)) hd
    exact hgs z
  · have e : (fun z ↦ g (I.privCell z)) = fun z ↦ f (I.privCell z) := funext hgs
    have e' : (fun z ↦ g (I.donCell z)) = sD := funext hdon
    rw [e, e']
    refine ⟨fun z hz ↦ ?_, hFF, fun y hy ↦ by rw [hdon]; exact hTT y hy⟩
    rw [hdon, hZ z hz, min_bot_left]

/-- **The lift provision at a positive cap from the coatom of `D`**, with block labels: the copy
on `T` is the lift of `T` from its dead cells of grade `1`, capped at `h` at grade `2`. -/
theorem capProvisionB_right (hT : I.left.IsLegal) (hdT : I.left.HasDeadLowCells)
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
  have heT := isLawful_privOf (ha.isLawfulBelow (univ.erase (Fin.last 2), 2))
  have hagD (i : Fin I.right.card) : min (f (I.donCell i)) h = min (a (I.donCell i)) h :=
    hfa _ (donCell_mem_below i)
  obtain ⟨w, hwU, hwV, hwf, hwa⟩ := exists_gradeOne hxyB.symm hyB hxB hh hf ha hfa
  obtain ⟨r, hr, hrp, hra⟩ := StageType.exists_lift_one_two hT (p := fun _ ↦ ⊥)
    (q := fun i ↦ a (I.privCell i)) (CellScheme.Rows.isLawful_const_bot (R := I.left.rows))
    heT hh fun z hz ↦ by
      show min ⊥ h = min (a (I.privCell z)) h
      rw [hdT.eq_bot heT hz]
  have hsT := StageType.isLawful_capTwo hr hh
  have hsw (i : Fin I.left.card) (hi : I.left.toCellScheme.grade i = 1) :
      (if I.left.toCellScheme.grade i = 2 then min (r i) h else r i) = w (I.privCell i) := by
    simp only [show I.left.toCellScheme.grade i ≠ 2 by omega, ↓reduceIte]
    exact (hrp i hi).trans (eq_bot_privCell_of_dead hdT hwV hi).symm
  have hsTa (i : Fin I.left.card) :
      min (if I.left.toCellScheme.grade i = 2 then min (r i) h else r i) h =
        min (a (I.privCell i)) h := by
    split_ifs
    · rw [min_assoc, min_self, hra]
    · exact hra i
  obtain ⟨g, hg, hgw, hgs⟩ := exists_assemble hxyB.symm hyB hxB I.restrictFace_left
    (Coatom.univ_map_left (m := 1)) hwU hwV hsT hsw
  have hdon (z : Fin I.right.card) : g (I.donCell z) = f (I.donCell z) :=
    (hgw _ (.inl (donCell_mem_below z))).trans (hwf _ (donCell_mem_below z))
  refine ⟨g, hg.isLawfulBelow _, fun d hd' ↦ (hgw d (.inl hd')).trans (hwf d hd'),
    fun d _ ↦ ?_, admD_orbitCode_block fun hcl ↦ ?_⟩
  · by_cases hb' : d ∈ I.lowerFieldLayer.toCellScheme.below
        (univ.erase (Fin.castSucc (Fin.last 1)), 2) ∨
        d ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1)
    · rw [hgw d hb']
      rcases hb' with hb' | hb'
      · rw [hwf d hb']
        exact hfa d hb'
      · exact hwa d hb'
    · obtain ⟨i, rfl⟩ := exists_faceCell_of_mem_below I.restrictFace_left
        (Coatom.univ_map_left (m := 1))
        (((mem_below_three hxyB.symm hyB hxB d).resolve_left fun h' ↦ hb' (.inl h')).resolve_left
          fun h' ↦ hb' (.inr h'))
      rw [hgs]
      exact hsTa i
  · set sT : Fin I.left.card → Label.{u} :=
      fun z ↦ if I.left.toCellScheme.grade z = 2 then min (r z) h else r z with hsTdef
    have e : (fun z ↦ g (I.privCell z)) = sT := funext hgs
    have e' : (fun z ↦ g (I.donCell z)) = fun z ↦ f (I.donCell z) := funext hdon
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
      rw [show (if I.left.toCellScheme.grade c.cap = 2 then min (r c.cap) h else r c.cap) =
        sT c.cap from rfl, min_eq_left hcapL] at e1
      exact e1.symm ▸ min_le_left _ _
    have hvR (z : Fin I.left.card) :
        min (visibilityReplace 2 1 (sT z)) h = min (visibilityReplace 2 1 (a (I.privCell z))) h :=
      Label.min_visibilityReplace_two_eq hh (by omega) (hsTa z)
    -- reduce under the cap `sT b ≤ h`
    have hred (x y : Label.{u}) (hxy : min x h = min y h) (hyz : min y (a (I.privCell c.cap)) = ⊥) :
        min x (sT c.cap) = ⊥ := by
      refine le_bot_iff.mp ?_
      calc min x (sT c.cap) = min (min x h) (sT c.cap) := by rw [min_assoc, min_eq_right hcapL]
        _ = min (min y h) (sT c.cap) := by rw [hxy]
        _ = min y (sT c.cap) := by rw [min_assoc, min_eq_right hcapL]
        _ ≤ min y (a (I.privCell c.cap)) := min_le_min_left _ hcapE
        _ = ⊥ := hyz
        _ ≤ ⊥ := le_rfl
    refine ⟨fun z hz ↦ ?_, fun g' h1 h2 ↦ ?_, fun y hy ↦ ?_⟩
    · rw [hdon, hgs]
      exact hred _ _ (hagD z) (eq_bot_of_isCorrectD hcorr hz)
    · have hE := donorExact_of_isCorrect hcorr g' h1 h2
      calc min (f (I.donCell g')) (sT c.cap)
          = min (min (f (I.donCell g')) h) (sT c.cap) := by rw [min_assoc, min_eq_right hcapL]
        _ = min (min (a (I.donCell g')) h) (sT c.cap) := by rw [hagD]
        _ = min (min (a (I.donCell g')) (a (I.privCell c.cap))) (sT c.cap) := by
            rw [min_assoc, min_eq_right hcapL, min_assoc, min_eq_right hcapE]
        _ = min (min (visibilityReplace 2 1 (a (I.privCell (c.ref g'))))
            (a (I.privCell c.cap))) (sT c.cap) := by rw [hE]
        _ = min (min (visibilityReplace 2 1 (a (I.privCell (c.ref g')))) h) (sT c.cap) := by
            rw [min_assoc, min_eq_right hcapE, min_assoc, min_eq_right hcapL]
        _ = min (min (visibilityReplace 2 1 (sT (c.ref g'))) h) (sT c.cap) := by rw [hvR]
        _ = min (visibilityReplace 2 1 (sT (c.ref g'))) (sT c.cap) := by
            rw [min_assoc, min_eq_right hcapL]
    · rw [hdon]
      have hle := (DonorCap.value_le_cap (c := c) sT).trans hcapL
      calc c.value sT = min (c.value sT) h := (min_eq_left hle).symm
        _ = min (c.value fun z ↦ a (I.privCell z)) h := DonorCap.min_value_eq hh hsTa
        _ ≤ min (a (I.donCell y)) h := min_le_min_right _ (le_of_isCorrectD hcorr hy)
        _ = min (f (I.donCell y)) h := (hagD y).symm
        _ ≤ f (I.donCell y) := min_le_left _ _

/-- **The lift provision at the cap `⊥` from the coatom of `D`**, with block labels. -/
theorem botProvisionB_right (hT : I.left.IsLegal) (hdT : I.left.HasDeadLowCells)
    (hb : I.left.toCellScheme.grade c.cap = 2) {f : Fin I.lowerFieldLayer.card → Label.{u}}
    (hf : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2)
      (fun d ↦ f d)) :
    ∃ W : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2),
        W d = f d) ∧
      I.admD c (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  obtain ⟨w, hwU, hwV, hwf, -⟩ := exists_gradeOne hxyB.symm hyB hxB (isSelfVisible_bot 2) hf
    (CellScheme.Rows.isLawful_const_bot (R := I.lowerFieldLayer.rows))
    fun _ _ ↦ by rw [min_bot_right, min_bot_right]
  obtain ⟨r, hr, hrp, -⟩ := StageType.exists_lift_one_two hT (p := fun _ ↦ ⊥)
    (q := fun _ ↦ ⊥) (CellScheme.Rows.isLawful_const_bot (R := I.left.rows))
    (CellScheme.Rows.isLawful_const_bot (R := I.left.rows)) (isSelfVisible_bot 2)
    fun _ _ ↦ rfl
  have hsT := StageType.isLawful_capTwo hr (isSelfVisible_bot 2)
  have hsw (i : Fin I.left.card) (hi : I.left.toCellScheme.grade i = 1) :
      (if I.left.toCellScheme.grade i = 2 then min (r i) ⊥ else r i) = w (I.privCell i) := by
    simp only [show I.left.toCellScheme.grade i ≠ 2 by omega, ↓reduceIte]
    exact (hrp i hi).trans (eq_bot_privCell_of_dead hdT hwV hi).symm
  obtain ⟨g, hg, hgw, hgs⟩ := exists_assemble hxyB.symm hyB hxB I.restrictFace_left
    (Coatom.univ_map_left (m := 1)) hwU hwV hsT hsw
  have hcap : g (I.privCell c.cap) = ⊥ := by
    rw [hgs]
    simp only [hb, ↓reduceIte, min_bot_right]
  refine ⟨g, hg.isLawfulBelow _, fun d hd' ↦ (hgw d (.inl hd')).trans (hwf d hd'),
    admD_orbitCode_block fun _ ↦ ⟨fun z _ ↦ by rw [hcap, min_bot_right], fun _ _ _ ↦ ?_,
      fun y _ ↦ ?_⟩⟩
  · change min _ (g (I.privCell c.cap)) = min _ (g (I.privCell c.cap))
    rw [hcap, min_bot_right, min_bot_right]
  · exact ((DonorCap.value_le_cap (c := c) _).trans hcap.le).trans bot_le

/-! ### Legality -/

private theorem erase_ne_univB (x : Fin 3) : univ.erase x ≠ univ :=
  fun he ↦ Finset.notMem_erase x univ (he.symm ▸ mem_univ x)

private theorem exists_gradedIndex_left_twoB :
    ∃ c, I.lowerFieldLayer.toCellScheme.gradedIndex c = (univ.erase (Fin.last 2), 2) := by
  obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq (univ.erase (Fin.last 2), 2)
    ⟨I.erase_last_mem_faces, two_pos, by decide⟩ (erase_ne_univB _)
  exact ⟨Fin.castAdd _ d, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd⟩

private theorem exists_gradedIndex_right_twoB :
    ∃ c, I.lowerFieldLayer.toCellScheme.gradedIndex c =
      (univ.erase (Fin.castSucc (Fin.last 1)), 2) := by
  obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq (univ.erase (Fin.castSucc (Fin.last 1)), 2)
    ⟨I.erase_castSucc_mem_faces, two_pos, by decide⟩ (erase_ne_univB _)
  exact ⟨Fin.castAdd _ d, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd⟩

/-- **The admitted completion with a donor labelled in blocks.**  For a seed with coatom types `T`
and `D` (`T` legal), donor data with the cap of grade `2` in `T`, `T` with dead cells of grade
`1`, the raise from `T` into `D` and the capped exact lift, the admitted layer at the grade `2`
over the canonical lower layer is legal below the full grade. -/
theorem isLegalBelowFullGrade_donorLayer_block (hT : I.left.IsLegal)
    (hb : I.left.toCellScheme.grade c.cap = 2) (hdT : I.left.HasDeadLowCells)
    (hraise : c.HasRaiseFromD) (hexact : c.HasExactLiftD) :
    (I.donorLayer c).IsLegalBelowFullGrade :=
  let L1 := Scheme.cappedLift_admittedFieldLayer (j := 1)
    (hS := I.not_univ_two_le_lowerFieldLayer) I.isConsistent_lowerFieldLayer
    (CapRequests.admits_bot _ _ _) (erase_ne_univB _) exists_gradedIndex_left_twoB
    (I.cappedLift_lowerFieldLayer hxyB hxB hyB)
    (fun _ hf ↦ botProvisionB_left (c := c) hdT hraise hf)
    (fun _ hh _ hbh _ ha hA _ hf hfa ↦ capProvisionB_left hdT hraise hexact hh hbh ha hA hf hfa)
  let L2 := Scheme.cappedLift_admittedFieldLayer (j := 1)
    (hS := I.not_univ_two_le_lowerFieldLayer) I.isConsistent_lowerFieldLayer
    (CapRequests.admits_bot _ _ _) (erase_ne_univB _) exists_gradedIndex_right_twoB
    (I.cappedLift_lowerFieldLayer hxyB.symm hyB hxB)
    (fun _ hf ↦ botProvisionB_right (c := c) hT hdT hb hf)
    (fun _ hh _ hbh _ ha hA _ hf hfa ↦ capProvisionB_right hT hdT hb hh hbh ha hA hf hfa)
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

end Seed

/-! ### References on a type with dead cells of grade `1` -/

/-- **The replacement at the offset `1` of a reference on a type with dead cells of grade `1` is
never `1`**: the reference is `⊥` (grade `1`) or self-visible at `2` (grade `2`). -/
theorem StageType.visibilityReplace_ne_one {α : Ordinal.{u}} {T : StageType.{u} α 2}
    (hd : T.HasDeadLowCells) {s : Fin T.card → Label.{u}} (hs : T.rows.IsLawful s)
    (r : Fin T.card) : visibilityReplace 2 1 (s r) ≠ ((1 : ℕ) : Label.{u}) := by
  rcases grade_one_or_two' r with h1 | h2
  · rw [hd.eq_bot hs h1, visibilityReplace_bot]
    exact (natCast_label_ne_bot 1).symm
  · have hvs : IsSelfVisible 2 (s r) := h2 ▸ hs.orderly r
    rw [hvs.visibilityReplace_eq]
    intro h
    have h' := hvs.visibilityReplace_eq 2
    rw [h, Label.visibilityReplace_natCast] at h'
    simp only [show (1 : ℕ) < 2 by omega, ↓reduceIte, Nat.cast_inj] at h'
    omega

/-! ### The instance: the private type as input, the coupled-gate type as donor -/

namespace DonorPair

/-- The shifter sending every label other than `⊥` to `⊤`. -/
private noncomputable def toTop (v : Label.{u}) : Label.{u} := by
  classical
  exact if v = ⊥ then ⊥ else ⊤

private theorem toTop_bot : toTop (⊥ : Label.{u}) = ⊥ := by simp [toTop]

private theorem toTop_of_ne {v : Label.{u}} (hv : v ≠ ⊥) : toTop v = ⊤ := by simp [toTop, hv]

private theorem isWitness_toTop : IsWitness (stepSuppressor 2) (toTop : Label.{u} → Label.{u}) where
  antitone := (IsWitness.id_step 2).antitone
  isSelfVisible := (IsWitness.id_step 2).isSelfVisible
  map_bot := toTop_bot
  monotone := by
    intro x y hxy
    by_cases hx : x = ⊥
    · rw [hx, toTop_bot]
      exact bot_le
    · have hy : y ≠ ⊥ := fun h ↦ hx (le_bot_iff.mp (h ▸ hxy))
      rw [toTop_of_ne hx, toTop_of_ne hy]
  visibilityReplace_comm x k _ i _ := by
    by_cases hx : x = ⊥
    · rw [hx, visibilityReplace_bot, toTop_bot, visibilityReplace_bot]
    · rw [toTop_of_ne (fun h ↦ hx (visibilityReplace_eq_bot_iff.mp h)), toTop_of_ne hx,
        visibilityReplace_top]

variable (α : Ordinal.{u}) (hα : 1 < α)

private theorem availability_casesCP : ∀ s t : Fin 5,
    CoupledGatedExtensionCounterexample.cellScope s ⊆
      CoupledGatedExtensionCounterexample.cellScope t →
    CoupledGatedExtensionCounterexample.cellGrade s =
      CoupledGatedExtensionCounterexample.cellGrade t →
    (s = 0 ∨ s = 1) ∨ (CoupledGatedExtensionCounterexample.cellScope t =
      CoupledGatedExtensionCounterexample.cellScope s ∧
        CoupledGatedExtensionCounterexample.cellGrade t =
          CoupledGatedExtensionCounterexample.cellGrade s) := by
  decide

/-- **The constant labelling `⊥, ⊥, ⊤, ⊤, ⊤` of the coupled-gate type is lawful**: every row read
with the shifter sending the labels other than `⊥` to `⊤`. -/
theorem isLawful_lab_top :
    (CoupledGatedExtensionCounterexample.P α hα).rows.IsLawful
      (CoupledGatedExtensionCounterexample.lab ⊤ ⊤ ⊤) where
  orderly d := by
    fin_cases d
    exacts [isSelfVisible_bot _, isSelfVisible_bot _, isSelfVisible_top _, isSelfVisible_top _,
      isSelfVisible_top _]
  locality s := by
    fin_cases s
    · exact ⟨fun _ ↦ ⊤, fun _ ↦ ⊥, IsWitness.bot_top, fun d ↦ by
        change min _ ⊥ = min ⊥ ⊤
        rw [min_bot_right, min_bot_left]⟩
    · exact ⟨fun _ ↦ ⊤, fun _ ↦ ⊥, IsWitness.bot_top, fun d ↦ by
        change min _ ⊥ = min ⊥ ⊤
        rw [min_bot_right, min_bot_left]⟩
    all_goals
      refine ⟨stepSuppressor 2, toTop, isWitness_toTop, fun d ↦ ?_⟩
      obtain ⟨d, hd⟩ := d
      fin_cases d
      all_goals first
        | exact absurd hd.2 (by change ¬ ((2 : ℕ) ≤ 1); omega)
        | (change min ⊥ _ = min (toTop ⊥) _; rw [toTop_bot, min_bot_left, min_bot_left])
        | (change min ⊤ ⊤ = min (toTop ((1 : ℕ) : Label.{u})) ⊤
           rw [toTop_of_ne (natCast_label_ne_bot 1)])
  availability s t hst hg := by
    rcases availability_casesCP s t hst hg with hs | ⟨h1, h2⟩
    · refine ⟨t, rfl, ?_⟩
      rcases hs with rfl | rfl <;> exact bot_le
    · exact ⟨s, Prod.ext h1.symm h2.symm, le_rfl⟩

/-- **The seed of the private type `T = P` and the coupled-gate type `D`** over their common
face. -/
noncomputable abbrev seedDT : Seed.{u} α 1 :=
  Seed.ofCoatoms (GatedExtensionCounterexample.isLegal_P α)
    (CoupledGatedExtensionCounterexample.isLegal_P α hα) (restrictFace_eq α hα)
    (restrictFace_of_mem _ _ (CoupledGatedExtensionCounterexample.mem_faces_castSuccEmb α hα))

/-- **Donor data with a cell labelled in a block**: cap and marker the full cell `4` of `T = P`,
the reference of every cell of `D` the cap, bottom class `{0, 1, 2}`. -/
def capDT (R : ℕ) (hR : R < 2) : (seedDT α hα).DonorCap where
  cap := ((4 : Fin 5) : Fin (GatedExtensionCounterexample.P α).card)
  marker := ((4 : Fin 5) : Fin (GatedExtensionCounterexample.P α).card)
  R := R
  R_lt_two := hR
  ref _ := ((4 : Fin 5) : Fin (GatedExtensionCounterexample.P α).card)
  botCells := ({0, 1, 2} : Set (Fin 5))

/-- **The raise into the coupled-gate type**: the constant labelling `⊥, ⊥, ⊤, ⊤, ⊤`. -/
theorem hasRaiseFromD_DT (R : ℕ) (hR : R < 2) : (capDT α hα R hR).HasRaiseFromD := by
  intro sT hsT
  have hvs : IsSelfVisible 2 (sT (capDT α hα R hR).cap) := hsT.orderly _
  refine ⟨CoupledGatedExtensionCounterexample.lab ⊤ ⊤ ⊤, isLawful_lab_top α hα, ?_, ?_, ?_⟩
  · change ∀ z : Fin 5, CoupledGatedExtensionCounterexample.lab 1 ⊤ ⊤ z = ⊥ →
      CoupledGatedExtensionCounterexample.lab ⊤ ⊤ ⊤ z = ⊥
    intro z hz
    fin_cases z
    all_goals first
      | rfl
      | exact absurd hz (by simp [CoupledGatedExtensionCounterexample.lab])
  · intro y _
    revert y
    change ∀ y : Fin 5, CoupledGatedExtensionCounterexample.lab 1 ⊤ ⊤ y = ⊤ →
      _ ≤ CoupledGatedExtensionCounterexample.lab ⊤ ⊤ ⊤ y
    intro y hy
    fin_cases y
    all_goals first
      | exact le_top
      | exact absurd hy (by simp [CoupledGatedExtensionCounterexample.lab])
  · have key : ∀ f : Fin 5, CoupledGatedExtensionCounterexample.lab 1 ⊤ ⊤ f ≠ ⊥ →
        CoupledGatedExtensionCounterexample.lab 1 ⊤ ⊤ f ≠ ⊤ →
          CoupledGatedExtensionCounterexample.lab (⊤ : Label.{u}) ⊤ ⊤ f = ⊤ := by
      intro f h1 h2
      fin_cases f
      all_goals first
        | exact absurd rfl h1
        | exact absurd rfl h2
        | rfl
    intro f h1 h2
    have hf : CoupledGatedExtensionCounterexample.lab (⊤ : Label.{u}) ⊤ ⊤ f = ⊤ := key f h1 h2
    change min (CoupledGatedExtensionCounterexample.lab ⊤ ⊤ ⊤ f) (sT (capDT α hα R hR).cap) =
      min (visibilityReplace 2 1 (sT (capDT α hα R hR).cap)) (sT (capDT α hα R hR).cap)
    rw [hf, min_top_left, hvs.visibilityReplace_eq, min_self]

/-- **The admitted layer with the coupled-gate type as donor is legal below the full grade** (a
donor with a cell `z₁` of grade `1` labelled `1`, read from the cap of `T = P`). -/
theorem isLegalBelowFullGrade_donorLayer_DT (R : ℕ) (hR : R < 2) :
    ((seedDT α hα).donorLayer (capDT α hα R hR)).IsLegalBelowFullGrade :=
  Seed.isLegalBelowFullGrade_donorLayer_block (GatedExtensionCounterexample.isLegal_P α) rfl
    (GatedExtensionCounterexample.hasDeadLowCells_P α) (hasRaiseFromD_DT α hα R hR)
    (Seed.hasExactLiftD_of_marker_eq_cap rfl rfl)

/-- **No reading back of the block label `1`**: every correct state of the pair whose copy of `T`
is lawful reads the copy of `z₁` other than `1`; so no stage type on a scheme with these requests
recovers the label `1` of `z₁`. -/
theorem donCell_ne_one_DT (R : ℕ) (hR : R < 2)
    {g : Fin (seedDT α hα).lowerFieldLayer.card → Label.{u}}
    (hc : ((seedDT α hα).requestsD (capDT α hα R hR)).IsCorrect g)
    (hcap : g ((seedDT α hα).privCell ((4 : Fin 5) :
      Fin (GatedExtensionCounterexample.P α).card)) = ⊤)
    (hT : (GatedExtensionCounterexample.P α).rows.IsLawful
      fun z ↦ g ((seedDT α hα).privCell z)) :
    g ((seedDT α hα).donCell ((2 : Fin 5) :
      Fin (CoupledGatedExtensionCounterexample.P α hα).card)) ≠ ((1 : ℕ) : Label.{u}) := by
  have hE : min (g ((seedDT α hα).donCell ((2 : Fin 5) :
      Fin (CoupledGatedExtensionCounterexample.P α hα).card)))
      (g ((seedDT α hα).privCell (capDT α hα R hR).cap)) =
      min (visibilityReplace 2 1 (g ((seedDT α hα).privCell (capDT α hα R hR).cap)))
        (g ((seedDT α hα).privCell (capDT α hα R hR).cap)) :=
    Seed.donorExact_of_isCorrect hc _
      (by change (1 : Label.{u}) ≠ ⊥; exact WithBot.coe_ne_bot)
      (by
        change (1 : Label.{u}) ≠ ⊤
        exact fun h ↦ WithTop.coe_ne_top (WithBot.coe_injective h))
  have hcap' : g ((seedDT α hα).privCell (capDT α hα R hR).cap) = ⊤ := hcap
  rw [hcap', min_top_right, min_top_right] at hE
  rw [hE, ← hcap']
  exact StageType.visibilityReplace_ne_one (GatedExtensionCounterexample.hasDeadLowCells_P α) hT _

end DonorPair

end VaughtConjecture
