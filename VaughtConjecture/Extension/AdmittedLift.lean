/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Admission

/-!
# The capped lifts of an admitted profile layer

Roadmap, Layer 3, 3.1, (R6), the completion below the full grade with a restricted catalogue at the
reading grades; third piece (bountifulness of an admitted layer).

Let `L` be a good level at the grade `g` of the tower of rank-normalized profiles of a seed `I`,
`k = g + 1 ≤ m + 1`, `A` an admission and `C` the admitted catalogue at `k`.  The admitted layer
`L.admittedNextS A` (`ProfileTower.Lvl.admittedNextS`) appends one cell of full scope and grade `k`
per admitted profile.  Its lifts below pairs not above `(univ, k)` are those of the level
(`ProfileTower.Lvl.cappedLift_nextSOn_iff`).  This file proves the **lift from either coatom into
`(univ, k)`** (`ProfileTower.Lvl.Good.cappedLift_admittedNextS`) under two **lift provisions** at
the coatom `C = univ.erase x`:

* **at the cap `⊥`** (`ProfileTower.BotLiftProvision`): every profile `f` lawful below `(C, k)`
  agrees below `(C, k)` with a profile `W` lawful on the grade-`k` cut whose code at `k`
  (`ProfileTower.code`, the orbit code of the splice) is admitted;
* **at the positive caps** (`ProfileTower.CapLiftProvision`): for every cap `h` self-visible and
  short at `k`, every admitted profile `P` and every `f` lawful below `(C, k)` agreeing with `P`
  capped at `h` below `(C, k)`, some `W` lawful on the cut agrees with `f` below `(C, k)`, with `P`
  capped at `h` everywhere, and has its orbit code at `k` admitted.

The other coatom is not prescribed: the provision chooses the cells of `D \ C` of grade `k`.

**The two extensions through an admitted layer.**  For a sub-catalogue `C` of the catalogue at `k`:

* at `⊥` (`ProfileTower.Lvl.Good.exists_extensionOn_bot`): if the code of `W` lies in `C`, the row
  labelling of the code read by the orbit decoder of the splice of `W` at the least grid point is
  lawful below `(univ, k)` and reads `W` at the old cells of grade at most `k`;
* at a positive cap `h` (`ProfileTower.Lvl.Good.exists_extensionOn`): if the orbit code of `W` lies
  in `C` and `W` agrees with a profile `P ∈ C` capped at `h`, the row labelling of the orbit code
  read by the orbit decoder of `W` at `h` is lawful, reads `W` at the old cells of grade at most `k`
  and agrees with the row labelling of `P` capped at `h`.

Both transport one row section of the layer by a witness that sends only `⊥` to `⊥`
(`CellScheme.Rows.IsLawfulBelow.map_of_apply_eq_bot`).  The old cells are read literally, because
the provision has put the whole boundary profile into the catalogue: the old cells off `C` are
chosen by the provision, not prescribed.

**The lift** is the one-grade lift `CellScheme.Rows.cappedLift_of_ownerCappedLift`: at `⊥` the
prescription capped at its owner is a profile lawful below `(C, k)`, extended by the provision and
`exists_extensionOn_bot`; at a positive cap, owner-capped lifts come from the serving rows
(`CellScheme.Rows.hasOwnerCappedLifts_of_rows_short`), whose lifts at the short caps are given by
the provision and `exists_extensionOn`.

**The trivial admission** (`Seed.Admission.all`) has both provisions, by the lift of the amalgam
within the other coatom from the common face (`ProfileTower.botLiftProvision_all`,
`ProfileTower.capLiftProvision_all`); on the whole catalogue the admitted layer is the canonical
next level (`ProfileTower.Lvl.admittedNextS_all`), whose lift is
`ProfileTower.Lvl.Good.cappedLift_next`.

## Placement

The engine of the restricted catalogue at the reading grades (`roadmap/README.md`, Layer 3, 3.1,
under "(R6)"); third piece.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-! ### The lift provisions -/

/-- **The lift provision at the cap `⊥`** at the grade `k` and the coatom `univ.erase x`, for a
catalogue `C`: every profile lawful below the coatom agrees below it with a profile lawful on the
grade-`k` cut whose code at `k` lies in `C`. -/
def BotLiftProvisionIn (C : Finset (Prof I)) (k : ℕ) (x : Fin (m + 2)) : Prop :=
  ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase x, k) (fun d ↦ f d) →
    ∃ W : Prof I, IsCutLawful I k W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, k), W d = f d) ∧ code k W ∈ C

/-- **The lift provision at the positive caps** at the grade `k` and the coatom `univ.erase x`, for
a catalogue `C`: for every cap `h` self-visible and short at `k`, every profile `P` of `C` and every
profile `f` lawful below the coatom agreeing with `P` capped at `h` below it, some profile lawful
on the grade-`k` cut agrees with `f` below the coatom and with `P` capped at `h` everywhere, and
has its orbit code at `k` in `C`. -/
def CapLiftProvisionIn (C : Finset (Prof I)) (k : ℕ) (x : Fin (m + 2)) : Prop :=
  ∀ h : Label.{u}, IsSelfVisible k h → IsShort k h → ⊥ < h → ∀ P ∈ C,
    ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase x, k) (fun d ↦ f d) →
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, k), min (f d) h = min (P d) h) →
      ∃ W : Prof I, IsCutLawful I k W ∧
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, k), W d = f d) ∧
        (∀ d, min (W d) h = min (P d) h) ∧ orbitCode k W ∈ C

/-- **The lift provision at the cap `⊥`** for a predicate `Rw` on states: for its catalogue. -/
abbrev BotLiftProvisionOf (Rw : I.State → Prop) (k : ℕ) (x : Fin (m + 2)) : Prop :=
  BotLiftProvisionIn (rowCat Rw k) k x

/-- **The lift provision at the positive caps** for a predicate `Rw` on states: for its
catalogue. -/
abbrev CapLiftProvisionOf (Rw : I.State → Prop) (k : ℕ) (x : Fin (m + 2)) : Prop :=
  CapLiftProvisionIn (rowCat Rw k) k x

/-- **The lift provision at the cap `⊥`** for an admission: for its reading rows. -/
abbrev BotLiftProvision (A : I.Admission) (k : ℕ) (x : Fin (m + 2)) : Prop :=
  BotLiftProvisionOf A.Row k x

/-- **The lift provision at the positive caps** for an admission: for its reading rows. -/
abbrev CapLiftProvision (A : I.Admission) (k : ℕ) (x : Fin (m + 2)) : Prop :=
  CapLiftProvisionOf A.Row k x

section Step

variable {g : ℕ} {L : Lvl I g} {C : Finset (Prof I)} {D : ℕ → Finset (Prof I)}

/-! ### The old cells of the layer on a sub-catalogue -/

theorem Lvl.GoodOn.gradedIndex_embedOn (hL : L.GoodOn D) (d : Fin I.amalgam.card) :
    (L.nextSOn C).toCellScheme.gradedIndex (L.embedOn C d) =
      I.amalgam.toCellScheme.gradedIndex d :=
  (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans (hL.gradedIndex_embed d)

/-- A cell of the layer on `C` below a pair off the ground set is an old cell of the amalgam below
that pair. -/
theorem Lvl.GoodOn.exists_embedOn_eq (hL : L.GoodOn D) {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X.1 ≠ univ) {z : Fin (L.nextSOn C).card} (hz : z ∈ (L.nextSOn C).toCellScheme.below X) :
    ∃ d ∈ I.amalgam.toCellScheme.below X, L.embedOn C d = z := by
  induction z using Fin.addCases with
  | right j =>
    have h : (L.S.appendFullCellsScheme (g + 1) C.card).scope (Fin.natAdd _ j) ⊆ X.1 := hz.1
    rw [Scheme.appendFullCellsScheme_scope_natAdd] at h
    exact absurd (univ_subset_iff.mp h) hX
  | left e =>
    have hne : L.S.toCellScheme.scope e ≠ univ := fun he ↦ by
      have h : (L.S.appendFullCellsScheme (g + 1) C.card).scope (Fin.castAdd _ e) ⊆ X.1 := hz.1
      rw [Scheme.appendFullCellsScheme_scope_castAdd, he] at h
      exact hX (univ_subset_iff.mp h)
    obtain ⟨d, rfl⟩ := hL.mem_range e hne
    refine ⟨d, ?_, rfl⟩
    rw [CellScheme.mem_below, ← hL.gradedIndex_embedOn (C := C)]
    exact hz

/-- Lawfulness below a pair off the ground set in the layer on `C` is lawfulness in the amalgam,
along the old cells. -/
theorem Lvl.GoodOn.isLawfulBelow_embedOn_iff (hL : L.GoodOn D) {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X.1 ≠ univ) {v : Fin (L.nextSOn C).card → Label.{u}} :
    (L.nextSOn C).rows.IsLawfulBelow X (fun z ↦ v z) ↔
      I.amalgam.rows.IsLawfulBelow X (fun d ↦ v (L.embedOn C d)) := by
  have hX' : ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ X := fun h ↦ hX (univ_subset_iff.mp h.1)
  exact (Lvl.isLawfulBelow_nextSOn_iff hX').trans
    (hL.isLawfulBelow_old_iff hX (w := fun e ↦ v (Fin.castAdd _ e)))

/-- **Lifts below a pair not above `(univ, g + 1)`** in the layer on `C` are those of the level. -/
theorem Lvl.cappedLift_nextSOn_iff {X Y : Finset (Fin (m + 2)) × ℕ} (hXY : X ≤ Y)
    (hY : ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ Y) :
    (L.nextSOn C).rows.CappedLift hXY ↔ L.S.rows.CappedLift hXY := by
  have h : L.S.toCellScheme.IsSourcePrefix (L.nextSOn C).toCellScheme (Fin.castAdd _) Y :=
    ⟨Scheme.isLowerEmbedding_castAdd (S := L.S) (g + 1) C.card
      (fun i ↦ L.ΦOn C (entryOn C i)) L.not_le,
      Scheme.appendFullCellsScheme_scope_castAdd L.S (g + 1) _,
      fun d hd ↦ ⟨⟨d, Scheme.lt_card_of_mem_below hY hd⟩, rfl⟩⟩
  rw [← h.cappedLift_iff hXY le_rfl, Scheme.comap_rows_castAdd]

/-- An old cell of grade at most `g + 1` lies below `(univ, g + 1)` in the layer on `C`. -/
theorem Lvl.GoodOn.embedOn_mem_below (hL : L.GoodOn D) {d : Fin I.amalgam.card}
    (hd : I.amalgam.toCellScheme.grade d ≤ g + 1) :
    L.embedOn C d ∈ (L.nextSOn C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) := by
  rw [CellScheme.mem_below, hL.gradedIndex_embedOn]
  exact ⟨subset_univ _, hd⟩

/-! ### The two extensions through a layer on a sub-catalogue -/

/-- **Extension at the cap `⊥` through a layer on a sub-catalogue.**  If the code at `g + 1` of a
profile `W` lies in `C ⊆ cat I (g + 1)`, the row labelling of the code, read by the orbit decoder of
the splice of `W` at the least grid point, is lawful below `(univ, g + 1)` and reads `W` at the old
cells of grade at most `g + 1`. -/
theorem Lvl.GoodOn.exists_extensionOn_bot (hL : L.GoodOn D) (hC : C ⊆ cat I (g + 1))
    (hdown : ∀ R ∈ C, code g R ∈ D g) {W : Prof I} (hQ : code (g + 1) W ∈ C) :
    ∃ r : (L.nextSOn C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) → Label.{u},
      (L.nextSOn C).rows.IsLawfulBelow (univ, g + 1) r ∧
      ∀ d (hd : I.amalgam.toCellScheme.grade d ≤ g + 1),
        r ⟨L.embedOn C d, hL.embedOn_mem_below hd⟩ = W d := by
  set W₀ := hat I (g + 1) W
  set Q : Prof I := code (g + 1) W
  have hQW (d : Fin I.amalgam.card) :
      min (Q d) (gridPoint (g + 1) 0) = min (W₀ d) (gridPoint (g + 1) 0) :=
    min_orbitCode_gridPoint_zero d
  refine ⟨fun z ↦ orbitDecoder (g + 1) W₀ (gridPoint (g + 1) 0) (L.ΦOn C Q z),
    (hL.isLawfulBelow_ΦOn (hC hQ) (hdown _ hQ) hQ).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_orbitDecoder (isSelfVisible_gridPoint _ 0) (gridPoint_ne_bot _ 0))
      (fun _ ↦ eq_bot_of_orbitDecoder_eq_bot (gridPoint_ne_bot _ 0)), fun d hd ↦ ?_⟩
  change orbitDecoder (g + 1) W₀ (gridPoint (g + 1) 0)
    (L.ΦOn C Q (Fin.castAdd _ (L.embed d))) = W d
  rw [Lvl.ΦOn_castAdd, hL.literal, orbitDecoder_orbitCode hQW d]
  exact hat_of_le hd

/-- **Extension at a positive cap through a layer on a sub-catalogue.**  Let
`P ∈ C ⊆ cat I (g + 1)`, `h` self-visible and short at `g + 1` other than `⊥`, and `W` a profile
agreeing with `P` capped at `h` whose orbit code at `g + 1` lies in `C`.  The row labelling of the
orbit code, read by the orbit decoder of `W` at `h`, is lawful below `(univ, g + 1)`, reads `W` at
the old cells of grade at most `g + 1`, and agrees with the row labelling of `P` capped at `h`. -/
theorem Lvl.GoodOn.exists_extensionOn (hL : L.GoodOn D) (hC : C ⊆ cat I (g + 1))
    (hdown : ∀ R ∈ C, code g R ∈ D g) {P : Prof I}
    (hP : P ∈ C) {h : Label.{u}} (hh : IsSelfVisible (g + 1) h) (hs : IsShort (g + 1) h)
    (hb : h ≠ ⊥) {W : Prof I} (hQ : orbitCode (g + 1) W ∈ C)
    (hWP : ∀ d, min (W d) h = min (P d) h) :
    ∃ r : (L.nextSOn C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) → Label.{u},
      (L.nextSOn C).rows.IsLawfulBelow (univ, g + 1) r ∧
      (∀ d (hd : I.amalgam.toCellScheme.grade d ≤ g + 1),
        r ⟨L.embedOn C d, hL.embedOn_mem_below hd⟩ = W d) ∧
      ∀ z, min (r z) h = min (L.ΦOn C P z) h := by
  set Q : Prof I := orbitCode (g + 1) W
  have hPc := hC hP
  have hPo := (mem_cat.mp hPc).2
  have hQP (d : Fin I.amalgam.card) : min (Q d) h = min (P d) h :=
    min_orbitCode_eq hh hs hPo hWP d
  have hQW (d : Fin I.amalgam.card) : min (Q d) h = min (W d) h := (hQP d).trans (hWP d).symm
  have hQ3 := hC hQ
  have hQB := mem_codeGrid_of_mem_cat hQ3
  have hag (z : (L.nextSOn C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
      min (orbitDecoder (g + 1) W h (L.ΦOn C Q z)) h = min (L.ΦOn C P z) h := by
    obtain ⟨z, -⟩ := z
    induction z using Fin.addCases with
    | left e =>
      rw [min_orbitDecoder_eq_of_isReadableAt hh hQW (by
          rw [Lvl.ΦOn_castAdd]; exact hL.readable Q orbitCode_orbitCode hQB e),
        Lvl.ΦOn_castAdd, Lvl.ΦOn_castAdd]
      exact hL.capAgree Q P hQB h hh hs hQP e
    | right j =>
      rw [Lvl.ΦOn_natAdd, Lvl.ΦOn_natAdd,
        min_orbitDecoder_eq (isSelfVisible_of_mem_grid (agreementHeight_spec
          (bot_mem_grid _ _) _ _).1)]
      exact min_agreementHeight_eq_of_isShort hh hs
        (fun d ↦ ⟨hQB d, mem_codeGrid_of_mem_cat hPc d⟩) hQP _
  refine ⟨fun z ↦ orbitDecoder (g + 1) W h (L.ΦOn C Q z),
    (hL.isLawfulBelow_ΦOn hQ3 (hdown _ hQ) hQ).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_orbitDecoder hh hb) (fun _ ↦ eq_bot_of_orbitDecoder_eq_bot hb), fun d hd ↦ ?_,
    hag⟩
  change orbitDecoder (g + 1) W h (L.ΦOn C Q (Fin.castAdd _ (L.embed d))) = W d
  rw [Lvl.ΦOn_castAdd, hL.literal, orbitDecoder_orbitCode hQW d]

/-! ### The lift from a coatom into an admitted layer -/


/-- **The capped lift from a coatom into the layer on the catalogue of a predicate `Rw`**, at the
grade `g + 1 ≤ m + 1`, under the lift provisions for `Rw` at `⊥` and at the positive caps for that
coatom: the one-grade lift
`CellScheme.Rows.cappedLift_of_ownerCappedLift`, with the lift of the level at the grade `g`, the
owner-capped lift at `⊥` by the provision at `⊥` and `Lvl.Good.exists_extensionOn_bot`, and the
owner-capped lifts at the positive caps from the serving rows, by the provision at the positive caps
and `Lvl.Good.exists_extensionOn`. -/
theorem Lvl.GoodOn.cappedLift_nextSOn (hL : L.GoodOn D) (hC : C ⊆ cat I (g + 1))
    (hdown : ∀ R ∈ C, code g R ∈ D g) (hgm : g + 1 ≤ m + 1)
    {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2))))
    (hbot : BotLiftProvisionIn C (g + 1) x) (hcap : CapLiftProvisionIn C (g + 1) x) :
    (L.nextSOn C).rows.CappedLift (X := (univ.erase x, g + 1))
      (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  classical
  have hne : (univ.erase x, g + 1).1 ≠ univ := Seed.ne_univ_erase x
  have hcard : #(univ.erase x) = m + 1 := Seed.card_erase x
  have hlift : (L.nextSOn C).rows.CappedLift (X := (univ.erase x, g))
      (Y := ((univ : Finset (Fin (m + 2))), g)) ⟨erase_subset _ _, le_rfl⟩ :=
    (Lvl.cappedLift_nextSOn_iff _ fun h ↦ absurd h.2 (by simp only; omega)).mpr
      (hL.lift x hx g le_rfl)
  obtain ⟨c₀, hc₀⟩ := I.exists_gradedIndex_eq (univ.erase x, g + 1)
    ⟨I.erase_mem_faces hx, by omega, show g + 1 ≤ #(univ.erase x) by rw [hcard]; omega⟩
    (Seed.ne_univ_erase x)
  have hX : ∃ c, (L.nextSOn C).toCellScheme.gradedIndex c = (univ.erase x, g + 1) :=
    ⟨L.embedOn C c₀, (hL.gradedIndex_embedOn c₀).trans hc₀⟩
  -- The prescription below the coatom, read on the amalgam.
  have hold (p : (L.nextSOn C).toCellScheme.below (univ.erase x, g + 1) → Label.{u})
      (hp : (L.nextSOn C).rows.IsLawfulBelow (univ.erase x, g + 1) p) :
      I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1)
        (fun d ↦ Rows.extendBot (univ.erase x, g + 1) p (L.embedOn C d)) :=
    (hL.isLawfulBelow_embedOn_iff hne).mp (Rows.isLawfulBelow_extendBot.mpr hp)
  -- A cell below the coatom is an old cell, read through the prescription.
  have hread (p : (L.nextSOn C).toCellScheme.below (univ.erase x, g + 1) → Label.{u})
      (e : (L.nextSOn C).toCellScheme.below (univ.erase x, g + 1)) :
      ∃ d ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1),
        ∃ hd : I.amalgam.toCellScheme.grade d ≤ g + 1,
        (⟨L.embedOn C d, hL.embedOn_mem_below hd⟩ :
          (L.nextSOn C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) =
            Set.inclusion ((L.nextSOn C).toCellScheme.below_mono
              (show ((univ.erase x, g + 1) : Finset (Fin (m + 2)) × ℕ) ≤ (univ, g + 1) from
                ⟨erase_subset _ _, le_rfl⟩)) e ∧
        Rows.extendBot (univ.erase x, g + 1) p (L.embedOn C d) = p e := by
    obtain ⟨d, hd, hde⟩ := hL.exists_embedOn_eq hne e.2
    refine ⟨d, hd, hd.2, Subtype.ext hde, ?_⟩
    rw [hde]
    exact Rows.extendBot_of_mem p e.2
  refine Rows.cappedLift_of_ownerCappedLift (erase_subset _ _) hX hlift fun c hc ↦ ?_
  rcases eq_bot_or_bot_lt c with rfl | hcbot
  · -- The cap `⊥`: the owner-capped prescription, extended by the provision.
    intro p _ hp _ _ o ho hop _
    have hp' := hp.min_const_of_isSelfVisible (hp.isSelfVisible_of_gradedIndex_eq ho)
    obtain ⟨W, -, hWf, hWC⟩ := hbot (fun d ↦ Rows.extendBot (univ.erase x, g + 1)
      (fun e ↦ min (p e) (p o)) (L.embedOn C d)) (hold _ hp')
    obtain ⟨r, hr, hrW⟩ := hL.exists_extensionOn_bot hC hdown hWC
    refine ⟨r, hr, fun e ↦ ?_, fun _ ↦ by simp⟩
    obtain ⟨d, hdb, hd, hde, hdp⟩ := hread _ e
    rw [← hde, hrW d hd, hWf d hdb, hdp]
  · -- The positive caps: owner-capped lifts from the serving rows.
    obtain ⟨W₀, -, -, hW₀C⟩ := hbot (fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _)
    obtain ⟨i₀, -⟩ := exists_entryOn_eq hW₀C
    have hY : ∃ t, (L.nextSOn C).toCellScheme.gradedIndex t =
        ((univ : Finset (Fin (m + 2))), g + 1) :=
      ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩
    refine Rows.hasOwnerCappedLifts_of_rows_short (erase_subset _ _) hcbot hc hY fun u hu ↦ ?_
    obtain ⟨i, rfl⟩ := Lvl.exists_natAdd_eq_nextSOn hu
    have hPC : entryOn C i ∈ C := entryOn_mem i
    have hrowB (z : (L.nextSOn C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
        (L.nextSOn C).rows.rowBelow _ hu z = L.ΦOn C (entryOn C i) z :=
      Scheme.appendFullCells_row_natAdd i _
    have hmem := hL.ΦOn_mem_codeGrid (C := C) (mem_codeGrid_of_mem_cat (hC hPC))
    refine ⟨hL.isConsistent_nextSOn hC hdown _, fun z ↦ ?_, fun z ↦ ?_, ?_⟩
    · rw [hrowB]; exact isShort_of_mem_codeGrid (hmem _)
    · rw [hrowB]; exact ne_top_of_mem_codeGrid (hmem _)
    · intro h hh hhs hhb f hf _ hfS
      have hfP (d : Fin I.amalgam.card)
          (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1)) :
          min (Rows.extendBot (univ.erase x, g + 1) f (L.embedOn C d)) h =
            min (entryOn C i d) h := by
        have hdb : L.embedOn C d ∈ (L.nextSOn C).toCellScheme.below (univ.erase x, g + 1) := by
          rw [CellScheme.mem_below, hL.gradedIndex_embedOn]
          exact hd
        have h1 := hfS ⟨_, hdb⟩
        rw [Rows.extendBot_of_mem f hdb]
        refine h1.trans ?_
        change min ((L.nextSOn C).rows.rowBelow _ hu ⟨L.embedOn C d, _⟩) h = _
        rw [hrowB]
        change min (L.ΦOn C (entryOn C i) (Fin.castAdd _ (L.embed d))) h = _
        rw [Lvl.ΦOn_castAdd, hL.literal]
      obtain ⟨W, -, hWf, hWP, hWQ⟩ := hcap h hh hhs hhb _ hPC
        (fun d ↦ Rows.extendBot (univ.erase x, g + 1) f (L.embedOn C d)) (hold f hf) hfP
      obtain ⟨r, hr, hrW, hrP⟩ := hL.exists_extensionOn hC hdown hPC hh hhs hhb.ne' hWQ hWP
      refine ⟨r, hr, fun e ↦ ?_, fun z ↦ by rw [hrowB]; exact hrP z⟩
      obtain ⟨d, hdb, hd, hde, hdp⟩ := hread f e
      rw [← hde, hrW d hd, hWf d hdb, hdp]


/-- **The capped lift from a coatom into the admitted layer**, at the grade `g + 1 ≤ m + 1`, under
the lift provisions of the admission (`ProfileTower.Lvl.Good.cappedLift_nextSOn_rowCat` for its
reading rows). -/
theorem Lvl.GoodOn.cappedLift_nextSOn_rowCat (Rw : I.State → Prop) (hL : L.GoodOn D)
    (hdown : ∀ R ∈ rowCat Rw (g + 1), code g R ∈ D g) (hgm : g + 1 ≤ m + 1)
    {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2))))
    (hbot : BotLiftProvisionOf Rw (g + 1) x) (hcap : CapLiftProvisionOf Rw (g + 1) x) :
    (L.nextSOn (rowCat Rw (g + 1))).rows.CappedLift (X := (univ.erase x, g + 1))
      (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  hL.cappedLift_nextSOn (rowCat_subset Rw _) hdown hgm hx hbot hcap

/-- **The capped lift from a coatom into the admitted layer**, at the grade `g + 1 ≤ m + 1`, under
the lift provisions of the admission and the downward clause. -/
theorem Lvl.GoodOn.cappedLift_admittedNextS (A : I.Admission) (hL : L.GoodOn D)
    (hdown : ∀ R ∈ admittedCat A (g + 1), code g R ∈ D g) (hgm : g + 1 ≤ m + 1)
    {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2))))
    (hbot : BotLiftProvision A (g + 1) x) (hcap : CapLiftProvision A (g + 1) x) :
    (L.admittedNextS A).rows.CappedLift (X := (univ.erase x, g + 1))
      (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  hL.cappedLift_nextSOn_rowCat A.Row hdown hgm hx hbot hcap

end Step

/-! ### The trivial admission has the lift provisions -/

/-- A profile lawful on the grade-`k` cut is lawful below either coatom. -/
theorem IsCutLawful.erase {k : ℕ} {P : Prof I} (hP : IsCutLawful I k P) {y : Fin (m + 2)}
    (hy : y ∈ (Pts : Finset (Fin (m + 2)))) :
    I.amalgam.rows.IsLawfulBelow (univ.erase y, k) fun d ↦ P d := by
  simp only [Pts, mem_insert, mem_singleton] at hy
  rcases hy with rfl | rfl
  exacts [hP.1, hP.2]

/-- **The lift within the other coatom from the common face**, at a grade `0 < k ≤ m`: a profile
`f` lawful below a coatom `(C, k)`, agreeing below it with a profile `P` lawful on the cut capped at
`h` (self-visible at `k`), agrees below `(C, k)` with a profile lawful on the cut that agrees with
`P` capped at `h` everywhere.  The other coatom `D` is filled by the capped lift of the amalgam from
`(C ∩ D, k)` to `(D, k)` at the ambient `P`. -/
theorem exists_isCutLawful_of_coatom {k : ℕ} (hk : 0 < k) (hkm : k ≤ m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) {h : Label.{u}} (hh : IsSelfVisible k h)
    {P : Prof I} (hP : IsCutLawful I k P) {f : Prof I}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase x, k) fun d ↦ f d)
    (hfP : ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, k), min (f d) h = min (P d) h) :
    ∃ W : Prof I, IsCutLawful I k W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, k), W d = f d) ∧
      ∀ d, min (W d) h = min (P d) h := by
  classical
  obtain ⟨y, hy, hxy⟩ := Seed.exists_other hx
  obtain ⟨hOf, hOcard⟩ := inter_props (I := I) hx hy hxy
  have hXf : ((univ.erase x ∩ univ.erase y, k) : Finset (Fin (m + 2)) × ℕ) ∈
      I.amalgam.toCellScheme.gradedFaces := ⟨hOf, hk, by simp only; rw [hOcard]; exact hkm⟩
  have hYf : ((univ.erase y, k) : Finset (Fin (m + 2)) × ℕ) ∈
      I.amalgam.toCellScheme.gradedFaces :=
    ⟨I.erase_mem_faces hy, hk, by simp only; rw [Seed.card_erase]; omega⟩
  have hXY : ((univ.erase x ∩ univ.erase y, k) : Finset (Fin (m + 2)) × ℕ) ≤
      (univ.erase y, k) := ⟨inter_subset_right, le_rfl⟩
  have hXC : ((univ.erase x ∩ univ.erase y, k) : Finset (Fin (m + 2)) × ℕ) ≤
      (univ.erase x, k) := ⟨inter_subset_left, le_rfl⟩
  obtain ⟨v, hv, hvP, hvf⟩ := (Rows.cappedLift_iff_forall_exists hXY).mp
    (I.isBountiful hXf hYf hXY) h hh (fun d ↦ f d) (fun d ↦ P d)
    (hf.mono (X := (univ.erase x ∩ univ.erase y, k)) hXC) (hP.erase hy)
    fun d ↦ (hfP d.1 (CellScheme.below_mono _ hXC d.2)).symm
  set W : Prof I := fun d ↦
    if d ∈ I.amalgam.toCellScheme.below (univ.erase x, k) then f d
    else if hD : d ∈ I.amalgam.toCellScheme.below (univ.erase y, k) then v ⟨d, hD⟩ else P d
    with hW
  have hWC (d) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase x, k)) : W d = f d :=
    ite_eq_left hd
  have hWD (d) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase y, k)) : W d = v ⟨d, hd⟩ := by
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase x, k)
    · rw [hWC d hdC]
      exact (hvf ⟨d, ⟨subset_inter hdC.1 hd.1, hd.2⟩⟩).symm
    · rw [hW]
      simp only [hdC, hd, ite_false, dite_true]
  have hlC : I.amalgam.rows.IsLawfulBelow (univ.erase x, k) fun d ↦ W d :=
    (Rows.isLawfulBelow_congr fun d hd ↦ (hWC d hd).symm).mp hf
  have hlD : I.amalgam.rows.IsLawfulBelow (univ.erase y, k) fun d ↦ W d := by
    convert hv using 1
    exact funext fun d ↦ hWD d d.2
  refine ⟨W, lawful_pair hx hy hxy hlC hlD, hWC, fun d ↦ ?_⟩
  by_cases hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase x, k)
  · rw [hWC d hdC]; exact hfP d hdC
  by_cases hdD : d ∈ I.amalgam.toCellScheme.below (univ.erase y, k)
  · rw [hWD d hdD]; exact hvP ⟨d, hdD⟩
  · rw [hW]
    simp only [hdC, hdD, ite_false, dite_false]


/-- **The trivial admission has the lift provision at `⊥`**, at every grade `0 < k ≤ m` and either
coatom: the fill within the other coatom (`ProfileTower.exists_isCutLawful_of_coatom` at the cap
`⊥`), whose code lies in the catalogue. -/
theorem botLiftProvisionIn_cat {k : ℕ} (hk : 0 < k) (hkm : k ≤ m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) : BotLiftProvisionIn (cat I k) k x := fun f hf ↦ by
  obtain ⟨W, hW, hWf, -⟩ := exists_isCutLawful_of_coatom hk hkm hx (isSelfVisible_bot k)
    (P := fun _ ↦ ⊥) ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ hf
    fun _ _ ↦ by simp
  exact ⟨W, hW, hWf, code_mem_cat_of_isCutLawful hW⟩

/-- The trivial admission has the lift provision at `⊥` at every grade `0 < k ≤ m`. -/
theorem botLiftProvision_all (N : ℕ) {k : ℕ} (hk : 0 < k) (hkm : k ≤ m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    BotLiftProvision (Seed.Admission.all I N) k x := by
  have h := botLiftProvisionIn_cat (I := I) hk hkm hx
  rwa [← admittedCat_all N k] at h

/-- **The trivial admission has the lift provision at the positive caps**, at every grade
`0 < k ≤ m` and either coatom: the fill within the other coatom at the ambient `P`
(`ProfileTower.exists_isCutLawful_of_coatom`), whose orbit code lies in the catalogue. -/
theorem capLiftProvisionIn_cat {k : ℕ} (hk : 0 < k) (hkm : k ≤ m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) : CapLiftProvisionIn (cat I k) k x :=
    fun h hh _ _ P hP f hf hfP ↦ by
  obtain ⟨W, hW, hWf, hWP⟩ := exists_isCutLawful_of_coatom hk hkm hx hh (mem_cat.mp hP).1 hf hfP
  exact ⟨W, hW, hWf, hWP, mem_cat.mpr ⟨⟨hW.1.orbitCode fun d ↦ d.2.2,
    hW.2.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩⟩

/-- The trivial admission has the lift provision at the positive caps at every grade
`0 < k ≤ m`. -/
theorem capLiftProvision_all (N : ℕ) {k : ℕ} (hk : 0 < k) (hkm : k ≤ m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    CapLiftProvision (Seed.Admission.all I N) k x := by
  have h := capLiftProvisionIn_cat (I := I) hk hkm hx
  rwa [← admittedCat_all N k] at h

end VaughtConjecture.ProfileTower

/-! ### Admissions with the lift provisions -/

namespace VaughtConjecture.Seed

open Finset ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- **An admission with the lift provisions**: an admission together with the lift provisions for
its reading rows at `⊥` and at the positive caps, at every grade `k` with `N ≤ k ≤ m + 1` and from
either coatom. -/
structure LiftAdmission extends I.Admission where
  /-- The lift provision at the cap `⊥`. -/
  botLift : ∀ ⦃k : ℕ⦄, N ≤ k → k ≤ m + 1 → ∀ ⦃x : Fin (m + 2)⦄,
    x ∈ (Pts : Finset (Fin (m + 2))) →
      BotLiftProvisionOf (fun s ↦ (InClass s ∧ Adm s) ∨ CapBot s) k x
  /-- The lift provision at the positive caps. -/
  capLift : ∀ ⦃k : ℕ⦄, N ≤ k → k ≤ m + 1 → ∀ ⦃x : Fin (m + 2)⦄,
    x ∈ (Pts : Finset (Fin (m + 2))) →
      CapLiftProvisionOf (fun s ↦ (InClass s ∧ Adm s) ∨ CapBot s) k x

variable {I}

/-- The lift provision at `⊥` of an admission with the lift provisions. -/
theorem LiftAdmission.botLiftProvision (A : I.LiftAdmission) {k : ℕ} (hk : A.N ≤ k)
    (hkm : k ≤ m + 1) {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    BotLiftProvision A.toAdmission k x :=
  A.botLift hk hkm hx

/-- The lift provision at the positive caps of an admission with the lift provisions. -/
theorem LiftAdmission.capLiftProvision (A : I.LiftAdmission) {k : ℕ} (hk : A.N ≤ k)
    (hkm : k ≤ m + 1) {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    CapLiftProvision A.toAdmission k x :=
  A.capLift hk hkm hx

end VaughtConjecture.Seed
