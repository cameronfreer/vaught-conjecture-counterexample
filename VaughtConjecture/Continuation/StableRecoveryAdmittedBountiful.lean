/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryAdmittedLayerP
import VaughtConjecture.Extension.OwnerCappedLift
import VaughtConjecture.Extension.Restoration

/-!
# Bountifulness of the admitted field layer at `P`

Roadmap, Layer 3, 3.1, (R6) (the completion below the full grade with a restricted catalogue at the
reading grades); the admitted field layer at `P` of
`VaughtConjecture.Continuation.StableRecoveryAdmittedLayerP`.

**The coatom lift into an admitted field layer** (`Scheme.cappedLift_admittedFieldLayer`).  Let `S`
be a scheme with consistent rows and no cell above `(univ, j + 1)`, `A` a predicate holding at the
constant `⊥`, and `U` a face other than the ground set with a cell at `(U, j + 1)` and a capped lift
from `(U, j)` to `(univ, j)`.  Under two **lift provisions** at `U`:

* at the cap `⊥`: every labelling lawful below `(U, j + 1)` agrees below `(U, j + 1)` with a
  labelling lawful below `(univ, j + 1)` whose orbit code satisfies `A`;
* at the short positive caps `h`: for every lawful `a` satisfying `A` and every labelling `f` lawful
  below `(U, j + 1)` agreeing with `a` capped at `h` below it, some labelling lawful below
  `(univ, j + 1)` agrees with `f` below `(U, j + 1)`, with `a` capped at `h` at every cell of grade
  at most `j + 1`, and has its orbit code satisfying `A`,

the admitted field layer lifts capped from `(U, j + 1)` to `(univ, j + 1)`.  The proof is the
one-grade lift `CellScheme.Rows.cappedLift_of_ownerCappedLift`: at the cap `⊥` the owner-capped
prescription is extended through the provision and `Scheme.exists_isLawfulBelow_fieldLayerOn`; at a
positive cap the owner-capped lifts come from the serving rows
(`CellScheme.Rows.hasOwnerCappedLifts_of_rows_short`) through the provision and
`Scheme.exists_extension_fieldLayerOn`.  It is the field-layer form of the lift of an admitted
profile layer of the admission engine.

**Assembly for a seed with equal coatom types** (`Seed.isBountiful_admittedDoubledLower`,
`Seed.isLegalBelowFullGrade_admittedDoubledLower`): the admitted layer at the grade `2` over the
doubled lower layer is bountiful from the lifts of the lower layer at the grade `1` and the two
coatom lifts at the grade `2`, and then legal below the full grade when `A` holds at `⊥`.

**At `P`, with the marker at the cap.**

* The cells of grade `1` of the lower scheme are dead, so its lifts at the grade `1` are trivial
  (`GatedExtensionCounterexample.cappedLift_lowerP_one`).
* **The provisions**, for every prescription and every cap
  (`GatedExtensionCounterexample.botProvision_left`, `capProvision_left`, `botProvision_right`,
  `capProvision_right`):
  * from the private coatom at `⊥`: the raise (the donor's full cells at the private cap value);
  * from the private coatom at a positive cap `h`: the donor copy of the entry, raised to the
    private cap value when the prescription is in the bottom class and the entry reads a full cell
    of the donor below it (then the entry's private cap, the raised values and the entry's donor
    values all lie at least at `h`, by capped correctness of the entry);
  * from the donor coatom at `⊥`: `⊥` on the private copy (outside the bottom class);
  * from the donor coatom at a positive cap: the private copy of the entry, lowered to the least
    donor value of the prescription when the entry is in the bottom class and reads its private cap
    above a donor value of the prescription (then that least value lies at least at `h`).
* `GatedExtensionCounterexample.cappedLift_admittedLayerP_left`,
  `GatedExtensionCounterexample.cappedLift_admittedLayerP_right`: the two coatom lifts at the grade
  `2`; `GatedExtensionCounterexample.isBountiful_admittedLayerP`: bountifulness;
  `GatedExtensionCounterexample.isLegalBelowFullGrade_admittedLayerP`: **the admitted layer at `P`
  is legal below the full grade.**

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

namespace Scheme

variable {n j : ℕ} {S : Scheme.{u} n} {A : (Fin S.card → Label.{u}) → Prop}
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), j + 1) ≤ S.toCellScheme.gradedIndex d}

/-- **The coatom lift into an admitted field layer**, under the lift provisions at the cap `⊥` and
at the short positive caps. -/
theorem cappedLift_admittedFieldLayer (hcons : S.rows.IsConsistent) (hA0 : A fun _ ↦ ⊥)
    {U : Finset (Fin n)} (hU : U ≠ univ)
    (hX : ∃ c, S.toCellScheme.gradedIndex c = (U, j + 1))
    (hlift : S.rows.CappedLift (X := (U, j)) (Y := ((univ : Finset (Fin n)), j))
      ⟨subset_univ _, le_rfl⟩)
    (hbot : ∀ f : Fin S.card → Label.{u}, S.rows.IsLawfulBelow (U, j + 1) (fun d ↦ f d) →
      ∃ W : Fin S.card → Label.{u},
        S.rows.IsLawfulBelow ((univ : Finset (Fin n)), j + 1) (fun d ↦ W d) ∧
        (∀ d ∈ S.toCellScheme.below (U, j + 1), W d = f d) ∧
        A (orbitCode (j + 1) (S.toCellScheme.splice (j + 1) (fun _ ↦ ⊥) W)))
    (hcap : ∀ h : Label.{u}, IsSelfVisible (j + 1) h → IsShort (j + 1) h → ⊥ < h →
      ∀ a : Fin S.card → Label.{u}, S.rows.IsLawful a → A a →
      ∀ f : Fin S.card → Label.{u}, S.rows.IsLawfulBelow (U, j + 1) (fun d ↦ f d) →
      (∀ d ∈ S.toCellScheme.below (U, j + 1), min (f d) h = min (a d) h) →
      ∃ W : Fin S.card → Label.{u},
        S.rows.IsLawfulBelow ((univ : Finset (Fin n)), j + 1) (fun d ↦ W d) ∧
        (∀ d ∈ S.toCellScheme.below (U, j + 1), W d = f d) ∧
        (∀ d, S.toCellScheme.grade d ≤ j + 1 → min (W d) h = min (a d) h) ∧
        A (orbitCode (j + 1) (S.toCellScheme.splice (j + 1) (fun _ ↦ ⊥) W))) :
    (S.admittedFieldLayer (j + 1) A hS).rows.CappedLift (X := (U, j + 1))
      (Y := ((univ : Finset (Fin n)), j + 1)) ⟨subset_univ _, le_rfl⟩ := by
  classical
  set C := S.admittedCatalogue (j + 1) A
  have hC : C ⊆ S.catalogue (j + 1) := admittedCatalogue_subset
  have hmem {W : Fin S.card → Label.{u}}
      (hW : S.rows.IsLawfulBelow ((univ : Finset (Fin n)), j + 1) (fun d ↦ W d))
      (hAW : A (orbitCode (j + 1) (S.toCellScheme.splice (j + 1) (fun _ ↦ ⊥) W))) :
      orbitCode (j + 1) (S.toCellScheme.splice (j + 1) (fun _ ↦ ⊥) W) ∈ C :=
    mem_admittedCatalogue.mpr ⟨orbitCode_splice_bot_mem_catalogue hW, hAW⟩
  have hUk : ¬ ((univ : Finset (Fin n)), j + 1) ≤ (U, j + 1) :=
    fun h ↦ hU (univ_subset_iff.mp h.1)
  -- the lift at the grade `j`, through the old cells
  have hsp : S.toCellScheme.IsSourcePrefix (S.admittedFieldLayer (j + 1) A hS).toCellScheme
      (Fin.castAdd _) ((univ : Finset (Fin n)), j) :=
    ⟨isLowerEmbedding_castAdd (j + 1) (S.admittedCatalogue (j + 1) A).card
      (fun i ↦ S.fieldRowOn (j + 1) _ (entryOn _ i)) hS, appendFullCellsScheme_scope_castAdd S _ _,
      fun d hd ↦ ⟨⟨d, lt_card_of_mem_below (fun h ↦ absurd h.2 (by omega)) hd⟩, rfl⟩⟩
  have hlift' : (S.admittedFieldLayer (j + 1) A hS).rows.CappedLift (X := (U, j))
      (Y := ((univ : Finset (Fin n)), j)) ⟨subset_univ _, le_rfl⟩ := by
    refine (hsp.cappedLift_iff _ le_rfl).mp ?_
    have hc : (S.admittedFieldLayer (j + 1) A hS).rows.comap hsp.isLowerEmbedding = S.rows :=
      comap_rows_castAdd (S := S) (k := j + 1) (M := C.card)
        (r := fun i ↦ S.fieldRowOn (j + 1) C (entryOn C i)) (h := hS)
    rw [hc]
    exact hlift
  obtain ⟨c₀, hc₀⟩ := hX
  have hXF : ∃ c, (S.admittedFieldLayer (j + 1) A hS).toCellScheme.gradedIndex c = (U, j + 1) :=
    ⟨Fin.castAdd _ c₀, (appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans hc₀⟩
  -- the prescription below the coatom, read on the old cells
  have hold (p : (S.admittedFieldLayer (j + 1) A hS).toCellScheme.below (U, j + 1) → Label.{u})
      (hp : (S.admittedFieldLayer (j + 1) A hS).rows.IsLawfulBelow (U, j + 1) p) :
      S.rows.IsLawfulBelow (U, j + 1)
        (fun d ↦ Rows.extendBot (U, j + 1) p (Fin.castAdd C.card d)) :=
    (isLawfulBelow_appendFullCells_iff (S := S) (k := j + 1) (M := C.card)
      (r := fun i ↦ S.fieldRowOn (j + 1) C (entryOn C i)) (h := hS) hUk).mp
        (Rows.isLawfulBelow_extendBot.mpr hp)
  have hread (p : (S.admittedFieldLayer (j + 1) A hS).toCellScheme.below (U, j + 1) → Label.{u})
      (e : (S.admittedFieldLayer (j + 1) A hS).toCellScheme.below (U, j + 1)) :
      ∃ d ∈ S.toCellScheme.below (U, j + 1), ∃ hd : S.toCellScheme.grade d ≤ j + 1,
        (⟨Fin.castAdd C.card d, castAdd_mem_below_fieldLayerOn hd⟩ :
          (S.admittedFieldLayer (j + 1) A hS).toCellScheme.below
            ((univ : Finset (Fin n)), j + 1)) =
          Set.inclusion ((S.admittedFieldLayer (j + 1) A hS).toCellScheme.below_mono
            (show ((U, j + 1) : Finset (Fin n) × ℕ) ≤ (univ, j + 1) from
              ⟨subset_univ _, le_rfl⟩)) e ∧
        Rows.extendBot (U, j + 1) p (Fin.castAdd C.card d) = p e := by
    have hlt := lt_card_of_mem_below hUk e.2
    set d : Fin S.card := ⟨e.1, hlt⟩
    have hde : Fin.castAdd C.card d = e.1 := rfl
    have hdb : d ∈ S.toCellScheme.below (U, j + 1) := by
      have h := e.2
      rw [← hde, CellScheme.mem_below, appendFullCellsScheme_gradedIndex_castAdd] at h
      exact h
    refine ⟨d, hdb, hdb.2, Subtype.ext hde, ?_⟩
    rw [hde]
    exact Rows.extendBot_of_mem p e.2
  refine Rows.cappedLift_of_ownerCappedLift (subset_univ U) hXF hlift' fun c hc ↦ ?_
  rcases eq_bot_or_bot_lt c with rfl | hcbot
  · -- the cap `⊥`: the owner-capped prescription, extended through the provision
    intro p _ hp _ _ o ho hop _
    have hp' := hp.min_const_of_isSelfVisible (hp.isSelfVisible_of_gradedIndex_eq ho)
    obtain ⟨W, hW, hWf, hWA⟩ := hbot (fun d ↦ Rows.extendBot (U, j + 1)
      (fun e ↦ min (p e) (p o)) (Fin.castAdd C.card d)) (hold _ hp')
    obtain ⟨r, hr, hrW⟩ := exists_isLawfulBelow_fieldLayerOn (hS := hS) hC (hmem hW hWA)
    refine ⟨r, hr, fun e ↦ ?_, fun _ ↦ by simp⟩
    obtain ⟨d, hdb, hd, hde, hdp⟩ := hread _ e
    rw [← hde, hrW d hd, hWf d hdb, hdp]
  · -- the positive caps: owner-capped lifts from the serving rows
    obtain ⟨i₀, -⟩ := exists_entryOn_eq (bot_mem_admittedCatalogue (S := S) (k := j + 1) hA0)
    have hY : ∃ t, (S.admittedFieldLayer (j + 1) A hS).toCellScheme.gradedIndex t =
        ((univ : Finset (Fin n)), j + 1) :=
      ⟨Fin.natAdd _ i₀, appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩
    refine Rows.hasOwnerCappedLifts_of_rows_short (subset_univ U) hcbot hc hY fun u hu ↦ ?_
    obtain ⟨i, rfl⟩ := exists_natAdd_eq_fieldLayerOn hu
    have hPC : entryOn C i ∈ C := entryOn_mem i
    obtain ⟨hPcat, hPA⟩ := mem_admittedCatalogue.mp hPC
    have hrowB (z : (S.admittedFieldLayer (j + 1) A hS).toCellScheme.below
        ((univ : Finset (Fin n)), j + 1)) :
        (S.admittedFieldLayer (j + 1) A hS).rows.rowBelow _ hu z =
          S.fieldRowOn (j + 1) C (entryOn C i) z :=
      fieldLayerOn_row_natAdd (hS := hS) i _
    have hcode := fieldRowOn_mem_codeGrid (C := C) hPcat
    refine ⟨isConsistent_fieldLayerOn hcons hC _, fun z ↦ ?_, fun z ↦ ?_, ?_⟩
    · rw [hrowB]; exact isShort_of_mem_codeGrid (hcode _)
    · rw [hrowB]; exact ne_top_of_mem_codeGrid (hcode _)
    · intro h hh hhs hhb f hf _ hfS
      have hfP (d : Fin S.card) (hd : d ∈ S.toCellScheme.below (U, j + 1)) :
          min (Rows.extendBot (U, j + 1) f (Fin.castAdd C.card d)) h =
            min (entryOn C i d) h := by
        have hdb : Fin.castAdd C.card d ∈
            (S.admittedFieldLayer (j + 1) A hS).toCellScheme.below (U, j + 1) := by
          rw [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_castAdd]
          exact hd
        have h1 := hfS ⟨_, hdb⟩
        rw [Rows.extendBot_of_mem f hdb]
        refine h1.trans ?_
        rw [hrowB]
        exact congrArg (min · h) (fieldRowOn_castAdd _ d)
      obtain ⟨W, hW, hWf, hWP, hWA⟩ := hcap h hh hhs hhb _ (mem_catalogue.mp hPcat).1 hPA
        (fun d ↦ Rows.extendBot (U, j + 1) f (Fin.castAdd C.card d)) (hold f hf) hfP
      obtain ⟨r, hr, hrW, hrP⟩ := exists_extension_fieldLayerOn (hS := hS) hC (hmem hW hWA)
        hPC hh hhs hhb hWP
      refine ⟨r, hr, fun e ↦ ?_, fun z ↦ by rw [hrowB]; exact hrP z⟩
      obtain ⟨d, hdb, hd, hde, hdp⟩ := hread f e
      rw [← hde, hrW d hd, hWf d hdb, hdp]

end Scheme

/-! ### The admitted layer over the doubled lower layer, for a seed with equal coatom types -/

namespace Seed

variable {α : Ordinal.{u}} (I : Seed.{u} α 1) (hLR : I.left = I.right)
  {A : (Fin (I.doubledLower hLR).card → Label.{u}) → Prop}

/-- The doubled lower layer is consistent. -/
theorem isConsistent_doubledLower (hI : I.left.IsLegal) : (I.doubledLower hLR).rows.IsConsistent :=
  Scheme.isConsistent_appendFullCells I.isConsistent fun i ↦
    (I.isDoubling_doubledLower hLR).isLawful_comp
      (Scheme.isLawful_rowAt hI.isConsistent (Scheme.gradedIndex_fullCell 1 i))

/-- The doubled lower layer is well formed. -/
theorem isWellFormed_doubledLower : (I.doubledLower hLR).IsWellFormed :=
  Scheme.isWellFormed_appendFullCells I.amalgam.isWellFormed one_pos (by omega)

/-- The doubled lower layer is coded. -/
theorem isCoded_doubledLower : (I.doubledLower hLR).IsCoded :=
  Scheme.isCoded_appendFullCells I.amalgam.isCoded fun _ _ ↦ I.left.isCoded.rowAt_lt _ _

/-- The admitted layer over the doubled lower layer is well formed. -/
theorem isWellFormed_admittedDoubledLower :
    ((I.doubledLower hLR).admittedFieldLayer 2 A
      (I.not_univ_two_le_doubledLower hLR)).IsWellFormed :=
  Scheme.isWellFormed_fieldLayerOn (I.isWellFormed_doubledLower hLR) two_pos (by omega)

/-- **Bountifulness of the admitted layer over the doubled lower layer**, from the lifts of the
lower layer at the grade `1` and the lifts from the two coatoms at the grade `2`: off the full face
by the amalgam (a source prefix), and from either coatom into the full face at every grade. -/
theorem isBountiful_admittedDoubledLower
    (h1 : ∀ U : Finset (Fin 3), (I.doubledLower hLR).rows.CappedLift (X := (U, 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨subset_univ _, le_rfl⟩)
    (hL : ((I.doubledLower hLR).admittedFieldLayer 2 A
      (I.not_univ_two_le_doubledLower hLR)).rows.CappedLift
        (X := (univ.erase (Fin.last 2), 2)) (Y := ((univ : Finset (Fin 3)), 2))
          ⟨erase_subset _ _, le_rfl⟩)
    (hR : ((I.doubledLower hLR).admittedFieldLayer 2 A
      (I.not_univ_two_le_doubledLower hLR)).rows.CappedLift
        (X := (univ.erase (Fin.castSucc (Fin.last 1)), 2)) (Y := ((univ : Finset (Fin 3)), 2))
          ⟨erase_subset _ _, le_rfl⟩) :
    ((I.doubledLower hLR).admittedFieldLayer 2 A
      (I.not_univ_two_le_doubledLower hLR)).rows.IsBountiful := by
  set F := (I.doubledLower hLR).admittedFieldLayer 2 A (I.not_univ_two_le_doubledLower hLR)
  have hemb := Scheme.isLowerEmbedding_castAdd (S := I.doubledLower hLR) 2
    ((I.doubledLower hLR).admittedCatalogue 2 A).card
    (fun i ↦ (I.doubledLower hLR).fieldRowOn 2 ((I.doubledLower hLR).admittedCatalogue 2 A)
      (Scheme.entryOn _ i)) (I.not_univ_two_le_doubledLower hLR)
  have hlow := Scheme.isLowerEmbedding_castAdd (S := I.amalgam.toScheme) 1 (I.nFull 1)
    (I.lowerRow hLR) (I.not_univ_le 1)
  have e1 : F.rows.comap hemb = (I.doubledLower hLR).rows :=
    Scheme.comap_rows_castAdd (S := I.doubledLower hLR) (k := 2)
      (M := ((I.doubledLower hLR).admittedCatalogue 2 A).card)
      (r := fun i ↦ (I.doubledLower hLR).fieldRowOn 2 ((I.doubledLower hLR).admittedCatalogue 2 A)
        (Scheme.entryOn _ i)) (h := I.not_univ_two_le_doubledLower hLR)
  have e2 : (I.doubledLower hLR).rows.comap hlow = I.amalgam.rows :=
    Scheme.comap_rows_castAdd (S := I.amalgam.toScheme) (k := 1) (M := I.nFull 1)
      (r := I.lowerRow hLR) (h := I.not_univ_le 1)
  -- the lower layer is a source prefix below `(univ, 1)`
  have hsp1 : (I.doubledLower hLR).toCellScheme.IsSourcePrefix F.toCellScheme (Fin.castAdd _)
      ((univ : Finset (Fin 3)), 1) :=
    ⟨hemb, Scheme.appendFullCellsScheme_scope_castAdd _ _ _,
      fun d hd ↦ ⟨⟨d, Scheme.lt_card_of_mem_below (fun h ↦ absurd h.2 (by omega)) hd⟩, rfl⟩⟩
  have hone (U : Finset (Fin 3)) : F.rows.CappedLift (X := (U, 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨subset_univ _, le_rfl⟩ := by
    refine (hsp1.cappedLift_iff _ le_rfl).mp ?_
    change (F.rows.comap hemb).CappedLift _
    rw [e1]
    exact h1 U
  have hle (z : Fin 3) (j : ℕ) (hj : j ≤ #(univ.erase z)) : j ≤ 2 := by
    rw [card_erase_of_mem (mem_univ z)] at hj
    simpa using hj
  have hfull (z : Fin 3) (hlift2 : F.rows.CappedLift (X := (univ.erase z, 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩) (j : ℕ) (hj : j ≤ 2) :
      F.rows.CappedLift (X := (univ.erase z, j)) (Y := ((univ : Finset (Fin 3)), j))
        ⟨erase_subset _ _, le_rfl⟩ := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · exact (I.isWellFormed_admittedDoubledLower hLR).isWellFormed.cappedLift _ (Or.inl rfl) _
    · exact hone _
    · exact hlift2
  refine CellScheme.Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last 2)
    (b := Fin.castSucc (Fin.last 1)) (mem_univ _) (mem_univ _) I.subset_or_subset
    I.erase_last_mem_faces I.erase_castSucc_mem_faces (fun X Y hX hY hXY hYne ↦ ?_)
    (fun j hj ↦ hfull _ hL j (hle _ j hj)) (fun j hj ↦ hfull _ hR j (hle _ j hj))
  -- off the full face: the amalgam is a source prefix
  have h : I.amalgam.toCellScheme.IsSourcePrefix F.toCellScheme
      (fun d ↦ Fin.castAdd _ (Fin.castAdd _ d)) Y := by
    refine ⟨hemb.comp hlow, fun t ↦
        (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
          (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _), fun d hd ↦ ?_⟩
    have hsc : F.toCellScheme.scope d ≠ univ := fun he ↦
      hYne (subset_antisymm (subset_univ _) (he ▸ hd.1))
    induction d using Fin.addCases with
    | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hsc
    | left d =>
      induction d using Fin.addCases with
      | right i =>
        exact absurd ((Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
          (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i)) hsc
      | left a => exact ⟨a, rfl⟩
  refine h.cappedLift_of_isBountiful ?_ hX hY hXY le_rfl
  have hc : F.rows.comap h.isLowerEmbedding = I.amalgam.rows := by
    change ((F.rows.comap hemb).comap hlow) = _
    rw [e1, e2]
  rw [hc]
  exact I.isBountiful

/-- **Legality below the full grade of the admitted layer over the doubled lower layer**, when it
is bountiful and the constant `⊥` is admitted. -/
theorem isLegalBelowFullGrade_admittedDoubledLower (hI : I.left.IsLegal) (hA0 : A fun _ ↦ ⊥)
    (hb : ((I.doubledLower hLR).admittedFieldLayer 2 A
      (I.not_univ_two_le_doubledLower hLR)).rows.IsBountiful) :
    ((I.doubledLower hLR).admittedFieldLayer 2 A
      (I.not_univ_two_le_doubledLower hLR)).IsLegalBelowFullGrade where
  isWellFormed := I.isWellFormed_admittedDoubledLower hLR
  isCoded := Scheme.isCoded_admittedFieldLayer (I.isCoded_doubledLower hLR)
  isConsistent := Scheme.isConsistent_admittedFieldLayer (I.isConsistent_doubledLower hLR hI)
  isBountiful := hb
  grade_lt d := by
    induction d using Fin.addCases with
    | left e =>
      rw [Scheme.appendFullCellsScheme_grade_castAdd]
      induction e using Fin.addCases with
      | left a =>
        rw [Scheme.appendFullCellsScheme_grade_castAdd]
        exact I.grade_lt a
      | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
    | right i =>
      rw [Scheme.appendFullCellsScheme_grade_natAdd]
      omega
  exists_gradedIndex_eq X hX hX2 := by
    obtain ⟨C, j⟩ := X
    by_cases hC : C = univ
    · subst hC
      have hj0 : 0 < j := hX.2.1
      have hj3 : j < 3 := hX2
      rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
      · obtain ⟨c, hc⟩ := hI.isComplete ((univ : Finset (Fin 2)), 1)
          ⟨I.left.univ_mem_faces, one_pos, by simp⟩
        obtain ⟨i₀, -⟩ := Scheme.exists_fullCell_eq hc
        exact ⟨Fin.castAdd _ (Fin.natAdd _ i₀),
          (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
            (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀)⟩
      · exact Scheme.exists_gradedIndex_eq_admittedFieldLayer hA0
    · obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq _ hX hC
      exact ⟨Fin.castAdd _ (Fin.castAdd _ d),
        ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
          (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _)).trans hd⟩

end Seed

/-! ### Facts at `P` -/

namespace GatedExtensionCounterexample

variable (β : Ordinal.{u})

/-- The dead cells of `P` read themselves at `⊥`. -/
theorem row_self_eq_bot_P {z : Fin 5} (hz : cellGrade z = 1) :
    rows.{u}.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥ := by
  fin_cases z <;> first | rfl | (exfalso; revert hz; decide)

/-- **A lawful labelling of `P` is `⊥` at the dead cells.** -/
theorem eq_bot_of_isLawful_P {s : Fin 5 → Label.{u}} (hs : rows.{u}.IsLawful s) {z : Fin 5}
    (hz : cellGrade z = 1) : s z = ⊥ := by
  have h := (hs.locality z).eq_bot (d := ⟨z, CellScheme.mem_below_gradedIndex _ z⟩)
    (row_self_eq_bot_P hz)
  simpa using h

/-- A lawful labelling of `P` is self-visible at `2` at the full cells. -/
theorem isSelfVisible_of_isLawful_P {s : Fin 5 → Label.{u}} (hs : rows.{u}.IsLawful s) {z : Fin 5}
    (hz : cellGrade z = 2) : IsSelfVisible 2 (s z) := by
  have h := hs.orderly z
  change IsSelfVisible (cellGrade z) (s z) at h
  rwa [hz] at h

/-- **Gluing lawful labellings of `P` on the lower scheme**: two lawful labellings of `P` glue to a
lawful labelling of the lower scheme, reading them on the private and donor copies and `⊥` at the
dead cell of full scope. -/
theorem exists_glue_lowerP {sL sR : Fin 5 → Label.{u}} (hL : rows.{u}.IsLawful sL)
    (hR : rows.{u}.IsLawful sR) :
    ∃ g : Fin (lowerP β).card → Label.{u}, (lowerP β).rows.IsLawful g ∧
      privP β g = sL ∧ donP β g = sR ∧ ∀ i, g (Fin.natAdd _ i) = ⊥ := by
  obtain ⟨w, hw, hwL, hwR⟩ := (seedP β).exists_isLawful_glue rfl hL hR (by
    change ∀ z : Fin 5, Fin.last 1 ∉ cellScope z → sL z = sR z
    intro z hz
    have h0 : z = 0 := by revert hz; fin_cases z <;> decide
    subst h0
    rw [eq_bot_of_isLawful_P hL rfl, eq_bot_of_isLawful_P hR rfl])
  have hdead {s : Fin 5 → Label.{u}} (hs : rows.{u}.IsLawful s) (z : Fin (seedP β).left.card)
      (hz : (P β).toCellScheme.grade z = 1) : s z = ⊥ :=
    eq_bot_of_isLawful_P hs hz
  have hw1 (d : Fin (seedP β).amalgam.card) (hd : (seedP β).amalgam.toCellScheme.grade d = 1) :
      w d = ⊥ := by
    rcases (seedP β).eq_faceCell_or rfl d with h | h
    · rw [← h, hwL]
      rw [← h, StageType.grade_faceCell] at hd
      exact hdead hL _ hd
    · rw [← h, hwR]
      rw [← h, StageType.grade_faceCell] at hd
      exact hdead hR _ hd
  have hc2 : (seedP β).left.toCellScheme.gradedIndex (2 : Fin 5) =
      ((univ : Finset (Fin 2)), 1) := by
    change cells.gradedIndex 2 = _
    rw [gradedIndex_cells]
    rfl
  obtain ⟨i₀, -⟩ := Scheme.exists_fullCell_eq (T := (seedP β).left.toScheme) (j := 1) hc2
  refine ⟨Fin.append w fun _ ↦ ⊥, Scheme.isLawful_appendFullCells (h := (seedP β).not_univ_le 1)
    ?_ (fun _ ↦ ?_) (fun i ↦ ?_) fun s hs ↦ ⟨i₀, ?_⟩, ?_, ?_, fun i ↦ Fin.append_right _ _ i⟩
  · convert hw using 1
    funext d
    exact Fin.append_left _ _ d
  · rw [Fin.append_right]
    exact isSelfVisible_bot _
  · convert TransformsTo.bot _ _ using 1
    funext t
    rw [Fin.append_right, min_bot_right]
  · rw [Fin.append_right]
    induction s using Fin.addCases with
    | left d =>
      rw [Fin.append_left, hw1 d (by
        rw [← Scheme.appendFullCellsScheme_grade_castAdd]; exact hs)]
    | right j => rw [Fin.append_right]
  · funext z
    exact (Fin.append_left _ _ _).trans (hwL z)
  · funext z
    exact (Fin.append_left _ _ _).trans (hwR z)

/-! ### The coatom pairs and the cells below them -/

/-- The private coatom pair at the grade `2`. -/
abbrev pairL : Finset (Fin 3) × ℕ := (univ.erase (Fin.last 2), 2)

/-- The donor coatom pair at the grade `2`. -/
abbrev pairR : Finset (Fin 3) × ℕ := (univ.erase (Fin.castSucc (Fin.last 1)), 2)

private theorem not_univ_one_le_erase {x : Fin 3} {g : ℕ} :
    ¬ ((univ : Finset (Fin 3)), 1) ≤ (univ.erase x, g) :=
  fun h ↦ Finset.notMem_erase x univ (h.1 (mem_univ x))

/-- **The private copy of a labelling lawful below the private coatom is lawful on `P`.** -/
theorem isLawful_privP {f : Fin (lowerP β).card → Label.{u}}
    (hf : (lowerP β).rows.IsLawfulBelow (pairL) (fun d ↦ f d)) : rows.{u}.IsLawful (privP β f) := by
  have h1 := (Scheme.isLawfulBelow_appendFullCells_iff (S := (seedP β).amalgam.toScheme) (k := 1)
    (M := (seedP β).nFull 1) (r := (seedP β).lowerRow rfl) (h := (seedP β).not_univ_le 1)
    not_univ_one_le_erase).mp hf
  have hpair : (pairL : Finset (Fin 3) × ℕ) =
      Prod.map (Finset.map (Coatom.left 1)) id ((univ : Finset (Fin 2)), 2) := by
    simp only [Prod.map, id, Coatom.univ_map_left]
  have h2 := (Scheme.isLawfulBelow_faceCell_iff
    (StageType.comap_toScheme_of_restrictFace (seedP β).restrictFace_left) (univ, 2)
      (fun d ↦ f (Fin.castAdd _ d))).mpr (by rw [← hpair]; exact h1)
  exact h2.isLawful fun d ↦ ⟨subset_univ _, (P β).grade_le d⟩

/-- **The donor copy of a labelling lawful below the donor coatom is lawful on `P`.** -/
theorem isLawful_donP {f : Fin (lowerP β).card → Label.{u}}
    (hf : (lowerP β).rows.IsLawfulBelow (pairR) (fun d ↦ f d)) : rows.{u}.IsLawful (donP β f) := by
  have h1 := (Scheme.isLawfulBelow_appendFullCells_iff (S := (seedP β).amalgam.toScheme) (k := 1)
    (M := (seedP β).nFull 1) (r := (seedP β).lowerRow rfl) (h := (seedP β).not_univ_le 1)
    not_univ_one_le_erase).mp hf
  have hpair : (pairR : Finset (Fin 3) × ℕ) =
      Prod.map (Finset.map (Coatom.right 1)) id ((univ : Finset (Fin 2)), 2) := by
    simp only [Prod.map, id, Coatom.univ_map_right]
  have h2 := (Scheme.isLawfulBelow_faceCell_iff
    (StageType.comap_toScheme_of_restrictFace ((seedP β).restrictFace_right_left rfl)) (univ, 2)
      (fun d ↦ f (Fin.castAdd _ d))).mpr (by rw [← hpair]; exact h1)
  exact h2.isLawful fun d ↦ ⟨subset_univ _, (P β).grade_le d⟩

/-- A cell below the private coatom pair is a private copy. -/
theorem exists_left_of_mem_below {d : Fin (lowerP β).card}
    (hd : d ∈ (lowerP β).toCellScheme.below pairL) :
    ∃ z : Fin 5, d = Fin.castAdd _ (StageType.faceCell (seedP β).restrictFace_left z) := by
  induction d using Fin.addCases with
  | right i =>
    exfalso
    have h := hd.1
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd] at h
    exact Finset.notMem_erase _ univ (h (mem_univ (Fin.last 2)))
  | left e =>
    have h : (seedP β).amalgam.toCellScheme.scope e ⊆ univ.map (Coatom.left 1) := by
      have h' := hd.1
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd] at h'
      rw [Coatom.univ_map_left]
      exact h'
    exact ⟨(seedP β).doublingCell rfl e, by rw [(seedP β).faceCell_left_of_subset rfl h]⟩

/-- A cell below the donor coatom pair is a donor copy. -/
theorem exists_right_of_mem_below {d : Fin (lowerP β).card}
    (hd : d ∈ (lowerP β).toCellScheme.below pairR) :
    ∃ z : Fin 5, d = Fin.castAdd _
      (StageType.faceCell ((seedP β).restrictFace_right_left rfl) z) := by
  induction d using Fin.addCases with
  | right i =>
    exfalso
    have h := hd.1
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd] at h
    exact Finset.notMem_erase _ univ (h (mem_univ _))
  | left e =>
    have h : (seedP β).amalgam.toCellScheme.scope e ⊆ univ.map (Coatom.right 1) := by
      have h' := hd.1
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd] at h'
      rw [Coatom.univ_map_right]
      exact h'
    exact ⟨(seedP β).doublingCell rfl e, by rw [(seedP β).faceCell_right_of_subset rfl h]⟩

/-- The private copies lie below the private coatom pair. -/
theorem left_mem_below (z : Fin 5) :
    Fin.castAdd _ (StageType.faceCell (seedP β).restrictFace_left z) ∈
      (lowerP β).toCellScheme.below pairL := by
  rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
  refine ⟨?_, ?_⟩
  · refine (StageType.scope_faceCell (seedP β).restrictFace_left
      (z : Fin (seedP β).left.card)).trans_subset ?_
    exact (map_subset_map.mpr (subset_univ _)).trans (Coatom.univ_map_left (m := 1)).subset
  · exact (StageType.grade_faceCell (seedP β).restrictFace_left
      (z : Fin (seedP β).left.card)).trans_le ((P β).grade_le z)

/-- The donor copies lie below the donor coatom pair. -/
theorem right_mem_below (z : Fin 5) :
    Fin.castAdd _ (StageType.faceCell ((seedP β).restrictFace_right_left rfl) z) ∈
      (lowerP β).toCellScheme.below pairR := by
  rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
  refine ⟨?_, ?_⟩
  · refine (StageType.scope_faceCell ((seedP β).restrictFace_right_left rfl)
      (z : Fin (seedP β).left.card)).trans_subset ?_
    exact (map_subset_map.mpr (subset_univ _)).trans (Coatom.univ_map_right (m := 1)).subset
  · exact (StageType.grade_faceCell ((seedP β).restrictFace_right_left rfl)
      (z : Fin (seedP β).left.card)).trans_le ((P β).grade_le z)

/-! ### The cells of grade `1` of the lower scheme are dead -/

/-- The cells of the lower scheme of grade `1` read themselves at `⊥`. -/
theorem row_self_eq_bot_lowerP {s : Fin (lowerP β).card}
    (hs : (lowerP β).toCellScheme.grade s = 1) :
    (lowerP β).rows.row s ⟨s, CellScheme.mem_below_gradedIndex _ s⟩ = ⊥ := by
  have hD := (seedP β).isDoubling_doubledLower rfl
  rw [← Scheme.rowAt_of_mem, hD.rowAt_eq s s (CellScheme.mem_below_gradedIndex _ s)]
  have hz : (P β).toCellScheme.grade ((seedP β).lowerCell rfl s) = 1 := (hD.grade_eq s).trans hs
  generalize (seedP β).lowerCell rfl s = z at hz ⊢
  change cellGrade z = 1 at hz
  rw [Scheme.rowAt_of_mem (CellScheme.mem_below_gradedIndex _ z)]
  exact row_self_eq_bot_P hz

/-- **A labelling lawful below a pair is `⊥` at the cells of grade `1` below it.** -/
theorem eq_bot_lowerP {X : Finset (Fin 3) × ℕ} {w : Fin (lowerP β).card → Label.{u}}
    (hw : (lowerP β).rows.IsLawfulBelow X (fun d ↦ w d)) {s : Fin (lowerP β).card}
    (hsX : s ∈ (lowerP β).toCellScheme.below X) (hs : (lowerP β).toCellScheme.grade s = 1) :
    w s = ⊥ := by
  have h := ((CellScheme.Rows.isLawfulBelow_iff_forall.mp hw).2.1 s hsX).eq_bot
    (d := ⟨s, CellScheme.mem_below_gradedIndex _ s⟩) (row_self_eq_bot_lowerP β hs)
  simpa using h

/-- Every cell of the lower scheme has positive grade. -/
theorem grade_pos_lowerP (d : Fin (lowerP β).card) : 0 < (lowerP β).toCellScheme.grade d := by
  have hwf : (lowerP β).IsWellFormed :=
    Scheme.isWellFormed_appendFullCells (h := (seedP β).not_univ_le 1)
      (seedP β).amalgam.isWellFormed one_pos (by omega)
  exact (hwf.isWellFormed.gradedIndex_mem d).2.1

/-- **The lifts of the lower scheme at the grade `1`**: every labelling lawful below a pair of
grade `1` is `⊥`, so the constant `⊥` is the lift. -/
theorem cappedLift_lowerP_one (U : Finset (Fin 3)) :
    (lowerP β).rows.CappedLift (X := (U, 1)) (Y := ((univ : Finset (Fin 3)), 1))
      ⟨subset_univ _, le_rfl⟩ := by
  rw [CellScheme.Rows.cappedLift_iff_forall_exists]
  intro c _ p q hp hq _
  have hbot {X : Finset (Fin 3) × ℕ} (hX : X.2 = 1) {r : (lowerP β).toCellScheme.below X →
      Label.{u}} (hr : (lowerP β).rows.IsLawfulBelow X r) (d) : r d = ⊥ := by
    have h := eq_bot_lowerP β (CellScheme.Rows.isLawfulBelow_extendBot.mpr hr) d.2
      (le_antisymm (d.2.2.trans hX.le) (grade_pos_lowerP β d.1))
    rwa [CellScheme.Rows.extendBot_of_mem r d.2] at h
  refine ⟨fun _ ↦ ⊥, CellScheme.Rows.isLawfulBelow_const_bot _, fun d ↦ ?_, fun d ↦ ?_⟩
  · rw [hbot rfl hq d]
  · exact (hbot rfl hp d).symm

/-! ### The lift provisions at `P` -/

/-- The constant `⊥` is admitted at `P`: it is not in the bottom class. -/
theorem admissionP_bot : admissionP β (fun _ ↦ ⊥) :=
  fun hcl ↦ absurd ((hcl 3).mp rfl) (by decide)

/-- A labelling whose private copy is not in the bottom class has its orbit code admitted
(vacuously). -/
theorem admissionP_orbitCode_of_not {g : Fin (lowerP β).card → Label.{u}}
    (hg : ¬ InBottomClassP (privP β g)) :
    admissionP β (orbitCode 2 ((lowerP β).toCellScheme.splice 2 (fun _ ↦ ⊥) g)) := by
  intro hcl
  refine absurd (fun z ↦ ?_) hg
  rw [privP_orbitCode] at hcl
  have := hcl z
  simpa only [orbitMap_eq_bot_iff] using this

/-- The bottom class passes along an agreement capped at a positive cap. -/
theorem inBottomClassP_of_min_eq {s t : Fin 5 → Label.{u}} {h : Label.{u}} (hh : ⊥ < h)
    (hst : ∀ z, min (s z) h = min (t z) h) (hs : InBottomClassP s) : InBottomClassP t := by
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

/-- If `y < x` read alike capped at `h`, then `h ≤ y`. -/
theorem le_of_min_eq_of_lt {x y h : Label.{u}} (hyx : y < x) (hmin : min x h = min y h) :
    h ≤ y := by
  by_contra hyh
  push Not at hyh
  rw [min_eq_left hyh.le] at hmin
  exact lt_irrefl _ (hmin ▸ lt_min hyx hyh)

private theorem fin5_cases (z : Fin 5) :
    cellGrade z = 1 ∨ z = 3 ∨ z = 4 := by
  fin_cases z <;> simp [cellGrade]

private theorem top_top_capped_dead {v : Label.{u}} {z : Fin 5} (hz : cellGrade z = 1) :
    min (labelling (⊤ : Label.{u}) ⊤ z) v = ⊥ := by
  have : labelling (⊤ : Label.{u}) ⊤ z = ⊥ := by
    fin_cases z <;> first | rfl | (exfalso; revert hz; decide)
  rw [this, min_bot_left]

/-- The cells of grade at most `2` of the lower scheme: copies, and the dead cell of full scope. -/
private theorem min_eq_of_copies {W a : Fin (lowerP β).card → Label.{u}} {h : Label.{u}}
    (ha : (lowerP β).rows.IsLawful a) (hWN : ∀ i, W (Fin.natAdd _ i) = ⊥)
    (hL : ∀ z : Fin 5, min (privP β W z) h = min (privP β a z) h)
    (hR : ∀ z : Fin 5, min (donP β W z) h = min (donP β a z) h) (d : Fin (lowerP β).card) :
    min (W d) h = min (a d) h := by
  induction d using Fin.addCases with
  | right i =>
    rw [hWN, eq_bot_lowerP β (ha.isLawfulBelow ((univ : Finset (Fin 3)), 2))
      (s := Fin.natAdd _ i) ⟨subset_univ _, grade_lowerP_le β _⟩
      (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i)]
  | left e =>
    rcases (seedP β).eq_faceCell_or rfl e with he | he
    · rw [← he]; exact hL _
    · rw [← he]; exact hR _

/-- **The lift provision at the cap `⊥` from the private coatom**: the private copy of the
prescription, and on the donor copy its own cap value at the two full cells (the raise). -/
theorem botProvision_left {f : Fin (lowerP β).card → Label.{u}}
    (hf : (lowerP β).rows.IsLawfulBelow pairL (fun d ↦ f d)) :
    ∃ W : Fin (lowerP β).card → Label.{u},
      (lowerP β).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (lowerP β).toCellScheme.below pairL, W d = f d) ∧
      admissionP β (orbitCode 2 ((lowerP β).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsL := isLawful_privP β hf
  have hvs : IsSelfVisible 2 (privP β f 3) := isSelfVisible_of_isLawful_P hsL rfl
  have hD : rows.{u}.IsLawful fun z ↦ min (labelling (⊤ : Label.{u}) ⊤ z) (privP β f 3) :=
    isLawful_labelling_top_top.min_const_of_isSelfVisible (K := 2)
      (fun d ↦ by fin_cases d <;> decide) hvs
  obtain ⟨g, hg, hgL, hgR, -⟩ := exists_glue_lowerP β hsL hD
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_, admissionP_orbitCode β ⟨?_, ?_⟩ ⟨?_, ?_⟩⟩
  · obtain ⟨z, rfl⟩ := exists_left_of_mem_below β hd
    exact congrFun hgL z
  · rw [hgR]; exact top_top_capped_dead rfl
  · rw [hgR]; exact top_top_capped_dead rfl
  · rw [hgL, hgR]; exact le_min le_top le_rfl
  · rw [hgL, hgR]; exact le_min le_top le_rfl

/-- **The lift provision at a positive cap from the private coatom.**  The fill is the private copy
of the prescription and, on the donor copy, the donor copy of the entry, raised to the private cap
value at both full cells when the prescription is in the bottom class and the entry reads a full
cell below it (then everything involved lies at least at the cap `h`). -/
theorem capProvision_left {h : Label.{u}} (hb : ⊥ < h) {a : Fin (lowerP β).card → Label.{u}}
    (ha : (lowerP β).rows.IsLawful a) (hA : admissionP β a) {f : Fin (lowerP β).card → Label.{u}}
    (hf : (lowerP β).rows.IsLawfulBelow pairL (fun d ↦ f d))
    (hfa : ∀ d ∈ (lowerP β).toCellScheme.below pairL, min (f d) h = min (a d) h) :
    ∃ W : Fin (lowerP β).card → Label.{u},
      (lowerP β).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (lowerP β).toCellScheme.below pairL, W d = f d) ∧
      (∀ d, (lowerP β).toCellScheme.grade d ≤ 2 → min (W d) h = min (a d) h) ∧
      admissionP β (orbitCode 2 ((lowerP β).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  classical
  have hsL := isLawful_privP β hf
  have heL := isLawful_privP β (ha.isLawfulBelow pairL)
  have heR := isLawful_donP β (ha.isLawfulBelow pairR)
  have hagL (z : Fin 5) : min (privP β f z) h = min (privP β a z) h :=
    hfa _ (left_mem_below β z)
  obtain ⟨D, hD, hDa, hDT⟩ : ∃ D : Fin 5 → Label.{u}, rows.{u}.IsLawful D ∧
      (∀ z, min (D z) h = min (donP β a z) h) ∧
      (InBottomClassP (privP β f) → privP β f 3 ≤ D 3 ∧ privP β f 3 ≤ D 4) := by
    by_cases hraise : InBottomClassP (privP β f) ∧
        ¬ (privP β f 3 ≤ donP β a 3 ∧ privP β f 3 ≤ donP β a 4)
    · obtain ⟨hcl, hnot⟩ := hraise
      have hclE := inBottomClassP_of_min_eq hb hagL hcl
      have hcorr := ((isCapCorrectP_self_iff (isSelfVisible_of_isLawful_P heL rfl)).mp
        (hA hclE)).2
      have h3 : privP β a 3 ≤ donP β a 3 := hcorr 3 (by simp [selfT])
      have h4 : privP β a 3 ≤ donP β a 4 := hcorr 4 (by simp [selfT])
      obtain ⟨y, hy, hlt⟩ : ∃ y, (y = 3 ∨ y = 4) ∧ donP β a y < privP β f 3 := by
        by_contra hc
        push Not at hc
        exact hnot ⟨hc 3 (.inl rfl), hc 4 (.inr rfl)⟩
      have hey : privP β a 3 ≤ donP β a y := by rcases hy with rfl | rfl <;> assumption
      have hhe : h ≤ privP β a 3 := le_of_min_eq_of_lt (hey.trans_lt hlt) (hagL 3)
      have hsh : h ≤ privP β f 3 := hhe.trans (hey.trans hlt.le)
      have hvs : IsSelfVisible 2 (privP β f 3) := isSelfVisible_of_isLawful_P hsL rfl
      refine ⟨fun z ↦ min (labelling (⊤ : Label.{u}) ⊤ z) (privP β f 3),
        isLawful_labelling_top_top.min_const_of_isSelfVisible (K := 2)
          (fun d ↦ by fin_cases d <;> decide) hvs, fun z ↦ ?_,
        fun _ ↦ ⟨le_min le_top le_rfl, le_min le_top le_rfl⟩⟩
      rcases fin5_cases z with hz | rfl | rfl
      · simp only
        rw [top_top_capped_dead hz, eq_bot_of_isLawful_P heR hz]
      · change min (min ⊤ (privP β f 3)) h = _
        rw [min_top_left, min_eq_right hsh, min_eq_right (hhe.trans h3)]
      · change min (min ⊤ (privP β f 3)) h = _
        rw [min_top_left, min_eq_right hsh, min_eq_right (hhe.trans h4)]
    · exact ⟨donP β a, heR, fun _ ↦ rfl, fun hcl ↦ not_not.mp fun hc ↦ hraise ⟨hcl, hc⟩⟩
  obtain ⟨g, hg, hgL, hgR, hgN⟩ := exists_glue_lowerP β hsL hD
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_,
    fun d _ ↦ min_eq_of_copies β ha hgN (fun z ↦ by rw [hgL]; exact hagL z)
      (fun z ↦ by rw [hgR]; exact hDa z) d, ?_⟩
  · obtain ⟨z, rfl⟩ := exists_left_of_mem_below β hd
    exact congrFun hgL z
  · by_cases hcl : InBottomClassP (privP β f)
    · obtain ⟨h3, h4⟩ := hDT hcl
      refine admissionP_orbitCode β ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · rw [hgR]; exact eq_bot_of_isLawful_P hD rfl
      · rw [hgR]; exact eq_bot_of_isLawful_P hD rfl
      · rw [hgL, hgR]; exact h3
      · rw [hgL, hgR]; exact h4
    · exact admissionP_orbitCode_of_not β (by rw [hgL]; exact hcl)

/-- **The lift provision at the cap `⊥` from the donor coatom**: `⊥` on the private copy, so that
the fill is outside the bottom class. -/
theorem botProvision_right {f : Fin (lowerP β).card → Label.{u}}
    (hf : (lowerP β).rows.IsLawfulBelow pairR (fun d ↦ f d)) :
    ∃ W : Fin (lowerP β).card → Label.{u},
      (lowerP β).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (lowerP β).toCellScheme.below pairR, W d = f d) ∧
      admissionP β (orbitCode 2 ((lowerP β).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  obtain ⟨g, hg, hgL, hgR, -⟩ := exists_glue_lowerP β
    (CellScheme.Rows.isLawful_const_bot (R := rows.{u})) (isLawful_donP β hf)
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_, admissionP_orbitCode_of_not β ?_⟩
  · obtain ⟨z, rfl⟩ := exists_right_of_mem_below β hd
    exact congrFun hgR z
  · rw [hgL]
    exact fun hcl ↦ absurd ((hcl 3).mp rfl) (by decide)

/-- **The lift provision at a positive cap from the donor coatom.**  The fill is the donor copy of
the prescription and, on the private copy, the private copy of the entry, lowered to the least
donor value at the full cells when the entry is in the bottom class and reads its private cap above
a donor value of the prescription (then that least value is at least the cap `h`). -/
theorem capProvision_right {h : Label.{u}} {a : Fin (lowerP β).card → Label.{u}}
    (ha : (lowerP β).rows.IsLawful a) (hA : admissionP β a) {f : Fin (lowerP β).card → Label.{u}}
    (hf : (lowerP β).rows.IsLawfulBelow pairR (fun d ↦ f d))
    (hfa : ∀ d ∈ (lowerP β).toCellScheme.below pairR, min (f d) h = min (a d) h) :
    ∃ W : Fin (lowerP β).card → Label.{u},
      (lowerP β).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (lowerP β).toCellScheme.below pairR, W d = f d) ∧
      (∀ d, (lowerP β).toCellScheme.grade d ≤ 2 → min (W d) h = min (a d) h) ∧
      admissionP β (orbitCode 2 ((lowerP β).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  classical
  have hsR := isLawful_donP β hf
  have heL := isLawful_privP β (ha.isLawfulBelow pairL)
  have heR := isLawful_donP β (ha.isLawfulBelow pairR)
  have hagR (z : Fin 5) : min (donP β f z) h = min (donP β a z) h :=
    hfa _ (right_mem_below β z)
  obtain ⟨L, hL, hLa, hLT⟩ : ∃ L : Fin 5 → Label.{u}, rows.{u}.IsLawful L ∧
      (∀ z, min (L z) h = min (privP β a z) h) ∧
      (InBottomClassP L → L 3 ≤ donP β f 3 ∧ L 3 ≤ donP β f 4) := by
    by_cases hlow : InBottomClassP (privP β a) ∧
        ¬ (privP β a 3 ≤ donP β f 3 ∧ privP β a 3 ≤ donP β f 4)
    · obtain ⟨hcl, hnot⟩ := hlow
      have hcorr := ((isCapCorrectP_self_iff (isSelfVisible_of_isLawful_P heL rfl)).mp
        (hA hcl)).2
      have h3 : privP β a 3 ≤ donP β a 3 := hcorr 3 (by simp [selfT])
      have h4 : privP β a 3 ≤ donP β a 4 := hcorr 4 (by simp [selfT])
      obtain ⟨y, hy, hlt⟩ : ∃ y, (y = 3 ∨ y = 4) ∧ donP β f y < privP β a 3 := by
        by_contra hc
        push Not at hc
        exact hnot ⟨hc 3 (.inl rfl), hc 4 (.inr rfl)⟩
      have hey : privP β a 3 ≤ donP β a y := by rcases hy with rfl | rfl <;> assumption
      have hhy : h ≤ donP β f y := le_of_min_eq_of_lt (hlt.trans_le hey) (hagR y).symm
      have hhe : h ≤ privP β a 3 := hhy.trans hlt.le
      -- both donor values of the prescription lie at least at `h`
      have hge (y' : Fin 5) (hy' : privP β a 3 ≤ donP β a y') : h ≤ donP β f y' := by
        have e := hagR y'
        rw [min_eq_right ((hhe.trans hy'))] at e
        exact (min_eq_right_iff.mp e)
      have hm : h ≤ min (donP β f 3) (donP β f 4) := le_min (hge 3 h3) (hge 4 h4)
      have hmv : IsSelfVisible 2 (min (donP β f 3) (donP β f 4)) := by
        rcases min_choice (donP β f 3) (donP β f 4) with e | e <;> rw [e] <;>
          exact isSelfVisible_of_isLawful_P hsR rfl
      refine ⟨fun z ↦ min (privP β a z) (min (donP β f 3) (donP β f 4)),
        heL.min_const_of_isSelfVisible (K := 2) (fun d ↦ by fin_cases d <;> decide) hmv,
        fun z ↦ ?_, fun _ ↦ ⟨(min_le_right _ _).trans (min_le_left _ _),
          (min_le_right _ _).trans (min_le_right _ _)⟩⟩
      simp only
      rw [min_assoc, min_eq_right hm]
    · refine ⟨privP β a, heL, fun _ ↦ rfl, fun hcl ↦ not_not.mp fun hc ↦ hlow ⟨hcl, hc⟩⟩
  obtain ⟨g, hg, hgL, hgR, hgN⟩ := exists_glue_lowerP β hL hsR
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_,
    fun d _ ↦ min_eq_of_copies β ha hgN (fun z ↦ by rw [hgL]; exact hLa z)
      (fun z ↦ by rw [hgR]; exact hagR z) d, ?_⟩
  · obtain ⟨z, rfl⟩ := exists_right_of_mem_below β hd
    exact congrFun hgR z
  · by_cases hcl : InBottomClassP L
    · obtain ⟨h3, h4⟩ := hLT hcl
      refine admissionP_orbitCode β ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · rw [hgR]; exact eq_bot_of_isLawful_P hsR rfl
      · rw [hgR]; exact eq_bot_of_isLawful_P hsR rfl
      · rw [hgL, hgR]; exact h3
      · rw [hgL, hgR]; exact h4
    · exact admissionP_orbitCode_of_not β (by rw [hgL]; exact hcl)

/-! ### Bountifulness and legality of the admitted layer at `P` -/

/-- The lower scheme is consistent. -/
theorem isConsistent_lowerP : (lowerP β).rows.IsConsistent :=
  Scheme.isConsistent_appendFullCells (seedP β).isConsistent fun i ↦
    ((seedP β).isDoubling_doubledLower rfl).isLawful_comp
      (Scheme.isLawful_rowAt (isLegal_P β).isConsistent (Scheme.gradedIndex_fullCell 1 i))

/-- The lower scheme is well formed. -/
theorem isWellFormed_lowerP : (lowerP β).IsWellFormed :=
  Scheme.isWellFormed_appendFullCells (h := (seedP β).not_univ_le 1)
    (seedP β).amalgam.isWellFormed one_pos (by omega)

/-- The lower scheme is coded. -/
theorem isCoded_lowerP : (lowerP β).IsCoded :=
  Scheme.isCoded_appendFullCells (h := (seedP β).not_univ_le 1) (seedP β).amalgam.isCoded fun _ _ ↦
    (P β).isCoded.rowAt_lt _ _

private theorem erase_ne_univ (x : Fin 3) : univ.erase x ≠ univ :=
  fun he ↦ Finset.notMem_erase x univ (he.symm ▸ mem_univ x)

/-- The private cap `3` of the private copy lies at the private coatom pair. -/
theorem gradedIndex_left_three :
    (lowerP β).toCellScheme.gradedIndex
      (Fin.castAdd _ (StageType.faceCell (seedP β).restrictFace_left
        ((3 : Fin 5) : Fin (seedP β).left.card))) = pairL := by
  refine (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans (Prod.ext ?_ ?_)
  · exact (StageType.scope_faceCell (seedP β).restrictFace_left
      ((3 : Fin 5) : Fin (seedP β).left.card)).trans (Coatom.univ_map_left (m := 1))
  · exact StageType.grade_faceCell (seedP β).restrictFace_left
      ((3 : Fin 5) : Fin (seedP β).left.card)

/-- The cap `3` of the donor copy lies at the donor coatom pair. -/
theorem gradedIndex_right_three :
    (lowerP β).toCellScheme.gradedIndex
      (Fin.castAdd _ (StageType.faceCell ((seedP β).restrictFace_right_left rfl)
        ((3 : Fin 5) : Fin (seedP β).left.card))) = pairR := by
  refine (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans (Prod.ext ?_ ?_)
  · exact (StageType.scope_faceCell ((seedP β).restrictFace_right_left rfl)
      ((3 : Fin 5) : Fin (seedP β).left.card)).trans (Coatom.univ_map_right (m := 1))
  · exact StageType.grade_faceCell ((seedP β).restrictFace_right_left rfl)
      ((3 : Fin 5) : Fin (seedP β).left.card)

/-- **The lift from the private coatom into the admitted layer at `P`.** -/
theorem cappedLift_admittedLayerP_left :
    (admittedLayerP β).rows.CappedLift (X := pairL) (Y := ((univ : Finset (Fin 3)), 2))
      ⟨erase_subset _ _, le_rfl⟩ :=
  Scheme.cappedLift_admittedFieldLayer (j := 1) (hS := not_univ_two_le_lowerP β)
    (isConsistent_lowerP β) (admissionP_bot β) (erase_ne_univ _) ⟨_, gradedIndex_left_three β⟩
    (cappedLift_lowerP_one β _) (fun _ hf ↦ botProvision_left β hf)
    (fun _ _ _ hb _ ha hA _ hf hfa ↦ capProvision_left β hb ha hA hf hfa)

/-- **The lift from the donor coatom into the admitted layer at `P`.** -/
theorem cappedLift_admittedLayerP_right :
    (admittedLayerP β).rows.CappedLift (X := pairR) (Y := ((univ : Finset (Fin 3)), 2))
      ⟨erase_subset _ _, le_rfl⟩ :=
  Scheme.cappedLift_admittedFieldLayer (j := 1) (hS := not_univ_two_le_lowerP β)
    (isConsistent_lowerP β) (admissionP_bot β) (erase_ne_univ _) ⟨_, gradedIndex_right_three β⟩
    (cappedLift_lowerP_one β _) (fun _ hf ↦ botProvision_right β hf)
    (fun _ _ _ _ _ ha hA _ hf hfa ↦ capProvision_right β ha hA hf hfa)

/-- **The admitted layer at `P` is bountiful.** -/
theorem isBountiful_admittedLayerP : (admittedLayerP β).rows.IsBountiful :=
  (seedP β).isBountiful_admittedDoubledLower rfl (cappedLift_lowerP_one β)
    (cappedLift_admittedLayerP_left β) (cappedLift_admittedLayerP_right β)

/-- **The admitted layer at `P` is legal below the full grade.** -/
theorem isLegalBelowFullGrade_admittedLayerP : (admittedLayerP β).IsLegalBelowFullGrade :=
  (seedP β).isLegalBelowFullGrade_admittedDoubledLower rfl (isLegal_P β) (admissionP_bot β)
    (isBountiful_admittedLayerP β)

end GatedExtensionCounterexample




end VaughtConjecture
