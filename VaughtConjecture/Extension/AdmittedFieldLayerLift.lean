/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AdmittedFieldLayerCells
import VaughtConjecture.Extension.OwnerCappedLift
import VaughtConjecture.Extension.Restoration

/-!
# Extension and lifts through an admitted field layer

Roadmap, Layer 3, 3.1, (R6) (the completion below the full grade with a restricted catalogue at the
reading grades); the admitted field layer of `VaughtConjecture.Extension.AdmittedFieldLayer`.

**Extension through a field layer on a sub-catalogue, by a chosen template.**  The lifts of the
canonical field layer extend a boundary labelling by the field row of the orbit code of the
labelling itself.  On a sub-catalogue `C` the same proofs go through as soon as that orbit code
lies in `C`: `Scheme.exists_isLawfulBelow_fieldLayerOn` (cap `⊥`) and
`Scheme.exists_extension_fieldLayerOn` (short positive cap), and for the admitted field layer
`Scheme.exists_lift_bot_admittedFieldLayer` and `Scheme.exists_lift_admittedFieldLayer`.

**The coatom lift into an admitted field layer** (`Scheme.cappedLift_admittedFieldLayer`): under
the two lift provisions at a face `U` (at the cap `⊥` and at the short positive caps), the
admitted field layer lifts capped from `(U, j + 1)` to `(univ, j + 1)`, by the one-grade lift
`CellScheme.Rows.cappedLift_of_ownerCappedLift`.

These statements quantify over arbitrary schemes, sub-catalogues and admissions; their instances
at the private type `P` are in `VaughtConjecture.Continuation.StableRecoveryAdmittedLayerP` and
`VaughtConjecture.Continuation.StableRecoveryAdmittedBountiful`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

/-! ### Extension through a field layer on a sub-catalogue -/

namespace Scheme

section SubCatalogue

variable {n k : ℕ} {S : Scheme.{u} n} {C : Finset (Fin S.card → Label.{u})}
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- An old cell of grade at most `k` lies below `(univ, k)` in the field layer on `C`. -/
theorem castAdd_mem_below_fieldLayerOn {d : Fin S.card} (hd : S.toCellScheme.grade d ≤ k) :
    Fin.castAdd C.card d ∈ (S.fieldLayerOn k C hS).toCellScheme.below (univ, k) :=
  ⟨subset_univ _, (appendFullCellsScheme_grade_castAdd S k _ d).trans_le hd⟩

/-- **Extension at the cap `⊥` through a field layer on a sub-catalogue**: a labelling of `S` whose
orbit code (of its splice) lies in `C` (so the splice is lawful below `(univ, k)`) extends,
unchanged at the old cells
of grade at most `k`, to a labelling lawful below `(univ, k)` in the field layer on `C`: the field
row of that code, read by the orbit decoder at the least grid point. -/
theorem exists_isLawfulBelow_fieldLayerOn (hC : C ⊆ S.catalogue k) {p : Fin S.card → Label.{u}}
    (hb : orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) p) ∈ C) :
    ∃ r : (S.fieldLayerOn k C hS).toCellScheme.below (univ, k) → Label.{u},
      (S.fieldLayerOn k C hS).rows.IsLawfulBelow (univ, k) r ∧
        ∀ d (hd : S.toCellScheme.grade d ≤ k),
          r ⟨Fin.castAdd _ d, castAdd_mem_below_fieldLayerOn hd⟩ = p d := by
  set t := S.toCellScheme.splice k (fun _ ↦ ⊥) p
  refine ⟨fun x ↦ orbitDecoder k t (gridPoint k 0) (S.fieldRowOn k C (orbitCode k t) x),
    ((isLawful_fieldRowOn (hS := hS) (hC hb) hb).isLawfulBelow _).map_of_apply_eq_bot
      (fun x ↦ x.2.2)
      (isWitness_orbitDecoder (isSelfVisible_gridPoint k 0) (gridPoint_ne_bot k 0))
      fun _ ↦ eq_bot_of_orbitDecoder_eq_bot (gridPoint_ne_bot k 0), fun d hd ↦ ?_⟩
  change orbitDecoder k t (gridPoint k 0) (S.fieldRowOn k C (orbitCode k t) (Fin.castAdd _ d)) =
    p d
  rw [fieldRowOn_castAdd, orbitDecoder_orbitCode (fun e ↦ min_orbitCode_gridPoint_zero e)]
  exact CellScheme.splice_of_le hd

/-- **Extension through a field layer on a sub-catalogue at a short positive cap.**  Let `p` be a
labelling of `S` with its orbit code in `C`, `a ∈ C` a catalogue entry, and `h`
self-visible and short at `k` with `⊥ < h`, such that `p` agrees with `a` capped at `h` at the
cells of grade at most `k`.  Then some labelling lawful below `(univ, k)` in the field layer on `C`
reads `p` at the old cells of grade at most `k` and agrees with the field row of `a` capped at `h`
at every cell below `(univ, k)` (the proof of `Scheme.exists_extension_fieldLayer`, short case). -/
theorem exists_extension_fieldLayerOn (hC : C ⊆ S.catalogue k) {p : Fin S.card → Label.{u}}
    (hb : orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) p) ∈ C)
    {a : Fin S.card → Label.{u}} (haC : a ∈ C) {h : Label.{u}} (hh : IsSelfVisible k h)
    (hs : IsShort k h) (hbot : ⊥ < h)
    (hag : ∀ d, S.toCellScheme.grade d ≤ k → min (p d) h = min (a d) h) :
    ∃ r : (S.fieldLayerOn k C hS).toCellScheme.below (univ, k) → Label.{u},
      (S.fieldLayerOn k C hS).rows.IsLawfulBelow (univ, k) r ∧
        (∀ d (hd : S.toCellScheme.grade d ≤ k),
          r ⟨Fin.castAdd _ d, castAdd_mem_below_fieldLayerOn hd⟩ = p d) ∧
          ∀ x, min (r x) h = min (S.fieldRowOn k C a x) h := by
  set t := S.toCellScheme.splice k (fun _ ↦ ⊥) p with ht_def
  have htle (d : Fin S.card) (hd : S.toCellScheme.grade d ≤ k) : t d = p d :=
    CellScheme.splice_of_le hd
  have htgt (d : Fin S.card) (hd : ¬ S.toCellScheme.grade d ≤ k) : t d = ⊥ :=
    CellScheme.splice_of_lt (not_le.mp hd)
  set b := orbitCode k t
  have ha : a ∈ S.catalogue k := hC haC
  obtain ⟨-, haup, haa⟩ := mem_catalogue.mp ha
  have hagt (d : Fin S.card) : min (t d) h = min (a d) h := by
    by_cases hd : S.toCellScheme.grade d ≤ k
    · rw [htle d hd]
      exact hag d hd
    · rw [htgt d hd, haup d (not_le.mp hd)]
  have hba (d : Fin S.card) : min (b d) h = min (a d) h := min_orbitCode_eq hh hs haa hagt d
  have hrowh (x : Fin (S.card + C.card)) :
      min (S.fieldRowOn k C b x) h = min (S.fieldRowOn k C a x) h := by
    induction x using Fin.addCases with
    | left d => rw [fieldRowOn_castAdd, fieldRowOn_castAdd]; exact hba d
    | right j =>
      rw [fieldRowOn_natAdd, fieldRowOn_natAdd]
      exact min_agreementHeight_eq_of_isShort hh hs
        (fun d ↦ ⟨codeGrid_mono (by omega) (mem_codeGrid_of_mem_catalogue (hC hb) d),
          codeGrid_mono (by omega) (mem_codeGrid_of_mem_catalogue ha d)⟩) hba _
  have hread (d : Fin S.card) : orbitDecoder k t h (b d) = t d :=
    orbitDecoder_orbitCode (fun e ↦ (hba e).trans (hagt e).symm) d
  have hcapr (x : Fin (S.card + C.card)) :
      min (orbitDecoder k t h (S.fieldRowOn k C b x)) h = min (S.fieldRowOn k C a x) h := by
    induction x using Fin.addCases with
    | left d => rw [fieldRowOn_castAdd, fieldRowOn_castAdd, hread]; exact hagt d
    | right j =>
      rw [min_orbitDecoder_eq (by
          rw [fieldRowOn_natAdd]
          exact isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid _ _) _ _).1)]
      exact hrowh _
  refine ⟨fun x ↦ orbitDecoder k t h (S.fieldRowOn k C b x),
    ((isLawful_fieldRowOn (hS := hS) (hC hb) hb).isLawfulBelow _).map_of_min_eq
      ((isLawful_fieldRowOn (hS := hS) ha haC).isLawfulBelow _) (fun x ↦ x.2.2)
      (isWitness_orbitDecoder hh hbot.ne') hbot.ne' fun x ↦ hcapr x.1, fun d hd ↦ ?_,
    fun x ↦ hcapr x.1⟩
  change orbitDecoder k t h (S.fieldRowOn k C b (Fin.castAdd _ d)) = p d
  rw [fieldRowOn_castAdd, hread, htle d hd]

/-! ### The admitted field layer: extension by an admitted template -/

variable {A : (Fin S.card → Label.{u}) → Prop}

/-- **Extension through the admitted field layer at the cap `⊥`**: a labelling lawful below
`(univ, k)` whose orbit code is admitted extends, unchanged at the old cells of grade at most `k`,
to a labelling lawful below `(univ, k)` in the admitted field layer. -/
theorem exists_lift_bot_admittedFieldLayer {g : Fin S.card → Label.{u}}
    (hg : S.rows.IsLawfulBelow (univ, k) fun d ↦ g d)
    (hA : A (orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) g))) :
    ∃ v : Fin (S.card + (S.admittedCatalogue k A).card) → Label.{u},
      (S.admittedFieldLayer k A hS).rows.IsLawfulBelow (univ, k) (fun x ↦ v x) ∧
        ∀ d, S.toCellScheme.grade d ≤ k → v (Fin.castAdd _ d) = g d := by
  classical
  obtain ⟨r, hr, hre⟩ := exists_isLawfulBelow_fieldLayerOn (hS := hS) admittedCatalogue_subset
    (mem_admittedCatalogue.mpr ⟨orbitCode_splice_bot_mem_catalogue hg, hA⟩)
  refine ⟨fun x ↦ if hx : x ∈ (S.admittedFieldLayer k A hS).toCellScheme.below (univ, k)
    then r ⟨x, hx⟩ else ⊥, ?_, fun d hd ↦ ?_⟩
  · convert hr using 1
    funext x
    exact dite_eq_left x.2
  · exact (dite_eq_left (castAdd_mem_below_fieldLayerOn hd)).trans (hre d hd)

/-- **Extension through the admitted field layer at a short positive cap**: if moreover the orbit
code `a` of a labelling `g₄` lawful below `(univ, k)` is admitted and agrees with `g` capped at
`h`, the extension agrees with the field row of `a` capped at `h`. -/
theorem exists_lift_admittedFieldLayer {g g₄ : Fin S.card → Label.{u}}
    (hg : S.rows.IsLawfulBelow (univ, k) fun d ↦ g d)
    (hA : A (orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) g)))
    (hg₄ : S.rows.IsLawfulBelow (univ, k) fun d ↦ g₄ d)
    (hA₄ : A (orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) g₄)))
    {h : Label.{u}} (hh : IsSelfVisible k h) (hs : IsShort k h) (hbot : ⊥ < h)
    (hag : ∀ d, S.toCellScheme.grade d ≤ k →
      min (g d) h = min (orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) g₄) d) h) :
    ∃ v : Fin (S.card + (S.admittedCatalogue k A).card) → Label.{u},
      (S.admittedFieldLayer k A hS).rows.IsLawfulBelow (univ, k) (fun x ↦ v x) ∧
        (∀ d, S.toCellScheme.grade d ≤ k → v (Fin.castAdd _ d) = g d) ∧
        ∀ x ∈ (S.admittedFieldLayer k A hS).toCellScheme.below (univ, k),
          min (v x) h = min (S.fieldRowOn k (S.admittedCatalogue k A)
            (orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) g₄)) x) h := by
  classical
  obtain ⟨r, hr, hre, hcap⟩ := exists_extension_fieldLayerOn (hS := hS) admittedCatalogue_subset
    (mem_admittedCatalogue.mpr ⟨orbitCode_splice_bot_mem_catalogue hg, hA⟩)
    (mem_admittedCatalogue.mpr ⟨orbitCode_splice_bot_mem_catalogue hg₄, hA₄⟩) hh hs hbot hag
  refine ⟨fun x ↦ if hx : x ∈ (S.admittedFieldLayer k A hS).toCellScheme.below (univ, k)
    then r ⟨x, hx⟩ else ⊥, ?_, fun d hd ↦ ?_, fun x hx ↦ ?_⟩
  · convert hr using 1
    funext x
    exact dite_eq_left x.2
  · exact (dite_eq_left (castAdd_mem_below_fieldLayerOn hd)).trans (hre d hd)
  · exact (congrArg (min · h) (dite_eq_left hx)).trans (hcap ⟨x, hx⟩)

end SubCatalogue

/-! ### The coatom lift into an admitted field layer -/

section Lift

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

end Lift

end Scheme

end VaughtConjecture
