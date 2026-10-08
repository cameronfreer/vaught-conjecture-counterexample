/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AdmittedFieldLayer
import VaughtConjecture.Extension.OwnerCappedLift
import VaughtConjecture.Extension.Restoration
import VaughtConjecture.Continuation.SourceGapDoubledCompletion

/-!
# The admitted field layer over a doubled lower layer: the generic lifts

Roadmap, Layer 3, 3.1, (R6) (the completion below the full grade with a restricted catalogue at the
reading grades).

The declarations of this file are those of the (R4) lane at commit `6b12c71`
(`VaughtConjecture.Continuation.StableRecoveryAdmittedLift`,
`VaughtConjecture.Continuation.StableRecoveryAdmittedLayerP` and
`VaughtConjecture.Continuation.StableRecoveryAdmittedBountiful`, the parts not specific to the
input `P`), reproduced here unchanged except that the lifts at the grade `1` asked by
`Seed.isBountiful_admittedDoubledLower` are asked only from the two coatoms (there, from every
face `univ.erase z`).  When that lane is
merged, this file is to be removed in favour of those modules.

* `Scheme.isLawfulBelow_faceCell_iff`, `Seed.exists_isLawful_glue`: gluing two lawful labellings of
  `T` on the amalgam of `T` with itself.
* `Scheme.exists_isLawfulBelow_fieldLayerOn`, `Scheme.exists_extension_fieldLayerOn`,
  `Scheme.exists_lift_bot_admittedFieldLayer`, `Scheme.exists_lift_admittedFieldLayer`: extension
  through a field layer on a sub-catalogue.
* `Scheme.cappedLift_admittedFieldLayer`: the coatom lift into an admitted field layer under the
  lift provisions at the cap `⊥` and at the short positive caps.
* `Seed.isBountiful_admittedDoubledLower`, `Seed.isLegalBelowFullGrade_admittedDoubledLower`: the
  admitted layer at the grade `2` over the doubled lower layer of a seed with equal coatom types.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

/-! ### Lawfulness through a face -/

namespace Scheme

variable {n m : ℕ} {S : Scheme.{u} n} {f : Fin m ↪ Fin n} {T : Scheme.{u} m}

/-- **Lawfulness through a face**: a labelling of `S` read on the cells of a face `T` along `f` is
lawful below `X` in `T` exactly when it is lawful below the image of `X` in `S`. -/
theorem isLawfulBelow_faceCell_iff (he : S.comap f = T) (X : Finset (Fin m) × ℕ)
    (x : Fin S.card → Label.{u}) :
    T.rows.IsLawfulBelow X (fun i ↦ x (S.faceCell f he i)) ↔
      S.rows.IsLawfulBelow (Prod.map (Finset.map f) id X) (fun d ↦ x d) := by
  subst he
  exact S.isLawfulBelow_comap_cellMap_iff f X x

end Scheme

/-! ### Gluing two labellings on the amalgam of a type with itself -/

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (hLR : I.left = I.right)

/-- A copy along the second coatom that also lies on the first is a cell of `T` avoiding the last
point. -/
theorem last_notMem_of_faceCell_right_mem {z : Fin I.left.card}
    (hz : StageType.faceCell (I.restrictFace_right_left hLR) z ∈
      I.amalgam.toScheme.visibleCells (Coatom.left m)) :
    Fin.last m ∉ I.left.toCellScheme.scope z := by
  intro hm
  have h := I.faceCell_left_doublingCell hLR hz
  rw [I.doublingCell_faceCell_right hLR] at h
  have hs := congrArg (fun d ↦ I.amalgam.toCellScheme.scope d) h
  simp only [StageType.scope_faceCell] at hs
  have hl : Coatom.right m (Fin.last m) ∈ (I.left.toCellScheme.scope z).map (Coatom.left m) :=
    hs ▸ mem_map_of_mem _ hm
  obtain ⟨y, -, hy⟩ := mem_map.mp hl
  rw [Coatom.right, extendByLast_last] at hy
  exact (Fin.castSucc_lt_last y).ne hy

open Classical in
/-- **Gluing on the amalgam**: two lawful labellings of `T` agreeing at the cells avoiding the last
point glue to a lawful labelling of the amalgam of `T` with itself, the first on the copies along
the first coatom and the second on the copies along the second. -/
theorem exists_isLawful_glue {sL sR : Fin I.left.card → Label.{u}}
    (hL : I.left.rows.IsLawful sL) (hR : I.left.rows.IsLawful sR)
    (hagree : ∀ z, Fin.last m ∉ I.left.toCellScheme.scope z → sL z = sR z) :
    ∃ w : Fin I.amalgam.card → Label.{u}, I.amalgam.rows.IsLawful w ∧
      (∀ z, w (StageType.faceCell I.restrictFace_left z) = sL z) ∧
      ∀ z, w (StageType.faceCell (I.restrictFace_right_left hLR) z) = sR z := by
  set w : Fin I.amalgam.card → Label.{u} := fun d ↦
    if d ∈ I.amalgam.toScheme.visibleCells (Coatom.left m) then sL (I.doublingCell hLR d)
    else sR (I.doublingCell hLR d)
  have hwL (z : Fin I.left.card) : w (StageType.faceCell I.restrictFace_left z) = sL z := by
    have h : StageType.faceCell I.restrictFace_left z ∈
        I.amalgam.toScheme.visibleCells (Coatom.left m) :=
      I.amalgam.toScheme.faceCell_mem_visibleCells _ z
    simp only [w, h, ↓reduceIte, I.doublingCell_faceCell_left hLR]
  have hwR (z : Fin I.left.card) :
      w (StageType.faceCell (I.restrictFace_right_left hLR) z) = sR z := by
    by_cases h : StageType.faceCell (I.restrictFace_right_left hLR) z ∈
        I.amalgam.toScheme.visibleCells (Coatom.left m)
    · simp only [w, h, ↓reduceIte, I.doublingCell_faceCell_right hLR]
      exact hagree z (I.last_notMem_of_faceCell_right_mem hLR h)
    · simp only [w, h, ↓reduceIte, I.doublingCell_faceCell_right hLR]
  have hU : I.amalgam.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))).map (Coatom.left m),
      m + 1) fun d ↦ w d := by
    refine (Scheme.isLawfulBelow_faceCell_iff
      (StageType.comap_toScheme_of_restrictFace I.restrictFace_left) (univ, m + 1) w).mp ?_
    convert hL.isLawfulBelow ((univ : Finset (Fin (m + 1))), m + 1) using 1
    funext i
    exact hwL i
  have hV : I.amalgam.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))).map (Coatom.right m),
      m + 1) fun d ↦ w d := by
    refine (Scheme.isLawfulBelow_faceCell_iff
      (StageType.comap_toScheme_of_restrictFace (I.restrictFace_right_left hLR)) (univ, m + 1)
        w).mp ?_
    convert hR.isLawfulBelow ((univ : Finset (Fin (m + 1))), m + 1) using 1
    funext i
    exact hwR i
  have hgrade (d : Fin I.amalgam.card) : I.amalgam.toCellScheme.grade d ≤ m + 1 :=
    Nat.lt_succ_iff.mp (I.grade_lt d)
  have hY : I.amalgam.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), m + 1)
      fun d ↦ w d := by
    refine CellScheme.Rows.IsLawfulBelow.glue hU hV fun d _ ↦ ?_
    rcases I.mem_visibleCells_or d with hd | hd
    · refine Or.inl ⟨fun x hx ↦ ?_, hgrade d⟩
      obtain ⟨y, hy⟩ := Scheme.mem_visibleCells.mp hd hx
      exact mem_map.mpr ⟨y, mem_univ _, hy⟩
    · refine Or.inr ⟨fun x hx ↦ ?_, hgrade d⟩
      obtain ⟨y, hy⟩ := Scheme.mem_visibleCells.mp hd hx
      exact mem_map.mpr ⟨y, mem_univ _, hy⟩
  exact ⟨w, hY.isLawful fun d ↦ ⟨subset_univ _, hgrade d⟩, hwL, hwR⟩

end Seed

/-! ### Extension through a field layer on a sub-catalogue -/

namespace Scheme

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

end Scheme

/-! ### Every cell of the amalgam is a copy -/

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (hLR : I.left = I.right)

/-- Every cell of the amalgam of a type with itself is the copy of its cell of `T` along one of the
two coatoms. -/
theorem eq_faceCell_or (d : Fin I.amalgam.card) :
    StageType.faceCell I.restrictFace_left (I.doublingCell hLR d) = d ∨
      StageType.faceCell (I.restrictFace_right_left hLR) (I.doublingCell hLR d) = d :=
  (I.mem_visibleCells_or d).imp (I.faceCell_left_doublingCell hLR)
    (I.faceCell_right_doublingCell hLR)

end Seed

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
    (h1 : ∀ z : Fin 3, (z = Fin.last 2 ∨ z = Fin.castSucc (Fin.last 1)) →
      (I.doubledLower hLR).rows.CappedLift (X := (univ.erase z, 1))
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
  have hone (z : Fin 3) (hz : z = Fin.last 2 ∨ z = Fin.castSucc (Fin.last 1)) :
      F.rows.CappedLift (X := (univ.erase z, 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨subset_univ _, le_rfl⟩ := by
    refine (hsp1.cappedLift_iff _ le_rfl).mp ?_
    change (F.rows.comap hemb).CappedLift _
    rw [e1]
    exact h1 z hz
  have hle (z : Fin 3) (j : ℕ) (hj : j ≤ #(univ.erase z)) : j ≤ 2 := by
    rw [card_erase_of_mem (mem_univ z)] at hj
    simpa using hj
  have hfull (z : Fin 3) (hz : z = Fin.last 2 ∨ z = Fin.castSucc (Fin.last 1))
      (hlift2 : F.rows.CappedLift (X := (univ.erase z, 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩) (j : ℕ) (hj : j ≤ 2) :
      F.rows.CappedLift (X := (univ.erase z, j)) (Y := ((univ : Finset (Fin 3)), j))
        ⟨erase_subset _ _, le_rfl⟩ := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · exact (I.isWellFormed_admittedDoubledLower hLR).isWellFormed.cappedLift _ (Or.inl rfl) _
    · exact hone _ hz
    · exact hlift2
  refine CellScheme.Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last 2)
    (b := Fin.castSucc (Fin.last 1)) (mem_univ _) (mem_univ _) I.subset_or_subset
    I.erase_last_mem_faces I.erase_castSucc_mem_faces (fun X Y hX hY hXY hYne ↦ ?_)
    (fun j hj ↦ hfull _ (.inl rfl) hL j (hle _ j hj))
    (fun j hj ↦ hfull _ (.inr rfl) hR j (hle _ j hj))
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

end VaughtConjecture
