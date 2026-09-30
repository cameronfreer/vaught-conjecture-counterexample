/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fintype.Sort
import VaughtConjecture.Extension.CoatomScheme
import VaughtConjecture.Stage.Legal

/-!
# The amalgam of two coatom stage types, with its literal faces

Roadmap, Layer 3 (the coatom extension construction: the constructed finite object as data, and
its literal ordered face-map restrictions); semantic contract, items 2–4.

The amalgamated cell scheme of `VaughtConjecture.Extension.CoatomScheme` has the cells of the
merge of the two given cell chains.  Enumerating them in the merged order (`Coatom.amalgamEnum`)
gives a scheme on `m + 2` points (`Coatom.amalgam h`), whose restrictions to the two coatoms are
**literally** the two given schemes, cells in the same order and rows included
(`Coatom.comap_left_amalgam`, `Coatom.comap_right_amalgam`).

For stage types `ta` and `tb` on `m + 1` points with the same face `p` along `Fin.castSuccEmb`,
the labels of `ta` and `tb` glue to a lawful labelling of the amalgam, since every cell lies on one
of the two coatoms.  This gives the stage type `Coatom.amalgamType hta htb` on `m + 2` points
whose faces along `Fin.castSuccEmb` and `extendByLast Fin.castSuccEmb` are literally `ta` and `tb`,
labels included (`Coatom.restrictFace_left_amalgamType`, `Coatom.restrictFace_right_amalgamType`).
When `ta` and `tb` are legal, its rows are consistent and bountiful [Kni26, Lemma 4.3.2] and every
graded face other than those of full scope is the graded index of a cell
(`Coatom.isLegal_amalgamType_iff`): the amalgam is legal exactly when it is complete at the full
face, which it is not, since it has no cell of full scope.  Adding cells of full scope, and
labels for them, is the completion of [Kni26, Definition 4.3.14], not constructed here; the
coatom extension property `StageType.HasCoatomExtensions` of
`VaughtConjecture.Extension.PinnedExtension` asks for such a completion.

## Placement

`StageType.label_eq_of_eq` belongs in `VaughtConjecture.Stage.Basic`, beside `StageType.ext`.  It
is stated here so that that file is unchanged.

## References

The amalgam is [Kni26, Definition 4.3.1] and its consistency and bountifulness are
[Kni26, Lemma 4.3.2], for R. W. Knight, *A counterexample to Vaught's Conjecture using generalised
Stone spaces* (draft, 20 February 2026) [Kni26].
-/

universe u

namespace VaughtConjecture.Coatom

open Finset Label

variable {m : ℕ} {Sa Sb : Scheme.{u} (m + 1)} (h : Sa.comap (face m) = Sb.comap (face m))

/-! ### The amalgamated scheme on `m + 2` points -/

variable (Sa Sb) in
/-- The number of cells of the amalgam. -/
noncomputable def amalgamCard : ℕ := Sa.card + (Sb.card - (Sa.comap (face m)).card)

/-- The cells of the amalgam, enumerated in the merged order. -/
noncomputable def amalgamEnum : Fin (amalgamCard Sa Sb) ≃o AmalgamCell h :=
  Fintype.orderIsoFinOfCardEq (AmalgamCell h) (Merge.card _ _)

/-- The **amalgamated scheme** of two coatom schemes, on `m + 2` points [Kni26, Definition 4.3.1]:
the amalgamated cell scheme with its cells enumerated in the merged order. -/
noncomputable def amalgam : Scheme.{u} (m + 2) where
  card := amalgamCard Sa Sb
  toCellScheme := (amalgamCellScheme h).reindex (amalgamEnum h).toEquiv
  rows := (amalgamRows h).comap
    (CellScheme.IsLowerEmbedding.reindex (amalgamCellScheme h) (amalgamEnum h).toEquiv)

@[simp] theorem amalgam_card : (amalgam h).card = amalgamCard Sa Sb := rfl

@[simp] theorem amalgam_ground : (amalgam h).toCellScheme.ground = univ := rfl

@[simp] theorem amalgam_faces : (amalgam h).toCellScheme.faces = amalgamFaces Sa Sb := rfl

@[simp] theorem amalgam_scope (d : Fin (amalgam h).card) :
    (amalgam h).toCellScheme.scope d = (amalgamCellScheme h).scope (amalgamEnum h d) := rfl

@[simp] theorem amalgam_grade (d : Fin (amalgam h).card) :
    (amalgam h).toCellScheme.grade d = (amalgamCellScheme h).grade (amalgamEnum h d) := rfl

/-- The amalgamated scheme is well formed. -/
theorem isWellFormed_amalgam (hSa : Sa.IsWellFormed) (hSb : Sb.IsWellFormed)
    (hf : univ.map (face m) ∈ Sa.toCellScheme.faces) : (amalgam h).IsWellFormed where
  ground_eq := rfl
  isWellFormed := (isWellFormed_amalgamCellScheme h hSa hSb hf).reindex _

/-- The rows of the amalgamated scheme are coded. -/
theorem isCoded_amalgam (hSa : Sa.IsCoded) (hSb : Sb.IsCoded) : (amalgam h).IsCoded :=
  fun s _ ↦ isCoded_amalgamRows h hSa hSb (amalgamEnum h s) _

/-- The rows of the amalgamated scheme are consistent. -/
theorem isConsistent_amalgam (hSa : Sa.rows.IsConsistent) (hSb : Sb.rows.IsConsistent) :
    (amalgam h).rows.IsConsistent :=
  (isConsistent_amalgamRows h hSa hSb).comap (CellScheme.IsLowerEmbedding.reindex _ _)

/-- **The rows of the amalgamated scheme are bountiful** [Kni26, Lemma 4.3.2]. -/
theorem isBountiful_amalgam (hSa : Sa.IsWellFormed) (hSb : Sb.IsWellFormed)
    (hf : univ.map (face m) ∈ Sa.toCellScheme.faces) (hSaB : Sa.rows.IsBountiful)
    (hSbB : Sb.rows.IsBountiful) : (amalgam h).rows.IsBountiful :=
  (isBountiful_amalgamRows h hSa hSb hf hSaB hSbB).reindex _

/-- No cell of the amalgamated scheme has the full scope. -/
theorem amalgam_scope_ne_univ (d : Fin (amalgam h).card) :
    (amalgam h).toCellScheme.scope d ≠ univ :=
  amalgamScope_ne_univ h _

/-- Every graded face of the amalgamated scheme other than those of full scope is the graded index
of a cell, when the given schemes are complete. -/
theorem exists_gradedIndex_eq_amalgam' (hSaC : Sa.toCellScheme.IsComplete)
    (hSbC : Sb.toCellScheme.IsComplete) {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ (amalgam h).toCellScheme.gradedFaces) (hne : X.1 ≠ univ) :
    ∃ d, (amalgam h).toCellScheme.gradedIndex d = X := by
  obtain ⟨x, hx⟩ := exists_gradedIndex_eq_amalgam h hSaC hSbC hX hne
  refine ⟨(amalgamEnum h).symm x, ?_⟩
  change (amalgamCellScheme h).gradedIndex (amalgamEnum h ((amalgamEnum h).symm x)) = X
  rw [OrderIso.apply_symm_apply]
  exact hx

/-! ### The literal faces -/

/-- The position in the amalgam of a cell of `Sa`. -/
noncomputable def posLeft (i : Fin Sa.card) : Fin (amalgam h).card :=
  (amalgamEnum h).symm (.inl i)

/-- The position in the amalgam of a cell of `Sb`. -/
noncomputable def posRight (j : Fin Sb.card) : Fin (amalgam h).card :=
  (amalgamEnum h).symm (Merge.rightFun _ _ j)

theorem strictMono_posLeft : StrictMono (posLeft h) :=
  (amalgamEnum h).symm.strictMono.comp (Merge.left _ (overlap h)).strictMono

theorem strictMono_posRight : StrictMono (posRight h) :=
  (amalgamEnum h).symm.strictMono.comp (Merge.right _ (overlap h)).strictMono

@[simp] theorem amalgamEnum_posLeft (i : Fin Sa.card) :
    amalgamEnum h (posLeft h i) = .inl i :=
  (amalgamEnum h).apply_symm_apply _

@[simp] theorem amalgamEnum_posRight (j : Fin Sb.card) :
    amalgamEnum h (posRight h j) = Merge.rightFun _ _ j :=
  (amalgamEnum h).apply_symm_apply _

/-- The cells of the amalgam visible through the first coatom are the cells of `Sa`. -/
theorem mem_range_posLeft_iff (d : Fin (amalgam h).card) :
    d ∈ Set.range (posLeft h) ↔ d ∈ (amalgam h).visibleCells (left m) := by
  rw [Scheme.visibleCells, mem_filter, amalgam_scope]
  simp only [mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    rw [amalgamEnum_posLeft, amalgamScope_inl]
    exact map_subset_map.mpr (subset_univ _)
  · intro hd
    obtain ⟨i, hi⟩ := exists_eq_inl_of_scope_subset h hd
    refine ⟨i, ?_⟩
    rw [posLeft, ← hi]
    exact (amalgamEnum h).symm_apply_apply d

/-- The cells of the amalgam visible through the second coatom are the cells of `Sb`. -/
theorem mem_range_posRight_iff (d : Fin (amalgam h).card) :
    d ∈ Set.range (posRight h) ↔ d ∈ (amalgam h).visibleCells (right m) := by
  rw [Scheme.visibleCells, mem_filter, amalgam_scope]
  simp only [mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    rw [amalgamEnum_posRight, amalgamScope_right]
    exact map_subset_map.mpr (subset_univ _)
  · intro hd
    obtain ⟨j, hj⟩ := mem_range_right_of_scope_subset h hd
    refine ⟨j, ?_⟩
    rw [posRight, hj]
    exact (amalgamEnum h).symm_apply_apply d

/-- The enumeration of the cells visible through the first coatom is `posLeft`. -/
theorem cellMap_left_eq {i : Fin Sa.card} {k : Fin ((amalgam h).comap (left m)).card}
    (hik : (i : ℕ) = k) : (amalgam h).cellMap (left m) k = posLeft h i :=
  ((amalgam h).cellMap_eq_of_strictMono (left m) (strictMono_posLeft h)
    (mem_range_posLeft_iff h) hik).symm

/-- The enumeration of the cells visible through the second coatom is `posRight`. -/
theorem cellMap_right_eq {j : Fin Sb.card} {k : Fin ((amalgam h).comap (right m)).card}
    (hjk : (j : ℕ) = k) : (amalgam h).cellMap (right m) k = posRight h j :=
  ((amalgam h).cellMap_eq_of_strictMono (right m) (strictMono_posRight h)
    (mem_range_posRight_iff h) hjk).symm

/-- **The restriction of the amalgam to the first coatom is `Sa`**, literally. -/
theorem comap_left_amalgam (hSa : Sa.IsWellFormed) (hSb : Sb.IsWellFormed) :
    (amalgam h).comap (left m) = Sa := by
  have hcard : ((amalgam h).comap (left m)).card = Sa.card :=
    (amalgam h).card_visibleCells_eq_of_strictMono (left m) (strictMono_posLeft h)
      (mem_range_posLeft_iff h)
  refine Scheme.ext hcard ?_ ?_ (fun k i hki ↦ ?_) (fun k i hki ↦ ?_) (fun s s' t t' hs ht ↦ ?_)
  · rw [Scheme.comap_ground, amalgam_ground, preimage_univ, hSa.ground_eq]
  · ext C
    rw [Scheme.mem_comap_faces, amalgam_faces, map_left_mem_amalgamFaces_iff h hSa hSb]
  · rw [Scheme.comap_scope, cellMap_left_eq h hki.symm, amalgam_scope, amalgamEnum_posLeft,
      amalgamScope_inl, preimage_map]
  · rw [Scheme.comap_grade, cellMap_left_eq h hki.symm, amalgam_grade, amalgamEnum_posLeft]
    rfl
  · rw [Scheme.comap_row]
    change (amalgamRows h).row (amalgamEnum h _) ⟨amalgamEnum h _, _⟩ = _
    have hs' : amalgamEnum h ((amalgam h).cellMap (left m) s) = .inl s' := by
      rw [cellMap_left_eq h hs.symm, amalgamEnum_posLeft]
    have ht' : amalgamEnum h ((amalgam h).cellMap (left m) t.1) = .inl t'.1 := by
      rw [cellMap_left_eq h ht.symm, amalgamEnum_posLeft]
    rw [CellScheme.Rows.row_congr (amalgamRows h) hs'
      (t' := ⟨.inl t'.1, (CellScheme.mem_below _).mpr
        (((isLowerEmbedding_left h).le_iff _ _).mpr t'.2)⟩) ht', amalgamRows_inl_inl]

/-- **The restriction of the amalgam to the second coatom is `Sb`**, literally. -/
theorem comap_right_amalgam (hSa : Sa.IsWellFormed) (hSb : Sb.IsWellFormed) :
    (amalgam h).comap (right m) = Sb := by
  have hcard : ((amalgam h).comap (right m)).card = Sb.card :=
    (amalgam h).card_visibleCells_eq_of_strictMono (right m) (strictMono_posRight h)
      (mem_range_posRight_iff h)
  refine Scheme.ext hcard ?_ ?_ (fun k j hkj ↦ ?_) (fun k j hkj ↦ ?_) (fun s s' t t' hs ht ↦ ?_)
  · rw [Scheme.comap_ground, amalgam_ground, preimage_univ, hSb.ground_eq]
  · ext C
    rw [Scheme.mem_comap_faces, amalgam_faces, map_right_mem_amalgamFaces_iff h hSa]
  · rw [Scheme.comap_scope, cellMap_right_eq h hkj.symm, amalgam_scope, amalgamEnum_posRight,
      amalgamScope_right, preimage_map]
  · rw [Scheme.comap_grade, cellMap_right_eq h hkj.symm, amalgam_grade, amalgamEnum_posRight,
      amalgamGrade_right]
  · rw [Scheme.comap_row]
    change (amalgamRows h).row (amalgamEnum h _) ⟨amalgamEnum h _, _⟩ = _
    have hs' : amalgamEnum h ((amalgam h).cellMap (right m) s) = Merge.rightFun _ _ s' := by
      rw [cellMap_right_eq h hs.symm, amalgamEnum_posRight]
    have ht' : amalgamEnum h ((amalgam h).cellMap (right m) t.1) = Merge.rightFun _ _ t'.1 := by
      rw [cellMap_right_eq h ht.symm, amalgamEnum_posRight]
    have hrow := congrArg (fun R ↦ R.row s' t') (comap_amalgamRows_right h)
    simp only [CellScheme.Rows.comap_row] at hrow
    rw [← hrow]
    exact CellScheme.Rows.row_congr _ hs' ht'

/-! ### The amalgam of two coatom stage types -/

section StageType

variable {α : Ordinal.{u}}

/-- Equal stage types have equal labels at corresponding cells. -/
theorem _root_.VaughtConjecture.StageType.label_eq_of_eq {n : ℕ} {t t' : StageType.{u} α n}
    (he : t = t') (i : Fin t.card) :
    t.label i = t'.label (Fin.cast (congrArg (fun t ↦ t.card) he) i) := by
  subst he
  rfl

variable {ta tb : StageType.{u} α (m + 1)} {p : StageType.{u} α m}
  (hta : StageType.restrictFace (face m) ta = some p)
  (htb : StageType.restrictFace (face m) tb = some p)

include hta htb in
/-- Two stage types with the same face along the common face have the same restricted scheme
there. -/
theorem comap_eq_of_restrictFace : ta.toScheme.comap (face m) = tb.toScheme.comap (face m) := by
  obtain ⟨hfa, hpa⟩ := (StageType.restrictFace_eq_some_iff ta (face m)).mp hta
  obtain ⟨hfb, hpb⟩ := (StageType.restrictFace_eq_some_iff tb (face m)).mp htb
  rw [← StageType.comap_toScheme ta (face m) hfa, hpa, ← hpb, StageType.comap_toScheme]

/-- The labels of the amalgam: the labels of `ta` and of `tb`. -/
def amalgamLabel : AmalgamCell (comap_eq_of_restrictFace hta htb) → Label.{u}
  | .inl i => ta.label i
  | .inr j _ => tb.label j

/-- Corresponding cells of the common face have the same label. -/
theorem label_overlap (t : Fin (ta.toScheme.comap (face m)).card) :
    ta.label (ta.cellMap (face m) t) = tb.label (overlap (comap_eq_of_restrictFace hta htb) t) := by
  obtain ⟨hfa, hpa⟩ := (StageType.restrictFace_eq_some_iff ta (face m)).mp hta
  obtain ⟨hfb, hpb⟩ := (StageType.restrictFace_eq_some_iff tb (face m)).mp htb
  exact StageType.label_eq_of_eq (hpa.trans hpb.symm) t

/-- The label of a cell of `tb` in the amalgam is its label in `tb`. -/
theorem amalgamLabel_rightFun (j : Fin tb.card) :
    amalgamLabel hta htb (Merge.rightFun _ _ j) = tb.label j := by
  by_cases hj : j ∈ Set.range (overlap (comap_eq_of_restrictFace hta htb))
  · obtain ⟨t, rfl⟩ := hj
    rw [Merge.rightFun_eb]
    exact label_overlap hta htb t
  · rw [Merge.rightFun_of_notMem _ _ hj]
    rfl

/-- The labels of the amalgam occur at stage `α`. -/
theorem atStage_amalgamLabel (x : AmalgamCell (comap_eq_of_restrictFace hta htb)) :
    AtStage α (amalgamLabel hta htb x) := by
  rcases x with i | ⟨j, hj⟩
  · exact ta.atStage i
  · exact tb.atStage j

include hta in
/-- The common face is closed in `ta`. -/
theorem univ_map_face_mem : univ.map (face m) ∈ ta.toCellScheme.faces :=
  ((StageType.restrictFace_eq_some_iff ta (face m)).mp hta).1

/-- **The labels of `ta` and `tb` glue to a lawful labelling of the amalgam**: every cell lies on
one of the two coatoms, where the labelling is that of `ta` or of `tb`. -/
theorem isLawful_amalgamLabel :
    (amalgamRows (comap_eq_of_restrictFace hta htb)).IsLawful (amalgamLabel hta htb) := by
  set hS := comap_eq_of_restrictFace hta htb
  have hD := isWellFormed_amalgamCellScheme hS ta.isWellFormed tb.isWellFormed
    (univ_map_face_mem hta)
  have hU : (amalgamRows hS).IsLawfulBelow
      (Prod.map (Finset.map (left m)) id ((univ : Finset (Fin (m + 1))), m + 1))
      (fun d ↦ amalgamLabel hta htb d) := by
    refine (CellScheme.Rows.isLawfulBelow_comap_iff (isLowerEmbedding_left hS)
      (image_left_below hS _)).mp ?_
    rw [comap_amalgamRows_left]
    exact ta.isLawful.isLawfulBelow _
  have hV : (amalgamRows hS).IsLawfulBelow
      (Prod.map (Finset.map (right m)) id ((univ : Finset (Fin (m + 1))), m + 1))
      (fun d ↦ amalgamLabel hta htb d) := by
    refine (CellScheme.Rows.isLawfulBelow_comap_iff (isLowerEmbedding_right hS)
      (image_right_below hS _)).mp ?_
    rw [comap_amalgamRows_right]
    convert tb.isLawful.isLawfulBelow ((univ : Finset (Fin (m + 1))), m + 1) using 1
    funext x
    exact amalgamLabel_rightFun hta htb x.1
  have hgrade (d : AmalgamCell hS) : (amalgamCellScheme hS).grade d ≤ m + 1 := by
    rcases d with i | ⟨j, hj⟩
    · exact (ta.isWellFormed.isWellFormed.grade_le_card i).trans
        ((card_le_univ _).trans (by simp))
    · exact (tb.isWellFormed.isWellFormed.grade_le_card j).trans
        ((card_le_univ _).trans (by simp))
  have hY : (amalgamRows hS).IsLawfulBelow ((univ : Finset (Fin (m + 2))), m + 2)
      (fun d ↦ amalgamLabel hta htb d) := by
    refine CellScheme.Rows.IsLawfulBelow.glue hU hV fun d _ ↦ ?_
    rcases d with i | ⟨j, hj⟩
    · exact Or.inl ⟨map_subset_map.mpr (subset_univ _), hgrade (.inl i)⟩
    · exact Or.inr ⟨map_subset_map.mpr (subset_univ _), hgrade (.inr j hj)⟩
  exact hY.isLawful fun d ↦ ⟨subset_univ _, (hgrade d).trans (Nat.le_succ _)⟩

/-- **The amalgam of two coatom stage types** [Kni26, Definition 4.3.1]: a stage type on `m + 2`
points whose faces along the two coatoms are `ta` and `tb`, labels included. -/
noncomputable def amalgamType : StageType.{u} α (m + 2) where
  toScheme := amalgam (comap_eq_of_restrictFace hta htb)
  label := amalgamLabel hta htb ∘ amalgamEnum (comap_eq_of_restrictFace hta htb)
  isWellFormed := isWellFormed_amalgam _ ta.isWellFormed tb.isWellFormed (univ_map_face_mem hta)
  isCoded := isCoded_amalgam _ ta.isCoded tb.isCoded
  isLawful :=
    (CellScheme.Rows.isLawful_comap_equiv_iff (CellScheme.IsLowerEmbedding.reindex _ _)).mpr
      (isLawful_amalgamLabel hta htb)
  atStage _ := atStage_amalgamLabel hta htb _

/-- The first coatom is a closed face of the amalgam. -/
theorem univ_map_left_mem_amalgamType :
    univ.map (left m) ∈ (amalgamType hta htb).toCellScheme.faces :=
  mem_insert_of_mem (mem_union_left _ (mem_map_of_mem _ ta.univ_mem_faces))

/-- The second coatom is a closed face of the amalgam. -/
theorem univ_map_right_mem_amalgamType :
    univ.map (right m) ∈ (amalgamType hta htb).toCellScheme.faces :=
  mem_insert_of_mem (mem_union_right _ (mem_map_of_mem _ tb.univ_mem_faces))

/-- **The face of the amalgam along `Fin.castSuccEmb` is `ta`**, literally, labels included. -/
theorem restrictFace_left_amalgamType :
    StageType.restrictFace Fin.castSuccEmb (amalgamType hta htb) = some ta := by
  rw [StageType.restrictFace_of_mem _ _ (univ_map_left_mem_amalgamType hta htb)]
  refine congrArg some (StageType.ext (comap_left_amalgam _ ta.isWellFormed tb.isWellFormed)
    fun k i hki ↦ ?_)
  rw [StageType.comap_label]
  change amalgamLabel hta htb (amalgamEnum _ ((amalgam _).cellMap (left m) k)) = _
  rw [cellMap_left_eq _ hki.symm, amalgamEnum_posLeft]
  rfl

/-- **The face of the amalgam along `extendByLast Fin.castSuccEmb` is `tb`**, literally, labels
included. -/
theorem restrictFace_right_amalgamType :
    StageType.restrictFace (extendByLast Fin.castSuccEmb) (amalgamType hta htb) = some tb := by
  rw [StageType.restrictFace_of_mem _ _ (univ_map_right_mem_amalgamType hta htb)]
  refine congrArg some (StageType.ext (comap_right_amalgam _ ta.isWellFormed tb.isWellFormed)
    fun k j hkj ↦ ?_)
  rw [StageType.comap_label]
  change amalgamLabel hta htb (amalgamEnum _ ((amalgam _).cellMap (right m) k)) = _
  rw [cellMap_right_eq _ hkj.symm, amalgamEnum_posRight]
  exact amalgamLabel_rightFun hta htb j

/-- The rows of the amalgam of two legal stage types are consistent. -/
theorem isConsistent_amalgamType (hla : ta.IsLegal) (hlb : tb.IsLegal) :
    (amalgamType hta htb).rows.IsConsistent :=
  isConsistent_amalgam _ hla.isConsistent hlb.isConsistent

/-- **The rows of the amalgam of two legal stage types are bountiful** [Kni26, Lemma 4.3.2]. -/
theorem isBountiful_amalgamType (hla : ta.IsLegal) (hlb : tb.IsLegal) :
    (amalgamType hta htb).rows.IsBountiful :=
  isBountiful_amalgam _ ta.isWellFormed tb.isWellFormed (univ_map_face_mem hta)
    hla.isBountiful hlb.isBountiful

/-- Every graded face of the amalgam of two legal stage types other than those of full scope is
the graded index of a cell. -/
theorem exists_gradedIndex_eq_amalgamType (hla : ta.IsLegal) (hlb : tb.IsLegal)
    {X : Finset (Fin (m + 2)) × ℕ} (hX : X ∈ (amalgamType hta htb).toCellScheme.gradedFaces)
    (hne : X.1 ≠ univ) : ∃ d, (amalgamType hta htb).toCellScheme.gradedIndex d = X :=
  exists_gradedIndex_eq_amalgam' _ hla.isComplete hlb.isComplete hX hne

/-- No cell of the amalgam has the full scope; in particular the amalgam is not complete, and
hence not legal. -/
theorem scope_ne_univ_amalgamType (d : Fin (amalgamType hta htb).card) :
    (amalgamType hta htb).toCellScheme.scope d ≠ univ :=
  amalgam_scope_ne_univ _ d

/-- The amalgam is not complete: the graded face `(univ, 1)` is the graded index of no cell. -/
theorem not_isComplete_amalgamType :
    ¬ (amalgamType hta htb).toCellScheme.IsComplete := fun hc ↦ by
  obtain ⟨d, hd⟩ := hc ((univ : Finset (Fin (m + 2))), 1)
    ⟨(amalgamType hta htb).univ_mem_faces, Nat.one_pos, by simp⟩
  exact scope_ne_univ_amalgamType hta htb d (congrArg Prod.fst hd)

end StageType

end VaughtConjecture.Coatom
