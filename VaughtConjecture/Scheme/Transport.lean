/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Scheme.Bountiful

/-!
# Transport of bountifulness

Roadmap, Layer 1 (bountifulness; restriction, transport, and pullback); semantic contract, item 3
(capping is not stage reduction, and capped vectors need not be lawful: bountifulness is
transported cap by cap, through lawful labellings, never by transporting a capped observation as
a lawful labelling); the expositions, §2.

Bountifulness (`CellScheme.Rows.IsBountiful`) passes to the rows pulled back along a lower
embedding `φ` of `E` into `D`, provided the graded faces of `E` are sent to graded faces of `D` by
a map of faces `g`, monotone on the faces of `E` (grades unchanged), under which `φ` maps the
cells below each graded face `X` of `E` onto the cells below its image
(`IsBountiful.comap_of_image_eq`).  The cells below `X` and below its image are then identified
by an equivalence (`IsLowerEmbedding.belowEquiv`) that is a lower embedding of the schemes of
cells below them in both directions, so lawfulness below `X` is lawfulness below the image
(`Rows.isLawfulBelow_comap_iff`) and cap balls correspond.

Instances:

* the pullback along an embedding `f : β ↪ α` of ground sets (`IsBountiful.comap`), with the
  faces `(C, j) ↦ (f '' C, j)` (`Prod.map (Finset.map f) id`): the graded faces of `D.comap f` are
  those whose image is a graded face of `D` (`mem_gradedFaces_comap`), and the cells below a pair
  in the pullback are the cells below its image (`image_val_below_comap`).  No well-formedness of
  the pullback is needed;
* reindexing along an equivalence of cells (`IsBountiful.reindex`).

Along the way, the inverse of an equivalence of cells that is a lower embedding is a lower
embedding (`IsLowerEmbedding.symm`), and lawful sections transport along such an equivalence in
both directions (`Rows.isLawful_comap_equiv_iff`).

## Placement

`gradedIndex_comap_le_iff`, `mem_gradedFaces_comap`, and `image_val_below_comap` belong in the
`Comap` section of `VaughtConjecture.Scheme.Cell`; `IsLowerEmbedding.symm`,
`IsLowerEmbedding.belowEquiv`, `IsLowerEmbedding.coe_belowEquiv`, and
`IsLowerEmbedding.isLowerEmbedding_belowEquiv` in the `IsLowerEmbedding` namespace of
`VaughtConjecture.Scheme.Cell`; `Rows.comap_comap_symm`, `Rows.isLawful_comap_equiv_iff`, and
`Rows.isLawfulBelow_comap_iff` in `VaughtConjecture.Scheme.Row`, beside the reindexing lemmas;
and `IsBountiful.comap_of_image_eq`, `IsBountiful.comap`, and `IsBountiful.reindex` in
`VaughtConjecture.Scheme.Bountiful`.  They are stated here so that those files are unchanged.
Once moved, the following become one-line consequences, to be derived from them or removed:
`Scheme.mem_gradedFaces_comap` (`CellScheme.mem_gradedFaces_comap S.toCellScheme f`, a fact also
re-derived inline in `CellScheme.IsComplete.comap`); `Rows.comap_reindex_comap_symm`
(`comap_comap_symm (IsLowerEmbedding.reindex D e)`); `Rows.isLawful_comap_reindex_iff`
(`isLawful_comap_equiv_iff (IsLowerEmbedding.reindex D e)`); `IsBountiful.restrict`
(`IsBountiful.comap_of_image_eq` with the identity map of faces); and
`IsLowerEmbedding.reindex_symm D e` (`(IsLowerEmbedding.reindex D e).symm`).

## References

Bountifulness is [Kni26, Definition 2.5.14]; the restriction of a semantics to a face of the plan
is [Kni26, Lemma 2.5.5], and its transport along a one-to-one map is clause 5 of
[Kni26, Proposition 2.6.3], for R. W. Knight, *A counterexample to Vaught's Conjecture using
generalised Stone spaces* (draft, 20 February 2026).
-/

universe u

namespace VaughtConjecture.CellScheme

open Finset

variable {ι κ α β : Type*} {D : CellScheme ι α} {E : CellScheme κ β} {φ : κ → ι}

/-! ### Cells below a pair in a pullback -/

section Comap

variable (D) (f : β ↪ α)

/-- A cell of the pullback lies below a pair exactly when its original cell lies below the image
of the pair. -/
theorem gradedIndex_comap_le_iff (d : D.visible (Set.range f)) {X : Finset β × ℕ} :
    (D.comap f).gradedIndex d ≤ X ↔ D.gradedIndex d ≤ Prod.map (Finset.map f) id X := by
  rw [gradedIndex_le_iff, gradedIndex_le_iff, ← map_subset_map (f := f), map_comap_scope,
    comap_grade, Prod.map_fst, Prod.map_snd, id_eq]

/-- The graded faces of the pullback are the pairs whose image is a graded face. -/
theorem mem_gradedFaces_comap {X : Finset β × ℕ} :
    X ∈ (D.comap f).gradedFaces ↔ Prod.map (Finset.map f) id X ∈ D.gradedFaces := by
  simp

/-- The cells below a pair in the pullback are the cells below the image of the pair. -/
theorem image_val_below_comap (X : Finset β × ℕ) :
    ((↑) : D.visible (Set.range f) → ι) '' (D.comap f).below X =
      D.below (Prod.map (Finset.map f) id X) := by
  ext d
  refine ⟨?_, fun hd ↦ ⟨⟨d, ?_⟩, (gradedIndex_comap_le_iff D f _).mpr hd, rfl⟩⟩
  · rintro ⟨d, hd, rfl⟩
    exact (gradedIndex_comap_le_iff D f d).mp hd
  · exact (coe_subset.mpr hd.1).trans (by simp)

end Comap

/-! ### Equivalences of lower sets -/

namespace IsLowerEmbedding

/-- The inverse of an equivalence of cells that is a lower embedding is a lower embedding. -/
theorem symm {e : κ ≃ ι} (h : E.IsLowerEmbedding D e) : D.IsLowerEmbedding E e.symm where
  injective := e.symm.injective
  grade_eq d := by rw [← h.grade_eq, e.apply_symm_apply]
  le_iff s t := by rw [← h.le_iff, e.apply_symm_apply, e.apply_symm_apply]
  mem_range _ d _ := e.symm.surjective d

variable {X : Finset β × ℕ} {Y : Finset α × ℕ}

/-- For a lower embedding `φ` mapping the cells below `X` onto the cells below `Y`, the induced
equivalence of these lower sets. -/
noncomputable def belowEquiv (hφ : E.IsLowerEmbedding D φ) (h : φ '' E.below X = D.below Y) :
    E.below X ≃ D.below Y :=
  Set.BijOn.equiv φ ⟨(Set.image_eq_iff_surjOn_mapsTo.mp h).2, hφ.injective.injOn,
    (Set.image_eq_iff_surjOn_mapsTo.mp h).1⟩

/-- The cell underlying the image of a cell under `belowEquiv` is its image under `φ`. -/
@[simp] theorem coe_belowEquiv (hφ : E.IsLowerEmbedding D φ) (h : φ '' E.below X = D.below Y)
    (t : E.below X) : (hφ.belowEquiv h t : ι) = φ t := rfl

/-- The equivalence of lower sets induced by a lower embedding is a lower embedding of the
schemes of cells below them. -/
theorem isLowerEmbedding_belowEquiv (hφ : E.IsLowerEmbedding D φ)
    (h : φ '' E.below X = D.below Y) :
    (E.reindex ((↑) : E.below X → κ)).IsLowerEmbedding (D.reindex ((↑) : D.below Y → ι))
      (hφ.belowEquiv h) :=
  ⟨(hφ.belowEquiv h).injective, fun t ↦ hφ.grade_eq t, fun s t ↦ hφ.le_iff s t,
    fun _ d _ ↦ (hφ.belowEquiv h).surjective d⟩

end IsLowerEmbedding

namespace Rows

variable (R : D.Rows.{u})

/-! ### Lawful sections along equivalences -/

/-- Rows pulled back along an equivalence of cells that is a lower embedding and then back along
its inverse are the original rows. -/
theorem comap_comap_symm {e : κ ≃ ι} (h : E.IsLowerEmbedding D e) :
    (R.comap h).comap h.symm = R := by
  ext s t
  exact R.row_congr (e.apply_symm_apply s) (e.apply_symm_apply t)

variable {R}

/-- **Transport along an equivalence of cells** that is a lower embedding: `p ∘ e` is lawful for
the pulled-back rows exactly when `p` is lawful. -/
theorem isLawful_comap_equiv_iff {e : κ ≃ ι} (h : E.IsLowerEmbedding D e) {p : ι → Label.{u}} :
    (R.comap h).IsLawful (p ∘ e) ↔ R.IsLawful p := by
  refine ⟨fun hp ↦ ?_, fun hp ↦ hp.comap h⟩
  have h' := hp.comap h.symm
  rwa [comap_comap_symm, Function.comp_assoc, e.self_comp_symm, Function.comp_id] at h'

/-- For a lower embedding `φ` mapping the cells below `X` onto the cells below `Y`, a labelling of
the cells below `Y` is lawful below `Y` exactly when its transport along `belowEquiv` is lawful
below `X` for the pulled-back rows. -/
theorem isLawfulBelow_comap_iff (hφ : E.IsLowerEmbedding D φ) {X : Finset β × ℕ}
    {Y : Finset α × ℕ} (h : φ '' E.below X = D.below Y) {r : D.below Y → Label.{u}} :
    (R.comap hφ).IsLawfulBelow X (r ∘ hφ.belowEquiv h) ↔ R.IsLawfulBelow Y r :=
  isLawful_comap_equiv_iff (R := R.comap (IsLowerEmbedding.subtypeVal_below D Y))
    (hφ.isLowerEmbedding_belowEquiv h)

/-! ### Transport of bountifulness -/

/-- **Transport of bountifulness.**  Let `φ` be a lower embedding of `E` into `D` and `g` a
map of faces, monotone on the faces of `E`, such that, for every graded face `X = (C, j)` of
`E`, the pair `(g C, j)` is a graded face of `D` and `φ` maps the cells below `X` onto the cells
below `(g C, j)`.  Then the pullback of bountiful rows along `φ` is bountiful. -/
theorem IsBountiful.comap_of_image_eq (hR : R.IsBountiful) (hφ : E.IsLowerEmbedding D φ)
    {g : Finset β → Finset α} (hg : MonotoneOn g E.faces)
    (hfaces : ∀ X ∈ E.gradedFaces, Prod.map g id X ∈ D.gradedFaces)
    (himage : ∀ X ∈ E.gradedFaces, φ '' E.below X = D.below (Prod.map g id X)) :
    (R.comap hφ).IsBountiful := by
  intro X Y hX hY hXY c hc q hq p ⟨hp, hpq⟩
  set eX := hφ.belowEquiv (himage X hX)
  set eY := hφ.belowEquiv (himage Y hY)
  have hle : Prod.map g id X ≤ Prod.map g id Y := ⟨hg hX.1 hY.1 hXY.1, hXY.2⟩
  have hinc (t : E.below X) :
      eY (Set.inclusion (E.below_mono hXY) t) = Set.inclusion (D.below_mono hle) (eX t) :=
    Subtype.ext (by simp [eX, eY])
  have hinc' (d : D.below (Prod.map g id X)) :
      eY.symm (Set.inclusion (D.below_mono hle) d) = Set.inclusion (E.below_mono hXY) (eX.symm d) :=
    eY.symm_apply_eq.mpr (by rw [hinc, eX.apply_symm_apply])
  have hq' : R.IsLawfulBelow _ (q ∘ eY.symm) :=
    (isLawfulBelow_comap_iff hφ (himage Y hY)).mp (by simpa [eY, Function.comp_assoc] using hq)
  have hp' : R.IsLawfulBelow _ (p ∘ eX.symm) :=
    (isLawfulBelow_comap_iff hφ (himage X hX)).mp (by simpa [eX, Function.comp_assoc] using hp)
  obtain ⟨q', ⟨hl, he⟩, hr⟩ := hR (hfaces X hX) (hfaces Y hY) hle c hc _ hq'
    ⟨hp', fun d ↦ by simpa [hinc'] using hpq (eX.symm d)⟩
  refine ⟨q' ∘ eY, ⟨(isLawfulBelow_comap_iff hφ (himage Y hY)).mpr hl,
    fun d ↦ by simpa using he (eY d)⟩, funext fun t ↦ ?_⟩
  simpa [hinc] using congrFun hr (eX t)

/-- **Pullback along an embedding of ground sets.**  The pullback of bountiful rows along the
inclusion of the cells visible through an embedding `f : β ↪ α` is bountiful. -/
theorem IsBountiful.comap (hR : R.IsBountiful) (f : β ↪ α) :
    (R.comap (IsLowerEmbedding.comap D f)).IsBountiful :=
  hR.comap_of_image_eq _ (fun _ _ _ _ h ↦ map_subset_map.mpr h)
    (fun _ hX ↦ (mem_gradedFaces_comap D f).mp hX) fun X _ ↦ image_val_below_comap D f X

/-- **Reindexing along an equivalence of cells.**  Bountifulness is preserved by reindexing the
cells along an equivalence. -/
theorem IsBountiful.reindex (hR : R.IsBountiful) (e : κ ≃ ι) :
    (R.comap (IsLowerEmbedding.reindex D e)).IsBountiful :=
  hR.comap_of_image_eq _ (monotone_id.monotoneOn _) (fun _ hX ↦ hX) fun X _ ↦
    e.image_preimage (D.below X)

end Rows

end VaughtConjecture.CellScheme
