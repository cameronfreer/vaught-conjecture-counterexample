/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.GrowthRelabel
import VaughtConjecture.Continuation.GrowthRecognition

/-!
# Requests and recognition under relabelling

Roadmap, Layer 3 ((R3) and (R4), the growth carrier at a calibrated context).

For a permutation `σ` of the points of a context `t'`, the cell map of `σ` is a bijection from the
cells of `t'.reindex σ` onto the cells of `t'`, keeping labels, grades, scopes up to `σ` and rows
(`StageType.rowAt_reindex`, `StageType.mem_below_reindex_iff`); its inverse is
`StageType.reindexCell`.  Requests at `t'` (`StageType.GrowthRequests`) are carried to requests at
`t'.reindex σ` by moving the cap, the marker and the references along it
(`StageType.GrowthRequests.reindex`); the donor side is untouched.

* `StageType.GrowthRequests.threshold_reindex`: the threshold is kept.
* `StageType.GrowthRequests.correctAt_reindex_iff`: **the relation of the requests is invariant**:
  it holds at the relabelled requests for a section read along the cell map exactly when it holds
  at the original requests for the section.
* `StageType.GrowthRequests.admitsOnClass_reindex_iff`: **admission on the exact class is
  invariant**, the exact class of `t'.reindex σ` below the relabelled cap being that of `t'` below
  the cap.
* `GrowthCarrier.Recognizes.relabel`: **recognition is transported**: if a carrier for the
  relabelled context recognizes the relabelled requests, the relabelled carrier
  (`GrowthCarrier.relabel`) recognizes the original requests.

## References

Reindexing of stage types is [Kni26, Definition 3.1.2]; the growth construction is that of
[Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- The **cell of the relabelled type** over a cell of `t'`: the inverse of the cell map of a
permutation `σ` of the points, which is a bijection of the cells. -/
noncomputable def reindexCell (t' : StageType.{u} α k) (σ : Equiv.Perm (Fin k)) :
    Fin t'.card ≃ Fin (t'.reindex σ).card :=
  (Equiv.ofBijective (t'.toScheme.cellMap σ.toEmbedding)
    ⟨(t'.toScheme.cellMap σ.toEmbedding).injective, t'.toScheme.surjective_cellMap_equiv σ⟩).symm

variable (t' : StageType.{u} α k) (σ : Equiv.Perm (Fin k))

@[simp] theorem cellMap_reindexCell (x : Fin t'.card) :
    t'.toScheme.cellMap σ.toEmbedding (t'.reindexCell σ x) = x :=
  Equiv.apply_symm_apply (Equiv.ofBijective (t'.toScheme.cellMap σ.toEmbedding)
    ⟨(t'.toScheme.cellMap σ.toEmbedding).injective, t'.toScheme.surjective_cellMap_equiv σ⟩) x

@[simp] theorem reindexCell_cellMap (y : Fin (t'.reindex σ).card) :
    t'.reindexCell σ (t'.toScheme.cellMap σ.toEmbedding y) = y :=
  Equiv.symm_apply_apply (Equiv.ofBijective (t'.toScheme.cellMap σ.toEmbedding)
    ⟨(t'.toScheme.cellMap σ.toEmbedding).injective, t'.toScheme.surjective_cellMap_equiv σ⟩) y

/-- The cells below a relabelled cell are the relabelled cells below it. -/
theorem reindexCell_mem_below_iff (x c : Fin t'.card) :
    t'.reindexCell σ x ∈ (t'.reindex σ).toCellScheme.below
        ((t'.reindex σ).toCellScheme.gradedIndex (t'.reindexCell σ c)) ↔
      x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex c) := by
  rw [mem_below_reindex_iff, cellMap_reindexCell, cellMap_reindexCell]

/-- The grade of a relabelled cell is its grade. -/
@[simp] theorem grade_reindexCell (x : Fin t'.card) :
    (t'.reindex σ).toCellScheme.grade (t'.reindexCell σ x) = t'.toCellScheme.grade x := by
  conv_rhs => rw [← cellMap_reindexCell t' σ x]
  rfl

/-- The label of a relabelled cell is its label. -/
@[simp] theorem label_reindexCell (x : Fin t'.card) :
    (t'.reindex σ).label (t'.reindexCell σ x) = t'.label x := by
  rw [reindex_label, cellMap_reindexCell]

namespace GrowthRequests

variable {t'} {D : Scheme.{u} (n + 1)} (Q : GrowthRequests t' D)

/-- **The relabelled requests** at `t'.reindex σ`: the cap, the marker and the references moved
along the inverse of the cell map of `σ`; the offsets and the donor cells unchanged. -/
noncomputable def reindex : GrowthRequests (t'.reindex σ) D where
  cap := t'.reindexCell σ Q.cap
  marker := t'.reindexCell σ Q.marker
  markerOffset := Q.markerOffset
  bottoms := Q.bottoms
  exacts := Q.exacts
  highs := Q.highs
  ref j := t'.reindexCell σ (Q.ref j)
  offset := Q.offset

/-- The threshold of the relabelled requests is the threshold. -/
@[simp] theorem threshold_reindex : (Q.reindex σ).threshold = Q.threshold :=
  grade_reindexCell t' σ Q.cap

/-- **The relation of the requests is invariant under relabelling**: it holds at the relabelled
requests for a section read along the cell map of `σ` exactly when it holds at the requests for
the section. -/
theorem correctAt_reindex_iff (s : Fin t'.card → Label.{u}) (j : Fin D.card) (ℓ : Label.{u}) :
    (Q.reindex σ).CorrectAt (fun y ↦ s (t'.toScheme.cellMap σ.toEmbedding y)) j ℓ ↔
      Q.CorrectAt s j ℓ := by
  unfold CorrectAt readExact readMarker
  rw [threshold_reindex]
  simp only [reindex, cellMap_reindexCell]

/-- **Admission on the exact class is invariant under relabelling**: the cells of `t'.reindex σ`
below the relabelled cap are the relabelled cells below the cap, with their labels. -/
theorem admitsOnClass_reindex_iff (s : Fin t'.card → Label.{u}) (w : Fin D.card → Label.{u}) :
    (Q.reindex σ).AdmitsOnClass (fun y ↦ s (t'.toScheme.cellMap σ.toEmbedding y)) w ↔
      Q.AdmitsOnClass s w := by
  have hcls : (∀ y ∈ (t'.reindex σ).toCellScheme.below
        ((t'.reindex σ).toCellScheme.gradedIndex (Q.reindex σ).cap),
        s (t'.toScheme.cellMap σ.toEmbedding y) = ⊥ ↔ (t'.reindex σ).label y = ⊥) ↔
      ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
        s x = ⊥ ↔ t'.label x = ⊥ := by
    constructor
    · intro h x hx
      have := h (t'.reindexCell σ x) ((reindexCell_mem_below_iff t' σ x Q.cap).mpr hx)
      rwa [cellMap_reindexCell, label_reindexCell] at this
    · intro h y hy
      rw [← reindexCell_cellMap t' σ y] at hy
      have := h _ ((reindexCell_mem_below_iff t' σ _ Q.cap).mp hy)
      rwa [reindex_label]
  unfold AdmitsOnClass
  rw [hcls]
  simp only [correctAt_reindex_iff]
  change ((∀ x ∈ _, _) → s (t'.toScheme.cellMap σ.toEmbedding (t'.reindexCell σ Q.cap)) ≠ ⊥ →
    _) ↔ _
  rw [cellMap_reindexCell]

end GrowthRequests

end StageType

namespace GrowthCarrier

open StageType

variable {α : Ordinal.{u}} {J n : ℕ} {P : Scheme.{u} (n + 1)} {t' : StageType.{u} α J}
  (σ : Equiv.Perm (Fin J)) {e'' : Fin n ↪ Fin J} (G : GrowthCarrier (t'.reindex σ).toScheme P e'')

/-- The context cell of the relabelled carrier at a cell `x` of `t'` lies over the context cell
of the carrier at the relabelled cell. -/
theorem relabel_contextCell' (x : Fin t'.card) :
    G.scheme.cellMap (extendPerm σ).symm.toEmbedding
        ((G.relabel (C := t'.toScheme) σ).contextCell x) =
      G.contextCell (t'.reindexCell σ x) := by
  have h := relabel_contextCell (C := t'.toScheme) σ G (t'.reindexCell σ x)
  rw [cellMap_reindexCell] at h
  exact h

/-- **Recognition is transported along a relabelling**: if a carrier for `t'.reindex σ` recognizes
the relabelled requests, the relabelled carrier recognizes the requests.  A lawful section of the
relabelled carrier is read back to the carrier (`GrowthCarrier.exists_isLawful_relabel`); the
recognized state is moved back along the cell map, with the same donor labelling, map and capping;
admission on the exact class and the threshold are invariant
(`StageType.GrowthRequests.admitsOnClass_reindex_iff`,
`StageType.GrowthRequests.threshold_reindex`). -/
theorem Recognizes.relabel {Q : GrowthRequests t' P} (h : G.Recognizes (Q.reindex σ)) :
    (G.relabel (C := t'.toScheme) σ).Recognizes Q := by
  intro v hv
  obtain ⟨w, hw, hwv⟩ := G.exists_isLawful_relabel (C := t'.toScheme) σ hv
  obtain ⟨s, w', θ, H, hadm, hθm, hθb, hθv, hHv, hHc, hrefl, hs, hw'⟩ := h w hw
  have hctx (x : Fin t'.card) : w (G.contextCell (t'.reindexCell σ x)) =
      v ((G.relabel (C := t'.toScheme) σ).contextCell x) := by
    rw [← relabel_contextCell']
    exact hwv _
  have hmem (x : Fin t'.card) (hx : x ∈ t'.toCellScheme.below
      (t'.toCellScheme.gradedIndex Q.cap)) :
      t'.reindexCell σ x ∈ (t'.reindex σ).toCellScheme.below
        ((t'.reindex σ).toCellScheme.gradedIndex (Q.reindex σ).cap) :=
    (reindexCell_mem_below_iff t' σ x Q.cap).mpr hx
  rw [GrowthRequests.threshold_reindex] at hθv hHv
  refine ⟨fun x ↦ s (t'.reindexCell σ x), w', θ, H, ?_, hθm, hθb, hθv, hHv, ?_,
    fun x hx ↦ hrefl _ (hmem x hx), fun x hx ↦ (hs _ (hmem x hx)).trans (by rw [hctx]),
    fun j ↦ (hw' j).trans ?_⟩
  · refine (GrowthRequests.admitsOnClass_reindex_iff σ Q _ w').mp ?_
    simpa only [reindexCell_cellMap] using hadm
  · rw [← hctx]
    exact hHc
  · exact congrArg (min · H)
      ((congrArg w (relabel_donorCell (C := t'.toScheme) σ G j)).symm.trans (hwv _))

end GrowthCarrier

end VaughtConjecture
