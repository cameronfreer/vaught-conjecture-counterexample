/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.GrowthRelabelRequests

/-!
# Recognizing growth carriers from the seed position

Roadmap, Layer 3 ((R3), the growth carrier at a calibrated context).

The inputs of `StageType.HasRecognizingGrowthCarriers` at a context `t'` along a root `e` (requests
`Q` read exactly at the labels of `t'`, calibrated, with the relative lift on the exact class) are
carried along a permutation `σ` of the points to the inputs at `t'.reindex σ` along the relabelled
root, for the relabelled requests (`StageType.GrowthRequests.reindex`):

* `StageType.GrowthRequests.Calibrated.reindex`: calibration is kept; the cells of the root
  correspond (`StageType.cellMap_faceCell_reindex`), and so do the cleaned cap rows
  (`StageType.GrowthRequests.cleanedCapRow_reindex`).
* `StageType.GrowthRequests.allowedOnClass_reindex_iff` and
  `StageType.GrowthRequests.HasRelativeLiftOnClass.reindex`: allowed pairs and the relative lift
  on the exact class are kept, the context sections read along the cell map.
* `StageType.GrowthRequests.topGrade_le_of_exact`: **the top-grade clause of the seed position is
  automatic**: if the requests are read exactly at the labels of `t'` and some donor cell is
  labelled `⊤`, the cap is labelled `⊤` (at a cap label `o < ⊤` the labels `⊤` and `o` would read
  alike), so the donor's top grade, at most `n + 1`, is at most the threshold, hence at most the
  context's top grade.

Hence **recognizing growth carriers at the seed position give them everywhere**
(`StageType.HasRecognizingGrowthCarriersAtSeed.hasRecognizingGrowthCarriers`), and so do ladder
growth carriers at the seed position
(`StageType.HasLadderGrowthCarriersAtSeed.hasRecognizingGrowthCarriers`): the root is not onto
(`StageType.GrowthRequests.Calibrated.not_surjective`), lies in the first coatom after a relabelling
(`Realization.exists_perm_root_eq`), and the recognizing carrier there is relabelled back with its
recognition (`GrowthCarrier.Recognizes.relabel`).  These are implications; the recognizing carriers
also follow from `StageType.hasLadderGrowthCarriersStableAtSeed_levels` (not yet reviewed).

## References

Reindexing of stage types is [Kni26, Definition 3.1.2]; the growth construction is that of
[Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ} (t' : StageType.{u} α k) (σ : Equiv.Perm (Fin k))

/-- **The root cells correspond**: the cell of `t'` under a root cell of `t'.reindex σ` along
`e''` is the root cell of `t'` along `e''.trans σ` at the same position. -/
theorem cellMap_faceCell_reindex {e'' : Fin n ↪ Fin k} {p : StageType.{u} α n}
    (hte'' : restrictFace e'' (t'.reindex σ) = some p)
    (hte : restrictFace (e''.trans σ.toEmbedding) t' = some p) (i : Fin p.card) :
    t'.toScheme.cellMap σ.toEmbedding ((t'.reindex σ).faceCell hte'' i) = t'.faceCell hte i :=
  t'.toScheme.cellMap_faceCell_comap σ.toEmbedding e'' _ i

namespace GrowthRequests

variable {t'} {d : StageType.{u} α (n + 1)} (Q : GrowthRequests t' d.toScheme)

/-- The cleaned cap row of the relabelled requests is the cleaned cap row along the cell map. -/
theorem cleanedCapRow_reindex (y : Fin (t'.reindex σ).card) :
    (Q.reindex σ).cleanedCapRow y = Q.cleanedCapRow (t'.toScheme.cellMap σ.toEmbedding y) := by
  unfold cleanedCapRow
  rw [reindex_label, rowAt_reindex]
  change (if _ then ⊥ else t'.rowAt (t'.toScheme.cellMap σ.toEmbedding
    (t'.reindexCell σ Q.cap)) _) = _
  rw [cellMap_reindexCell]

variable {e'' : Fin n ↪ Fin k} {p : StageType.{u} α n}
  (hte'' : restrictFace e'' (t'.reindex σ) = some p)
  (hte : restrictFace (e''.trans σ.toEmbedding) t' = some p)

/-- **Calibration is kept under relabelling.** -/
theorem Calibrated.reindex {Q : GrowthRequests t' d.toScheme} (hQ : Q.Calibrated hte) :
    (Q.reindex σ).Calibrated hte'' where
  cover := hQ.cover
  scope_cap := by
    change (t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding
      (t'.reindexCell σ Q.cap))).preimage σ.toEmbedding σ.toEmbedding.injective.injOn = univ
    rw [cellMap_reindexCell, hQ.scope_cap]
    exact preimage_univ _
  label_cap := by
    change (t'.reindex σ).label (t'.reindexCell σ Q.cap) ≠ ⊥
    rw [label_reindexCell]
    exact hQ.label_cap
  ref j hj := by
    obtain ⟨h1, h2, h3⟩ := hQ.ref j hj
    refine ⟨?_, ?_, ?_⟩
    · change (t'.reindex σ).toCellScheme.grade (t'.reindexCell σ (Q.ref j)) ≤ _
      rw [grade_reindexCell, threshold_reindex]
      exact h1
    · rw [threshold_reindex]
      exact h2
    · change (t'.reindex σ).label (t'.reindexCell σ (Q.ref j)) ≠ ⊥
      rw [label_reindexCell]
      exact h3
  marker := by
    obtain ⟨h1, h2, h3⟩ := hQ.marker
    refine ⟨?_, ?_, ?_⟩
    · change (t'.reindex σ).toCellScheme.grade (t'.reindexCell σ Q.marker) ≤ _
      rw [grade_reindexCell, threshold_reindex]
      exact h1
    · rw [threshold_reindex]
      exact h2
    · change (t'.reindex σ).label (t'.reindexCell σ Q.marker) ≠ ⊥
      rw [label_reindexCell]
      exact h3
  root i := by
    obtain ⟨h1, h2⟩ := hQ.root i
    have hc := cellMap_faceCell_reindex t' σ hte'' hte i
    refine ⟨?_, ?_⟩
    · change t'.toCellScheme.grade (t'.toScheme.cellMap σ.toEmbedding _) ≤ _
      rw [hc, threshold_reindex]
      exact h1
    · rw [cleanedCapRow_reindex, hc, h2, rowAt_reindex, hc]
      change _ = t'.rowAt (t'.toScheme.cellMap σ.toEmbedding (t'.reindexCell σ Q.cap)) _
      rw [cellMap_reindexCell]
  arity := by
    rw [threshold_reindex]
    exact hQ.arity

variable (hdp : restrictFace Fin.castSuccEmb d = some p)

/-- **Allowed pairs on the exact class are kept under relabelling**, the context section read
along the cell map of `σ`. -/
theorem allowedOnClass_reindex_iff (U : Fin t'.card → Label.{u}) (v : Fin d.card → Label.{u}) :
    (Q.reindex σ).AllowedOnClass hte'' hdp (fun y ↦ U (t'.toScheme.cellMap σ.toEmbedding y)) v ↔
      Q.AllowedOnClass hte hdp U v := by
  refine and_congr (Scheme.isLawful_comap_perm_iff t'.toScheme σ U)
    (and_congr Iff.rfl (and_congr (forall_congr' fun i ↦ ?_) (admitsOnClass_reindex_iff σ Q U v)))
  change v _ = U (t'.toScheme.cellMap σ.toEmbedding _) ↔ _
  rw [cellMap_faceCell_reindex t' σ hte'' hte]

/-- **The relative lift on the exact class is kept under relabelling.** -/
theorem HasRelativeLiftOnClass.reindex {Q : GrowthRequests t' d.toScheme}
    (h : Q.HasRelativeLiftOnClass hte hdp) : (Q.reindex σ).HasRelativeLiftOnClass hte'' hdp := by
  intro u u' v γ hall hu' hγ hag
  set U : Fin t'.card → Label.{u} := fun x ↦ u (t'.reindexCell σ x)
  set U' : Fin t'.card → Label.{u} := fun x ↦ u' (t'.reindexCell σ x)
  have hU : (fun y ↦ U (t'.toScheme.cellMap σ.toEmbedding y)) = u :=
    funext fun y ↦ congrArg u (reindexCell_cellMap t' σ y)
  have hU' : (fun y ↦ U' (t'.toScheme.cellMap σ.toEmbedding y)) = u' :=
    funext fun y ↦ congrArg u' (reindexCell_cellMap t' σ y)
  rw [← hU] at hall
  rw [← hU'] at hu'
  change (t'.toScheme.comap σ.toEmbedding).rows.IsLawful _ at hu'
  rw [Scheme.isLawful_comap_perm_iff] at hu'
  rw [threshold_reindex] at hγ
  obtain ⟨v', hall', hv'⟩ := h U U' v γ ((allowedOnClass_reindex_iff σ Q hte'' hte hdp U v).mp hall)
    hu' hγ (fun x ↦ hag _)
  refine ⟨v', ?_, hv'⟩
  rw [← hU']
  exact (allowedOnClass_reindex_iff σ Q hte'' hte hdp U' v').mpr hall'

end GrowthRequests

/-- **The top-grade clause is automatic for exact calibrated requests**: if the requests are read
exactly at the labels of `t'`, a donor cell labelled `⊤` forces the cap to be labelled `⊤` (at a cap
label `o` the reads of `⊤` and of `o` agree, both capped at `o`), so the donor's top grade, at most
`n + 1`, is at most the threshold, the grade of a cell of `t'` labelled `⊤`. -/
theorem GrowthRequests.topGrade_le_of_exact {t' : StageType.{u} α k} {e : Fin n ↪ Fin k}
    {p : StageType.{u} α n} {hte : restrictFace e t' = some p} {d : StageType.{u} α (n + 1)}
    {Q : GrowthRequests t' d.toScheme} (hex : ∀ j ℓ, Q.CorrectAt t'.label j ℓ ↔ ℓ = d.label j)
    (hQ : Q.Calibrated hte) : d.topGrade ≤ t'.topGrade := by
  refine topGrade_le_iff.mpr fun j hj ↦ ?_
  have hcap : t'.label Q.cap = ⊤ := by
    by_contra hc
    have h1 : Q.CorrectAt t'.label j ⊤ := (hex j ⊤).mpr hj.symm
    have hm : min (t'.label Q.cap) (t'.label Q.cap) = min ⊤ (t'.label Q.cap) := by
      rw [min_self, min_eq_right le_top]
    have h2 : Q.CorrectAt t'.label j (t'.label Q.cap) := by
      unfold GrowthRequests.CorrectAt at h1 ⊢
      rw [hm]
      exact h1
    exact hc (((hex j _).mp h2).trans hj)
  have h1 := grade_le_topGrade hcap
  have h2 := d.grade_le j
  have h3 := hQ.arity
  unfold GrowthRequests.threshold at h3
  omega

end StageType

end VaughtConjecture
