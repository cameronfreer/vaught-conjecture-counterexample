/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.SourceGapMarkedCapRoute

/-!
# The receiving route with the lost point last

Roadmap, Layer 6 ("Status: the hypotheses of the main theorem"), for the receiving route
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_receivingModels'`); semantic contract,
items 5 and 8.

The (R2) hypothesis of the main theorem from three finite coatom statements
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap`)
is coatom cutoff determination (`Realization.CoatomCutoffDetermination`) for the source-gap context
(`StageType.IsSourceGapContext`).  Its coatom form puts the root in the first coatom, so it asks
determination also at contexts whose lost point lies on the first coatom.  This file asks it only
at the source-gap contexts whose lost point is the last point (`StageType.IsSourceGapContextLast`).
Each item is compiled in this repository (theorem named).

* **The reduction**
  (`Realization.FirstCoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff`, and for
  the coatom form
  `Realization.CoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff`):
  cutoff determination at the first coatom for `IsSourceGapContextLast` gives cutoff determination
  for the source-gap contexts with the coatom off the lost point closed
  (`StageType.IsSourceGapContextOff`).  That coatom is closed by hypothesis; the transposition of
  the lost point with the last point only moves it to the coordinate first coatom
  (`Fin.castSuccEmb`), and makes the context one with the lost point last
  (`Realization.FirstCoatomCutoffDetermination.exists_coface_reindex`).  A relabelling
  never makes a coatom closed that is not.
* **The acquisition** (`Realization.residualAcquisition_isSourceGapContextOff`, in
  `VaughtConjecture.Continuation.SourceGapContext`): the acquired source-gap contexts have the lost
  point last, and their first coatom is the face of first loss, which is closed by the first-loss
  construction.
* **The main theorem from three finite statements, lost point last** (in `MainTheorem`,
  `densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGapLast_markedCap`), with
  (R4) and (R3) as in the source-gap form.  Its (R2) hypothesis is implied by the (R2)
  hypothesis of the source-gap form
  (`Realization.CoatomCutoffDetermination.isSourceGapContextLast`); no converse is claimed.

The reduction does not extend to the source-gap form by a relabelling.  The closed coatoms of a
context are the complements `univ.erase a` of the extreme points `a` of its plan
(`StageType.isPlan`, `Geometry.mem_extremes`, `StageType.erase_mem_faces_iff_mem_extremes`), at
most two (`Geometry.IsPlan.card_extremes_le_two`).  At a context none of whose witnessing lost
points is extreme, the coatom off each lost point is not closed: a relabelling can move it to the
coordinate first coatom but cannot make it closed, and the coatom form is asked only where the
first coatom is closed.  There the source-gap form asks determination with every witnessing lost
point on a closed first coatom, and this file does not reduce that to the form with the lost point
last.

**Not claimed.**  Coatom cutoff determination for `IsSourceGapContextLast` is not proved, nor are
(R4) and (R3), so the spectrum is not proved here.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset

namespace Realization

/-- **The coatom form with the lost point last is implied by the source-gap coatom form**:
`CoatomCutoffDetermination.mono` with `StageType.IsSourceGapContextLast.isSourceGapContext`. -/
theorem CoatomCutoffDetermination.isSourceGapContextLast
    (hdet : CoatomCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContext K h) :
    CoatomCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextLast K h :=
  hdet.mono fun _ _ _ _ _ _ hs ↦ hs.isSourceGapContext

/-- **Cutoff determination with the coatom off the lost point closed, from cutoff determination at
the first coatom with the lost point last**: relabel the context by the transposition `σ` of the
lost point `l` with the last point.  The relabelled context has the lost point last, its root
avoids the last point, and its coordinate first coatom is the image of the complement of `l`,
which is closed by the hypothesis (`IsSourceGapContextOff`); the transposition only moves it to the
coordinate position.  The form at the first coatom applies there
(`FirstCoatomCutoffDetermination.exists_coface_reindex`). -/
theorem FirstCoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff
    (hdet : FirstCoatomCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextLast K h) :
    CutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextOff K h where
  exists_coface α K n k t' h hα ht' hP t ht d hd hdK := by
    obtain ⟨l, o, r, hs, hface⟩ := hP
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := l.2; omega⟩
    set σ : Equiv.Perm (Fin (j + 1)) := Equiv.swap l (Fin.last j) with hσ
    -- relabelled by `σ`, the context has the lost point last
    have hsurj := t'.toScheme.surjective_cellMap_equiv σ
    obtain ⟨o', rfl⟩ := hsurj o
    obtain ⟨r', rfl⟩ := hsurj r
    have hs' := hs.reindex (σ := σ)
    rw [show σ.symm l = Fin.last j by simp [hσ]] at hs'
    -- the relabelled root avoids the last point, so it lies in the first coatom
    have hne (i : Fin n) : (h.trans σ.symm.toEmbedding) i ≠ Fin.last j :=
      fun hi ↦ hs'.notMem_range ⟨i, hi⟩
    let g : Fin n ↪ Fin j :=
      ⟨fun i ↦ ((h.trans σ.symm.toEmbedding) i).castPred (hne i), fun a b hab ↦
        (h.trans σ.symm.toEmbedding).injective (by simpa using congrArg Fin.castSucc hab)⟩
    have hg : g.trans Fin.castSuccEmb = h.trans σ.symm.toEmbedding :=
      Function.Embedding.ext fun i ↦ by simp [g]
    have hroot : (g.trans Fin.castSuccEmb).trans σ.toEmbedding = h := by
      rw [hg]
      exact Function.Embedding.ext fun i ↦ by simp
    -- the first coatom of the relabelled context is the complement of `l`
    have hcoatom : univ.map (Fin.castSuccEmb.trans σ.toEmbedding) = univ.erase l := by
      rw [← Finset.map_map, ← erase_cons (s := univ.map Fin.castSuccEmb) (a := Fin.last j)
        (by simp [Fin.castSucc_ne_last]), ← Fin.univ_castSuccEmb, map_erase, map_univ_equiv]
      simp [hσ]
    have hp : StageType.restrictFace Fin.castSuccEmb (t'.reindex σ) =
        some (t'.comap (Fin.castSuccEmb.trans σ.toEmbedding) (hcoatom ▸ hface)) := by
      rw [StageType.restrictFace_reindex]
      exact StageType.restrictFace_of_mem t' _ _
    have := hdet.exists_coface_reindex hα ht' σ ⟨Fin.last j, o', r', by simp, hg ▸ hs'⟩ hp
      (hroot ▸ ht) hd hdK
    rwa [hroot] at this

/-- **Cutoff determination with the coatom off the lost point closed, from the coatom form with
the lost point last**: `FirstCoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff`
through `CoatomCutoffDetermination.firstCoatom`. -/
theorem CoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff
    (hdet : CoatomCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextLast K h) :
    CutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextOff K h :=
  hdet.firstCoatom.cutoffDetermination_isSourceGapContextOff

end Realization

namespace MainTheorem

open FirstOrder Language baseLanguage Realization StageType
open Ordinal hiding univ

/-- **The thin `ℵ₁` spectrum from three finite coatom statements, lost point last**: the density
sentence has exactly `ℵ₁` classes of models coded on `ℕ` and no perfect set of pairwise
nonisomorphic ones, conditional on exactly three finite statements about stage types, none proved:
* (R4): cutoff completions at the first coatom for the graded cap calibration at every `ξ < ω₁`
  (`h4`);
* (R2): coatom cutoff determination for the source-gap context with the lost point last
  (`StageType.IsSourceGapContextLast`, `h2`);
* (R3): hollow coatom cutoff determination for the marked-cap context (`h3`).
As `densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap`, whose
(R2) hypothesis implies `h2` (`Realization.CoatomCutoffDetermination.isSourceGapContextLast`).
The acquisition `Realization.residualAcquisition_isSourceGapContextOff` and the reduction
`Realization.CoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff` are compiled. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGapLast_markedCap
    (h4 : ∀ ξ < ω₁, HasCutoffFirstCoatomCompletions.{0} ξ (GradedCapCalibration.{0} ξ))
    (h2 : CoatomCutoffDetermination.{0} fun K t' h ↦ t'.IsSourceGapContextLast K h)
    (h3 : HollowCoatomCutoffDetermination.{0} fun t' h ↦ t'.IsMarkedCapContext h) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_determinations
    (fun ξ hξ ↦ (h4 ξ hξ).hasCutoffStableRecoverySchemes_gradedCap)
    residualAcquisition_isSourceGapContextOff h2.cutoffDetermination_isSourceGapContextOff
    hollowAcquisition_isMarkedCapContext
    (h3.hollowCutoffDetermination (fun _ _ _ _ _ ht ↦ ht.not_surjective)
      fun _ _ _ _ _ σ ht ↦ ht.reindex σ)

end MainTheorem

end VaughtConjecture
