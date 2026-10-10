/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthCalibrationReindex
import VaughtConjecture.MainTheorem.GrowthSeed
import VaughtConjecture.MainTheorem.GrowthRelabelInputs
import VaughtConjecture.MainTheorem.GrowthAdmittedCarrier

/-!
# Growth carriers at the seed position

Roadmap, Layer 3 ((R3), the growth carrier at a calibrated context).

The contracts of the chain of record (`StageType.HasLadderGrowthCarriers`,
`StageType.HasRecognizingGrowthCarriers`, `StageType.HasExactGrowthCarriers`) are stated at every
context `t'` with every root `e`.  The growth seed (`StageType.exists_growthSeed`) is built at the
**seed position**: the context on `m + 1` points has its first coatom (the first `m` points) as a
closed face `p'`, the root is `g.trans Fin.castSuccEmb` inside it, and the donor has top grade at
most that of the context.  At this position the growth seed exists for every input
(`StageType.exists_growthSeed_atSeed`).

## Main definitions

* `StageType.HasExactGrowthCarriersAtSeed C`, `StageType.HasRecognizingGrowthCarriersAtSeed`,
  `StageType.HasLadderGrowthCarriersAtSeed`: the contracts at the seed position only (see the
  definitions for their status).

## Main statements

* `StageType.HasExactGrowthCarriersAtSeed.hasExactGrowthCarriers`: exact growth carriers at the
  seed position give them everywhere, for a calibration whose roots are never onto, invariant under
  relabelling the points of the context (the root relabelled along), and bounding the donor's top
  grade by the context's.  The root lies in a closed coatom, which is the first one after a
  relabelling `σ` (`Realization.exists_perm_root_eq`); the carrier at the relabelled context is
  relabelled back (`GrowthCarrier.relabel`) and its recovery is transported
  (`GrowthCarrier.Recovers.relabel`).
* The hollow reference calibration with a nonempty root has these three properties
  (`StageType.HollowReferenceCalibration'.not_surjective`,
  `StageType.HollowReferenceCalibration'.reindex`,
  `StageType.HollowReferenceCalibration'.topGrade_le`).
* `StageType.HasRecognizingGrowthCarriersAtSeed.hasExactGrowthCarriers` and
  `StageType.HasLadderGrowthCarriersAtSeed.hasExactGrowthCarriers`: the composed reductions, so a
  construction at the seed position suffices for the chain of record; and the main theorem from
  ladder carriers at the seed position
  (`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_ladderCarriersAtSeed`).

The recognizing form itself transfers as well: recognizing (or ladder) growth carriers at the
seed position give `StageType.HasRecognizingGrowthCarriers` at every context
(`StageType.HasRecognizingGrowthCarriersAtSeed.hasRecognizingGrowthCarriers`, in
`VaughtConjecture.MainTheorem.GrowthRelabelInputs`), the requests being relabelled with the context
and the top-grade clause of the seed position being automatic for exact calibrated requests.

These are implications.  The everywhere forms `StageType.HasLadderGrowthCarriers`,
`StageType.HasRecognizingGrowthCarriers` and `StageType.HasExactGrowthCarriers` for
`StageType.HollowReferenceCalibrationPos` follow from the stable contract at the seed position
(`StageType.hasLadderGrowthCarriersStableAtSeed_levels`; not yet reviewed), and so do the
seed-position forms with a compiled restriction (`StageType.HasRecognizingGrowthCarriers.atSeed`,
`StageType.HasExactGrowthCarriers.atSeed`).

**Scope.**  Not used by the main theorem through the levels
(`VaughtConjecture.MainTheorem.GrowthLevelRoute`); kept as reusable mathematics.

## References

Reindexing of stage types is [Kni26, Definition 3.1.2]; coatom amalgams and pinned extensions are
[Kni26, Lemma 4.3.2 and Corollary 4.3.22]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset StageType

namespace StageType

/-! ### The contracts at the seed position -/

/-- **Exact growth carriers at the seed position** for a calibration `C` (open): over every legal
`t'` on `m + 1` points at a limit stage whose first coatom is a closed face `p'`, along a root
`g.trans Fin.castSuccEmb` in the first coatom with face `t`, for every one-point coface `d` of `t`
of top grade at most that of `t'` with `C`, some growth carrier recovers the labels of `d` exactly
from the labels of `t'`. -/
def HasExactGrowthCarriersAtSeed
    (C : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄ (t' : StageType.{u} α (m + 1)) (g : Fin n ↪ Fin m)
    (p' : StageType.{u} α m), Order.IsSuccLimit α → t'.IsLegal →
    restrictFace Fin.castSuccEmb t' = some p' → ∀ t : StageType.{u} α n,
      restrictFace (g.trans Fin.castSuccEmb) t' = some t → ∀ d ∈ t.cofaces,
        d.topGrade ≤ t'.topGrade → C t' (g.trans Fin.castSuccEmb) d →
          ∃ G : GrowthCarrier t'.toScheme d.toScheme (g.trans Fin.castSuccEmb),
            G.Recovers t'.label fun j ℓ ↦ ℓ = d.label j

/-- **Exact growth carriers everywhere give them at the seed position.** -/
theorem HasExactGrowthCarriers.atSeed
    {C : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop}
    (h : HasExactGrowthCarriers.{u} C) : HasExactGrowthCarriersAtSeed.{u} C :=
  fun _ _ _ t' _ _ hα ht' _ t ht d hd _ hC ↦ h t' _ hα ht' t ht d hd hC

/-- **Exact growth carriers from the seed position**, for a calibration `C` whose roots are never
onto (`hns`), invariant under relabelling the points of the context with the root relabelled along
(`hinv`), and bounding the donor's top grade by the context's (`htop`).  After a relabelling `σ`
the root lies in the first coatom, a closed face (`Realization.exists_perm_root_eq`); the carrier
at `t'.reindex σ` is relabelled back to a carrier at `t'` with literal faces
(`GrowthCarrier.relabel`), and its exact recovery is transported
(`GrowthCarrier.Recovers.relabel`): the labels of `t'.reindex σ` are those of `t'` along the cell
map of `σ`. -/
theorem HasExactGrowthCarriersAtSeed.hasExactGrowthCarriers
    {C : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop}
    (hseed : HasExactGrowthCarriersAtSeed.{u} C)
    (hns : ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
      (d : StageType.{u} α (n + 1)), C t' h d → ¬ Function.Surjective h)
    (hinv : ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
      (d : StageType.{u} α (n + 1)) (σ : Equiv.Perm (Fin k)), C t' h d →
        C (t'.reindex σ) (h.trans σ.symm.toEmbedding) d)
    (htop : ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
      (d : StageType.{u} α (n + 1)), C t' h d → d.topGrade ≤ t'.topGrade) :
    HasExactGrowthCarriers.{u} C := by
  intro α n k t' h hα ht' t ht d hd hC
  have hs := hns t' h d hC
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    obtain ⟨x, -⟩ : ∃ x, x ∉ Set.range h := by
      by_contra! hall
      exact hs hall
    exact ⟨k - 1, by have := x.2; omega⟩
  obtain ⟨σ, g, p', rfl, hp'⟩ := Realization.exists_perm_root_eq ht hs
  have hroot : ((g.trans Fin.castSuccEmb).trans σ.toEmbedding).trans σ.symm.toEmbedding =
      g.trans Fin.castSuccEmb :=
    Function.Embedding.ext fun i ↦ by simp
  have hC' := hinv t' _ d σ hC
  rw [hroot] at hC'
  have ht'' : restrictFace (g.trans Fin.castSuccEmb) (t'.reindex σ) = some t := by
    rw [restrictFace_reindex]
    exact ht
  have htop' : d.topGrade ≤ (t'.reindex σ).topGrade := by
    rw [topGrade_reindex]
    exact htop t' _ d hC
  obtain ⟨G, hrec⟩ := hseed (t'.reindex σ) g p' hα (ht'.reindex σ) hp' t ht'' d hd htop' hC'
  exact ⟨GrowthCarrier.relabel (C := t'.toScheme) σ G, GrowthCarrier.Recovers.relabel σ G hrec⟩

/-- **The hollow reference calibration with a nonempty root is invariant under relabelling** the
points of the context, the root relabelled along (`StageType.HollowReferenceCalibration'.reindex`).
-/
theorem HollowReferenceCalibrationPos.reindex {α : Ordinal.{u}} {n k : ℕ}
    {t' : StageType.{u} α k} {h : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)}
    (hC : HollowReferenceCalibrationPos t' h d) (σ : Equiv.Perm (Fin k)) :
    HollowReferenceCalibrationPos (t'.reindex σ) (h.trans σ.symm.toEmbedding) d :=
  ⟨hC.1.reindex σ, hC.2⟩

/-- **Exact growth carriers for the hollow reference calibration with a nonempty root from the
seed position**: its roots are never onto, it is invariant under relabelling, and it bounds the
donor's top grade by the context's. -/
theorem HasExactGrowthCarriersAtSeed.hasExactGrowthCarriers_pos
    (hseed : HasExactGrowthCarriersAtSeed.{u} HollowReferenceCalibrationPos) :
    HasExactGrowthCarriers.{u} HollowReferenceCalibrationPos :=
  hseed.hasExactGrowthCarriers (fun _ _ _ _ _ _ hC ↦ hC.1.not_surjective)
    (fun _ _ _ _ _ _ σ hC ↦ hC.reindex σ) (fun _ _ _ _ _ _ hC ↦ hC.1.topGrade_le)

/-- **Recognizing growth carriers at the seed position** (from
`StageType.hasLadderGrowthCarriersStableAtSeed_levels` through
`StageType.HasRecognizingGrowthCarriers.atSeed`; not yet reviewed):
`StageType.HasRecognizingGrowthCarriers` asked only at contexts on `m + 1` points whose first coatom
is a closed face `p'`, along roots `g.trans Fin.castSuccEmb`, for donors of top grade at most that
of the context. -/
def HasRecognizingGrowthCarriersAtSeed : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄ (t' : StageType.{u} α (m + 1)) (g : Fin n ↪ Fin m)
    (p' : StageType.{u} α m), Order.IsSuccLimit α → t'.IsLegal →
    restrictFace Fin.castSuccEmb t' = some p' → ∀ (p : StageType.{u} α n)
      (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p) (d : StageType.{u} α (n + 1))
      (hd : d ∈ p.cofaces), d.topGrade ≤ t'.topGrade → 0 < n →
      ∀ Q : GrowthRequests t' d.toScheme,
        (∀ j ℓ, Q.CorrectAt t'.label j ℓ ↔ ℓ = d.label j) → Q.Calibrated hte →
        Q.HasRelativeLiftOnClass hte hd.2 →
        ∃ G : GrowthCarrier t'.toScheme d.toScheme (g.trans Fin.castSuccEmb), G.Recognizes Q

/-- **Recognizing growth carriers everywhere give them at the seed position.** -/
theorem HasRecognizingGrowthCarriers.atSeed (h : HasRecognizingGrowthCarriers.{u}) :
    HasRecognizingGrowthCarriersAtSeed.{u} :=
  fun _ _ _ t' _ _ hα ht' _ p hte d hd _ hn Q hex hQ hrel ↦
    h t' _ hα ht' p hte d hd hn Q hex hQ hrel

/-- **Ladder growth carriers at the seed position**: `StageType.HasLadderGrowthCarriers` asked only
at the seed position, as in `StageType.HasRecognizingGrowthCarriersAtSeed`.  No restriction from the
everywhere form is compiled; the everywhere form follows from
`StageType.hasLadderGrowthCarriersStableAtSeed_levels` (not yet reviewed). -/
def HasLadderGrowthCarriersAtSeed : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄ (t' : StageType.{u} α (m + 1)) (g : Fin n ↪ Fin m)
    (p' : StageType.{u} α m), Order.IsSuccLimit α → t'.IsLegal →
    restrictFace Fin.castSuccEmb t' = some p' → ∀ (p : StageType.{u} α n)
      (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p) (d : StageType.{u} α (n + 1))
      (hd : d ∈ p.cofaces), d.topGrade ≤ t'.topGrade → 0 < n →
      ∀ Q : GrowthRequests t' d.toScheme,
        (∀ j ℓ, Q.CorrectAt t'.label j ℓ ↔ ℓ = d.label j) → Q.Calibrated hte →
        Q.HasRelativeLiftOnClass hte hd.2 →
        ∃ G : GrowthCarrier t'.toScheme d.toScheme (g.trans Fin.castSuccEmb),
          (∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold)) ∧
          ∃ (Mb : Type) (H : ℕ) (r : Mb → ℕ → Fin G.scheme.card), 0 < H ∧
            (∀ a, ∀ i < H, G.scheme.toCellScheme.gradedIndex (r a i) = (univ, 1)) ∧
            (∀ a, ∀ i < H, G.scheme.rowAt (r a i) (r a i) = Label.ladderSource (i + 1) (i + 1)) ∧
            (∀ a, ∀ i < H, 0 < i →
              G.scheme.rowAt (r a i) (r a (i - 1)) = Label.ladderSource (i + 1) i) ∧
            ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
              ∃ (a : Mb) (F : ℕ → Label.{u}), G.IsLadderController Q (H := H) r u a F

/-- **Ladder growth carriers at the seed position recognize** (`GrowthCarrier.recognizes_of_ladder`,
as in `StageType.HasLadderGrowthCarriers.hasRecognizingGrowthCarriers`). -/
theorem HasLadderGrowthCarriersAtSeed.hasRecognizingGrowthCarriersAtSeed
    (h : HasLadderGrowthCarriersAtSeed.{u}) : HasRecognizingGrowthCarriersAtSeed.{u} := by
  intro α n m t' g p' hα ht' hp' p hte d hd hdK hn Q hex hQ hrel
  obtain ⟨G, hfull, Mb, H, r, hH, hr, hrd, hrp, hctrl⟩ :=
    h t' g p' hα ht' hp' p hte d hd hdK hn Q hex hQ hrel
  refine ⟨G, G.recognizes_of_ladder Q (by have := hQ.arity; omega) hfull (fun j ↦ ?_) hH r hr hrd
    hrp hctrl⟩
  rw [GrowthCarrier.donorCell, Scheme.grade_faceCell]
  exact (d.grade_le j).trans hQ.arity

/-- **Exact growth carriers at the seed position from recognizing carriers there**, as in
`StageType.HasRecognizingGrowthCarriers.hasExactGrowthCarriers`. -/
theorem HasRecognizingGrowthCarriersAtSeed.hasExactGrowthCarriersAtSeed
    (h : HasRecognizingGrowthCarriersAtSeed.{u}) :
    HasExactGrowthCarriersAtSeed.{u} HollowReferenceCalibrationPos := by
  intro α n m t' g p' hα ht' hp' p hte d hd hdK hC
  obtain ⟨hC, hn⟩ := hC
  obtain ⟨Q, hex, hQ, hrel⟩ := hC.exists_relativeLift ht' hte hd.2 hd.1 hn
  obtain ⟨G, hrec⟩ := h t' g p' hα ht' hp' p hte d hd hdK hn Q hex hQ
    (GrowthRequests.hasRelativeLiftOnClass_of_hasRelativeLift hte hd.2 hex hQ hd.1 hn hrel)
  exact ⟨G, GrowthRequests.recovers_eq_of_recognizes hex hQ G hrec⟩

/-- **Exact growth carriers for the hollow reference calibration with a nonempty root from
recognizing carriers at the seed position**: a construction at the seed position suffices. -/
theorem HasRecognizingGrowthCarriersAtSeed.hasExactGrowthCarriers
    (h : HasRecognizingGrowthCarriersAtSeed.{u}) :
    HasExactGrowthCarriers.{u} HollowReferenceCalibrationPos :=
  h.hasExactGrowthCarriersAtSeed.hasExactGrowthCarriers_pos

/-- **Exact growth carriers for the hollow reference calibration with a nonempty root from ladder
carriers at the seed position.** -/
theorem HasLadderGrowthCarriersAtSeed.hasExactGrowthCarriers
    (h : HasLadderGrowthCarriersAtSeed.{u}) :
    HasExactGrowthCarriers.{u} HollowReferenceCalibrationPos :=
  h.hasRecognizingGrowthCarriersAtSeed.hasExactGrowthCarriers

/-- **The growth seed exists at every input of the seed position**
(`StageType.exists_growthSeed`): its first coatom type is `t'`, its second coatom type has top
grade at most that of `t'`, and the face of its amalgam along the root followed by the new point
is `d`. -/
theorem exists_growthSeed_atSeed {α : Ordinal.{u}} {n m : ℕ} (hα : Order.IsSuccLimit α)
    {t' : StageType.{u} α (m + 1)} (ht' : t'.IsLegal) {g : Fin n ↪ Fin m}
    {p' : StageType.{u} α m} (hp' : restrictFace Fin.castSuccEmb t' = some p')
    {p : StageType.{u} α n} (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p)
    {d : StageType.{u} α (n + 1)} (hd : d ∈ p.cofaces) (hdK : d.topGrade ≤ t'.topGrade) :
    ∃ I : Seed.{u} α m, I.left = t' ∧ I.right.topGrade ≤ t'.topGrade ∧
      restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d :=
  exists_growthSeed hα ht' hp' ((restrictFace_trans t' _ g hp').trans hte) hd hdK

end StageType

namespace MainTheorem

open Ordinal Realization FirstOrder Language Structure baseLanguage Expansion

/-- **The thin `ℵ₁` spectrum from recognizing growth carriers at the seed position**: as
`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_recognizingCarriers`, with the carriers
asked only at the seed position.  `hstab` and `hrec` follow from
`StageType.hasLadderGrowthCarriersStableAtSeed_levels` (not yet reviewed); `hres` is (R2), proved by
`Realization.receivingResidualReceiving_of_padded`. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_recognizingCarriersAtSeed
    (hstab : ∀ ξ < ω₁, HasStableGrowthCarriers.{0} ξ (GradedCapMarginCalibration.{0} ξ))
    (hres : ReceivingResidualReceiving.{0, 0})
    (hrec : HasRecognizingGrowthCarriersAtSeed.{0}) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_growthCarriers_pos hstab hres
    hrec.hasExactGrowthCarriers

/-- **The thin `ℵ₁` spectrum from ladder growth carriers at the seed position**: as
`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_ladderCarriers`, with the carriers asked
only at the seed position.  `hstab` follows from
`StageType.hasLadderGrowthCarriersStableAtSeed_levels` (not yet reviewed); `hres` is (R2), proved by
`Realization.receivingResidualReceiving_of_padded`. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_ladderCarriersAtSeed
    (hstab : ∀ ξ < ω₁, HasStableGrowthCarriers.{0} ξ (GradedCapMarginCalibration.{0} ξ))
    (hres : ReceivingResidualReceiving.{0, 0})
    (hlad : HasLadderGrowthCarriersAtSeed.{0}) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_growthCarriers_pos hstab hres
    hlad.hasExactGrowthCarriers

end MainTheorem

namespace StageType

open Finset Label
variable {α : Ordinal.{u}} {n k : ℕ} (t' : StageType.{u} α k) (σ : Equiv.Perm (Fin k))

/-- **Recognizing growth carriers from the seed position**: recognizing growth carriers at the
seed position give them at every context.  The root of calibrated requests is not onto
(`StageType.GrowthRequests.Calibrated.not_surjective`); after a relabelling `σ` it lies in the
first coatom, a closed face (`Realization.exists_perm_root_eq`); the requests, their exactness,
calibration and relative lift are carried to `t'.reindex σ`, where the top-grade clause holds
(`StageType.GrowthRequests.topGrade_le_of_exact`); the recognizing carrier there is relabelled back
(`GrowthCarrier.Recognizes.relabel`). -/
theorem HasRecognizingGrowthCarriersAtSeed.hasRecognizingGrowthCarriers
    (h : HasRecognizingGrowthCarriersAtSeed.{u}) : HasRecognizingGrowthCarriers.{u} := by
  intro α n k t' e hα ht' p hte d hd hn Q hex hQ hrel
  have hs := hQ.not_surjective
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    obtain ⟨x, -⟩ : ∃ x, x ∉ Set.range e := by
      by_contra! hall
      exact hs hall
    exact ⟨k - 1, by have := x.2; omega⟩
  obtain ⟨σ, g, p', rfl, hp'⟩ := Realization.exists_perm_root_eq hte hs
  have hte'' : restrictFace (g.trans Fin.castSuccEmb) (t'.reindex σ) = some p := by
    rw [restrictFace_reindex]
    exact hte
  have hex'' (i : Fin d.card) (ℓ : Label.{u}) :
      (Q.reindex σ).CorrectAt (t'.reindex σ).label i ℓ ↔ ℓ = d.label i :=
    (GrowthRequests.correctAt_reindex_iff σ Q t'.label i ℓ).trans (hex i ℓ)
  have hdK : d.topGrade ≤ (t'.reindex σ).topGrade := by
    rw [topGrade_reindex]
    exact GrowthRequests.topGrade_le_of_exact hex hQ
  obtain ⟨G, hrec⟩ := h (t'.reindex σ) g p' hα (ht'.reindex σ) hp' p hte'' d hd hdK hn
    (Q.reindex σ) hex'' (hQ.reindex σ hte'' hte) (hrel.reindex σ hte'' hte hd.2)
  exact ⟨GrowthCarrier.relabel (C := t'.toScheme) σ G, GrowthCarrier.Recognizes.relabel σ G hrec⟩

end StageType

namespace StageType

open Finset Label
variable {α : Ordinal.{u}} {n k : ℕ} (t' : StageType.{u} α k) (σ : Equiv.Perm (Fin k))

/-- **Recognizing growth carriers from ladder carriers at the seed position**
(`StageType.HasLadderGrowthCarriersAtSeed.hasRecognizingGrowthCarriersAtSeed`, then the
relabelling). -/
theorem HasLadderGrowthCarriersAtSeed.hasRecognizingGrowthCarriers
    (h : HasLadderGrowthCarriersAtSeed.{u}) : HasRecognizingGrowthCarriers.{u} :=
  h.hasRecognizingGrowthCarriersAtSeed.hasRecognizingGrowthCarriers

end StageType

end VaughtConjecture
