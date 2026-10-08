/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthRecognition

/-!
# Admission forced on every face of a recognizing carrier

Roadmap, Layer 3 ((R3) and (R4), the second coatom of the recognizing growth carrier).

A recognizing growth carrier extends **every** lawful section of **every** closed face to a lawful
section of the carrier whose context and donor parts are admitted on the exact class
(`GrowthCarrier.exists_admitted_extension`, the cap `⊥` of
`GrowthCarrier.exists_admitsOnClass_extend`).  At a face containing the donor face but not the
context cap (the second coatom of the seed amalgam, whose cap has full scope in the context), the
donor values are fixed by the section of the face, and the context values off the face are the
only freedom.  Hence the **obstruction** (`GrowthCarrier.not_recognizes_of_bottom`): if a lawful
section of such a face is positive at a bottom request, and every lawful extension of it to the
carrier has a context part in the class of `t'` below the cap with a positive cap value, the
carrier does not recognize admitted states.

So over the seed amalgam, a carrier whose face along the second coatom is the enlarged donor
itself (only cells of full scope added) recognizes only if every lawful section of the enlarged
donor extends, through the context cells off that coatom, to an admitted or off-class context
section.  Where the enlarged donor has a lawful section positive at a bottom request and the
cap and the bottom class are forced by availability, this fails: the second coatom must carry the
recognition data itself (the replication of the full-scope cells into it).

## References

The controllers and the growth step are those of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType.GrowthRequests

variable {α : Ordinal.{u}} {J n : ℕ} {t' : StageType.{u} α J} {D : Scheme.{u} (n + 1)}
  {Q : StageType.GrowthRequests t' D}

/-- **Admission transfers under capped agreement above the cap value**: if `(s, v)` is admitted
on the exact class and `(s', v')` agrees with it capped at `c > ⊥`, strictly above the cap value
of `s` (self-visible at the threshold), then `(s', v')` is admitted on the exact class.  The reads
of the requests are capped at the cap value, below `c`. -/
theorem AdmitsOnClass.of_min_eq {s s' : Fin t'.card → Label.{u}} {v v' : Fin D.card → Label.{u}}
    (h : Q.AdmitsOnClass s v) {c : Label.{u}} (hc0 : c ≠ ⊥)
    (hss : ∀ x, min (s' x) c = min (s x) c) (hvv : ∀ j, min (v' j) c = min (v j) c)
    (hcap : s Q.cap < c) (hvis : IsSelfVisible Q.threshold (s Q.cap))
    (hoff : ∀ j ∈ Q.exacts, Q.offset j ≤ Q.threshold) (hR : Q.markerOffset ≤ Q.threshold) :
    Q.AdmitsOnClass s' v' := by
  intro hcls hcap0
  have hcap' : s' Q.cap = s Q.cap := by
    have h1 := hss Q.cap
    rw [min_eq_left hcap.le] at h1
    rcases le_total (s' Q.cap) c with hle | hle
    · rwa [min_eq_left hle] at h1
    · rw [min_eq_right hle] at h1
      exact absurd h1.symm hcap.ne
  have hS (a a' : Label.{u}) (haa : min a' c = min a c) :
      min a' (s Q.cap) = min a (s Q.cap) := Label.min_eq_min_of_le haa hcap.le
  have hV (a a' : Label.{u}) (haa : min a' c = min a c) {i : ℕ} (hi : i ≤ Q.threshold) :
      min (visibilityReplace Q.threshold i a') (s Q.cap) =
        min (visibilityReplace Q.threshold i a) (s Q.cap) := by
    rw [← visibilityReplace_min_of_isSelfVisible hi hvis,
      ← visibilityReplace_min_of_isSelfVisible hi hvis, hS a a' haa]
  have hcls' : ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      s x = ⊥ ↔ t'.label x = ⊥ := fun x hx ↦
    (Label.eq_bot_iff_of_min_eq (hss x) hc0).symm.trans (hcls x hx)
  have hcap0' : s Q.cap ≠ ⊥ := hcap' ▸ hcap0
  intro j
  obtain ⟨h1, h2, h3⟩ := h hcls' hcap0' j
  refine ⟨fun hj ↦ ?_, fun hj ↦ ?_, fun hj ↦ ?_⟩
  · rw [hcap', hS _ _ (hvv j)]; exact h1 hj
  · rw [hcap', hS _ _ (hvv j), h2 hj, readExact, readExact, hcap',
      hV _ _ (hss (Q.ref j)) (hoff j hj)]
  · have h3' := h3 hj
    rw [readMarker] at h3' ⊢
    rw [hcap', hV _ _ (hss Q.marker) hR, hS _ _ (hvv j)]
    exact h3'

end StageType.GrowthRequests

namespace GrowthCarrier

variable {α : Ordinal.{u}} {J n : ℕ} {t' : StageType.{u} α J} {D : Scheme.{u} (n + 1)}
  {e : Fin n ↪ Fin J} (G : GrowthCarrier t'.toScheme D e) (Q : StageType.GrowthRequests t' D)

/-- **A recognizing carrier extends every lawful section of a closed face to an admitted lawful
section.** -/
theorem exists_admitted_extension (hrec : G.Recognizes Q)
    (href : ∀ j ∈ Q.exacts, Q.ref j ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) ∧
      Q.offset j ≤ Q.threshold)
    (hmk : Q.marker ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) ∧
      Q.markerOffset ≤ Q.threshold)
    {m : ℕ} {f : Fin m ↪ Fin (J + 1)} (hf : univ.map f ∈ G.scheme.toCellScheme.faces)
    {ℓ : Fin (G.scheme.comap f).card → Label.{u}} (hℓ : (G.scheme.comap f).rows.IsLawful ℓ) :
    ∃ r : Fin G.scheme.card → Label.{u}, G.scheme.rows.IsLawful r ∧
      (∀ i, r (G.scheme.cellMap f i) = ℓ i) ∧
      Q.AdmitsOnClass (fun x ↦ r (G.contextCell x)) (fun j ↦ r (G.donorCell j)) := by
  obtain ⟨r, hr, -, hrℓ, hadm⟩ := G.exists_admitsOnClass_extend Q hrec href hmk hf
    (isSelfVisible_bot _) hℓ CellScheme.Rows.isLawful_const_bot fun _ ↦ by simp
  exact ⟨r, hr, hrℓ, hadm⟩

/-- **The obstruction at a face**: if a lawful section `ℓ` of a closed face is such that every
lawful extension of it to the carrier is positive at a bottom request `j`, has a context part in
the bottom class of `t'` below the cap, and a positive cap value, then the carrier does not
recognize admitted states. -/
theorem not_recognizes_of_bottom
    (href : ∀ j ∈ Q.exacts, Q.ref j ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) ∧
      Q.offset j ≤ Q.threshold)
    (hmk : Q.marker ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) ∧
      Q.markerOffset ≤ Q.threshold)
    {m : ℕ} {f : Fin m ↪ Fin (J + 1)} (hf : univ.map f ∈ G.scheme.toCellScheme.faces)
    {ℓ : Fin (G.scheme.comap f).card → Label.{u}} (hℓ : (G.scheme.comap f).rows.IsLawful ℓ)
    {j : Fin D.card} (hj : j ∈ Q.bottoms)
    (hforced : ∀ r : Fin G.scheme.card → Label.{u}, G.scheme.rows.IsLawful r →
      (∀ i, r (G.scheme.cellMap f i) = ℓ i) →
      r (G.donorCell j) ≠ ⊥ ∧
        (∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
          r (G.contextCell x) = ⊥ ↔ t'.label x = ⊥) ∧ r (G.contextCell Q.cap) ≠ ⊥) :
    ¬ G.Recognizes Q := by
  intro hrec
  obtain ⟨r, hr, hrℓ, hadm⟩ := G.exists_admitted_extension Q hrec href hmk hf hℓ
  obtain ⟨hj0, hcls, hcap⟩ := hforced r hr hrℓ
  exact hj0 (StageType.GrowthRequests.eq_bot_of_correctAt (hadm hcls hcap j) hj hcap)

end GrowthCarrier

end VaughtConjecture
