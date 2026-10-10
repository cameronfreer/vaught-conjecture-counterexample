/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthRequests

/-!
# The admitted step of the growth construction: the reads below the cap

Roadmap, Layer 3 ((R3) and (R4), the controllers at the activation grade).  A profile of the
growth amalgam is a section `s` of the context with a labelling `v` of the donor; it is **admitted
by the requests** (`StageType.GrowthRequests.Admits`) when, if `s` has the bottom class of the
context below the cap and a cap value other than `⊥`, `v` reads the requests from `s`.  The
controllers at the activation grade are the admitted profiles; the capped lift from the context
face into them (the catalogue step of `VaughtConjecture.Extension.TowerCatalogueLayer` for this
predicate) asks: if `(s, v)` agrees with an admitted profile `(s', v')` capped at a cap `h > ⊥`,
some admitted profile extends `s`, agreeing with `(s', v')` capped at `h`.

**The reads one by one** (`StageType.GrowthRequests.admits_of_min_eq_of_lt`).  When the cap value
`c` of `s` is below `h`, capped agreement at `h` gives agreement capped at `c`; the bottom class
and `c` itself pass from `s` to `s'`; and every read of the requests is capped at `c`: the bottom
read trivially, the exact read and the marker read because visibility replacement at the threshold
commutes with capping at the cap value, self-visible at the threshold.  So every profile agreeing
with an admitted one capped above its cap value is admitted, with no condition on the donor
values above the cap value: **the admitted step holds below the cap value**.

**Invariance under the orbit code** (`StageType.GrowthRequests.Admits.map`,
`StageType.GrowthRequests.Admits.orbitMap`): the catalogue step asks admission of the orbit code
of the extension; the orbit map at a grade at least the threshold is monotone, bottom exactly at
bottom, and commutes with visibility replacement there, so it keeps admission.

**Above the cap value** (`h ≤ c`) the reads of `s` and of `s'` agree only capped at `h`, while the
requests read the donor below `c`: an exact read `visibilityReplace N i (s ρ)` with a value in
`[h, c)` is prescribed at the donor cell, and the donor values of the extension above `h` are not
determined by the capped agreement.  So the admitted step above the cap value asks for a lawful
donor completion of the context section with the request reads prescribed below the cap value: the
request lift of `GrowthCarrier.exists_requestLift_of_cappedLift` at the cap `h`.  This case is
open.

## References

Visibility replacement is [Kni26, Definition 2.2.3]; the controllers of the growth step are those
of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType.GrowthRequests

variable {α : Ordinal.{u}} {n k : ℕ} {t' : StageType.{u} α k} {D : Scheme.{u} (n + 1)}
  (Q : GrowthRequests t' D)

/-- A profile `(s, v)` is **admitted by the requests**: if `s` reads no cell of the context below
the cap as `⊥` unless the context does, and reads the cap above `⊥`, then `v` reads the requests
from `s`. -/
def Admits (s : Fin t'.card → Label.{u}) (v : Fin D.card → Label.{u}) : Prop :=
  (∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap), s x = ⊥ → t'.label x = ⊥) →
    s Q.cap ≠ ⊥ → ∀ j, Q.CorrectAt s j (v j)

variable {Q}

/-- Capped agreement at `h` gives capped agreement at every `c ≤ h`. -/
theorem min_eq_min_of_le {x y h c : Label.{u}} (hxy : min x h = min y h) (hc : c ≤ h) :
    min x c = min y c := by
  rw [← min_eq_right hc, ← min_assoc, hxy, min_assoc]

/-- **The admitted step below the cap value.**  If `(s, v)` agrees with an admitted profile
`(s', v')` capped at `h > ⊥`, and the cap value of `s` is below `h` and self-visible at the
threshold, with the offsets at most the threshold, then `(s, v)` is admitted. -/
theorem admits_of_min_eq_of_lt {s s' : Fin t'.card → Label.{u}} {v v' : Fin D.card → Label.{u}}
    (hadm : Q.Admits s' v') {h : Label.{u}} (hh : h ≠ ⊥)
    (hs : ∀ x, min (s x) h = min (s' x) h) (hv : ∀ j, min (v j) h = min (v' j) h)
    (hlt : s Q.cap < h) (hvis : IsSelfVisible Q.threshold (s Q.cap))
    (hoff : ∀ j ∈ Q.exacts, Q.offset j ≤ Q.threshold) (hR : Q.markerOffset ≤ Q.threshold) :
    Q.Admits s v := by
  intro hclass hcap j
  set c := s Q.cap with hc
  -- the cap values agree
  have hcc : s' Q.cap = c := by
    have h1 := hs Q.cap
    rw [min_eq_left hlt.le] at h1
    rcases le_total (s' Q.cap) h with hle | hle
    · rw [min_eq_left hle] at h1; exact h1.symm
    · rw [min_eq_right hle] at h1; exact absurd h1 hlt.ne
  -- capped agreement at `c`
  have hsc (x) : min (s x) c = min (s' x) c := min_eq_min_of_le (hs x) hlt.le
  have hvc (j) : min (v j) c = min (v' j) c := min_eq_min_of_le (hv j) hlt.le
  -- the bottom class passes to `s'`
  have hbot (x) : s x = ⊥ ↔ s' x = ⊥ := by
    have h1 := hs x
    constructor
    · intro hx
      rw [hx, min_eq_left bot_le] at h1
      rcases min_eq_bot.mp h1.symm with h' | h'
      · exact h'
      · exact absurd h' hh
    · intro hx
      rw [hx, min_eq_left bot_le] at h1
      rcases min_eq_bot.mp h1 with h' | h'
      · exact h'
      · exact absurd h' hh
  have hA := hadm (fun x hx hx' ↦ hclass x hx ((hbot x).mpr hx')) (by rw [hcc]; exact hcap) j
  -- the reads agree
  have hread (x : Fin t'.card) (i : ℕ) (hi : i ≤ Q.threshold) :
      min (visibilityReplace Q.threshold i (s x)) c =
        min (visibilityReplace Q.threshold i (s' x)) c := by
    rw [← visibilityReplace_min_of_isSelfVisible hi hvis, hsc,
      visibilityReplace_min_of_isSelfVisible hi hvis]
  refine ⟨fun hz ↦ ?_, fun hf ↦ ?_, fun hy ↦ ?_⟩
  · rw [hvc, ← hcc]
    exact hA.1 hz
  · rw [hvc, readExact, ← hc, hread _ _ (hoff j hf), ← hcc]
    exact hA.2.1 hf
  · rw [readMarker, ← hc, hread _ _ hR, hvc, ← hcc]
    exact hA.2.2 hy

/-- **The admitted step at or below the cap value of the new section**: if `(s, v)` agrees with an
admitted `(s', v')` capped at `h > ⊥`, and the cap value `c` of `s` is at most `h` and
self-visible at the threshold, then `(s, v)` is admitted: the cap value of `s'` is at least `c`,
and every read of the requests at `s'` capped at `c` is the read at `s`. -/
theorem admits_of_min_eq_of_le {s s' : Fin t'.card → Label.{u}} {v v' : Fin D.card → Label.{u}}
    (hadm : Q.Admits s' v') {h : Label.{u}} (hh : h ≠ ⊥)
    (hs : ∀ x, min (s x) h = min (s' x) h) (hv : ∀ j, min (v j) h = min (v' j) h)
    (hle : s Q.cap ≤ h) (hvis : IsSelfVisible Q.threshold (s Q.cap))
    (hoff : ∀ j ∈ Q.exacts, Q.offset j ≤ Q.threshold) (hR : Q.markerOffset ≤ Q.threshold) :
    Q.Admits s v := by
  intro hclass hcap j
  set c := s Q.cap with hc
  have hcc : c ≤ s' Q.cap := by
    have h1 := hs Q.cap
    rw [min_eq_left hle] at h1
    exact h1.trans_le (min_le_left _ _)
  have hsc (x) : min (s x) c = min (s' x) c := min_eq_min_of_le (hs x) hle
  have hvc (j) : min (v j) c = min (v' j) c := min_eq_min_of_le (hv j) hle
  have hbot (x) : s x = ⊥ ↔ s' x = ⊥ := by
    have h1 := hs x
    constructor
    · intro hx
      rw [hx, min_eq_left bot_le] at h1
      rcases min_eq_bot.mp h1.symm with h' | h'
      · exact h'
      · exact absurd h' hh
    · intro hx
      rw [hx, min_eq_left bot_le] at h1
      rcases min_eq_bot.mp h1 with h' | h'
      · exact h'
      · exact absurd h' hh
  have hA := hadm (fun x hx hx' ↦ hclass x hx ((hbot x).mpr hx'))
    (fun h0 ↦ hcap (le_bot_iff.mp (h0 ▸ hcc))) j
  have hread (x : Fin t'.card) (i : ℕ) (hi : i ≤ Q.threshold) :
      min (visibilityReplace Q.threshold i (s x)) c =
        min (visibilityReplace Q.threshold i (s' x)) c := by
    rw [← visibilityReplace_min_of_isSelfVisible hi hvis, hsc,
      visibilityReplace_min_of_isSelfVisible hi hvis]
  refine ⟨fun hz ↦ ?_, fun hf ↦ ?_, fun hy ↦ ?_⟩
  · rw [hvc, ← min_eq_right hcc, ← min_assoc, hA.1 hz, min_eq_left bot_le]
  · have h1 := hA.2.1 hf
    rw [readExact] at h1 ⊢
    rw [← hc, hvc, hread _ _ (hoff j hf), ← min_eq_right hcc, ← min_assoc, h1, min_assoc]
  · have h1 := hA.2.2 hy
    rw [readMarker] at h1 ⊢
    rw [← hc, hread _ _ hR, hvc]
    calc min (visibilityReplace Q.threshold Q.markerOffset (s' Q.marker)) c
        = min (min (visibilityReplace Q.threshold Q.markerOffset (s' Q.marker)) (s' Q.cap)) c := by
          rw [min_assoc, min_eq_right hcc]
      _ ≤ min (min (v' j) (s' Q.cap)) c := min_le_min_right _ h1
      _ = min (v' j) c := by rw [min_assoc, min_eq_right hcc]

/-- **Admission is invariant under a relabelling of the values** by a monotone map that is bottom
exactly at bottom and commutes with visibility replacement at the threshold with values at most the
threshold: the reads of the requests are minima and visibility replacements of the values. -/
theorem Admits.map {s : Fin t'.card → Label.{u}} {v : Fin D.card → Label.{u}}
    (hadm : Q.Admits s v) {Ψ : Label.{u} → Label.{u}} (hΨ : Monotone Ψ)
    (hΨb : ∀ x, Ψ x = ⊥ ↔ x = ⊥)
    (hΨv : ∀ i ≤ Q.threshold, ∀ x, Ψ (visibilityReplace Q.threshold i x) =
      visibilityReplace Q.threshold i (Ψ x))
    (hoff : ∀ j ∈ Q.exacts, Q.offset j ≤ Q.threshold) (hR : Q.markerOffset ≤ Q.threshold) :
    Q.Admits (Ψ ∘ s) (Ψ ∘ v) := by
  intro hclass hcap j
  have hA := hadm (fun x hx hx' ↦ hclass x hx ((hΨb _).mpr hx'))
    (fun h ↦ hcap ((hΨb _).mpr h)) j
  refine ⟨fun hz ↦ ?_, fun hf ↦ ?_, fun hy ↦ ?_⟩
  · change min (Ψ (v j)) (Ψ (s Q.cap)) = ⊥
    rw [← hΨ.map_min, hA.1 hz]
    exact (hΨb ⊥).mpr rfl
  · change min (Ψ (v j)) (Ψ (s Q.cap)) =
      min (visibilityReplace Q.threshold (Q.offset j) (Ψ (s (Q.ref j)))) (Ψ (s Q.cap))
    have h1 := hA.2.1 hf
    rw [readExact] at h1
    rw [← hΨ.map_min, h1, ← hΨv _ (hoff j hf), hΨ.map_min]
  · change min (visibilityReplace Q.threshold Q.markerOffset (Ψ (s Q.marker))) (Ψ (s Q.cap)) ≤
      min (Ψ (v j)) (Ψ (s Q.cap))
    have h1 := hA.2.2 hy
    rw [readMarker] at h1
    rw [← hΨv _ hR, ← hΨ.map_min, ← hΨ.map_min]
    exact hΨ h1

/-- **Admission is invariant under the orbit code** at a grade at least the threshold: the orbit
map of a labelling is a witness with the step suppressor (`Label.isWitness_orbitMap`), bottom
exactly at bottom. -/
theorem Admits.orbitMap {s : Fin t'.card → Label.{u}} {v : Fin D.card → Label.{u}}
    (hadm : Q.Admits s v) {K : ℕ} (hK : Q.threshold ≤ K) {ι : Type*} [Fintype ι]
    (w : ι → Label.{u}) (hoff : ∀ j ∈ Q.exacts, Q.offset j ≤ Q.threshold)
    (hR : Q.markerOffset ≤ Q.threshold) :
    Q.Admits (orbitMap K w ∘ s) (orbitMap K w ∘ v) :=
  hadm.map (monotone_orbitMap K w) (fun _ ↦ orbitMap_eq_bot_iff)
    (fun i hi x ↦ (isWitness_orbitMap K w).visibilityReplace_comm x _
      (by rw [stepSuppressor_of_le hK]; exact le_top) i hi) hoff hR

end StageType.GrowthRequests

end VaughtConjecture
