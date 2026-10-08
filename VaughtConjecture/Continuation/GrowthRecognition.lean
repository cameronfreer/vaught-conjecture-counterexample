/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthAdmittedSections
import VaughtConjecture.Continuation.GrowthRelativeLiftCases

/-!
# Admission on the exact class, and recovery by recognition

Roadmap, Layer 3 ((R3) and (R4), the controllers of the growth construction).

A carrier whose cells of full scope at the threshold are all admitted cannot be continued by good
levels (`ProfileTower.Lvl.Good.not_forall_admitted`).  This file states the two notions that
replace it.

* **Admission on the exact class** (`StageType.GrowthRequests.AdmitsOnClass`): `(s, v)` reads the
  requests whenever `s` has exactly the bottom pattern of `t'` below the cap and a cap value other
  than `⊥`.  It is required of the catalogue states at the grades at least the threshold only (the
  activation grade is the threshold; no further cutoff).  One-way admission
  (`StageType.GrowthRequests.Admits`) implies it.  The relative lift on the exact class
  (`StageType.GrowthRequests.HasRelativeLiftOnClass`) follows from the relative lift
  (`StageType.GrowthRequests.hasRelativeLiftOnClass_of_hasRelativeLift`): on the class and at a
  positive cap the old pair reads the requests outright, and at the cap `⊥` the pair of labels
  serves as the old pair.
* **Recognition** (`GrowthCarrier.Recognizes`): every lawful section of the carrier, capped at a
  label `H` at least its cap value and self-visible at the threshold, is on the context cells below
  the cap and on the donor cells the image of a state admitted on the exact class under a monotone
  map fixing `⊥`, commuting with visibility replacement at the threshold, and reflecting `⊥` on the
  context values of the state below the cap.  It replaces "every cell of full scope at the
  threshold is admitted": the state is recognized in the section, not read off one row, and the
  reflection of `⊥` carries the bottom pattern from the section to the state in both directions.
* **Recovery by recognition** (`GrowthCarrier.recovers_of_recognizes`): a recognizing carrier
  recovers the relation of the requests from every context section with exactly the bottom pattern
  of `t'` below the cap and a cap value other than `⊥`; the labels of `t'` are such a section.

## References

The controllers and the growth step are those of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

namespace GrowthRequests

section Class

variable {t' : StageType.{u} α k} {D : Scheme.{u} (n + 1)} (Q : GrowthRequests t' D)

/-- **Admission on the exact class**: if `s` is `⊥` below the cap exactly where `t'` is labelled
`⊥`, and the cap value of `s` is not `⊥`, then `v` reads the requests from `s`. -/
def AdmitsOnClass (s : Fin t'.card → Label.{u}) (v : Fin D.card → Label.{u}) : Prop :=
  (∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap), s x = ⊥ ↔ t'.label x = ⊥) →
    s Q.cap ≠ ⊥ → ∀ j, Q.CorrectAt s j (v j)

variable {Q}

/-- One-way admission implies admission on the exact class. -/
theorem Admits.admitsOnClass {s : Fin t'.card → Label.{u}} {v : Fin D.card → Label.{u}}
    (h : Q.Admits s v) : Q.AdmitsOnClass s v :=
  fun hcls hcap ↦ h (fun x hx hb ↦ (hcls x hx).mp hb) hcap

/-- **The relation of the requests is carried by a monotone map** fixing `⊥` and commuting with
visibility replacement at the threshold. -/
theorem CorrectAt.map {s : Fin t'.card → Label.{u}} {j : Fin D.card} {ℓ : Label.{u}}
    (h : Q.CorrectAt s j ℓ) {θ : Label.{u} → Label.{u}} (hθ : Monotone θ) (hθb : θ ⊥ = ⊥)
    (hθv : ∀ i ≤ Q.threshold, ∀ x, θ (visibilityReplace Q.threshold i x) =
      visibilityReplace Q.threshold i (θ x))
    (hoff : j ∈ Q.exacts → Q.offset j ≤ Q.threshold) (hR : Q.markerOffset ≤ Q.threshold) :
    Q.CorrectAt (θ ∘ s) j (θ ℓ) := by
  refine ⟨fun hz ↦ ?_, fun hf ↦ ?_, fun hy ↦ ?_⟩
  · change min (θ ℓ) (θ (s Q.cap)) = ⊥
    rw [← hθ.map_min, h.1 hz, hθb]
  · change min (θ ℓ) (θ (s Q.cap)) =
      min (visibilityReplace Q.threshold (Q.offset j) (θ (s (Q.ref j)))) (θ (s Q.cap))
    rw [← hθ.map_min, h.2.1 hf, readExact, ← hθv _ (hoff hf), hθ.map_min]
  · change min (visibilityReplace Q.threshold Q.markerOffset (θ (s Q.marker))) (θ (s Q.cap)) ≤
      min (θ ℓ) (θ (s Q.cap))
    have h1 := h.2.2 hy
    rw [readMarker] at h1
    rw [← hθv _ hR, ← hθ.map_min, ← hθ.map_min]
    exact hθ h1

/-- The relation of the requests reads a section only at the cap, the references and the
marker. -/
theorem CorrectAt.congr {s s' : Fin t'.card → Label.{u}} {j : Fin D.card} {ℓ : Label.{u}}
    (h : Q.CorrectAt s j ℓ) (hc : s Q.cap = s' Q.cap)
    (hr : j ∈ Q.exacts → s (Q.ref j) = s' (Q.ref j)) (hm : s Q.marker = s' Q.marker) :
    Q.CorrectAt s' j ℓ := by
  refine ⟨fun hz ↦ ?_, fun hf ↦ ?_, fun hy ↦ ?_⟩
  · rw [← hc]; exact h.1 hz
  · rw [← hc, readExact, ← hr hf, ← hc]; exact h.2.1 hf
  · rw [readMarker, ← hm, ← hc]; exact h.2.2 hy

/-- **Uncapping the relation of the requests**: a capping `H` at least the cap value and
self-visible at the threshold changes no read. -/
theorem CorrectAt.of_min {s : Fin t'.card → Label.{u}} {j : Fin D.card} {ℓ H : Label.{u}}
    (h : Q.CorrectAt (fun x ↦ min (s x) H) j (min ℓ H)) (hH : s Q.cap ≤ H)
    (hvis : IsSelfVisible Q.threshold H)
    (hoff : j ∈ Q.exacts → Q.offset j ≤ Q.threshold) (hR : Q.markerOffset ≤ Q.threshold) :
    Q.CorrectAt s j ℓ := by
  have hc : min (s Q.cap) H = s Q.cap := min_eq_left hH
  have key (a : Label.{u}) : min (min a H) (s Q.cap) = min a (s Q.cap) := by
    rw [min_assoc, min_eq_right hH]
  obtain ⟨h1, h2, h3⟩ := h
  simp only [hc] at h1 h2 h3
  refine ⟨fun hz ↦ ?_, fun hf ↦ ?_, fun hy ↦ ?_⟩
  · rw [← key]; exact h1 hz
  · have := h2 hf
    rw [key, readExact, hc, visibilityReplace_min_of_isSelfVisible (hoff hf) hvis, key] at this
    rwa [readExact]
  · have := h3 hy
    rw [key, readMarker, hc, visibilityReplace_min_of_isSelfVisible hR hvis, key] at this
    rwa [readMarker]

end Class

/-! ### The relative lift on the exact class -/

variable {t' : StageType.{u} α k} {p : StageType.{u} α n} {e : Fin n ↪ Fin k}
  {d : StageType.{u} α (n + 1)}
  (hte : restrictFace e t' = some p) (hdp : restrictFace Fin.castSuccEmb d = some p)

/-- An **allowed pair on the exact class**: lawful sections of the context and of the donor,
equal on the root, admitted on the exact class. -/
def AllowedOnClass (Q : GrowthRequests t' d.toScheme) (u : Fin t'.card → Label.{u})
    (v : Fin d.card → Label.{u}) : Prop :=
  t'.rows.IsLawful u ∧ d.rows.IsLawful v ∧
    (∀ i, v (d.faceCell hdp i) = u (t'.faceCell hte i)) ∧ Q.AdmitsOnClass u v

/-- **The relative lift on the exact class.** -/
def HasRelativeLiftOnClass (Q : GrowthRequests t' d.toScheme) : Prop :=
  ∀ (u u' : Fin t'.card → Label.{u}) (v : Fin d.card → Label.{u}) (γ : Label.{u}),
    Q.AllowedOnClass hte hdp u v → t'.rows.IsLawful u' → IsSelfVisible Q.threshold γ →
    (∀ x, min (u' x) γ = min (u x) γ) →
    ∃ v' : Fin d.card → Label.{u}, Q.AllowedOnClass hte hdp u' v' ∧
      ∀ j, min (v' j) γ = min (v j) γ

/-- **The relative lift on the exact class from the relative lift**, for calibrated requests read
exactly at the labels of `t'` on a legal donor with a nonempty root.  Off the class (or at a cap
value `⊥`) the root lift suffices; on the class at a positive `γ` the old pair reads the requests
outright, so it is allowed; at `γ = ⊥` the labels of `t'` and `d` serve as the old pair. -/
theorem hasRelativeLiftOnClass_of_hasRelativeLift {Q : GrowthRequests t' d.toScheme}
    (hex : ∀ j ℓ, Q.CorrectAt t'.label j ℓ ↔ ℓ = d.label j) (hQ : Q.Calibrated hte)
    (hd : d.IsLegal) (hn : 0 < n) (hrel : Q.HasRelativeLift hte hdp) :
    Q.HasRelativeLiftOnClass hte hdp := by
  intro u u' v γ hall hu' hγ hag
  obtain ⟨hu, hv, hroot, hadm⟩ := hall
  by_cases hin : (∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      u' x = ⊥ ↔ t'.label x = ⊥) ∧ u' Q.cap ≠ ⊥
  swap
  · obtain ⟨v', hv', hv'r, hv'c⟩ := StageType.IsLegal.exists_rootLift hd hn hdp hv
      (isLawful_root hte hu') (hγ.mono hQ.arity) (fun i ↦ by rw [hroot i, hag])
    exact ⟨v', ⟨hu', hv', hv'r, fun h hc ↦ absurd ⟨h, hc⟩ hin⟩, hv'c⟩
  obtain ⟨hcls, hcb⟩ := hin
  by_cases hγb : γ = ⊥
  · -- the labels as the old pair
    have hlab : Q.Allowed hte hdp t'.label d.label :=
      ⟨t'.isLawful, d.isLawful, fun i ↦ by rw [StageType.label_faceCell, StageType.label_faceCell],
        fun _ _ j ↦ (hex j _).mpr rfl⟩
    obtain ⟨v', ⟨h1, h2, h3, h4⟩, -⟩ := hrel t'.label u' d.label ⊥ hlab hu'
      (isSelfVisible_bot _) (fun x ↦ by rw [min_bot_right, min_bot_right])
    exact ⟨v', ⟨h1, h2, h3, h4.admitsOnClass⟩, fun j ↦ by
      rw [hγb, min_bot_right, min_bot_right]⟩
  · -- the old pair reads the requests outright
    have hcls' : ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
        u x = ⊥ ↔ t'.label x = ⊥ := fun x hx ↦
      (eq_bot_iff_of_min_eq (hag x) hγb).symm.trans (hcls x hx)
    have hcb' : u Q.cap ≠ ⊥ := fun h0 ↦ hcb ((eq_bot_iff_of_min_eq (hag Q.cap) hγb).mpr h0)
    have hcor := hadm hcls' hcb'
    obtain ⟨v', ⟨h1, h2, h3, h4⟩, hv'c⟩ :=
      hrel u u' v γ ⟨hu, hv, hroot, fun _ _ ↦ hcor⟩ hu' hγ hag
    exact ⟨v', ⟨h1, h2, h3, h4.admitsOnClass⟩, hv'c⟩

end GrowthRequests

end StageType

/-! ### Recovery by recognition -/

namespace GrowthCarrier

variable {α : Ordinal.{u}} {J n : ℕ} {t' : StageType.{u} α J} {D : Scheme.{u} (n + 1)}
  {e : Fin n ↪ Fin J} (G : GrowthCarrier t'.toScheme D e) (Q : StageType.GrowthRequests t' D)

/-- **Recognition** at a growth carrier: every lawful section `v` of the carrier, capped at some
`H` at least its cap value and self-visible at the threshold, is the image of a state `(s, w)`
admitted on the exact class under a monotone map `θ` fixing `⊥`, commuting with visibility
replacement at the threshold, and reflecting `⊥` on the values of `s` below the cap: at the
context cells below the cap and at the donor cells. -/
def Recognizes : Prop :=
  ∀ v : Fin G.scheme.card → Label.{u}, G.scheme.rows.IsLawful v →
    ∃ (s : Fin t'.card → Label.{u}) (w : Fin D.card → Label.{u}) (θ : Label.{u} → Label.{u})
      (H : Label.{u}), Q.AdmitsOnClass s w ∧ Monotone θ ∧ θ ⊥ = ⊥ ∧
      (∀ i ≤ Q.threshold, ∀ x, θ (visibilityReplace Q.threshold i x) =
        visibilityReplace Q.threshold i (θ x)) ∧
      IsSelfVisible Q.threshold H ∧ v (G.contextCell Q.cap) ≤ H ∧
      (∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
        θ (s x) = ⊥ → s x = ⊥) ∧
      (∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
        θ (s x) = min (v (G.contextCell x)) H) ∧
      ∀ j, θ (w j) = min (v (G.donorCell j)) H

/-- **Recovery by recognition**: a recognizing carrier recovers the relation of the requests from
every context section `σ` with exactly the bottom pattern of `t'` below the cap and a cap value
other than `⊥`.  The recognized state carries the bottom pattern of `σ` (reflection of `⊥`), so it
reads the requests; the map carries the reads to `σ` capped at `H`, and the capping at `H`, at
least the cap value, changes no read.  The references and the marker lie below the cap. -/
theorem recovers_of_recognizes (hrec : G.Recognizes Q)
    (href : ∀ j ∈ Q.exacts, Q.ref j ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) ∧
      Q.offset j ≤ Q.threshold)
    (hmk : Q.marker ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) ∧
      Q.markerOffset ≤ Q.threshold)
    {σ : Fin t'.card → Label.{u}}
    (hclass : ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      σ x = ⊥ ↔ t'.label x = ⊥)
    (hcap : σ Q.cap ≠ ⊥) : G.Recovers σ (Q.CorrectAt σ) := by
  intro v hv hctx i j hij
  have hvσ (x : Fin t'.card) : v (G.contextCell x) = σ x := hctx _ x rfl
  have hdj : G.scheme.cellMap (extendByLast e) i = G.donorCell j :=
    congrArg (G.scheme.cellMap (extendByLast e)) (Fin.ext hij)
  rw [hdj]
  obtain ⟨s, w, θ, H, hadm, hθm, hθb, hθv, hHv, hHc, hrefl, hs, hw⟩ := hrec v hv
  rw [hvσ] at hHc
  have hHb : H ≠ ⊥ := fun h0 ↦ hcap (le_bot_iff.mp (h0 ▸ hHc))
  have hcb : Q.cap ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) :=
    CellScheme.mem_below_gradedIndex _ _
  -- the bottom pattern passes to the state
  have hbot (x : Fin t'.card) (hx : x ∈ t'.toCellScheme.below
      (t'.toCellScheme.gradedIndex Q.cap)) : s x = ⊥ ↔ σ x = ⊥ := by
    rw [← hvσ]
    constructor
    · intro h0
      have h1 := hs x hx
      rw [h0, hθb] at h1
      rcases min_eq_bot.mp h1.symm with h | h
      · exact h
      · exact absurd h hHb
    · intro h0
      refine hrefl x hx ?_
      rw [hs x hx, h0, min_eq_left bot_le]
  have hcor := hadm (fun x hx ↦ (hbot x hx).trans (hclass x hx))
    (fun h0 ↦ hcap ((hbot _ hcb).mp h0)) j
  have h1 := hcor.map hθm hθb hθv (fun hf ↦ (href j hf).2) hmk.2
  rw [hw j] at h1
  have h2 : Q.CorrectAt (fun x ↦ min (σ x) H) j (min (v (G.donorCell j)) H) :=
    h1.congr (by simp only [Function.comp_apply]; rw [hs _ hcb, hvσ])
      (fun hf ↦ by simp only [Function.comp_apply]; rw [hs _ (href j hf).1, hvσ])
      (by simp only [Function.comp_apply]; rw [hs _ hmk.1, hvσ])
  exact h2.of_min hHc hHv (fun hf ↦ (href j hf).2) hmk.2

/-- **Every face of a recognizing carrier has completions admitted on the exact class in every
capped ball**: legality of the carrier (`Scheme.IsLegal.exists_isLawful_extend`) and recovery by
recognition.  At the second coatom (`GrowthCarrier.exists_donorCoatom`) this is the donor-side
lift that a recognizing carrier provides. -/
theorem exists_admitsOnClass_extend (hrec : G.Recognizes Q)
    (href : ∀ j ∈ Q.exacts, Q.ref j ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) ∧
      Q.offset j ≤ Q.threshold)
    (hmk : Q.marker ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) ∧
      Q.markerOffset ≤ Q.threshold)
    {m : ℕ} {f : Fin m ↪ Fin (J + 1)} (hf : univ.map f ∈ G.scheme.toCellScheme.faces)
    {c : Label.{u}} (hc : IsSelfVisible (J + 1) c)
    {ℓ : Fin (G.scheme.comap f).card → Label.{u}} (hℓ : (G.scheme.comap f).rows.IsLawful ℓ)
    {P : Fin G.scheme.card → Label.{u}} (hP : G.scheme.rows.IsLawful P)
    (hPℓ : ∀ i, min (P (G.scheme.cellMap f i)) c = min (ℓ i) c) :
    ∃ r : Fin G.scheme.card → Label.{u}, G.scheme.rows.IsLawful r ∧
      (∀ z, min (r z) c = min (P z) c) ∧ (∀ i, r (G.scheme.cellMap f i) = ℓ i) ∧
      Q.AdmitsOnClass (fun x ↦ r (G.contextCell x)) (fun j ↦ r (G.donorCell j)) := by
  obtain ⟨r, hr, hrc, hrℓ⟩ := G.isLegal.exists_isLawful_extend hf hc hℓ hP hPℓ
  exact ⟨r, hr, hrc, hrℓ, fun hcls hcap j ↦
    (G.recovers_of_recognizes Q hrec href hmk hcls hcap).apply G hr (fun _ ↦ rfl) j⟩

end GrowthCarrier

end VaughtConjecture
