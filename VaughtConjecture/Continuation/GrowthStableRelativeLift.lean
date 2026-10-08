/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthRecognition

/-!
# The relative lift on the exact class at requests calibrated on the class

Roadmap, Layer 3 ((R4), the stable evaluation of the growth carrier).

Calibrated requests (`StageType.GrowthRequests.Calibrated`) ask the cap row to be clean on the
root: a root cell labelled `⊥` in the context is read as `⊥` by the cap's row.  At the actual
context of (R3) this is part of the calibration; at the stable context of (R4) it fails in general
(the cap's row may code a cell labelled `⊥` by a value that the reading witness suppresses).  On
the **exact class** (sections with exactly the bottom pattern of the context below the cap) the
clause is not needed: a root cell labelled `⊥` is read as `⊥` by every section of the class, and
the cleaned cap row is `⊥` there by definition.

* `StageType.GrowthRequests.ClassCalibrated`: the fields of `Calibrated` with the root clause
  reduced to the grade bound.  Calibrated requests are calibrated on the class
  (`StageType.GrowthRequests.Calibrated.classCalibrated`).
* `StageType.GrowthRequests.ClassCalibrated.hasRelativeLiftOnClass`: requests calibrated on the
  class with a template (`StageType.GrowthRequests.HasTemplate`) have the relative lift on the
  exact class, for a legal donor with a nonempty root.  The four cases are those of
  `StageType.GrowthRequests.hasRelativeLift_of_template`; outside the class and at a cap value at
  most `γ` they are the cases already compiled, and the frame and the template image are re-proved
  here with the class in place of the root clause.

No relation between the requests and the labels of the context is used: the old pair of the lift
reads the requests outright whenever `γ ≠ ⊥`, since it lies in the class with the new section.

## References

The relative lift is the growth step of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

namespace GrowthRequests

variable {t' : StageType.{u} α k} {p : StageType.{u} α n} {e : Fin n ↪ Fin k}
  {d : StageType.{u} α (n + 1)}
  (hte : restrictFace e t' = some p) (hdp : restrictFace Fin.castSuccEmb d = some p)

/-- **Requests calibrated on the exact class**: every donor cell is a request; the cap has full
scope and a label other than `⊥`; the references and the marker are labelled other than `⊥` and,
with their offsets, lie at most at the threshold; the root cells have grade at most the threshold;
and the threshold is at least the arity `n + 1` of the donor.  This is `Calibrated` without the
cleanness of the cap row on the root. -/
structure ClassCalibrated (Q : GrowthRequests t' d.toScheme) : Prop where
  /-- Every donor cell is a bottom, an exact or a high request. -/
  cover : ∀ j, j ∈ Q.bottoms ∨ j ∈ Q.exacts ∨ j ∈ Q.highs
  /-- The cap has full scope. -/
  scope_cap : t'.toCellScheme.scope Q.cap = univ
  /-- The cap is not labelled `⊥`. -/
  label_cap : t'.label Q.cap ≠ ⊥
  /-- The references: grade and offset at most the threshold, label other than `⊥`. -/
  ref : ∀ j ∈ Q.exacts, t'.toCellScheme.grade (Q.ref j) ≤ Q.threshold ∧
    Q.offset j ≤ Q.threshold ∧ t'.label (Q.ref j) ≠ ⊥
  /-- The marker: grade and offset at most the threshold, label other than `⊥`. -/
  marker : t'.toCellScheme.grade Q.marker ≤ Q.threshold ∧ Q.markerOffset ≤ Q.threshold ∧
    t'.label Q.marker ≠ ⊥
  /-- The root cells lie below the cap. -/
  root : ∀ i, t'.toCellScheme.grade (t'.faceCell hte i) ≤ Q.threshold
  /-- The threshold is at least the arity of the donor. -/
  arity : n + 1 ≤ Q.threshold

/-- Calibrated requests are calibrated on the class. -/
theorem Calibrated.classCalibrated {Q : GrowthRequests t' d.toScheme} (hQ : Q.Calibrated hte) :
    Q.ClassCalibrated hte :=
  ⟨hQ.cover, hQ.scope_cap, hQ.label_cap, hQ.ref, hQ.marker, fun i ↦ (hQ.root i).1, hQ.arity⟩

/-- **The decoder on the cleaned cap row, on the exact class**: for a section `u'` with exactly
the bottom pattern of the context below the cap and a map `θ` fixing `⊥` and sending the cap row
at the cells of grade at most the threshold to `u'` capped at its cap value, `θ` sends the cleaned
cap row at the cap, the references, the marker and the root cells to `u'` capped at its cap value.
At a root cell labelled `⊥` both sides are `⊥`. -/
theorem ClassCalibrated.decoder_cleanedCapRow {Q : GrowthRequests t' d.toScheme}
    (hQ : Q.ClassCalibrated hte) {u' : Fin t'.card → Label.{u}} {θ : Label.{u} → Label.{u}}
    (hθb : θ ⊥ = ⊥)
    (hθr : ∀ x, t'.toCellScheme.grade x ≤ Q.threshold →
      θ (t'.rowAt Q.cap x) = min (u' x) (u' Q.cap))
    (hcls : ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      u' x = ⊥ ↔ t'.label x = ⊥) :
    θ (Q.cleanedCapRow Q.cap) = u' Q.cap ∧
      (∀ j ∈ Q.exacts, θ (Q.cleanedCapRow (Q.ref j)) = min (u' (Q.ref j)) (u' Q.cap)) ∧
      θ (Q.cleanedCapRow Q.marker) = min (u' Q.marker) (u' Q.cap) ∧
      ∀ i, θ (Q.cleanedCapRow (t'.faceCell hte i)) =
        min (u' (t'.faceCell hte i)) (u' Q.cap) := by
  refine ⟨?_, fun j hj ↦ ?_, ?_, fun i ↦ ?_⟩
  · rw [Q.cleanedCapRow_of_ne_bot hQ.label_cap, hθr _ le_rfl, min_self]
  · rw [Q.cleanedCapRow_of_ne_bot (hQ.ref j hj).2.2, hθr _ (hQ.ref j hj).1]
  · rw [Q.cleanedCapRow_of_ne_bot hQ.marker.2.2, hθr _ hQ.marker.1]
  · by_cases hb : t'.label (t'.faceCell hte i) = ⊥
    · have hu : u' (t'.faceCell hte i) = ⊥ :=
        (hcls _ (Q.mem_below_cap hQ.scope_cap (hQ.root i))).mpr hb
      rw [hu, min_eq_left bot_le]
      simp only [cleanedCapRow, hb, ite_true, hθb]
    · rw [Q.cleanedCapRow_of_ne_bot hb, hθr _ (hQ.root i)]

/-- **The relative lift by the template image on the exact class** (case 3): as
`StageType.GrowthRequests.Allowed.exists_lift_of_template`, for requests calibrated on the class
and a new section `u'` with exactly the bottom pattern of the context below the cap; the old pair
need only be admitted on the class. -/
theorem ClassCalibrated.exists_lift_of_template {Q : GrowthRequests t' d.toScheme}
    (hQ : Q.ClassCalibrated hte) (hT : Q.HasTemplate hte hdp) (hd : d.IsLegal) (hn : 0 < n)
    {u u' : Fin t'.card → Label.{u}} {v : Fin d.card → Label.{u}}
    (hadm : Q.AdmitsOnClass u v) (hu' : t'.rows.IsLawful u') {γ : Label.{u}}
    (hγ : IsSelfVisible Q.threshold γ) (hag : ∀ x, min (u' x) γ = min (u x) γ)
    (hcls : ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      u' x = ⊥ ↔ t'.label x = ⊥)
    (hlt : γ < u' Q.cap) (hmk : Q.highs.Nonempty → γ ≤ Q.readMarker u') :
    ∃ v' : Fin d.card → Label.{u}, Q.AllowedOnClass hte hdp u' v' ∧
      ∀ j, min (v' j) γ = min (v j) γ := by
  obtain ⟨V, hV, hVr, hVc, -, hVz⟩ := hT
  obtain ⟨θ, hW, hθv, hθr⟩ := Q.exists_capDecoder hu' hQ.scope_cap
  obtain ⟨hθc, hθref, hθmk, hθroot⟩ := hQ.decoder_cleanedCapRow hte hW.map_bot hθr hcls
  set c' := u' Q.cap with hc'
  have hc'b : c' ≠ ⊥ := ne_bot_of_gt hlt
  have hvis' : IsSelfVisible Q.threshold c' := hu'.orderly Q.cap
  -- the template image reads the requests from `u'`
  have hwc (j : Fin d.card) : Q.CorrectAt u' j (θ (V j)) :=
    Q.correctAt_map (hVc j) hW.monotone hW.map_bot hθv hθc (hθref j) hθmk hvis'
      (fun hf ↦ (hQ.ref j hf).2.1) hQ.marker.2.1
  -- the reads of `u'` are not `⊥`
  have hrefb (j : Fin d.card) (hj : j ∈ Q.exacts) : Q.readExact u' j ≠ ⊥ := by
    intro h0
    rcases min_eq_bot.mp h0 with h | h
    · exact (hQ.ref j hj).2.2 ((hcls _ (Q.mem_below_cap hQ.scope_cap (hQ.ref j hj).1)).mp
        (visibilityReplace_eq_bot_iff.mp h))
    · exact hc'b h
  have hmkb : Q.readMarker u' ≠ ⊥ := by
    intro h0
    rcases min_eq_bot.mp h0 with h | h
    · exact hQ.marker.2.2 ((hcls _ (Q.mem_below_cap hQ.scope_cap hQ.marker.1)).mp
        (visibilityReplace_eq_bot_iff.mp h))
    · exact hc'b h
  -- the template image has the bottom pattern of the template
  have hpat (j : Fin d.card) : θ (V j) = ⊥ ↔ V j = ⊥ := by
    by_cases hz : j ∈ Q.bottoms
    · rw [hVz j hz, hW.map_bot]
    refine ⟨fun h0 ↦ ?_, fun h ↦ by rw [h, hW.map_bot]⟩
    rcases (hQ.cover j).resolve_left hz with hf | hy
    · have h1 := (hwc j).2.1 hf
      rw [h0, min_eq_left bot_le] at h1
      exact absurd h1.symm (hrefb j hf)
    · have h1 := (hwc j).2.2 hy
      rw [h0, min_eq_left bot_le, le_bot_iff] at h1
      exact absurd h1 hmkb
  have hw : d.rows.IsLawful (θ ∘ V) := templateImage_isLawful hV hQ.arity hW hpat
  -- the root lift at `c'`
  obtain ⟨v', hv', hv'r, hv'c⟩ := StageType.IsLegal.exists_rootLift hd hn hdp hw
    (isLawful_root hte hu') (hvis'.mono hQ.arity)
    (fun i ↦ by rw [Function.comp_apply, hVr i, hθroot i, min_assoc, min_self])
  have hv'cor (j : Fin d.card) : Q.CorrectAt u' j (v' j) := correctAt_of_min_eq (hwc j) (hv'c j)
  refine ⟨v', ⟨hu', hv', hv'r, fun _ _ ↦ hv'cor⟩, fun j ↦ ?_⟩
  -- the `γ`-reading
  by_cases hγb : γ = ⊥
  · rw [hγb, min_bot_right, min_bot_right]
  have hγc : γ ≤ u Q.cap := by
    have h1 := hag Q.cap
    rw [← hc', min_eq_right hlt.le] at h1
    exact min_eq_right_iff.mp h1.symm
  have hA := hadm (fun x hx ↦ (eq_bot_iff_of_min_eq (hag x) hγb).symm.trans (hcls x hx))
    (fun h0 ↦ hγb (le_bot_iff.mp (h0 ▸ hγc))) j
  rw [min_eq_min_of_le (hv'c j) hlt.le]
  refine min_eq_min_of_correctAt (hwc j) hA hγ hag hlt.le hγc (hQ.cover j)
    (fun hf ↦ (hQ.ref j hf).2.1) fun hy ↦ ?_
  have hm := hmk ⟨j, hy⟩
  refine ⟨hm, ?_⟩
  have h1 := min_readMarker_eq hγ hag hlt.le hγc hQ.marker.2.1
  rw [min_eq_right hm] at h1
  exact min_eq_right_iff.mp h1.symm

/-- **The relative lift in the frame on the exact class** (case 2): as
`StageType.GrowthRequests.Allowed.exists_lift_of_frame`, for requests calibrated on the class, a
new section `u'` with exactly the bottom pattern of the context below the cap, and an old pair
admitted on the class. -/
theorem ClassCalibrated.exists_lift_of_frame {Q : GrowthRequests t' d.toScheme}
    (hQ : Q.ClassCalibrated hte) (hT : Q.HasTemplate hte hdp) (hd : d.IsLegal) (hn : 0 < n)
    {u u' : Fin t'.card → Label.{u}} {v : Fin d.card → Label.{u}}
    (hall : Q.AllowedOnClass hte hdp u v) (hu' : t'.rows.IsLawful u') {γ : Label.{u}}
    (hγ : IsSelfVisible Q.threshold γ) (hag : ∀ x, min (u' x) γ = min (u x) γ)
    (hcls : ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      u' x = ⊥ ↔ t'.label x = ⊥)
    (hlt : γ < u' Q.cap) (hne : Q.highs.Nonempty) (hmk : Q.readMarker u' < γ) :
    ∃ v' : Fin d.card → Label.{u}, Q.AllowedOnClass hte hdp u' v' ∧
      ∀ j, min (v' j) γ = min (v j) γ := by
  obtain ⟨-, hv, hroot, hadm⟩ := hall
  obtain ⟨-, -, -, -, hVf, -⟩ := hT
  obtain ⟨θ, hW, hθv, hθr⟩ := Q.exists_capDecoder hu' hQ.scope_cap
  obtain ⟨hθc, hθref, hθmk, -⟩ := hQ.decoder_cleanedCapRow hte hW.map_bot hθr hcls
  have hvis' : IsSelfVisible Q.threshold (u' Q.cap) := hu'.orderly Q.cap
  have hγb : γ ≠ ⊥ := ne_bot_of_gt hmk
  -- the frame at `u'`
  have hframe (j : Fin d.card) (hj : j ∈ Q.exacts) : Q.readExact u' j < γ := by
    have h1 := hW.monotone (hVf hne j hj)
    rw [map_readExact hW.monotone hθv hθc (hθref j hj) hvis' (hQ.ref j hj).2.1,
      map_readMarker hW.monotone hθv hθc hθmk hvis' hQ.marker.2.1] at h1
    exact h1.trans_lt hmk
  -- `u` is in the class, with cap value at least `γ`
  have hγc : γ ≤ u Q.cap := by
    have h1 := hag Q.cap
    rw [min_eq_right hlt.le] at h1
    exact min_eq_right_iff.mp h1.symm
  have hA := hadm (fun x hx ↦ (eq_bot_iff_of_min_eq (hag x) hγb).symm.trans (hcls x hx))
    (fun h0 ↦ hγb (le_bot_iff.mp (h0 ▸ hγc)))
  -- the root lift of `v` at `γ`
  obtain ⟨v', hv', hv'r, hv'c⟩ := StageType.IsLegal.exists_rootLift hd hn hdp hv
    (isLawful_root hte hu') (hγ.mono hQ.arity) (fun i ↦ by rw [hroot i, hag])
  refine ⟨v', ⟨hu', hv', hv'r, fun _ _ j ↦ ⟨fun hz ↦ ?_, fun hf ↦ ?_, fun hy ↦ ?_⟩⟩, hv'c⟩
  · -- a bottom request: `v` is `⊥` capped at `γ`, hence so is `v'`
    have h1 : min (v j) γ = ⊥ := by rw [← min_min_cap hγc, (hA j).1 hz, min_eq_left bot_le]
    rw [← hv'c j] at h1
    rcases min_eq_bot.mp h1 with h | h
    · rw [h, min_eq_left bot_le]
    · exact absurd h hγb
  · -- an exact request: the reads at `u` and `u'` are equal and below `γ`
    have ha := hframe j hf
    have h1 := min_readExact_eq hγ hag hlt.le hγc (hQ.ref j hf).2.1 (j := j)
    rw [min_eq_left ha.le] at h1
    have hu : Q.readExact u j = Q.readExact u' j := eq_of_min_eq_of_lt h1.symm ha
    have hvj : v j = Q.readExact u' j := eq_of_correctAt (hA j) hf hu (ha.trans_le hγc)
    have hv'j : v' j = Q.readExact u' j :=
      eq_of_min_eq_of_lt ((hv'c j).trans (by rw [hvj, min_eq_left ha.le])) ha
    rw [hv'j, min_eq_left (ha.trans hlt).le]
  · -- a high request: the marker reads at `u` and `u'` are equal and below `γ`
    have h1 := min_readMarker_eq hγ hag hlt.le hγc hQ.marker.2.1
    rw [min_eq_left hmk.le] at h1
    have hu : Q.readMarker u = Q.readMarker u' := eq_of_min_eq_of_lt h1.symm hmk
    have hb : Q.readMarker u' ≤ v j := by
      rw [← hu]
      exact ((hA j).2.2 hy).trans (min_le_left _ _)
    have hb' : Q.readMarker u' ≤ v' j := by
      have h2 : Q.readMarker u' ≤ min (v j) γ := le_min hb hmk.le
      rw [← hv'c j] at h2
      exact h2.trans (min_le_left _ _)
    exact le_min hb' (hmk.trans hlt).le

/-- **The relative lift on the exact class from a template**, for requests calibrated on the
class on a legal donor with a nonempty root.  Outside the class (or at a cap value `⊥`) the root
lift suffices and admission is vacuous; at a cap value at most `γ` the old pair, in the class with
the new section, reads the requests outright and
`StageType.GrowthRequests.Allowed.exists_lift_of_cap_le` applies; above `γ` the frame
(`StageType.GrowthRequests.ClassCalibrated.exists_lift_of_frame`) or the template image
(`StageType.GrowthRequests.ClassCalibrated.exists_lift_of_template`). -/
theorem ClassCalibrated.hasRelativeLiftOnClass {Q : GrowthRequests t' d.toScheme}
    (hQ : Q.ClassCalibrated hte) (hT : Q.HasTemplate hte hdp) (hd : d.IsLegal) (hn : 0 < n) :
    Q.HasRelativeLiftOnClass hte hdp := by
  intro u u' v γ hall hu' hγ hag
  obtain ⟨hu, hv, hroot, hadm⟩ := hall
  have hγ1 : IsSelfVisible (n + 1) γ := hγ.mono hQ.arity
  by_cases hin : (∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      u' x = ⊥ ↔ t'.label x = ⊥) ∧ u' Q.cap ≠ ⊥
  swap
  · obtain ⟨v', hv', hv'r, hv'c⟩ := StageType.IsLegal.exists_rootLift hd hn hdp hv
      (isLawful_root hte hu') hγ1 (fun i ↦ by rw [hroot i, hag])
    exact ⟨v', ⟨hu', hv', hv'r, fun h hc ↦ absurd ⟨h, hc⟩ hin⟩, hv'c⟩
  obtain ⟨hcls, hcb⟩ := hin
  rcases le_or_gt (u' Q.cap) γ with hle | hlt
  · have hγb : γ ≠ ⊥ := fun h ↦ hcb (le_bot_iff.mp (h ▸ hle))
    have hcor := hadm (fun x hx ↦ (eq_bot_iff_of_min_eq (hag x) hγb).symm.trans (hcls x hx))
      (fun h0 ↦ hcb ((eq_bot_iff_of_min_eq (hag Q.cap) hγb).mpr h0))
    obtain ⟨v', ⟨h1, h2, h3, h4⟩, hv'c⟩ := Allowed.exists_lift_of_cap_le hte hdp Q hd hn
      ⟨hu, hv, hroot, fun _ _ ↦ hcor⟩ hu' hγ1 hγb hag hle (fun j hj ↦ (hQ.ref j hj).2.1)
      hQ.marker.2.1
    exact ⟨v', ⟨h1, h2, h3, h4.admitsOnClass⟩, hv'c⟩
  by_cases h2 : Q.highs.Nonempty ∧ Q.readMarker u' < γ
  · exact hQ.exists_lift_of_frame hte hdp hT hd hn ⟨hu, hv, hroot, hadm⟩ hu' hγ hag hcls hlt
      h2.1 h2.2
  · exact hQ.exists_lift_of_template hte hdp hT hd hn hadm hu' hγ hag hcls hlt
      fun hne ↦ not_lt.mp fun h ↦ h2 ⟨hne, h⟩

end GrowthRequests

end StageType

end VaughtConjecture
