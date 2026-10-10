/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthRelativeLift

/-!
# The relative lift on the donor from a template

Roadmap, Layer 3 ((R3) and (R4), the controllers of the growth construction for the small donor).

From calibrated requests (`StageType.GrowthRequests.Calibrated`) with a template
(`StageType.GrowthRequests.HasTemplate`), a legal donor with a nonempty root has the relative lift
(`StageType.GrowthRequests.hasRelativeLift_of_template`).  Given an allowed pair `(u, v)` and a
lawful context section `u'` agreeing with `u` capped at `γ`, write `c'` for the cap value of `u'`.

* **Case 0** (`u'` outside the bottom class of the context, or `c' = ⊥`) and **case 1**
  (`c' ≤ γ`) are `StageType.GrowthRequests.Allowed.exists_lift_of_not_class` and
  `StageType.GrowthRequests.Allowed.exists_lift_of_cap_le`.
* **Case 2** (`γ < c'`, high requests, marker read of `u'` below `γ`,
  `StageType.GrowthRequests.Allowed.exists_lift_of_frame`): the frame inequalities of the template,
  carried to `u'` by the capped decoder of `u'` at the cap, put every exact read of `u'` below `γ`;
  the root lift of `v` at `γ` then reads every request correctly.
* **Case 3** (`γ < c'`, marker read of `u'` at least `γ` or no high requests,
  `StageType.GrowthRequests.Allowed.exists_lift_of_template`): the **template image** `θ ∘ V`,
  for the capped decoder `θ` of `u'`, is lawful (it has the bottom pattern of `V`: a request other
  than a bottom request is read from a value of `u'` other than `⊥`), reads the requests from `u'`,
  and is `u'` capped at `c'` on the root (the cap row is clean there); the root lift at `c'` makes
  the root literal.  Below `γ` it agrees with `v`, since both read the same requests from sections
  agreeing capped at `γ` (`StageType.GrowthRequests.min_eq_min_of_correctAt`).

## References

The relative lift is the growth step of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

namespace GrowthRequests

section Reads

variable {t' : StageType.{u} α k} {D : Scheme.{u} (n + 1)} {Q : GrowthRequests t' D}

/-- The relation of the requests at `s` depends on a label only through its value capped at the
cap value of `s`. -/
theorem correctAt_of_min_eq {s : Fin t'.card → Label.{u}} {j : Fin D.card} {ℓ ℓ' : Label.{u}}
    (h : Q.CorrectAt s j ℓ) (hm : min ℓ' (s Q.cap) = min ℓ (s Q.cap)) : Q.CorrectAt s j ℓ' :=
  ⟨fun hz ↦ hm.trans (h.1 hz), fun hf ↦ hm.trans (h.2.1 hf), fun hy ↦ hm ▸ h.2.2 hy⟩

/-- A label whose value capped at `γ` is some `a < γ` is `a`. -/
theorem eq_of_min_eq_of_lt {x a γ : Label.{u}} (h : min x γ = a) (ha : a < γ) : x = a := by
  rcases le_total x γ with hle | hle
  · rwa [min_eq_left hle] at h
  · rw [min_eq_right hle] at h
    exact absurd h ha.ne'

/-- Two sections agreeing capped at `γ > ⊥` have the same cells read as `⊥`. -/
theorem eq_bot_iff_of_min_eq {x y γ : Label.{u}} (h : min x γ = min y γ) (hγ : γ ≠ ⊥) :
    x = ⊥ ↔ y = ⊥ := by
  constructor
  · intro hx
    rw [hx, min_eq_left bot_le] at h
    rcases min_eq_bot.mp h.symm with h' | h'
    · exact h'
    · exact absurd h' hγ
  · intro hy
    rw [hy, min_eq_left bot_le] at h
    rcases min_eq_bot.mp h with h' | h'
    · exact h'
    · exact absurd h' hγ

/-- Capping at a label `γ` below the cap value forgets the cap. -/
theorem min_min_cap {s : Fin t'.card → Label.{u}} {x γ : Label.{u}} (hγ : γ ≤ s Q.cap) :
    min (min x (s Q.cap)) γ = min x γ := by
  rw [min_assoc, min_eq_right hγ]

/-- **The exact reads capped at `γ`**: for two sections agreeing capped at `γ`, self-visible at
the threshold and at most both cap values, the exact reads agree capped at `γ`. -/
theorem min_readExact_eq {s s' : Fin t'.card → Label.{u}} {γ : Label.{u}}
    (hvis : IsSelfVisible Q.threshold γ) (hs : ∀ x, min (s x) γ = min (s' x) γ)
    (hγ : γ ≤ s Q.cap) (hγ' : γ ≤ s' Q.cap) {j : Fin D.card} (hoff : Q.offset j ≤ Q.threshold) :
    min (Q.readExact s j) γ = min (Q.readExact s' j) γ := by
  rw [readExact, readExact, min_min_cap hγ, min_min_cap hγ',
    ← visibilityReplace_min_of_isSelfVisible hoff hvis, hs,
    visibilityReplace_min_of_isSelfVisible hoff hvis]

/-- **The marker reads capped at `γ`**, as `StageType.GrowthRequests.min_readExact_eq`. -/
theorem min_readMarker_eq {s s' : Fin t'.card → Label.{u}} {γ : Label.{u}}
    (hvis : IsSelfVisible Q.threshold γ) (hs : ∀ x, min (s x) γ = min (s' x) γ)
    (hγ : γ ≤ s Q.cap) (hγ' : γ ≤ s' Q.cap) (hR : Q.markerOffset ≤ Q.threshold) :
    min (Q.readMarker s) γ = min (Q.readMarker s') γ := by
  rw [readMarker, readMarker, min_min_cap hγ, min_min_cap hγ',
    ← visibilityReplace_min_of_isSelfVisible hR hvis, hs,
    visibilityReplace_min_of_isSelfVisible hR hvis]

/-- **The `γ`-reading**: labels reading a request from two sections agreeing capped at `γ`
(self-visible at the threshold, at most both cap values) agree capped at `γ`, if a high request's
marker reads are at least `γ`. -/
theorem min_eq_min_of_correctAt {s s' : Fin t'.card → Label.{u}} {j : Fin D.card}
    {ℓ ℓ' : Label.{u}} (h : Q.CorrectAt s j ℓ) (h' : Q.CorrectAt s' j ℓ') {γ : Label.{u}}
    (hvis : IsSelfVisible Q.threshold γ) (hs : ∀ x, min (s x) γ = min (s' x) γ)
    (hγ : γ ≤ s Q.cap) (hγ' : γ ≤ s' Q.cap)
    (hcov : j ∈ Q.bottoms ∨ j ∈ Q.exacts ∨ j ∈ Q.highs)
    (hoff : j ∈ Q.exacts → Q.offset j ≤ Q.threshold)
    (hmk : j ∈ Q.highs → γ ≤ Q.readMarker s ∧ γ ≤ Q.readMarker s') : min ℓ γ = min ℓ' γ := by
  rcases hcov with hz | hf | hy
  · rw [← min_min_cap (x := ℓ) hγ, h.1 hz, ← min_min_cap (x := ℓ') hγ', h'.1 hz]
  · rw [← min_min_cap (x := ℓ) hγ, h.2.1 hf, ← min_min_cap (x := ℓ') hγ', h'.2.1 hf]
    exact min_readExact_eq hvis hs hγ hγ' (hoff hf)
  · rw [min_eq_right ((hmk hy).1.trans ((h.2.2 hy).trans (min_le_left _ _))),
      min_eq_right ((hmk hy).2.trans ((h'.2.2 hy).trans (min_le_left _ _)))]

/-- **The decoder carries the exact reads**: a monotone map commuting with visibility replacement
at the threshold, sending the cap value of `e` to that of `s` and the reference value to the
reference value of `s` capped, sends the exact read of `e` to that of `s`. -/
theorem map_readExact {e s : Fin t'.card → Label.{u}} {θ : Label.{u} → Label.{u}}
    (hθ : Monotone θ) (hθv : ∀ i ≤ Q.threshold, ∀ x, θ (visibilityReplace Q.threshold i x) =
      visibilityReplace Q.threshold i (θ x))
    (hcap : θ (e Q.cap) = s Q.cap) {j : Fin D.card}
    (href : θ (e (Q.ref j)) = min (s (Q.ref j)) (s Q.cap))
    (hvis : IsSelfVisible Q.threshold (s Q.cap)) (hoff : Q.offset j ≤ Q.threshold) :
    θ (Q.readExact e j) = Q.readExact s j := by
  rw [readExact, hθ.map_min, hθv _ hoff, href, hcap,
    visibilityReplace_min_of_isSelfVisible hoff hvis, min_assoc, min_self]
  rfl

/-- **The decoder carries the marker read**, as `StageType.GrowthRequests.map_readExact`. -/
theorem map_readMarker {e s : Fin t'.card → Label.{u}} {θ : Label.{u} → Label.{u}}
    (hθ : Monotone θ) (hθv : ∀ i ≤ Q.threshold, ∀ x, θ (visibilityReplace Q.threshold i x) =
      visibilityReplace Q.threshold i (θ x))
    (hcap : θ (e Q.cap) = s Q.cap) (hmk : θ (e Q.marker) = min (s Q.marker) (s Q.cap))
    (hvis : IsSelfVisible Q.threshold (s Q.cap)) (hR : Q.markerOffset ≤ Q.threshold) :
    θ (Q.readMarker e) = Q.readMarker s := by
  rw [readMarker, hθ.map_min, hθv _ hR, hmk, hcap,
    visibilityReplace_min_of_isSelfVisible hR hvis, min_assoc, min_self]
  rfl

/-- **The capped decoder at the cap**: for a lawful context section `u'` and a cap of full scope,
a witness bounded by the threshold, commuting with visibility replacement at the threshold, that
sends the cap row at every cell of grade at most the threshold to `u'` capped at its cap value
(`Scheme.exists_cappedDecoder`). -/
theorem exists_capDecoder (Q : GrowthRequests t' D) {u' : Fin t'.card → Label.{u}}
    (hu' : t'.rows.IsLawful u') (hscope : t'.toCellScheme.scope Q.cap = univ) :
    ∃ θ : Label.{u} → Label.{u}, IsWitness (stepSuppressor Q.threshold) θ ∧
      (∀ i ≤ Q.threshold, ∀ x, θ (visibilityReplace Q.threshold i x) =
        visibilityReplace Q.threshold i (θ x)) ∧
      ∀ x, t'.toCellScheme.grade x ≤ Q.threshold →
        θ (t'.rowAt Q.cap x) = min (u' x) (u' Q.cap) := by
  obtain ⟨θ, hθm, hθb, -, hθv, hθz, hθr⟩ := Scheme.exists_cappedDecoder (S := t'.toScheme) hu'
    (rfl : t'.toCellScheme.grade Q.cap = Q.threshold)
  have hW : IsWitness (stepSuppressor Q.threshold) θ :=
    ⟨(IsWitness.id_step _).antitone, (IsWitness.id_step _).isSelfVisible, hθb, hθm,
      fun x k hx i hi ↦ by
        by_cases hk : k ≤ Q.threshold
        · exact hθv k hk i hi x
        · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
          rw [hx, visibilityReplace_bot]
          exact hθz x hx k i hi⟩
  refine ⟨θ, hW, fun i hi x ↦ hθv _ le_rfl i hi x, fun x hx ↦ hθr x ?_⟩
  rw [CellScheme.mem_below, CellScheme.gradedIndex_le_iff, CellScheme.gradedIndex_fst,
    CellScheme.gradedIndex_snd, hscope]
  exact ⟨subset_univ _, hx⟩

end Reads

/-! ### The template image and the frame -/

variable {t' : StageType.{u} α k} {p : StageType.{u} α n} {e : Fin n ↪ Fin k}
  {d : StageType.{u} α (n + 1)}
  (hte : restrictFace e t' = some p) (hdp : restrictFace Fin.castSuccEmb d = some p)

/-- A cell of grade at most the threshold lies below the cap, for a cap of full scope. -/
theorem mem_below_cap (Q : GrowthRequests t' d.toScheme)
    (hscope : t'.toCellScheme.scope Q.cap = univ) {x : Fin t'.card}
    (hx : t'.toCellScheme.grade x ≤ Q.threshold) :
    x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) := by
  rw [CellScheme.mem_below, CellScheme.gradedIndex_le_iff, CellScheme.gradedIndex_fst,
    CellScheme.gradedIndex_snd, hscope]
  exact ⟨subset_univ _, hx⟩

/-- The cleaned cap row is the cap row at a cell not labelled `⊥`. -/
theorem cleanedCapRow_of_ne_bot (Q : GrowthRequests t' d.toScheme) {x : Fin t'.card}
    (hx : t'.label x ≠ ⊥) : Q.cleanedCapRow x = t'.rowAt Q.cap x :=
  ite_eq_right hx

/-- **The decoder on the cleaned cap row** at calibrated requests: for the capped decoder `θ` of a
lawful section `u'`, `θ` sends the cleaned cap row at the cap, the references, the marker and the
root cells to `u'` capped at its cap value. -/
theorem Calibrated.decoder_cleanedCapRow {Q : GrowthRequests t' d.toScheme} (hQ : Q.Calibrated hte)
    {u' : Fin t'.card → Label.{u}} {θ : Label.{u} → Label.{u}}
    (hθr : ∀ x, t'.toCellScheme.grade x ≤ Q.threshold →
      θ (t'.rowAt Q.cap x) = min (u' x) (u' Q.cap)) :
    θ (Q.cleanedCapRow Q.cap) = u' Q.cap ∧
      (∀ j ∈ Q.exacts, θ (Q.cleanedCapRow (Q.ref j)) = min (u' (Q.ref j)) (u' Q.cap)) ∧
      θ (Q.cleanedCapRow Q.marker) = min (u' Q.marker) (u' Q.cap) ∧
      ∀ i, θ (Q.cleanedCapRow (t'.faceCell hte i)) =
        min (u' (t'.faceCell hte i)) (u' Q.cap) := by
  refine ⟨?_, fun j hj ↦ ?_, ?_, fun i ↦ ?_⟩
  · rw [Q.cleanedCapRow_of_ne_bot hQ.label_cap, hθr _ le_rfl, min_self]
  · rw [Q.cleanedCapRow_of_ne_bot (hQ.ref j hj).2.2, hθr _ (hQ.ref j hj).1]
  · rw [Q.cleanedCapRow_of_ne_bot hQ.marker.2.2, hθr _ hQ.marker.1]
  · rw [(hQ.root i).2, hθr _ (hQ.root i).1]

/-- The root section of a lawful context section is lawful on the root face. -/
theorem isLawful_root {u' : Fin t'.card → Label.{u}} (hu' : t'.rows.IsLawful u') :
    p.rows.IsLawful fun i ↦ u' (t'.faceCell hte i) := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t' e).mp hte
  exact hu'.comap (t'.isLowerEmbedding_comap e)

/-- **The relative lift by the template image** (case 3).  For calibrated requests with a
template, an allowed pair `(u, v)` and a lawful context section `u'` in the bottom class below the
cap, agreeing with `u` capped at `γ` (self-visible at the threshold) below its cap value `c'`, with
marker read at least `γ` when high values are requested: the template image `θ ∘ V` under the
capped decoder of `u'`, with its root made literal by the root lift at `c'`, is allowed with `u'`
and agrees with `v` capped at `γ`. -/
theorem Allowed.exists_lift_of_template {Q : GrowthRequests t' d.toScheme}
    (hQ : Q.Calibrated hte) (hT : Q.HasTemplate hte hdp) (hd : d.IsLegal) (hn : 0 < n)
    {u u' : Fin t'.card → Label.{u}} {v : Fin d.card → Label.{u}}
    (hall : Q.Allowed hte hdp u v) (hu' : t'.rows.IsLawful u') {γ : Label.{u}}
    (hγ : IsSelfVisible Q.threshold γ) (hag : ∀ x, min (u' x) γ = min (u x) γ)
    (hcls : ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      u' x = ⊥ → t'.label x = ⊥)
    (hlt : γ < u' Q.cap) (hmk : Q.highs.Nonempty → γ ≤ Q.readMarker u') :
    ∃ v' : Fin d.card → Label.{u}, Q.Allowed hte hdp u' v' ∧ ∀ j, min (v' j) γ = min (v j) γ := by
  obtain ⟨-, -, -, hadm⟩ := hall
  obtain ⟨V, hV, hVr, hVc, -, hVz⟩ := hT
  obtain ⟨θ, hW, hθv, hθr⟩ := Q.exists_capDecoder hu' hQ.scope_cap
  obtain ⟨hθc, hθref, hθmk, hθroot⟩ := hQ.decoder_cleanedCapRow hte hθr
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
    · exact (hQ.ref j hj).2.2 (hcls _ (Q.mem_below_cap hQ.scope_cap (hQ.ref j hj).1)
        (visibilityReplace_eq_bot_iff.mp h))
    · exact hc'b h
  have hmkb : Q.readMarker u' ≠ ⊥ := by
    intro h0
    rcases min_eq_bot.mp h0 with h | h
    · exact hQ.marker.2.2 (hcls _ (Q.mem_below_cap hQ.scope_cap hQ.marker.1)
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
  have hA := hadm (fun x hx hux ↦ hcls x hx ((eq_bot_iff_of_min_eq (hag x) hγb).mpr hux))
    (fun h0 ↦ hγb (le_bot_iff.mp (h0 ▸ hγc))) j
  rw [min_eq_min_of_le (hv'c j) hlt.le]
  refine min_eq_min_of_correctAt (hwc j) hA hγ hag hlt.le hγc (hQ.cover j)
    (fun hf ↦ (hQ.ref j hf).2.1) fun hy ↦ ?_
  have hm := hmk ⟨j, hy⟩
  refine ⟨hm, ?_⟩
  have h1 := min_readMarker_eq hγ hag hlt.le hγc hQ.marker.2.1
  rw [min_eq_right hm] at h1
  exact min_eq_right_iff.mp h1.symm

/-- **The relative lift in the frame** (case 2).  For calibrated requests with a template, an
allowed pair `(u, v)` and a lawful context section `u'` in the bottom class below the cap, agreeing
with `u` capped at `γ` (self-visible at the threshold) below its cap value, with high requests and
a marker read below `γ`: the frame inequalities of the template, carried to `u'` by its capped
decoder, put every exact read of `u'` below `γ`, so the root lift of `v` at `γ` is allowed with
`u'`. -/
theorem Allowed.exists_lift_of_frame {Q : GrowthRequests t' d.toScheme}
    (hQ : Q.Calibrated hte) (hT : Q.HasTemplate hte hdp) (hd : d.IsLegal) (hn : 0 < n)
    {u u' : Fin t'.card → Label.{u}} {v : Fin d.card → Label.{u}}
    (hall : Q.Allowed hte hdp u v) (hu' : t'.rows.IsLawful u') {γ : Label.{u}}
    (hγ : IsSelfVisible Q.threshold γ) (hag : ∀ x, min (u' x) γ = min (u x) γ)
    (hcls : ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      u' x = ⊥ → t'.label x = ⊥)
    (hlt : γ < u' Q.cap) (hne : Q.highs.Nonempty) (hmk : Q.readMarker u' < γ) :
    ∃ v' : Fin d.card → Label.{u}, Q.Allowed hte hdp u' v' ∧ ∀ j, min (v' j) γ = min (v j) γ := by
  obtain ⟨-, hv, hroot, hadm⟩ := hall
  obtain ⟨-, -, -, -, hVf, -⟩ := hT
  obtain ⟨θ, hW, hθv, hθr⟩ := Q.exists_capDecoder hu' hQ.scope_cap
  obtain ⟨hθc, hθref, hθmk, -⟩ := hQ.decoder_cleanedCapRow hte hθr
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
  have hA := hadm (fun x hx hux ↦ hcls x hx ((eq_bot_iff_of_min_eq (hag x) hγb).mpr hux))
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

/-- **The relative lift from a template**: calibrated requests with a template on a legal donor
with a nonempty root have the relative lift.  The four cases: outside the class
(`StageType.GrowthRequests.Allowed.exists_lift_of_not_class`), cap value at most `γ`
(`StageType.GrowthRequests.Allowed.exists_lift_of_cap_le`), the frame
(`StageType.GrowthRequests.Allowed.exists_lift_of_frame`) and the template image
(`StageType.GrowthRequests.Allowed.exists_lift_of_template`). -/
theorem hasRelativeLift_of_template {Q : GrowthRequests t' d.toScheme} (hQ : Q.Calibrated hte)
    (hT : Q.HasTemplate hte hdp) (hd : d.IsLegal) (hn : 0 < n) : Q.HasRelativeLift hte hdp := by
  intro u u' v γ hall hu' hγ hag
  have hγ1 : IsSelfVisible (n + 1) γ := hγ.mono hQ.arity
  by_cases hin : (∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      u' x = ⊥ → t'.label x = ⊥) ∧ u' Q.cap ≠ ⊥
  swap
  · exact Allowed.exists_lift_of_not_class hte hdp Q hd hn hall hu' hγ1 hag hin
  obtain ⟨hcls, hcb⟩ := hin
  rcases le_or_gt (u' Q.cap) γ with hle | hlt
  · exact Allowed.exists_lift_of_cap_le hte hdp Q hd hn hall hu' hγ1
      (fun h ↦ hcb (le_bot_iff.mp (h ▸ hle))) hag hle (fun j hj ↦ (hQ.ref j hj).2.1)
      hQ.marker.2.1
  by_cases h2 : Q.highs.Nonempty ∧ Q.readMarker u' < γ
  · exact Allowed.exists_lift_of_frame hte hdp hQ hT hd hn hall hu' hγ hag hcls hlt h2.1 h2.2
  · exact Allowed.exists_lift_of_template hte hdp hQ hT hd hn hall hu' hγ hag hcls hlt
      fun hne ↦ not_lt.mp fun h ↦ h2 ⟨hne, h⟩

end GrowthRequests

end StageType

end VaughtConjecture
