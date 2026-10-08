/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthAdmittedStep
import VaughtConjecture.Continuation.GrowthCappedDecoder

/-!
# The relative lift on the donor

Roadmap, Layer 3 ((R3) and (R4), the controllers of the growth construction for the small donor).

The growth carrier attaches the donor `d`, on the root and one new point, to the whole context
`t'` along the root.  Its controllers are **allowed pairs** (`StageType.GrowthRequests.Allowed`):
a lawful section `u` of the context, a lawful section `v` of the donor, equal on the root, with
`(u, v)` admitted by the requests.  The lifts from the context face ask the **relative lift on the
donor** (`StageType.GrowthRequests.HasRelativeLift`): from an allowed pair `(u, v)` and a lawful
section `u'` of the context agreeing with `u` capped at `γ`, some `v'` makes `(u', v')` allowed and
agrees with `v` capped at `γ`.  It is a lift on the donor alone: the context enters through one map
applied to one template.

## Main statements

* `StageType.IsLegal.cappedLift_root_top`: **donor bountifulness from the root to the top** — a
  legal donor lifts capped from its root face to its full face, at every cap self-visible at its
  arity.  The root must have a point.
* `StageType.GrowthRequests.correctAt_map`: **the template image reads the requests** — if a
  donor labelling `V` reads the requests from the cleaned cap row `e`, and `θ` is monotone, fixes
  `⊥`, commutes with visibility replacement at the threshold, and sends `e` at the cap, the
  references and the marker to `u'` capped at its cap value, then `θ ∘ V` reads the requests from
  `u'`.  With the capped decoder of `u'` at the cap (`Scheme.exists_cappedDecoder`) this is case 3
  of the relative lift; lawfulness of `θ ∘ V` is the transport of lawfulness through a witness
  with the bottom pattern of a lawful companion (`CellScheme.Rows.IsLawful.map_of_bot_iff`).
* `StageType.GrowthRequests.HasTemplate` (open): a lawful donor template reading the requests
  from the cleaned cap row, equal to it on the root, with the frame inequalities.
* `StageType.GrowthRequests.HasRelativeLift` (open): the relative lift.

## References

The relative lift is the growth step of [Kni26, §4]; bountifulness is [Kni26, Definition 2.5.14].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **Donor bountifulness from the root to the top**: a legal stage type on `n + 1` points whose
first `n` points span a closed face, with `0 < n`, lifts capped from the root face at the grade `n`
to the full face at the grade `n + 1`. -/
theorem IsLegal.cappedLift_root_top {d : StageType.{u} α (n + 1)} (hd : d.IsLegal)
    (hface : univ.map Fin.castSuccEmb ∈ d.toCellScheme.faces) (hn : 0 < n) :
    d.rows.CappedLift (X := (univ.map Fin.castSuccEmb, n))
      (Y := ((univ : Finset (Fin (n + 1))), n + 1)) ⟨subset_univ _, Nat.le_succ n⟩ :=
  hd.isBountiful.cappedLift ⟨hface, hn, by simp⟩ ⟨d.univ_mem_faces, Nat.succ_pos n, by simp⟩ _

namespace GrowthRequests

variable {t' : StageType.{u} α k} {D : Scheme.{u} (n + 1)} (Q : GrowthRequests t' D)

/-- **The template image reads the requests.**  Let `ℓ` read the requests from `e` at `j`, and let
`θ` be monotone, fix `⊥`, commute with visibility replacement at the threshold with the values at
most the threshold, and send `e` at the cap, at the reference of `j` and at the marker to `s`
capped at `s Q.cap`, which is self-visible at the threshold.  Then `θ ℓ` reads the requests from
`s` at `j`. -/
theorem correctAt_map {e s : Fin t'.card → Label.{u}} {j : Fin D.card} {ℓ : Label.{u}}
    (h : Q.CorrectAt e j ℓ) {θ : Label.{u} → Label.{u}} (hθ : Monotone θ) (hθb : θ ⊥ = ⊥)
    (hθv : ∀ i ≤ Q.threshold, ∀ x, θ (visibilityReplace Q.threshold i x) =
      visibilityReplace Q.threshold i (θ x))
    (hcap : θ (e Q.cap) = s Q.cap)
    (href : j ∈ Q.exacts → θ (e (Q.ref j)) = min (s (Q.ref j)) (s Q.cap))
    (hmk : θ (e Q.marker) = min (s Q.marker) (s Q.cap))
    (hvis : IsSelfVisible Q.threshold (s Q.cap)) (hoff : j ∈ Q.exacts → Q.offset j ≤ Q.threshold)
    (hR : Q.markerOffset ≤ Q.threshold) : Q.CorrectAt s j (θ ℓ) := by
  refine ⟨fun hz ↦ ?_, fun hf ↦ ?_, fun hy ↦ ?_⟩
  · rw [← hcap, ← hθ.map_min, h.1 hz, hθb]
  · rw [← hcap, ← hθ.map_min, h.2.1 hf, readExact, hθ.map_min, hθv _ (hoff hf), href hf, hcap,
      readExact, ← visibilityReplace_min_of_isSelfVisible (hoff hf) hvis, min_assoc, min_self,
      visibilityReplace_min_of_isSelfVisible (hoff hf) hvis]
  · have h1 := hθ (h.2.2 hy)
    rw [readMarker, hθ.map_min, hθv _ hR, hmk, hcap, hθ.map_min, hcap,
      ← visibilityReplace_min_of_isSelfVisible hR hvis, min_assoc, min_self,
      visibilityReplace_min_of_isSelfVisible hR hvis] at h1
    exact h1

/-- **The root lift on the donor**: a legal donor `d` with root face `p` (`0 < n`), a lawful
section `v` of `d`, a lawful section `ρ` of `p` agreeing with `v` on the root capped at a cap `γ`
self-visible at `n + 1`: some lawful section of `d` is `ρ` on the root and agrees with `v` capped
at `γ`.  Bountifulness of `d` from the root face to the full face
(`StageType.IsLegal.cappedLift_root_top`), with the root face read through the lower embedding of
the face. -/
theorem _root_.VaughtConjecture.StageType.IsLegal.exists_rootLift {d : StageType.{u} α (n + 1)}
    (hd : d.IsLegal) (hn : 0 < n)
    {p : StageType.{u} α n} (hdp : restrictFace Fin.castSuccEmb d = some p)
    {v : Fin d.card → Label.{u}} (hv : d.rows.IsLawful v) {ρ : Fin p.card → Label.{u}}
    (hρ : p.rows.IsLawful ρ) {γ : Label.{u}} (hγ : IsSelfVisible (n + 1) γ)
    (hag : ∀ i, min (ρ i) γ = min (v (d.faceCell hdp i)) γ) :
    ∃ v' : Fin d.card → Label.{u}, d.rows.IsLawful v' ∧ (∀ i, v' (d.faceCell hdp i) = ρ i) ∧
      ∀ j, min (v' j) γ = min (v j) γ := by
  classical
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff d _).mp hdp
  set X : Finset (Fin (n + 1)) × ℕ := (univ.map Fin.castSuccEmb, n)
  set Y : Finset (Fin (n + 1)) × ℕ := ((univ : Finset (Fin (n + 1))), n + 1)
  have hXY : X ≤ Y := ⟨subset_univ _, Nat.le_succ n⟩
  have hφ := d.toScheme.isLowerEmbedding_comap Fin.castSuccEmb
  have himg : d.toScheme.cellMap Fin.castSuccEmb ''
      (d.toScheme.comap Fin.castSuccEmb).toCellScheme.below
        ((univ : Finset (Fin n)), n) = d.toCellScheme.below X := by
    rw [Scheme.image_cellMap_below]
    rfl
  -- the root section, as a labelling of the cells below the root face
  let r : d.toCellScheme.below X → Label.{u} := fun x ↦ ρ ((hφ.belowEquiv himg).symm x).1
  have hr : d.rows.IsLawfulBelow X r := by
    rw [← CellScheme.Rows.isLawfulBelow_comap_iff hφ himg]
    have h1 : (d.rows.comap hφ).IsLawfulBelow ((univ : Finset (Fin n)), n) fun x ↦ ρ x.1 :=
      hρ.isLawfulBelow _
    convert h1 using 1
    funext x
    simp [r]
  -- the cell of the root at a cell of the face
  have hsymm (i : Fin (d.comap Fin.castSuccEmb hf).card)
      (hi : i ∈ (d.toScheme.comap Fin.castSuccEmb).toCellScheme.below ((univ : Finset (Fin n)), n))
      (hm : d.toScheme.cellMap Fin.castSuccEmb i ∈ d.toCellScheme.below X) :
      ((hφ.belowEquiv himg).symm ⟨_, hm⟩).1 = i := by
    have : (hφ.belowEquiv himg) ⟨i, hi⟩ = ⟨_, hm⟩ := Subtype.ext rfl
    rw [← this, Equiv.symm_apply_apply]
  have hfc (i : Fin (d.comap Fin.castSuccEmb hf).card) :
      d.faceCell hdp i = d.toScheme.cellMap Fin.castSuccEmb i := rfl
  have hface (i : Fin (d.comap Fin.castSuccEmb hf).card) :
      i ∈ (d.toScheme.comap Fin.castSuccEmb).toCellScheme.below ((univ : Finset (Fin n)), n) :=
    ⟨subset_univ _, (d.comap Fin.castSuccEmb hf).grade_le i⟩
  have hmem (i : Fin (d.comap Fin.castSuccEmb hf).card) :
      d.toScheme.cellMap Fin.castSuccEmb i ∈ d.toCellScheme.below X := by
    rw [← himg]
    exact ⟨i, hface i, rfl⟩
  have hlift := hd.cappedLift_root_top hf hn
  obtain ⟨q', hq', hq'cap, hq'r⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists hXY).mp
    hlift γ hγ r (fun x ↦ v x) hr (hv.isLawfulBelow _) (fun x ↦ by
      obtain ⟨x, hx⟩ := x
      rw [← himg] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      simp only [r]
      rw [hsymm i hi (hmem i), hag i]
      rfl)
  have hall (j : Fin d.card) : j ∈ d.toCellScheme.below Y := ⟨subset_univ _, d.grade_le j⟩
  set w : Fin d.card → Label.{u} := fun j ↦ q' ⟨j, hall j⟩ with hw
  have hwq : (fun j : d.toCellScheme.below Y ↦ w j) = q' := funext fun _ ↦ rfl
  have hwl : d.rows.IsLawfulBelow Y fun j ↦ w j := by rw [hwq]; exact hq'
  obtain ⟨hord, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hwl
  refine ⟨w, ⟨fun j ↦ hord j (hall j), fun s ↦ hloc s (hall s),
    fun s t hst hg ↦ havail s t (hall t) hst hg⟩, fun i ↦ ?_, fun j ↦ hq'cap ⟨j, hall j⟩⟩
  have h1 := hq'r ⟨_, hmem i⟩
  simp only [r] at h1
  rw [hsymm i (hface i) (hmem i)] at h1
  exact h1

/-! ### Allowed pairs, the template, and the relative lift -/

variable {p : StageType.{u} α n} {e : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)}
  (hte : restrictFace e t' = some p) (hdp : restrictFace Fin.castSuccEmb d = some p)

/-- The **cleaned cap row**: the row of the cap, `⊥` where the context is `⊥`. -/
noncomputable def cleanedCapRow (Q : GrowthRequests t' d.toScheme) : Fin t'.card → Label.{u} :=
  fun x ↦ if t'.label x = ⊥ then ⊥ else t'.rowAt Q.cap x

/-- An **allowed pair**: lawful sections of the context and of the donor, equal on the root, and
admitted by the requests. -/
def Allowed (Q : GrowthRequests t' d.toScheme) (u : Fin t'.card → Label.{u})
    (v : Fin d.card → Label.{u}) : Prop :=
  t'.rows.IsLawful u ∧ d.rows.IsLawful v ∧
    (∀ i, v (d.faceCell hdp i) = u (t'.faceCell hte i)) ∧ Q.Admits u v

/-- **The template** (open): a lawful donor labelling reading the requests from the cleaned cap
row, equal to it on the root, with the frame inequalities when high values are requested. -/
def HasTemplate (Q : GrowthRequests t' d.toScheme) : Prop :=
  ∃ V : Fin d.card → Label.{u}, d.rows.IsLawful V ∧
    (∀ i, V (d.faceCell hdp i) = Q.cleanedCapRow (t'.faceCell hte i)) ∧
    (∀ j, Q.CorrectAt Q.cleanedCapRow j (V j)) ∧
    (Q.highs.Nonempty → ∀ j ∈ Q.exacts,
      Q.readExact Q.cleanedCapRow j ≤ Q.readMarker Q.cleanedCapRow)

/-- **The relative lift on the donor** (open): from an allowed pair `(u, v)` and a lawful section
`u'` of the context agreeing with `u` capped at `γ`, self-visible at the threshold, some `v'` makes
`(u', v')` allowed and agrees with `v` capped at `γ`. -/
def HasRelativeLift (Q : GrowthRequests t' d.toScheme) : Prop :=
  ∀ (u u' : Fin t'.card → Label.{u}) (v : Fin d.card → Label.{u}) (γ : Label.{u}),
    Q.Allowed hte hdp u v → t'.rows.IsLawful u' → IsSelfVisible Q.threshold γ →
    (∀ x, min (u' x) γ = min (u x) γ) →
    ∃ v' : Fin d.card → Label.{u}, Q.Allowed hte hdp u' v' ∧ ∀ j, min (v' j) γ = min (v j) γ

/-- **The template image reads the requests from every section in the class**: for a lawful
context section `u'` with the bottom class of `t'` below the cap, the capped decoder `θ` of `u'` at
the cap sends the template's reads of the cleaned cap row to the reads of `u'`, so `θ ∘ V` reads
the requests from `u'`.  The cap has full scope, and the references and the marker have grade at
most the threshold. -/
theorem exists_templateImage_correctAt (Q : GrowthRequests t' d.toScheme)
    {V : Fin d.card → Label.{u}} (hV : ∀ j, Q.CorrectAt Q.cleanedCapRow j (V j))
    {u' : Fin t'.card → Label.{u}} (hu' : t'.rows.IsLawful u')
    (hcls : ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      u' x = ⊥ ↔ t'.label x = ⊥)
    (hscope : t'.toCellScheme.scope Q.cap = univ)
    (href : ∀ j ∈ Q.exacts, t'.toCellScheme.grade (Q.ref j) ≤ Q.threshold ∧
      Q.offset j ≤ Q.threshold)
    (hmk : t'.toCellScheme.grade Q.marker ≤ Q.threshold ∧ Q.markerOffset ≤ Q.threshold) :
    ∃ θ : Label.{u} → Label.{u}, IsWitness (stepSuppressor Q.threshold) θ ∧
      (∀ x, θ x ≤ u' Q.cap) ∧ ∀ j, Q.CorrectAt u' j (θ (V j)) := by
  obtain ⟨θ, hθm, hθb, hθle, hθv, hθz, hθr⟩ := Scheme.exists_cappedDecoder (S := t'.toScheme) hu'
    (rfl : t'.toCellScheme.grade Q.cap = Q.threshold)
  have hbelow (x : Fin t'.card) (hx : t'.toCellScheme.grade x ≤ Q.threshold) :
      x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) := by
    rw [CellScheme.mem_below, CellScheme.gradedIndex_le_iff, CellScheme.gradedIndex_fst,
      CellScheme.gradedIndex_snd, hscope]
    exact ⟨subset_univ _, hx⟩
  -- the decoder on the cleaned cap row
  have hθe (x : Fin t'.card) (hx : x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap)) :
      θ (Q.cleanedCapRow x) = min (u' x) (u' Q.cap) := by
    unfold cleanedCapRow
    by_cases hb : t'.label x = ⊥
    · simp only [hb, ite_true, hθb, (hcls x hx).mpr hb, min_eq_left bot_le]
    · simp only [hb, ite_false]
      exact hθr x hx
  have hcb := hbelow Q.cap le_rfl
  have hcap : θ (Q.cleanedCapRow Q.cap) = u' Q.cap := by rw [hθe _ hcb, min_self]
  have hvis : IsSelfVisible Q.threshold (u' Q.cap) := hu'.orderly Q.cap
  have hW : IsWitness (stepSuppressor Q.threshold) θ :=
    ⟨(IsWitness.id_step _).antitone, (IsWitness.id_step _).isSelfVisible, hθb, hθm,
      fun x k hx i hi ↦ by
        by_cases hk : k ≤ Q.threshold
        · exact hθv k hk i hi x
        · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
          rw [hx, visibilityReplace_bot]
          exact hθz x hx k i hi⟩
  refine ⟨θ, hW, hθle, fun j ↦ ?_⟩
  exact Q.correctAt_map (hV j) hθm hθb (fun i hi x ↦ hθv _ le_rfl i hi x) hcap
    (fun hf ↦ hθe _ (hbelow _ (href j hf).1)) (hθe _ (hbelow _ hmk.1)) hvis
    (fun hf ↦ (href j hf).2) hmk.2

/-- **The template image is lawful on the donor** when the decoder keeps the bottom pattern of the
template: lawfulness passes through a witness bounded by the threshold, at least the arity of the
donor, with the template as lawful companion (`CellScheme.Rows.IsLawful.map_of_bot_iff`). -/
theorem templateImage_isLawful {V : Fin d.card → Label.{u}} (hV : d.rows.IsLawful V)
    {N : ℕ} (hN : n + 1 ≤ N) {θ : Label.{u} → Label.{u}} (hθ : IsWitness (stepSuppressor N) θ)
    (hpat : ∀ j, θ (V j) = ⊥ ↔ V j = ⊥) : d.rows.IsLawful (θ ∘ V) :=
  hV.map_of_bot_iff hV (fun j ↦ (d.grade_le j).trans hN) hθ hpat

/-- **The relative lift outside the class** (case 0): if the new section `u'` is not in the bottom
class of the context below the cap, or reads the cap as `⊥`, admission is vacuous and the root
lift of the donor at `γ` gives the lift.  The root has a point and `γ` is self-visible at the
arity of the donor. -/
theorem Allowed.exists_lift_of_not_class (Q : GrowthRequests t' d.toScheme) (hd : d.IsLegal)
    (hn : 0 < n) {u u' : Fin t'.card → Label.{u}} {v : Fin d.card → Label.{u}}
    (hall : Q.Allowed hte hdp u v) (hu' : t'.rows.IsLawful u') {γ : Label.{u}}
    (hγ : IsSelfVisible (n + 1) γ) (hag : ∀ x, min (u' x) γ = min (u x) γ)
    (hout : ¬ ((∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      u' x = ⊥ → t'.label x = ⊥) ∧ u' Q.cap ≠ ⊥)) :
    ∃ v' : Fin d.card → Label.{u}, Q.Allowed hte hdp u' v' ∧ ∀ j, min (v' j) γ = min (v j) γ := by
  obtain ⟨-, hv, hroot, -⟩ := hall
  -- the root section of `u'`, lawful on the root face
  have hρ : p.rows.IsLawful fun i ↦ u' (t'.faceCell hte i) := by
    obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t' e).mp hte
    exact hu'.comap (t'.isLowerEmbedding_comap e)
  obtain ⟨v', hv', hv'r, hv'cap⟩ := StageType.IsLegal.exists_rootLift hd hn hdp hv hρ hγ
    (fun i ↦ by rw [hroot i, hag])
  exact ⟨v', ⟨hu', hv', hv'r, fun hcls hcap ↦ absurd ⟨hcls, hcap⟩ hout⟩, hv'cap⟩

/-- **The relative lift at or below the cap value** (case 1): if the cap value of the new section
`u'` is at most `γ > ⊥`, the root lift of the donor at `γ` gives the lift, and admission passes by
capping at the cap value (`StageType.GrowthRequests.admits_of_min_eq_of_le`). -/
theorem Allowed.exists_lift_of_cap_le (Q : GrowthRequests t' d.toScheme) (hd : d.IsLegal)
    (hn : 0 < n) {u u' : Fin t'.card → Label.{u}} {v : Fin d.card → Label.{u}}
    (hall : Q.Allowed hte hdp u v) (hu' : t'.rows.IsLawful u') {γ : Label.{u}}
    (hγ : IsSelfVisible (n + 1) γ) (hγb : γ ≠ ⊥) (hag : ∀ x, min (u' x) γ = min (u x) γ)
    (hle : u' Q.cap ≤ γ) (hoff : ∀ j ∈ Q.exacts, Q.offset j ≤ Q.threshold)
    (hR : Q.markerOffset ≤ Q.threshold) :
    ∃ v' : Fin d.card → Label.{u}, Q.Allowed hte hdp u' v' ∧ ∀ j, min (v' j) γ = min (v j) γ := by
  obtain ⟨-, hv, hroot, hadm⟩ := hall
  have hρ : p.rows.IsLawful fun i ↦ u' (t'.faceCell hte i) := by
    obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t' e).mp hte
    exact hu'.comap (t'.isLowerEmbedding_comap e)
  obtain ⟨v', hv', hv'r, hv'cap⟩ := StageType.IsLegal.exists_rootLift hd hn hdp hv hρ hγ
    (fun i ↦ by rw [hroot i, hag])
  exact ⟨v', ⟨hu', hv', hv'r, Q.admits_of_min_eq_of_le hadm hγb hag hv'cap hle
    (hu'.orderly Q.cap) hoff hR⟩, hv'cap⟩

/-! ### The template from an encoding -/

/-- **The template from an encoding of the donor.**  Let `enc` be a witness bounded by the arity
`n + 1` of the donor that reflects `⊥` on the donor's labels, `H` (nonbottom, self-visible at
`n + 1`) the marker read of the cleaned cap row `e`, and let `enc` send the donor's labels to the
reads of `e`: bottom requests are bottom, exact requests to their reference reads (below `H`),
high requests to `H`, and the root to `e` capped at `H`.  If the root section of `e` is lawful on
the root face, then some lawful donor labelling is `e` on the root, reads the requests from `e`
exactly, and satisfies the frame inequalities: the encoded donor (lawful by transport), with its
root restored literally by the root lift at `H`. -/
theorem exists_template_of_encoding (Q : GrowthRequests t' d.toScheme) (hd : d.IsLegal)
    (hn : 0 < n) {eC : Fin t'.card → Label.{u}}
    (heρ : p.rows.IsLawful fun i ↦ eC (t'.faceCell hte i))
    {enc : Label.{u} → Label.{u}} (henc : IsWitness (stepSuppressor (n + 1)) enc)
    (hbot : ∀ j, enc (d.label j) = ⊥ → d.label j = ⊥) {H : Label.{u}} (hH : H ≠ ⊥)
    (hHvis : IsSelfVisible (n + 1) H)
    (hroot : ∀ i, min (enc (d.label (d.faceCell hdp i))) H = min (eC (t'.faceCell hte i)) H)
    (hZ : ∀ j ∈ Q.bottoms, d.label j = ⊥)
    (hF : ∀ j ∈ Q.exacts, enc (d.label j) =
      visibilityReplace Q.threshold (Q.offset j) (eC (Q.ref j)))
    (hFlt : ∀ j ∈ Q.exacts, visibilityReplace Q.threshold (Q.offset j) (eC (Q.ref j)) < H)
    (hT : ∀ j ∈ Q.highs, enc (d.label j) = H)
    (hHm : min H (eC Q.cap) = Q.readMarker eC) :
    ∃ V : Fin d.card → Label.{u}, d.rows.IsLawful V ∧
      (∀ i, V (d.faceCell hdp i) = eC (t'.faceCell hte i)) ∧
      (∀ j, Q.CorrectAt eC j (V j)) ∧
      (Q.highs.Nonempty → ∀ j ∈ Q.exacts, Q.readExact eC j ≤ Q.readMarker eC) := by
  have hV0 : d.rows.IsLawful (enc ∘ d.label) :=
    d.isLawful.map_of_bot_iff d.isLawful (fun j ↦ d.grade_le j) henc
      (fun j ↦ ⟨hbot j, fun h ↦ by rw [h, henc.map_bot]⟩)
  obtain ⟨V, hV, hVr, hVcap⟩ := StageType.IsLegal.exists_rootLift hd hn hdp hV0 heρ hHvis
    (fun i ↦ (hroot i).symm)
  have hVF (j) (hj : j ∈ Q.exacts) :
      V j = visibilityReplace Q.threshold (Q.offset j) (eC (Q.ref j)) := by
    have h1 := hVcap j
    simp only [Function.comp_apply] at h1
    rw [hF j hj, min_eq_left (hFlt j hj).le] at h1
    rcases le_total (V j) H with hle | hle
    · rwa [min_eq_left hle] at h1
    · rw [min_eq_right hle] at h1
      exact absurd h1.symm (hFlt j hj).ne
  have hVT (j) (hj : j ∈ Q.highs) : H ≤ V j := by
    have h1 := hVcap j
    simp only [Function.comp_apply] at h1
    rw [hT j hj, min_self] at h1
    exact min_eq_right_iff.mp h1
  have hVZ (j) (hj : j ∈ Q.bottoms) : V j = ⊥ := by
    have h1 := hVcap j
    simp only [Function.comp_apply] at h1
    rw [hZ j hj, henc.map_bot, min_eq_left bot_le] at h1
    rcases min_eq_bot.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 hH
  refine ⟨V, hV, hVr, fun j ↦ ⟨fun hz ↦ by rw [hVZ j hz, min_eq_left bot_le],
    fun hf ↦ by rw [hVF j hf]; rfl, fun hy ↦ ?_⟩, fun _ j hj ↦ ?_⟩
  · rw [← hHm]
    exact min_le_min_right _ (hVT j hy)
  · rw [readExact, ← hHm]
    exact min_le_min_right _ (hFlt j hj).le

end GrowthRequests

end StageType

end VaughtConjecture
