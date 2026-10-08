/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapCarrier
import VaughtConjecture.Extension.CapTransport

/-!
# A carrier at which cutoff determination fails at every cutoff

Roadmap, Layer 3 ((R3) of the table of 3.4).

The clause of hollow cutoff determination at the context of `TiedRootCapCounterexample` asks for
**some** carrier and **some** permitted cutoff (`StageType.isDeterminedWithin_receivingFamily_iff`
unfolds it to the top clause).  This file compiles a carrier at which it fails at **every**
permitted cutoff, at every stage that is a limit of stages zero or limits.

* **The lifting shifter** (`Label.liftShifter δ x`, `Label.isWitness_liftShifter`, compiled in this
  repository (theorem named)): the map keeping the labels below a stage `δ` (zero or a limit) and
  the formal top and sending every other label to `x ≥ δ`, self-visible at `K` and not `⊤`, is a
  witness bounded by grade `K` sending only `⊥` to `⊥`.
* **The lowered donor** (`TiedRootCapCounterexample.lowDonor`): the donor capped at `δ + 4`, a
  legal one-point coface of the root (the root is labelled `3 < δ`); its apex is `δ + 4`.
* **The lowered carrier** (`TiedRootCapCounterexample.exists_lowCarrier`): a legal one-point
  extension of the context whose face along `extendByLast rootEmb` is the lowered donor (the exact
  pinned extension, by coatom extensions on at most four points).
* **The raised carrier** (`TiedRootCapCounterexample.raised`, `restrictFace_raised_context`,
  `restrictFace_raised_donor`): the lowered carrier with its labels reduced to `δ` (stage
  reduction, lawful at `δ` zero or a limit): its faces are the context and the donor, literally,
  when `δ` lies above `3` and above the labels of the donor other than `⊤`.
* **The members** (`TiedRootCapCounterexample.member`): the lowered carrier sent by the lifting
  shifter at `δ` to an ordinal above a cutoff `c`; it agrees with the raised carrier below `c`, is
  literal on the context, and has the apex of the donor below `⊤`.
* **Failure at every cutoff** (`TiedRootCapCounterexample.exists_carrier_not_isDeterminedWithin`,
  compiled): for `α` a limit of stages that are zero or limits, some legal coface of the context
  whose face along `extendByLast rootEmb` is the donor determines the donor within its receiving
  family at no permitted cutoff.

**What this says.**  The clause is a property of the carrier, not of the context: the mechanism
uses only that the root of the context has no cell labelled `⊤` and that the labels lie below a
stage `δ` that is zero or a limit; it does not use the separation of the tied root cells.  A
carrier meeting the clause must force, by its rows, the apex of the donor to `⊤` in every literal
member (`StageType.isDeterminedWithin_receivingFamily_iff`), as a top-reading carrier does; the
raised carrier does not, because its labelling comes from a lawful labelling with the apex below
`⊤`.  Whether some carrier meets it at this context (the selective top-reading carrier) remains
open; the carrier with the canonical labelling of the completion is not decided here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### The lifting shifter -/

namespace Label

open Classical in
/-- The **lifting shifter** at a stage `δ` and a label `x`: it keeps the labels below `δ` and the
formal top, and sends every other label (an ordinal at least `δ`) to `x`. -/
noncomputable def liftShifter (δ : Ordinal.{u}) (x y : Label.{u}) : Label.{u} :=
  if y < δ then y else if y = ⊤ then ⊤ else x

variable {δ : Ordinal.{u}} {x y : Label.{u}}

theorem liftShifter_of_lt (h : y < δ) : liftShifter δ x y = y := ite_eq_left h

theorem liftShifter_top : liftShifter δ x ⊤ = ⊤ := by
  simp [liftShifter, not_lt.mpr (le_top : (δ : Label.{u}) ≤ ⊤)]

theorem liftShifter_of_le (h : (δ : Label.{u}) ≤ y) (ht : y ≠ ⊤) : liftShifter δ x y = x := by
  simp [liftShifter, not_lt.mpr h, ht]

/-- **The lifting shifter is a witness bounded by grade `K`** at a stage `δ` that is zero or a
limit, for a label `x` at least `δ`, not the formal top, and self-visible at `K`. -/
theorem isWitness_liftShifter {K : ℕ} (hδ : Order.IsSuccPrelimit δ) (hx : (δ : Label.{u}) ≤ x)
    (hxv : IsSelfVisible K x) :
    IsWitness (stepSuppressor.{u} K) (liftShifter δ x) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := liftShifter_of_lt (WithBot.bot_lt_coe _)
  monotone a b hab := by
    by_cases hb : b < δ
    · rw [liftShifter_of_lt (hab.trans_lt hb), liftShifter_of_lt hb]
      exact hab
    by_cases hbt : b = ⊤
    · rw [hbt, liftShifter_top]
      exact le_top
    rw [liftShifter_of_le (not_lt.mp hb) hbt]
    by_cases ha : a < δ
    · rw [liftShifter_of_lt ha]
      exact ha.le.trans hx
    · have hat : a ≠ ⊤ := fun h ↦ hbt (top_le_iff.mp (h ▸ hab))
      rw [liftShifter_of_le (not_lt.mp ha) hat]
  visibilityReplace_comm y k hy i hi := by
    have hδb : (⊥ : Label.{u}) < δ := WithBot.bot_lt_coe _
    by_cases hyδ : y < δ
    · have h' : visibilityReplace k i y < δ := (visibilityReplace_lt_iff hδ).mpr hyδ
      rw [liftShifter_of_lt h', liftShifter_of_lt hyδ]
    by_cases hyt : y = ⊤
    · subst hyt
      rw [visibilityReplace_top, liftShifter_top, visibilityReplace_top]
    have h' : ¬ visibilityReplace k i y < δ := fun h ↦ hyδ ((visibilityReplace_lt_iff hδ).mp h)
    have h't : visibilityReplace k i y ≠ ⊤ := by
      induction y using recBotCoeTop with
      | bot => exact absurd hδb hyδ
      | top => exact absurd rfl hyt
      | coe o => simp
    rw [liftShifter_of_le (not_lt.mp h') h't, liftShifter_of_le (not_lt.mp hyδ) hyt] at *
    rcases le_or_gt k K with hk | hk
    · exact ((hxv.mono hk).visibilityReplace_eq i).symm
    · rw [stepSuppressor_of_lt hk, le_bot_iff] at hy
      exact absurd (hy ▸ hx) (not_le.mpr hδb)

/-- The lifting shifter sends only `⊥` to `⊥` when `x` is at least `δ`. -/
theorem eq_bot_of_liftShifter_eq_bot (hx : (δ : Label.{u}) ≤ x) (h : liftShifter δ x y = ⊥) :
    y = ⊥ := by
  by_cases hyδ : y < δ
  · rwa [liftShifter_of_lt hyδ] at h
  by_cases hyt : y = ⊤
  · rw [hyt, liftShifter_top] at h
    exact absurd h top_ne_bot
  · rw [liftShifter_of_le (not_lt.mp hyδ) hyt] at h
    exact absurd (h ▸ hx) (not_le.mpr (WithBot.bot_lt_coe _))

end Label

/-! ### The carrier and the member -/

namespace TiedRootCapCounterexample

open StageType

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α) {δ : Ordinal.{u}}

/-- Every label of the context is `⊤` or below a stage `δ` above `3`. -/
theorem context_label_top_or_lt (h3 : three.{u} < δ) (z : Fin (context hα).card) :
    (context hα).label z = ⊤ ∨ (context hα).label z < δ := by
  induction z using Fin.lastCases with
  | last => exact .inl (context_label_cap hα)
  | cast d =>
    rw [context_label_castSucc]
    unfold collapseShifter
    split_ifs
    · exact .inr (WithBot.bot_lt_coe _)
    · exact .inl rfl
    · exact .inr h3

/-- A label `⊤` or below `δ` is fixed by the lifting shifter and by the reduction to `δ`. -/
theorem fixed_of_top_or_lt {y x : Label.{u}} (hy : y = ⊤ ∨ y < δ) :
    liftShifter δ x y = y ∧ Label.reduce δ y = y := by
  rcases hy with rfl | hy
  · exact ⟨liftShifter_top, reduce_top⟩
  · exact ⟨liftShifter_of_lt hy, reduce_of_lt hy⟩

variable (hδ : Order.IsSuccPrelimit δ) (hδα : δ < α) (h3 : three.{u} < δ)
  (hdδ : ∀ j, (donor hα).label j ≠ ⊤ → (donor hα).label j < δ)

/-- The lowered value `δ + 4` at the new tops. -/
noncomputable abbrev low (δ : Ordinal.{u}) : Label.{u} := ((δ + 4 : Ordinal.{u}) : Label.{u})

include hδ in
theorem isSelfVisible_low : IsSelfVisible 4 (low δ) := isSelfVisible_coe_add hδ le_rfl

theorem le_low : (δ : Label.{u}) ≤ low δ :=
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (le_self_add))

theorem low_ne_top : low δ ≠ (⊤ : Label.{u}) :=
  fun h ↦ WithTop.coe_ne_top (WithBot.coe_injective h)

include hα hδα in
theorem low_lt : low δ < (α : Label.{u}) :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (hα.isSuccPrelimit.add_natCast_lt hδα 4))

/-- **The lowered donor**: the donor with its labels capped at `δ + 4`, so that its labels `⊤`
become the ordinal `δ + 4`. -/
noncomputable def lowDonor (δ : Ordinal.{u}) (hδ : Order.IsSuccPrelimit δ) (hδα : δ < α) :
    StageType.{u} α 2 where
  toScheme := (donor hα).toScheme
  label j := min ((donor hα).label j) (low δ)
  isWellFormed := (donor hα).isWellFormed
  isCoded := (donor hα).isCoded
  isLawful := (donor hα).isLawful.min_const_of_isSelfVisible (K := 4)
    (fun d ↦ ((donor hα).grade_le d).trans (by omega)) (isSelfVisible_low hδ)
  atStage j := .inl ((min_le_right _ _).trans_lt (low_lt hα hδα))

include h3 in
/-- The lowered donor has the root as its face on the first point. -/
theorem restrictFace_lowDonor :
    restrictFace Fin.castSuccEmb (lowDonor hα δ hδ hδα) = some (root hα) := by
  refine (restrictFace_congr_label (t := lowDonor hα δ hδ hδα) (s := donor hα) rfl
    fun i j hij hi ↦ ?_).trans (restrictFace_donor hα)
  obtain rfl : i = j := Fin.ext hij
  obtain ⟨y, rfl⟩ := exists_faceCell_eq (restrictFace_donor hα) hi
  change min ((donor hα).label _) (low δ) = _
  rw [label_faceCell]
  exact min_eq_left ((h3.le.trans le_low).trans' le_rfl |>.trans' le_rfl)

theorem lowDonor_apex : (lowDonor hα δ hδ hδα).label (donorApex hα) = low δ := by
  change min ((donor hα).label (donorApex hα)) (low δ) = low δ
  rw [donorApex_label, min_top_left]

include h3 in
/-- **The lowered carrier**: a legal one-point extension of the context whose face along
`extendByLast rootEmb` is the lowered donor (the exact pinned extension). -/
theorem exists_lowCarrier : ∃ D : StageType.{u} α 4, D.IsLegal ∧
    restrictFace Fin.castSuccEmb D = some (context hα) ∧
    restrictFace (extendByLast rootEmb) D = some (lowDonor hα δ hδ hδα) :=
  exists_pinned_extension_of_lt (fun m' hm' ta tb p ↦
    exists_coatomExtension_of_le_two hα.isSuccPrelimit (by omega) ta tb p)
    (isLegal_context hα) (restrictFace_context hα) (isLegal_donor hα)
    (restrictFace_lowDonor hα hδ hδα h3)

/-! ### The raised carrier and the members of its receiving families -/

/-- **The raised carrier**: the labels of `D` reduced to the stage `δ` (every label at least `δ`
becomes `⊤`). -/
noncomputable def raised (D : StageType.{u} α 4) (δ : Ordinal.{u}) (hδ : Order.IsSuccPrelimit δ)
    (hδα : δ < α) : StageType.{u} α 4 where
  toScheme := D.toScheme
  label := Label.reduce δ ∘ D.label
  isWellFormed := D.isWellFormed
  isCoded := D.isCoded
  isLawful := D.isLawful.reduce hδ
  atStage j := by
    by_cases h : D.label j < δ
    · left
      rw [Function.comp_apply, reduce_of_lt h]
      exact h.trans (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hδα))
    · right
      exact reduce_of_le (not_lt.mp h)

/-- The labels of the raised carrier other than `⊤` lie below `δ`. -/
theorem raised_label_lt {D : StageType.{u} α 4} (j : Fin D.card)
    (hj : (raised D δ hδ hδα).label j ≠ ⊤) : (raised D δ hδ hδα).label j < δ := by
  change Label.reduce δ (D.label j) ≠ ⊤ at hj
  change Label.reduce δ (D.label j) < δ
  by_cases h : D.label j < δ
  · rwa [reduce_of_lt h]
  · exact absurd (reduce_of_le (not_lt.mp h)) hj

include h3 in
theorem restrictFace_raised_context {D : StageType.{u} α 4}
    (h₁ : restrictFace Fin.castSuccEmb D = some (context hα)) :
    restrictFace Fin.castSuccEmb (raised D δ hδ hδα) = some (context hα) := by
  refine (restrictFace_congr_label (t := raised D δ hδ hδα) (s := D) rfl
    fun i j hij hi ↦ ?_).trans h₁
  obtain rfl : i = j := Fin.ext hij
  obtain ⟨z, rfl⟩ := exists_faceCell_eq h₁ hi
  change Label.reduce δ (D.label _) = _
  rw [label_faceCell]
  exact (fixed_of_top_or_lt (x := ⊤) (context_label_top_or_lt hα h3 z)).2

include hdδ in
theorem restrictFace_raised_donor {D : StageType.{u} α 4}
    (h₂ : restrictFace (extendByLast rootEmb) D = some (lowDonor hα δ hδ hδα)) :
    restrictFace (extendByLast rootEmb) (raised D δ hδ hδα) = some (donor hα) := by
  obtain ⟨hf, hcomap⟩ := (restrictFace_eq_some_iff D _).mp h₂
  rw [restrictFace_of_mem (raised D δ hδ hδα) _ hf]
  have hS : (D.comap _ hf).toScheme = (lowDonor hα δ hδ hδα).toScheme :=
    congrArg StageType.toScheme hcomap
  refine congrArg some (StageType.ext hS fun i j hij ↦ ?_)
  have hl : D.label (D.cellMap (extendByLast rootEmb) i) = (lowDonor hα δ hδ hδα).label j :=
    label_congr hcomap (i := i) (j := j) hij
  change Label.reduce δ (D.label (D.cellMap (extendByLast rootEmb) i)) = _
  rw [hl]
  change Label.reduce δ (min ((donor hα).label j) (low δ)) = _
  by_cases hj : (donor hα).label j = ⊤
  · rw [hj, min_top_left, reduce_of_le le_low]
  · rw [min_eq_left ((hdδ j hj).le.trans le_low), reduce_of_lt (hdδ j hj)]

/-- **The member at a cutoff**: the labels of `D` sent by the lifting shifter at `δ` to `x`. -/
noncomputable def member (D : StageType.{u} α 4) (δ : Ordinal.{u}) (hδ : Order.IsSuccPrelimit δ)
    {x : Label.{u}} (hx : (δ : Label.{u}) ≤ x) (hxv : IsSelfVisible 4 x) (hxα : x < α) :
    StageType.{u} α 4 where
  toScheme := D.toScheme
  label := liftShifter δ x ∘ D.label
  isWellFormed := D.isWellFormed
  isCoded := D.isCoded
  isLawful := D.isLawful.map_of_apply_eq_bot (K := 4) (fun d ↦ D.grade_le d)
    (isWitness_liftShifter hδ hx hxv) fun _ h ↦ eq_bot_of_liftShifter_eq_bot hx h
  atStage j := by
    by_cases h : D.label j < δ
    · rw [Function.comp_apply, liftShifter_of_lt h]
      exact D.atStage j
    by_cases ht : D.label j = ⊤
    · right
      rw [Function.comp_apply, ht, liftShifter_top]
    · left
      rw [Function.comp_apply, liftShifter_of_le (not_lt.mp h) ht]
      exact hxα

/-- **Cutoff determination fails at a carrier, at every cutoff.**  Let the stage `α` be a limit of
stages that are zero or limits.  Some legal one-point extension of the context, whose face along
`extendByLast rootEmb` is the donor, determines the donor within its receiving family at no
permitted cutoff.  It is the pinned extension over the lowered donor (`⊤` replaced by `δ + 4`),
raised to `⊤` at its labels at least `δ`; at a cutoff `c`, the lifting shifter sending the labels
at least `δ` to an ordinal at least `c` gives a member literal on the context whose face along
`extendByLast rootEmb` has the apex of the donor below `⊤`. -/
theorem exists_carrier_not_isDeterminedWithin
    (hα₂ : ∀ γ < α, ∃ δ : Ordinal.{u}, Order.IsSuccPrelimit δ ∧ γ < δ ∧ δ < α) :
    ∃ D : StageType.{u} α 4, D ∈ (context hα).cofaces ∧
      restrictFace (extendByLast rootEmb) D = some (donor hα) ∧
      ∀ c : Label.{u}, IsPermittedCutoff α c →
        ¬ IsDeterminedWithin (receivingFamily D c) (context hα) rootEmb (donor hα) := by
  -- a stage `δ` above `3` and the labels of the donor other than `⊤`
  have h3α : three.{u} < α := (atStage_three hα).resolve_right three_ne_top
  obtain ⟨c₀, h3c, hcα, -, hc⟩ :=
    exists_isSelfVisible_bound hα.isSuccPrelimit 0 h3α (donor hα).label
  induction c₀ using recBotCoeTop with
  | bot => exact absurd (le_bot_iff.mp h3c) three_ne_bot
  | top => exact absurd hcα (not_lt.mpr le_top)
  | coe γ =>
  have hγα : γ < α := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hcα)
  obtain ⟨δ, hδ, hγδ, hδα⟩ := hα₂ γ hγα
  have hγδ' : ((γ : Ordinal.{u}) : Label.{u}) < δ :=
    WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hγδ)
  have h3 : three.{u} < δ := h3c.trans_lt hγδ'
  have hdδ : ∀ j, (donor hα).label j ≠ ⊤ → (donor hα).label j < δ := fun j hj ↦
    (hc j ((donor hα).atStage j |>.resolve_right hj)).trans_lt hγδ'
  obtain ⟨D, hD, h₁, h₂⟩ := exists_lowCarrier hα hδ hδα h3
  refine ⟨raised D δ hδ hδα, ⟨hD, restrictFace_raised_context hα hδ hδα h3 h₁⟩,
    restrictFace_raised_donor hα hδ hδα hdδ h₂, fun c hc hdet ↦ ?_⟩
  -- the cutoff is an ordinal below the stage
  obtain ⟨hcb, hcα'⟩ := hc
  induction c using recBotCoeTop with
  | bot => exact absurd hcb (lt_irrefl _)
  | top => exact absurd hcα' (not_lt.mpr le_top)
  | coe o =>
  have hoα : o < α := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hcα')
  obtain ⟨xo, hxo, hxoα, hxv⟩ :=
    exists_lt_lt_isSelfVisible hα.isSuccPrelimit (max_lt hδα hoα) 4
  have hδx : (δ : Label.{u}) ≤ (xo : Label.{u}) :=
    WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ((le_max_left _ _).trans hxo.le))
  have hox : ((o : Ordinal.{u}) : Label.{u}) ≤ (xo : Label.{u}) :=
    WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ((le_max_right _ _).trans hxo.le))
  have hxα : ((xo : Ordinal.{u}) : Label.{u}) < α :=
    WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hxoα)
  have hxt : ((xo : Ordinal.{u}) : Label.{u}) ≠ ⊤ :=
    fun h ↦ WithTop.coe_ne_top (WithBot.coe_injective h)
  set q := member D δ hδ hδx hxv hxα
  -- the member lies in the receiving family
  have hq : q ∈ receivingFamily (raised D δ hδ hδα) (o : Label.{u}) := by
    refine ⟨rfl, fun i j hij ↦ ?_⟩
    obtain rfl : i = j := Fin.ext hij
    change min (liftShifter δ _ (D.label i)) _ = min (Label.reduce δ (D.label i)) _
    by_cases h : D.label i < δ
    · rw [liftShifter_of_lt h, reduce_of_lt h]
    by_cases ht : D.label i = ⊤
    · rw [ht, liftShifter_top, reduce_top]
    · rw [liftShifter_of_le (not_lt.mp h) ht, reduce_of_le (not_lt.mp h), min_top_left,
        min_eq_right hox]
  -- its face on the context is literal
  have hq₁ : restrictFace Fin.castSuccEmb q = some (context hα) := by
    refine (restrictFace_congr_label (t := q) (s := D) rfl fun i j hij hi ↦ ?_).trans h₁
    obtain rfl : i = j := Fin.ext hij
    obtain ⟨z, rfl⟩ := exists_faceCell_eq h₁ hi
    change liftShifter δ _ (D.label _) = _
    rw [label_faceCell]
    exact (fixed_of_top_or_lt (context_label_top_or_lt hα h3 z)).1
  -- its face along `extendByLast rootEmb` has the apex of the donor below `⊤`
  have hq₂ := hdet q hq hq₁
  have happex := label_faceCell hq₂ (donorApex hα)
  rw [donorApex_label] at happex
  have hD₂ := label_faceCell h₂ (donorApex hα)
  rw [lowDonor_apex] at hD₂
  change liftShifter δ _ (D.label (faceCell h₂ (donorApex hα))) = ⊤ at happex
  rw [hD₂, liftShifter_of_le le_low low_ne_top] at happex
  exact hxt happex

end TiedRootCapCounterexample

end VaughtConjecture
