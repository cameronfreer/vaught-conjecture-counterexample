/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapMember

/-!
# Cutoff determination at a carrier: raised labellings and the zero-one law

Roadmap, Layer 3 ((R3) of the table of 3.4).

The clause of hollow cutoff determination asks, at a context `t'` along `h` and a donor `d`, for
some carrier `D` (a legal coface of `t'` with face `d` along `extendByLast h`) and some permitted
cutoff at which `d` is determined within the receiving family of `D`.  This file proves, for
**every** carrier, that the cutoff plays no role above the labels of the carrier, and that the
mechanism of `TiedRootCapCounterexample.exists_carrier_not_isDeterminedWithin` is the only way a
carrier fails.

* **Raising above a stage** (`StageType.raiseAbove`): the labels of a stage type at least a stage
  `δ` (zero or a limit, below `α`) replaced by `⊤`, on the same scheme.
* **A raised labelling below `⊤` at a new top fails at every cutoff**
  (`StageType.not_isDeterminedWithin_raiseAbove`, compiled in this repository (theorem named)):
  if `D` is literal on `t'`, the labels of `t'` are `⊤` or below `δ`, and `D` is below `⊤` at a
  new top of the donor of `D.raiseAbove δ`, then `D.raiseAbove δ` determines the donor at no
  permitted cutoff.  The lifting shifter at `δ` sends `D` into every receiving family of the raised
  carrier, literal on `t'` and below `⊤` at that new top.
* **Every failure at a limit cutoff above the labels is of that form**
  (`StageType.exists_raiseAbove_eq_of_not_isDeterminedWithin`, compiled): a carrier `D` that does
  not determine its donor at a stage `δ` above its labels other than `⊤` is `D'.raiseAbove δ` for a
  lawful `D'` on its scheme, literal on `t'` and below `⊤` at a new top of the donor (a member of
  the receiving family at `δ`).
* **The zero-one law** (`StageType.isDeterminedWithin_of_exists`, compiled): a carrier that
  determines its donor at some permitted cutoff determines it at every stage `δ` (zero or a limit,
  below `α`) above its labels other than `⊤`.  So, when such a stage exists, a carrier either
  determines at every such stage or at no permitted cutoff, and the lifting-shifter argument
  applies to a carrier exactly when it fails at such a stage; it cannot be arranged by stage
  reduction at a carrier that determines.

The instances at the context of `BottomRootCounterexample` (root cells labelled `⊥`) are in
`VaughtConjecture.Continuation.TiedRootCapBottomCarrier`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ}

/-! ### Raising above a stage, and lifting above a stage -/

/-- **The labels at least `δ` raised to `⊤`**, on the scheme of `D` (stage reduction of the labels
to `δ`, which is zero or a limit). -/
noncomputable def raiseAbove (D : StageType.{u} α k) (δ : Ordinal.{u})
    (hδ : Order.IsSuccPrelimit δ) (hδα : δ < α) : StageType.{u} α k where
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

/-- **The labels at least `δ` other than `⊤` lifted to `x`**, on the scheme of `D` (the lifting
shifter at `δ`). -/
noncomputable def liftAbove (D : StageType.{u} α k) (δ : Ordinal.{u})
    (hδ : Order.IsSuccPrelimit δ) {x : Label.{u}} (hx : (δ : Label.{u}) ≤ x)
    (hxv : IsSelfVisible k x) (hxα : x < α) : StageType.{u} α k where
  toScheme := D.toScheme
  label := liftShifter δ x ∘ D.label
  isWellFormed := D.isWellFormed
  isCoded := D.isCoded
  isLawful := D.isLawful.map_of_apply_eq_bot (K := k) (fun d ↦ D.grade_le d)
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

/-! ### A raised labelling below `⊤` at a new top fails at every cutoff -/

/-- **A raised labelling below `⊤` at a new top determines at no cutoff.**  Let `α` be a limit,
`δ < α` zero or a limit, `D` literal on `t'` along the first points, the labels of `t'` `⊤` or
below `δ`, and `D` below `⊤` at a new top `j` of the face `d` of `D.raiseAbove δ` along
`extendByLast h`.  Then `D.raiseAbove δ` determines `d` over `t'` along `h` within its receiving
family at no permitted cutoff: at a cutoff `c`, the lifting shifter at `δ` to an ordinal at least
`c` sends `D` into the receiving family, literal on `t'`, and below `⊤` at `j`. -/
theorem not_isDeterminedWithin_raiseAbove (hα : Order.IsSuccLimit α) {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)} {D : StageType.{u} α (k + 1)}
    {δ : Ordinal.{u}} (hδ : Order.IsSuccPrelimit δ) (hδα : δ < α)
    (h₁ : restrictFace Fin.castSuccEmb D = some t')
    (hfix : ∀ z, t'.label z = ⊤ ∨ t'.label z < δ)
    (h₂ : restrictFace (extendByLast h) (D.raiseAbove δ hδ hδα) = some d) {j : Fin d.card}
    (hj : d.label j = ⊤) (hDj : ∀ i : Fin D.card, (i : ℕ) = faceCell h₂ j → D.label i ≠ ⊤)
    (c : Label.{u})
    (hc : IsPermittedCutoff α c) :
    ¬ IsDeterminedWithin (receivingFamily (D.raiseAbove δ hδ hδα) c) t' h d := by
  intro hdet
  obtain ⟨hcb, hcα⟩ := hc
  induction c using recBotCoeTop with
  | bot => exact absurd hcb (lt_irrefl _)
  | top => exact absurd hcα (not_lt.mpr le_top)
  | coe o =>
  have hoα : o < α := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hcα)
  obtain ⟨xo, hxo, hxoα, hxv⟩ :=
    exists_lt_lt_isSelfVisible hα.isSuccPrelimit (max_lt hδα hoα) (k + 1)
  have hδx : (δ : Label.{u}) ≤ (xo : Label.{u}) :=
    WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ((le_max_left _ _).trans hxo.le))
  have hox : ((o : Ordinal.{u}) : Label.{u}) ≤ (xo : Label.{u}) :=
    WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ((le_max_right _ _).trans hxo.le))
  have hxα : ((xo : Ordinal.{u}) : Label.{u}) < α :=
    WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hxoα)
  have hxt : ((xo : Ordinal.{u}) : Label.{u}) ≠ ⊤ :=
    fun h ↦ WithTop.coe_ne_top (WithBot.coe_injective h)
  set q := D.liftAbove δ hδ hδx hxv hxα
  -- the lifted labelling lies in the receiving family of the raised one
  have hq : q ∈ receivingFamily (D.raiseAbove δ hδ hδα) (o : Label.{u}) := by
    refine ⟨rfl, fun i i' hii ↦ ?_⟩
    obtain rfl : i = i' := Fin.ext hii
    change min (liftShifter δ _ (D.label i)) _ = min (Label.reduce δ (D.label i)) _
    by_cases hl : D.label i < δ
    · rw [liftShifter_of_lt hl, reduce_of_lt hl]
    by_cases ht : D.label i = ⊤
    · rw [ht, liftShifter_top, reduce_top]
    · rw [liftShifter_of_le (not_lt.mp hl) ht, reduce_of_le (not_lt.mp hl), min_top_left,
        min_eq_right hox]
  -- it is literal on `t'`
  have hq₁ : restrictFace Fin.castSuccEmb q = some t' := by
    refine (restrictFace_congr_label (t := q) (s := D) rfl fun i i' hii hi ↦ ?_).trans h₁
    obtain rfl : i = i' := Fin.ext hii
    obtain ⟨z, rfl⟩ := exists_faceCell_eq h₁ hi
    change liftShifter δ _ (D.label _) = _
    rw [label_faceCell]
    rcases hfix z with hz | hz
    · rw [hz, liftShifter_top]
    · exact liftShifter_of_lt hz
  -- its face along `extendByLast h` would be `d`, `⊤` at `j`
  have hq₂ := hdet q hq hq₁
  have hqj := label_faceCell hq₂ j
  rw [hj] at hqj
  set i₀ : Fin D.card := ⟨faceCell hq₂ j, (faceCell hq₂ j).isLt⟩
  change liftShifter δ _ (D.label i₀) = ⊤ at hqj
  have hDj' := hDj i₀ rfl
  by_cases hl : D.label i₀ < δ
  · rw [liftShifter_of_lt hl] at hqj
    exact hDj' hqj
  · rw [liftShifter_of_le (not_lt.mp hl) hDj'] at hqj
    exact hxt hqj

/-! ### Every failure at a limit cutoff above the labels is a raised labelling -/

/-- **A failure at a stage above the labels is a raised labelling.**  Let `D` restrict along
`extendByLast h` to `d`, and let `δ < α`, zero or a limit, lie above the labels of `D` other than
`⊤`.  If `d` is not determined over `t'` within the receiving family of `D` at `δ`, then `D` is
`D'.raiseAbove δ` for a stage type `D'` on its scheme, literal on `t'` along the first points and
below `⊤` at a cell of `D` carrying a new top of `d` (a member of the receiving family). -/
theorem exists_raiseAbove_eq_of_not_isDeterminedWithin {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)} {D : StageType.{u} α (k + 1)}
    (h₂ : restrictFace (extendByLast h) D = some d) {δ : Ordinal.{u}}
    (hδ : Order.IsSuccPrelimit δ) (hδα : δ < α) (hδD : ∀ j, D.label j ≠ ⊤ → D.label j < δ)
    (hndet : ¬ IsDeterminedWithin (receivingFamily D δ) t' h d) :
    ∃ D' : StageType.{u} α (k + 1), D'.raiseAbove δ hδ hδα = D ∧
      restrictFace Fin.castSuccEmb D' = some t' ∧
      ∃ (i : Fin D'.card) (j : Fin d.card), (i : ℕ) = faceCell h₂ j ∧ d.label j = ⊤ ∧
        D'.label i ≠ ⊤ := by
  rw [isDeterminedWithin_receivingFamily_iff h₂ hδD] at hndet
  push Not at hndet
  obtain ⟨q, hq, hq₁, i, j, hij, hj, hqi⟩ := hndet
  refine ⟨q, ?_, hq₁, i, j, hij, hj, hqi⟩
  obtain ⟨hS, hcut⟩ := hq
  refine StageType.ext hS fun a b hab ↦ ?_
  change Label.reduce δ (q.label a) = D.label b
  have hm := hcut a b hab
  by_cases hb : D.label b = ⊤
  · rw [hb, min_top_left] at hm
    rw [hb]
    exact reduce_of_le (min_eq_right_iff.mp hm)
  · have hlt := hδD b hb
    rw [min_eq_left hlt.le] at hm
    have hqa : q.label a < δ := by
      by_contra hge
      rw [min_eq_right (not_lt.mp hge)] at hm
      exact hlt.ne hm.symm
    rw [reduce_of_lt hqa, ← hm, min_eq_left hqa.le]

/-! ### The zero-one law -/

/-- **The zero-one law of cutoff determination at a carrier.**  Let `α` be a limit and `D` a stage
type with faces `t'` along the first points and `d` along `extendByLast h`.  If `D` determines `d`
over `t'` within its receiving family at some permitted cutoff, it does so at every stage `δ < α`,
zero or a limit, above its labels other than `⊤`. -/
theorem isDeterminedWithin_of_exists (hα : Order.IsSuccLimit α) {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)} {D : StageType.{u} α (k + 1)}
    (h₁ : restrictFace Fin.castSuccEmb D = some t') (h₂ : restrictFace (extendByLast h) D = some d)
    (hex : ∃ c, IsPermittedCutoff α c ∧ IsDeterminedWithin (receivingFamily D c) t' h d)
    {δ : Ordinal.{u}} (hδ : Order.IsSuccPrelimit δ) (hδα : δ < α)
    (hδD : ∀ j, D.label j ≠ ⊤ → D.label j < δ) :
    IsDeterminedWithin (receivingFamily D δ) t' h d := by
  by_contra hndet
  obtain ⟨D', rfl, h₁', i, j, hij, hj, hD'i⟩ :=
    exists_raiseAbove_eq_of_not_isDeterminedWithin h₂ hδ hδα hδD hndet
  obtain ⟨c, hc, hdet⟩ := hex
  refine not_isDeterminedWithin_raiseAbove hα hδ hδα h₁' (fun z ↦ ?_) h₂ hj ?_ c hc hdet
  · rw [← label_faceCell h₁ z]
    set i₁ : Fin D'.card := ⟨faceCell h₁ z, (faceCell h₁ z).isLt⟩
    change Label.reduce δ (D'.label i₁) = ⊤ ∨ Label.reduce δ (D'.label i₁) < δ
    by_cases hz : D'.label i₁ < δ
    · exact .inr (by rwa [reduce_of_lt hz])
    · exact .inl (reduce_of_le (not_lt.mp hz))
  · intro i' hi'
    obtain rfl : i' = i := Fin.ext (hi'.trans hij.symm)
    exact hD'i

end StageType

end VaughtConjecture
