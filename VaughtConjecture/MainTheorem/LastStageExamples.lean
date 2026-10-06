/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.Examples
import VaughtConjecture.MainTheorem.LastStage

/-!
# Examples of eventual departure and the last stage

The statements of `VaughtConjecture.MainTheorem.LastStage` on abstract types of classes.

* **The last stage `0`**: a class not in `D_1` has last stage `0` and lies in the loss at `0`,
  for any expansion domains.
* **The domains of a rank**: for a map `r` from the classes to the countable ordinals, the
  domains `{x | β ≤ r x}` are expansion domains, and the last stage of `x` is `r x`.  Two
  instances: the tail domains of the countable ordinals (the last stage of an ordinal is itself),
  and a two-stage family on `Bool` (`false` lost at `0`, `true` at `1`, and `D_2` empty).
* **Separation does not give departure** (the control of `COMPANIONS.md`, terminal refinement,
  item 1): the tail domains with one further class `⋆` adjoined to every domain below `ω₁`
  (`adjoinPersistent Unit`, with the tail domains `tail` of `VaughtConjecture.MainTheorem.Examples`)
  have nonempty losses and logical agreement for the observations "is the ordinal `s`", which
  separate distinct classes; yet `⋆` lies in every domain below `ω₁`.  So no family of observations
  isolating every class has logical agreement on these domains (`core_eq_empty`): isolation of each
  class cannot be weakened to separation.
-/

namespace VaughtConjecture.MainTheorem

open Set Order
open scoped Ordinal

section Examples

/-! ### The last stage `0` -/

/-- **A class not in `D_1` has last stage `0`** and lies in the loss at `0`. -/
example {X : Type} (D : ExpansionDomains X) {q : X} (hq : q ∉ D.domain 1) :
    D.lastStage q = 0 ∧ q ∈ D.domain 0 \ D.domain (0 + 1) :=
  ⟨ExpansionDomains.lastStage_eq_zero hq, by simp [D.zero], by simpa using hq⟩

/-! ### The domains of a rank -/

/-- The **domains of a rank** `r` below `ω₁`: stage `β` keeps the classes of rank at least `β`. -/
private def ofRank {X : Type*} (r : X → Ordinal.{0}) (hr : ∀ x, r x < ω₁) :
    ExpansionDomains X where
  domain β := {x | β ≤ r x}
  zero := eq_univ_of_forall fun x ↦ (zero_le : (0 : Ordinal) ≤ r x)
  antitone _ _ h _ hx := h.trans hx
  limit l hl _ x hx := by
    by_contra h
    exact not_add_one_le (r x) (mem_iInter₂.1 hx _ (hl.succ_lt (not_le.1 h)))
  domain_eq_empty_of_omega_one_le _ h :=
    eq_empty_of_forall_notMem fun x hx ↦ (h.trans hx).not_gt (hr x)

/-- **The last stage of the domains of a rank is the rank**: `x` is not in the domain just above
its rank, so the last stage is attained there. -/
private theorem lastStage_ofRank {X : Type*} (r : X → Ordinal.{0}) (hr : ∀ x, r x < ω₁) (x : X) :
    (ofRank r hr).lastStage x = r x := by
  have h := ExpansionDomains.isGreatest_lastStage (D := ofRank r hr) (add_one_lt_omega_one (hr x))
    (not_add_one_le (r x))
  exact le_antisymm (Order.lt_add_one_iff.1 h.2)
    (ExpansionDomains.le_lastStage (D := ofRank r hr) (le_refl (r x)))

/-- **The tail domains of the countable ordinals**: the last stage of an ordinal is itself, and
the loss at `ξ` is the fibre of the last stage at `ξ`, the ordinal `ξ`. -/
example (x : CountableOrdinal) (ξ : Ordinal.{0}) :
    tail.lastStage x = x.1 ∧
      (x ∈ tail.domain ξ \ tail.domain (ξ + 1) ↔ x.1 = ξ) := by
  -- the tail domains are the domains of the rank `x ↦ x`
  have h : tail.lastStage x = x.1 := lastStage_ofRank Subtype.val (fun x ↦ mem_Iio.1 x.2) x
  rw [ExpansionDomains.mem_loss_iff_lastStage_eq_of_notMem (D := tail)
    (add_one_lt_omega_one x.2) (not_add_one_le x.1), h]
  exact ⟨rfl, Iff.rfl⟩

/-- The rank of the two-stage family: `true` has rank `1`, `false` rank `0`. -/
private def twoStageRank (b : Bool) : Ordinal.{0} := if b then 1 else 0

/-- The ranks of the two-stage family are countable. -/
private theorem twoStageRank_lt (b : Bool) : twoStageRank b < ω₁ := by
  cases b
  · exact Ordinal.omega_pos 1
  · exact Ordinal.one_lt_omega0.trans Ordinal.omega0_lt_omega_one

/-- **A two-stage family**: `false` is lost at `0`, `true` at `1`, and `D_2` is empty. -/
example : (ofRank twoStageRank twoStageRank_lt).lastStage false = 0 ∧
    (ofRank twoStageRank twoStageRank_lt).lastStage true = 1 ∧
    (ofRank twoStageRank twoStageRank_lt).domain 2 = ∅ := by
  refine ⟨lastStage_ofRank _ _ false, lastStage_ofRank _ _ true,
    eq_empty_of_forall_notMem fun b hb ↦ ?_⟩
  have h : (2 : Ordinal.{0}) ≤ 1 := hb.trans (by cases b <;> simp [twoStageRank])
  exact one_lt_two.not_ge h

/-! ### Separation does not give departure -/

/-- **Separation does not give departure**: the domains with a persistent class adjoined have
nonempty losses and logical agreement for the observations "is the ordinal `s`", which separate
distinct classes, yet the persistent class lies in every domain below `ω₁`; so no family of
observations isolating every class has logical agreement on them. -/
example : (adjoinPersistent Unit).HasNonemptyLosses ∧
    (adjoinPersistent Unit).HasLogicalAgreement
      (fun (s : CountableOrdinal) (z : CountableOrdinal ⊕ Unit) ↦ z = .inl s) ∧
    (∀ p q : CountableOrdinal ⊕ Unit, p ≠ q → ∃ s, ¬ ((p = .inl s) ↔ (q = .inl s))) ∧
    Sum.inr () ∈ ⋂ ξ < ω₁, (adjoinPersistent Unit).domain ξ ∧
    ∀ (S : Type) (truth : S → CountableOrdinal ⊕ Unit → Prop),
      (∀ q, ∃ s, ∀ p, truth s p ↔ p = q) → ¬ (adjoinPersistent Unit).HasLogicalAgreement truth := by
  have hn : (adjoinPersistent Unit).HasNonemptyLosses :=
    ⟨fun ξ hξ ↦ ⟨.inl ⟨ξ, hξ⟩, le_refl ξ, not_add_one_le ξ⟩⟩
  have hcore : Sum.inr () ∈ ⋂ ξ < ω₁, (adjoinPersistent Unit).domain ξ :=
    mem_iInter₂.2 fun _ hξ ↦ hξ
  refine ⟨hn, ⟨fun s ↦ ⟨s.1 + 1, add_one_lt_omega_one s.2, fun p hp p' hp' ↦ ?_⟩⟩, ?_, hcore,
    fun S truth hiso ha ↦ by simp [ExpansionDomains.core_eq_empty ha hn hiso] at hcore⟩
  · have hne : ∀ z ∈ (adjoinPersistent Unit).domain (s.1 + 1), z ≠ .inl s := by
      rintro _ hz rfl
      exact not_add_one_le s.1 hz
    exact iff_of_false (hne p hp) (hne p' hp')
  · rintro (a | ⟨⟩) q h
    · exact ⟨a, by simp [Ne.symm h]⟩
    · rcases q with b | ⟨⟩
      · exact ⟨b, by simp⟩
      · exact absurd rfl h

end Examples

end VaughtConjecture.MainTheorem
