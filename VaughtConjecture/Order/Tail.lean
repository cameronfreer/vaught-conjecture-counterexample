/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.Hom.Set
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Countable

/-!
# Tails of linear orders and isomorphisms between final segments of a well-order

**Tails.**  A *tail* of a linear order is a nonempty upper set.  Two linear orders are
**tail-equivalent** (`Order.TailEquivalent`) when some tail of one is order-isomorphic to some tail
of the other.  This is the comparison that survives a change of root of an exterior order: above
an infinite closed root `B`, enlarging `B` to a closed `D ⊇ B` keeps the exterior relation on the
points outside `D` and puts every point of `D` first (`Closure.exteriorRootChangeTarget`,
`Closure.rootBeforeExteriorTarget`), so the exterior order above `D` is the upper set of the
exterior order above `B` formed by the points outside `D`.  Tails are upper sets, not only final
segments `Set.Ici a`: the points outside a closed set need not have a least element.  In an order
whose proper initial segments `Set.Iio x` are countable, every tail has countable complement, so
tail equivalence also absorbs every change of a countable initial part.

**Final segments of a well-order.**  `IciIsoEventuallyIdTarget`: in a well-order in which every
countable set is bounded above (for example the countable ordinals), an order isomorphism between
two final segments `Set.Ici a` and `Set.Ici b` is the identity on a whole final segment
`Set.Ici γ`, not merely on a closed unbounded set.  An initial shift `a ≠ b` moves only countably
many indices.

**Results.**  `tailEquivalentSymmTarget` and `iciIsoEventuallyIdTarget` are proved (the latter
through `exists_iciIso_eq_of_le`, the case `a ≤ b`).  `TailEquivalentTransTarget` is stated;
open.
-/

universe u v w

namespace VaughtConjecture.Order

/-- Two linear orders are **tail-equivalent** when some nonempty upper set of the first is
order-isomorphic to some nonempty upper set of the second. -/
def TailEquivalent (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β] : Prop :=
  ∃ (U : Set α) (V : Set β), IsUpperSet U ∧ IsUpperSet V ∧ U.Nonempty ∧ V.Nonempty ∧
    Nonempty (U ≃o V)

/-- **Target: tail equivalence is symmetric.**  Proved (`Order.tailEquivalentSymmTarget`). -/
def TailEquivalentSymmTarget : Prop :=
  ∀ ⦃α : Type u⦄ ⦃β : Type v⦄ [LinearOrder α] [LinearOrder β],
    TailEquivalent α β → TailEquivalent β α

/-- **Tail equivalence is symmetric**, the target form: invert the isomorphism. -/
theorem tailEquivalentSymmTarget : TailEquivalentSymmTarget.{u, v} := by
  intro α β _ _ ⟨U, V, hU, hV, hU₀, hV₀, ⟨e⟩⟩
  exact ⟨V, U, hV, hU, hV₀, hU₀, ⟨e.symm⟩⟩

/-- **Target: tail equivalence is transitive.**  If a tail of `α` is isomorphic to a tail of `β`
and a tail of `β` to a tail of `γ`, then a tail of `α` is isomorphic to a tail of `γ`: the two
tails of `β` are comparable by inclusion, and the isomorphism of the larger carries the smaller to
a tail.  Stated; open. -/
def TailEquivalentTransTarget : Prop :=
  ∀ ⦃α : Type u⦄ ⦃β : Type v⦄ ⦃γ : Type w⦄ [LinearOrder α] [LinearOrder β] [LinearOrder γ],
    TailEquivalent α β → TailEquivalent β γ → TailEquivalent α γ

/-- **Target: isomorphisms of final segments of an `ω₁`-like well-order are eventually the
identity.**  Let `I` be a well-order in which every countable set is bounded above.  Every order
isomorphism `φ` between final segments `Set.Ici a` and `Set.Ici b` is the identity on some final
segment `Set.Ici γ` with `a, b ≤ γ`.  Proved (`Order.iciIsoEventuallyIdTarget`).

Proof.  If `a ≤ b`, then `φ` is a strictly monotone self-map of the well-order
`Set.Ici a`, so `δ ≤ φ δ`.  Put `γ₀ = b` and `γₙ₊₁ = φ γₙ`; the least upper bound `γ` of this
increasing sequence exists (countable sets are bounded; least elements exist) and is a fixed
point: if `γ < φ γ`, then `γ = φ δ` with `δ < γ`, so `δ < γₙ` for some `n` and
`γ = φ δ < φ γₙ = γₙ₊₁ ≤ γ`.  For `δ ≥ γ`, the inverse sends `δ` to `φ⁻¹ δ ≥ φ⁻¹ γ = γ` and is a
strictly monotone self-map of `Set.Ici γ`, so `δ ≤ φ⁻¹ δ`, whence `φ δ ≤ δ ≤ φ δ`.  If `b ≤ a`,
apply this to `φ⁻¹`. -/
def IciIsoEventuallyIdTarget : Prop :=
  ∀ ⦃I : Type u⦄ [LinearOrder I] [WellFoundedLT I], (∀ s : Set I, s.Countable → BddAbove s) →
    ∀ ⦃a b : I⦄ (φ : Set.Ici a ≃o Set.Ici b), ∃ γ, a ≤ γ ∧ b ≤ γ ∧
      ∀ δ (hδ : a ≤ δ), γ ≤ δ → (φ ⟨δ, hδ⟩ : I) = δ

/-- The case `a ≤ b` of `IciIsoEventuallyIdTarget`. -/
theorem exists_iciIso_eq_of_le {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (hbdd : ∀ s : Set I, s.Countable → BddAbove s) {a b : I} (hab : a ≤ b)
    (φ : Set.Ici a ≃o Set.Ici b) :
    ∃ γ, b ≤ γ ∧ ∀ δ (hδ : a ≤ δ), γ ≤ δ → (φ ⟨δ, hδ⟩ : I) = δ := by
  let f : Set.Ici a → Set.Ici a := fun x ↦ ⟨φ x, hab.trans (φ x).2⟩
  have hf : StrictMono f := fun _ _ h ↦ φ.strictMono h
  let g : ℕ → I := fun n ↦ (f^[n] ⟨b, hab⟩ : I)
  have hg (n : ℕ) : g (n + 1) = φ (f^[n] ⟨b, hab⟩) := by
    simp only [g, Function.iterate_succ_apply']
    rfl
  obtain ⟨M, hM⟩ := hbdd (Set.range g) (Set.countable_range g)
  obtain ⟨γ, hγ, hmin⟩ := wellFounded_lt.has_min (upperBounds (Set.range g)) ⟨M, hM⟩
  have hbγ : b ≤ γ := hγ ⟨0, rfl⟩
  have haγ : a ≤ γ := hab.trans hbγ
  have hfix : (φ ⟨γ, haγ⟩ : I) = γ := by
    refine le_antisymm (not_lt.mp fun hlt ↦ ?_) (hf.le_apply (x := ⟨γ, haγ⟩))
    set δ := φ.symm ⟨γ, hbγ⟩ with hδ
    have hφδ : φ δ = ⟨γ, hbγ⟩ := φ.apply_symm_apply _
    have hδγ : δ < ⟨γ, haγ⟩ := by
      rw [← φ.lt_iff_lt, hφδ]
      exact hlt
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ : ∃ y ∈ Set.range g, ¬ y ≤ (δ : I) := by
      by_contra! h
      exact hmin δ (fun y hy ↦ h y hy) hδγ
    have h1 : δ < f^[n] ⟨b, hab⟩ := not_le.mp hn
    have h2 := φ.strictMono h1
    rw [hφδ] at h2
    exact (not_lt.mpr (hγ ⟨n + 1, rfl⟩)) (by rw [hg]; exact h2)
  refine ⟨γ, hbγ, fun δ hδ hγδ ↦ le_antisymm ?_ (hf.le_apply (x := ⟨δ, hδ⟩))⟩
  have hfix' : φ.symm ⟨γ, hbγ⟩ = ⟨γ, haγ⟩ := by
    rw [OrderIso.symm_apply_eq]
    exact Subtype.ext hfix.symm
  have hψ (y : Set.Ici γ) : γ ≤ (φ.symm ⟨y, hbγ.trans (Set.mem_Ici.mp y.2)⟩ : I) := by
    have hmono := φ.symm.monotone (show (⟨γ, hbγ⟩ : Set.Ici b) ≤
      ⟨y, hbγ.trans (Set.mem_Ici.mp y.2)⟩ from Set.mem_Ici.mp y.2)
    rw [hfix'] at hmono
    exact hmono
  let h : Set.Ici γ → Set.Ici γ := fun y ↦ ⟨φ.symm ⟨y, hbγ.trans (Set.mem_Ici.mp y.2)⟩, hψ y⟩
  have hh : StrictMono h := fun _ _ hlt ↦ φ.symm.strictMono hlt
  have hle : δ ≤ (φ.symm ⟨δ, hbγ.trans hγδ⟩ : I) := hh.le_apply (x := ⟨δ, hγδ⟩)
  have := φ.monotone (show (⟨δ, hδ⟩ : Set.Ici a) ≤ φ.symm ⟨δ, hbγ.trans hγδ⟩ from hle)
  rw [φ.apply_symm_apply] at this
  exact this

/-- **Isomorphisms of final segments of an `ω₁`-like well-order are eventually the identity**,
the target form. -/
theorem iciIsoEventuallyIdTarget : IciIsoEventuallyIdTarget.{u} := by
  intro I _ _ hbdd a b φ
  rcases le_total a b with hab | hba
  · obtain ⟨γ, hbγ, hγ⟩ := exists_iciIso_eq_of_le hbdd hab φ
    exact ⟨γ, hab.trans hbγ, hbγ, hγ⟩
  · obtain ⟨γ, haγ, hγ⟩ := exists_iciIso_eq_of_le hbdd hba φ.symm
    refine ⟨γ, haγ, hba.trans haγ, fun δ hδ hγδ ↦ ?_⟩
    have h := hγ δ (hba.trans hδ) hγδ
    have : φ.symm ⟨δ, hba.trans hδ⟩ = ⟨δ, hδ⟩ := Subtype.ext h
    rw [← this, φ.apply_symm_apply]

end VaughtConjecture.Order
