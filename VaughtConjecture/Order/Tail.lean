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
`Set.Ici γ`, not merely on a closed unbounded set.  An initial shift `a ≠ b` moves only boundedly
many indices; when the proper initial segments are countable, only countably many.

**Results (all proved).**  `tailEquivalentSymmTarget`; `tailEquivalentTransTarget`, through
`exists_orderIso_of_subset` (an isomorphism of upper sets restricts to a smaller nonempty upper set
of its codomain); `iciIsoEventuallyIdTarget`, through `exists_iciIso_eq_of_le` (the case
`a ≤ b`), and its form for a strictly monotone map onto a final segment,
`exists_forall_ge_eq_of_strictMonoOn`.
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
a tail.  The two tails of `β` meet in a nonempty upper set because `β` is linearly ordered (upper
sets are then comparable by inclusion); no cardinality hypothesis is used.  Proved
(`Order.tailEquivalentTransTarget`). -/
def TailEquivalentTransTarget : Prop :=
  ∀ ⦃α : Type u⦄ ⦃β : Type v⦄ ⦃γ : Type w⦄ [LinearOrder α] [LinearOrder β] [LinearOrder γ],
    TailEquivalent α β → TailEquivalent β γ → TailEquivalent α γ

/-- **Restricting an isomorphism of upper sets.**  If `e : U ≃o V` with `U` an upper set and
`V' ⊆ V` a nonempty upper set, then the points of `U` sent into `V'` form a nonempty upper set
isomorphic to `V'`. -/
theorem exists_orderIso_of_subset {α : Type u} {β : Type v} [LinearOrder α] [LinearOrder β]
    {U : Set α} {V V' : Set β} (hU : IsUpperSet U) (e : U ≃o V) (hV' : IsUpperSet V')
    (hV'V : V' ⊆ V) (hne : V'.Nonempty) :
    ∃ U' : Set α, IsUpperSet U' ∧ U'.Nonempty ∧ Nonempty (U' ≃o V') := by
  refine ⟨{a | ∃ h : a ∈ U, (e ⟨a, h⟩ : β) ∈ V'}, ?_, ?_, ⟨?_⟩⟩
  · rintro a a' haa' ⟨h, hv⟩
    exact ⟨hU haa' h, hV' (e.monotone (show (⟨a, h⟩ : U) ≤ ⟨a', hU haa' h⟩ from haa')) hv⟩
  · obtain ⟨v, hv⟩ := hne
    refine ⟨(e.symm ⟨v, hV'V hv⟩ : α), (e.symm ⟨v, hV'V hv⟩).2, ?_⟩
    simpa using hv
  · exact
      { toFun := fun x ↦ ⟨e ⟨x, x.2.fst⟩, x.2.snd⟩
        invFun := fun y ↦ ⟨e.symm ⟨y, hV'V y.2⟩, (e.symm _).2, by simp⟩
        left_inv := fun x ↦ by ext; simp
        right_inv := fun y ↦ by ext; simp
        map_rel_iff' := fun {x y} ↦ by
          change e _ ≤ e _ ↔ _
          rw [e.le_iff_le]
          rfl }

/-- **Tail equivalence is transitive**, the target form: the two tails of the middle order meet in
a nonempty upper set (they are comparable), to which both isomorphisms restrict. -/
theorem tailEquivalentTransTarget : TailEquivalentTransTarget.{u, v, w} := by
  rintro α β γ _ _ _ ⟨U₁, V₁, hU₁, hV₁, -, hV₁n, ⟨e₁⟩⟩ ⟨U₂, W, hU₂, hW, hU₂n, -, ⟨e₂⟩⟩
  have hMn : (V₁ ∩ U₂).Nonempty := by
    rcases hV₁.total hU₂ with h | h
    · obtain ⟨y, hy⟩ := hV₁n
      exact ⟨y, hy, h hy⟩
    · obtain ⟨y, hy⟩ := hU₂n
      exact ⟨y, h hy, hy⟩
  obtain ⟨U', hU', hU'n, ⟨f₁⟩⟩ :=
    exists_orderIso_of_subset hU₁ e₁ (hV₁.inter hU₂) Set.inter_subset_left hMn
  obtain ⟨W', hW', hW'n, ⟨f₂⟩⟩ :=
    exists_orderIso_of_subset hW e₂.symm (hV₁.inter hU₂) Set.inter_subset_right hMn
  exact ⟨U', W', hU', hW', hU'n, hW'n, ⟨f₁.trans f₂.symm⟩⟩

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

/-- **A strictly monotone map of a final segment onto a final segment is eventually the
identity.**  Let `I` be a well-order in which every countable set is bounded above, and let
`f : I → I` be strictly monotone on `Set.Ici a` with image exactly `Set.Ici b` (surjectivity onto
the final segment is a hypothesis; cofinality alone would not do).  Then `f` is the identity on a
final segment: the corestriction is an order isomorphism `Set.Ici a ≃o Set.Ici b`, to which
`iciIsoEventuallyIdTarget` applies. -/
theorem exists_forall_ge_eq_of_strictMonoOn {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (hbdd : ∀ s : Set I, s.Countable → BddAbove s) {a b : I} {f : I → I}
    (hf : StrictMonoOn f (Set.Ici a)) (himg : f '' Set.Ici a = Set.Ici b) :
    ∃ γ, a ≤ γ ∧ b ≤ γ ∧ ∀ δ, γ ≤ δ → f δ = δ := by
  let g : Set.Ici a → Set.Ici b := fun x ↦ ⟨f x, himg ▸ Set.mem_image_of_mem f x.2⟩
  have hg : StrictMono g := fun x y h ↦ hf x.2 y.2 h
  have hgs : Function.Surjective g := fun y ↦ by
    obtain ⟨x, hx, hxy⟩ := (himg.symm ▸ y.2 : (y : I) ∈ f '' Set.Ici a)
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  obtain ⟨γ, haγ, hbγ, hγ⟩ := iciIsoEventuallyIdTarget hbdd (hg.orderIsoOfSurjective g hgs)
  exact ⟨γ, haγ, hbγ, fun δ hδ ↦ hγ δ (haγ.trans hδ) hδ⟩

end VaughtConjecture.Order
