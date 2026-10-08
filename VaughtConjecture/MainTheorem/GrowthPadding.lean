/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthExactCarrier
import VaughtConjecture.MainTheorem.CoatomExtensionTheorem

/-!
# Padding the empty root

Roadmap, Layer 3 ((R3), the empty cover).

The relative lift of the growth construction reads the donor through its root face, which must be
a graded face: the root has a point.  (R3) asks exact receiving over every cover, the empty one
included.  The empty cover is **padded** (`Realization.HollowReceiving.of_pos`): over an occurrence
`x` of positive arity, the exact pinned extension at the limit stage gives a legal type `Q` with
face `x.type` along the first points and face `D` along the new point alone (the empty face of
`x.type` is closed); receiving `Q` exactly over `x` and restricting to the new point receives `D`
over the empty cover.  No clause of a model beyond exact consistency and the receiving of positive
covers is used.

## Main statements

* `Realization.HollowReceivingPos H`: (R3) for `H` over covers of positive arity.
* `Realization.HollowReceiving.of_pos`: it gives (R3) for `H` over every cover.
-/

universe u w

namespace VaughtConjecture

open Finset StageType

namespace Realization

/-- **(R3) over positive covers**: the statement of `HollowReceiving H` asked only over covers of
positive arity. -/
structure HollowReceivingPos (H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop) :
    Prop where
  /-- Over every cover of positive arity, every one-point coface is received exactly. -/
  exists_covers ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄ :
    Order.IsSuccLimit α → R.IsModel → H R → R.topGradeSup = ⊤ →
      ∀ ⦃n : ℕ⦄, 0 < n → ∀ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
        ∀ D ∈ t.cofaces, ∃ y : M, R.Covers D (Fin.snoc c y)

/-- **Padding**: (R3) over positive covers gives (R3) over every cover.  Over the empty cover, a
coface `D` of the empty type is received over an occurrence of positive arity through a legal
type with that occurrence and `D` as faces, and restricted to the new point. -/
theorem HollowReceiving.of_pos {H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop}
    (h : HollowReceivingPos.{u, w} H) : HollowReceiving.{u, w} H where
  exists_covers α M R hα hR hH htop n t c hc D hD := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    swap
    · exact h.exists_covers hα hR hH htop hn t c hc D hD
    -- an occurrence of positive arity
    obtain ⟨x, hx⟩ := hR.exists_le_arity hα.bot_lt 1
    have hxpos : 0 < x.arity := hx
    -- the empty face of its type is the empty type
    let f : Fin 0 ↪ Fin x.arity := Function.Embedding.ofIsEmpty
    obtain ⟨p₀, hp₀⟩ := Option.isSome_iff_exists.mp (x.type.isSome_restrictFace_of_zero f)
    have htp : t = p₀ := by
      have h1 := Realization.eval_face hR.isConsistent x f
      rw [hp₀] at h1
      have h2 : R.eval (f.trans x.tuple) = R.eval ⟨c, hc.injective⟩ := by
        congr 1
        ext i
        exact i.elim0
      rw [h2, hc.eval_eq] at h1
      exact Option.some_injective _ h1
    subst htp
    -- the legal type with faces `x.type` and `D`
    obtain ⟨Q, hQ, hQx, hQD⟩ := exists_pinned_extension_of_isSuccPrelimit hα.isSuccPrelimit
      (hR.isLegal _ _ x.eval_tuple) hp₀ hD.1 hD.2
    have hQc : Q ∈ x.type.cofaces := ⟨hQ, hQx⟩
    obtain ⟨y, hy⟩ := h.exists_covers hα hR hH htop hxpos x.type x.tuple
      (covers_of_eval _ x.eval_tuple) Q hQc
    refine ⟨y, ?_⟩
    -- restrict to the new point
    have hy' := hy.eval_eq
    have hres := hR.isConsistent _ Q (extendByLast f) hy'
    rw [hQD] at hres
    refine ⟨?_, ?_⟩
    · intro i j _
      exact Fin.ext (by omega)
    · rw [← hres]
      congr 1
      ext i
      obtain rfl : i = Fin.last 0 := Fin.ext (by omega)
      simp only [Function.Embedding.coeFn_mk, Function.Embedding.trans_apply, extendByLast_last]
      change Fin.snoc (α := fun _ ↦ M) c y (Fin.last 0) =
        Fin.snoc (α := fun _ ↦ M) (⇑x.tuple) y (Fin.last x.arity)
      rw [Fin.snoc_last, Fin.snoc_last]

end Realization

end VaughtConjecture
