/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.Rank
import VaughtConjecture.Correspondence.Systems.Targets

/-!
# [AFK26, Lemma 2.22]: a countable bound on the ranks of the lifts

Numbering as in the current draft of [AFK26] (the published v1 reads identically).

`WeakSystem.existsRankBoundTarget`: on a countable carrier, an eventually determined
`L_c`-structure `B` has a countable level `α` at which every lift of `B` in the weak system is
fixed.  The proof follows the printed one.

* The closed tuples of `B` are countably many (the carrier is countable); for each, eventual
  determination gives a threshold `α_ā` and an invariant `Q_ā`.  The bound is the supremum of the
  **successors** `α_ā + 1`, a countable ordinal (`InfinitaryLogic.iSup_add_one_lt_omega1`), so
  every threshold is strictly below it, as the strict inequality of [AFK26, Definition 2.21]
  requires.
* A lift at a level `β ≤ α` is fixed at `β`, hence at `α` (`InvariantSystem.IsFixedAt.mono`).
* A lift `G` at a level `β > α`: its projection `τ_α(G)` is a lift at `α`
  (`WeakSystem.projection_mem`, `BaseSublanguage.reduct_projection`).  Both levels exceed every
  threshold, so `G` and `τ_α(G)` carry `Q_ā` on every closed tuple `ā`.  In a structure compatible
  with the diagram an invariant holds only of closed tuples ([AFK26, Definition 2.2 (b)]) and
  distinct invariants of one arity hold of no common tuple (Definition 2.2 (c)), so `G` and
  `τ_α(G)` have the same invariants; the other symbols agree by Definition 2.7.  Hence
  `τ_α(G) = G`.

No uniqueness of maximal lifts, Reconstruction or successor strictness is used.
-/

universe w w' wc wc' v

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal

variable {L : Language.{w, w'}} {σ : GeometrySignature L}

namespace GeometrySignature.BaseSublanguage

variable {Lc : Language.{wc, wc'}} (E : σ.BaseSublanguage Lc)

/-- **An invariant holds only of closed tuples** ([AFK26, Definition 2.2 (b)]): in a structured
geometry `G` with reduct `B`, a tuple of which an invariant holds is a closed tuple of `B`.
Correspondence with the printed definitions. -/
theorem isClosedTuple_of_relMap_invariant {M : Type v} {G : L.Structure M}
    (hG : @IsStructuredGeometry L σ M G) {n : ℕ} {R : L.Relations n} (hR : σ.IsInvariant R)
    {x : Fin n → M} (hx : RelMap (L := L) (self := G) R x) :
    E.IsClosedTuple (E.reduct G) x := by
  have hn := σ.pos_of_relations R
  obtain ⟨r, hr⟩ := (E.mem_range_iff (σ.closed n hn)).mpr (σ.not_isInvariant_closed n hn)
  refine ⟨hn, r, hr, ?_⟩
  change RelMap (L := L) (self := G) (E.incl.onRelation r) x
  rw [hr]
  exact (hG.closed_iff hn x).mpr ⟨R, hR, hx⟩

end GeometrySignature.BaseSublanguage

/-- **Distinct invariants hold of no common tuple** ([AFK26, Definition 2.2 (c)]): two invariants
holding of one tuple in a structured geometry are equal.  Correspondence with the printed
definitions. -/
theorem IsStructuredGeometry.eq_of_relMap {M : Type v} {G : L.Structure M}
    (hG : @IsStructuredGeometry L σ M G) {n : ℕ} {R R' : L.Relations n} (hR : σ.IsInvariant R)
    (hR' : σ.IsInvariant R') {x : Fin n → M} (hx : RelMap (L := L) (self := G) R x)
    (hx' : RelMap (L := L) (self := G) R' x) : R = R' := by
  by_contra hne
  exact hG.exclusive R R' hR hR' hne x hx hx'

namespace WeakSystem

variable {D : InvarianceDiagram σ} {S : InvariantSystem.{0} σ}
variable {Lc : Language.{wc, wc'}} (E : σ.BaseSublanguage Lc)

/-- **[AFK26, Lemma 2.22]** (`ExistsRankBoundTarget`): on a countable carrier, an eventually
determined `L_c`-structure has a countable level at which all its lifts are fixed.  The bound is
the supremum of the successor thresholds `α_ā + 1` over the countably many closed tuples `ā`;
lifts below the bound are fixed by monotonicity, lifts above it by comparison with their
projection to the bound.  Correspondence with the printed definitions. -/
theorem existsRankBoundTarget (W : WeakSystem.{w, w', v} D S) : W.ExistsRankBoundTarget E := by
  intro M _ B hB
  let T := Σ n : ℕ, {a : Fin n → M // E.IsClosedTuple B a}
  have hED (t : T) : ∃ (a : SystemLevel) (q : σ.Invariant t.1), ∀ a' : SystemLevel, a < a' →
      ∀ G : L.Structure M, W.IsLiftAt E a' G B → RelMap (L := L) (self := G) q.1 t.2.1 := by
    obtain ⟨a, q, -, h⟩ := hB t.2.1 t.2.2
    exact ⟨a, q, h⟩
  choose α Q hall using hED
  have ha : (⨆ t, ((α t).1 + 1)) < ω₁ :=
    InfinitaryLogic.iSup_add_one_lt_omega1 (fun t ↦ (α t).1) fun t ↦ (α t).2
  let α₀ : SystemLevel := ⟨⨆ t, ((α t).1 + 1), ha⟩
  have hlt (t : T) : α t < α₀ :=
    show (α t).1 < ⨆ t, ((α t).1 + 1) from
      (Order.lt_add_one_iff.mpr le_rfl).trans_le (Ordinal.le_iSup (fun t ↦ (α t).1 + 1) t)
  refine ⟨α₀, fun β G ⟨hG, hGB⟩ ↦ ?_⟩
  rcases le_or_gt β α₀ with hβ | hβ
  · exact (W.fixed hG).mono hβ
  · have hG' := W.projection_mem hβ hG
    have hG'B : E.reduct (S.projection α₀ G) = B := by rw [E.reduct_projection, hGB]
    have hsG : @IsStructuredGeometry L σ M G := (W.isCompatible hG).1
    have hsG' : @IsStructuredGeometry L σ M (S.projection α₀ G) :=
      @InvarianceDiagram.IsCompatible.isStructuredGeometry L σ D M (S.projection α₀ G)
        (W.isCompatible hG')
    refine σ.structure_ext fun n R x ↦ ?_
    by_cases hR : σ.IsInvariant R
    · constructor
      · intro hx
        have hc := E.isClosedTuple_of_relMap_invariant hsG' hR hx
        rw [hG'B] at hc
        let t : T := ⟨n, x, hc⟩
        have h₁ := hall t α₀ (hlt t) _ ⟨hG', hG'B⟩
        have h₂ := hall t β ((hlt t).trans hβ) G ⟨hG, hGB⟩
        rw [hsG'.eq_of_relMap hR (Q t).2 hx h₁]
        exact h₂
      · intro hx
        have hc := E.isClosedTuple_of_relMap_invariant hsG hR hx
        rw [hGB] at hc
        let t : T := ⟨n, x, hc⟩
        have h₁ := hall t α₀ (hlt t) _ ⟨hG', hG'B⟩
        have h₂ := hall t β ((hlt t).trans hβ) G ⟨hG, hGB⟩
        rw [hsG.eq_of_relMap hR (Q t).2 hx h₂]
        exact h₁
    · exact S.relMap_projection_of_not_isInvariant α₀ G hR x

end WeakSystem

end VaughtConjecture.Correspondence
