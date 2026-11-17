/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.ChartChain
import VaughtConjecture.Realization.Closure

/-!
# Reading the realization of a chain of charts

Two facts about a realization `S` on `X` that gives each chart `w k` of a chain its type `T k`
(as the realization of `Realization.ChartChainRealizationTarget` does).

* **Closed sets from closed faces** (`Realization.isClosed_of_chartChain`): a set `C` is closed
  for the canonical closure of `S` when every finite subset of `C` lies in the points of a closed
  face of some chart whose points lie in `C`.  The points of a closed face form a support of `S`,
  which contains the canonical hull (`finiteHull_subset_of_isSupport`).
* **Old evaluations** (`Realization.eval_trans_of_chartChain`): if the charts contain, along
  old positions `o k`, the tuples of a monotone sequence `c` of occurrences of an exactly
  consistent `R` on `M` exhausting `M`, read in `X` along an embedding `ι`, with the types of the
  occurrences, then `S` gives every tuple of `M`, read in `X`, its evaluation in `R`, `none`
  included.

Both are proved; neither assumes countability.

## Placement

This file belongs to Layer 0 of `roadmap/README.md`, beside
`VaughtConjecture.Realization.ChartChain`; it is used by the blocks of the `ℵ₁` companion
construction.
-/

universe u v w

namespace VaughtConjecture.Realization

variable {α : Ordinal.{u}} {X : Type w} {N : ℕ → ℕ} {w : ∀ k, Fin (N k) ↪ X}
  {T : ∀ k, StageType.{u} α (N k)} {S : Realization.{u, w} α X}

/-- **Closed sets from closed faces of the charts.**  If `S` is exactly consistent and covering
and gives each chart its type, a set `C` such that every finite subset of `C` lies in the points
of a closed face of some chart, those points lying in `C`, is closed for the canonical closure. -/
theorem isClosed_of_chartChain (hS : S.IsConsistent) (hSc : S.IsCovering)
    (hSw : ∀ k, S.eval (w k) = some (T k)) {C : Set X}
    (hC : ∀ F : Finset X, ↑F ⊆ C → ∃ (k r : ℕ) (f : Fin r ↪ Fin (N k)),
      ↑F ⊆ Set.range (f.trans (w k)) ∧ Set.range (f.trans (w k)) ⊆ C ∧
        (StageType.restrictFace f (T k)).isSome) :
    (S.closure hS hSc).IsClosed C := by
  classical
  rw [ClosureOperator.isClosed_iff_closure_le]
  intro y hy
  obtain ⟨F, hF, hyF⟩ := (mem_closure_iff hS hSc).mp hy
  obtain ⟨k, r, f, hFr, hrC, hsome⟩ := hC F hF
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome
  have hsup : S.IsSupport (Finset.univ.map (f.trans (w k))) :=
    ⟨⟨r, f.trans (w k), q, by rw [hS _ _ _ (hSw k), hq]⟩, rfl⟩
  have hcoe : (↑(Finset.univ.map (f.trans (w k))) : Set X) = Set.range (f.trans (w k)) := by
    ext z
    simp
  have hFs : F ⊆ Finset.univ.map (f.trans (w k)) := by
    rw [← Finset.coe_subset, hcoe]
    exact hFr
  have hy' := finiteHull_subset_of_isSupport hS hSc hsup hFs hyF
  rw [← Finset.mem_coe, hcoe] at hy'
  exact hrC hy'

/-- **Old evaluations in the realization of a chain of charts.**  Let `R` on `M` be exactly
consistent, `c` a monotone sequence of occurrences of `R` whose supports exhaust `M`, `ι : M ↪ X`,
and `o k` old positions of chart `k` carrying the tuple of `c k`, read along `ι`, with the type of
`c k`.  If `S` is exactly consistent and gives each chart its type, then `S` gives every tuple of
`M`, read along `ι`, its evaluation in `R`, `none` included. -/
theorem eval_trans_of_chartChain {M : Type v} {R : Realization.{u, v} α M}
    (hR : R.IsConsistent) {c : ℕ → R.Occurrence} (hmono : Monotone c)
    (hex : ∀ a : M, ∃ k, a ∈ (c k).support) {ι : M ↪ X} (hS : S.IsConsistent)
    (hSw : ∀ k, S.eval (w k) = some (T k)) (o : ∀ k, Fin (c k).arity ↪ Fin (N k))
    (ho : ∀ k, (o k).trans (w k) = (c k).tuple.trans ι)
    (hoT : ∀ k, StageType.restrictFace (o k) (T k) = some (c k).type) {n : ℕ}
    (t : Fin n ↪ M) : S.eval (t.trans ι) = R.eval t := by
  choose K hK using hex
  obtain ⟨k, h, hh⟩ : ∃ k, ∃ h : Fin n ↪ Fin (c k).arity, h.trans (c k).tuple = t :=
    ⟨_, (c (Finset.univ.sup fun i ↦ K (t i))).exists_trans_eq fun a ha ↦ by
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp ha
      exact hmono (Finset.le_sup (f := fun i ↦ K (t i)) (Finset.mem_univ i)) (hK (t i))⟩
  have ht : t.trans ι = (h.trans (o k)).trans (w k) := by
    rw [Function.Embedding.trans_assoc, ho, ← Function.Embedding.trans_assoc, hh]
  rw [ht, hS _ _ _ (hSw k), ← StageType.restrictFace_trans _ _ _ (hoT k), ← eval_face hR, hh]

end VaughtConjecture.Realization
