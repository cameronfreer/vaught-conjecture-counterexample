/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.Basic

/-!
# Transport of realizations along bijections and stage reduction

Roadmap, Layer 2 (isomorphism transport and reduction of models; reindexing and stage reduction
identities before dependent transport spreads) and Library conventions (face restriction, stage
reduction, and capped observation are different operations); semantic contract, item 5.

* **Transport.**  A bijection of carriers `e : M ≃ N` carries a realization `R` on `M` to the
  realization `R.map e` on `N` giving a tuple of `N` the type of its preimage
  (`Realization.map_eval_trans`).  Transport is functorial (`map_refl`, `map_map`), so `R.map e`
  is the unique realization on `N` isomorphic to `R` along `e`, and it preserves and reflects
  exact consistency and covering (`isConsistent_map_iff`, `isCovering_map_iff`).
* **Stage reduction.**  At a stage `β` that is zero or a limit, `R.reduce hβ` reduces every
  actual type to stage `β` (`StageType.reduce`) and leaves untyped tuples untyped.  Since stage
  reduction does not change the scheme and commutes with face maps, including definedness
  (`StageType.restrictFace_reduce`), it preserves exact consistency and covering
  (`IsConsistent.reduce`, `IsCovering.reduce`); reductions compose (`reduce_reduce`), reduction to
  the stage of the realization is the identity (`reduce_self`), and reduction commutes with
  transport (`reduce_map`).

## References

Stage reduction of realizations is the reduction of [Kni26, Definition 5.1.1] (unique by
[Kni26, Lemma 5.2.1]), pointwise the vertical map of [Kni26, Definition 3.1.2]; transport along
a bijection of carriers is the relabelling implicit in [Kni26, Definition 3.1.5], for
R. W. Knight, *A counterexample to Vaught's Conjecture using generalised Stone spaces* (draft,
20 February 2026).
-/

universe u v w x

namespace VaughtConjecture.Realization

open Finset

variable {α β γ : Ordinal.{u}} {M : Type v} {N : Type w} {P : Type x} {m n : ℕ}
  {R : Realization.{u, v} α M}

/-! ### Transport along a bijection of carriers -/

section Map

variable (e : M ≃ N) (R)

/-- The **transport** of a realization along a bijection of carriers: a tuple of `N` has the type
of its preimage in `M`. -/
def map : Realization.{u, w} α N where
  eval t := R.eval (t.trans e.symm.toEmbedding)

/-- The evaluation of a transported realization is the evaluation of the preimage. -/
theorem map_eval (t : Fin n ↪ N) : (R.map e).eval t = R.eval (t.trans e.symm.toEmbedding) := rfl

/-- A transported realization gives the image of a tuple the type of the tuple. -/
@[simp] theorem map_eval_trans (t : Fin n ↪ M) :
    (R.map e).eval (t.trans e.toEmbedding) = R.eval t := by
  simp only [map_eval]
  congr 1
  ext i
  simp

/-- Transport along the identity is the identity. -/
@[simp] theorem map_refl : R.map (Equiv.refl M) = R :=
  ext fun t ↦ congrArg R.eval (by ext; simp)

/-- Transport along two bijections is transport along the composite. -/
@[simp] theorem map_map (e' : N ≃ P) : (R.map e).map e' = R.map (e.trans e') :=
  ext fun t ↦ congrArg R.eval (by ext; simp)

/-- Transport back along the inverse bijection recovers the realization. -/
theorem map_symm_map : (R.map e).map e.symm = R := by
  rw [map_map, Equiv.self_trans_symm, map_refl]

/-- Transport along a bijection and then its inverse on the other side recovers the
realization. -/
theorem map_map_symm (R : Realization.{u, w} α N) : (R.map e.symm).map e = R := by
  rw [map_map, Equiv.symm_trans_self, map_refl]

/-- A realization on `N` agreeing with `R` along `e` is the transport of `R`. -/
theorem eq_map_of_eval_trans {R' : Realization.{u, w} α N}
    (h : ∀ {n : ℕ} (t : Fin n ↪ M), R'.eval (t.trans e.toEmbedding) = R.eval t) :
    R' = R.map e :=
  ext fun t ↦ by rw [map_eval, ← h]; exact congrArg R'.eval (by ext; simp)

variable {R e}

/-- Exact consistency is preserved by transport. -/
theorem IsConsistent.map (hR : R.IsConsistent) (e : M ≃ N) : (R.map e).IsConsistent :=
  fun _ _ t p f ht ↦ by
    rw [map_eval, Function.Embedding.trans_assoc]
    exact hR _ p f ht

/-- Covering is preserved by transport. -/
theorem IsCovering.map (hc : R.IsCovering) (e : M ≃ N) : (R.map e).IsCovering := fun _ t ↦ by
  obtain ⟨m, u, f, hf, hu⟩ := hc (t.trans e.symm.toEmbedding)
  refine ⟨m, u.trans e.toEmbedding, f, ?_, by rwa [map_eval_trans]⟩
  ext i
  simpa using congrArg (e ·) (DFunLike.congr_fun hf i)

/-- Exact consistency is preserved and reflected by transport. -/
@[simp] theorem isConsistent_map_iff : (R.map e).IsConsistent ↔ R.IsConsistent :=
  ⟨fun h ↦ map_symm_map R e ▸ h.map e.symm, fun h ↦ h.map e⟩

/-- Covering is preserved and reflected by transport. -/
@[simp] theorem isCovering_map_iff : (R.map e).IsCovering ↔ R.IsCovering :=
  ⟨fun h ↦ map_symm_map R e ▸ h.map e.symm, fun h ↦ h.map e⟩

variable (e) in
/-- The **transport** of an occurrence: the image tuple with the same type. -/
def Occurrence.map (x : R.Occurrence) : (R.map e).Occurrence where
  arity := x.arity
  tuple := x.tuple.trans e.toEmbedding
  type := x.type
  eval_tuple := by rw [map_eval_trans, x.eval_tuple]

/-- The tuple of a transported occurrence is the image tuple. -/
@[simp] theorem Occurrence.map_tuple (x : R.Occurrence) :
    (x.map e).tuple = x.tuple.trans e.toEmbedding := rfl

/-- The type of a transported occurrence is unchanged. -/
@[simp] theorem Occurrence.map_type (x : R.Occurrence) : (x.map e).type = x.type := rfl

end Map

/-! ### Stage reduction -/

section Reduce

variable (R)

/-- **Stage reduction** of a realization to a stage `β` that is zero or a limit: every actual type
is reduced to stage `β`, and untyped tuples stay untyped. -/
noncomputable def reduce (hβ : Order.IsSuccPrelimit β) : Realization.{u, v} β M where
  eval t := (R.eval t).map (StageType.reduce · hβ)

/-- The evaluation of a stage reduction is the reduction of the evaluation. -/
@[simp] theorem reduce_eval (hβ : Order.IsSuccPrelimit β) (t : Fin n ↪ M) :
    (R.reduce hβ).eval t = (R.eval t).map (StageType.reduce · hβ) := rfl

/-- A tuple is typed after stage reduction exactly when it is typed before. -/
theorem isSome_reduce_eval (hβ : Order.IsSuccPrelimit β) (t : Fin n ↪ M) :
    ((R.reduce hβ).eval t).isSome = (R.eval t).isSome := by
  simp

/-- **Coherence of stage reduction**: reducing to `β` and then to a lower stage `γ` is reducing
to `γ`. -/
theorem reduce_reduce (hβ : Order.IsSuccPrelimit β) (hγ : Order.IsSuccPrelimit γ) (hγβ : γ ≤ β) :
    (R.reduce hβ).reduce hγ = R.reduce hγ := by
  refine ext fun t ↦ ?_
  simp [Option.map_map, Function.comp_def, StageType.reduce_reduce _ hβ hγ hγβ]

/-- Reduction to the stage of the realization is the identity. -/
@[simp] theorem reduce_self (hα : Order.IsSuccPrelimit α) : R.reduce hα = R := by
  refine ext fun t ↦ ?_
  simp

/-- Stage reduction commutes with transport along a bijection of carriers. -/
theorem reduce_map (hβ : Order.IsSuccPrelimit β) (e : M ≃ N) :
    (R.map e).reduce hβ = (R.reduce hβ).map e :=
  rfl

variable {R}

/-- Exact consistency is preserved by stage reduction: reduction commutes with face maps,
including definedness. -/
theorem IsConsistent.reduce (hR : R.IsConsistent) (hβ : Order.IsSuccPrelimit β) :
    (R.reduce hβ).IsConsistent := fun _ _ t p f ht ↦ by
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp ht
  rw [reduce_eval, hR t q f hq, StageType.restrictFace_reduce]

/-- Covering is preserved by stage reduction. -/
theorem IsCovering.reduce (hc : R.IsCovering) (hβ : Order.IsSuccPrelimit β) :
    (R.reduce hβ).IsCovering := fun _ t ↦ by
  obtain ⟨m, u, f, hf, hu⟩ := hc t
  exact ⟨m, u, f, hf, by rwa [isSome_reduce_eval]⟩

/-- Covering is preserved and reflected by stage reduction. -/
@[simp] theorem isCovering_reduce_iff (hβ : Order.IsSuccPrelimit β) :
    (R.reduce hβ).IsCovering ↔ R.IsCovering := by
  simp only [IsCovering, isSome_reduce_eval]

/-- The **stage reduction** of an occurrence: the same tuple with the reduced type. -/
noncomputable def Occurrence.reduce (hβ : Order.IsSuccPrelimit β) (x : R.Occurrence) :
    (R.reduce hβ).Occurrence where
  arity := x.arity
  tuple := x.tuple
  type := x.type.reduce hβ
  eval_tuple := by rw [reduce_eval, x.eval_tuple, Option.map_some]

/-- The tuple of a reduced occurrence is unchanged. -/
@[simp] theorem Occurrence.reduce_tuple (hβ : Order.IsSuccPrelimit β) (x : R.Occurrence) :
    (x.reduce hβ).tuple = x.tuple := rfl

/-- The type of a reduced occurrence is the reduced type. -/
@[simp] theorem Occurrence.reduce_type (hβ : Order.IsSuccPrelimit β) (x : R.Occurrence) :
    (x.reduce hβ).type = x.type.reduce hβ := rfl

/-- Every occurrence of a stage reduction is the reduction of an occurrence with the same
tuple. -/
theorem Occurrence.exists_reduce_eq (hβ : Order.IsSuccPrelimit β) (y : (R.reduce hβ).Occurrence) :
    ∃ x : R.Occurrence, x.reduce hβ = y := by
  obtain ⟨n, t, q, hq⟩ := y
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
  exact ⟨⟨n, t, p, hp⟩, rfl⟩

end Reduce

end VaughtConjecture.Realization
