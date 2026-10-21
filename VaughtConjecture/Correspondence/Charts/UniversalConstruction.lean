/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Charts.UniversalSteps
import VaughtConjecture.Stage.Countable

/-!
# The universal chart model: the scheduling and the limit

Native construction throughout.  The statements are in
`VaughtConjecture.Correspondence.Charts.UniversalModel`, the finite steps in
`VaughtConjecture.Correspondence.Charts.UniversalSteps`.

* **The order on conditions** (`UniversalCondition.instPreorder`): `c ≤ d` is
  `UniversalCondition.Extends c d`, reflexive and transitive by `Extends.refl` and `Extends.trans`.
* **The requirements** (`UniversalRequirement α M`): the index
  `M ⊕ Σ k m, (Fin k ↪ M) × StageType α m × (Fin k ↪ Fin m)`, a point of the carrier (the
  enumeration of the carrier) or an exact task (a root tuple, a donor stage type at the stage `α`,
  an embedding of places).  `UniversalRequirement.Met` is the set of conditions meeting it.
* **Countability of the requirements** (`countable_universalRequirement`): when `M` is countable
  and there are countably many ordinals below `α`.  This is the countability of this index at the
  one stage `α`, from the countability of the stage types at `α` (`StageType.countable`); no
  countability of the whole vocabulary `templateLanguage` is used or claimed.  At a block stage
  `λ_β` with `β < ω₁` (`countable_universalRequirement_blockStage`).
* **Density of the requirements** (`UniversalRequirement.exists_le_met`): the point step and the
  exact task step (`universalPointStepTarget`, `universalTaskStepTarget`).
* **The scheduling** (`exists_universalChain`): the Rasiowa–Sikorski lemma
  `Construction.exists_monotone_forall_exists_mem`, from a condition on no points
  (`UniversalCondition.exists_empty`), gives a chain, each condition extending the previous one,
  meeting every requirement.
* **The limit** (`universalChainLimitTarget`): the type of a tuple is its face of the type of any
  condition of the chain whose tuple contains its points; it is well defined because face
  evaluations persist along extensions as `Option`s (`UniversalCondition.Extends.restrictFace_eq`).
  The limit reads every condition literally, undefined faces included:
  `R.eval (h.trans (cs n).W) = restrictFace h (cs n).w` for every `h`, an equality of `Option`s.
  Exact consistency, covering, legal and strongly coded types follow from the conditions; exact
  receiving within the strongly coded legal stage types from the exact tasks, with the donor `D`
  itself as the received type and the empty root included (`k = 0`); finite-cut receiving of the
  strongly coded cofaces from exact receiving
  (`Realization.ExactReceivingWithin.hasFiniteCutReceivingIn_isStronglyCoded`).
* **The positional realization theorem** (`stronglyCodedUniversalRealizationTarget`): for
  `β < ω₁` on a countably infinite carrier, a realization at `λ_β` in the strongly coded receiving
  class with exact receiving of every strongly coded legal donor.  The stronger form
  `exists_stronglyCodedUniversalRealization` also gives the chain read literally.
-/

universe u v

namespace VaughtConjecture

open Finset StageType Ordinal

noncomputable section

/-! ### The order on conditions and a condition on no points -/

namespace UniversalCondition

variable {α : Ordinal.{u}} {M : Type v}

/-- **The order on conditions**: extension with literal root preservation.
Native construction. -/
instance instPreorder : Preorder (UniversalCondition.{u, v} α M) where
  le := Extends
  le_refl := Extends.refl
  le_trans _ _ _ := Extends.trans

theorem le_iff_extends {c d : UniversalCondition.{u, v} α M} : c ≤ d ↔ c.Extends d :=
  Iff.rfl

/-- **A condition on no points**: the empty tuple with the strongly coded legal stage type on no
points (the face on no points of a strongly coded legal one-point type).
Native construction. -/
theorem exists_empty : ∃ c : UniversalCondition.{u, v} α M, c.N = 0 := by
  obtain ⟨d₀, hd₀⟩ := exists_stronglyCodedLegal_onePoint (α := α)
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
    (d₀.isSome_restrictFace_of_zero (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin 1))
  exact ⟨⟨0, Function.Embedding.ofIsEmpty, p,
    ⟨hd₀.1.restrictFace _ hp, isStronglyCoded_of_restrictFace hp hd₀.2⟩⟩, rfl⟩

end UniversalCondition

/-! ### The requirements -/

/-- **The requirements of the universal construction** at a stage `α` on a carrier `M`: a point
of `M` (`inl`), or an exact task (`inr`): a root tuple on `k` points, a donor stage type at `α` on
`m` points and an embedding of places.  Native construction. -/
abbrev UniversalRequirement (α : Ordinal.{u}) (M : Type v) :=
  M ⊕ Σ k m : ℕ, (Fin k ↪ M) × StageType.{u} α m × (Fin k ↪ Fin m)

/-- **The conditions meeting a requirement**: those whose tuple contains the point, or at which the
exact task is done.  Native construction. -/
def UniversalRequirement.Met {α : Ordinal.{u}} {M : Type v} :
    UniversalRequirement.{u, v} α M → Set (UniversalCondition.{u, v} α M)
  | .inl a => {c | a ∈ Set.range c.W}
  | .inr ⟨_, _, t, D, g⟩ => {c | c.ExactTaskDone t D g}

/-- **The requirements at a stage are countable**, for a countable carrier and countably many
ordinals below the stage: only the stage types at this one stage are counted
(`StageType.countable`).  Native construction. -/
theorem countable_universalRequirement {α : Ordinal.{u}} {M : Type v} [Countable M]
    (hα : (Set.Iio α).Countable) : Countable (UniversalRequirement.{u, v} α M) := by
  have : ∀ k, Countable (Fin k ↪ M) := fun k ↦
    Function.Injective.countable (f := fun e : Fin k ↪ M ↦ (e : Fin k → M)) DFunLike.coe_injective
  have := StageType.countable hα
  infer_instance

/-- **The requirements at a block stage `λ_β`, `β < ω₁`, are countable**, on a countable carrier.
Native construction. -/
theorem countable_universalRequirement_blockStage {β : Ordinal.{u}} {M : Type v} [Countable M]
    (hβ : β < ω₁) : Countable (UniversalRequirement.{u, v} (blockStage β) M) :=
  countable_universalRequirement
    (Cardinal.countable_Iio_of_lt_omega_one (blockStage_lt_omega_one hβ))

/-- **Every requirement is dense**: at a stage that is zero or a limit, on an infinite carrier,
every condition extends to one meeting a given requirement.  Native construction. -/
theorem UniversalRequirement.exists_le_met {α : Ordinal.{u}} {M : Type v}
    (hα : Order.IsSuccPrelimit α) (hM : Infinite M) (r : UniversalRequirement.{u, v} α M)
    (c : UniversalCondition.{u, v} α M) : ∃ d ∈ UniversalRequirement.Met r, c ≤ d := by
  rcases r with a | ⟨k, m, t, D, g⟩
  · obtain ⟨d, hcd, hd⟩ := universalPointStepTarget α M hα c {a}
    exact ⟨d, hd a (Finset.mem_singleton_self a), hcd⟩
  · obtain ⟨d, hcd, hd⟩ := universalTaskStepTarget α M hα hM c t D g
    exact ⟨d, hd, hcd⟩

/-! ### The scheduling -/

/-- **The scheduling** (Rasiowa–Sikorski, `Construction.exists_monotone_forall_exists_mem`): at a
stage that is zero or a limit with countably many ordinals below it, on a countably infinite
carrier, a chain of conditions, each extending the previous one, meets every point requirement and
every exact task.  Native construction. -/
theorem exists_universalChain {α : Ordinal.{u}} {M : Type v} [Countable M]
    (hα : Order.IsSuccPrelimit α) (hcount : (Set.Iio α).Countable) (hM : Infinite M) :
    ∃ cs : ℕ → UniversalCondition.{u, v} α M, (∀ n, (cs n).Extends (cs (n + 1))) ∧
      (∀ a : M, ∃ n, a ∈ Set.range (cs n).W) ∧
      (∀ ⦃k m : ℕ⦄ (t : Fin k ↪ M) (D : StageType.{u} α m) (g : Fin k ↪ Fin m),
        ∃ n, (cs n).ExactTaskDone t D g) := by
  have := countable_universalRequirement (M := M) hcount
  obtain ⟨c₀, -⟩ := UniversalCondition.exists_empty (α := α) (M := M)
  obtain ⟨cs, -, hmono, hmeet⟩ := Construction.exists_monotone_forall_exists_mem c₀
    (fun r : UniversalRequirement.{u, v} α M ↦ UniversalRequirement.Met r)
    fun r c _ ↦ UniversalRequirement.exists_le_met hα hM r c
  exact ⟨cs, fun n ↦ hmono (Nat.le_succ n), fun a ↦ hmeet (.inl a),
    fun k m t D g ↦ hmeet (.inr ⟨k, m, t, D, g⟩)⟩

/-! ### The limit -/

section Limit

variable (α : Ordinal.{u}) (M : Type v)

/-- **The limit of a chain of conditions holds** (`UniversalChainLimitTarget α M`): the realization
reading every condition of the chain literally, undefined faces included, is in the strongly
coded receiving class with exact receiving of every strongly coded legal donor (the donor itself
received, the empty root included).  No premise on the stage or the carrier.
Native construction. -/
theorem universalChainLimitTarget : UniversalChainLimitTarget α M := by
  intro cs hsucc hpt htask
  have hmono : Monotone cs := monotone_nat_of_le_succ hsucc
  -- every tuple is a face of the tuple of some condition of the chain
  have hface {k : ℕ} (t : Fin k ↪ M) : ∃ n, ∃ h : Fin k ↪ Fin (cs n).N, h.trans (cs n).W = t := by
    choose nf hnf using fun j : Fin k ↦ hpt (t j)
    refine ⟨Finset.univ.sup nf, Realization.exists_trans_eq_of_forall_mem_range fun j ↦ ?_⟩
    exact UniversalCondition.Extends.range_subset
      (hmono (Finset.le_sup (f := nf) (Finset.mem_univ j))) (hnf j)
  -- faces along different conditions agree, as `Option`s
  have hwd {k : ℕ} {t : Fin k ↪ M} {n n' : ℕ} {h : Fin k ↪ Fin (cs n).N}
      {h' : Fin k ↪ Fin (cs n').N} (hh : h.trans (cs n).W = t) (hh' : h'.trans (cs n').W = t) :
      restrictFace h' (cs n').w = restrictFace h (cs n).w := by
    rcases le_total n n' with hnn | hnn
    · exact UniversalCondition.Extends.restrictFace_eq (hmono hnn) hh hh'
    · exact (UniversalCondition.Extends.restrictFace_eq (hmono hnn) hh' hh).symm
  let R : Realization.{u, v} α M :=
    ⟨fun t ↦ restrictFace (hface t).choose_spec.choose (cs (hface t).choose).w⟩
  have hR {k : ℕ} {t : Fin k ↪ M} {n : ℕ} {h : Fin k ↪ Fin (cs n).N}
      (hh : h.trans (cs n).W = t) : R.eval t = restrictFace h (cs n).w :=
    hwd hh (hface t).choose_spec.choose_spec
  -- exact receiving of the strongly coded legal donors
  have hexact : R.ExactReceivingWithin
      fun m ↦ {D : StageType.{u} α m | D.IsStronglyCodedLegal} := by
    intro k m t c hc D g hD hg
    obtain ⟨hcinj, hct⟩ := hc
    obtain ⟨n, h, hh, hdone⟩ := htask ⟨c, hcinj⟩ D g
    obtain ⟨i, hi, hiD⟩ := hdone t ((hR hh).symm.trans hct) hD hg
    refine ⟨i.trans (cs n).W, ⟨(i.trans (cs n).W).injective, (hR rfl).trans hiD⟩, ?_⟩
    funext j
    exact DFunLike.congr_fun hi j
  refine ⟨R, ⟨?_, ?_, ?_, ?_, hexact.hasFiniteCutReceivingIn_isStronglyCoded⟩, hexact,
    fun n k h ↦ hR rfl⟩
  · -- exact consistency
    intro m k t p f hp
    obtain ⟨n, h, hh⟩ := hface t
    rw [hR hh] at hp
    rw [hR (h := f.trans h) (by rw [← hh]; rfl), restrictFace_trans (cs n).w h f hp]
  · -- covering
    intro k t
    obtain ⟨n, h, hh⟩ := hface t
    refine ⟨_, (cs n).W, h, hh, ?_⟩
    rw [hR (t := (cs n).W) (h := Function.Embedding.refl _) rfl, restrictFace_refl]
    rfl
  · -- legal types
    intro k t p hp
    obtain ⟨n, h, hh⟩ := hface t
    rw [hR hh] at hp
    exact (cs n).isStronglyCodedLegal.1.restrictFace h hp
  · -- strongly coded types
    intro k t p hp
    obtain ⟨n, h, hh⟩ := hface t
    rw [hR hh] at hp
    exact isStronglyCoded_of_restrictFace hp (cs n).isStronglyCodedLegal.2

end Limit

/-! ### The positional realization theorem -/

/-- **The strongly coded universal realization, with its chain** (native construction): for
`β < ω₁` on a countably infinite carrier, a chain of conditions at `λ_β` and a realization in the
strongly coded receiving class, with exact receiving of every strongly coded legal donor, reading
every condition of the chain literally (undefined faces included). -/
theorem exists_stronglyCodedUniversalRealization {β : Ordinal.{u}} {M : Type v} [Countable M]
    (hβ : β < ω₁) (hM : Infinite M) :
    ∃ (cs : ℕ → UniversalCondition.{u, v} (blockStage β) M)
      (R : Realization.{u, v} (blockStage β) M), (∀ n, (cs n).Extends (cs (n + 1))) ∧
      R.IsStronglyCodedReceiving ∧
      R.ExactReceivingWithin
        (fun m ↦ {D : StageType.{u} (blockStage β) m | D.IsStronglyCodedLegal}) ∧
      ∀ (n : ℕ) ⦃k : ℕ⦄ (h : Fin k ↪ Fin (cs n).N),
        R.eval (h.trans (cs n).W) = restrictFace h (cs n).w := by
  obtain ⟨cs, hsucc, hpt, htask⟩ := exists_universalChain (isSuccPrelimit_blockStage β)
    (Cardinal.countable_Iio_of_lt_omega_one (blockStage_lt_omega_one hβ)) hM
  obtain ⟨R, hR, hex, hread⟩ := universalChainLimitTarget (blockStage β) M cs hsucc hpt htask
  exact ⟨cs, R, hsucc, hR, hex, hread⟩

/-- **The positional realization theorem** (`StronglyCodedUniversalRealizationTarget β M` holds):
for `β < ω₁` on a countably infinite carrier, a realization at `λ_β` in the strongly coded
receiving class with exact receiving of every strongly coded legal donor, built by the scheduling
of this file, from no given structure of `K_β[L]`.  Native construction. -/
theorem stronglyCodedUniversalRealizationTarget (β : Ordinal.{u}) (M : Type v) :
    StronglyCodedUniversalRealizationTarget β M := by
  intro hβ _ hM
  obtain ⟨-, R, -, hR, hex, -⟩ := exists_stronglyCodedUniversalRealization (M := M) hβ hM
  exact ⟨R, hR, hex⟩

end

end VaughtConjecture
