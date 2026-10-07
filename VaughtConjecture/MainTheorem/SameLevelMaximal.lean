/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.LegalAge
import VaughtConjecture.Continuation.Hollow

/-!
# Same-level maximal realization

Roadmap, the section "Reduction to full presentations" (acceptance lemma 1, the same-level
maximal realization) and the section "The intended construction: the finite age and its
classical limit" (the uncapped age of all legal stage types, whose classical limit is the
countable saturated model).

Throughout, `λ_β = blockStage β` is the block stage of a countable `β`, and `λ_{β+1}` is the next
one.  **Acceptance lemma 1** (`exists_sameLevelMaximal`): on every countably infinite carrier
`X` there is a realization `H` at `λ_β` that

* is a model (`Realization.IsModel`);
* realizes every legal stage type at `λ_β` (`Realization.Covers`);
* has exact receiving of every legal donor over every actual root
  (`Realization.ExactReceivingWithin` for the family of all legal stage types), the received type
  being the donor itself, with no cutoff;
* is cover-hollow (`Realization.IsCoverHollow`) and terminal at `β` (`Realization.IsTerminalAt`):
  no model at `λ_{β+1}` on `X` reduces to it.

The strengthening on a prescribed tuple (`exists_sameLevelMaximal_covers`): for a legal stage
type `p` on `n` points and an injective tuple `a` of `X`, `H` can be chosen with `a` a cover of
`p`.

Without terminality, the countable saturated realization (`exists_saturated_reconstruct`: a model
realizing every legal stage type, with exact receiving of legal donors) needs only the first of
the two hypotheses below.  Acceptance lemma 1 is conditional on two named hypotheses, each still
to be proved:

* `StageType.HasApexCoatomExtensions (blockStage β)`, the coatom extension property with apex at
  `λ_β` (Layer 3, 3.1, the open part of (R6)).  Its plain form gives the amalgamation of legal
  stage types, hence the classical limit of the age of all legal charts; the apex gives the
  dominance instances of modelhood ([Kni26, Lemma 4.4.3]).
* `ForcingDonors β` (`VaughtConjecture.Continuation.Normalization`; Layer 4, output 2).  It is
  used only at legal stage types at `λ_{β+1}` that are stage types at `λ_β` read at `λ_{β+1}`
  (`StageType.castLE`): at a cell labelled the formal top, every threshold is forced by some legal
  extension (`StageType.exists_forcesThreshold_of_label_eq_top`).

Neither the continuation criterion (`ContinuationCriterion`), nor finite-cut receiving of models
((R1), `Expansion.FiniteCutReceiving`), nor uniqueness of expansions, nor global termination is
used.  The continuation criterion is a sufficiency statement: it makes models at `λ_ξ`, `ξ < ω₁`,
that are not cover-hollow and have unbounded top-grade growth (`Realization.topGradeSup = ⊤`)
continue, and says nothing about cover-hollow ones.  Terminality of a cover-hollow realization is
proved directly, with no hypothesis.

**The route.**  The realization is the reconstruction of a Fraïssé limit of the age of legal
charts, the uncapped age (`legalAge`, `exists_isFraisseLimit_legalAge`,
`isModel_reconstruct_of_legalAge`, `exactReceivingWithin_reconstruct_of_legalAge`, in
`VaughtConjecture.ClassicalLimit.LegalAge`).  Exact receiving of legal donors makes it cover-hollow
under forcing donors (`Realization.isCoverHollow_of_exactReceivingWithin`), and every cover-hollow
realization at a block stage is terminal, with no hypothesis
(`Realization.IsCoverHollow.isTerminalAt`); both are in `VaughtConjecture.Continuation.Hollow`.

**Countability and the carrier.**  The limit is countable (classical existence) and infinite
(`Realization.IsModel.infinite`), so it is in bijection with any countably infinite `X`, and
every property above is invariant under transport along a bijection of carriers
(`Realization.isModel_map_iff`, `Realization.exactReceivingWithin_map_iff`,
`Realization.covers_map_iff`; cover-hollowness and terminality are proved for the transport
directly).  For the prescribed tuple, the bijection is chosen to carry a cover of `p` in the limit
to `a` (`exists_equiv_extend_tuple`, from `Cardinal.extend_function_of_lt`).

**Not here.**  Unbounded top-grade growth (`Realization.topGradeSup = ⊤`) of the realization is
not proved and not used: it needs legal stage types of arbitrarily large top grade.  Nothing here
identifies the base reduct of `H` or places it in a successor loss of the expansion domains;
that needs uniqueness of model expansions at `λ_β` (Layer 5).

## Placement

This file belongs to the section "Reduction to full presentations" of `roadmap/README.md`.

## References

Models are [Kni26, Definition 3.2.1]; the nonemptiness of the uniformity and dominance instances is
[Kni26, Lemmas 4.4.2 and 4.4.3]; the countable saturated model is [Kni26, Definition 4.1.1 and
Proposition 4.4.5].
-/

universe v

namespace VaughtConjecture

open FirstOrder Language Realization
open scoped Ordinal

/-! ### Acceptance lemma 1 -/

/-- **The countable saturated realization at a block stage**, conditional on the coatom extension
property with apex at `λ_β`: for a countable `β`, some countable structure `M` of the hull language
at `λ_β` has a reconstructed realization that is a model, realizes every legal stage type at
`λ_β`, and has exact receiving of every legal donor.  `M` is a Fraïssé limit of the age of legal
charts.

The coatom extension property with apex `StageType.HasApexCoatomExtensions (blockStage β)` is
still to be proved: it is the open part of statement (R6) of roadmap, Layer 3, 3.1. -/
theorem exists_saturated_reconstruct {β : Ordinal.{0}} (hβ : β < ω₁)
    (hext : StageType.HasApexCoatomExtensions.{0} (blockStage β)) :
    ∃ (M : Type) (_ : (hullLanguage.{0} (blockStage β)).Structure M), Countable M ∧
      (reconstruct (blockStage β) M).IsModel ∧
      (∀ ⦃n : ℕ⦄ (p : StageType.{0} (blockStage β) n), p.IsLegal →
        ∃ c : Fin n → M, (reconstruct (blockStage β) M).Covers p c) ∧
      (reconstruct (blockStage β) M).ExactReceivingWithin
        (fun m ↦ {D : StageType.{0} (blockStage β) m | D.IsLegal}) := by
  have hcount := Cardinal.countable_Iio_of_lt_omega_one (blockStage_lt_omega_one hβ)
  let := hullLanguage.countable_functions hcount
  obtain ⟨M, hMc, hM⟩ := exists_isFraisseLimit_legalAge hext.hasCoatomExtensions hcount
  exact ⟨M, inferInstance, hMc,
    isModel_reconstruct_of_legalAge hext hM.age hM.ultrahomogeneous (isSuccLimit_blockStage β),
    fun _ _ hp ↦ exists_covers_reconstruct_of_legalAge hM.age.symm.subset hp,
    exactReceivingWithin_reconstruct_of_legalAge hM.age hM.ultrahomogeneous⟩

/-- **The same-level maximal realization on the carrier of a classical limit**, conditional on the
coatom extension property with apex at `λ_β` and on forcing donors at `β`: the countable saturated
realization of `exists_saturated_reconstruct` is moreover cover-hollow
(`Realization.isCoverHollow_of_exactReceivingWithin`) and terminal at `β`
(`Realization.IsCoverHollow.isTerminalAt`).

Both hypotheses are still to be proved: `StageType.HasApexCoatomExtensions (blockStage β)` is the
open part of statement (R6) of roadmap, Layer 3, 3.1; `ForcingDonors β` is a finite statement of
Layer 4, output 2. -/
theorem exists_sameLevelMaximal_reconstruct {β : Ordinal.{0}} (hβ : β < ω₁)
    (hext : StageType.HasApexCoatomExtensions.{0} (blockStage β)) (hF : ForcingDonors.{0} β) :
    ∃ (M : Type) (_ : (hullLanguage.{0} (blockStage β)).Structure M), Countable M ∧
      (reconstruct (blockStage β) M).IsModel ∧
      (∀ ⦃n : ℕ⦄ (p : StageType.{0} (blockStage β) n), p.IsLegal →
        ∃ c : Fin n → M, (reconstruct (blockStage β) M).Covers p c) ∧
      (reconstruct (blockStage β) M).ExactReceivingWithin
        (fun m ↦ {D : StageType.{0} (blockStage β) m | D.IsLegal}) ∧
      (reconstruct (blockStage β) M).IsCoverHollow ∧
      (reconstruct (blockStage β) M).IsTerminalAt β := by
  obtain ⟨M, _, hMc, hmod, hocc, hrec⟩ := exists_saturated_reconstruct hβ hext
  have hhol := isCoverHollow_of_exactReceivingWithin hF hasLegalTypes_reconstruct hrec
  exact ⟨M, inferInstance, hMc, hmod, hocc, hrec, hhol, hhol.isTerminalAt⟩

/-- **A bijection of countably infinite types extending a finite injection**: two injective tuples
of the same length in countably infinite types are matched by a bijection.  This is Mathlib's
`Cardinal.extend_function_of_lt` for the finite range of the first tuple. -/
private theorem exists_equiv_extend_tuple {M X : Type v} [Countable M] [Infinite M]
    [Countable X] [Infinite X] {n : ℕ} (c : Fin n ↪ M) (a : Fin n ↪ X) :
    ∃ e : M ≃ X, ∀ i, e (c i) = a i := by
  let f : Set.range c ↪ X :=
    ⟨fun x ↦ a ((Equiv.ofInjective c c.injective).symm x), a.injective.comp (Equiv.injective _)⟩
  have hs : Cardinal.mk (Set.range c) < Cardinal.mk M :=
    (Cardinal.lt_aleph0_iff_finite.mpr (Set.finite_range c).to_subtype).trans_le
      (Cardinal.aleph0_le_mk M)
  obtain ⟨e, he⟩ := Cardinal.extend_function_of_lt f hs nonempty_equiv_of_countable
  refine ⟨e, fun i ↦ (he ⟨c i, i, rfl⟩).trans ?_⟩
  simp [f, Equiv.ofInjective_symm_apply]

/-- **Acceptance lemma 1, the same-level maximal realization**, conditional on the coatom
extension property with apex at `λ_β` and on forcing donors at `β`: for a countable `β` and every
countably infinite carrier `X`, some realization `H` at `λ_β = blockStage β` on `X`

* is a model;
* realizes every legal stage type at `λ_β`;
* has exact receiving of every legal donor over every actual root (the received type is the donor
  itself, with no cutoff);
* is cover-hollow and terminal at `β`: no model at `λ_{β+1}` on `X` reduces to it.

It is the transport to `X` of the reconstruction of a Fraïssé limit of the age of legal charts
(`exists_sameLevelMaximal_reconstruct`).

Both hypotheses are still to be proved: `StageType.HasApexCoatomExtensions (blockStage β)` is the
open part of statement (R6) of roadmap, Layer 3, 3.1; `ForcingDonors β` is a finite statement of
Layer 4, output 2. -/
theorem exists_sameLevelMaximal_covers {β : Ordinal.{0}} (hβ : β < ω₁)
    (hext : StageType.HasApexCoatomExtensions.{0} (blockStage β)) (hF : ForcingDonors.{0} β)
    (X : Type) [Countable X] [Infinite X] {n : ℕ} {p : StageType.{0} (blockStage β) n}
    (hp : p.IsLegal) (a : Fin n ↪ X) :
    ∃ H : Realization.{0, 0} (blockStage β) X, H.IsModel ∧ H.Covers p a ∧
      (∀ ⦃n : ℕ⦄ (p : StageType.{0} (blockStage β) n), p.IsLegal → ∃ c : Fin n → X, H.Covers p c) ∧
      H.ExactReceivingWithin (fun m ↦ {D : StageType.{0} (blockStage β) m | D.IsLegal}) ∧
      H.IsCoverHollow ∧ H.IsTerminalAt β := by
  obtain ⟨M, _, hMc, hmod, hocc, hrec, -, -⟩ := exists_sameLevelMaximal_reconstruct hβ hext hF
  have := hMc
  have := hmod.infinite (Ordinal.omega0_pos.trans_le (omega0_le_blockStage β))
  obtain ⟨c, hc⟩ := hocc p hp
  obtain ⟨e, he⟩ := exists_equiv_extend_tuple ⟨c, hc.injective⟩ a
  have hmod' := (isModel_map_iff e).mpr hmod
  have hrec' := (exactReceivingWithin_map_iff e).mpr hrec
  have hhol := isCoverHollow_of_exactReceivingWithin hF hmod'.hasLegalTypes hrec'
  have hcov (n : ℕ) (q : StageType.{0} (blockStage β) n) (c' : Fin n → M)
      (hq : (reconstruct (blockStage β) M).Covers q c') :
      ((reconstruct (blockStage β) M).map e).Covers q (e ∘ c') :=
    (covers_map_iff e).mpr (by simpa [Function.comp_def] using hq)
  refine ⟨_, hmod', ?_, fun n q hq ↦ ?_, hrec', hhol, hhol.isTerminalAt⟩
  · have ha : e ∘ c = a := funext he
    exact ha ▸ hcov n p c hc
  · obtain ⟨c', hc'⟩ := hocc q hq
    exact ⟨_, hcov n q c' hc'⟩

/-- **Acceptance lemma 1, the same-level maximal realization** (`exists_sameLevelMaximal_covers`
without the prescribed tuple), conditional on the coatom extension property with apex at `λ_β`
and on forcing donors at `β`, both still to be proved: for a countable `β`, every countably
infinite carrier `X` carries a model at `λ_β` that realizes every legal stage type at `λ_β`,
receives every legal donor exactly over every actual root, and is cover-hollow and terminal at
`β`. -/
theorem exists_sameLevelMaximal {β : Ordinal.{0}} (hβ : β < ω₁)
    (hext : StageType.HasApexCoatomExtensions.{0} (blockStage β)) (hF : ForcingDonors.{0} β)
    (X : Type) [Countable X] [Infinite X] :
    ∃ H : Realization.{0, 0} (blockStage β) X, H.IsModel ∧
      (∀ ⦃n : ℕ⦄ (p : StageType.{0} (blockStage β) n), p.IsLegal → ∃ c : Fin n → X, H.Covers p c) ∧
      H.ExactReceivingWithin (fun m ↦ {D : StageType.{0} (blockStage β) m | D.IsLegal}) ∧
      H.IsCoverHollow ∧ H.IsTerminalAt β := by
  obtain ⟨H, hH, -, h⟩ := exists_sameLevelMaximal_covers hβ hext hF X
    (TopFreeIndex.empty (blockStage β)).2.2.1 (Function.Embedding.ofIsEmpty : Fin 0 ↪ X)
  exact ⟨H, hH, h⟩

end VaughtConjecture
