/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Receiving

/-!
# Examples: receiving for the reconstructed realization of a classical limit

Special cases of `VaughtConjecture.ClassicalLimit.Receiving` (roadmap, the top-free witnesses,
step 6).  Every statement below about a structure `M` assumes that its age is the age of top-free
charts and that it is ultrahomogeneous, or that it is a Fraïssé limit of the age of top-free
charts; none assumes the coatom extension property or modelhood.

* **The empty root**: the empty tuple is typed, every legal stage type on one point is a coface of
  its type, and it is received over the empty tuple at every permitted cutoff.
* **A donor with a top label**: no reconstructed type has a top label, so the donor itself is
  never the received type; for every received occurrence there is a higher permitted cutoff that
  it does not serve, so receiving at two cutoffs can need two different occurrences.
* **A donor with bottom labels**: at every permitted cutoff, the received type is bottom exactly
  where the donor is.
* **A top-free donor** is received exactly.
* **The base stage**: for a Fraïssé limit at a limit stage `α ≥ ω`, the reduction of the
  reconstructed realization to `ω` has finite-cut receiving and finite-extension receiving.  This
  is the receiving clause of the density sentence for that reduction; the density sentence itself
  and modelhood are not claimed.

## Placement

This file belongs to the section on the top-free witnesses of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open FirstOrder Language Structure Label Realization StageType
open scoped Ordinal

variable {α : Ordinal.{u}} {M : Type} [(hullLanguage.{u} α).Structure M]

section Receiving

variable (hage : (hullLanguage.{u} α).age M = topFreeAge α)
  (hu : (hullLanguage.{u} α).IsUltrahomogeneous M)
include hage hu

/-! ### The empty root -/

/-- **The empty root**: at a stage that is zero or a limit, every legal stage type on one point is
received over the empty tuple at every permitted cutoff.  The empty tuple has a type, the face on
no points of a top-free chart, and the face on no points of the donor is that type, the only stage
type on no points. -/
example (hα : Order.IsSuccPrelimit α) (d : StageType.{u} α 1) (hd : d.IsLegal) {c : Label.{u}}
    (hc : IsPermittedCutoff α c) :
    (reconstruct α M).RealizesOver (Function.Embedding.ofIsEmpty : Fin 0 ↪ M)
      (receivingFamily d c) := by
  obtain ⟨i, e, b, hb⟩ :=
    exists_eq_trans_topFreeChart hage.subset (Function.Embedding.ofIsEmpty : Fin 0 ↪ M)
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (i.2.1.isSome_restrictFace_of_zero b)
  have ht : (reconstruct α M).eval (Function.Embedding.ofIsEmpty : Fin 0 ↪ M) = some p := by
    rw [← hb, reconstruct_eval_trans_chart i.2.2.1 e b, faceRealization_eval, hp]
  obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (d.isSome_restrictFace_of_zero Fin.castSuccEmb)
  exact hasFiniteCutReceiving_reconstruct hage hu hα ⟨0, _, p, ht⟩ d
    ⟨hd, hp'.trans (congrArg some (eq_of_zero p' p))⟩ c hc

/-! ### A donor with a top label -/

/-- **The top label is never recovered**: a donor with a top label is the type of no tuple. -/
example {n : ℕ} {v : Fin n ↪ M} {q d : StageType.{u} α n} (hv : (reconstruct α M).eval v = some q)
    {i : Fin d.card} (hi : d.label i = ⊤) : q ≠ d := by
  rintro rfl
  exact isTopFree_of_reconstruct_eval hage.subset hv i hi

omit hu in
/-- **No occurrence serves every cutoff** for a donor with a top label: at a limit stage, for every
typed tuple whose type is on the scheme of the donor there is a permitted cutoff at which its type
does not agree with the donor.  Its label at the top cell of the donor is at most an ordinal
`o < α`; at a cutoff above `o` that label is below the cutoff, and the top label is not. -/
private theorem exists_not_mem_receivingFamily_of_label_eq_top (hα : Order.IsSuccPrelimit α)
    (h0 : 0 < α) {n : ℕ} {v : Fin n ↪ M} {q d : StageType.{u} α n}
    (hv : (reconstruct α M).eval v = some q) {i : Fin d.card} (hi : d.label i = ⊤) :
    ∃ δ < α, q ∉ receivingFamily d (δ : Label.{u}) := by
  obtain ⟨o, ho, hqo⟩ := (isTopFree_of_reconstruct_eval hage.subset hv).exists_label_le h0
  obtain ⟨δ, hoδ, hδα, -⟩ := exists_lt_lt_isSelfVisible hα ho 0
  refine ⟨δ, hδα, fun hq ↦ ?_⟩
  have hk : (i : ℕ) < q.card := i.2.trans_eq (congrArg Scheme.card hq.1.symm)
  have h := hq.2 ⟨i, hk⟩ i rfl
  have hlt : q.label ⟨i, hk⟩ < (δ : Label.{u}) :=
    (hqo _).trans_lt (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hoδ))
  rw [hi, min_eq_right le_top, min_eq_left hlt.le] at h
  exact hlt.ne h

/-- **Two cutoffs, two occurrences**: at a limit stage, for a donor with a top label and a permitted
cutoff `δ`, there is a higher permitted cutoff `δ'` such that the occurrences received at `δ` and
at `δ'` are different, although both extend the root literally. -/
example (hα : Order.IsSuccPrelimit α) (x : (reconstruct α M).Occurrence) {d : StageType.{u} α _}
    (hd : d ∈ x.type.cofaces) {i : Fin d.card} (hi : d.label i = ⊤) {δ : Ordinal.{u}}
    (hδ : δ < α) :
    ∃ δ' : Ordinal.{u}, δ < δ' ∧ δ' < α ∧ ∃ v v' : Fin (x.arity + 1) ↪ M, v ≠ v' ∧
      Fin.castSuccEmb.trans v = x.tuple ∧ Fin.castSuccEmb.trans v' = x.tuple ∧
      (∃ q ∈ receivingFamily d (δ : Label.{u}), (reconstruct α M).eval v = some q) ∧
      ∃ q' ∈ receivingFamily d (δ' : Label.{u}), (reconstruct α M).eval v' = some q' := by
  have hrec := hasFiniteCutReceiving_reconstruct hage hu hα
  obtain ⟨v, hv, q, hq, hvq⟩ := hrec x d hd δ (isPermittedCutoff_coe.mpr hδ)
  obtain ⟨c, hcα, hqc⟩ := exists_not_mem_receivingFamily_of_label_eq_top hage hα
    (pos_of_gt hδ) hvq hi
  have hq' : q ∉ receivingFamily d ((max δ c : Ordinal.{u}) : Label.{u}) := fun h ↦
    hqc (mem_receivingFamily_of_le h (by exact_mod_cast le_max_right δ c))
  obtain ⟨v', hv', q', hq'', hvq'⟩ :=
    hrec x d hd _ (isPermittedCutoff_coe.mpr (max_lt hδ hcα))
  refine ⟨max δ c, lt_of_le_of_ne (le_max_left δ c) fun h ↦ hq' (h ▸ hq), max_lt hδ hcα, v, v',
    ?_, hv, hv', ⟨q, hq, hvq⟩, q', hq'', hvq'⟩
  rintro rfl
  exact hq' (Option.some_injective _ (hvq.symm.trans hvq') ▸ hq'')

/-! ### A donor with bottom labels -/

/-- **Bottom labels are received**: at a stage that is zero or a limit, over every occurrence and
at every permitted cutoff, a coface is received by an occurrence whose type is bottom exactly where
the coface is.  A permitted cutoff is not bottom, so agreement below it keeps the bottom labels. -/
example (hα : Order.IsSuccPrelimit α) (x : (reconstruct α M).Occurrence) {d : StageType.{u} α _}
    (hd : d ∈ x.type.cofaces) {c : Label.{u}} (hc : IsPermittedCutoff α c) :
    ∃ v : Fin (x.arity + 1) ↪ M, Fin.castSuccEmb.trans v = x.tuple ∧
      ∃ q : StageType.{u} α (x.arity + 1), (reconstruct α M).eval v = some q ∧
        q.toScheme = d.toScheme ∧
        ∀ (i : Fin q.card) (j : Fin d.card), (i : ℕ) = j → (q.label i = ⊥ ↔ d.label j = ⊥) := by
  obtain ⟨v, hv, q, hq, hvq⟩ := hasFiniteCutReceiving_reconstruct hage hu hα x d hd c hc
  refine ⟨v, hv, q, hvq, hq.1, fun i j hij ↦ ?_⟩
  simpa only [eq_iff_iff, min_eq_bot, hc.1.ne', or_false] using congrArg (· = ⊥) (hq.2 i j hij)

/-! ### A top-free donor -/

/-- **A top-free donor is received exactly**: over every occurrence, every top-free coface of its
type is the type of an extension of the occurrence by one point.  No hypothesis on the stage is
needed. -/
example (x : (reconstruct α M).Occurrence) {d : StageType.{u} α _} (hd : d ∈ x.type.cofaces)
    (hdt : d.IsTopFree) : (reconstruct α M).RealizesOver x.tuple {d} :=
  let ⟨v, hv, hvd⟩ := exists_reconstruct_eval_eq_of_isTopFree hage hu x.eval_tuple hd.1 hdt hd.2
  ⟨v, hv, d, rfl, hvd⟩

end Receiving

/-! ### The base stage -/

/-- **The base stage**: for a Fraïssé limit of the age of top-free charts at a limit stage `α ≥ ω`,
the reduction of the reconstructed realization to `ω` has finite-cut receiving, by receiving at `α`
and its descent along stage reduction, cutoff by cutoff.  This is the receiving clause of the
density sentence for that reduction; modelhood is not claimed. -/
example [Countable (Σ l, (hullLanguage.{u} α).Functions l)] [Countable M]
    (hα : Order.IsSuccPrelimit α) (hωα : ω ≤ α) (hM : IsFraisseLimit (topFreeAge.{u} α) M) :
    ((reconstruct α M).reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).HasFiniteCutReceiving :=
  (hasFiniteCutReceiving_reconstruct_of_isFraisseLimit hα hM).reduce hα _ hωα

/-- **The base stage, several new points**: the reduction to `ω` is exactly consistent as well, so
it has finite-extension receiving. -/
example [Countable (Σ l, (hullLanguage.{u} α).Functions l)] [Countable M]
    (hα : Order.IsSuccPrelimit α) (hωα : ω ≤ α) (hM : IsFraisseLimit (topFreeAge.{u} α) M) :
    ((reconstruct α M).reduce
      Ordinal.isSuccLimit_omega0.isSuccPrelimit).HasFiniteExtensionReceiving :=
  ((hasFiniteCutReceiving_reconstruct_of_isFraisseLimit hα hM).reduce hα _ hωα
    ).hasFiniteExtensionReceiving ((isConsistent_reconstruct hM.age.subset).reduce _)
    Ordinal.isSuccLimit_omega0.isSuccPrelimit

end VaughtConjecture
