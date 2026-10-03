/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.Model

/-!
# The cap-to-model theorem at a limit stage

Roadmap, Layer 3, 3.4 (the cap-to-model theorem); the section on the top-free witnesses, step 7
(modelhood); semantic contract, item 5 (the four unchanged extension families) and item 12 (one
permitted cutoff at a time).

Let `R` be a realization at a nonzero limit stage `α` on a nonempty carrier, with legal types,
exactly consistent and covering, and with the finite-cut receiving property.  Then `R` is a model
(`Realization.isModel_of_hasFiniteCutReceiving`) as soon as, over every occurrence, the
uniformity and dominance instances of the clause of a model have a member among the cofaces of its
type: the hypotheses `hunif` and `hdom`, the instances of [Kni26, Lemmas 4.4.2 and 4.4.3] used.
The conclusion is `Realization.IsModel` with its four families unchanged; no exactness is added to
it.

Each clause receives a member of its instance at one permitted cutoff, and the received type stays
in the family (the receiving family of a member lies in the family):

* **generalized saturation** at the cutoff `0`: the received type has the scheme of the donor
  (`StageType.receivingFamily_subset_saturationFamily`);
* **the bottom pattern** at the cutoff `0`, or any cutoff other than `⊥`: `min x c = ⊥` exactly
  when `x = ⊥` (`StageType.receivingFamily_subset_bottomPatternFamily`);
* **uniformity** at the cutoff `L + 1`, for a member with a label `L` in `[γ, γ + ω)`:
  `min x (L + 1) = L` forces `x = L` (`StageType.receivingFamily_subset_uniformityFamily`);
* **high-arity dominance** at the cutoff `γ + 1`: `min x (γ + 1) = γ + 1` forces `γ < x`, at a
  cell of the same grade, the schemes being equal
  (`StageType.receivingFamily_subset_dominanceFamily`).

The guarded clauses come with their member; the uniformity and dominance clauses are not guarded,
which is why `hunif` and `hdom` are hypotheses.  The cutoffs `L + 1` and `γ + 1` are below the
stage because it is a limit; at stage `0` there is no permitted cutoff, so the stage hypothesis
cannot be dropped (`VaughtConjecture.Realization.ModelExamples`).

**Reducing to `ω` does not suffice.**  The cap-to-model theorem at `ω`, applied to the reduction
of `R` to `ω`, gives modelhood at `ω` only: every label at least `ω` becomes the formal top, so
the uniformity clauses at `ω ≤ γ < α` and the dominance clauses at `γ ≥ ω` are not visible there.
Lifting modelhood from the reductions to lower block stages would need those reductions to be
models already, which for a realization not yet known to be a model is what is to be proved.

## Placement

This file belongs to Layer 3, 3.4, of `roadmap/README.md`.

## References

Models are [Kni26, Definition 3.2.1]; the nonemptiness of the uniformity and dominance instances is
[Kni26, Lemmas 4.4.2 and 4.4.3], for R. W. Knight, *A counterexample to Vaught's Conjecture using
generalised Stone spaces* (draft, 20 February 2026).
-/

universe u v

namespace VaughtConjecture

open Label

namespace StageType

variable {α γ : Ordinal.{u}} {n : ℕ}

/-- The cells of a member of a receiving family correspond to those of the donor, with the same
grade and the same observation at the cutoff. -/
theorem exists_cell_of_mem_receivingFamily {d q : StageType.{u} α n} {c : Label.{u}}
    (hq : q ∈ receivingFamily d c) (j : Fin d.card) :
    ∃ i : Fin q.card, q.toCellScheme.grade i = d.toCellScheme.grade j ∧
      min (q.label i) c = min (d.label j) c := by
  obtain ⟨hS, hl⟩ := hq
  obtain ⟨S, ℓ, _, _, _, _⟩ := q
  obtain ⟨S', ℓ', _, _, _, _⟩ := d
  obtain rfl : S = S' := hS
  exact ⟨j, rfl, hl j j rfl⟩

variable {d : StageType.{u} α (n + 1)}

/-- Receiving keeps the scheme, hence generalized saturation, at every cutoff. -/
theorem receivingFamily_subset_saturationFamily {S : Scheme.{u} (n + 1)}
    (hd : d ∈ saturationFamily S) (c : Label.{u}) : receivingFamily d c ⊆ saturationFamily S :=
  fun _ hq ↦ hq.1.trans hd

/-- Receiving keeps the bottom pattern at every cutoff other than `⊥`. -/
theorem receivingFamily_subset_bottomPatternFamily {S : Scheme.{u} (n + 1)}
    {ρ : Fin S.card → Label.{u}} (hd : d ∈ bottomPatternFamily S ρ) {c : Label.{u}} (hc : c ≠ ⊥) :
    receivingFamily d c ⊆ bottomPatternFamily S ρ := by
  rintro q ⟨hqd, hl⟩
  obtain ⟨hdS, hpat⟩ := hd
  obtain ⟨T, ℓ, _, _, _, _⟩ := q
  obtain ⟨T', ℓ', _, _, _, _⟩ := d
  obtain rfl : T = T' := hqd
  subst hdS
  refine ⟨rfl, fun i j hij hg ↦ (Iff.trans ?_ (hpat i j hij hg))⟩
  simpa only [eq_iff_iff, min_eq_bot, hc, or_false] using congrArg (· = ⊥) (hl i i rfl)

/-- Receiving at the cutoff `L + 1` keeps a label `L` in `[γ, γ + ω)`, hence uniformity. -/
theorem receivingFamily_subset_uniformityFamily {j : Fin d.card} {L : Ordinal.{u}}
    (hdL : d.label j = L) (hγL : γ ≤ L) (hLγ : L < γ + Ordinal.omega0) :
    receivingFamily d ((L + 1 : Ordinal.{u}) : Label.{u}) ⊆ uniformityFamily γ := by
  intro q hq
  obtain ⟨i, -, hi⟩ := exists_cell_of_mem_receivingFamily hq j
  have hL : (L : Label.{u}) < ((L + 1 : Ordinal.{u}) : Label.{u}) := by
    exact_mod_cast Order.lt_add_one_iff.mpr le_rfl
  rw [hdL, min_eq_left hL.le] at hi
  have hqi : q.label i = L := (min_eq_iff.mp hi).elim And.left fun h ↦ absurd h.1 hL.ne'
  exact ⟨i, by rw [hqi]; exact_mod_cast hγL, by rw [hqi]; exact_mod_cast hLγ⟩

/-- Receiving at the cutoff `γ + 1` keeps a label above `γ` at a cell of full grade, hence
high-arity dominance. -/
theorem receivingFamily_subset_dominanceFamily (hd : d ∈ dominanceFamily γ) :
    receivingFamily d ((γ + 1 : Ordinal.{u}) : Label.{u}) ⊆ dominanceFamily γ := by
  intro q hq
  obtain ⟨j, hg, hγj⟩ := hd
  obtain ⟨i, hgi, hi⟩ := exists_cell_of_mem_receivingFamily hq j
  have hsucc : ((γ + 1 : Ordinal.{u}) : Label.{u}) ≤ d.label j := by
    induction h : d.label j using recBotCoeTop with
    | bot => rw [h] at hγj; exact absurd hγj not_lt_bot
    | coe o => rw [h] at hγj; exact_mod_cast Order.add_one_le_of_lt (by exact_mod_cast hγj)
    | top => exact le_top
  rw [min_eq_right hsucc] at hi
  refine ⟨i, hgi.trans hg, lt_of_lt_of_le ?_ (min_eq_right_iff.mp hi)⟩
  exact_mod_cast Order.lt_add_one_iff.mpr le_rfl

end StageType

namespace Realization

open StageType

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-! ### The four clauses from finite-cut receiving -/

/-- **Generalized saturation from receiving**, at the cutoff `0`. -/
theorem HasFiniteCutReceiving.saturation (hr : R.HasFiniteCutReceiving) (hα : 0 < α)
    (x : R.Occurrence) (S : Scheme.{u} (x.arity + 1))
    (hne : (x.type.cofaces ∩ saturationFamily S).Nonempty) :
    R.RealizesOver x.tuple (saturationFamily S) := by
  obtain ⟨d, hd, hdS⟩ := hne
  exact (hr x d hd 0 (isPermittedCutoff_zero.mpr hα)).mono
    (receivingFamily_subset_saturationFamily hdS 0)

/-- **The bottom pattern from receiving**, at the cutoff `0`. -/
theorem HasFiniteCutReceiving.bottomPattern (hr : R.HasFiniteCutReceiving) (hα : 0 < α)
    (x : R.Occurrence) (S : Scheme.{u} (x.arity + 1)) (ρ : Fin S.card → Label.{u})
    (hne : (x.type.cofaces ∩ bottomPatternFamily S ρ).Nonempty) :
    R.RealizesOver x.tuple (bottomPatternFamily S ρ) := by
  obtain ⟨d, hd, hdS⟩ := hne
  exact (hr x d hd 0 (isPermittedCutoff_zero.mpr hα)).mono
    (receivingFamily_subset_bottomPatternFamily hdS WithBot.coe_ne_bot)

/-- **Uniformity from receiving**: at a stage that is zero or a limit, a coface with a label `L`
in `[γ, γ + ω)` is received at the cutoff `L + 1`.  No hypothesis on `γ` is used. -/
theorem HasFiniteCutReceiving.uniformity (hr : R.HasFiniteCutReceiving)
    (hα : Order.IsSuccPrelimit α) (x : R.Occurrence) (γ : Ordinal.{u})
    (hne : (x.type.cofaces ∩ uniformityFamily γ).Nonempty) :
    R.RealizesOver x.tuple (uniformityFamily γ) := by
  obtain ⟨d, hd, j, hγj, hjγ⟩ := hne
  induction h : d.label j using recBotCoeTop with
  | bot => rw [h] at hγj; exact absurd hγj (not_le.mpr (WithBot.bot_lt_coe _))
  | top => rw [h] at hjγ; exact absurd hjγ (not_lt.mpr le_top)
  | coe L =>
    rw [h] at hγj hjγ
    have hLα : L < α := atStage_coe.mp (h ▸ d.atStage j)
    exact (hr x d hd _ (isPermittedCutoff_coe.mpr (by simpa using hα.add_natCast_lt hLα 1))).mono
      (receivingFamily_subset_uniformityFamily h (by exact_mod_cast hγj) (by exact_mod_cast hjγ))

/-- **High-arity dominance from receiving**: at a stage that is zero or a limit, for `γ` below the
stage, a coface with a label above `γ` at a cell of full grade is received at the cutoff
`γ + 1`. -/
theorem HasFiniteCutReceiving.dominance (hr : R.HasFiniteCutReceiving)
    (hα : Order.IsSuccPrelimit α) (x : R.Occurrence) {γ : Ordinal.{u}} (hγα : γ < α)
    (hne : (x.type.cofaces ∩ dominanceFamily γ).Nonempty) :
    R.RealizesOver x.tuple (dominanceFamily γ) := by
  obtain ⟨d, hd, hdγ⟩ := hne
  exact (hr x d hd _ (isPermittedCutoff_coe.mpr (by simpa using hα.add_natCast_lt hγα 1))).mono
    (receivingFamily_subset_dominanceFamily hdγ)

/-! ### The cap-to-model theorem -/

/-- **The cap-to-model theorem at a nonzero limit stage** (roadmap, Layer 3, 3.4): a realization
on a nonempty carrier with legal types, exactly consistent, covering, and with the finite-cut
receiving property is a model, provided the uniformity and dominance instances over every
occurrence are nonempty ([Kni26, Lemmas 4.4.2 and 4.4.3], here the hypotheses `hunif` and
`hdom`).  The conclusion is the four-family `IsModel`; each clause is received at one permitted
cutoff (`HasFiniteCutReceiving.saturation`, `.bottomPattern`, `.uniformity`, `.dominance`). -/
theorem isModel_of_hasFiniteCutReceiving (hα : Order.IsSuccLimit α) (hne : Nonempty M)
    (hl : R.HasLegalTypes) (hc : R.IsConsistent) (hcov : R.IsCovering)
    (hr : R.HasFiniteCutReceiving)
    (hunif : ∀ (x : R.Occurrence) (γ : Ordinal.{u}), Order.IsSuccPrelimit γ → γ < α →
      (x.type.cofaces ∩ uniformityFamily γ).Nonempty)
    (hdom : ∀ (x : R.Occurrence) (γ : Ordinal.{u}), γ < α →
      (x.type.cofaces ∩ dominanceFamily γ).Nonempty) :
    R.IsModel where
  nonempty := hne
  isLegal := hl
  isConsistent := hc
  isCovering := hcov
  saturation := hr.saturation (by simpa [Ordinal.bot_eq_zero] using hα.bot_lt)
  bottomPattern := hr.bottomPattern (by simpa [Ordinal.bot_eq_zero] using hα.bot_lt)
  uniformity x γ hγ hγα := hr.uniformity hα.isSuccPrelimit x γ (hunif x γ hγ hγα)
  dominance x γ hγα := hr.dominance hα.isSuccPrelimit x hγα (hdom x γ hγα)

end Realization

end VaughtConjecture
