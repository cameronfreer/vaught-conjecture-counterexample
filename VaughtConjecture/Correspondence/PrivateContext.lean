/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.PrivateContext

/-!
# Correspondence: the private context, clauses 3 and 4

Roadmap, "Manuscript concordance", row 21.  The conclusion of
`Realization.IsModel.exists_privateContext` is compared with clauses 3 and 4 of
[Kni26, Lemma 8.1.1].  Clauses 1 and 2 of the lemma (the hollow case, with its anchors at
infinity) are not compared here.

## The setting

[Kni26, Proposition 7.3.3] fixes a model `M` of `S_α`, a tuple `x` of arity `n` with type
`p = M(x)`, and a type `p♦` on `n + 1` points extending `p`, with domain `D♦`.  Here `M` is a
realization `R` with `R.IsModel` at stage `α` (row 11), `x` is an occurrence of `R`, and `p♦` is
a stage type `d` on `x.arity + 1` points.  Lemma 8.1.1 gives a tuple `x'` of arity `m` with
`x⌢x' ∈ dom M`; here this is an occurrence `y` with an embedding `f` of the coordinates of `x`
into those of `y` and `f.trans y.tuple = x.tuple`, so `n + m` is `y.arity` and
`p' = M(x⌢x')` is `y.type`.

## The clauses (`Realization.PrintedPrivateContext`)

| Printed | Field |
| --- | --- |
| `x⌢x' ∈ dom M` | `face` |
| 3. for every limit `μ < α` with some `p♦(Ξ) ∈ [μ, μ + ω)`, some `p'(Ω_μ) ∈ [μ, μ + ω)` | `block` |
| 4(a). `N > n + 1` | `lt_a` |
| 4(b). `N > K`, the characteristic arity if finite | `lt_b` |
| 4(c). `N > j` whenever `p♦(Θ) = μ + j`, `μ` not a successor | `lt_c` |
| 4(d). `N > j` whenever `p'(Ω_μ) = μ + j` | `lt_d` |
| 4. `Ω ∈ D'_{n+m,N}` | `gradedIndex_eq` |
| 4. `p'(Ω) > p♦(Θ)` for every `Θ` with `p♦(Θ) < ∞` (finite characteristic arity) | `lt_label` |

The cells `Ω_μ` of clause 3 are data (`ref`), since clause 4(d) refers to them.  The printed `N`
is read existentially, with `m`: [Kni26, Definition 8.1.2] fixes it as a term.  The
characteristic arity [Kni26, Definition 5.4.1] has no counterpart in this repository; clause 4(b)
is stated for a given natural number `K`.

**Comparison** (`Realization.IsModel.exists_printedPrivateContext`): for a model at a stage
`α > 0` (the printed `α` is a limit), every occurrence `x`, every donor `d`, and every `K`, there
are `y`, `f`, cells `Ω_μ`, and `Ω` satisfying the fields above with `N = n + m`, the arity of `y`.
It is derived from the conclusion of `Realization.IsModel.exists_privateContext`, with the floor
`γ` taken as the largest ordinal label of `d` and `N₀ = K + 1`.

**Departures.**
1. *Clause 4, the infinite characteristic arity.*  When `M` has infinite characteristic arity the
   printed `Ω` has `p'(Ω) = ∞`; this is not produced.  Only the alternative for finite
   characteristic arity, `p'(Ω)` above every label of `p♦` below `∞`, is (`lt_label`).
2. *The tuple `x⌢x'`.*  The printed `x` is an initial segment of `x⌢x'`; here it is a literal
   face of `y` along an embedding `f` of coordinates.  Not proved equivalent here.
3. *The hypotheses of [Kni26, Proposition 7.3.3]* (hollowness or finite characteristic arity, a
   core `x`, the extension `p♦` of `p` and its two further conditions) are not assumed: harmless,
   since `Realization.IsModel.exists_printedPrivateContext` holds without them.

**Clause 3 and the block `[0, ω)`.**  The printed clause 3 and the field `block` concern limits
`μ` only, so the comparison says nothing at `μ = 0`.  The conclusion of
`Realization.IsModel.exists_privateContext`, which treats every block start, also gives a cell
with label in `[0, ω)` when some label of `d` lies there; this is not part of the comparison.

**Status.**  Row 21 is still to be proved, for three reasons: clauses 1 and 2 of the lemma are not
compared; the alternative `p'(Ω) = ∞` of clause 4 (departure 1) is not produced, and the
characteristic arity has no counterpart here; and the literal face of departure 2 is not proved
equivalent to the printed initial segment.

**The cited clause of the definition of a model.**  The printed proof of clause 4 cites
high-arity dominance as clause 4(a) of [Kni26, Definition 3.2.1], where it is clause 4(c); this is
a correction of the citation, not of the statement.  The proof here uses uniformity, clause 4(b)
(`Realization.IsModel.uniformity`), for clause 3 and high-arity dominance, clause 4(c)
(`Realization.IsModel.dominance`), for clause 4.

## Placement

The concordance and its notes are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".
-/

universe u v

namespace VaughtConjecture

open Finset Label

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-- **Clauses 3 and 4 of [Kni26, Lemma 8.1.1]**, for an occurrence `x`, a donor `d` on
`x.arity + 1` points, and a bound `K`: the occurrence `y` contains `x` along `f`, the cells
`ref μ` are the cells `Ω_μ` of clause 3, and `Ω` is the cell of clause 4, of arity `N`.  The value
of `Ω` is that of the case of finite characteristic arity. -/
structure PrintedPrivateContext (x : R.Occurrence) (d : StageType.{u} α (x.arity + 1)) (K : ℕ)
    (y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity) (ref : Ordinal.{u} → Fin y.type.card)
    (N : ℕ) (Ω : Fin y.type.card) : Prop where
  /-- [Kni26, Lemma 8.1.1]: `x⌢x' ∈ dom M`, with `x` a literal face of `y` along `f`. -/
  face : f.trans y.tuple = x.tuple
  /-- Clause 3 of [Kni26, Lemma 8.1.1]: for every limit `μ < α` such that some label of `d` lies
  in `[μ, μ + ω)`, the label of `Ω_μ` lies in `[μ, μ + ω)`. -/
  block (μ : Ordinal.{u}) : Order.IsSuccLimit μ → μ < α →
    (∃ j, ∃ k : ℕ, d.label j = ((μ + k : Ordinal.{u}) : Label.{u})) →
      ∃ k : ℕ, y.type.label (ref μ) = ((μ + k : Ordinal.{u}) : Label.{u})
  /-- Clause 4(a) of [Kni26, Lemma 8.1.1]: `N > n + 1`. -/
  lt_a : x.arity + 1 < N
  /-- Clause 4(b) of [Kni26, Lemma 8.1.1]: `N > K`. -/
  lt_b : K < N
  /-- Clause 4(c) of [Kni26, Lemma 8.1.1]: `N > j` whenever a label of `d` is `μ + j` with `μ`
  not a successor. -/
  lt_c (j : Fin d.card) (μ : Ordinal.{u}) (k : ℕ) : Order.IsSuccPrelimit μ →
    d.label j = ((μ + k : Ordinal.{u}) : Label.{u}) → k < N
  /-- Clause 4(d) of [Kni26, Lemma 8.1.1]: `N > j` whenever the label of `Ω_μ` is `μ + j`, for
  the `μ` of clause 3. -/
  lt_d (μ : Ordinal.{u}) : Order.IsSuccLimit μ → μ < α →
    (∃ j, ∃ k : ℕ, d.label j = ((μ + k : Ordinal.{u}) : Label.{u})) → ∀ k : ℕ,
      y.type.label (ref μ) = ((μ + k : Ordinal.{u}) : Label.{u}) → k < N
  /-- Clause 4 of [Kni26, Lemma 8.1.1]: `Ω ∈ D'_{n+m,N}`, of full scope and arity `N`. -/
  gradedIndex_eq : y.type.toCellScheme.gradedIndex Ω = (univ, N)
  /-- Clause 4 of [Kni26, Lemma 8.1.1], for finite characteristic arity: the label of `Ω` is above
  every label of `d` below `∞`. -/
  lt_label (j : Fin d.card) : d.label j < ⊤ → d.label j < y.type.label Ω

/-- The block of a label obtained by visibility replacement from a label that is not
self-visible: if `μ + k = vr_n(i, x)`, with `μ` zero or a limit and `x` not self-visible at `n`,
then `k = i` and `x = μ + k'` for some `k' < n`. -/
private theorem eq_coe_add_of_coe_add_eq_visibilityReplace {μ : Ordinal.{u}} {k n i : ℕ}
    {x : Label.{u}} (hμ : Order.IsSuccPrelimit μ) (hx : ¬ IsSelfVisible n x)
    (h : ((μ + k : Ordinal.{u}) : Label.{u}) = visibilityReplace n i x) :
    k = i ∧ ∃ k' < n, x = ((μ + k' : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => exact absurd (isSelfVisible_bot n) hx
  | top => exact absurd (isSelfVisible_top n) hx
  | coe o =>
    obtain ⟨μ', hμ', k', rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o
    have hk' : k' < n := not_le.mp fun hk ↦ hx ((isSelfVisible_coe_add_natCast_iff hμ').mpr hk)
    rw [visibilityReplace_coe_add_natCast hμ' hk'] at h
    obtain ⟨rfl, rfl⟩ := (add_natCast_eq_add_natCast_iff hμ hμ').mp
      (WithTop.coe_injective (WithBot.coe_injective h))
    exact ⟨rfl, k', hk', rfl⟩

/-- **Clauses 3 and 4 of [Kni26, Lemma 8.1.1]**, in the case of finite characteristic arity, for
the models of this repository: over an occurrence `x`, for a donor `d` on `x.arity + 1` points and
a bound `K`, an occurrence `y` containing `x` along `f`, cells `Ω_μ`, and a cell `Ω` satisfying
clauses 3 and 4 with `N` the arity of `y`.  The stage is positive (the printed stage is a limit).
It is the conclusion of `Realization.IsModel.exists_privateContext`, with the floor the largest
ordinal label of `d`. -/
theorem IsModel.exists_printedPrivateContext (hR : R.IsModel) (hα : 0 < α) (x : R.Occurrence)
    (d : StageType.{u} α (x.arity + 1)) (K : ℕ) :
    ∃ (y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity) (ref : Ordinal.{u} → Fin y.type.card)
      (Ω : Fin y.type.card), R.PrintedPrivateContext x d K y f ref y.arity Ω := by
  classical
  -- the floor: the largest ordinal label of the donor
  let g : Fin d.card → Ordinal.{u} := fun j ↦ if h : IsProper (d.label j) then h.choose else 0
  have hg (j : Fin d.card) (o : Ordinal.{u}) (ho : d.label j = o) : g j = o := by
    have hp : IsProper (d.label j) := ⟨o, ho.symm⟩
    simp only [g, hp, ↓reduceDIte]
    exact WithTop.coe_injective (WithBot.coe_injective (hp.choose_spec.trans ho))
  have hγ : univ.sup g < α := by
    refine (Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr hα.ne')).mpr fun j _ ↦ ?_
    rcases atStage_iff.mp (d.atStage j) with h | ⟨o, ho, h⟩ | h
    · simp [g, h, hα]
    · rw [hg j o h.symm]
      exact ho
    · simp [g, h, hα]
  obtain ⟨y, f, C, hf, hn, hN, hC, hγC, hanc⟩ := hR.exists_privateContext x d hγ (K + 1)
  choose z i hi hz hzv _ using hanc
  -- the cell `Ω_μ`: the reference cell of a donor label in the block of `μ`
  let ref : Ordinal.{u} → Fin y.type.card := fun μ ↦
    if hμ : ∃ j, ∃ k : ℕ, d.label j = ((μ + k : Ordinal.{u}) : Label.{u}) then
      z hμ.choose _ hμ.choose_spec.choose_spec else C
  have href (μ : Ordinal.{u}) (hμ : Order.IsSuccPrelimit μ)
      (h : ∃ j, ∃ k : ℕ, d.label j = ((μ + k : Ordinal.{u}) : Label.{u})) :
      ∃ k' < y.arity, y.type.label (ref μ) = ((μ + k' : Ordinal.{u}) : Label.{u}) := by
    simp only [ref, h, ↓reduceDIte]
    have h₀ := h.choose_spec.choose_spec
    exact (eq_coe_add_of_coe_add_eq_visibilityReplace hμ (hzv _ _ h₀)
      (h₀.symm.trans (hz _ _ h₀))).2
  refine ⟨y, f, ref, C, hf, fun μ hμ _ h ↦ ?_, hn, by omega, fun j μ k hμ hjk ↦ ?_,
    fun μ hμ _ h k hk ↦ ?_, hC, fun j hj ↦ ?_⟩
  · obtain ⟨k', -, hk'⟩ := href μ hμ.isSuccPrelimit h
    exact ⟨k', hk'⟩
  · obtain ⟨hki, -⟩ := eq_coe_add_of_coe_add_eq_visibilityReplace hμ (hzv _ _ hjk)
      (hjk.symm.trans (hz _ _ hjk))
    rw [hki]
    exact hi _ _ hjk
  · obtain ⟨k', hk', hlabel⟩ := href μ hμ.isSuccPrelimit h
    obtain ⟨-, rfl⟩ := (add_natCast_eq_add_natCast_iff hμ.isSuccPrelimit
      hμ.isSuccPrelimit).mp (WithTop.coe_injective (WithBot.coe_injective (hk.symm.trans hlabel)))
    exact hk'
  · induction hj' : d.label j using recBotCoeTop with
    | bot => exact (WithBot.bot_lt_coe _).trans hγC
    | coe o =>
      refine lt_of_le_of_lt (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ?_)) hγC
      rw [← hg j o hj']
      exact le_sup (mem_univ j)
    | top => exact absurd (hj' ▸ hj) (lt_irrefl _)

end Realization

end VaughtConjecture
