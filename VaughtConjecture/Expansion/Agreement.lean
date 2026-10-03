/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.SatisfactionBorel
import InfinitaryLogic.Karp.CarrierTheorem
import InfinitaryLogic.Lomega1omega.OpenBoundsSemantics
import InfinitaryLogic.Lomega1omega.QuantifierRank
import VaughtConjecture.Comparison.GradedMatchingApplications
import VaughtConjecture.Realization.Expansion

/-!
# Condition 3 from model expansions, conditional on finite-extension receiving

Roadmap, the reduction of the main theorem to expansion domains ("Condition 3 from
back-and-forth") and Layer 5 (the one-block transfer and the sharp sentence comparison); semantic
contract, items 6, 9 and 12.

This file instantiates the abstract expansion-match data of
`VaughtConjecture.Comparison.GradedMatchingApplications` (`ExpansionMatchData`) by the model
expansions of two base structures `M` and `N` (`VaughtConjecture.Realization.Expansion`): at
level `α` the expansions are those to the block stage `λ_α = ω + ω · α` (`blockStage α`, the
stage at which the block `[λ_α, λ_α + ω)` begins; `ModelExpansion M (blockStage α)`), the charts
on `k` points are the stage types at `λ_α` on `k` points, and a tuple covers a chart in an
expansion when it enumerates an actual occurrence of it (`Realization.Covers`).

**Finite-extension receiving.**  A realization has **finite-extension receiving**
(`Realization.HasFiniteExtensionReceiving`) when, for every actual root `t` of type `p`, every
legal stage type `D` with a face `g` along which it restricts to `p`, and every permitted cutoff
`c`, some injective tuple `u` extends the root along `g` literally (`g.trans u = t`) and has a
type in the receiving family of `D` at `c`.  The donor `D` may add several points at once.  It
implies the finite-cut receiving property (`HasFiniteExtensionReceiving.hasFiniteCutReceiving`,
the case of one new point).  `FiniteExtensionReceiving` is the statement that every model at a
countable limit stage has finite-extension receiving: it is Layer 3's receiving for finite
extensions (from finite-cut receiving, along a chain of closed faces) composed with (R1)
(finite-cut receiving of models).  **It is not proved here, and nothing here proves it**: it is a
statement still to be proved, taken as an explicit hypothesis by every theorem that uses it.

**The laws.**

* *Atomic agreement, lowering, existence and compatibility are unconditional.*  Two covers of
  one chart have the same atomic type in the base language at every level
  (`Realization.Covers.sameAtomicType`), not only at level `0`.  Lowering reduces both expansions
  and the chart to the lower block stage (`exists_reduce_covers`), by the same tuples; no
  uniqueness or coherence of expansions is used.  Every expansion at `λ_η` has a cover of a chart
  on no points (`ModelExpansion.exists_covers_zero`), and any two stage types on no points are
  equal (`StageType.eq_of_zero`).
* *Forth and back for an already-covered point are unconditional*
  (`exists_extend_covers_of_mem_range`, `exists_extend_covers_back_of_mem_range`): the extended
  covers are the reductions of the given ones, with the identity as common map.
* *Forth and back in general are conditional on finite-extension receiving* in the expansion of
  `N` for forth and of `M` for back (`exists_extend_covers`, `exists_extend_covers_back`).  For a
  new point `x` of `M`, cover the tuple `c` followed by `x` by a typed tuple `u` of the expansion
  `e` of `M` at `λ_{α+1}`, as an initial segment (`IsCovering.exists_castAdd`); its type `D` is
  legal and restricts to the common chart `t` along the face `g` of the coordinates of `c`.
  Finite-extension receiving in the expansion `f` of `N` at the permitted cutoff `λ_α`
  (`isPermittedCutoff_blockStage`) gives `u'` with `g.trans u' = d` and a type in the receiving
  family of `D` at `λ_α`, whose stage reduction to `λ_α` is that of `D`
  (`StageType.reduce_eq_of_mem_receivingFamily`).  The new chart is `D` reduced to `λ_α`,
  covered by `u` and `u'` in the reduced expansions.  The donor `D` is already a type at
  `λ_{α+1}`, so it is its own lift: no projected-donor lifting is used, and only the one cutoff
  `λ_α` is used (semantic contract, item 12).

**Consequences.**  With finite-extension receiving as a hypothesis, the data form
`ExpansionMatchData baseLanguage.{0} M N η` for `η < ω₁` (`expansionMatchData`), so the empty
tuples of two base structures with model expansions to `λ_η` are back-and-forth equivalent at
`η` (`bfEquiv_of_modelExpansions`).  By InfinitaryLogic's `BFEquiv_implies_agreeQR`, through the
passage from a sentence to a formula with no free variables (`BoundedFormulaω.openBounds`, which
keeps the quantifier rank and the semantics), the two structures agree on every sentence of
quantifier rank at most `η` (`realize_iff_of_modelExpansions`), and so do two codes on `ℕ`
(`mem_modelsOf_iff_of_modelExpansions`).  The case `η = 0` needs no hypothesis, since the forth
and back laws are vacuous there (`VaughtConjecture.Expansion.AgreementExamples`).

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe v w

namespace VaughtConjecture

open Ordinal FirstOrder Language Structure baseLanguage Comparison

/-! ### Finite-extension receiving -/

namespace Realization

variable {α : Ordinal.{0}} {M : Type v} (R : Realization.{0, v} α M)

/-- **Finite-extension receiving**: for every actual root `t` of type `p`, every legal stage type
`D` restricting to `p` along a face `g`, and every permitted cutoff `c`, some injective tuple `u`
extends `t` along `g` literally and has a type in the receiving family of `D` at `c`. -/
def HasFiniteExtensionReceiving : Prop :=
  ∀ ⦃n m : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{0} α n), R.eval t = some p →
    ∀ (D : StageType.{0} α m) (g : Fin n ↪ Fin m), D.IsLegal →
      StageType.restrictFace g D = some p → ∀ c : Label.{0}, Label.IsPermittedCutoff α c →
        ∃ u : Fin m ↪ M, g.trans u = t ∧
          ∃ q ∈ StageType.receivingFamily D c, R.eval u = some q

variable {R}

/-- **Finite-extension receiving gives finite-cut receiving**: the case of a donor on one more
point, along the initial segment. -/
theorem HasFiniteExtensionReceiving.hasFiniteCutReceiving (h : R.HasFiniteExtensionReceiving) :
    R.HasFiniteCutReceiving :=
  fun x d hd c hc ↦ h x.tuple x.type x.eval_tuple d Fin.castSuccEmb hd.1 hd.2 c hc

end Realization

namespace Expansion

/-- **Finite-extension receiving for models** on the carriers in the universe `w`: every model at
a countable limit stage has finite-extension receiving.  It is a statement still to be proved
(Layer 3, receiving for finite extensions; (R1)), not proved here. -/
structure FiniteExtensionReceiving : Prop where
  /-- Every model at a countable limit stage has finite-extension receiving. -/
  receive : ∀ {α : Ordinal.{0}} {M : Type w}, Order.IsSuccLimit α → α < ω₁ →
    ∀ R : Realization.{0, w} α M, R.IsModel → R.HasFiniteExtensionReceiving

/-! ### The unconditional laws -/

variable {M : Type v} {N : Type w} [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]

/-- **Lowering**: two covers of one chart at `λ_α` give covers, by the same tuples, of one chart
at `λ_β` for `β ≤ α`: the reductions of the expansions and of the chart. -/
theorem exists_reduce_covers {α β : Ordinal.{0}} (hβα : β ≤ α) {k : ℕ}
    {e : ModelExpansion M (blockStage α)} {f : ModelExpansion N (blockStage α)}
    {t : StageType.{0} (blockStage α) k} {c : Fin k → M} {d : Fin k → N}
    (hc : e.1.Covers t c) (hd : f.1.Covers t d) :
    ∃ (e' : ModelExpansion M (blockStage β)) (f' : ModelExpansion N (blockStage β))
      (t' : StageType.{0} (blockStage β) k), e'.1.Covers t' c ∧ f'.1.Covers t' d :=
  ⟨e.reduceBlock hβα, f.reduceBlock hβα, t.reduce (isSuccPrelimit_blockStage β), hc.reduce _,
    hd.reduce _⟩

/-- **Forth for an already-covered point**: if `x` is a coordinate of the cover `c`, the
reductions of the covers to `λ_α` serve, with the identity as common map.  No receiving is
used. -/
theorem exists_extend_covers_of_mem_range {α : Ordinal.{0}} {k : ℕ}
    {e : ModelExpansion M (blockStage (α + 1))} {f : ModelExpansion N (blockStage (α + 1))}
    {t : StageType.{0} (blockStage (α + 1)) k} {c : Fin k → M} {d : Fin k → N}
    (hc : e.1.Covers t c) (hd : f.1.Covers t d) {x : M} (hx : x ∈ Set.range c) :
    ∃ (e' : ModelExpansion M (blockStage α)) (f' : ModelExpansion N (blockStage α)) (k' : ℕ)
      (t' : StageType.{0} (blockStage α) k') (c' : Fin k' → M) (d' : Fin k' → N)
      (j : Fin k → Fin k') (i : Fin k'),
      e'.1.Covers t' c' ∧ f'.1.Covers t' d' ∧ c' ∘ j = c ∧ d' ∘ j = d ∧ c' i = x := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨e', f', t', hc', hd'⟩ := exists_reduce_covers (Order.le_succ α) hc hd
  exact ⟨e', f', k, t', c, d, id, i, hc', hd', rfl, rfl, rfl⟩

/-- **Back for an already-covered point**: `exists_extend_covers_of_mem_range` with the roles of
`M` and `N` exchanged.  No receiving is used. -/
theorem exists_extend_covers_back_of_mem_range {α : Ordinal.{0}} {k : ℕ}
    {e : ModelExpansion M (blockStage (α + 1))} {f : ModelExpansion N (blockStage (α + 1))}
    {t : StageType.{0} (blockStage (α + 1)) k} {c : Fin k → M} {d : Fin k → N}
    (hc : e.1.Covers t c) (hd : f.1.Covers t d) {y : N} (hy : y ∈ Set.range d) :
    ∃ (e' : ModelExpansion M (blockStage α)) (f' : ModelExpansion N (blockStage α)) (k' : ℕ)
      (t' : StageType.{0} (blockStage α) k') (c' : Fin k' → M) (d' : Fin k' → N)
      (j : Fin k → Fin k') (i : Fin k'),
      e'.1.Covers t' c' ∧ f'.1.Covers t' d' ∧ c' ∘ j = c ∧ d' ∘ j = d ∧ d' i = y := by
  obtain ⟨f', e', k', t', d', c', j, i, hd', hc', hj, hj', hi⟩ :=
    exists_extend_covers_of_mem_range hd hc hy
  exact ⟨e', f', k', t', c', d', j, i, hc', hd', hj', hj, hi⟩

/-! ### Forth and back, conditional on finite-extension receiving -/

/-- **Forth, conditional on finite-extension receiving in the expansion of `N`**: two covers `c`
and `d` of one chart at `λ_{α+1}` and a point `x` of `M` give covers `c'` and `d'` of one chart
at `λ_α`, extending `c` and `d` along a common map, with `x` among the coordinates of `c'`.  The
chart is the reduction to `λ_α` of the type `D` at `λ_{α+1}` of a typed tuple of `e` starting
with `c` and `x`; `d'` is received for `D` over `d` at the permitted cutoff `λ_α`.

This is conditional on finite-extension receiving, which is still to be proved (Layer 3,
receiving for finite extensions; (R1)): here `hf` is that property of the expansion `f`. -/
theorem exists_extend_covers {α : Ordinal.{0}} {k : ℕ}
    {e : ModelExpansion M (blockStage (α + 1))} {f : ModelExpansion N (blockStage (α + 1))}
    (hf : f.1.HasFiniteExtensionReceiving)
    {t : StageType.{0} (blockStage (α + 1)) k} {c : Fin k → M} {d : Fin k → N}
    (hc : e.1.Covers t c) (hd : f.1.Covers t d) (x : M) :
    ∃ (e' : ModelExpansion M (blockStage α)) (f' : ModelExpansion N (blockStage α)) (k' : ℕ)
      (t' : StageType.{0} (blockStage α) k') (c' : Fin k' → M) (d' : Fin k' → N)
      (j : Fin k → Fin k') (i : Fin k'),
      e'.1.Covers t' c' ∧ f'.1.Covers t' d' ∧ c' ∘ j = c ∧ d' ∘ j = d ∧ c' i = x := by
  by_cases hx : x ∈ Set.range c
  · exact exists_extend_covers_of_mem_range hc hd hx
  have hR := e.2.isModel
  -- the cover `c` followed by the new point `x`
  have hinj : Function.Injective (Fin.snoc c x : Fin (k + 1) → M) :=
    Fin.snoc_injective_of_injective hc.injective hx
  obtain ⟨k₂, u, hu, hsome⟩ :=
    hR.isCovering.exists_castAdd hR.isConsistent ⟨Fin.snoc c x, hinj⟩
  obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp hsome
  have hu' (i : Fin (k + 1)) : u (Fin.castAdd k₂ i) = (Fin.snoc c x : Fin (k + 1) → M) i :=
    DFunLike.congr_fun hu i
  -- the face of the coordinates of `c`
  let g : Fin k ↪ Fin (k + 1 + k₂) := Fin.castSuccEmb.trans (Fin.castAddEmb k₂)
  have hgu : ⇑u ∘ ⇑g = c := funext fun i ↦ by simpa [g] using hu' i.castSucc
  have hgD : StageType.restrictFace g D = some t := by
    rw [← hR.isConsistent u D g hD, ← hc.eval_eq]
    congr 1
    ext i
    exact congrFun hgu i
  obtain ⟨u', hgu', q, hq, hq'⟩ := hf ⟨d, hd.injective⟩ t hd.eval_eq D g (hR.isLegal u D hD) hgD
    _ (isPermittedCutoff_blockStage α)
  refine ⟨e.reduceBlock (Order.le_succ α), f.reduceBlock (Order.le_succ α), k + 1 + k₂,
    D.reduce (isSuccPrelimit_blockStage α), u, u', g, Fin.castAdd k₂ (Fin.last k),
    (Realization.covers_of_eval u hD).reduce _, ?_, hgu, funext fun i ↦ ?_, ?_⟩
  · rw [← StageType.reduce_eq_of_mem_receivingFamily _ hq]
    exact (Realization.covers_of_eval u' hq').reduce _
  · exact DFunLike.congr_fun hgu' i
  · simpa using hu' (Fin.last k)

/-- **Back, conditional on finite-extension receiving in the expansion of `M`**:
`exists_extend_covers` with the roles of `M` and `N` exchanged, for a point `y` of `N`.

This is conditional on finite-extension receiving, which is still to be proved (Layer 3,
receiving for finite extensions; (R1)): here `he` is that property of the expansion of `M`. -/
theorem exists_extend_covers_back {α : Ordinal.{0}} {k : ℕ}
    {e : ModelExpansion M (blockStage (α + 1))} {f : ModelExpansion N (blockStage (α + 1))}
    (he : e.1.HasFiniteExtensionReceiving)
    {t : StageType.{0} (blockStage (α + 1)) k} {c : Fin k → M} {d : Fin k → N}
    (hc : e.1.Covers t c) (hd : f.1.Covers t d) (y : N) :
    ∃ (e' : ModelExpansion M (blockStage α)) (f' : ModelExpansion N (blockStage α)) (k' : ℕ)
      (t' : StageType.{0} (blockStage α) k') (c' : Fin k' → M) (d' : Fin k' → N)
      (j : Fin k → Fin k') (i : Fin k'),
      e'.1.Covers t' c' ∧ f'.1.Covers t' d' ∧ c' ∘ j = c ∧ d' ∘ j = d ∧ d' i = y := by
  obtain ⟨f', e', k', t', d', c', j, i, hd', hc', hj, hj', hi⟩ := exists_extend_covers he hd hc y
  exact ⟨e', f', k', t', c', d', j, i, hc', hd', hj', hj, hi⟩

/-! ### The expansion-match data and condition 3 -/

variable (M N) in
/-- **The expansion-match data of two base structures** at a height `η < ω₁`: at level `α`, the
model expansions to `λ_α`, the stage types at `λ_α` as charts, and covers as actual occurrences.
Atomic agreement and lowering are unconditional; forth and back use finite-extension receiving at
the countable block stages `λ_{α+1}` with `α + 1 ≤ η`.

This is conditional on finite-extension receiving, which is still to be proved (Layer 3,
receiving for finite extensions; (R1)): `hrec` is that statement. -/
def expansionMatchData (hrec : FiniteExtensionReceiving.{w}) (M N : Type w)
    [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N] {η : Ordinal.{0}}
    (hη : η < ω₁) : ExpansionMatchData baseLanguage.{0} M N η where
  ExpansionM α := ModelExpansion M (blockStage α)
  ExpansionN α := ModelExpansion N (blockStage α)
  Chart α k := StageType.{0} (blockStage α) k
  coversM e t c := e.1.Covers t c
  coversN f t d := f.1.Covers t d
  atomic := fun {_ e f _ _ _} hc hd ↦ Realization.Covers.sameAtomicType e.2 f.2 hc hd
  lower hβα _ _ _ _ _ _ _ hc hd := exists_reduce_covers hβα hc hd
  forth hα _ _ f _ _ _ hc hd x :=
    exists_extend_covers (hrec.receive (isSuccLimit_blockStage _)
      (blockStage_lt_omega_one (hα.trans_lt hη)) f.1 f.2.isModel) hc hd x
  back hα _ e _ _ _ _ hc hd y :=
    exists_extend_covers_back (hrec.receive (isSuccLimit_blockStage _)
      (blockStage_lt_omega_one (hα.trans_lt hη)) e.1 e.2.isModel) hc hd y

variable {M N : Type w} [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]

/-- **Condition 3 in back-and-forth form, from model expansions**: two base structures with model
expansions to `λ_η`, for `η < ω₁`, have back-and-forth equivalent empty tuples at `η` in the base
language.  The initial match is the common chart on no points: each expansion has a cover of a
stage type on no points (`ModelExpansion.exists_covers_zero`), and there is only one such type
(`StageType.eq_of_zero`).

This is conditional on finite-extension receiving, which is still to be proved (Layer 3,
receiving for finite extensions; (R1)): `hrec` is that statement. -/
theorem bfEquiv_of_modelExpansions (hrec : FiniteExtensionReceiving.{w}) {η : Ordinal.{0}}
    (hη : η < ω₁) (hM : Nonempty (ModelExpansion M (blockStage η)))
    (hN : Nonempty (ModelExpansion N (blockStage η))) :
    BFEquiv (L := baseLanguage.{0}) (M := M) (N := N) η 0 ![] ![] :=
  have ⟨e⟩ := hM
  have ⟨f⟩ := hN
  (expansionMatchData hrec M N hη).bfEquiv_of_expansionMatch
    ⟨⟨e, e.exists_covers_zero⟩, ⟨f, f.exists_covers_zero⟩⟩
    fun _ _ ↦ StageType.eq_of_zero _ _

/-- **Sentence agreement from model expansions**: two base structures with model expansions to
`λ_η`, for `η < ω₁`, satisfy the same sentences of quantifier rank at most `η`.  The sentence is
read as a formula with no free variables (`BoundedFormulaω.openBounds`, of the same quantifier
rank and the same truth), and InfinitaryLogic's `BFEquiv_implies_agreeQR` applies to the
back-and-forth equivalence of `bfEquiv_of_modelExpansions`.

This is conditional on finite-extension receiving, which is still to be proved (Layer 3,
receiving for finite extensions; (R1)): `hrec` is that statement. -/
theorem realize_iff_of_modelExpansions (hrec : FiniteExtensionReceiving.{w}) {η : Ordinal.{0}}
    (hη : η < ω₁) (hM : Nonempty (ModelExpansion M (blockStage η)))
    (hN : Nonempty (ModelExpansion N (blockStage η))) (θ : baseLanguage.{0}.Sentenceω)
    (hθ : θ.qrank ≤ η) : θ.Realize M ↔ θ.Realize N :=
  (realize_openBounds θ Fin.elim0).symm.trans <|
    (BFEquiv_implies_agreeQR η Fin.elim0 Fin.elim0 (bfEquiv_of_modelExpansions hrec hη hM hN)
      θ.openBounds ((qrank_openBounds θ).le.trans hθ)).trans (realize_openBounds θ Fin.elim0)

/-- **Sentence agreement for codes on `ℕ`**: two codes whose structures have model expansions to
`λ_η`, for `η < ω₁`, lie in the same sets `ModelsOf θ` for the sentences `θ` of quantifier rank
at most `η`.  This is condition 3 of the reduction to expansion domains, for codes.

This is conditional on finite-extension receiving, which is still to be proved (Layer 3,
receiving for finite extensions; (R1)): `hrec` is that statement. -/
theorem mem_modelsOf_iff_of_modelExpansions (hrec : FiniteExtensionReceiving.{0})
    {η : Ordinal.{0}} (hη : η < ω₁) (c₁ c₂ : StructureSpace baseLanguage.{0})
    (h₁ : Nonempty (@ModelExpansion ℕ c₁.toStructure (blockStage η)))
    (h₂ : Nonempty (@ModelExpansion ℕ c₂.toStructure (blockStage η)))
    (θ : baseLanguage.{0}.Sentenceω) (hθ : θ.qrank ≤ η) :
    c₁ ∈ ModelsOf θ ↔ c₂ ∈ ModelsOf θ :=
  @realize_iff_of_modelExpansions ℕ ℕ c₁.toStructure c₂.toStructure hrec η hη h₁ h₂ θ hθ

end Expansion

end VaughtConjecture
