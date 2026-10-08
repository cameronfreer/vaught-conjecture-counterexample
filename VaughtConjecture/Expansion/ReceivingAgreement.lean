/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Expansion.Agreement

/-!
# Condition 3 for receiving model expansions

Roadmap, the reduction of the main theorem to expansion domains ("Condition 3 from
back-and-forth") and Layer 5 (the one-block transfer), for the auxiliary class `𝒞_α` of receiving
models; semantic contract, items 6, 9 and 12.

The expansion-match data of `VaughtConjecture.Expansion.Agreement` (`Expansion.expansionMatchData`)
take every model expansion as an expansion at each level, and their forth and back laws use
finite-extension receiving of the expansions at the level above, from (R1).  Here the expansions
at each level are the model expansions **with the finite-cut receiving property**
(`Expansion.receivingMatchData`), so receiving is a clause of the expansions and (R1) is not used.

**Where a new statement is needed.**  The forth law of `Expansion.Agreement`
(`Expansion.exists_extend_covers`) concludes the existence of some expansions `e'` and `f'` at
`λ_α` with the extended covers; its proof takes the reductions of the given expansions, but the
statement does not say so.  In the receiving data the expansions at `λ_α` must again receive,
which holds for the reductions (`Realization.HasFiniteCutReceiving.reduce`) and is not known for
arbitrary model expansions.  So the forth law is restated with the reductions named
(`Expansion.exists_extend_covers_reduceBlock`); its proof is that of `exists_extend_covers`.

**Consequences.**  The receiving data form `ExpansionMatchData baseLanguage.{0} M N η` for every
`η < ω₁` with no hypothesis, so two base structures with receiving model expansions to `λ_η` have
back-and-forth equivalent empty tuples at `η` (`Expansion.bfEquiv_of_receivingModelExpansions`)
and satisfy the same sentences of quantifier rank at most `η`
(`Expansion.realize_iff_of_receivingModelExpansions`); covers of a common chart in receiving
model expansions give back-and-forth equivalent selected tuples
(`ModelExpansion.bfEquiv_comp_of_covers_of_hasFiniteCutReceiving`).

**Status.**  Proved, with no receiving hypothesis on models in general; finite-cut receiving is
asked only of the two given expansions.  Existence of receiving model expansions is not treated.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture

open Ordinal FirstOrder Language Structure baseLanguage Comparison

namespace Expansion

variable {M N : Type w} [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]

/-- **Forth with the reductions named**, conditional on finite-extension receiving in the
expansion of `N`: two covers `c` and `d` of one chart at `λ_{α+1}` and a point `x` of `M` give
covers `c'` and `d'` of one chart at `λ_α` in the **reductions** of the two expansions, extending
`c` and `d` along a common map, with `x` among the coordinates of `c'`.  The proof is that of
`exists_extend_covers`, whose statement leaves the expansions at `λ_α` unnamed. -/
theorem exists_extend_covers_reduceBlock {α : Ordinal.{0}} {k : ℕ}
    {e : ModelExpansion M (blockStage (α + 1))} {f : ModelExpansion N (blockStage (α + 1))}
    (hf : f.1.HasFiniteExtensionReceiving)
    {t : StageType.{0} (blockStage (α + 1)) k} {c : Fin k → M} {d : Fin k → N}
    (hc : e.1.Covers t c) (hd : f.1.Covers t d) (x : M) :
    ∃ (k' : ℕ) (t' : StageType.{0} (blockStage α) k') (c' : Fin k' → M) (d' : Fin k' → N)
      (j : Fin k → Fin k') (i : Fin k'),
      (e.reduceBlock (Order.le_succ α)).1.Covers t' c' ∧
        (f.reduceBlock (Order.le_succ α)).1.Covers t' d' ∧ c' ∘ j = c ∧ d' ∘ j = d ∧
          c' i = x := by
  by_cases hx : x ∈ Set.range c
  · obtain ⟨i, rfl⟩ := hx
    exact ⟨k, _, c, d, id, i, hc.reduce _, hd.reduce _, rfl, rfl, rfl⟩
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
  refine ⟨k + 1 + k₂, D.reduce (isSuccPrelimit_blockStage α), u, u', g,
    Fin.castAdd k₂ (Fin.last k), (Realization.covers_of_eval u hD).reduce _, ?_, hgu,
    funext fun i ↦ ?_, ?_⟩
  · rw [← StageType.reduce_eq_of_mem_receivingFamily _ hq]
    exact (Realization.covers_of_eval u' hq').reduce _
  · exact DFunLike.congr_fun hgu' i
  · simpa using hu' (Fin.last k)

/-- **Back with the reductions named**: `exists_extend_covers_reduceBlock` with the roles of `M`
and `N` exchanged, for a point `y` of `N`, conditional on finite-extension receiving in the
expansion of `M`. -/
theorem exists_extend_covers_back_reduceBlock {α : Ordinal.{0}} {k : ℕ}
    {e : ModelExpansion M (blockStage (α + 1))} {f : ModelExpansion N (blockStage (α + 1))}
    (he : e.1.HasFiniteExtensionReceiving)
    {t : StageType.{0} (blockStage (α + 1)) k} {c : Fin k → M} {d : Fin k → N}
    (hc : e.1.Covers t c) (hd : f.1.Covers t d) (y : N) :
    ∃ (k' : ℕ) (t' : StageType.{0} (blockStage α) k') (c' : Fin k' → M) (d' : Fin k' → N)
      (j : Fin k → Fin k') (i : Fin k'),
      (e.reduceBlock (Order.le_succ α)).1.Covers t' c' ∧
        (f.reduceBlock (Order.le_succ α)).1.Covers t' d' ∧ c' ∘ j = c ∧ d' ∘ j = d ∧
          d' i = y := by
  obtain ⟨k', t', d', c', j, i, hd', hc', hj, hj', hi⟩ :=
    exists_extend_covers_reduceBlock he hd hc y
  exact ⟨k', t', c', d', j, i, hc', hd', hj', hj, hi⟩

/-- The reduction of a model expansion with finite-cut receiving between block stages has
finite-cut receiving (`Realization.HasFiniteCutReceiving.reduce`). -/
theorem _root_.VaughtConjecture.ModelExpansion.hasFiniteCutReceiving_reduceBlock
    {ξ β : Ordinal.{0}} {e : ModelExpansion M (blockStage ξ)} (he : e.1.HasFiniteCutReceiving)
    (h : β ≤ ξ) : (e.reduceBlock h).1.HasFiniteCutReceiving := by
  rw [ModelExpansion.reduceBlock_val]
  exact he.reduce (isSuccPrelimit_blockStage ξ) _ (blockStage_mono h)

/-- A model expansion with finite-cut receiving to a block stage has finite-extension receiving
(`Realization.HasFiniteCutReceiving.hasFiniteExtensionReceiving`). -/
theorem _root_.VaughtConjecture.ModelExpansion.hasFiniteExtensionReceiving_of_hasFiniteCutReceiving
    {ξ : Ordinal.{0}} {e : ModelExpansion M (blockStage ξ)} (he : e.1.HasFiniteCutReceiving) :
    e.1.HasFiniteExtensionReceiving :=
  he.hasFiniteExtensionReceiving e.2.isModel.isConsistent (isSuccPrelimit_blockStage ξ)

variable (M N) in
/-- **The receiving expansion-match data** of two base structures at a height `η < ω₁`: at level
`α`, the model expansions to `λ_α` with the finite-cut receiving property, the stage types at
`λ_α` as charts, and covers as actual occurrences.  Lowering and the forth and back laws take the
reductions of the given expansions, which receive again; no hypothesis is used. -/
def receivingMatchData {η : Ordinal.{0}} (_hη : η < ω₁) :
    ExpansionMatchData baseLanguage.{0} M N η where
  ExpansionM α := {e : ModelExpansion M (blockStage α) // e.1.HasFiniteCutReceiving}
  ExpansionN α := {f : ModelExpansion N (blockStage α) // f.1.HasFiniteCutReceiving}
  Chart α k := StageType.{0} (blockStage α) k
  coversM e t c := e.1.1.Covers t c
  coversN f t d := f.1.1.Covers t d
  atomic := fun {_ e f _ _ _} hc hd ↦ Realization.Covers.sameAtomicType e.1.2 f.1.2 hc hd
  lower hβα _ _ e f _ _ _ hc hd :=
    ⟨⟨e.1.reduceBlock hβα, ModelExpansion.hasFiniteCutReceiving_reduceBlock e.2 hβα⟩,
      ⟨f.1.reduceBlock hβα, ModelExpansion.hasFiniteCutReceiving_reduceBlock f.2 hβα⟩,
      _, hc.reduce _, hd.reduce _⟩
  forth _ _ e f _ _ _ hc hd x :=
    have ⟨k', t', c', d', j, i, hc', hd', hj, hj', hi⟩ := exists_extend_covers_reduceBlock
      (ModelExpansion.hasFiniteExtensionReceiving_of_hasFiniteCutReceiving f.2) hc hd x
    ⟨⟨_, ModelExpansion.hasFiniteCutReceiving_reduceBlock e.2 (Order.le_succ _)⟩,
      ⟨_, ModelExpansion.hasFiniteCutReceiving_reduceBlock f.2 (Order.le_succ _)⟩,
      k', t', c', d', j, i, hc', hd', hj, hj', hi⟩
  back _ _ e f _ _ _ hc hd y :=
    have ⟨k', t', c', d', j, i, hc', hd', hj, hj', hi⟩ := exists_extend_covers_back_reduceBlock
      (ModelExpansion.hasFiniteExtensionReceiving_of_hasFiniteCutReceiving e.2) hc hd y
    ⟨⟨_, ModelExpansion.hasFiniteCutReceiving_reduceBlock e.2 (Order.le_succ _)⟩,
      ⟨_, ModelExpansion.hasFiniteCutReceiving_reduceBlock f.2 (Order.le_succ _)⟩,
      k', t', c', d', j, i, hc', hd', hj, hj', hi⟩

/-- **Condition 3 in back-and-forth form, for receiving model expansions**: two base structures
with model expansions to `λ_η`, `η < ω₁`, having the finite-cut receiving property, have
back-and-forth equivalent empty tuples at `η` in the base language.  (R1) is not used. -/
theorem bfEquiv_of_receivingModelExpansions {η : Ordinal.{0}} (hη : η < ω₁)
    (hM : ∃ e : ModelExpansion M (blockStage η), e.1.HasFiniteCutReceiving)
    (hN : ∃ f : ModelExpansion N (blockStage η), f.1.HasFiniteCutReceiving) :
    BFEquiv (L := baseLanguage.{0}) (M := M) (N := N) η 0 ![] ![] :=
  have ⟨e, he⟩ := hM
  have ⟨f, hf⟩ := hN
  (receivingMatchData M N hη).bfEquiv_of_expansionMatch
    ⟨⟨⟨e, he⟩, e.exists_covers_zero⟩, ⟨⟨f, hf⟩, f.exists_covers_zero⟩⟩
    fun _ _ ↦ StageType.eq_of_zero _ _

/-- **Sentence agreement for receiving model expansions**: two base structures with model
expansions to `λ_η`, `η < ω₁`, having the finite-cut receiving property, satisfy the same
sentences of quantifier rank at most `η`.  (R1) is not used. -/
theorem realize_iff_of_receivingModelExpansions {η : Ordinal.{0}} (hη : η < ω₁)
    (hM : ∃ e : ModelExpansion M (blockStage η), e.1.HasFiniteCutReceiving)
    (hN : ∃ f : ModelExpansion N (blockStage η), f.1.HasFiniteCutReceiving)
    (θ : baseLanguage.{0}.Sentenceω) (hθ : θ.qrank ≤ η) : θ.Realize M ↔ θ.Realize N :=
  (realize_openBounds θ Fin.elim0).symm.trans <|
    (BFEquiv_implies_agreeQR η Fin.elim0 Fin.elim0
      (bfEquiv_of_receivingModelExpansions hη hM hN) θ.openBounds
      ((qrank_openBounds θ).le.trans hθ)).trans (realize_openBounds θ Fin.elim0)

end Expansion

namespace ModelExpansion

open Expansion

variable {M N : Type w} [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]

/-- **Comparison from a common chart, for receiving model expansions**: if model expansions `e`
of `M` and `f` of `N` to `λ_η`, `η < ω₁`, with the finite-cut receiving property, have covers `c`
and `d` of one stage type at `λ_η`, then for every selector `s` the selected tuples `c ∘ s` and
`d ∘ s` are back-and-forth equivalent at `η` in the base language.  (R1) is not used. -/
theorem bfEquiv_comp_of_covers_of_hasFiniteCutReceiving {η : Ordinal.{0}} (hη : η < ω₁)
    (e : ModelExpansion M (blockStage η)) (f : ModelExpansion N (blockStage η))
    (he : e.1.HasFiniteCutReceiving) (hf : f.1.HasFiniteCutReceiving)
    {k : ℕ} {t : StageType.{0} (blockStage η) k} {c : Fin k → M} {d : Fin k → N}
    (hc : e.1.Covers t c) (hd : f.1.Covers t d) {n : ℕ} (s : Fin n → Fin k) :
    BFEquiv (L := baseLanguage.{0}) η n (c ∘ s) (d ∘ s) :=
  (receivingMatchData M N hη).bfEquiv_of_match
    ⟨le_rfl, ⟨e, he⟩, ⟨f, hf⟩, k, t, c, d, hc, hd, s, rfl, rfl⟩

end ModelExpansion

end VaughtConjecture
