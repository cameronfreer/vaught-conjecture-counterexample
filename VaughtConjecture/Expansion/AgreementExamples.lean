/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Expansion.Agreement

/-!
# Examples for condition 3 from model expansions

Regressions for `VaughtConjecture.Realization.Expansion` and
`VaughtConjecture.Expansion.Agreement`:

* the block stages: `λ_0 = ω`, `λ_1 = ω · 2`, and `λ_α` is a permitted cutoff at `λ_{α+1}`;
* the height `η = 0` needs no finite-extension receiving: the forth and back laws are vacuous,
  and atomic agreement, lowering, existence and compatibility are unconditional;
* forth and back with an already-covered point use no receiving;
* finite-extension receiving gives finite-cut receiving;
* a received type has the stage reduction of its donor at the cutoff, and at every lower block
  stage;
* the code-level statement at `ℕ`, in the base language `baseLanguage.{0} : Language.{0, 1}` with
  levels in `Ordinal.{0}`, and the universes of the match data;
* without an initial match nothing follows: on an empty carrier there is no model expansion, and
  the match data relate no pair.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe v w

namespace VaughtConjecture.Expansion

open Ordinal FirstOrder Language Structure Comparison

/-! ### Block stages -/

/-- The block stage of index `0` is the base stage. -/
example : blockStage (0 : Ordinal.{0}) = ω :=
  blockStage_zero

/-- The block stage of index `1` is `ω · 2`. -/
example : blockStage (1 : Ordinal.{0}) = ω * 2 := by
  rw [blockStage_eq_mul, one_add_one_eq_two]

/-- The block stage `λ_α` is a permitted cutoff at `λ_{α+1}`. -/
example (α : Ordinal.{0}) :
    Label.IsPermittedCutoff (blockStage (α + 1)) (blockStage α : Label.{0}) :=
  isPermittedCutoff_blockStage α

/-! ### The height `0` needs no receiving -/

variable {M N : Type w} [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]

/-- At height `0`, two base structures with model expansions to `λ_0 = ω` have back-and-forth
equivalent empty tuples at `0`, with no finite-extension receiving: the forth and back laws are
vacuous (`α + 1 ≤ 0` never holds), and the other laws and the initial match are unconditional. -/
example (hM : Nonempty (ModelExpansion M (blockStage 0)))
    (hN : Nonempty (ModelExpansion N (blockStage 0))) :
    BFEquiv (L := baseLanguage.{0}) (M := M) (N := N) (0 : Ordinal.{0}) 0 ![] ![] :=
  have ⟨e⟩ := hM
  have ⟨f⟩ := hN
  ExpansionMatchData.bfEquiv_of_expansionMatch (L := baseLanguage.{0})
    { ExpansionM := fun α ↦ ModelExpansion M (blockStage α)
      ExpansionN := fun α ↦ ModelExpansion N (blockStage α)
      Chart := fun α k ↦ StageType.{0} (blockStage α) k
      coversM := fun e t c ↦ e.1.Covers t c
      coversN := fun f t d ↦ f.1.Covers t d
      atomic := fun {_ e f _ _ _} hc hd ↦ Realization.Covers.sameAtomicType e.2 f.2 hc hd
      lower := fun hβα _ _ _ _ _ _ _ hc hd ↦ exists_reduce_covers hβα hc hd
      forth := fun h ↦ absurd h (by simp)
      back := fun h ↦ absurd h (by simp) }
    ⟨⟨e, e.exists_covers_zero⟩, ⟨f, f.exists_covers_zero⟩⟩
    fun _ _ ↦ StageType.eq_of_zero _ _

/-! ### Already-covered points use no receiving -/

/-- Forth with a point that is already a coordinate of the cover (a repetition): no receiving
hypothesis appears. -/
example {α : Ordinal.{0}} {k : ℕ} {e : ModelExpansion M (blockStage (α + 1))}
    {f : ModelExpansion N (blockStage (α + 1))} {t : StageType.{0} (blockStage (α + 1)) k}
    {c : Fin k → M} {d : Fin k → N} (hc : e.1.Covers t c) (hd : f.1.Covers t d) (i : Fin k) :
    ∃ (e' : ModelExpansion M (blockStage α)) (f' : ModelExpansion N (blockStage α)) (k' : ℕ)
      (t' : StageType.{0} (blockStage α) k') (c' : Fin k' → M) (d' : Fin k' → N)
      (j : Fin k → Fin k') (i' : Fin k'),
      e'.1.Covers t' c' ∧ f'.1.Covers t' d' ∧ c' ∘ j = c ∧ d' ∘ j = d ∧ c' i' = c i :=
  exists_extend_covers_of_mem_range hc hd ⟨i, rfl⟩

/-- Back with a point that is already a coordinate of the cover: no receiving hypothesis
appears. -/
example {α : Ordinal.{0}} {k : ℕ} {e : ModelExpansion M (blockStage (α + 1))}
    {f : ModelExpansion N (blockStage (α + 1))} {t : StageType.{0} (blockStage (α + 1)) k}
    {c : Fin k → M} {d : Fin k → N} (hc : e.1.Covers t c) (hd : f.1.Covers t d) (i : Fin k) :
    ∃ (e' : ModelExpansion M (blockStage α)) (f' : ModelExpansion N (blockStage α)) (k' : ℕ)
      (t' : StageType.{0} (blockStage α) k') (c' : Fin k' → M) (d' : Fin k' → N)
      (j : Fin k → Fin k') (i' : Fin k'),
      e'.1.Covers t' c' ∧ f'.1.Covers t' d' ∧ c' ∘ j = c ∧ d' ∘ j = d ∧ d' i' = d i :=
  exists_extend_covers_back_of_mem_range hc hd ⟨i, rfl⟩

/-! ### Receiving -/

/-- Finite-extension receiving gives finite-cut receiving (the donors on one more point). -/
example {α : Ordinal.{0}} {R : Realization.{0, w} α M} (h : R.HasFiniteExtensionReceiving) :
    R.HasFiniteCutReceiving :=
  h.hasFiniteCutReceiving

/-- A type received for a donor at the cutoff `λ_α` has the stage reduction of the donor to
`λ_α`. -/
example {α : Ordinal.{0}} {n : ℕ} {D q : StageType.{0} (blockStage (α + 1)) n}
    (hq : q ∈ StageType.receivingFamily D (blockStage α : Label.{0})) :
    q.reduce (isSuccPrelimit_blockStage α) = D.reduce (isSuccPrelimit_blockStage α) :=
  StageType.reduce_eq_of_mem_receivingFamily _ hq

/-- The agreement of a received type with its donor after stage reduction to the cutoff `λ_α`
descends to every lower block stage `λ_β`, by the composition law of stage reduction. -/
example {α β : Ordinal.{0}} (hβα : β ≤ α) {n : ℕ} {D q : StageType.{0} (blockStage (α + 1)) n}
    (hq : q ∈ StageType.receivingFamily D (blockStage α : Label.{0})) :
    q.reduce (isSuccPrelimit_blockStage β) = D.reduce (isSuccPrelimit_blockStage β) := by
  rw [← q.reduce_reduce (isSuccPrelimit_blockStage α) _ (blockStage_mono hβα),
    ← D.reduce_reduce (isSuccPrelimit_blockStage α) _ (blockStage_mono hβα),
    StageType.reduce_eq_of_mem_receivingFamily _ hq]

/-! ### The code-level statement at `ℕ` -/

/-- The base language is in `Language.{0, 1}`. -/
example : Language.{0, 1} :=
  baseLanguage.{0}

/-- The match data on carriers in `Type`: expansions and charts live in `Type 1`, and the levels
in `Ordinal.{0}`. -/
example (hrec : FiniteExtensionReceiving.{0}) (M N : Type) [baseLanguage.{0}.Structure M]
    [baseLanguage.{0}.Structure N] {η : Ordinal.{0}} (hη : η < ω₁) :
    ExpansionMatchData.{0, 1, 0, 0, 1, 1, 1} baseLanguage.{0} M N η :=
  expansionMatchData hrec M N hη

/-- Condition 3 for codes on `ℕ`, conditional on finite-extension receiving. -/
example (hrec : FiniteExtensionReceiving.{0}) {η : Ordinal.{0}} (hη : η < ω₁)
    (c₁ c₂ : StructureSpace baseLanguage.{0})
    (h₁ : Nonempty (@ModelExpansion ℕ c₁.toStructure (blockStage η)))
    (h₂ : Nonempty (@ModelExpansion ℕ c₂.toStructure (blockStage η)))
    (θ : baseLanguage.{0}.Sentenceω) (hθ : θ.qrank ≤ η) :
    c₁ ∈ ModelsOf θ ↔ c₂ ∈ ModelsOf θ :=
  mem_modelsOf_iff_of_modelExpansions hrec hη c₁ c₂ h₁ h₂ θ hθ

/-! ### Without an initial match nothing follows -/

/-- An empty carrier has no model expansion: a model has a nonempty carrier. -/
example [IsEmpty M] (α : Ordinal.{0}) : IsEmpty (ModelExpansion M α) :=
  ⟨fun e ↦ isEmptyElim (Classical.choice e.2.isModel.nonempty)⟩

/-- On an empty carrier the match data relate no pair at any level: the laws alone give
nothing. -/
example (hrec : FiniteExtensionReceiving.{w}) [IsEmpty M] {η : Ordinal.{0}} (hη : η < ω₁)
    (α : Ordinal.{0}) (n : ℕ) (a : Fin n → M) (b : Fin n → N) :
    ¬ (expansionMatchData hrec M N hη).Match α n a b :=
  fun ⟨_, e, _⟩ ↦ isEmptyElim (Classical.choice e.2.isModel.nonempty)

end VaughtConjecture.Expansion
