/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import VaughtConjecture.Definability.BlockFormulas
import VaughtConjecture.Geometry.IntervalPlan

/-!
# Examples for the base-language formulas of the chart predicates

Special cases of `VaughtConjecture.Definability.Syntax`, `VaughtConjecture.Definability.BlockStages`
and `VaughtConjecture.Definability.BlockFormulas`:

* the syntax: closing no variable, and the extension formula along the identity;
* `η = 0`: the formula is the atomic formula of `t↓ω` or `⊥`, of rank `0`, correct with no
  hypothesis (block determination below `0` is vacuous); an illegal type is never covered;
* `η = 1` (written `0 + 1`, the form of the successor equation): rank at most `ω`, correctness from
  block determination at `0`; a type with no cell reducing to the top at `ω` has a formula of rank
  `0`, and the clauses of a cell labelled with the formal top are the threshold formulas for every
  `n`;
* `η = ω`: the conjunction over the blocks `n < ω`, rank at most `ω · ω`, correctness from block
  determination at every `n < ω`; a type at `λ_ω = ω ^ 2` is determined by its reductions to the
  `λ_n`;
* `η = ω + 1`: the successor step above a limit, rank at most `ω · ω + ω`, with the limit formula as
  the formula of the reduction;
* repeated coordinates: in every model expansion a tuple with repeated coordinates covers nothing,
  so the formula fails there; in a base structure that is not a type assignment (every relation
  holds of every tuple) the formula at `η = 0` holds of a tuple with repeated coordinates, so the
  correctness theorem says nothing outside base reducts of model expansions;
* the empty tuple: the formula of the unique type on no points holds of `![]` whenever there is a
  model expansion;
* two carriers: lifting along an isomorphism of base structures, and `Equiv.refl` gives uniqueness
  again;
* a carrier universe other than `0`.

## Placement

`roadmap/COMPANIONS.md`, Further companion results, Quantitative reconstruction, row 1.
-/

universe w

namespace VaughtConjecture

open Ordinal Order FirstOrder Language Structure baseLanguage BoundedFormulaω BlockFormula Finset

/-! ### The syntax -/

/-- Closing no variable is the identity. -/
example {L : Language} {k : ℕ} (φ : L.Formulaω (Fin (k + 0))) : existsLastVars 0 φ = φ :=
  rfl

/-- Closing one variable is `existsLastVar`. -/
example {L : Language} {k : ℕ} (φ : L.Formulaω (Fin (k + 1))) :
    existsLastVars 1 φ = existsLastVar φ :=
  rfl

/-- The extension formula along the identity holds exactly where the formula does, and it adds
the arity to the rank. -/
example {L : Language} {M : Type} [L.Structure M] {k : ℕ} (ψ : L.Formulaω (Fin k))
    (c : Fin k → M) :
    (extendFormula ψ id).Realize c ↔ ψ.Realize c ∧ (extendFormula ψ id).qrank = ψ.qrank + k := by
  rw [realize_extendFormula, qrank_extendFormula]
  exact ⟨fun ⟨s, hs, h⟩ ↦ ⟨hs ▸ h, rfl⟩, fun ⟨h, _⟩ ↦ ⟨c, rfl, h⟩⟩

variable (U : ∀ ξ : Ordinal.{0}, CoverThresholds ξ) {k : ℕ}

/-! ### The base block, `η = 0` -/

/-- At `η = 0` the formula has rank `0`. -/
example (hη : (0 : Ordinal.{0}) < ω₁) (t : StageType.{0} (blockStage 0) k) :
    (blockFormula U 0 hη t).qrank = 0 := by
  rw [blockFormula_zero, qrank_chartAtom]

/-- At `η = 0` the formula of a type whose reduction to `ω` is illegal is `⊥`. -/
example (hη : (0 : Ordinal.{0}) < ω₁) (t : StageType.{0} (blockStage 0) k)
    (ht : ¬ (t.reduce isSuccLimit_omega0.isSuccPrelimit).IsLegal) : blockFormula U 0 hη t = ⊥ := by
  rw [blockFormula_zero, chartAtom, dite_eq_right ht]

/-- At `η = 0` correctness needs no hypothesis: block determination below `0` is vacuous. -/
example {M : Type w} [baseLanguage.{0}.Structure M] (hη : (0 : Ordinal.{0}) < ω₁)
    (R : ModelExpansion M (blockStage 0)) (t : StageType.{0} (blockStage 0) k) (c : Fin k → M) :
    (blockFormula U 0 hη t).Realize c ↔ R.1.Covers t c :=
  realize_blockFormula_iff U (fun _ hξ ↦ (not_lt_zero hξ).elim) hη R t c

/-- An illegal type is never covered, at any block stage: models have legal types. -/
example {M : Type w} [baseLanguage.{0}.Structure M] {η : Ordinal.{0}}
    (R : ModelExpansion M (blockStage η)) (t : StageType.{0} (blockStage η) k) (ht : ¬ t.IsLegal)
    (c : Fin k → M) : ¬ R.1.Covers t c :=
  fun ⟨_, he⟩ ↦ ht (R.2.isModel.isLegal _ _ he)

/-! ### The first successor block, `η = 1` -/

/-- At `η = 1` the rank is at most `ω`. -/
example (hη : (0 + 1 : Ordinal.{0}) < ω₁) (t : StageType.{0} (blockStage (0 + 1)) k) :
    (blockFormula U (0 + 1) hη t).qrank ≤ ω := by
  simpa using qrank_blockFormula_le U hη t

/-- At `η = 1` correctness needs block determination at `0`. -/
example {M : Type w} [baseLanguage.{0}.Structure M] (h0 : (U 0).Determines.{w})
    (hη : (0 + 1 : Ordinal.{0}) < ω₁) (R : ModelExpansion M (blockStage (0 + 1)))
    (t : StageType.{0} (blockStage (0 + 1)) k) (c : Fin k → M) :
    (blockFormula U (0 + 1) hη t).Realize c ↔ R.1.Covers t c :=
  realize_blockFormula_iff U (fun ξ hξ ↦ by
    obtain rfl : ξ = 0 := nonpos_iff_eq_zero.mp (Order.lt_add_one_iff.mp hξ)
    exact h0) hη R t c

/-- At `η = 1` a type with no cell reducing to the formal top at `ω` has a formula of rank `0`:
the bound `ω · η` is not attained. -/
example (hη : (0 + 1 : Ordinal.{0}) < ω₁) (t : StageType.{0} (blockStage (0 + 1)) k)
    (ht : ∀ d, (t.reduce (isSuccPrelimit_blockStage 0)).label d ≠ ⊤) :
    (blockFormula U (0 + 1) hη t).qrank = 0 := by
  rw [blockFormula_add_one]
  refine le_antisymm ?_ zero_le
  unfold succFormula
  refine (qrank_inf _ _).trans_le (max_le ?_ ?_)
  · exact (qrank_blockFormula_le U _ _).trans (by simp)
  · simp only [qrank_einf]
    exact Ordinal.iSup_le fun d ↦ absurd d.2 (ht d.1)

/-- The clauses of a cell labelled with the formal top are the threshold formulas themselves, for
every `n : ℕ`: such a cell needs the whole conjunction over `n`. -/
example {η : Ordinal.{0}} (hη : η < ω₁)
    (F : ∀ m, StageType.{0} (blockStage η) m → baseLanguage.{0}.Formulaω (Fin m))
    (t : StageType.{0} (blockStage (η + 1)) k) (d : Fin t.card) (hd : t.label d = ⊤) (n : ℕ) :
    labelClause (U η) hη F t d n =
      thresholdFormula (U η) hη F (t.reduce (isSuccPrelimit_blockStage η)) d n := by
  rw [labelClause, ite_eq_left (hd ▸ le_top)]

/-- A cell labelled `λ_η + j` has the threshold formula at `n = j` and its negation at
`n = j + 1`. -/
example {η : Ordinal.{0}} (hη : η < ω₁)
    (F : ∀ m, StageType.{0} (blockStage η) m → baseLanguage.{0}.Formulaω (Fin m))
    (t : StageType.{0} (blockStage (η + 1)) k) (d : Fin t.card) (j : ℕ)
    (hd : t.label d = ((blockStage η + j : Ordinal.{0}) : Label.{0})) :
    labelClause (U η) hη F t d j =
        thresholdFormula (U η) hη F (t.reduce (isSuccPrelimit_blockStage η)) d j ∧
      labelClause (U η) hη F t d (j + 1) =
        (thresholdFormula (U η) hη F (t.reduce (isSuccPrelimit_blockStage η)) d (j + 1)).not := by
  refine ⟨by rw [labelClause, ite_eq_left hd.ge], ?_⟩
  refine ite_eq_right ?_
  rw [hd, Nat.cast_add_one, ← add_assoc]
  exact not_le.mpr (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (lt_add_one _)))

/-! ### The first limit block, `η = ω` -/

/-- At `η = ω` the formula is the conjunction of the formulas of the reductions to the `λ_n`. -/
example (hη : ω < ω₁) (t : StageType.{0} (blockStage ω) k) :
    blockFormula U ω hη t =
      limitFormula hη (fun ξ hξ _ s ↦ blockFormula U ξ (hξ.trans hη) s) t :=
  blockFormula_limit U isSuccLimit_omega0 hη t

/-- At `η = ω` the rank is at most `ω · ω`. -/
example (hη : ω < ω₁) (t : StageType.{0} (blockStage ω) k) :
    (blockFormula U ω hη t).qrank ≤ ω * ω :=
  qrank_blockFormula_le U hη t

/-- At `η = ω` correctness needs block determination at every `n < ω`. -/
example {M : Type w} [baseLanguage.{0}.Structure M] (hU : ∀ n : ℕ, (U n).Determines.{w})
    (hη : ω < ω₁) (R : ModelExpansion M (blockStage ω)) (t : StageType.{0} (blockStage ω) k)
    (c : Fin k → M) : (blockFormula U ω hη t).Realize c ↔ R.1.Covers t c :=
  realize_blockFormula_iff U (fun ξ hξ ↦ by
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hξ
    exact hU n) hη R t c

/-- The block stage of `ω` is `ω ^ 2`. -/
example : blockStage (ω : Ordinal.{0}) = ω ^ 2 := by
  rw [blockStage_eq_mul, one_add_of_omega0_le le_rfl, sq]

/-- A type at `λ_ω` is determined by its reductions to the block stages `λ_n`, `n : ℕ`. -/
example (t t' : StageType.{0} (blockStage ω) k)
    (h : ∀ n : ℕ,
      t.reduce (isSuccPrelimit_blockStage n) = t'.reduce (isSuccPrelimit_blockStage n)) :
    t = t' :=
  StageType.eq_of_forall_reduce_eq_of_isSuccLimit isSuccLimit_omega0 fun ξ hξ ↦ by
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hξ
    exact h n

/-! ### A successor above a limit, `η = ω + 1` -/

/-- At `η = ω + 1` the rank is at most `ω · ω + ω`. -/
example (hη : ω + 1 < ω₁) (t : StageType.{0} (blockStage (ω + 1)) k) :
    (blockFormula U (ω + 1) hη t).qrank ≤ ω * ω + ω := by
  simpa [mul_add_one] using qrank_blockFormula_le U hη t

/-- At `η = ω + 1` the formula is the successor step over the limit formula at `ω`. -/
example (hη : ω + 1 < ω₁) (t : StageType.{0} (blockStage (ω + 1)) k) :
    blockFormula U (ω + 1) hη t =
      succFormula (U ω) (le_self_add.trans_lt hη)
        (fun _ s ↦ limitFormula (le_self_add.trans_lt hη)
          (fun ξ hξ _ s' ↦ blockFormula U ξ (hξ.trans (le_self_add.trans_lt hη)) s') s) t := by
  rw [blockFormula_add_one]
  congr 1
  funext m s
  exact blockFormula_limit U isSuccLimit_omega0 _ s

/-! ### Repeated coordinates -/

/-- In every model expansion, a tuple with repeated coordinates covers nothing, so the formula
fails there. -/
example {M : Type w} [baseLanguage.{0}.Structure M] {η : Ordinal.{0}}
    (hU : ∀ ξ < η, (U ξ).Determines.{w}) (hη : η < ω₁) (R : ModelExpansion M (blockStage η))
    (t : StageType.{0} (blockStage η) 2) (a : M) : ¬ (blockFormula U η hη t).Realize ![a, a] := by
  rw [realize_blockFormula_iff U hU hη R]
  rintro ⟨hc, -⟩
  exact absurd (hc (show ![a, a] 0 = ![a, a] 1 from rfl)) (by decide)

/-- The cell scheme on two points with one cell for each graded face of the interval plan. -/
private def pairCells : CellScheme (Fin 4) (Fin 2) :=
  ⟨univ, Geometry.intervalPlan univ, ![{0}, {1}, univ, univ], ![1, 1, 1, 2]⟩

/-- A stage type at `λ_0` on two points: the cells `pairCells`, the bottom rows and the bottom
label. -/
private def pair : StageType.{0} (blockStage 0) 2 where
  card := 4
  toCellScheme := pairCells
  rows := CellScheme.Rows.bot _
  label _ := ⊥
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ by
    fin_cases d <;> simp [pairCells, CellScheme.gradedIndex, Geometry.mem_intervalPlan]⟩⟩
  isCoded _ _ := WithBot.bot_lt_coe _
  isLawful := CellScheme.Rows.isLawful_const_bot
  atStage _ := Label.atStage_bot

/-- Every graded face of `pairCells` is the graded index of a cell. -/
private theorem isComplete_pairCells : pairCells.IsComplete := by
  rintro ⟨C, j⟩ ⟨hC, hpos, hle⟩
  have hj : j ≤ 2 := hle.trans (card_le_univ C)
  simp only at hpos hle
  interval_cases j <;> revert C <;> decide

/-- `pair` is legal. -/
private theorem isLegal_pair : pair.IsLegal :=
  StageType.isLegal_iff.mpr ⟨CellScheme.Rows.isConsistent_bot, CellScheme.Rows.isBountiful_bot,
    isComplete_pairCells⟩

/-- The base structure on one point in which every relation holds of every tuple.  It is not a
type assignment. -/
@[instance_reducible] private def fullStructure : baseLanguage.{0}.Structure Unit where
  funMap f := isEmptyElim f
  RelMap _ _ := True

/-- **Outside base reducts of model expansions the formula may hold of a tuple with repeated
coordinates**: in the base structure in which every relation holds of every tuple, the formula of
the legal type `pair` at `η = 0` holds of `![(), ()]`.  The correctness theorem says nothing here,
since this structure is not the base reduct of a model expansion. -/
example (hη : (0 : Ordinal.{0}) < ω₁) :
    letI := fullStructure
    (blockFormula U 0 hη pair).Realize ![(), ()] ∧ ¬ Function.Injective ![(), ()] := by
  let := fullStructure
  refine ⟨?_, fun h ↦ absurd (h (show ![(), ()] 0 = ![(), ()] 1 from rfl)) (by decide)⟩
  rw [blockFormula_zero, chartAtom, dite_eq_left (isLegal_pair.reduce _)]
  trivial

/-! ### The empty tuple -/

/-- The formula of the unique stage type on no points holds of the empty tuple whenever there is a
model expansion. -/
example {M : Type w} [baseLanguage.{0}.Structure M] {η : Ordinal.{0}}
    (hU : ∀ ξ < η, (U ξ).Determines.{w}) (hη : η < ω₁) (R : ModelExpansion M (blockStage η))
    (t : StageType.{0} (blockStage η) 0) : (blockFormula U η hη t).Realize (![] : Fin 0 → M) := by
  rw [realize_blockFormula_iff U hU hη R]
  obtain ⟨t', ht'⟩ := R.exists_covers_zero
  rwa [StageType.eq_of_zero t t']

/-! ### Two carriers -/

/-- Lifting along the identity isomorphism is uniqueness again. -/
example {M : Type w} [baseLanguage.{0}.Structure M] {η : Ordinal.{0}}
    (hU : ∀ ξ < η, (U ξ).Determines.{w}) (hη : η < ω₁) (R S : ModelExpansion M (blockStage η)) :
    R = S := by
  have h := ModelExpansion.map_eq_of_determines hU hη (Language.Equiv.refl baseLanguage.{0} M) R S
  exact Subtype.ext ((Realization.map_refl R.1).symm.trans h)

/-- Lifting along an isomorphism `e` and back along its inverse. -/
example {M N : Type w} [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
    {η : Ordinal.{0}} (hU : ∀ ξ < η, (U ξ).Determines.{w}) (hη : η < ω₁)
    (e : M ≃[baseLanguage.{0}] N) (R : ModelExpansion M (blockStage η))
    (S : ModelExpansion N (blockStage η)) :
    R.1.map (e : M ≃ N) = S.1 ∧ S.1.map (e.symm : N ≃ M) = R.1 :=
  ⟨ModelExpansion.map_eq_of_determines hU hη e R S,
    ModelExpansion.map_eq_of_determines hU hη e.symm S R⟩

/-! ### A carrier universe other than `0` -/

/-- Correctness on carriers in the universe `2`, from block determination at that universe. -/
example {M : Type 2} [baseLanguage.{0}.Structure M] {η : Ordinal.{0}}
    (hU : ∀ ξ < η, (U ξ).Determines.{2}) (hη : η < ω₁) (R : ModelExpansion M (blockStage η))
    (t : StageType.{0} (blockStage η) k) (c : Fin k → M) :
    (blockFormula U η hη t).Realize c ↔ R.1.Covers t c :=
  realize_blockFormula_iff U hU hη R t c

end VaughtConjecture
