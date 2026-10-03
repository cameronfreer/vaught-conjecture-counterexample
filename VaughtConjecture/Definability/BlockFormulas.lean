/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Karp.CarrierTheorem
import InfinitaryLogic.Lomega1omega.Theory
import VaughtConjecture.Definability.BlockStages
import VaughtConjecture.Definability.Syntax
import VaughtConjecture.Language.HullOperations

/-!
# Base-language formulas for the chart predicates at the block stages

Roadmap, the quantitative reconstruction pathway of `roadmap/COMPANIONS.md` ("Further companion
results"), row 1: definitions of the chart predicates at `λ_η` in the base language, of quantifier
rank at most `ω · η`; semantic contract, item 10 (definability).

Throughout, `η : Ordinal.{0}` is a countable block index (`η < ω₁`), `λ_η = ω + ω · η` is its block
stage (`blockStage η`), and a tuple `c` **covers** a stage type `t` in a realization when `c` is
injective and is evaluated to `t` (`Realization.Covers`).  The chart predicate of `t` in a model
expansion `R` to `λ_η` (`ModelExpansion`) is the set of tuples covering `t` in `R`; in the stage
chart language it is the relation of `t` (`Realization.toChartStructure`).

**Thresholds and block determination.**  A label of the block `[λ_η, λ_η + ω)` or the formal top
is determined by its **thresholds**, the answers to "is the label at least `λ_η + n`?" for all
`n : ℕ` (`Label.eq_of_forall_threshold_iff`).  Threshold data `U : CoverThresholds η` assigns to a
stage type `p` at `λ_η`, a cell `d` of `p` and `n : ℕ` a set of triples `(m, q, f)`: a stage type
`q` at `λ_η` on `m` points and an embedding `f : Fin k ↪ Fin m` of coordinates.  A tuple `c`
**extends to a cover** of such a triple in a realization `S` (`Realization.ExtendsToCover`) when
some tuple `s` covering `q` in `S` restricts along `f` to `c`.  The data are kept apart from their
law: **block determination** at `η` (`CoverThresholds.Determines`) is the statement that in every
model expansion `R` to `λ_{η+1}`, at every tuple `c` covering a type `t`, and at every cell `d` of
`t` that reduces to the formal top at `λ_η`, the label of `d` is at least `λ_η + n` exactly when `c`
extends to a cover of some triple of `U (t↓λ_η) d n` in the reduction of `R` to `λ_η`.  So the new
labels of the block are read off covers one block lower.  Block determination is expected to follow
from Layer 4, outputs 1–2 (the stable candidate and normalization; `roadmap/README.md`, Layer 4),
provided the stable value of a cell is the supremum over covers of an offset determined by the
cover's type at `λ_η`, the coordinate embedding and the transported cell; that shape — the
existential finite-data form of the threshold — is part of what remains to be proved.  An
eventual-value construction that allows decreases does not by itself establish this existential
finite-cover characterization; that characterization would then require a separate proof.  Here
block determination is a hypothesis.

**The formulas** (`blockFormula U η hη t`, a formula of the base language with free variables
`Fin k`, for a type `t` at `λ_η` on `k` points) are defined by recursion on `η`
(`Ordinal.limitRecOn`):

* at `η = 0`, the atomic formula of the relation symbol of `t↓ω` if that type is legal, and `⊥`
  otherwise (`chartAtom`);
* at `η + 1`, the formula of `t↓λ_η`, conjoined, over the cells `d` of `t` reducing to the formal
  top at `λ_η` and all `n : ℕ`, with the **threshold formula** of `(t↓λ_η, d, n)` if
  `λ_η + n ≤ t.label d` and with its negation otherwise (`succFormula`); the threshold formula
  (`thresholdFormula`) is the disjunction, over the triples `(m, q, f)` of `U (t↓λ_η) d n`, of the
  extension formula `∃ z̄ (φ_q(z̄) ∧ ⋀_i z_{f i} = x_i)` (`extendFormula`) of the formula `φ_q` of
  `q` at `λ_η`;
* at a limit `η`, the countable conjunction of the formulas of `t↓λ_ξ` over `ξ < η`
  (`limitFormula`).

**Results.**

* `qrank_blockFormula_le` (**unconditional**): the quantifier rank is at most `ω · η`.  At a
  successor each extension formula adds its arity `m < ω` to a formula of rank at most `ω · η`, and
  `ω · η + ω = ω · (η + 1)`.
* `realize_blockFormula_iff`, conditional on block determination (`CoverThresholds.Determines`) at
  the blocks below `η`: in **every** model expansion `R` to `λ_η` of a base structure `M` (carrier
  in the universe `w` at which block determination is assumed), the formula holds of a tuple
  exactly when the tuple covers `t` in `R`.  The formula does not depend on `R`, and the proof uses
  this uniformity: the successor step applies the induction hypothesis to the reduction of `R` to
  `λ_η`, at covers of every arity, and the limit step to its reductions to every `λ_ξ`.  The base
  case needs no hypothesis (the base reduct of `R` is `M`, and reduction from `λ_0` to `ω` is
  injective), and neither does the limit step (a type at a limit block stage is determined by its
  reductions, `StageType.eq_of_forall_reduce_eq_of_isSuccLimit`); the successor step uses block
  determination at `η` and the determination of a type at `λ_{η+1}` by its reduction and its
  thresholds (`StageType.eq_of_reduce_eq_of_threshold_iff`).
* Corollaries, under the same hypothesis: **uniqueness** of the model expansion to `λ_η` on a fixed
  carrier (`ModelExpansion.eq_of_determines`); **lifting along an isomorphism of base structures**
  by the same bijection (`ModelExpansion.map_eq_of_determines`), with `Equiv.refl` giving uniqueness
  again; the chart relations of the stage chart language at `λ_η` are defined by these base-language
  formulas (`ModelExpansion.relMap_toChartStructure_iff`); and, in pointed form, tuples
  back-and-forth equivalent at level `ω · η` in two base structures with model expansions to `λ_η`
  cover the same stage types (`ModelExpansion.covers_iff_of_bfEquiv`, by InfinitaryLogic's
  `BFEquiv_implies_agreeQR`).

**What is not claimed.**

* *No existence of expansions.*  The correctness theorem quantifies over model expansions; for a
  base structure with no model expansion to `λ_η` it says nothing, and at a structure that is not
  the base reduct of a model expansion the formula may hold of tuples that cover nothing, of a
  tuple with repeated coordinates for instance
  (`VaughtConjecture.Definability.BlockFormulasExamples`).  The sentence defining the existence of
  an expansion (row 2 of the pathway, the domain guard) is a separate theorem.
* *No uniqueness from definability alone.*  Uniqueness is downstream of block determination, which
  is already a pointwise statement about every expansion; definability supplies no other proof of
  it.  Conversely, a property fixed by automorphisms has no defining formula for that reason alone
  (semantic contract, item 10): the formulas here use the specific shape of the labels of a block,
  thresholds read off covers.
* *Syntax bounds only.*  `ω · η` bounds the rank of the constructed formula; it is not claimed to be
  attained or optimal (at `η = 1`, a type with no cell reducing to the top at `ω` has a formula of
  rank `0`), and it is not a Scott rank, an orbit rank, an internal Scott rank, a stabilization
  ordinal, or a height.
* *No complexity classes.*  No membership in `IsSigmaIn` or `IsPiIn` and no normal form is asserted.
* *Not rows 2–4.*  Nothing is claimed about the definability of the expansion domains, about Scott
  sentences, or about the relative transfer of the pathway.
* *Possibly vacuous.*  No model expansion is constructed in this repository at any stage, including
  `ω`, so the semantic theorems may be vacuous today; nonvacuity is not part of these statements.

## Placement

`roadmap/COMPANIONS.md`, Further companion results, Quantitative reconstruction, row 1.
-/

universe w w'

namespace VaughtConjecture

open Ordinal Order FirstOrder Language Structure baseLanguage BoundedFormulaω

/-! ### Threshold data, covers of extensions, and block determination -/

/-- **Threshold data** at the block `[λ_η, λ_η + ω)`: for a stage type `p` at `λ_η` on `k` points,
a cell `d` of `p` and `n : ℕ`, a set of triples `(m, q, f)`, each a stage type `q` at `λ_η` on `m`
points with an embedding `f : Fin k ↪ Fin m` of coordinates.  The covers of these triples are to
witness that the label of `d` at `λ_{η+1}` is at least `λ_η + n` (`CoverThresholds.Determines`). -/
def CoverThresholds (η : Ordinal.{0}) : Type 1 :=
  ∀ ⦃k : ℕ⦄ (p : StageType.{0} (blockStage η) k), Fin p.card → ℕ →
    Set (Σ m : ℕ, StageType.{0} (blockStage η) m × (Fin k ↪ Fin m))

/-- Equal stage types and cells at equal positions have the same threshold data. -/
theorem CoverThresholds.apply_congr {η : Ordinal.{0}} (U : CoverThresholds η) {k : ℕ}
    {p p' : StageType.{0} (blockStage η) k} (h : p = p') {i : Fin p.card} {j : Fin p'.card}
    (hij : (i : ℕ) = j) (n : ℕ) : U p i n = U p' j n := by
  subst h
  rw [Fin.ext hij]

namespace Realization

variable {α : Ordinal.{0}} {M : Type w} {k : ℕ}

/-- A tuple `c` **extends to a cover** of a triple `(m, q, f)` in `S` when some tuple `s` covering
`q` in `S` restricts along `f` to `c`. -/
def ExtendsToCover (S : Realization.{0, w} α M) (c : Fin k → M)
    (x : Σ m : ℕ, StageType.{0} α m × (Fin k ↪ Fin m)) : Prop :=
  ∃ s : Fin x.1 → M, s ∘ x.2.2 = c ∧ S.Covers x.2.1 s

variable {R : Realization.{0, w} α M}

/-- An injective tuple covers a stage type exactly when it is evaluated to it. -/
theorem covers_iff_eval {t : StageType.{0} α k} (u : Fin k ↪ M) :
    R.Covers t u ↔ R.eval u = some t :=
  ⟨fun h ↦ h.eval_eq, covers_of_eval u⟩

/-- **The base relations of an expansion**: in an expansion `R` of `M`, a relation holds of a tuple
exactly when the tuple is injective and the reduction to `ω` of its type is the stage type of the
relation. -/
theorem IsExpansionOf.relMap_iff [baseLanguage.{0}.Structure M] (hR : R.IsExpansionOf)
    (P : baseLanguage.{0}.Relations k) (c : Fin k → M) :
    RelMap P c ↔ ∃ hc : Function.Injective c,
      (R.eval ⟨c, hc⟩).map (StageType.reduce · isSuccLimit_omega0.isSuccPrelimit) =
        some (type P) := by
  obtain ⟨-, hstr⟩ := hR
  subst hstr
  -- After the substitution the instance is `(R.reduce _).toStructure`, whose `RelMap` unfolds by
  -- definition to the right-hand side (`Realization.relMap_toStructure`, `reduce_eval`).
  rfl

end Realization

/-- **Block determination** at `η`: in every model expansion `R` to `λ_{η+1}` of a base structure
on a carrier in the universe `w`, at every tuple `c` covering a type `t`, at every cell `d` of `t`
reducing to the formal top at `λ_η`, and for every `n : ℕ`, the label of `d` is at least
`λ_η + n` exactly when `c` extends to a cover of a triple of `U (t↓λ_η) d n` in the reduction of `R`
to `λ_η`.  It is expected to follow from Layer 4, outputs 1–2 (the stable candidate and
normalization), at the block `η`, provided the stable value of a cell is the supremum over covers of
an offset determined by the cover's type at `λ_η`, the coordinate embedding and the transported
cell; that shape — the existential finite-data form of the threshold — is part of what remains to
be proved.  An eventual-value construction that allows decreases does not by itself establish this
existential finite-cover characterization; that characterization would then require a separate
proof. -/
def CoverThresholds.Determines {η : Ordinal.{0}} (U : CoverThresholds η) : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M (blockStage (η + 1)))
    ⦃k : ℕ⦄ (t : StageType.{0} (blockStage (η + 1)) k) (c : Fin k → M), R.1.Covers t c →
    ∀ d : Fin t.card, (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤ → ∀ n : ℕ,
      (((blockStage η + n : Ordinal.{0}) : Label.{0}) ≤ t.label d ↔
        ∃ x ∈ U (t.reduce (isSuccPrelimit_blockStage η)) d n,
          (R.reduceBlock le_self_add).1.ExtendsToCover c x)

/-! ### The steps of the recursion -/

namespace BlockRecursion

variable {k : ℕ}

open Classical in
/-- The formula at `η = 0`: the atomic formula of the relation symbol of `t↓ω` if that stage type is
legal, and `⊥` otherwise. -/
noncomputable def chartAtom (t : StageType.{0} (blockStage 0) k) :
    baseLanguage.{0}.Formulaω (Fin k) :=
  if h : (t.reduce isSuccLimit_omega0.isSuccPrelimit).IsLegal then
    rel (symbol _ h) fun i ↦ Term.var (Sum.inl i)
  else ⊥

/-- The **threshold formula** of `(p, d, n)` for formulas `F` of the stage types at `λ_η`: the
disjunction, over the triples `(m, q, f)` of `U p d n`, of the extension formula
`∃ z̄ (F q (z̄) ∧ ⋀_i z_{f i} = x_i)`.  The index is countable since `η < ω₁`. -/
noncomputable def thresholdFormula {η : Ordinal.{0}} (U : CoverThresholds η) (hη : η < ω₁)
    (F : ∀ m, StageType.{0} (blockStage η) m → baseLanguage.{0}.Formulaω (Fin m))
    (p : StageType.{0} (blockStage η) k) (d : Fin p.card) (n : ℕ) :
    baseLanguage.{0}.Formulaω (Fin k) :=
  haveI : ∀ m, Countable (StageType.{0} (blockStage η) m) :=
    StageType.countable_of_lt_omega_one (blockStage_lt_omega_one hη)
  haveI : Encodable (U p d n) := Encodable.ofCountable _
  esup fun x : U p d n ↦ extendFormula (F x.1.1 x.1.2.1) x.1.2.2

/-- The **clause** of a cell `d` of `t` at `λ_{η+1}` and `n : ℕ`: the threshold formula of
`(t↓λ_η, d, n)` if `λ_η + n ≤ t.label d`, and its negation otherwise. -/
noncomputable def labelClause {η : Ordinal.{0}} (U : CoverThresholds η) (hη : η < ω₁)
    (F : ∀ m, StageType.{0} (blockStage η) m → baseLanguage.{0}.Formulaω (Fin m))
    (t : StageType.{0} (blockStage (η + 1)) k) (d : Fin t.card) (n : ℕ) :
    baseLanguage.{0}.Formulaω (Fin k) :=
  if ((blockStage η + n : Ordinal.{0}) : Label.{0}) ≤ t.label d then
    thresholdFormula U hη F (t.reduce (isSuccPrelimit_blockStage η)) d n
  else (thresholdFormula U hη F (t.reduce (isSuccPrelimit_blockStage η)) d n).not

/-- The formula at `η + 1`: the formula of `t↓λ_η`, conjoined with the clauses of the cells of `t`
reducing to the formal top at `λ_η`, for all `n : ℕ`. -/
noncomputable def succFormula {η : Ordinal.{0}} (U : CoverThresholds η) (hη : η < ω₁)
    (F : ∀ m, StageType.{0} (blockStage η) m → baseLanguage.{0}.Formulaω (Fin m))
    (t : StageType.{0} (blockStage (η + 1)) k) : baseLanguage.{0}.Formulaω (Fin k) :=
  haveI : Encodable
      {d : Fin t.card // (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤} :=
    Encodable.ofCountable _
  F k (t.reduce (isSuccPrelimit_blockStage η)) ⊓
    einf fun d : {d : Fin t.card // (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤} ↦
      einf fun n : ℕ ↦ labelClause U hη F t d n

/-- The formula at a limit `η`: the countable conjunction of the formulas of `t↓λ_ξ`, `ξ < η`. -/
noncomputable def limitFormula {η : Ordinal.{0}} (hη : η < ω₁)
    (F : ∀ ξ < η, ∀ m, StageType.{0} (blockStage ξ) m → baseLanguage.{0}.Formulaω (Fin m))
    (t : StageType.{0} (blockStage η) k) : baseLanguage.{0}.Formulaω (Fin k) :=
  haveI : Countable (Set.Iio η) := (Cardinal.countable_Iio_of_lt_omega_one hη).to_subtype
  haveI : Encodable (Set.Iio η) := Encodable.ofCountable _
  einf fun ξ : Set.Iio η ↦ F ξ.1 ξ.2 k (t.reduce (isSuccPrelimit_blockStage ξ.1))

end BlockRecursion

open BlockRecursion

/-! ### The formulas -/

/-- The **base-language formula of a stage type `t` at `λ_η`**, by recursion on `η`: the atomic
formula of `t↓ω` at `η = 0` (`chartAtom`), the formula of `t↓λ_ξ` with the threshold clauses of the
new block at `η = ξ + 1` (`succFormula`), and the conjunction of the lower formulas at a limit
(`limitFormula`).  It holds of exactly the covers of `t`, in every model expansion to `λ_η`,
conditional on block determination below `η` (`realize_blockFormula_iff`). -/
noncomputable def blockFormula (U : ∀ ξ : Ordinal.{0}, CoverThresholds ξ) (η : Ordinal.{0})
    (hη : η < ω₁) {k : ℕ} (t : StageType.{0} (blockStage η) k) :
    baseLanguage.{0}.Formulaω (Fin k) :=
  Ordinal.limitRecOn (motive := fun η ↦ η < ω₁ →
      ∀ k, StageType.{0} (blockStage η) k → baseLanguage.{0}.Formulaω (Fin k)) η
    (fun _ _ t ↦ chartAtom t)
    (fun ξ F hξ _ t ↦ succFormula (U ξ) (le_self_add.trans_lt hξ) (F (le_self_add.trans_lt hξ)) t)
    (fun _ _ F hξ _ t ↦ limitFormula hξ (fun ζ hζ ↦ F ζ hζ (hζ.trans hξ)) t)
    hη k t

variable (U : ∀ ξ : Ordinal.{0}, CoverThresholds ξ) {k : ℕ}

/-- The formula at `η = 0` is the atomic formula of `t↓ω`, or `⊥`. -/
theorem blockFormula_zero (hη : (0 : Ordinal.{0}) < ω₁) (t : StageType.{0} (blockStage 0) k) :
    blockFormula U 0 hη t = chartAtom t := by
  rw [blockFormula, Ordinal.limitRecOn_zero]

/-- The formula at `η + 1` is the formula of `t↓λ_η` with the threshold clauses. -/
theorem blockFormula_add_one {η : Ordinal.{0}} (hη : η + 1 < ω₁)
    (t : StageType.{0} (blockStage (η + 1)) k) :
    blockFormula U (η + 1) hη t =
      succFormula (U η) (le_self_add.trans_lt hη)
        (fun _ s ↦ blockFormula U η (le_self_add.trans_lt hη) s) t := by
  rw [blockFormula, Ordinal.limitRecOn_add_one]
  rfl

/-- The formula at a limit `η` is the conjunction of the formulas of the reductions. -/
theorem blockFormula_limit {η : Ordinal.{0}} (hl : IsSuccLimit η) (hη : η < ω₁)
    (t : StageType.{0} (blockStage η) k) :
    blockFormula U η hη t =
      limitFormula hη (fun ξ hξ _ s ↦ blockFormula U ξ (hξ.trans hη) s) t := by
  rw [blockFormula, Ordinal.limitRecOn_limit _ _ _ _ hl]
  rfl

/-! ### The rank bound -/

/-- The formula at `η = 0` has rank `0`. -/
theorem BlockRecursion.qrank_chartAtom (t : StageType.{0} (blockStage 0) k) :
    (chartAtom t).qrank = 0 := by
  unfold chartAtom
  split_ifs <;> rfl

/-- The successor step adds at most `ω` to the rank: if the formulas at `λ_η` have rank at most
`ω · η`, the formula at `λ_{η+1}` has rank at most `ω · (η + 1)`. -/
theorem BlockRecursion.qrank_succFormula_le {η : Ordinal.{0}} (V : CoverThresholds η) (hη : η < ω₁)
    {F : ∀ m, StageType.{0} (blockStage η) m → baseLanguage.{0}.Formulaω (Fin m)}
    (hF : ∀ m (q : StageType.{0} (blockStage η) m), (F m q).qrank ≤ ω * η)
    (t : StageType.{0} (blockStage (η + 1)) k) :
    (succFormula V hη F t).qrank ≤ ω * (η + 1) := by
  have hle : ω * η ≤ ω * (η + 1) := mul_le_mul_right le_self_add ω
  have hthr (p : StageType.{0} (blockStage η) k) (d : Fin p.card) (n : ℕ) :
      (thresholdFormula V hη F p d n).qrank ≤ ω * (η + 1) := by
    simp only [thresholdFormula, Formulaω.qrank, qrank_esup]
    refine Ordinal.iSup_le fun x ↦ ?_
    rw [← Formulaω.qrank, qrank_extendFormula, mul_add_one]
    exact add_le_add (hF _ _) (natCast_lt_omega0 _).le
  unfold succFormula
  refine (qrank_inf _ _).trans_le (max_le ((hF _ _).trans hle) ?_)
  simp only [qrank_einf]
  refine Ordinal.iSup_le fun d ↦ Ordinal.iSup_le fun n ↦ ?_
  unfold labelClause
  split_ifs
  · exact hthr _ _ _
  · exact (qrank_not _).trans_le (hthr _ _ _)

/-- **The rank bound** (unconditional): the formula of a stage type at `λ_η` has quantifier rank at
most `ω · η`.  This is a bound on the constructed syntax, not a Scott rank. -/
theorem qrank_blockFormula_le {η : Ordinal.{0}} (hη : η < ω₁)
    (t : StageType.{0} (blockStage η) k) : (blockFormula U η hη t).qrank ≤ ω * η := by
  induction η using Ordinal.limitRecOn generalizing k with
  | zero =>
    rw [blockFormula_zero, qrank_chartAtom]
    exact zero_le
  | add_one η ih =>
    rw [blockFormula_add_one]
    exact qrank_succFormula_le _ _ (fun m q ↦ ih _ q) t
  | limit η hl ih =>
    rw [blockFormula_limit _ hl]
    simp only [limitFormula, Formulaω.qrank, qrank_einf]
    exact Ordinal.iSup_le fun ξ ↦ (ih ξ.1 ξ.2 _ _).trans (mul_le_mul_right ξ.2.le ω)

/-! ### Correctness, conditional on block determination -/

section Correctness

variable {M : Type w} [baseLanguage.{0}.Structure M]

/-- The base case: the atomic formula of `t↓ω` holds of exactly the covers of `t`, in every model
expansion to `λ_0`.  No hypothesis is needed. -/
theorem BlockRecursion.realize_chartAtom (R : ModelExpansion M (blockStage 0))
    (t : StageType.{0} (blockStage 0) k) (c : Fin k → M) :
    (chartAtom t).Realize c ↔ R.1.Covers t c := by
  have hω : IsSuccPrelimit (ω : Ordinal.{0}) := isSuccLimit_omega0.isSuccPrelimit
  unfold chartAtom
  split_ifs with hl
  · rw [Formulaω.realize_def, realize_rel]
    -- `realize_rel` leaves the tuple as `fun i ↦ (Term.var (Sum.inl i)).realize _`, which is `c`
    -- by definition.
    change RelMap (symbol _ hl) c ↔ _
    refine (R.2.relMap_iff _ _).trans ⟨fun ⟨hc, he⟩ ↦ ?_, fun ⟨hc, he⟩ ↦ ⟨hc, by rw [he]; rfl⟩⟩
    obtain ⟨s, hs, hsr⟩ := Option.map_eq_some_iff.mp he
    exact ⟨hc, hs.trans (congrArg some
      (StageType.reduce_injective_of_le hω blockStage_zero.le hsr))⟩
  · simp only [Formulaω.realize_bot, false_iff]
    rintro ⟨hc, he⟩
    exact hl ((R.2.isModel.isLegal ⟨c, hc⟩ t he).reduce hω)

/-- The threshold formula holds of `c` exactly when `c` extends to a cover of one of its triples,
provided the formulas at `λ_η` hold of exactly the covers in `S`. -/
theorem BlockRecursion.realize_thresholdFormula {η : Ordinal.{0}} (V : CoverThresholds η)
    (hη : η < ω₁) {F : ∀ m, StageType.{0} (blockStage η) m → baseLanguage.{0}.Formulaω (Fin m)}
    {S : Realization.{0, w} (blockStage η) M}
    (hF : ∀ m (q : StageType.{0} (blockStage η) m) (s : Fin m → M),
      (F m q).Realize s ↔ S.Covers q s)
    (p : StageType.{0} (blockStage η) k) (d : Fin p.card) (n : ℕ) (c : Fin k → M) :
    (thresholdFormula V hη F p d n).Realize c ↔ ∃ x ∈ V p d n, S.ExtendsToCover c x := by
  simp only [thresholdFormula, Formulaω.realize_esup, realize_extendFormula, hF, Subtype.exists]
  exact ⟨fun ⟨x, hx, h⟩ ↦ ⟨x, hx, h⟩, fun ⟨x, hx, h⟩ ↦ ⟨x, hx, h⟩⟩

/-- The successor step, conditional on block determination (`CoverThresholds.Determines`) at the
block `η`, expected from Layer 4, outputs 1–2, under the proviso stated in the module docstring —
still to be proved: if the formulas at `λ_η` hold of exactly the covers in the reduction of `R` to
`λ_η`, then the formula of `t` at `λ_{η+1}` holds of exactly the covers of `t` in `R`. -/
theorem BlockRecursion.realize_succFormula {η : Ordinal.{0}} {V : CoverThresholds η}
    (hV : V.Determines.{w}) (hη : η < ω₁)
    {F : ∀ m, StageType.{0} (blockStage η) m → baseLanguage.{0}.Formulaω (Fin m)}
    (R : ModelExpansion M (blockStage (η + 1)))
    (hF : ∀ m (q : StageType.{0} (blockStage η) m) (s : Fin m → M),
      (F m q).Realize s ↔ (R.reduceBlock le_self_add).1.Covers q s)
    (t : StageType.{0} (blockStage (η + 1)) k) (c : Fin k → M) :
    (succFormula V hη F t).Realize c ↔ R.1.Covers t c := by
  have hthr := realize_thresholdFormula V hη hF (c := c)
  have hcl (d : Fin t.card) (n : ℕ) : (labelClause V hη F t d n).Realize c ↔
      (((blockStage η + n : Ordinal.{0}) : Label.{0}) ≤ t.label d ↔
        ∃ x ∈ V (t.reduce (isSuccPrelimit_blockStage η)) d n,
          (R.reduceBlock le_self_add).1.ExtendsToCover c x) := by
    unfold labelClause
    split_ifs with h
    · exact (hthr _ _ _).trans (iff_true_left h).symm
    · exact (Formulaω.realize_not.trans (not_congr (hthr _ _ _))).trans (iff_false_left h).symm
  simp only [succFormula, Formulaω.realize_inf, Formulaω.realize_einf, hF, Subtype.forall, hcl]
  refine ⟨fun ⟨⟨hc, he⟩, hl⟩ ↦ ?_, fun hcov ↦ ⟨hcov.reduce _, fun d hd n ↦ hV R t c hcov d hd n⟩⟩
  rw [ModelExpansion.reduceBlock_val, Realization.reduce_eval, Option.map_eq_some_iff] at he
  obtain ⟨t', ht', hred⟩ := he
  have hcov : R.1.Covers t' c := ⟨hc, ht'⟩
  suffices t' = t from this ▸ hcov
  refine StageType.eq_of_reduce_eq_of_threshold_iff hred fun i j hij hi n ↦ ?_
  rw [hV R t' c hcov i hi n, hl j ((StageType.label_congr hred hij).symm.trans hi) n,
    V.apply_congr hred hij n]

/-- The limit step: if, for every `ξ < η`, the formulas at `λ_ξ` hold of exactly the covers in the
reduction of `R` to `λ_ξ`, then the formula of `t` at the limit `λ_η` holds of exactly the covers
of `t` in `R`.  No hypothesis on the thresholds is needed. -/
theorem BlockRecursion.realize_limitFormula {η : Ordinal.{0}} (hl : IsSuccLimit η) (hη : η < ω₁)
    {F : ∀ ξ < η, ∀ m, StageType.{0} (blockStage ξ) m → baseLanguage.{0}.Formulaω (Fin m)}
    (R : ModelExpansion M (blockStage η))
    (hF : ∀ ξ (hξ : ξ < η) m (q : StageType.{0} (blockStage ξ) m) (s : Fin m → M),
      (F ξ hξ m q).Realize s ↔ (R.reduceBlock hξ.le).1.Covers q s)
    (t : StageType.{0} (blockStage η) k) (c : Fin k → M) :
    (limitFormula hη F t).Realize c ↔ R.1.Covers t c := by
  simp only [limitFormula, Formulaω.realize_einf, Subtype.forall, Set.mem_Iio]
  refine ⟨fun h ↦ ?_, fun hcov ξ hξ ↦ (hF ξ hξ _ _ _).mpr (hcov.reduce _)⟩
  replace h ξ (hξ : ξ < η) := (hF ξ hξ _ _ _).mp (h ξ hξ)
  obtain ⟨hc, he⟩ := h 0 hl.pos
  rw [ModelExpansion.reduceBlock_val, Realization.reduce_eval, Option.map_eq_some_iff] at he
  obtain ⟨t', ht', -⟩ := he
  have hcov : R.1.Covers t' c := ⟨hc, ht'⟩
  suffices t' = t from this ▸ hcov
  refine StageType.eq_of_forall_reduce_eq_of_isSuccLimit hl fun ξ hξ ↦ ?_
  exact Option.some_injective _ ((hcov.reduce _).eval_eq.symm.trans (h ξ hξ).eval_eq)

/-- **Correctness of the formulas**, conditional on block determination
(`CoverThresholds.Determines`) at the blocks below `η`, expected from Layer 4, outputs 1–2, under
the proviso stated in the module docstring — still to be proved.  In every model expansion `R` to
`λ_η` of a base structure `M`, the formula of `t` holds of a tuple exactly when the tuple covers `t`
in `R`: on every tuple, the empty tuple and tuples with repeated coordinates included.  The formula
does not depend on `R`. -/
theorem realize_blockFormula_iff {η : Ordinal.{0}} (hU : ∀ ξ < η, (U ξ).Determines.{w})
    (hη : η < ω₁) (R : ModelExpansion M (blockStage η)) (t : StageType.{0} (blockStage η) k)
    (c : Fin k → M) : (blockFormula U η hη t).Realize c ↔ R.1.Covers t c := by
  induction η using Ordinal.limitRecOn generalizing k with
  | zero =>
    rw [blockFormula_zero]
    exact realize_chartAtom R t c
  | add_one η ih =>
    rw [blockFormula_add_one]
    exact realize_succFormula (hU η (lt_add_one η)) _ R
      (fun m q s ↦ ih (fun ξ hξ ↦ hU ξ (hξ.trans (lt_add_one η))) _ _ q s) t c
  | limit η hl ih =>
    rw [blockFormula_limit _ hl]
    exact realize_limitFormula hl hη R
      (fun ξ hξ m q s ↦ ih ξ hξ (fun ζ hζ ↦ hU ζ (hζ.trans hξ)) _ _ q s) t c

end Correctness

/-! ### Corollaries -/

variable {U} {η : Ordinal.{0}}

/-- **Uniqueness of the model expansion on a fixed carrier**, conditional on block determination
(`CoverThresholds.Determines`) at the blocks below `η`, expected from Layer 4, outputs 1–2, under
the proviso stated in the module docstring — still to be proved.  Two model expansions of one base
structure to `λ_η` have the same covers, those of the formulas `blockFormula`, hence are equal. -/
theorem ModelExpansion.eq_of_determines (hU : ∀ ξ < η, (U ξ).Determines.{w}) (hη : η < ω₁)
    {M : Type w} [baseLanguage.{0}.Structure M] (R S : ModelExpansion M (blockStage η)) :
    R = S := by
  refine Subtype.ext (Realization.ext fun u ↦ Option.ext fun t ↦ ?_)
  rw [← Realization.covers_iff_eval, ← Realization.covers_iff_eval,
    ← realize_blockFormula_iff U hU hη R, realize_blockFormula_iff U hU hη S]

/-- **Lifting along an isomorphism of base structures by the same bijection**, conditional on block
determination (`CoverThresholds.Determines`) at the blocks below `η`, expected from Layer 4, outputs
1–2, under the proviso stated in the module docstring — still to be proved.  If
`e : M ≃[baseLanguage] N` is an isomorphism of base structures and `R` and `S` are model expansions
of `M` and `N` to `λ_η`, then `e` carries `R` to `S`: an isomorphism preserves every relation
defined by a formula of the base language. -/
theorem ModelExpansion.map_eq_of_determines (hU : ∀ ξ < η, (U ξ).Determines.{w}) (hη : η < ω₁)
    {M N : Type w} [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
    (e : M ≃[baseLanguage.{0}] N) (R : ModelExpansion M (blockStage η))
    (S : ModelExpansion N (blockStage η)) : R.1.map (e : M ≃ N) = S.1 := by
  refine Realization.ext fun u ↦ Option.ext fun t ↦ ?_
  rw [Realization.map_eval, ← Realization.covers_iff_eval, ← Realization.covers_iff_eval,
    ← realize_blockFormula_iff U hU hη R, ← realize_blockFormula_iff U hU hη S,
    Formulaω.realize_def, Formulaω.realize_def, BoundedFormulaω.realize_equiv e]
  have h1 : (e ∘ ⇑(u.trans (e : M ≃ N).symm.toEmbedding)) = ⇑u := funext fun i ↦ by simp
  have h2 : (e ∘ (Fin.elim0 : Fin 0 → M)) = Fin.elim0 := Subsingleton.elim _ _
  rw [h1, h2]

/-- **The chart relations are defined in the base language**, conditional on block determination
(`CoverThresholds.Determines`) at the blocks below `η`, expected from Layer 4, outputs 1–2, under
the proviso stated in the module docstring — still to be proved.  In the structure of a model
expansion `R` to `λ_η` in the stage chart language at `λ_η`, the relation of a legal stage type `t`
holds of a tuple exactly when the formula of `t` does. -/
theorem ModelExpansion.relMap_toChartStructure_iff (hU : ∀ ξ < η, (U ξ).Determines.{w})
    (hη : η < ω₁) {M : Type w} [baseLanguage.{0}.Structure M] (R : ModelExpansion M (blockStage η))
    (t : StageType.{0} (blockStage η) k) (ht : t.IsLegal) (c : Fin k → M) :
    @RelMap _ M R.1.toChartStructure k (stageChartLanguage.symbol t ht) c ↔
      (blockFormula U η hη t).Realize c :=
  -- The relation of `t` in `R.1.toChartStructure` unfolds by definition to `R.1.Covers t c`.
  (realize_blockFormula_iff U hU hη R t c).symm

/-- **Pointed agreement of covers from back-and-forth equivalence**, conditional on block
determination (`CoverThresholds.Determines`) at the blocks below `η`, expected from Layer 4, outputs
1–2, under the proviso stated in the module docstring — still to be proved (here at the universes of
both carriers).  Tuples `a` of `M` and `b` of `N` that are back-and-forth equivalent at level
`ω · η` in the base language cover the same stage types at `λ_η` in any model expansions of `M` and
`N` to `λ_η`. -/
theorem ModelExpansion.covers_iff_of_bfEquiv (hU : ∀ ξ < η, (U ξ).Determines.{w})
    (hU' : ∀ ξ < η, (U ξ).Determines.{w'}) (hη : η < ω₁) {M : Type w} {N : Type w'}
    [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
    (R : ModelExpansion M (blockStage η)) (S : ModelExpansion N (blockStage η)) {a : Fin k → M}
    {b : Fin k → N} (h : BFEquiv (L := baseLanguage.{0}) (ω * η) k a b)
    (t : StageType.{0} (blockStage η) k) : R.1.Covers t a ↔ S.1.Covers t b := by
  rw [← realize_blockFormula_iff U hU hη R, ← realize_blockFormula_iff U hU' hη S]
  exact BFEquiv_implies_agreeQR (ω * η) a b h _ (qrank_blockFormula_le U hη t)

end VaughtConjecture
