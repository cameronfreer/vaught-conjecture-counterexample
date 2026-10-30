/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.CountablePrime
import VaughtConjecture.Continuation.ExactAge
import VaughtConjecture.Correspondence.Charts.UniversalConstruction
import VaughtConjecture.Language.HullOperations

/-!
# Chart formulas and atomicity in the stage chart language

Roadmap, Layer 4 (terminal classification by exact ages: homogeneity, orbit formulas, atomicity).
This file states, in the stage chart language, the rooted back-and-forth family of the exact-age
comparison, the first-order chart formulas, and the atomicity of a realization with an exact age
over its own complete first-order theory.  Every statement here is a native construction; [AFK26]
states nothing about atomicity.  The statements are stated, not proved, except one composition
(the instance at the universal realization from the general instance).

**The language.**  Every statement about realizations is in the **stage chart language**
`stageChartLanguage α`: one `n`-ary relation symbol `P_t` (`stageChartLanguage.symbol t ht`) for
each legal stage type `t` at stage `α` on `n` points, nullary symbols included, and no function
symbols.  A realization `R` on `M` is a structure of this language through
`Realization.toChartStructure`: `P_t` holds of a tuple exactly when the tuple covers `t`
(`Realization.Covers`, `Realization.relMap_toChartStructure`).  The general isolation statements
are in an arbitrary first-order language.  The instance at the universal realization is at the
block stage `α = blockStage β`.

**The reference model.**  Any realization `R : Realization α M` with an age family `A`, with the
hypotheses written out on each statement (no bundled hypothesis): exact consistency
(`R.IsConsistent`), covering (`R.IsCovering`), **age inclusion** (every actual type of `R` lies in
`A`), and **exact receiving within `A`** (`R.ExactReceivingWithin A`).  The statements of
atomicity and coverage add legal types (`R.HasLegalTypes`): the stage chart language names only
legal types, so a tuple whose covers all have illegal types is not visible to it.  The rooted chart
family and its specification do not need legality and do not assume it.  The statements that
mention the complete theory of the reference add `Nonempty M`.  The theory is the first-order
complete theory of the chart structure of `R`, `(stageChartLanguage α).completeTheory M`
(`FirstOrder.Language.completeTheory`); atomicity and isolation are ComputableModelTheory's
`FirstOrder.Language.IsAtomic` and `FirstOrder.Language.IsolatesTuple`, with modelhood of the
theory stated separately (`N ⊨ T`).  No countability of the carriers or of the language is assumed
anywhere in this file, and the carriers compared may lie in different universes.  The age family is
general; strongly coded legal types are the specialization at the universal realization.

**The rooted chart family.**  The matching is `Realization.CoverMatch` of the exact-age comparison
(`VaughtConjecture.Continuation.ExactAge`), which mentions no language: `a = x ∘ s` and `b = y ∘ s`
for covers `x`, `y` of one common stage type containing the cores at common positions.  In the
base language its back-and-forth family is `Realization.rootedPotentialIso`, for expansions of base
structures.  In the stage chart language matched tuples have the same atomic type under exact
consistency alone, with no expansion hypothesis (stated:
`Realization.CoverMatchChartSameAtomicTypeTarget`); with the forth and back steps already proved
(`Realization.CoverMatch.exists_snoc`), the matching is then a potential isomorphism of the chart
structures whose family is exactly the matching (stated: `Realization.RootedChartFamilyTarget`),
to be declared as `Realization.rootedChartPotentialIso` once the first is proved.  Matched tuples
are back-and-forth equivalent at every ordinal and satisfy the same infinitary and first-order
formulas of the stage chart language (stated: `Realization.CoverMatchChartAgreementTarget`).
Root compatibility of matched tuples does not depend on the language and is proved
(`Realization.CoverMatch.root_compatible`).

**Three kinds of formulas.**

* *Formulas defining charts.*  In the stage chart language a chart is atomic: `P_t(x̄)` holds
  exactly of the covers of `t`.  The **chart formula** `stageChartLanguage.chartFormula t ht s` of
  a legal type `t` on `k` points along a selector `s : Fin n → Fin k` (not necessarily injective;
  `n = 0` allowed) is the first-order formula `∃ z̄, P_t(z̄) ∧ ⋀_{i < n} z_{s i} = x_i`.  Its
  semantics in any structure of the language (stated: `ChartFormulaRealizeTarget`); it holds of
  the selection `x ∘ s` of a cover `x` of `t` (stated:
  `Realization.ChartFormulaRealizeOfCoversTarget`); in a reference model it defines exactly the
  tuples matched to `x ∘ s` (stated: `Realization.ChartFormulaCoverMatchTarget`).
* *Formulas defining orbits.*  On countable carriers the chart formula is expected to define the
  automorphism orbit of `x ∘ s`; orbits are not stated here (later).
* *Isolating formulas.*  In a reference model the chart formula of `x ∘ s` isolates its complete
  first-order type over the complete theory of the reference: it holds of `x ∘ s`, and every tuple
  satisfying it, in any structure of the language that is a model of that theory, on any carrier,
  has the first-order type of `x ∘ s` (stated: `Realization.ChartFormulaIsolationTarget`, and in
  the form of `IsolatesTuple`, `Realization.ChartFormulaIsolatesTupleTarget`).

Hence the reference model is atomic over its complete theory (stated:
`Realization.ChartAtomicTarget`), and among the models of that theory, on arbitrary carriers,
atomicity is **chart coverage** (`IsChartCovered`: every finite tuple, the empty tuple and tuples
with repeated entries included, is a selection of a tuple in some chart relation, nullary chart
relations included) (stated: `Realization.ChartCoverageAtomicityTarget`).

**General isolation and atomic models.**  Construction-free statements in an arbitrary
first-order language, kept in their own section: isolation from one first-order type in the
structure's own complete theory, without automorphisms
(`IsolatesTupleOfSameFormulaTypeTarget`); an isolating formula isolates each of its realizations in
every model of the theory (`IsolatesTupleOfRealizeTarget`); two atomic models of one complete
theory are potentially isomorphic through the tuples of the same first-order type
(`AtomicModelsPotentialIsoTarget`).

**The universal realization.**  At `α = blockStage β` with the strongly coded legal types as age:
atomicity and coverage for every realization in the strongly coded receiving class with exact
receiving of strongly coded legal donors (stated: `Realization.StronglyCodedChartAtomicityTarget`),
and, through the realization given by `exists_stronglyCodedUniversalRealization` (no canonical
choice is made), the same for a realization on every countably infinite carrier when `β < ω₁`
(`Realization.UniversalChartAtomicityTarget`, proved from the former:
`Realization.universalChartAtomicityTarget_of_stronglyCodedChartAtomicityTarget`).

**What is not stated here.**  Descent to a base language is a separate later question, for each of
the two bases: the base language `baseLanguage` of the four-family sentence (where charts are
infinitary block formulas) and the base template language `baseTemplateLanguage`.  No first-order
atomicity is claimed for either reduct.  Countable conclusions, namely primeness of the reference
among the models of its theory, isomorphism of countable atomic models with it, and chart formulas
as automorphism orbit formulas, are later and separate from the arbitrary-carrier statements of
this file (agreement of matched tuples, isolation, atomicity, coverage), which assert no
isomorphism.  Scott sentences, ranks, class-level matching in `templateLanguage` and the
countability of the stage chart language are not stated.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v w w' uι uβ u₁ v₁

namespace VaughtConjecture

open FirstOrder Language Structure
open scoped Ordinal

/-! ### General isolation and atomic models -/

section General

/-- **Target: isolation from one first-order type.**  In a nonempty structure `M` of any
first-order language, a formula `φ` that holds of a tuple `a`, all of whose realizations in `M`
have the first-order type of `a`, isolates `a` over the complete theory of `M`.  No automorphism
and no countability enters: this is the form of `FirstOrder.Language.isolatesTuple_of_orbit_formula`
with agreement of first-order types in place of automorphisms.  Stated; open. -/
def IsolatesTupleOfSameFormulaTypeTarget : Prop :=
  ∀ ⦃L : Language.{u₁, v₁}⦄ ⦃M : Type w⦄ [L.Structure M], Nonempty M →
    ∀ ⦃n : ℕ⦄ (φ : L.Formula (Fin n)) (a : Fin n → M), φ.Realize a →
      (∀ b : Fin n → M, φ.Realize b → SameFormulaType (L := L) a b) →
        IsolatesTuple (L.completeTheory M) φ a

/-- **Target: an isolating formula isolates each of its realizations.**  If `φ` isolates a tuple
`a` of `M` over a theory `T`, then it isolates every tuple `b` satisfying it in any nonempty model
`N` of `T`, on a carrier in any universe.  Stated; open. -/
def IsolatesTupleOfRealizeTarget : Prop :=
  ∀ ⦃L : Language.{u₁, v₁}⦄ ⦃M : Type w⦄ [L.Structure M] ⦃N : Type w'⦄ [L.Structure N]
    (T : L.Theory), Nonempty N → N ⊨ T → ∀ ⦃n : ℕ⦄ (φ : L.Formula (Fin n)) (a : Fin n → M)
      (b : Fin n → N), IsolatesTuple T φ a → φ.Realize b → IsolatesTuple T φ b

/-- **Target: atomic models of one complete theory are potentially isomorphic.**  Let `M` be a
nonempty structure of a relational language and `N` a model of the complete theory of `M`, on
carriers in any universes.  If both are atomic over that theory, the pairs of tuples with the same
first-order type form a potential isomorphism (InfinitaryLogic's `PotentialIso`).  No countability
of the carriers or of the language.  Stated; open. -/
def AtomicModelsPotentialIsoTarget : Prop :=
  ∀ ⦃L : Language.{u₁, v₁}⦄ [L.IsRelational] ⦃M : Type w⦄ [L.Structure M] ⦃N : Type w'⦄
    [L.Structure N], Nonempty M → N ⊨ L.completeTheory M → IsAtomic (L.completeTheory M) M →
      IsAtomic (L.completeTheory M) N →
        ∃ P : PotentialIso L M N, P.family = {q | SameFormulaType (L := L) q.2.1 q.2.2}

end General

/-! ### Chart formulas and chart coverage -/

namespace stageChartLanguage

variable {α : Ordinal.{u}}

/-- The **chart formula** of a legal stage type `t` on `k` points along a selector
`s : Fin n → Fin k`: the first-order formula `∃ z̄, P_t(z̄) ∧ ⋀_{i < n} z_{s i} = x_i` of the stage
chart language, in the free variables `x_0, …, x_{n-1}`, with one block of `k` existential
quantifiers over a quantifier-free matrix.  It holds of a tuple when the tuple is a selection along
`s` of a tuple in the relation `P_t`.  The selector need not be injective, so repeated entries are
selected, and `n = 0` is allowed. -/
noncomputable def chartFormula {k n : ℕ} (t : StageType.{u} α k) (ht : t.IsLegal)
    (s : Fin n → Fin k) : (stageChartLanguage.{u} α).Formula (Fin n) :=
  Formula.iExs (Fin k)
    ((symbol t ht).formula (fun j ↦ Term.var (Sum.inr j)) ⊓
      Formula.iInf fun i ↦ (Term.var (Sum.inr (s i))).equal (Term.var (Sum.inl i)))

end stageChartLanguage

/-- A structure of the stage chart language is **chart covered** when every finite tuple, the empty
tuple and tuples with repeated entries included, is a selection `z ∘ s` of a tuple `z` in some
chart relation `P_t`, along a selector `s` that need not be injective; nullary chart relations are
allowed. -/
def IsChartCovered (α : Ordinal.{u}) (N : Type w) [(stageChartLanguage.{u} α).Structure N] :
    Prop :=
  ∀ ⦃n : ℕ⦄ (a : Fin n → N), ∃ (k : ℕ) (t : StageType.{u} α k) (ht : t.IsLegal)
    (z : Fin k → N) (s : Fin n → Fin k), RelMap (stageChartLanguage.symbol t ht) z ∧ z ∘ s = a

/-- **Target: the semantics of the chart formula.**  In any structure of the stage chart language,
the chart formula of `t` along `s` holds of a tuple `b` exactly when `b` is the selection along `s`
of a tuple in the relation `P_t`.  Stated; open. -/
def ChartFormulaRealizeTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃N : Type w⦄ [(stageChartLanguage.{u} α).Structure N] ⦃k : ℕ⦄
    (t : StageType.{u} α k) (ht : t.IsLegal) ⦃n : ℕ⦄ (s : Fin n → Fin k) (b : Fin n → N),
      (stageChartLanguage.chartFormula t ht s).Realize b ↔
        ∃ z : Fin k → N, RelMap (stageChartLanguage.symbol t ht) z ∧ z ∘ s = b

namespace Realization

/-! ### The rooted chart family -/

section Rooted

/-- **Target: matched tuples have the same atomic type in the stage chart language.**  For
exactly consistent realizations `R` on `M` and `R'` on `N` at one stage, read as structures of the
stage chart language (`Realization.toChartStructure`), tuples matched through covers
(`Realization.CoverMatch`) satisfy the same atomic formulas: equalities, by injectivity of the two
covers, and chart relations, since a selection of a cover along an injective selector covers the
face of the common type (`Realization.Covers.eval_comp`).  This is the compatibility of the rooted
chart family; no expansion, covering, age, receiving or legality hypothesis enters, and the
carriers may lie in different universes.  Stated; open. -/
def CoverMatchChartSameAtomicTypeTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ ⦃N : Type w⦄ ⦃k₀ : ℕ⦄ (R : Realization.{u, v} α M)
    (R' : Realization.{u, w} α N) (x₀ : Fin k₀ → M) (y₀ : Fin k₀ → N), R.IsConsistent →
      R'.IsConsistent → ∀ ⦃n : ℕ⦄ ⦃a : Fin n → M⦄ ⦃b : Fin n → N⦄,
        CoverMatch R R' x₀ y₀ n a b →
          letI := R.toChartStructure
          letI := R'.toChartStructure
          SameAtomicType (L := stageChartLanguage.{u} α) a b

/-- **Target: the rooted chart family.**  Let `R` on `M` and `R'` on `N` be exactly consistent
covering realizations at one stage, with cores `x₀` and `y₀` covering a common stage type `p`.  If
every actual type of a cover containing the core at positions `ι` lies in `A m ι`, in both (age
inclusion), and both have exact receiving within `A` at their cores, then some potential
isomorphism of the chart structures (`Realization.toChartStructure`) has as its family exactly the
tuples matched through covers at the cores (`Realization.CoverMatch`).  Its empty pair is
`CoverMatch.zero`, its compatibility is `CoverMatchChartSameAtomicTypeTarget`, and forth and back
are `CoverMatch.exists_snoc`; the construction is to be declared as
`Realization.rootedChartPotentialIso`.  No expansion, legality or countability hypothesis; the
carriers may lie in different universes.  Stated; open. -/
def RootedChartFamilyTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ ⦃N : Type w⦄ ⦃k₀ : ℕ⦄ (R : Realization.{u, v} α M)
    (R' : Realization.{u, w} α N) (x₀ : Fin k₀ → M) (y₀ : Fin k₀ → N) (p : StageType.{u} α k₀)
    (A : ∀ m, (Fin k₀ ↪ Fin m) → Set (StageType.{u} α m)),
    R.IsConsistent → R.IsCovering → R'.IsConsistent → R'.IsCovering →
    (∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (ι : Fin k₀ ↪ Fin m) (D : StageType.{u} α m),
      R.eval s = some D → ⇑s ∘ ι = x₀ → D ∈ A m ι) →
    (∀ ⦃m : ℕ⦄ (s : Fin m ↪ N) (ι : Fin k₀ ↪ Fin m) (D : StageType.{u} α m),
      R'.eval s = some D → ⇑s ∘ ι = y₀ → D ∈ A m ι) →
    R.ExactReceivingWithinAt x₀ A → R'.ExactReceivingWithinAt y₀ A →
    R.Covers p x₀ → R'.Covers p y₀ →
      letI := R.toChartStructure
      letI := R'.toChartStructure
      ∃ P : PotentialIso (stageChartLanguage.{u} α) M N,
        P.family = {q | CoverMatch R R' x₀ y₀ q.1 q.2.1 q.2.2}

/-- **Target: agreement of matched tuples in the stage chart language.**  Under the hypotheses of
the rooted chart family (`RootedChartFamilyTarget`), tuples matched through covers at the cores
are back-and-forth equivalent in the stage chart language at every ordinal of every universe
(InfinitaryLogic's `BFEquiv`), satisfy the same infinitary formulas of the stage chart language,
branching over any carrier `ι` in any universe, and have the same first-order type
(`FirstOrder.Language.SameFormulaType`).  No countability; the carriers may lie in different
universes.  Stated; open. -/
def CoverMatchChartAgreementTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ ⦃N : Type w⦄ ⦃k₀ : ℕ⦄ (R : Realization.{u, v} α M)
    (R' : Realization.{u, w} α N) (x₀ : Fin k₀ → M) (y₀ : Fin k₀ → N) (p : StageType.{u} α k₀)
    (A : ∀ m, (Fin k₀ ↪ Fin m) → Set (StageType.{u} α m)),
    R.IsConsistent → R.IsCovering → R'.IsConsistent → R'.IsCovering →
    (∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (ι : Fin k₀ ↪ Fin m) (D : StageType.{u} α m),
      R.eval s = some D → ⇑s ∘ ι = x₀ → D ∈ A m ι) →
    (∀ ⦃m : ℕ⦄ (s : Fin m ↪ N) (ι : Fin k₀ ↪ Fin m) (D : StageType.{u} α m),
      R'.eval s = some D → ⇑s ∘ ι = y₀ → D ∈ A m ι) →
    R.ExactReceivingWithinAt x₀ A → R'.ExactReceivingWithinAt y₀ A →
    R.Covers p x₀ → R'.Covers p y₀ →
    ∀ ⦃n : ℕ⦄ ⦃a : Fin n → M⦄ ⦃b : Fin n → N⦄, CoverMatch R R' x₀ y₀ n a b →
      letI := R.toChartStructure
      letI := R'.toChartStructure
      (∀ β : Ordinal.{uβ}, BFEquiv (L := stageChartLanguage.{u} α) β n a b) ∧
        (∀ (ι : Type uι) (φ : (stageChartLanguage.{u} α).BoundedFormulaInf ι (Fin n) 0),
          FormulaInf.Realize φ a ↔ FormulaInf.Realize φ b) ∧
        SameFormulaType (L := stageChartLanguage.{u} α) a b

end Rooted

/-! ### Chart formulas in a reference model -/

section Reference

/-- **Target: the chart formula holds of a selection of a cover.**  If `x` covers a legal stage
type `t` in `R`, the chart formula of `t` along any selector `s` holds of `x ∘ s` in the chart
structure of `R`.  No hypothesis on `R`.  Stated; open. -/
def ChartFormulaRealizeOfCoversTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ (R : Realization.{u, v} α M) ⦃k : ℕ⦄
    (t : StageType.{u} α k) (ht : t.IsLegal) (x : Fin k → M), R.Covers t x →
      ∀ ⦃n : ℕ⦄ (s : Fin n → Fin k),
        letI := R.toChartStructure
        (stageChartLanguage.chartFormula t ht s).Realize (x ∘ s)

/-- **Target: the chart formula defines the matched tuples.**  Let `R` be an exactly consistent
covering realization whose actual types all lie in `A`, with exact receiving within `A`.  If `x`
covers a legal stage type `t`, then, in the chart structure of `R`, the chart formula of `t` along
`s` holds of a tuple `b` exactly when `b` is matched through covers to `x ∘ s` (at the empty
cores).  No countability and no legality of the other types.  Stated; open. -/
def ChartFormulaCoverMatchTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ (R : Realization.{u, v} α M)
    (A : ∀ m, Set (StageType.{u} α m)), R.IsConsistent → R.IsCovering →
    (∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (D : StageType.{u} α m), R.eval s = some D → D ∈ A m) →
    R.ExactReceivingWithin A →
    ∀ ⦃k : ℕ⦄ (t : StageType.{u} α k) (ht : t.IsLegal) (x : Fin k → M), R.Covers t x →
      ∀ ⦃n : ℕ⦄ (s : Fin n → Fin k) (b : Fin n → M),
        (letI := R.toChartStructure
         (stageChartLanguage.chartFormula t ht s).Realize b) ↔
          CoverMatch R R (Fin.elim0 : Fin 0 → M) Fin.elim0 n (x ∘ s) b

/-- **Target: the chart formula isolates the first-order type of a selection of a cover.**  Let
`R` on a nonempty carrier `M` be an exactly consistent covering realization whose actual types all
lie in `A`, with exact receiving within `A`, and let `T` be the complete first-order theory of its
chart structure.  If `x` covers a legal stage type `t`, then the chart formula of `t` along `s`
holds of `x ∘ s`, and every tuple `b` satisfying it in any structure `N` of the stage chart language
that is a model of `T`, on a carrier in any universe and not necessarily the chart structure of a
realization, has the first-order type of `x ∘ s`.  No countability.  Stated; open. -/
def ChartFormulaIsolationTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ (R : Realization.{u, v} α M)
    (A : ∀ m, Set (StageType.{u} α m)), Nonempty M → R.IsConsistent → R.IsCovering →
    (∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (D : StageType.{u} α m), R.eval s = some D → D ∈ A m) →
    R.ExactReceivingWithin A →
    ∀ ⦃k : ℕ⦄ (t : StageType.{u} α k) (ht : t.IsLegal) (x : Fin k → M), R.Covers t x →
      ∀ ⦃n : ℕ⦄ (s : Fin n → Fin k),
        letI := R.toChartStructure
        (stageChartLanguage.chartFormula t ht s).Realize (x ∘ s) ∧
          ∀ (N : Type w') [(stageChartLanguage.{u} α).Structure N],
            N ⊨ (stageChartLanguage.{u} α).completeTheory M →
              ∀ b : Fin n → N, (stageChartLanguage.chartFormula t ht s).Realize b →
                SameFormulaType (L := stageChartLanguage.{u} α) (x ∘ s) b

/-- **Target: the chart formula isolates, in the form of `IsolatesTuple`.**  Under the hypotheses
of `ChartFormulaIsolationTarget`, the chart formula of `t` along `s` isolates `x ∘ s` over the
complete first-order theory of the chart structure of `R` (ComputableModelTheory's
`FirstOrder.Language.IsolatesTuple`).  Stated; open. -/
def ChartFormulaIsolatesTupleTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ (R : Realization.{u, v} α M)
    (A : ∀ m, Set (StageType.{u} α m)), Nonempty M → R.IsConsistent → R.IsCovering →
    (∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (D : StageType.{u} α m), R.eval s = some D → D ∈ A m) →
    R.ExactReceivingWithin A →
    ∀ ⦃k : ℕ⦄ (t : StageType.{u} α k) (ht : t.IsLegal) (x : Fin k → M), R.Covers t x →
      ∀ ⦃n : ℕ⦄ (s : Fin n → Fin k),
        letI := R.toChartStructure
        IsolatesTuple ((stageChartLanguage.{u} α).completeTheory M)
          (stageChartLanguage.chartFormula t ht s) (x ∘ s)

/-- **Target: the reference model is atomic.**  An exactly consistent covering realization on a
nonempty carrier, with legal types, whose actual types all lie in `A` and which has exact receiving
within `A`, is atomic over the complete first-order theory of its chart structure
(ComputableModelTheory's `FirstOrder.Language.IsAtomic`): every finite tuple, the empty tuple and
tuples with repeated entries included, is isolated, by the chart formula of a cover containing its
entries.  No countability of the carrier or of the language.  Stated; open. -/
def ChartAtomicTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ (R : Realization.{u, v} α M)
    (A : ∀ m, Set (StageType.{u} α m)), Nonempty M → R.IsConsistent → R.IsCovering →
    R.HasLegalTypes →
    (∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (D : StageType.{u} α m), R.eval s = some D → D ∈ A m) →
    R.ExactReceivingWithin A →
      letI := R.toChartStructure
      IsAtomic ((stageChartLanguage.{u} α).completeTheory M) M

/-- **Target: coverage is atomicity among the models of the complete theory.**  Let `R` be as in
`ChartAtomicTarget` and `T` the complete first-order theory of its chart structure.  For every
structure `N` of the stage chart language that is a model of `T`, on a carrier in any universe,
with no countability and not necessarily the chart structure of a realization, `N` is atomic over
`T` exactly when it is chart covered (`IsChartCovered`).  Stated; open. -/
def ChartCoverageAtomicityTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ (R : Realization.{u, v} α M)
    (A : ∀ m, Set (StageType.{u} α m)), Nonempty M → R.IsConsistent → R.IsCovering →
    R.HasLegalTypes →
    (∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (D : StageType.{u} α m), R.eval s = some D → D ∈ A m) →
    R.ExactReceivingWithin A →
      letI := R.toChartStructure
      ∀ (N : Type w') [(stageChartLanguage.{u} α).Structure N],
        N ⊨ (stageChartLanguage.{u} α).completeTheory M →
          (IsAtomic ((stageChartLanguage.{u} α).completeTheory M) N ↔ IsChartCovered α N)

end Reference

/-! ### The universal realization -/

section Universal

/-- **Target: atomicity and coverage in the strongly coded receiving class.**  For every
realization `R` at the block stage `λ_β` on a nonempty carrier, in the strongly coded receiving
class (`Realization.IsStronglyCodedReceiving`: exactly consistent, covering, with legal and strongly
coded types) and with exact receiving of every strongly coded legal donor, the chart structure of
`R` is atomic over its complete first-order theory, and among the models of that theory on
arbitrary carriers atomicity is chart coverage.  This is `ChartAtomicTarget` and
`ChartCoverageAtomicityTarget` with the strongly coded legal types as age.  Stated; open. -/
def StronglyCodedChartAtomicityTarget : Prop :=
  ∀ ⦃β : Ordinal.{u}⦄ ⦃M : Type v⦄ (R : Realization.{u, v} (blockStage β) M), Nonempty M →
    R.IsStronglyCodedReceiving →
    R.ExactReceivingWithin
      (fun m ↦ {D : StageType.{u} (blockStage β) m | D.IsStronglyCodedLegal}) →
      letI := R.toChartStructure
      IsAtomic ((stageChartLanguage.{u} (blockStage β)).completeTheory M) M ∧
        ∀ (N : Type w') [(stageChartLanguage.{u} (blockStage β)).Structure N],
          N ⊨ (stageChartLanguage.{u} (blockStage β)).completeTheory M →
            (IsAtomic ((stageChartLanguage.{u} (blockStage β)).completeTheory M) N ↔
              IsChartCovered (blockStage β) N)

/-- **Target: atomicity and coverage at a universal realization.**  For `β < ω₁` and every
countably infinite carrier `M`, some realization at `λ_β` on `M` in the strongly coded receiving
class, with exact receiving of every strongly coded legal donor (as given by
`exists_stronglyCodedUniversalRealization`), has a chart structure atomic over its complete
first-order theory, among whose models on arbitrary carriers atomicity is chart coverage.  No
canonical realization is chosen.  Stated; proved from `StronglyCodedChartAtomicityTarget`
(`universalChartAtomicityTarget_of_stronglyCodedChartAtomicityTarget`). -/
def UniversalChartAtomicityTarget : Prop :=
  ∀ ⦃β : Ordinal.{u}⦄ (M : Type v) [Countable M], β < ω₁ → Infinite M →
    ∃ R : Realization.{u, v} (blockStage β) M, R.IsStronglyCodedReceiving ∧
      R.ExactReceivingWithin
        (fun m ↦ {D : StageType.{u} (blockStage β) m | D.IsStronglyCodedLegal}) ∧
      (letI := R.toChartStructure
       IsAtomic ((stageChartLanguage.{u} (blockStage β)).completeTheory M) M ∧
        ∀ (N : Type w') [(stageChartLanguage.{u} (blockStage β)).Structure N],
          N ⊨ (stageChartLanguage.{u} (blockStage β)).completeTheory M →
            (IsAtomic ((stageChartLanguage.{u} (blockStage β)).completeTheory M) N ↔
              IsChartCovered (blockStage β) N))

/-- **Atomicity at a universal realization, from the strongly coded class**: the realization given
by `exists_stronglyCodedUniversalRealization` is in the strongly coded receiving class with exact
receiving of strongly coded legal donors, so `StronglyCodedChartAtomicityTarget` applies to it.
Conditional on `StronglyCodedChartAtomicityTarget`. -/
theorem universalChartAtomicityTarget_of_stronglyCodedChartAtomicityTarget
    (h : StronglyCodedChartAtomicityTarget.{u, v, w'}) : UniversalChartAtomicityTarget.{u, v, w'} :=
  fun _ _ _ hβ hM ↦
    let ⟨_, R, _, hR, hex, _⟩ := exists_stronglyCodedUniversalRealization hβ hM
    ⟨R, hR, hex, h R (@Infinite.nonempty _ hM) hR hex⟩

end Universal

end Realization

end VaughtConjecture
