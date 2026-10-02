/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Definability
import VaughtConjecture.Language.HullOperations

/-!
# First-order definability of the hull operations on finite charts

Roadmap, Layer 2 ("Hull operations: finite charts as finite substructures", item 2, for finite
charts; and "Hull closure inside definable closure", for finite charts); `HULL_ALGEBRA.md`, §§1, 2
and 4.

**The formulas.**  Let `ι` be a hull index of arity `m`, with stage type `q`, generators `i₀`,
`i₁`, and target `j`.  In the stage chart language, with free variables `x₀`, `x₁`, `x₂` (indexed
by `Fin 3`) and bound variables `z₀, …, z_{m-1}`:

* the **witness matrix** `ι.witnessMatrix` is the quantifier-free formula
  `P_q(z) ∧ ⋀_{i ≠ i'} z_i ≠ z_{i'} ∧ z_{i₀} = x₀ ∧ z_{i₁} = x₁`;
* the **chart witness formula** `ι.chartWitnessFormula`, the unique-coordinate formula
  `θ_ι(x₀, x₁, x₂)` of `HULL_ALGEBRA.md`, §1, is `∃ z (matrix ∧ z_j = x₂)`;
* `ι.existsChartWitnessFormula` is `∃ z matrix`; it does not mention `x₂` and says that a chart
  witness at `x₀` and `x₁` exists;
* the **graph formula** `ι.graphFormula` is `θ_ι ∨ (¬ ∃ z matrix ∧ x₂ = x₀)`, the graph of the hull
  operation of `ι` with its default value.

The inequalities state the injectivity of the witness explicitly.  In the structure of a
realization the relation of `q` holds only of injective tuples anyway, but with the inequalities
the formulas have the intended meaning in every structure of the stage chart language: a triple
satisfies the chart witness formula exactly when an injective tuple in the relation of `q` has the
triple at `i₀`, `i₁`, `j` (`HullIndex.realize_chartWitnessFormula`), and in the structure of a
realization exactly when there is a chart witness with the third point at the target
(`Realization.realize_chartWitnessFormula`).

**Complexity.**  The witness matrix is quantifier-free (`HullIndex.isQF_witnessMatrix`), and the
chart witness formula is existential, a block of `m` existential quantifiers in front of a
quantifier-free formula (`HullIndex.isExistential_chartWitnessFormula`); so it is preserved by
every embedding of structures of the stage chart language
(`HullIndex.realize_chartWitnessFormula_of_embedding`).  The graph formula is a Boolean
combination of two such existential formulas, so its quantifier rank is `m`, the arity of `ι`.
Mathlib defines quantifier rank only for its infinitary formulas, not for `BoundedFormula`; the
rank is therefore recorded here and not as a lemma.

**On charts.**  Let `P` be a stage type on `k` points, read through its chart (the structure of its
face realization).

* The chart witness formula holds at `(a, b, z)` exactly when a face of `P` of type `q` has the
  points `a`, `b`, `z` at `i₀`, `i₁`, `j` (`StageType.realize_chartWitnessFormula`).  Where such a
  face exists for `a` and `b`, the formula has exactly one solution `z`, the value of the hull
  operation, by the two-charts theorem
  (`StageType.realize_chartWitnessFormula_iff_hullOp_eq_of_exists`); where none exists, it has no
  solution (`StageType.not_realize_chartWitnessFormula_of_not_exists`), and the hull operation
  takes its default value `a`.  Together: `StageType.realize_chartWitnessFormula_iff`; and the
  formula has at most one solution over every pair (`StageType.eq_of_realize_chartWitnessFormula`).
* The graph formula defines the graph of the hull operation, the default value included
  (`StageType.realize_graphFormula`).  So the function symbol of `ι` in the hull language is a
  parameter-free definable function of the stage chart language (`StageType.definableFun_funMap_op`,
  in the sense of Mathlib's `Set.DefinableFun`): on charts, the hull language is a definitional
  expansion of the stage chart language.
* **Hull closure inside definable closure.**  Every point of the hull of two distinct points `a`
  and `b` is the target of a chart witness at them (`StageType.exists_chartWitness_of_mem_hull`),
  hence the unique solution over `a` and `b` of a chart witness formula
  (`StageType.exists_realize_chartWitnessFormula_iff_eq`).  So it is definable over `{a, b}` in
  the sense of Mathlib's `Set.Definable₁` (`StageType.definable₁_singleton_of_mem_hull_pair`), and
  every point of the hull of a finite set `s` is definable over `s`
  (`StageType.definable₁_singleton_of_mem_hull`): the inclusion `cl ⊆ dcl` of
  `HULL_ALGEBRA.md`, (2), for finite charts.
* **Invariance.**  Along a chart embedding (a face map along which the restriction is literal)
  chart witnesses at a pair exist exactly when they exist at the image pair
  (`StageType.exists_chartWitness_map_iff`), and both formulas are preserved and reflected, the
  default value included (`StageType.realize_chartWitnessFormula_map`,
  `StageType.realize_graphFormula_map`).

**Legality.**  The meaning of the formulas, the uniqueness of solutions, the graph, the definable
function, and the invariance hold for every stage type: the two-charts theorem does not use
legality.  Legality of the restriction to the hull of the generating pair (of the finite set `s`)
is assumed in the statements of hull closure inside definable closure.  In
`StageType.exists_chartWitness_of_mem_hull` and
`StageType.exists_realize_chartWitnessFormula_iff_eq` it is necessary: a chart witness at `a`
and `b` enumerates the hull of `{a, b}` (`StageType.map_univ_eq_hull_of_restrictFace`) and has
the legal type of its hull index, so the restriction to the hull is a reindexing of a legal
type.  In the two definability statements it cannot be dropped: on the stage type on four points
with no cells whose faces are the intervals of `Fin 4`, no relation holds of a nonempty tuple, so
the transposition of `1` and `2` is an automorphism of the chart in the stage chart language
fixing `0` and `3`, and the point `1` of the hull of `{0, 3}` is not definable over `{0, 3}`
(`VaughtConjecture.Language.HullDefinabilityExamples`).

**Not proved here.**  Definability on realizations other than the face realizations of charts: the
formulas and their meaning are stated for every structure and every realization, but the
uniqueness of solutions, the graph of `Realization.hullOp`, and the definability statements need
the two-charts theorem for exactly consistent covering realizations, which is not yet proved; so
roadmap, Layer 2, item 2 is proved here for finite charts only.  Nothing here concerns the
infinitary language.

## Placement

This file belongs to Layer 2 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open FirstOrder Language Structure Finset

namespace HullIndex

variable {α : Ordinal.{u}} (ι : HullIndex.{u} α)

/-- The **witness matrix** of a hull index `ι`: the quantifier-free formula, with free variables
`x₀, x₁, x₂` and a bound variable `z_i` for each coordinate `i` of `ι.type`, saying that `z` is an
injective tuple in the relation of `ι.type` with `x₀` and `x₁` at the generators. -/
noncomputable def witnessMatrix : (stageChartLanguage.{u} α).BoundedFormula (Fin 3) ι.arity :=
  (stageChartLanguage.symbol ι.type ι.isLegal).boundedFormula (fun i ↦ &i) ⊓
    BoundedFormula.iInf (fun ij : {ij : Fin ι.arity × Fin ι.arity // ij.1 ≠ ij.2} ↦
      ∼((&ij.1.1).bdEqual &ij.1.2)) ⊓
    (&ι.left).bdEqual (Term.var (Sum.inl 0)) ⊓ (&ι.right).bdEqual (Term.var (Sum.inl 1))

/-- The **chart witness formula** `θ_ι(x₀, x₁, x₂)` of a hull index `ι` (`HULL_ALGEBRA.md`, §1):
there is a chart witness of `ι` at `x₀` and `x₁` with `x₂` at the target. -/
noncomputable def chartWitnessFormula : (stageChartLanguage.{u} α).Formula (Fin 3) :=
  (ι.witnessMatrix ⊓ (&ι.target).bdEqual (Term.var (Sum.inl 2))).exs

/-- The formula saying that there is a chart witness of `ι` at `x₀` and `x₁`; it does not mention
`x₂`. -/
noncomputable def existsChartWitnessFormula : (stageChartLanguage.{u} α).Formula (Fin 3) :=
  ι.witnessMatrix.exs

/-- The **graph formula** of a hull index `ι` (`HULL_ALGEBRA.md`, §1): either `x₂` is the target
of a chart witness at `x₀` and `x₁`, or there is no chart witness there and `x₂` is the default
value `x₀`. -/
noncomputable def graphFormula : (stageChartLanguage.{u} α).Formula (Fin 3) :=
  ι.chartWitnessFormula ⊔
    (∼ι.existsChartWitnessFormula ⊓ (Term.var 2).equal (Term.var 0))

variable {M : Type v} [(stageChartLanguage.{u} α).Structure M]

/-- The witness matrix holds of a tuple exactly when the tuple is injective, lies in the relation
of `ι.type`, and has the first two free points at the generators. -/
theorem realize_witnessMatrix (v : Fin 3 → M) (xs : Fin ι.arity → M) :
    ι.witnessMatrix.Realize v xs ↔
      RelMap (stageChartLanguage.symbol ι.type ι.isLegal) xs ∧ Function.Injective xs ∧
        xs ι.left = v 0 ∧ xs ι.right = v 1 := by
  have hinj : (∀ ij : {ij : Fin ι.arity × Fin ι.arity // ij.1 ≠ ij.2}, xs ij.1.1 ≠ xs ij.1.2) ↔
      Function.Injective xs :=
    ⟨fun h i j hij ↦ by_contra fun hne ↦ h ⟨(i, j), hne⟩ hij, fun h ij hij ↦ ij.2 (h hij)⟩
  simp only [witnessMatrix, BoundedFormula.realize_inf, BoundedFormula.realize_rel,
    BoundedFormula.realize_iInf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    Function.comp_apply, Term.realize_var, Sum.elim_inr, Sum.elim_inl, hinj, and_assoc]

/-- **Meaning of the chart witness formula in every structure** of the stage chart language: it
holds at `(a, b, z)` exactly when an injective tuple in the relation of `ι.type` has `a`, `b`, `z`
at the generators and the target. -/
theorem realize_chartWitnessFormula (a b z : M) :
    ι.chartWitnessFormula.Realize ![a, b, z] ↔
      ∃ g : Fin ι.arity ↪ M, RelMap (stageChartLanguage.symbol ι.type ι.isLegal) ⇑g ∧
        g ι.left = a ∧ g ι.right = b ∧ g ι.target = z := by
  simp only [chartWitnessFormula, BoundedFormula.realize_exs, BoundedFormula.realize_inf,
    realize_witnessMatrix, BoundedFormula.realize_bdEqual, Term.realize_var, Sum.elim_inl]
  constructor
  · rintro ⟨xs, ⟨hR, hinj, hl, hr⟩, ht⟩
    exact ⟨⟨xs, hinj⟩, hR, hl, hr, ht⟩
  · rintro ⟨g, hR, hl, hr, ht⟩
    exact ⟨g, ⟨hR, g.injective, hl, hr⟩, ht⟩

/-- The formula `∃ z matrix` holds at `(a, b, _)` exactly when an injective tuple in the relation
of `ι.type` has `a` and `b` at the generators. -/
theorem realize_existsChartWitnessFormula (a b z : M) :
    ι.existsChartWitnessFormula.Realize ![a, b, z] ↔
      ∃ g : Fin ι.arity ↪ M, RelMap (stageChartLanguage.symbol ι.type ι.isLegal) ⇑g ∧
        g ι.left = a ∧ g ι.right = b := by
  simp only [existsChartWitnessFormula, BoundedFormula.realize_exs, realize_witnessMatrix]
  constructor
  · rintro ⟨xs, hR, hinj, hl, hr⟩
    exact ⟨⟨xs, hinj⟩, hR, hl, hr⟩
  · rintro ⟨g, hR, hl, hr⟩
    exact ⟨g, hR, g.injective, hl, hr⟩

/-- The graph formula is the disjunction of the chart witness formula and the default case. -/
theorem realize_graphFormula (a b z : M) :
    ι.graphFormula.Realize ![a, b, z] ↔
      ι.chartWitnessFormula.Realize ![a, b, z] ∨
        ¬ ι.existsChartWitnessFormula.Realize ![a, b, z] ∧ z = a := by
  simp [graphFormula]

/-- A finite conjunction of quantifier-free formulas is quantifier-free. -/
private theorem isQF_foldr_inf {L : Language} {β γ : Type*} {n : ℕ}
    (f : β → L.BoundedFormula γ n) (h : ∀ b, (f b).IsQF) :
    ∀ l : List β, ((l.map f).foldr (· ⊓ ·) ⊤).IsQF
  | [] => BoundedFormula.IsQF.top
  | b :: l => (h b).inf (isQF_foldr_inf f h l)

/-- Existential quantification of all bound variables of an existential formula gives an
existential formula. -/
private theorem isExistential_exs {L : Language} {γ : Type*} :
    ∀ {n : ℕ} {φ : L.BoundedFormula γ n}, φ.IsExistential → φ.exs.IsExistential
  | 0, _, h => h
  | _ + 1, φ, h => isExistential_exs (φ := φ.ex) h.ex

/-- The witness matrix is quantifier-free. -/
theorem isQF_witnessMatrix : ι.witnessMatrix.IsQF := by
  refine (((BoundedFormula.IsAtomic.rel _ _).isQF.inf ?_).inf
    (BoundedFormula.IsAtomic.equal _ _).isQF).inf (BoundedFormula.IsAtomic.equal _ _).isQF
  exact isQF_foldr_inf _ (fun _ ↦ (BoundedFormula.IsAtomic.equal _ _).isQF.not) _

/-- The chart witness formula is **existential**: a block of `ι.arity` existential quantifiers in
front of a quantifier-free formula. -/
theorem isExistential_chartWitnessFormula : ι.chartWitnessFormula.IsExistential :=
  isExistential_exs
    (ι.isQF_witnessMatrix.inf (BoundedFormula.IsAtomic.equal _ _).isQF).isExistential

/-- The chart witness formula, being existential, is preserved by every embedding of structures of
the stage chart language. -/
theorem realize_chartWitnessFormula_of_embedding {N : Type w}
    [(stageChartLanguage.{u} α).Structure N] (f : M ↪[stageChartLanguage.{u} α] N)
    {v : Fin 3 → M} (h : ι.chartWitnessFormula.Realize v) :
    ι.chartWitnessFormula.Realize (f ∘ v) := by
  have := ι.isExistential_chartWitnessFormula.realize_embedding f h
  rwa [Subsingleton.elim (f ∘ default) default] at this

end HullIndex

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} (R : Realization.{u, v} α M) (ι : HullIndex.{u} α)

/-- **Meaning of the chart witness formula in a realization**: it holds at `(a, b, z)` exactly when
there is a chart witness of `ι` at `a` and `b` with `z` at the target. -/
theorem realize_chartWitnessFormula (a b z : M) :
    letI := R.toChartStructure
    ι.chartWitnessFormula.Realize ![a, b, z] ↔
      ∃ g : Fin ι.arity ↪ M, R.eval g = some ι.type ∧ g ι.left = a ∧ g ι.right = b ∧
        g ι.target = z := by
  let := R.toChartStructure
  rw [HullIndex.realize_chartWitnessFormula]
  simp only [relMap_toChartStructure]

end Realization

namespace StageType

variable {α : Ordinal.{u}} {k k' : ℕ} (P : StageType.{u} α k) (ι : HullIndex.{u} α)

/-- **The chart witness formula on a chart**: it holds at `(a, b, z)` exactly when a face of type
`ι.type` has `a`, `b`, `z` at the generators and the target.  No legality is needed. -/
theorem realize_chartWitnessFormula (a b z : Fin k) :
    ι.chartWitnessFormula.Realize ![P.toChart a, P.toChart b, P.toChart z] ↔
      ∃ g : Fin ι.arity ↪ Fin k, restrictFace g P = some ι.type ∧ g ι.left = a ∧
        g ι.right = b ∧ g ι.target = z := by
  rw [HullIndex.realize_chartWitnessFormula]
  exact ⟨fun ⟨g, ⟨_, h⟩, hl, hr, ht⟩ ↦ ⟨g, h, hl, hr, ht⟩,
    fun ⟨g, h, hl, hr, ht⟩ ↦ ⟨g, ⟨g.injective, h⟩, hl, hr, ht⟩⟩

/-- On a chart, the formula `∃ z matrix` holds at `(a, b, _)` exactly when a face of type `ι.type`
has `a` and `b` at the generators. -/
theorem realize_existsChartWitnessFormula (a b z : Fin k) :
    ι.existsChartWitnessFormula.Realize ![P.toChart a, P.toChart b, P.toChart z] ↔
      ∃ g : Fin ι.arity ↪ Fin k, restrictFace g P = some ι.type ∧ g ι.left = a ∧
        g ι.right = b := by
  rw [HullIndex.realize_existsChartWitnessFormula]
  exact ⟨fun ⟨g, ⟨_, h⟩, hl, hr⟩ ↦ ⟨g, h, hl, hr⟩,
    fun ⟨g, h, hl, hr⟩ ↦ ⟨g, ⟨g.injective, h⟩, hl, hr⟩⟩

variable {P ι}

/-- **Unique solution where a chart witness exists** (`HULL_ALGEBRA.md`, §1): if a face of type
`ι.type` has `a` and `b` at the generators, the chart witness formula holds at `(a, b, z)` exactly
when `z` is the value of the hull operation at `a` and `b`.  By the two-charts theorem
(`eq_of_restrictFace_eq_some`); no legality is needed. -/
theorem realize_chartWitnessFormula_iff_hullOp_eq_of_exists {a b : Fin k} (z : Fin k)
    (h : ∃ g : Fin ι.arity ↪ Fin k, restrictFace g P = some ι.type ∧ g ι.left = a ∧
      g ι.right = b) :
    ι.chartWitnessFormula.Realize ![P.toChart a, P.toChart b, P.toChart z] ↔
      P.faceRealization.hullOp ι a b = z := by
  obtain ⟨g, hg, rfl, rfl⟩ := h
  rw [realize_chartWitnessFormula, hullOp_eq_of_restrictFace hg]
  constructor
  · rintro ⟨g', hg', hl, hr, rfl⟩
    rw [eq_of_restrictFace_eq_some ι.hull_eq_univ hg hg' hl.symm hr.symm]
  · rintro rfl
    exact ⟨g, hg, rfl, rfl, rfl⟩

/-- **No solution where no chart witness exists**: then the chart witness formula fails at every
`(a, b, z)`, while the hull operation takes its default value `a`
(`Realization.hullOp_of_not_exists`). -/
theorem not_realize_chartWitnessFormula_of_not_exists {a b : Fin k} (z : Fin k)
    (h : ¬ ∃ g : Fin ι.arity ↪ Fin k, restrictFace g P = some ι.type ∧ g ι.left = a ∧
      g ι.right = b) :
    ¬ ι.chartWitnessFormula.Realize ![P.toChart a, P.toChart b, P.toChart z] := by
  rw [realize_chartWitnessFormula]
  exact fun ⟨g, hg, hl, hr, _⟩ ↦ h ⟨g, hg, hl, hr⟩

/-- **The chart witness formula and the hull operation**: on a chart, the chart witness formula
holds at `(a, b, z)` exactly when a chart witness at `a` and `b` exists and `z` is the value of
the hull operation there. -/
theorem realize_chartWitnessFormula_iff (a b z : Fin k) :
    ι.chartWitnessFormula.Realize ![P.toChart a, P.toChart b, P.toChart z] ↔
      (∃ g : Fin ι.arity ↪ Fin k, restrictFace g P = some ι.type ∧ g ι.left = a ∧
        g ι.right = b) ∧ P.faceRealization.hullOp ι a b = z := by
  by_cases h : ∃ g : Fin ι.arity ↪ Fin k, restrictFace g P = some ι.type ∧ g ι.left = a ∧
      g ι.right = b
  · rw [realize_chartWitnessFormula_iff_hullOp_eq_of_exists z h]
    exact ⟨fun h' ↦ ⟨h, h'⟩, And.right⟩
  · exact iff_of_false (not_realize_chartWitnessFormula_of_not_exists z h) fun h' ↦ h h'.1

/-- **At most one solution for every pair** (`HULL_ALGEBRA.md`, §1): on a chart, the chart witness
formula has at most one solution over any two points. -/
theorem eq_of_realize_chartWitnessFormula {a b z z' : Fin k}
    (hz : ι.chartWitnessFormula.Realize ![P.toChart a, P.toChart b, P.toChart z])
    (hz' : ι.chartWitnessFormula.Realize ![P.toChart a, P.toChart b, P.toChart z']) :
    z = z' := by
  rw [realize_chartWitnessFormula_iff] at hz hz'
  exact hz.2.symm.trans hz'.2

variable (P ι)

/-- **The graph of a hull operation is first-order definable** (roadmap, Layer 2, item 2, for
finite charts; `HULL_ALGEBRA.md`, §1): on a chart, the graph formula holds at `(a, b, z)` exactly
when `z` is the value of the hull operation at `a` and `b`, the default value included.  No
legality is needed. -/
theorem realize_graphFormula (a b z : Fin k) :
    ι.graphFormula.Realize ![P.toChart a, P.toChart b, P.toChart z] ↔
      P.faceRealization.hullOp ι a b = z := by
  rw [HullIndex.realize_graphFormula, realize_existsChartWitnessFormula]
  by_cases h : ∃ g : Fin ι.arity ↪ Fin k, restrictFace g P = some ι.type ∧ g ι.left = a ∧
      g ι.right = b
  · rw [realize_chartWitnessFormula_iff_hullOp_eq_of_exists z h]
    simp [h]
  · rw [Realization.hullOp_of_not_exists h]
    simp only [not_realize_chartWitnessFormula_of_not_exists z h, h, not_false_eq_true,
      true_and, false_or]
    exact ⟨fun h ↦ (P.toChart.injective h).symm, fun h ↦ congrArg P.toChart h.symm⟩

/-- **The hull operations are parameter-free definable functions** of the stage chart language on
a chart, in the sense of Mathlib's `Set.DefinableFun`: their graphs are defined by the graph
formulas (`realize_graphFormula`).  So on charts the hull language is a definitional expansion of
the stage chart language. -/
theorem definableFun_funMap_op :
    (∅ : Set P.Chart).DefinableFun (stageChartLanguage.{u} α)
      (funMap (L := hullLanguage.{u} α) (hullLanguage.op ι)) := by
  rw [Set.empty_definableFun_iff]
  refine ⟨ι.graphFormula.relabel ![some 0, some 1, none], ?_⟩
  ext v
  have hv : v ∘ ![some 0, some 1, none] =
      ![P.toChart (P.toChart.symm (v (some 0))), P.toChart (P.toChart.symm (v (some 1))),
        P.toChart (P.toChart.symm (v none))] := by
    funext i
    match i with
    | 0 | 1 | 2 => rfl
  change funMap (hullLanguage.op ι) (v ∘ some) = v none ↔
    (ι.graphFormula.relabel ![some 0, some 1, none]).Realize v
  rw [Formula.realize_relabel, hv, realize_graphFormula]
  rfl

variable {P ι}

/-- **Every point of a two-point hull is the target of a chart witness** (`HULL_ALGEBRA.md`, §3):
for distinct points `a`, `b` of a chart, every point of the hull of `{a, b}` is the point at the
target of a face, of the type of a hull index, with `a` and `b` at the generators.

Legality along the hull of `{a, b}` (`hleg`) is necessary: the face enumerates that hull
(`map_univ_eq_hull_of_restrictFace`) and has the legal type of the hull index, so the restriction
to the hull is a reindexing of a legal type. -/
theorem exists_chartWitness_of_mem_hull {a b z : Fin k} (hab : a ≠ b)
    (hleg : ∀ {m : ℕ} (g : Fin m ↪ Fin k) (hg : univ.map g ∈ P.toCellScheme.faces),
      univ.map g = Geometry.hull univ P.toCellScheme.faces {a, b} → (P.comap g hg).IsLegal)
    (hz : z ∈ Geometry.hull univ P.toCellScheme.faces {a, b}) :
    ∃ (ι : HullIndex.{u} α) (g : Fin ι.arity ↪ Fin k), restrictFace g P = some ι.type ∧
      g ι.left = a ∧ g ι.right = b ∧ g ι.target = z := by
  obtain ⟨ι, hι⟩ := exists_hullOp_eq_of_mem_hull hab hleg
    (Geometry.subset_hull (subset_univ _) (mem_insert_of_mem (mem_singleton_self b)))
  have hex : ∃ g : Fin ι.arity ↪ Fin k,
      P.faceRealization.eval g = some ι.type ∧ g ι.left = a ∧ g ι.right = b := by
    by_contra h
    exact hab ((Realization.hullOp_of_not_exists h).symm.trans hι)
  obtain ⟨g, hg, hl, hr⟩ := hex
  have hz' : z ∈ univ.map g := by
    rw [map_univ_eq_hull_of_restrictFace hg ι.hull_eq_univ, hl, hr]
    exact hz
  obtain ⟨j, -, hj⟩ := mem_map.mp hz'
  exact ⟨{ ι with target := j }, g, hg, hl, hr, hj⟩

/-- **The unique-coordinate formula of a hull point** (roadmap, Layer 2, "Hull closure inside
definable closure"; `HULL_ALGEBRA.md`, §§1 and 4): every point `z` of the hull of two distinct
points `a`, `b` of a chart is the unique solution over `a` and `b` of the chart witness formula of
a hull index.  Legality along the hull of `{a, b}` is necessary, as for
`exists_chartWitness_of_mem_hull`. -/
theorem exists_realize_chartWitnessFormula_iff_eq {a b z : Fin k} (hab : a ≠ b)
    (hleg : ∀ {m : ℕ} (g : Fin m ↪ Fin k) (hg : univ.map g ∈ P.toCellScheme.faces),
      univ.map g = Geometry.hull univ P.toCellScheme.faces {a, b} → (P.comap g hg).IsLegal)
    (hz : z ∈ Geometry.hull univ P.toCellScheme.faces {a, b}) :
    ∃ ι : HullIndex.{u} α, ∀ w : Fin k,
      ι.chartWitnessFormula.Realize ![P.toChart a, P.toChart b, P.toChart w] ↔ w = z := by
  obtain ⟨ι, g, hg, rfl, rfl, rfl⟩ := exists_chartWitness_of_mem_hull hab hleg hz
  refine ⟨ι, fun w ↦ ?_⟩
  rw [realize_chartWitnessFormula_iff_hullOp_eq_of_exists w ⟨g, hg, rfl, rfl⟩,
    hullOp_eq_of_restrictFace hg, eq_comm]

/-- **Hull closure inside definable closure, for two points** (`HULL_ALGEBRA.md`, (2), for finite
charts): every point of the hull of `{a, b}` in a chart is definable over `{a, b}` in the stage
chart language.  For `a = b` the hull is `{a}`; otherwise the point is defined by its
unique-coordinate formula (`exists_realize_chartWitnessFormula_iff_eq`).  Legality along the hull
of `{a, b}` is assumed; it cannot be dropped: on a stage type on four points with no cells, a point
of the hull of the two extreme points is moved by an automorphism fixing them
(`VaughtConjecture.Language.HullDefinabilityExamples`). -/
theorem definable₁_singleton_of_mem_hull_pair {a b z : Fin k}
    (hleg : ∀ {m : ℕ} (g : Fin m ↪ Fin k) (hg : univ.map g ∈ P.toCellScheme.faces),
      univ.map g = Geometry.hull univ P.toCellScheme.faces {a, b} → (P.comap g hg).IsLegal)
    (hz : z ∈ Geometry.hull univ P.toCellScheme.faces {a, b}) :
    ({P.toChart a, P.toChart b} : Set P.Chart).Definable₁ (stageChartLanguage.{u} α)
      {P.toChart z} := by
  rcases eq_or_ne a b with rfl | hab
  · rw [insert_eq_of_mem (mem_singleton_self a),
      Geometry.hull_eq_self (P.isPlan.singleton_mem (mem_univ a)) (subset_univ _),
      mem_singleton] at hz
    subst hz
    exact Set.Definable.singleton_of_mem _ (Set.mem_insert _ _)
  obtain ⟨ι, hι⟩ := exists_realize_chartWitnessFormula_iff_eq hab hleg hz
  set A : Set P.Chart := {P.toChart a, P.toChart b}
  rw [Set.Definable₁, Set.definable_iff_exists_formula_sum]
  refine ⟨ι.chartWitnessFormula.relabel
    ![Sum.inl ⟨P.toChart a, Set.mem_insert _ _⟩, Sum.inl ⟨P.toChart b, by simp [A]⟩,
      Sum.inr 0], ?_⟩
  ext v
  have hv : Sum.elim ((↑) : A → P.Chart) v ∘
      ![Sum.inl ⟨P.toChart a, Set.mem_insert _ _⟩, Sum.inl ⟨P.toChart b, by simp [A]⟩,
        Sum.inr 0] = ![P.toChart a, P.toChart b, P.toChart (P.toChart.symm (v 0))] := by
    funext i
    match i with
    | 0 | 1 | 2 => rfl
  change v 0 = P.toChart z ↔ _
  rw [Set.mem_ofPred_eq, Formula.realize_relabel, hv, hι]
  exact ⟨fun h ↦ congrArg P.toChart.symm h, fun h ↦ (P.toChart.symm_apply_eq.mp h)⟩

/-- **Hull closure inside definable closure** (roadmap, Layer 2, "Hull closure inside definable
closure", for finite charts; `HULL_ALGEBRA.md`, (2)): every point of the hull of a finite set `s`
of points of a chart is definable over `s` in the stage chart language.  The hull of `s` is the
hull of at most two of its points (`Geometry.IsPlan.exists_subset_card_le_two_hull_eq`), and
`definable₁_singleton_of_mem_hull_pair` applies to them.  Legality along the hull of `s` is
assumed; it cannot be dropped, as for `definable₁_singleton_of_mem_hull_pair`. -/
theorem definable₁_singleton_of_mem_hull {s : Finset (Fin k)} {z : Fin k}
    (hleg : ∀ {m : ℕ} (g : Fin m ↪ Fin k) (hg : univ.map g ∈ P.toCellScheme.faces),
      univ.map g = Geometry.hull univ P.toCellScheme.faces s → (P.comap g hg).IsLegal)
    (hz : z ∈ Geometry.hull univ P.toCellScheme.faces s) :
    (P.toChart '' s : Set P.Chart).Definable₁ (stageChartLanguage.{u} α) {P.toChart z} := by
  obtain ⟨T, hTs, hT2, hTH⟩ := P.isPlan.exists_subset_card_le_two_hull_eq (subset_univ s)
  -- the hull of `s` is the hull of two of its points, possibly equal
  obtain ⟨a, b, ha, hb, rfl⟩ : ∃ a b, a ∈ s ∧ b ∈ s ∧ T = {a, b} := by
    rcases T.eq_empty_or_nonempty with rfl | ⟨a, haT⟩
    · rw [← hTH, Geometry.hull_eq_self P.isPlan.empty_mem (empty_subset _)] at hz
      exact absurd hz (notMem_empty z)
    · rcases Nat.lt_or_ge 1 #T with h1 | h1
      · obtain ⟨a, b, -, rfl⟩ := card_eq_two.mp (le_antisymm hT2 h1)
        exact ⟨a, b, hTs (mem_insert_self a _), hTs (by simp), rfl⟩
      · refine ⟨a, a, hTs haT, hTs haT, ?_⟩
        rw [insert_eq_of_mem (mem_singleton_self a)]
        exact eq_singleton_iff_unique_mem.mpr ⟨haT, fun x hx ↦ card_le_one.mp h1 x hx a haT⟩
  rw [← hTH] at hleg hz
  refine (definable₁_singleton_of_mem_hull_pair hleg hz).mono ?_
  exact Set.insert_subset_iff.mpr ⟨⟨a, mem_coe.mpr ha, rfl⟩,
    Set.singleton_subset_iff.mpr ⟨b, mem_coe.mpr hb, rfl⟩⟩

variable {Q : StageType.{u} α k'} {e : Fin k ↪ Fin k'}

/-- **Chart witnesses along a chart embedding**: along a face map `e` along which the restriction
of `Q` is `P`, there is a chart witness of `ι` at `e a` and `e b` in `Q` exactly when there is one
at `a` and `b` in `P`.  A witness in `P` is carried to `Q`; a witness in `Q` has as points the hull
of `{e a, e b}`, which lies in the closed range of `e`, so it reflects to `P`. -/
theorem exists_chartWitness_map_iff (he : restrictFace e Q = some P) (a b : Fin k) :
    (∃ g : Fin ι.arity ↪ Fin k', restrictFace g Q = some ι.type ∧ g ι.left = e a ∧
      g ι.right = e b) ↔
      ∃ g : Fin ι.arity ↪ Fin k, restrictFace g P = some ι.type ∧ g ι.left = a ∧
        g ι.right = b := by
  constructor
  · rintro ⟨g, hg, hl, hr⟩
    have hge : univ.map e ∈ Q.toCellScheme.faces := ((restrictFace_eq_some_iff Q e).mp he).1
    have hsub : univ.map g ⊆ univ.map e := by
      rw [map_univ_eq_hull_of_restrictFace hg ι.hull_eq_univ, hl, hr]
      exact Geometry.hull_subset hge (by simp [insert_subset_iff])
    obtain ⟨w, rfl⟩ := Function.Embedding.exists_trans_eq (e := e) fun j ↦ by
      simpa using hsub (mem_map_of_mem g (mem_univ j))
    refine ⟨w, ?_, e.injective hl, e.injective hr⟩
    rw [restrictFace_trans Q e w he]
    exact hg
  · rintro ⟨w, hw, rfl, rfl⟩
    refine ⟨w.trans e, ?_, rfl, rfl⟩
    rw [← restrictFace_trans Q e w he]
    exact hw

/-- **The chart witness formula is invariant under chart embeddings** (roadmap, Layer 2, item 3, for
chart embeddings): it holds at the image of a triple exactly when it holds at the triple. -/
theorem realize_chartWitnessFormula_map (he : restrictFace e Q = some P) (a b z : Fin k) :
    ι.chartWitnessFormula.Realize ![Q.toChart (e a), Q.toChart (e b), Q.toChart (e z)] ↔
      ι.chartWitnessFormula.Realize ![P.toChart a, P.toChart b, P.toChart z] := by
  rw [realize_chartWitnessFormula_iff, realize_chartWitnessFormula_iff,
    exists_chartWitness_map_iff he, hullOp_map_of_restrictFace he, e.injective.eq_iff]

/-- **The graph formula is invariant under chart embeddings**, the default value included: it holds
at the image of a triple exactly when it holds at the triple (`hullOp_map_of_restrictFace`). -/
theorem realize_graphFormula_map (he : restrictFace e Q = some P) (a b z : Fin k) :
    ι.graphFormula.Realize ![Q.toChart (e a), Q.toChart (e b), Q.toChart (e z)] ↔
      ι.graphFormula.Realize ![P.toChart a, P.toChart b, P.toChart z] := by
  rw [realize_graphFormula, realize_graphFormula, hullOp_map_of_restrictFace he,
    e.injective.eq_iff]

end StageType

end VaughtConjecture
