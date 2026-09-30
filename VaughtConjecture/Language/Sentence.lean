/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.CountableIndex
import InfinitaryLogic.Lomega1omega.FiniteQuantification
import VaughtConjecture.Language.Structure

/-!
# The four-family sentence

Roadmap, Layer 2 (the literal infinitary sentence: the structural clauses, namely injective
tuples, unique labels, exact face coherence, covering, and nonemptiness, and the four extension
families; bottom-pattern parameters encoded through their finite observational quotient, with no
quantification over an uncountable collection of labellings); semantic contract, items 1 and 5.

All formulas are formulas of the base language in `L_{ω₁,ω}` (`BoundedFormulaω`), with no free
variables and `n` bound variables `x₀, …, x_{n-1}`; countable conjunctions and disjunctions over a
countable index type are the library's `ciInf` and `ciSup`.

* `atom p f` is the atomic formula `P_p(x_{f 0}, …, x_{f (m-1)})`, and `atomOfSet U f` is the
  disjunction `P_U` of the `P_p` over the members `p` of a set `U` of relation symbols
  [Kni26, Definition 3.3.2]; `BoundedFormulaω.distinct n` says that the bound variables are
  pairwise distinct.  It, its realization, and the realization `BoundedFormulaω.realize_alls` of
  universal closures at the empty tuple are stated for an arbitrary language.

**The structural clauses** [Kni26, Definition 3.3.3, clauses 1–3], and nonemptiness of the
carrier, a condition of the models of [Kni26, Definition 3.2.1]:

* `nonemptyClause`: `∃ x, ⊤`;
* `arityClause` (clause 1, first part): `∀ x̄, x_i = x_j → ¬ P_p(x̄)` for `i < j`;
* `uniquenessClause` (clause 1, second part): `∀ x̄, ¬ (P_p(x̄) ∧ P_q(x̄))` for `p ≠ q`;
* `consistencyClause` (clause 2): for `f : Fin m ↪ Fin n`, `∀ x̄, P_p(x̄) → P_q(x̄ ∘ f)` when the
  face map sends `p` to `q`, and `∀ x̄, P_p(x̄) → ⋀_q ¬ P_q(x̄ ∘ f)` when it is undefined at `p`
  (`faceFormula`);
* `coveringClause` (clause 3): `∀ x̄, ⋀_{i ≠ j} x_i ≠ x_j → ⋁_k ⋁_p ∃ ȳ, P_p(x̄, ȳ)`, with `p` on
  `n + k` points.

Their conjunction is `structuralSentence`; it holds in `M` exactly when `M` is a type assignment
with a nonempty carrier, exact face coherence, and covering (`IsStructural`,
`realize_structuralSentence_iff`).

**The extension clauses** [Kni26, Definition 3.3.3, clause 4] all have one shape
(`extensionClause`): for a countable parameter type `P n p` and families `U n p a` of stage types
on `n + 1` points, `∀ x̄, P_p(x̄) → ⋀_{a : P n p} ∃ y, P_{U n p a}(x̄, y)`.  Its semantic form is
that some point extends every tuple of type `p` to a tuple with a type in each family
(`RealizesOver`).  The four families are those of `Realization.IsModel`, with exactly its
quantifiers:

* `saturationClause` (generalized saturation): the schemes `S` on `n + 1` points whose instance has
  a member among the cofaces of `p` (`SaturationIndex`);
* `bottomPatternClause` (the bottom pattern): the same, for pairs of a scheme `S` and a *pattern*
  `π : Fin S.card → Bool`, with family that of the labelling `patternLabel π`, bottom exactly where
  `π` holds (`BottomPatternIndex`).  The family of a labelling `ρ` depends on `ρ` only through
  which of its values are bottom (`StageType.bottomPatternFamily_congr`), so this finite
  observational quotient replaces the uncountably many labellings of the source; the realization
  lemma `realize_bottomPatternClause` is stated for every labelling;
* `uniformityClause` (uniformity): the ordinals `γ < ω` that are zero or limits (only `γ = 0`);
* `dominanceClause` (high-arity dominance): the ordinals `γ < ω`.

The **four-family sentence** `fourFamilySentence` is the conjunction of the structural sentence and
the four extension clauses; it holds in `M` exactly when `M` satisfies the corresponding semantic
conditions (`IsFourFamilyModel`, `realize_fourFamilySentence_iff_isFourFamilyModel`).  Its
correspondence with models of stage `ω` is `VaughtConjecture.Language.Satisfaction`.

## Placement

`StageType.bottomPatternFamily_congr` belongs in `VaughtConjecture.Realization.Families`, beside
`StageType.mem_bottomPatternFamily`; it is on the placement list of
`VaughtConjecture.Language.Basic`.  The formula helpers `BoundedFormulaω.distinct`,
`BoundedFormulaω.realize_distinct`, and `BoundedFormulaω.realize_alls` hold for an arbitrary
language and are candidates for upstreaming.

## References

The language and the formulas `P_U` are [Kni26, Definitions 3.3.1 and 3.3.2], and the four-family
sentence is the sentence `T` of [Kni26, Definition 3.3.3] together with nonemptiness, for
R. W. Knight, *A counterexample to Vaught's Conjecture using generalised Stone spaces* (draft,
20 February 2026).
-/

universe u v w

/-! ### Formula helpers for an arbitrary language -/

namespace FirstOrder.Language.BoundedFormulaω

variable {L : Language} {α M : Type*} [L.Structure M] {n : ℕ}

/-- The bound variables are pairwise distinct: `⋀_{i ≠ j} x_i ≠ x_j`. -/
noncomputable def distinct (n : ℕ) : L.BoundedFormulaω α n :=
  ciInf fun ij : {ij : Fin n × Fin n // ij.1 ≠ ij.2} ↦
    (equal (Term.var (Sum.inr ij.1.1)) (Term.var (Sum.inr ij.1.2))).not

/-- The distinctness formula holds exactly of the injective tuples. -/
@[simp] theorem realize_distinct {v : α → M} {xs : Fin n → M} :
    (distinct n : L.BoundedFormulaω α n).Realize v xs ↔ Function.Injective xs := by
  simp only [distinct, realize_ciInf, realize_not, realize_equal, Term.realize_var, Sum.elim_inr,
    Subtype.forall, Prod.forall]
  exact ⟨fun h i j hij ↦ by_contra fun hne ↦ h i j hne hij, fun h i j hne hij ↦ hne (h hij)⟩

/-- Realization of the universal closure of a formula, read at the empty tuple.  This differs from
`BoundedFormulaInf.realize_alls`, which reads the closure at `default` as a formula; it is a
candidate for upstreaming. -/
@[simp]
theorem realize_alls {v : α → M} (φ : L.BoundedFormulaω α n) :
    Realize φ.alls v Fin.elim0 ↔ ∀ ys : Fin n → M, φ.Realize v ys :=
  BoundedFormulaInf.realize_alls

end FirstOrder.Language.BoundedFormulaω

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal Label

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ}

/-- The bottom-pattern family of a labelling depends only on which of its values are bottom. -/
theorem bottomPatternFamily_congr {S : Scheme.{u} (n + 1)} {ρ ρ' : Fin S.card → Label.{u}}
    (h : ∀ j, ρ j = ⊥ ↔ ρ' j = ⊥) :
    (bottomPatternFamily S ρ : Set (StageType.{u} α (n + 1))) = bottomPatternFamily S ρ' := by
  ext q
  simp only [mem_bottomPatternFamily, h]

end StageType

namespace baseLanguage

open BoundedFormulaω StageType

variable {M : Type v} {n m : ℕ}

/-! ### Formulas -/

section Formulas

/-- The atomic formula `P_p(x_{f 0}, …, x_{f (m-1)})` on the bound variables. -/
def atom (p : baseLanguage.{u}.Relations m) (f : Fin m → Fin n) :
    baseLanguage.{u}.BoundedFormulaω Empty n :=
  rel p fun i ↦ Term.var (Sum.inr (f i))

/-- The formula `P_U(x_{f 0}, …, x_{f (m-1)})` of [Kni26, Definition 3.3.2]: the disjunction of
the atomic formulas `P_p` over the members `p` of `U`. -/
noncomputable def atomOfSet (U : Set (baseLanguage.{u}.Relations m)) (f : Fin m → Fin n) :
    baseLanguage.{u}.BoundedFormulaω Empty n :=
  ciSup fun p : U ↦ atom p.1 f

variable [baseLanguage.{u}.Structure M] {v : Empty → M} {xs : Fin n → M}

/-- An atomic formula holds of the tuple read through `f`. -/
@[simp] theorem realize_atom (p : baseLanguage.{u}.Relations m) (f : Fin m → Fin n) :
    (atom p f).Realize v xs ↔ RelMap p (xs ∘ f) :=
  Iff.rfl

/-- The formula `P_U` holds exactly when `P_p` holds for some member `p` of `U`. -/
@[simp] theorem realize_atomOfSet (U : Set (baseLanguage.{u}.Relations m)) (f : Fin m → Fin n) :
    (atomOfSet U f).Realize v xs ↔ ∃ p ∈ U, RelMap p (xs ∘ f) := by
  simp [atomOfSet, realize_ciSup]

end Formulas

/-! ### The structural clauses -/

section Structural

/-- **Nonemptiness**: `∃ x, ⊤`. -/
def nonemptyClause : baseLanguage.{u}.Sentenceω :=
  (⊤ : baseLanguage.{u}.BoundedFormulaω Empty 1).ex

/-- **Arity preservation**, first part [Kni26, Definition 3.3.3, clause 1]: for every relation
symbol `p` on `n` points and `i < j < n`, `∀ x̄, x_i = x_j → ¬ P_p(x̄)`. -/
noncomputable def arityClause : baseLanguage.{u}.Sentenceω :=
  ciInf fun n : ℕ ↦ ciInf fun p : baseLanguage.{u}.Relations n ↦
    ciInf fun ij : {ij : Fin n × Fin n // ij.1 < ij.2} ↦
      ((equal (Term.var (Sum.inr ij.1.1)) (Term.var (Sum.inr ij.1.2))).imp (atom p id).not).alls

/-- **Arity preservation**, second part [Kni26, Definition 3.3.3, clause 1]: for distinct relation
symbols `p` and `q` on `n` points, `∀ x̄, ¬ (P_p(x̄) ∧ P_q(x̄))`. -/
noncomputable def uniquenessClause : baseLanguage.{u}.Sentenceω :=
  ciInf fun n : ℕ ↦ ciInf fun pq : {pq : baseLanguage.{u}.Relations n × _ // pq.1 ≠ pq.2} ↦
    (atom pq.1.1 id ⊓ atom pq.1.2 id).not.alls

/-- Where the face map along `f` is defined at the stage type of a relation symbol, its value is
legal. -/
theorem isLegal_restrictFace_get (p : baseLanguage.{u}.Relations n) (f : Fin m ↪ Fin n)
    (h : (restrictFace f (type p)).isSome) : ((restrictFace f (type p)).get h).IsLegal :=
  (isLegal_type p).restrictFace f (Option.some_get h).symm

/-- The **face formula** of a relation symbol `p` along `f : Fin m ↪ Fin n`: `P_q(x̄ ∘ f)` when the
face map sends the stage type of `p` to `q`, and `⋀_q ¬ P_q(x̄ ∘ f)` when it is undefined. -/
noncomputable def faceFormula (p : baseLanguage.{u}.Relations n) (f : Fin m ↪ Fin n) :
    baseLanguage.{u}.BoundedFormulaω Empty n :=
  if h : (restrictFace f (type p)).isSome then
    atom (symbol _ (isLegal_restrictFace_get p f h)) f
  else ciInf fun q : baseLanguage.{u}.Relations m ↦ (atom q f).not

/-- **Consistency** [Kni26, Definition 3.3.3, clause 2]: for every relation symbol `p` on `n`
points and every `f : Fin m ↪ Fin n`, `∀ x̄, P_p(x̄) → φ(x̄)` for the face formula `φ` of `p`
along `f`. -/
noncomputable def consistencyClause : baseLanguage.{u}.Sentenceω :=
  ciInf fun n : ℕ ↦ ciInf fun p : baseLanguage.{u}.Relations n ↦
    ciInf fun f : (m : ℕ) × (Fin m ↪ Fin n) ↦ ((atom p id).imp (faceFormula p f.2)).alls

/-- **Covering** [Kni26, Definition 3.3.3, clause 3]: for every `n`,
`∀ x̄, ⋀_{i ≠ j} x_i ≠ x_j → ⋁_k ⋁_p ∃ y₀ … y_{k-1}, P_p(x̄, ȳ)`, with `p` on `n + k` points. -/
noncomputable def coveringClause : baseLanguage.{u}.Sentenceω :=
  ciInf fun n : ℕ ↦ ((distinct n).imp (ciSup fun k : ℕ ↦
    ciSup fun p : baseLanguage.{u}.Relations (n + k) ↦ existsBlock (atom p id))).alls

/-- The **structural sentence**: nonemptiness, arity preservation, consistency, and covering. -/
noncomputable def structuralSentence : baseLanguage.{u}.Sentenceω :=
  nonemptyClause ⊓ arityClause ⊓ uniquenessClause ⊓ consistencyClause ⊓ coveringClause

variable (M) [baseLanguage.{u}.Structure M]

/-- The semantic content of the structural sentence: a type assignment on a nonempty carrier with
exact face coherence and covering by initial segments. -/
structure IsStructural : Prop extends IsTypeAssignment M where
  /-- The carrier is nonempty. -/
  nonempty : Nonempty M
  /-- The faces of a tuple of type `p` have the faces of `p` as types, and no type where the face
  map is undefined. -/
  face ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M) : RelMap p xs →
    ∀ ⦃m : ℕ⦄ (f : Fin m ↪ Fin n),
      (∀ q : baseLanguage.{u}.Relations m, restrictFace f (type p) = some (type q) →
        RelMap q (xs ∘ f)) ∧
      (restrictFace f (type p) = none → ∀ q : baseLanguage.{u}.Relations m, ¬ RelMap q (xs ∘ f))
  /-- Every injective tuple is an initial segment of a tuple of some type. -/
  covering ⦃n : ℕ⦄ (xs : Fin n → M) : Function.Injective xs →
    ∃ (k : ℕ) (p : baseLanguage.{u}.Relations (n + k)) (ys : Fin k → M), RelMap p (Fin.append xs ys)

/-- The nonemptiness clause, realized. -/
theorem realize_nonemptyClause : nonemptyClause.Realize M ↔ Nonempty M := by
  simp only [nonemptyClause, Sentenceω.realize_def, realize_ex, realize_top]
  exact ⟨fun ⟨x, _⟩ ↦ ⟨x⟩, fun ⟨x⟩ ↦ ⟨x, trivial⟩⟩

/-- The first arity-preservation clause, realized: relations hold only of injective tuples. -/
theorem realize_arityClause : arityClause.Realize M ↔
    ∀ ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M), RelMap p xs →
      Function.Injective xs := by
  simp only [arityClause, Sentenceω.realize_def, realize_ciInf, realize_alls, realize_imp,
    realize_equal, Term.realize_var, Sum.elim_inr, realize_not, realize_atom, Function.comp_id,
    Subtype.forall, Prod.forall]
  refine forall_congr' fun n ↦ forall_congr' fun p ↦ ⟨fun h xs hp i j hij ↦ ?_,
    fun h i j hlt xs hxs hp ↦ hlt.ne (h xs hp hxs)⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h i j hlt xs hij hp
  · exact h j i hlt xs hij.symm hp

/-- The second arity-preservation clause, realized: at most one relation holds of a tuple. -/
theorem realize_uniquenessClause : uniquenessClause.Realize M ↔
    ∀ ⦃n : ℕ⦄ (p q : baseLanguage.{u}.Relations n) (xs : Fin n → M), RelMap p xs → RelMap q xs →
      p = q := by
  simp only [uniquenessClause, Sentenceω.realize_def, realize_ciInf, realize_alls, realize_not,
    realize_inf, realize_atom, Function.comp_id, Subtype.forall, Prod.forall, not_and]
  exact forall_congr' fun n ↦ ⟨fun h p q xs hp hq ↦ by_contra fun hpq ↦ h p q hpq xs hp hq,
    fun h p q hpq xs hp hq ↦ hpq (h p q xs hp hq)⟩

variable {M} in
/-- The face formula, realized: the faces of the tuple have the faces of `p` as types, and no type
where the face map is undefined. -/
theorem realize_faceFormula {v : Empty → M} {xs : Fin n → M} (p : baseLanguage.{u}.Relations n)
    (f : Fin m ↪ Fin n) : (faceFormula p f).Realize v xs ↔
      (∀ q : baseLanguage.{u}.Relations m, restrictFace f (type p) = some (type q) →
        RelMap q (xs ∘ f)) ∧
      (restrictFace f (type p) = none →
        ∀ q : baseLanguage.{u}.Relations m, ¬ RelMap q (xs ∘ f)) := by
  unfold faceFormula
  split_ifs with h
  · have hget := Option.some_get h
    rw [realize_atom]
    refine ⟨fun hq ↦ ⟨fun q hq' ↦ ?_, fun hn ↦ absurd hn (Option.isSome_iff_ne_none.mp h)⟩,
      fun hq ↦ hq.1 _ hget.symm⟩
    obtain rfl : symbol _ (isLegal_restrictFace_get p f h) = q :=
      type_injective (Option.some_injective _ (hget.trans hq'))
    exact hq
  · have hn : restrictFace f (type p) = none := Option.not_isSome_iff_eq_none.mp h
    simp only [realize_ciInf, realize_not, realize_atom, hn, reduceCtorEq, false_imp_iff,
      implies_true, forall_const, true_and]

/-- The consistency clause, realized. -/
theorem realize_consistencyClause : consistencyClause.Realize M ↔
    ∀ ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M), RelMap p xs →
      ∀ ⦃m : ℕ⦄ (f : Fin m ↪ Fin n),
        (∀ q : baseLanguage.{u}.Relations m, restrictFace f (type p) = some (type q) →
          RelMap q (xs ∘ f)) ∧
        (restrictFace f (type p) = none → ∀ q : baseLanguage.{u}.Relations m,
          ¬ RelMap q (xs ∘ f)) := by
  simp only [consistencyClause, Sentenceω.realize_def, realize_ciInf, realize_alls, realize_imp,
    realize_atom, Function.comp_id, realize_faceFormula, Sigma.forall]
  exact forall_congr' fun n ↦ forall_congr' fun p ↦
    ⟨fun h xs hp m f ↦ h m f xs hp, fun h m f xs hp ↦ h xs hp f⟩

/-- The covering clause, realized: every injective tuple is an initial segment of a tuple on
which a relation holds. -/
theorem realize_coveringClause : coveringClause.Realize M ↔
    ∀ ⦃n : ℕ⦄ (xs : Fin n → M), Function.Injective xs →
      ∃ (k : ℕ) (p : baseLanguage.{u}.Relations (n + k)) (ys : Fin k → M),
        RelMap p (Fin.append xs ys) := by
  simp only [coveringClause, Sentenceω.realize_def, realize_ciInf, realize_alls, realize_imp,
    realize_distinct, realize_ciSup, realize_existsBlock, realize_atom, Function.comp_id]

/-- **Realization of the structural sentence**: it holds in `M` exactly when `M` is a type
assignment on a nonempty carrier with exact face coherence and covering. -/
theorem realize_structuralSentence_iff : structuralSentence.Realize M ↔ IsStructural M := by
  have h : structuralSentence.Realize M ↔ nonemptyClause.Realize M ∧ arityClause.Realize M ∧
      uniquenessClause.Realize M ∧ consistencyClause.Realize M ∧ coveringClause.Realize M := by
    simp only [structuralSentence, Sentenceω.realize_def, realize_inf, and_assoc]
  rw [h, realize_nonemptyClause, realize_arityClause, realize_uniquenessClause,
    realize_consistencyClause, realize_coveringClause]
  exact ⟨fun ⟨h₁, h₂, h₃, h₄, h₅⟩ ↦ ⟨⟨h₂, h₃⟩, h₁, h₄, h₅⟩,
    fun h ↦ ⟨h.nonempty, h.injective, h.unique, h.face, h.covering⟩⟩

end Structural

/-! ### The extension clauses -/

section Extension

variable [baseLanguage.{u}.Structure M]

/-- Some point extends the tuple `xs` to a tuple on which `P_q` holds for a relation symbol `q`
whose stage type is in `U`. -/
def RealizesOver (xs : Fin n → M) (U : Set (StageType.{u} ω (n + 1))) : Prop :=
  ∃ (y : M) (q : baseLanguage.{u}.Relations (n + 1)), type q ∈ U ∧ RelMap q (Fin.snoc xs y)

/-- The shape of the **extension clauses** [Kni26, Definition 3.3.3, clause 4]: for a countable
parameter type `P n p` for each relation symbol `p` on `n` points and families `U n p a` of stage
types on `n + 1` points, `∀ x̄, P_p(x̄) → ⋀_{a : P n p} ∃ y, P_{U n p a}(x̄, y)`. -/
noncomputable def extensionClause (P : ∀ n : ℕ, baseLanguage.{u}.Relations n → Type w)
    [∀ n p, Countable (P n p)]
    (U : ∀ (n : ℕ) (p : baseLanguage.{u}.Relations n), P n p → Set (StageType.{u} ω (n + 1))) :
    baseLanguage.{u}.Sentenceω :=
  ciInf fun n : ℕ ↦ ciInf fun p : baseLanguage.{u}.Relations n ↦
    ((atom p id).imp (ciInf fun a : P n p ↦ (atomOfSet {q | type q ∈ U n p a} id).ex)).alls

variable (M) in
/-- An extension clause, realized: over every tuple of a type `p`, for every parameter, some point
extends the tuple to one with a type in the family. -/
theorem realize_extensionClause (P : ∀ n : ℕ, baseLanguage.{u}.Relations n → Type w)
    [∀ n p, Countable (P n p)]
    (U : ∀ (n : ℕ) (p : baseLanguage.{u}.Relations n), P n p → Set (StageType.{u} ω (n + 1))) :
    (extensionClause P U).Realize M ↔
      ∀ ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M), RelMap p xs →
        ∀ a : P n p, RealizesOver xs (U n p a) := by
  simp only [extensionClause, Sentenceω.realize_def, realize_ciInf, realize_alls, realize_imp,
    realize_atom, Function.comp_id, realize_ex, realize_atomOfSet, Set.mem_ofPred_eq, RealizesOver]

/-- The parameters of **generalized saturation** over a relation symbol `p` on `n` points: the
schemes on `n + 1` points whose saturation family has a member among the cofaces of the stage type
of `p`. -/
def SaturationIndex (p : baseLanguage.{u}.Relations n) : Type (u + 1) :=
  {S : Scheme.{u} (n + 1) // ((type p).cofaces ∩ saturationFamily S).Nonempty}

/-- The labelling of the cells of a scheme with the **bottom pattern** `π`: bottom where `π`
holds, and the formal top elsewhere. -/
def patternLabel {k : ℕ} (π : Fin k → Bool) (j : Fin k) : Label.{u} :=
  if π j then ⊥ else ⊤

/-- The labelling of a pattern is bottom exactly where the pattern holds. -/
@[simp] theorem patternLabel_eq_bot_iff {k : ℕ} (π : Fin k → Bool) (j : Fin k) :
    patternLabel.{u} π j = ⊥ ↔ π j = true := by
  unfold patternLabel
  split_ifs with h <;> simp [h]

/-- The parameters of the **bottom pattern** over a relation symbol `p` on `n` points: the schemes
on `n + 1` points with a bottom pattern on their cells whose bottom-pattern family has a member
among the cofaces of the stage type of `p`. -/
def BottomPatternIndex (p : baseLanguage.{u}.Relations n) : Type (u + 1) :=
  {Sπ : (S : Scheme.{u} (n + 1)) × (Fin S.card → Bool) //
    ((type p).cofaces ∩ bottomPatternFamily Sπ.1 (patternLabel Sπ.2)).Nonempty}

/-- The schemes of the cofaces of a stage type are schemes of relation symbols. -/
theorem mem_range_toScheme_of_mem_cofaces {p : StageType.{u} ω n}
    {q : StageType.{u} ω (n + 1)} (hq : q ∈ p.cofaces) :
    q.toScheme ∈ Set.range fun q' : baseLanguage.{u}.Relations (n + 1) ↦ (type q').toScheme :=
  ⟨symbol q hq.1, rfl⟩

/-- The parameters of generalized saturation are countably many: their schemes are schemes of
relation symbols. -/
instance (p : baseLanguage.{u}.Relations n) : Countable (SaturationIndex p) :=
  Set.Countable.to_subtype (s := {S | ((type p).cofaces ∩ saturationFamily S).Nonempty}) <|
    (Set.countable_range _).mono fun _ ⟨_, hq, hS⟩ ↦ hS ▸ mem_range_toScheme_of_mem_cofaces hq

/-- The parameters of the bottom pattern are countably many: their schemes are schemes of
relation symbols, each with finitely many patterns. -/
instance (p : baseLanguage.{u}.Relations n) : Countable (BottomPatternIndex p) := by
  let T := Set.range fun q : baseLanguage.{u}.Relations (n + 1) ↦ (type q).toScheme
  have : Countable T := (Set.countable_range _).to_subtype
  let F : BottomPatternIndex p → Σ S : T, (Fin S.1.card → Bool) := fun x ↦
    ⟨⟨x.1.1, x.2.elim fun _ ⟨hq, hS, _⟩ ↦ hS ▸ mem_range_toScheme_of_mem_cofaces hq⟩, x.1.2⟩
  refine Function.Injective.countable (f := F) ?_
  intro x y h
  obtain ⟨h, h'⟩ := Sigma.mk.inj_iff.mp h
  have hS : x.1.1 = y.1.1 := congrArg Subtype.val h
  obtain ⟨⟨S, π⟩, hx⟩ := x
  obtain ⟨⟨S', π'⟩, hy⟩ := y
  obtain rfl : S = S' := hS
  obtain rfl := eq_of_heq h'
  rfl

/-- **Generalized saturation** [Kni26, Definition 3.3.3, clause 4, with Definition 3.2.1,
clause 4(a)i]: over a tuple of type `p`, a point realizing the saturation family of every scheme
`S` whose instance has a member among the cofaces of `p`. -/
noncomputable def saturationClause : baseLanguage.{u}.Sentenceω :=
  extensionClause (fun _ p ↦ SaturationIndex p) fun _ _ S ↦ saturationFamily S.1

/-- The **bottom pattern** [Kni26, Definition 3.3.3, clause 4, with Definition 3.2.1,
clause 4(a)ii]: over a tuple of type `p`, a point realizing the bottom-pattern family of every
scheme and pattern whose instance has a member among the cofaces of `p`. -/
noncomputable def bottomPatternClause : baseLanguage.{u}.Sentenceω :=
  extensionClause (fun _ p ↦ BottomPatternIndex p) fun _ _ Sπ ↦
    bottomPatternFamily Sπ.1.1 (patternLabel Sπ.1.2)

/-- **Uniformity** [Kni26, Definition 3.3.3, clause 4, with Definition 3.2.1, clause 4(b)]: over
every tuple of a type, a point realizing the uniformity family of every `γ < ω` that is zero or a
limit. -/
noncomputable def uniformityClause : baseLanguage.{u}.Sentenceω :=
  extensionClause (fun _ _ ↦ {γ : Set.Iio (ω : Ordinal.{u}) // Order.IsSuccPrelimit γ.1})
    fun _ _ γ ↦ uniformityFamily γ.1.1

/-- **High-arity dominance** [Kni26, Definition 3.3.3, clause 4, with Definition 3.2.1,
clause 4(c)]: over every tuple of a type, a point realizing the dominance family of every
`γ < ω`. -/
noncomputable def dominanceClause : baseLanguage.{u}.Sentenceω :=
  extensionClause (fun _ _ ↦ Set.Iio (ω : Ordinal.{u})) fun _ _ γ ↦ dominanceFamily γ.1

/-- The **four-family sentence** [Kni26, Definition 3.3.3]: the structural sentence and the four
extension clauses. -/
noncomputable def fourFamilySentence : baseLanguage.{u}.Sentenceω :=
  structuralSentence ⊓ saturationClause ⊓ bottomPatternClause ⊓ uniformityClause ⊓ dominanceClause

variable (M)

/-- The generalized-saturation clause, realized, for every scheme with a nonempty instance. -/
theorem realize_saturationClause : saturationClause.Realize M ↔
    ∀ ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M), RelMap p xs →
      ∀ S : Scheme.{u} (n + 1), ((type p).cofaces ∩ saturationFamily S).Nonempty →
        RealizesOver xs (saturationFamily S) := by
  rw [saturationClause, realize_extensionClause]
  exact ⟨fun h _ p xs hp S hS ↦ h p xs hp ⟨S, hS⟩, fun h _ p xs hp S ↦ h p xs hp S.1 S.2⟩

/-- The bottom-pattern clause, realized, for every labelling of the cells of every scheme. -/
theorem realize_bottomPatternClause : bottomPatternClause.Realize M ↔
    ∀ ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M), RelMap p xs →
      ∀ (S : Scheme.{u} (n + 1)) (ρ : Fin S.card → Label.{u}),
        ((type p).cofaces ∩ bottomPatternFamily S ρ).Nonempty →
          RealizesOver xs (bottomPatternFamily S ρ) := by
  rw [bottomPatternClause, realize_extensionClause]
  refine ⟨fun h n p xs hp S ρ hne ↦ ?_, fun h _ p xs hp Sπ ↦ h p xs hp _ _ Sπ.2⟩
  have hfam : (bottomPatternFamily S ρ : Set (StageType.{u} ω (n + 1))) =
      bottomPatternFamily S (patternLabel fun j ↦ decide (ρ j = ⊥)) :=
    bottomPatternFamily_congr fun j ↦ by simp
  rw [hfam] at hne ⊢
  exact h p xs hp ⟨⟨S, _⟩, hne⟩

/-- The uniformity clause, realized, for every `γ < ω` that is zero or a limit. -/
theorem realize_uniformityClause : uniformityClause.Realize M ↔
    ∀ ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M), RelMap p xs →
      ∀ γ : Ordinal.{u}, Order.IsSuccPrelimit γ → γ < ω →
        RealizesOver xs (uniformityFamily γ) := by
  rw [uniformityClause, realize_extensionClause]
  exact ⟨fun h _ p xs hp γ hγ hγω ↦ h p xs hp ⟨⟨γ, hγω⟩, hγ⟩,
    fun h _ p xs hp γ ↦ h p xs hp γ.1.1 γ.2 γ.1.2⟩

/-- The high-arity dominance clause, realized, for every `γ < ω`. -/
theorem realize_dominanceClause : dominanceClause.Realize M ↔
    ∀ ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M), RelMap p xs →
      ∀ γ : Ordinal.{u}, γ < ω → RealizesOver xs (dominanceFamily γ) := by
  rw [dominanceClause, realize_extensionClause]
  exact ⟨fun h _ p xs hp γ hγω ↦ h p xs hp ⟨γ, hγω⟩, fun h _ p xs hp γ ↦ h p xs hp γ.1 γ.2⟩

/-- The semantic content of the four-family sentence: the structural conditions, and over every
tuple of a type `p` a point realizing each instance of the four families, with the quantifiers of
`Realization.IsModel` at stage `ω`. -/
structure IsFourFamilyModel : Prop extends IsStructural M where
  /-- Generalized saturation, for every instance with a member among the cofaces of `p`. -/
  saturation ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M) : RelMap p xs →
    ∀ S : Scheme.{u} (n + 1), ((type p).cofaces ∩ saturationFamily S).Nonempty →
      RealizesOver xs (saturationFamily S)
  /-- The bottom pattern, for every instance with a member among the cofaces of `p`. -/
  bottomPattern ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M) : RelMap p xs →
    ∀ (S : Scheme.{u} (n + 1)) (ρ : Fin S.card → Label.{u}),
      ((type p).cofaces ∩ bottomPatternFamily S ρ).Nonempty →
        RealizesOver xs (bottomPatternFamily S ρ)
  /-- Uniformity, for every `γ < ω` that is zero or a limit. -/
  uniformity ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M) : RelMap p xs →
    ∀ γ : Ordinal.{u}, Order.IsSuccPrelimit γ → γ < ω → RealizesOver xs (uniformityFamily γ)
  /-- High-arity dominance, for every `γ < ω`. -/
  dominance ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M) : RelMap p xs →
    ∀ γ : Ordinal.{u}, γ < ω → RealizesOver xs (dominanceFamily γ)

/-- **Realization of the four-family sentence**: it holds in `M` exactly when `M` satisfies the
structural conditions and the four extension families. -/
theorem realize_fourFamilySentence_iff_isFourFamilyModel :
    fourFamilySentence.Realize M ↔ IsFourFamilyModel M := by
  have h : fourFamilySentence.Realize M ↔ structuralSentence.Realize M ∧
      saturationClause.Realize M ∧ bottomPatternClause.Realize M ∧ uniformityClause.Realize M ∧
        dominanceClause.Realize M := by
    simp only [fourFamilySentence, Sentenceω.realize_def, realize_inf, and_assoc]
  rw [h, realize_structuralSentence_iff, realize_saturationClause, realize_bottomPatternClause,
    realize_uniformityClause, realize_dominanceClause]
  exact ⟨fun ⟨h₁, h₂, h₃, h₄, h₅⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅⟩,
    fun h ↦ ⟨h.toIsStructural, h.saturation, h.bottomPattern, h.uniformity, h.dominance⟩⟩

end Extension

end baseLanguage

end VaughtConjecture
