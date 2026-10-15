/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.CountableIndex
import InfinitaryLogic.Lomega1omega.FiniteQuantification
import VaughtConjecture.Correspondence.Density.Density
import VaughtConjecture.Language.Sentence

/-!
# The sentence `σ[L]`

Numbering as in the current draft of [AFK26].  This file transcribes the sentence `σ[L]` of
[AFK26, Definition 4.22] for the template system `L` of legal templates, as a sentence of
`L_{ω₁,ω}` over the base sublanguage `L_c[L]` (`baseTemplateLanguage`), clause by clause.  It is
defined syntactically, as a countable conjunction of the printed sentences; it is **not** defined
by the existence of a lift in `K₀[L]` (that comparison is B.T12, proved in
`VaughtConjecture.Correspondence.Sentence.Correspondence`; its statement is
`SentenceCorrespondenceTarget` in `VaughtConjecture.Correspondence.Sentence.Targets`).
Correspondence with the printed definitions.

**The vocabulary.**  `L_c[L] = L_a ∪ {R_t : t ∈ L, τ₀(Q_t) = Q_t}` [AFK26, Definition 4.17].  In
`baseTemplateLanguage` the symbol `R_t` is named by the renaming class of `t`
(`BaseSymbol.base`), as in `templateLanguage`: the template system `L` keeps exactly one template
in each renaming class ([AFK26, Definition 4.11], last two clauses), and every stage type already
has the underlying set `[n]` and the cells `[k]`, so `t ↦ [t]` is a bijection from the printed
symbols `R_t` onto the classes fixed by `τ₀`.  The printed vocabulary therefore needs no separate
language renaming here; the bijection is recorded as `ChosenVocabularyTarget` in
`VaughtConjecture.Correspondence.Sentence.Dictionary`, and it is distinct from the class-disjunction
interpretation of the symbols in the base language of positional types (`classStructure` there).
`cR[L] = L_c[L] ∖ L_a` is `ClassSymbol`: the legal classes fixed by `τ₀`, the projection to the
block stage `blockStage 0 = ω`.

**Variables and arities.**  Printed sentences quantify over `x₀, …, x_{n-1}` with `n ≥ 1`; here
the arity is written `n + 1` with `n : ℕ`, and a sentence `∀ x̄, φ` is the universal closure
`φ.alls` of a formula `φ` on `n + 1` bound variables.  `atomAt r f` is `r(x_{f 0}, …)`, and
`eqAt i j` is `x_i = x_j`.

**Countability.**  Every countable conjunction and disjunction is the library's `ciInf` or
`ciSup`, whose index type carries a `Countable` instance; each clause names its index and the
reason it is countable.  The sources are: `ℕ` (arities, numbers of new points, the cutoffs
`n ∈ ω` of clause (d)); finite types (positions `Fin k`, maps `Fin k → Fin m`, permutations); the
symbols of `L_c[L]` of a fixed arity (`countable_classSymbol`, `countable_baseSymbol`: a legal class
fixed by `τ₀` is determined by its reduction to the block stage `ω`, and the stage types at the
countable stage `ω` on `n` points are countably many, `StageType.countable_of_lt_omega_one`);
and sigma, product and subtype types built from these.

**The clauses** (the conjunction `templateSentence`):

* (a) `⋀ ThPlan` [AFK26, Definition 4.13], `planClause`:
  - `Th_Geo[L_a]` [AFK26, Definition 2.1]: `geometryDistinctClause`, `geometryPermClause`,
    `geometryExtensionClause`, `geometryIntersectionClause`;
  - (Singletons) `∀ x, P_1(x)`: `singletonsClause`;
  - (Convexity), with the printed infinitary formula `a ∈ cl({b_i})` (`closureFormula`):
    `convexityClause`;
  - (Extreme Points), the two sentences for `n ≥ 3`: `extremePointsClause`,
    `extremePointsExclusionClause`.
* (b) `structureClause`: `typingClause` (`P_n ↔ ⋁_{R ∈ cR[L]^n} R`), `exclusivityClause`
  (distinct `R, R' ∈ cR[L]^n` hold of no common tuple), `determinationClause` (`R ∈ cR[L]^n`
  determines every `S ∈ L_c[L]^k` along every sequence of places).
* (c) `diagramClause`: for `R_t ∈ cR[L]` and every pair `(Q_t(x), ψ)` of `ID[L]` with `ψ` an atomic
  or negated atomic formula of `L_c[L]`, `∀ x, R_t(x) → ψ`.  The pairs are those of
  `templateDiagramPairs`: `S(x_i)` when `t.Holds S i`, and `¬S(x_i)` otherwise
  (`mk_atom_mem_templateDiagramPairs_iff`).
* (d) `densityClause`: for every `k ∈ ω` and all `t*, t` with `R_{t*} ∈ cR[L]`, `R_t ∈ L_c[L]` and
  `(Q_t(x y), Q_{t*}(x)) ∈ ID[L]`, `∀ x, R_{t*}(x) → ∃ y ⋁_{s} R_s(x y)` over the `s` with
  `R_s ∈ L_c[L]` and `trunc_k(s) ≅_ren trunc_k(t)` (`TemplateClass.TruncEquiv`, raw truncation up
  to renaming).  The donors `t` are of rank `0` (`R_t ∈ L_c[L]`), on any number `m ≥ 0` of new
  points, and the witnesses are taken up to renaming.

**Empty carrier.**  Every clause is a conjunction of universal closures over at least one
variable, so the empty structure satisfies `σ[L]`; `K_β[L]` has nonempty carriers by convention
(`templateStageClass`).  The comparison B.T12 therefore assumes a nonempty carrier
(`VaughtConjecture.Correspondence.Sentence.Targets`).
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal BoundedFormulaω

noncomputable section

/-! ### The symbols `cR[L]` and countability -/

/-- **The symbols `cR[L]^n = L_c[L]^n ∖ L_a`** [AFK26, Definitions 4.17 and 4.22]: the legal
classes `t` on `n` points with `τ₀(Q_t) = Q_t`, the projection to the block stage `ω`.
Correspondence with the printed definitions. -/
def ClassSymbol (n : ℕ) : Type (u + 1) :=
  {c : LegalClass.{u} n // c.1.project (isSuccPrelimit_blockStage 0) = c.1}

/-- The symbol `R_t` of `L_c[L]` for `t ∈ cR[L]^n`, `n ≥ 1`.
Correspondence with the printed definitions. -/
def ClassSymbol.toBaseSymbol {n : ℕ} (t : ClassSymbol.{u} n) (hn : 0 < n) : BaseSymbol.{u} n :=
  BaseSymbol.base t.1 t.2 hn

/-- **`cR[L]^n` is countable**: a legal class fixed by `τ₀` is determined by its reduction to the
block stage `ω` (it is the projection, which is the reduction read again at `ω₁`), and the classes
at the countable stage `ω` are countably many.  Native construction. -/
instance countable_classSymbol (n : ℕ) : Countable (ClassSymbol.{u} n) := by
  have : Countable (StageType.{u} (blockStage 0) n) :=
    StageType.countable_of_lt_omega_one
      (by rw [blockStage_zero]; exact omega0_lt_omega_one) n
  refine Function.Injective.countable
    (f := fun t : ClassSymbol.{u} n ↦ t.1.1.reduce (isSuccPrelimit_blockStage 0)) ?_
  intro t t' h
  have h' : t.1.1 = t'.1.1 := by
    rw [← t.2, ← t'.2, TemplateClass.project_eq_reduce_reduce,
      TemplateClass.project_eq_reduce_reduce]
    exact congrArg _ h
  exact Subtype.ext (Subtype.ext h')

/-- A symbol of `L_c[L]` read as `none` for `P_n` and as its class for `R_t`. -/
private def BaseSymbol.toOption {n : ℕ} : BaseSymbol.{u} n → Option (ClassSymbol.{u} n)
  | .closed _ => none
  | .base c h0 _ => some ⟨c, h0⟩

/-- **`L_c[L]^n` is countable** (`|L_c^n| ≤ ω`, [AFK26, Convention 2.3]): one symbol `P_n` and
the symbols of `cR[L]^n`.  Native construction. -/
instance countable_baseSymbol (n : ℕ) : Countable (BaseSymbol.{u} n) := by
  refine Function.Injective.countable (f := BaseSymbol.toOption) ?_
  rintro (_ | ⟨c, h0, _⟩) (_ | ⟨c', h0', _⟩) h
  · rfl
  · cases h
  · cases h
  · obtain rfl : c = c' := congrArg Subtype.val (Option.some.inj h)
    rfl

/-! ### Formula helpers -/

namespace TemplateSentence

variable {N : ℕ}

/-- The atomic formula `r(x_{f 0}, …, x_{f (k-1)})` of `L_c[L]` on the bound variables. -/
def atomAt {k : ℕ} (r : BaseSymbol.{u} k) (f : Fin k → Fin N) :
    baseTemplateLanguage.{u}.BoundedFormulaω Empty N :=
  rel r fun i ↦ Term.var (Sum.inr (f i))

/-- The atomic formula `x_i = x_j`. -/
def eqAt (i j : Fin N) : baseTemplateLanguage.{u}.BoundedFormulaω Empty N :=
  equal (Term.var (Sum.inr i)) (Term.var (Sum.inr j))

/-- `P_k(x_{f 0}, …, x_{f (k-1)})`, for `k ≥ 1`. -/
def closedAt (k : ℕ) (hk : 0 < k) (f : Fin k → Fin N) :
    baseTemplateLanguage.{u}.BoundedFormulaω Empty N :=
  atomAt (BaseSymbol.closed hk) f

/-- `x_a` is among `x_{e 0}, …, x_{e (m-1)}`: the finite disjunction `⋁_{l < m} x_a = x_{e l}`.
The index `Fin m` is finite. -/
def memAmong {m : ℕ} (a : Fin N) (e : Fin m → Fin N) :
    baseTemplateLanguage.{u}.BoundedFormulaω Empty N :=
  ciSup fun l : Fin m ↦ eqAt a (e l)

/-- `⋀_{i < j} x_{f i} ≠ x_{f j}`: the places `f` carry distinct points.  The index, pairs
`i < j` in `Fin k`, is finite. -/
def distinctAt {k : ℕ} (f : Fin k → Fin N) : baseTemplateLanguage.{u}.BoundedFormulaω Empty N :=
  ciInf fun ij : {ij : Fin k × Fin k // ij.1 < ij.2} ↦ (eqAt (f ij.1.1) (f ij.1.2)).not

/-- **The formula `a ∈ cl({b_i}_{i ∈ ι})`** of [AFK26, Definition 4.13] (Convexity): there is a
finite set `{e_l}_{l ∈ [m]}` (here `m + 1` new variables, as `P_m` needs `m ≥ 1`) with
`{b_i} ∪ {a} ⊆ {e_l}`, `P_m(e_0, …, e_{m-1})`, and, for every sequence `{i_j}_{j ∈ [k]}` of
places (`k ≥ 1`), if `P_k(e_{i_0}, …, e_{i_{k-1}})` and every `b_r` is among the `e_{i_j}`, then
`a` is among the `e_{i_j}`.  Indices: the size `m ∈ ℕ`; the parameters `ι` (countable by
hypothesis; finite in every use); the sequences `Σ k : ℕ, Fin (k + 1) → Fin (m + 1)` (a sigma over
`ℕ` of finite types). -/
def closureFormula {ι : Type} [Countable ι] (a : Fin N) (b : ι → Fin N) :
    baseTemplateLanguage.{u}.BoundedFormulaω Empty N :=
  ciSup fun m : ℕ ↦
    let old : Fin N → Fin (N + (m + 1)) := Fin.castAdd (m + 1)
    let e : Fin (m + 1) → Fin (N + (m + 1)) := Fin.natAdd N
    existsBlock
      ((ciInf fun r : ι ↦ memAmong (old (b r)) e) ⊓ memAmong (old a) e ⊓
        closedAt (m + 1) m.succ_pos e ⊓
        ciInf fun ki : Σ k : ℕ, Fin (k + 1) → Fin (m + 1) ↦
          ((closedAt (ki.1 + 1) ki.1.succ_pos (e ∘ ki.2) ⊓
              ciInf fun r : ι ↦ memAmong (old (b r)) (e ∘ ki.2)).imp
            (memAmong (old a) (e ∘ ki.2))))

end TemplateSentence

open TemplateSentence

/-! ### (a) `⋀ ThPlan` -/

/-- **`Th_Geo`, first clause, first sentence** [AFK26, Definition 2.1]: for `n ≥ 1`,
`∀ x̄, P_n(x̄) → ⋀_{i < j ∈ [n]} x_i ≠ x_j`.  Indices: the arity `n ∈ ℕ`; the pairs `i < j`
(finite).  Correspondence with the printed definitions. -/
def geometryDistinctClause : baseTemplateLanguage.{u}.Sentenceω :=
  ciInf fun n : ℕ ↦ ((closedAt (n + 1) n.succ_pos id).imp (distinctAt id)).alls

/-- **`Th_Geo`, first clause, second sentence** [AFK26, Definition 2.1]: for `n ≥ 1` and every
bijection `σ : [n] → [n]`, `∀ x̄, P_n(x₀, …, x_{n-1}) ↔ P_n(x_{σ(0)}, …, x_{σ(n-1)})`.  Indices:
the arity `n ∈ ℕ`; the permutations of `Fin (n + 1)` (finite).
Correspondence with the printed definitions. -/
def geometryPermClause : baseTemplateLanguage.{u}.Sentenceω :=
  ciInf fun n : ℕ ↦ ciInf fun σ : Equiv.Perm (Fin (n + 1)) ↦
    ((closedAt (n + 1) n.succ_pos id).iff (closedAt (n + 1) n.succ_pos σ)).alls

/-- **`Th_Geo`, second clause** [AFK26, Definition 2.1]: for `n ≥ 1`,
`∀ x̄, ⋀_{i < j} x_i ≠ x_j → ⋁_{k ∈ ω} ∃ x_n, …, x_{n+k-1}, P_{n+k}(x₀, …, x_{n+k-1})`.
Indices: the arity `n ∈ ℕ`; the number `k ∈ ℕ` of new points.
Correspondence with the printed definitions. -/
def geometryExtensionClause : baseTemplateLanguage.{u}.Sentenceω :=
  ciInf fun n : ℕ ↦ ((distinctAt id).imp (ciSup fun k : ℕ ↦
    existsBlock (closedAt (n + 1 + k) (Nat.lt_add_right k n.succ_pos) id))).alls

/-- **`Th_Geo`, third clause** [AFK26, Definition 2.1]: for `n₀, n₁, k ≥ 1`, if
`P_{n₀}(x₀, …, x_{n₀-1})`, `P_{n₁}(y₀, …, y_{n₁-1})`, and `z₀, …, z_{k-1}` is an enumeration of
`{x_i} ∩ {y_i}` (the `z_l` are distinct, each lies among the `x_i` and among the `y_j`, and every
common point `x_i = y_j` lies among the `z_l`), then `P_k(z₀, …, z_{k-1})`.  The variables are
`x̄ ȳ z̄`, in this order.  Indices: the arities `(n₀, n₁, k) ∈ ℕ³`; positions and pairs of positions
(finite).  Correspondence with the printed definitions. -/
def geometryIntersectionClause : baseTemplateLanguage.{u}.Sentenceω :=
  ciInf fun a : ℕ × ℕ × ℕ ↦
    let x : Fin (a.1 + 1) → Fin (a.1 + 1 + (a.2.1 + 1) + (a.2.2 + 1)) :=
      fun i ↦ Fin.castAdd (a.2.2 + 1) (Fin.castAdd (a.2.1 + 1) i)
    let y : Fin (a.2.1 + 1) → Fin (a.1 + 1 + (a.2.1 + 1) + (a.2.2 + 1)) :=
      fun j ↦ Fin.castAdd (a.2.2 + 1) (Fin.natAdd (a.1 + 1) j)
    let z : Fin (a.2.2 + 1) → Fin (a.1 + 1 + (a.2.1 + 1) + (a.2.2 + 1)) :=
      Fin.natAdd (a.1 + 1 + (a.2.1 + 1))
    ((closedAt (a.1 + 1) a.1.succ_pos x ⊓ closedAt (a.2.1 + 1) a.2.1.succ_pos y ⊓
        (distinctAt z ⊓ (ciInf fun l : Fin (a.2.2 + 1) ↦ memAmong (z l) x ⊓ memAmong (z l) y) ⊓
          ciInf fun ij : Fin (a.1 + 1) × Fin (a.2.1 + 1) ↦
            (eqAt (x ij.1) (y ij.2)).imp (memAmong (x ij.1) z))).imp
      (closedAt (a.2.2 + 1) a.2.2.succ_pos z)).alls

/-- **(Singletons)** [AFK26, Definition 4.13]: `∀ x, P_1(x)`.
Correspondence with the printed definitions. -/
def singletonsClause : baseTemplateLanguage.{u}.Sentenceω :=
  (closedAt 1 Nat.one_pos id : baseTemplateLanguage.{u}.BoundedFormulaω Empty 1).alls

/-- **(Convexity)** [AFK26, Definition 4.13]: for `n ≥ 1`,
`∀ x̄ ∀ y z, [P_n(x̄) ∧ y ≠ z ∧ ⋀_i (x_i ≠ y ∧ x_i ≠ z)] →
[y ∈ cl({x_i} ∪ {z}) → z ∉ cl({x_i} ∪ {y})]`, with `cl` the printed formula `closureFormula`.  The
variables are `x̄ y z`; the parameter set `{x_i} ∪ {z}` is indexed by `Option (Fin (n + 1))`
(`none ↦ z`).  Indices: the arity `n ∈ ℕ`; positions (finite).
Correspondence with the printed definitions. -/
def convexityClause : baseTemplateLanguage.{u}.Sentenceω :=
  ciInf fun n : ℕ ↦
    let x : Fin (n + 1) → Fin (n + 1 + 2) := Fin.castAdd 2
    let y : Fin (n + 1 + 2) := Fin.natAdd (n + 1) 0
    let z : Fin (n + 1 + 2) := Fin.natAdd (n + 1) 1
    ((closedAt (n + 1) n.succ_pos x ⊓ (eqAt y z).not ⊓
        ciInf fun i : Fin (n + 1) ↦ (eqAt (x i) y).not ⊓ (eqAt (x i) z).not).imp
      ((closureFormula y fun o : Option (Fin (n + 1)) ↦ o.elim z x).imp
        (closureFormula z fun o : Option (Fin (n + 1)) ↦ o.elim y x).not)).alls

/-- **(Extreme Points), first sentence** [AFK26, Definition 4.13]: for `n ≥ 3`,
`∀ x̄, P_n(x̄) → ⋁_{i < j ∈ [n]} [P_{n-1}(x̄ without x_i) ∧ P_{n-1}(x̄ without x_j)]`; "without
`x_i`" is the composite with `Fin.succAbove i`.  Here `n = m + 3`.  Indices: `m ∈ ℕ`; the pairs
`i < j` (finite).  Correspondence with the printed definitions. -/
def extremePointsClause : baseTemplateLanguage.{u}.Sentenceω :=
  ciInf fun m : ℕ ↦ ((closedAt (m + 3) (by omega) id).imp
    (ciSup fun ij : {ij : Fin (m + 3) × Fin (m + 3) // ij.1 < ij.2} ↦
      closedAt (m + 2) (by omega) (Fin.succAbove ij.1.1) ⊓
        closedAt (m + 2) (by omega) (Fin.succAbove ij.1.2))).alls

/-- **(Extreme Points), second sentence** [AFK26, Definition 4.13]: for `n ≥ 3`,
`∀ x̄, P_n(x̄) → ¬[P_{n-1}(x₁, …, x_{n-1}) ∧ P_{n-1}(x₀, x₂, …, x_{n-1}) ∧
P_{n-1}(x₀, x₁, x₃, …, x_{n-1})]` (the tuples without `x₀`, `x₁`, `x₂`).  Here `n = m + 3`.
Index: `m ∈ ℕ`.  Correspondence with the printed definitions. -/
def extremePointsExclusionClause : baseTemplateLanguage.{u}.Sentenceω :=
  ciInf fun m : ℕ ↦ ((closedAt (m + 3) (by omega) id).imp
    (closedAt (m + 2) (by omega) (Fin.succAbove 0) ⊓ closedAt (m + 2) (by omega) (Fin.succAbove 1) ⊓
      closedAt (m + 2) (by omega) (Fin.succAbove 2)).not).alls

/-- **Clause (a) of [AFK26, Definition 4.22], `⋀ ThPlan`** [AFK26, Definition 4.13]: `Th_Geo[L_a]`
(four sentences), (Singletons), (Convexity), and (Extreme Points) (two sentences).
Correspondence with the printed definitions. -/
def planClause : baseTemplateLanguage.{u}.Sentenceω :=
  geometryDistinctClause ⊓ geometryPermClause ⊓ geometryExtensionClause ⊓
    geometryIntersectionClause ⊓ singletonsClause ⊓ convexityClause ⊓ extremePointsClause ⊓
    extremePointsExclusionClause

/-! ### (b) The structured geometry of `cR[L]` -/

/-- **Clause (b) of [AFK26, Definition 4.22], first sentence**: for `n ≥ 1`,
`∀ x̄, P_n(x̄) ↔ ⋁_{R ∈ cR[L]^n} R(x̄)`.  Indices: the arity `n ∈ ℕ`; the symbols `cR[L]^n`
(`countable_classSymbol`).  Correspondence with the printed definitions. -/
def typingClause : baseTemplateLanguage.{u}.Sentenceω :=
  ciInf fun n : ℕ ↦ ((closedAt (n + 1) n.succ_pos id).iff
    (ciSup fun t : ClassSymbol.{u} (n + 1) ↦ atomAt (t.toBaseSymbol n.succ_pos) id)).alls

/-- **Clause (b) of [AFK26, Definition 4.22], second sentence**: for `n ≥ 1` and distinct
`R, R' ∈ cR[L]^n`, `∀ x̄, R(x̄) → ¬R'(x̄)`.  Indices: the arity `n ∈ ℕ`; the pairs of distinct
symbols (a subtype of a product of countable types).
Correspondence with the printed definitions. -/
def exclusivityClause : baseTemplateLanguage.{u}.Sentenceω :=
  ciInf fun n : ℕ ↦
    ciInf fun tt : {tt : ClassSymbol.{u} (n + 1) × ClassSymbol.{u} (n + 1) // tt.1 ≠ tt.2} ↦
      ((atomAt (tt.1.1.toBaseSymbol n.succ_pos) id).imp
        (atomAt (tt.1.2.toBaseSymbol n.succ_pos) id).not).alls

/-- **Clause (b) of [AFK26, Definition 4.22], third sentence**: for `n ≥ 1`, `k ≥ 1`,
`R ∈ cR[L]^n`, `S ∈ L_c[L]^k` and every sequence `⟨i_j⟩_{j ∈ [k]} ⊆ [n]`,
`∀ x̄ ∀ ȳ, [R(x̄) ∧ R(ȳ)] → [S(x_{i_0}, …) ↔ S(y_{i_0}, …)]`.  The variables are `x̄ ȳ`.  Indices:
the arity `n ∈ ℕ`; `R ∈ cR[L]^n`; the triples `⟨k, S, i⟩ : Σ k : ℕ, L_c[L]^k × (Fin k → Fin n)`
(a sigma over `ℕ` of products of a countable type and a finite one; `L_c[L]^0` is empty, so only
`k ≥ 1` contributes).  Correspondence with the printed definitions. -/
def determinationClause : baseTemplateLanguage.{u}.Sentenceω :=
  ciInf fun n : ℕ ↦ ciInf fun t : ClassSymbol.{u} (n + 1) ↦
    ciInf fun a : Σ k : ℕ, BaseSymbol.{u} k × (Fin k → Fin (n + 1)) ↦
      ((atomAt (t.toBaseSymbol n.succ_pos) (Fin.castAdd (n + 1)) ⊓
          atomAt (t.toBaseSymbol n.succ_pos) (Fin.natAdd (n + 1))).imp
        ((atomAt a.2.1 (Fin.castAdd (n + 1) ∘ a.2.2)).iff
          (atomAt a.2.1 (Fin.natAdd (n + 1) ∘ a.2.2)))).alls

/-- **Clause (b) of [AFK26, Definition 4.22]**: the three sentences.
Correspondence with the printed definitions. -/
def structureClause : baseTemplateLanguage.{u}.Sentenceω :=
  typingClause ⊓ exclusivityClause ⊓ determinationClause

/-! ### (c) The diagram clauses -/

/-- **Clause (c) of [AFK26, Definition 4.22]**: for `R_t ∈ cR[L]` on `n ≥ 1` points and every pair
`(Q_t(x̄), ψ)` of `ID[L]` with `ψ` an atomic or negated atomic formula of `L_c[L]`,
`∀ x̄, R_t(x̄) → ψ`.  The pairs are those of `templateDiagramPairs`: `ψ = S(x_{i_0}, …)` when
`t.Holds S i` (`mk_atom_mem_templateDiagramPairs_iff`), and `ψ = ¬S(x_{i_0}, …)` otherwise.
Indices: the arity `n ∈ ℕ`; `t ∈ cR[L]^n`; the triples `⟨k, S, i⟩` with, resp. without,
`t.Holds S i` (subtypes of the countable sigma type of `determinationClause`).
Correspondence with the printed definitions. -/
def diagramClause : baseTemplateLanguage.{u}.Sentenceω :=
  ciInf fun n : ℕ ↦ ciInf fun t : ClassSymbol.{u} (n + 1) ↦
    (ciInf fun a : {a : Σ k : ℕ, BaseSymbol.{u} k × (Fin k → Fin (n + 1)) //
        t.1.1.Holds a.2.1.toTemplateSymbol a.2.2} ↦
      ((atomAt (t.toBaseSymbol n.succ_pos) id).imp (atomAt a.1.2.1 a.1.2.2)).alls) ⊓
    ciInf fun a : {a : Σ k : ℕ, BaseSymbol.{u} k × (Fin k → Fin (n + 1)) //
        ¬ t.1.1.Holds a.2.1.toTemplateSymbol a.2.2} ↦
      ((atomAt (t.toBaseSymbol n.succ_pos) id).imp (atomAt a.1.2.1 a.1.2.2).not).alls

/-! ### (d) Density -/

/-- The parameters of clause (d) at the arity `n + 1` with `m` new points: pairs `(t*, t)` with
`R_{t*} ∈ cR[L]^{n+1}`, `R_t ∈ L_c[L]^{n+1+m}`, and `(Q_t(x̄ ȳ), Q_{t*}(x̄)) ∈ ID[L]`, the first
`n + 1` places of `t` carrying `t*` (`satisfiesDensityAt_iff`).  A subtype of a product of
countable types. -/
def DensityIndex (n m : ℕ) : Type (u + 1) :=
  {tt : ClassSymbol.{u} (n + 1) × ClassSymbol.{u} (n + 1 + m) //
    tt.2.1.1.Holds (TemplateSymbol.invariant tt.1.1 n.succ_pos) (Fin.castAdd m)}

instance (n m : ℕ) : Countable (DensityIndex.{u} n m) :=
  inferInstanceAs (Countable (Subtype _))

/-- **Clause (d) of [AFK26, Definition 4.22]**: for every `k ∈ ω` and all `t*, t` with
`R_{t*} ∈ cR[L]`, `R_t ∈ L_c[L]` and `(Q_t(x̄ ȳ), Q_{t*}(x̄)) ∈ ID[L]`,
`∀ x̄, R_{t*}(x̄) → ∃ ȳ ⋁_{s ∈ L, R_s ∈ L_c[L], trunc_k(s) ≅_ren trunc_k(t)} R_s(x̄ ȳ)`.  The donor
`t` has rank `0` (`R_t ∈ L_c[L]`) and any number `m ≥ 0` of new points; the witness `s` is taken
up to renaming of the truncations (`TemplateClass.TruncEquiv k`, raw truncation at the finite
ordinal `k`, not stage reduction).  Indices: the cutoff `k ∈ ℕ`; the arity `n ∈ ℕ`; the number
`m ∈ ℕ` of new points; the pairs `DensityIndex n m`; the witnesses, a subtype of
`cR[L]^{n+1+m}`.  Correspondence with the printed definitions. -/
def densityClause : baseTemplateLanguage.{u}.Sentenceω :=
  ciInf fun k : ℕ ↦ ciInf fun n : ℕ ↦ ciInf fun m : ℕ ↦ ciInf fun tt : DensityIndex.{u} n m ↦
    ((atomAt (tt.1.1.toBaseSymbol n.succ_pos) id).imp (existsBlock
      (ciSup fun s : {s : ClassSymbol.{u} (n + 1 + m) // s.1.1.TruncEquiv k tt.1.2.1.1} ↦
        atomAt (s.1.toBaseSymbol (Nat.lt_add_right m n.succ_pos)) id))).alls

/-! ### The sentence -/

/-- **The sentence `σ[L]`** [AFK26, Definition 4.22], for the template system `L` of legal
templates: the countable conjunction of clauses (a) `⋀ ThPlan` (`planClause`, with (Singletons)),
(b) `structureClause`, (c) `diagramClause` and (d) `densityClause`, over the base sublanguage
`L_c[L]` (`baseTemplateLanguage`).  Defined syntactically, not by the existence of a lift.
Correspondence with the printed definitions. -/
def templateSentence : baseTemplateLanguage.{u}.Sentenceω :=
  planClause ⊓ structureClause ⊓ diagramClause ⊓ densityClause

end

end VaughtConjecture
