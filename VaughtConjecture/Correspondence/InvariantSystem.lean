/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Complexity
import VaughtConjecture.Correspondence.StageIndexing
import VaughtConjecture.Extension.FamilyCofaces
import VaughtConjecture.Realization.Closure
import VaughtConjecture.Realization.Partial

/-!
# Invariance diagrams and invariant systems

Roadmap, "Manuscript correspondence (required)", item 2; concordance rows 14 and 29.

**The printed definitions, clause by clause.**  The definitions of [AFK26, §2.1–2.2] are stated
here with one field for each printed clause.

* The setting [AFK26, Convention 2.3, with the conventions of §1.4: relational languages, every
  relation of positive arity, countable structures] is `GeometrySignature`: the symbols `P_n` of
  `L_a` (`closed`), the invariants `L_b` (`IsInvariant`), and `L_c`, the other symbols, with the
  clauses `L_a ⊆ L_c`, `|L_b^n| > 0` for `n ≥ 1`, and `|L_c^n| ≤ ω`; `L_b ∩ L_c = ∅` and
  `L = L_a ∪ L_b ∪ L_c` hold by the definition of `L_c` as the complement of `L_b`.
* The theory `Th_Geo` [AFK26, Definition 2.1] is `IsGeometry` (its first clause has two sentences,
  `injective` and `perm`, then `exists_closed` and `inter`), and `Th_StrGeo`
  [AFK26, Definition 2.2] is `IsStructuredGeometry` (clauses (a)–(d)).  Each sentence is stated by
  its satisfaction in a structure; clause (b) is a disjunction over `L_b^n`, which here has `ℵ₁`
  members.
* An invariance diagram [AFK26, Definition 2.4] is `InvarianceDiagram`.  A pair
  `(P(x₀, …, x_{n-1}), ψ)` is `⟨n, P, ψ⟩` with `ψ : L.Formula (Fin n)` (`DiagramPair`): the
  printed condition that the variables of `ψ` are among the `x_i` is the type of `ψ`.  The fields
  are the three clauses: `mem_pairs`, `exactlyOne`, and `realized`, in which the structure is
  countable, as are all structures of [AFK26].
* A structure compatible with a diagram [AFK26, Definition 2.5] is
  `InvarianceDiagram.IsCompatible`, with its two clauses.
* An invariant system [AFK26, Definition 2.6] is `InvariantSystem`: the type of the field `τ`
  is clauses (a) and (b) (`τ_β` maps `L_b^n` to `L_b^n`; it is read only at `β < ω₁`), and the
  fields `comp`, `countable`, `ne_univ`, and `exists_fixed` are clauses (c), (d)(i), (d)(ii),
  and (d)(iii).
* The compatibility of a diagram and a system [AFK26, Definition 2.8] is
  `InvarianceDiagram.IsCompatibleWith`, with its two clauses.

**The instance of the stage types.**  The invariance language `invariantLanguage` has the symbols
`P_n`, an invariant `Q_p` for each legal stage type `p` at stage `ω₁` (labels below `ω₁`, `-∞`,
or `∞`), and a base relation for each relation symbol of the base language, a legal stage type at
stage `ω` (`InvariantSymbol`); `stageSignature` satisfies the clauses of the setting, with a legal
stage type on every number of points (`exists_isLegal`, from the complete interval scheme
`intervalScheme`).  The invariance diagram of the stage types (`stageDiagram`) pairs `Q_p(x)` with
the literals of `p` (`Literal`): `R(x_j)` when `R` holds in `p` along `j`
(`InvariantSymbol.HoldsIn`: the places are distinct and span a closed face, which is the type `q`
for `R = Q_q` and reduces at stage `ω` to the type of a base relation `R`), and `¬R(x_j)`
otherwise.  The invariant systems are
the projections along a stage function (`reductionSystem`): `τ_β` is the projection
(`StageType.project`) to the stage `f β`, the reduction of the labels to `f β`.

* `stageDiagram` satisfies the three clauses of [AFK26, Definition 2.4]; the third holds in the
  face realization of `p` (`StageType.faceRealization`).
* The structure of a realization at stage `ω₁` (`Realization.toInvariantStructure`) is compatible
  with `stageDiagram` when the realization is exactly consistent, covering, and has legal types
  (`Realization.isCompatible_toInvariantStructure`); its base relations are those of the
  structure, in the base language, of its reduction to `ω` (`Realization.relMap_base_iff`).
  Conversely every compatible structure is the structure of exactly one such realization
  (`isCompatible_iff_exists_toInvariantStructure_eq`), by the mutually inverse maps
  `Realization.toInvariantStructure` and `invariantLanguage.toRealization`
  (`invariantLanguage.toInvariantStructure_toRealization`,
  `toRealization_toInvariantStructure`): a compatible structure is determined by its invariants
  (`structure_eq_of_isCompatible`).  No clause of the diagram asks for a nonempty carrier: the
  empty structure is the structure of the realization on the empty carrier.
* **Closed tuples are supported tuples** [AFK26, Definition 2.1]: `P_n` holds of a tuple of the
  structure of a realization exactly when the tuple is injective and its set of points is a
  support (`Realization.relMap_closed_iff_isSupport`), equivalently a finite closed set of the
  canonical closure (`Realization.relMap_closed_iff_isClosed`).
* `blockSystem`, the projections to the block stages `λ_ξ`, and `omega0MulSystem`, the projections
  to the printed stages `ω · β`, are invariant systems, and `omega0MulSystem.τ (1 + ξ)` is
  `blockSystem.τ ξ` (`omega0MulSystem_τ_one_add`).  `blockSystem` is compatible with
  `stageDiagram` (`isCompatibleWith_blockSystem`), and `omega0MulSystem` is not
  (`not_isCompatibleWith_omega0MulSystem`): its projection of index `0`, to the stage `0`, changes
  the base relation of a legal one-point type with label `1`.

**Departures.**

* The invariants are legal stage types, with fixed coded rows and a separate labelling, in place
  of the templates of [AFK26, Definition 4.6] (concordance row 9).
* The invariance diagram of the templates is not printed (the body of [AFK26, Definition 4.17] is
  that of the diagram of trees, [AFK26, Definition 3.6], with a note that it is to be defined);
  `stageDiagram` is the diagram supplied here.
* The language `L_c` of [AFK26, Definition 4.16] is printed as the symbols of the invariants fixed
  by `τ_ω`; here the base relations are the legal stage types at stage `ω`, the invariants fixed
  by `τ_1` in the printed indexing (by `τ_0` in the block indexing), as in the proof of
  [AFK26, Lemma 4.21].
* The printed compatibility of the diagram of the templates with the printed projections
  [AFK26, Lemma 4.18] fails at the printed index `0` for the stage types
  (`not_isCompatibleWith_omega0MulSystem`); it holds with the block indexing
  (`isCompatibleWith_blockSystem`), which is the printed indexing shifted by one at finite indices
  (`VaughtConjecture.Correspondence.StageIndexing`).
* The fact after [AFK26, Definition 2.8] that projections preserve compatibility
  [AFK26, Lemma 2.9] is not compiled here.

## Placement

The concordance rows and their notes are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".

## References

[AFK26] is the draft *A counterexample to Vaught's Conjecture for `L_{ω₁ω}`* (2026), recorded in
`roadmap/REFERENCES.bib`.
-/

universe u v w w'

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal Order

/-! ### The setting -/

/-- **The signature of a structured geometry** [AFK26, Convention 2.3]: a relational language
`L = L_a ∪ L_b ∪ L_c` whose relation symbols have positive arity, with one symbol `P_n` of each
arity `n ≥ 1` (the language `L_a` of the geometry, `closed`), a set `L_b` of symbols, the
**invariants** (`IsInvariant`), with at least one of each arity `n ≥ 1`, and the remaining
symbols `L_c`, countably many of each arity, among them those of `L_a`. -/
structure GeometrySignature (L : Language.{w, w'}) where
  /-- The symbol `P_n` of the geometry, of arity `n ≥ 1`. -/
  closed (n : ℕ) (hn : 0 < n) : L.Relations n
  /-- A symbol is an invariant: it lies in `L_b`. -/
  IsInvariant ⦃n : ℕ⦄ : L.Relations n → Prop
  /-- The language is relational. -/
  isEmpty_functions (n : ℕ) : IsEmpty (L.Functions n)
  /-- Every relation symbol has positive arity. -/
  pos_of_relations ⦃n : ℕ⦄ : L.Relations n → 0 < n
  /-- `L_a ⊆ L_c`: the symbols of the geometry are not invariants. -/
  not_isInvariant_closed (n : ℕ) (hn : 0 < n) : ¬ IsInvariant (closed n hn)
  /-- `|L_b^n| > 0` for `n ≥ 1`. -/
  exists_isInvariant (n : ℕ) (hn : 0 < n) : ∃ Q : L.Relations n, IsInvariant Q
  /-- `|L_c^n| ≤ ω`. -/
  countable_setOf_not_isInvariant (n : ℕ) : {R : L.Relations n | ¬ IsInvariant R}.Countable

variable {L : Language.{w, w'}} (σ : GeometrySignature L)

namespace GeometrySignature

/-- The invariants of arity `n`, `L_b^n`. -/
abbrev Invariant (n : ℕ) : Type w' := {Q : L.Relations n // σ.IsInvariant Q}

end GeometrySignature

/-! ### Geometries and structured geometries -/

section Structures

variable (M : Type*) [L.Structure M]

/-- **A structure with an `L_a`-geometry** [AFK26, Definition 2.1]: the structure satisfies the
theory `Th_Geo[L_a]`, each of whose clauses is stated here by its satisfaction. -/
structure IsGeometry : Prop where
  /-- First clause, first sentence: `P_n` holds only of tuples of distinct points. -/
  injective ⦃n : ℕ⦄ (hn : 0 < n) (x : Fin n → M) :
    RelMap (σ.closed n hn) x → Function.Injective x
  /-- First clause, second sentence: `P_n` is invariant under permutations of its places. -/
  perm ⦃n : ℕ⦄ (hn : 0 < n) (x : Fin n → M) (e : Equiv.Perm (Fin n)) :
    RelMap (σ.closed n hn) x ↔ RelMap (σ.closed n hn) (x ∘ e)
  /-- Second clause: every tuple of `n ≥ 1` distinct points extends, by `k ∈ ω` further points, to
  a tuple satisfying `P_{n+k}`. -/
  exists_closed ⦃n : ℕ⦄ (hn : 0 < n) (x : Fin n → M) : Function.Injective x →
    ∃ (k : ℕ) (y : Fin (n + k) → M), y ∘ Fin.castAdd k = x ∧
      RelMap (σ.closed (n + k) (Nat.lt_add_right k hn)) y
  /-- Third clause: if `P_{n₀}(x)` and `P_{n₁}(y)`, then every enumeration `z` of the `k ≥ 1`
  common points of `x` and `y` satisfies `P_k`. -/
  inter ⦃n₀ n₁ k : ℕ⦄ (h₀ : 0 < n₀) (h₁ : 0 < n₁) (hk : 0 < k) (x : Fin n₀ → M) (y : Fin n₁ → M)
    (z : Fin k → M) : RelMap (σ.closed n₀ h₀) x → RelMap (σ.closed n₁ h₁) y →
    Function.Injective z → Set.range z = Set.range x ∩ Set.range y → RelMap (σ.closed k hk) z

/-- **A structure with an `(L_a, L_b, L_c)`-structured geometry** [AFK26, Definition 2.2]: the
structure satisfies the theory `Th_StrGeo`, each of whose clauses is stated here by its
satisfaction (clause (b) is a disjunction over `L_b^n`, which is not a formula of `L_{ω₁,ω}` when
`L_b^n` is uncountable). -/
structure IsStructuredGeometry : Prop where
  /-- (a) The structure has an `L_a`-geometry. -/
  isGeometry : IsGeometry σ M
  /-- (b) `P_n(x)` holds exactly when some invariant of arity `n` holds of `x`. -/
  closed_iff ⦃n : ℕ⦄ (hn : 0 < n) (x : Fin n → M) :
    RelMap (σ.closed n hn) x ↔ ∃ Q : L.Relations n, σ.IsInvariant Q ∧ RelMap Q x
  /-- (c) Distinct invariants of the same arity hold of no common tuple. -/
  exclusive ⦃n : ℕ⦄ (Q Q' : L.Relations n) : σ.IsInvariant Q → σ.IsInvariant Q' → Q ≠ Q' →
    ∀ x : Fin n → M, RelMap Q x → ¬ RelMap Q' x
  /-- (d) Two tuples with the same invariant `Q` satisfy the same relations `R ∈ L_b ∪ L_c` along
  every sequence `i` of their places. -/
  determines ⦃n k : ℕ⦄ (Q : L.Relations n) (R : L.Relations k) (i : Fin k → Fin n) :
    σ.IsInvariant Q → ∀ x y : Fin n → M, RelMap Q x → RelMap Q y →
      (RelMap R (x ∘ i) ↔ RelMap R (y ∘ i))

end Structures

/-! ### Invariance diagrams -/

variable (L) in
/-- A **pair of formulas** `(P(x₀, …, x_{n-1}), ψ)` of an invariance diagram: the first formula is
the symbol `P` of arity `n` applied to the distinct variables `x₀, …, x_{n-1}`, and the free
variables of the second are among them. -/
abbrev DiagramPair : Type (max w w') := Σ n : ℕ, L.Relations n × L.Formula (Fin n)

/-- The atomic formula `R(x_{j₀}, …, x_{j_{k-1}})`. -/
def atom {n k : ℕ} (R : L.Relations k) (j : Fin k → Fin n) : L.Formula (Fin n) :=
  R.formula fun i ↦ Term.var (j i)

/-- A structure **satisfies a set of pairs** `(P(x), ψ)` when `∀ x, P(x) → ψ` holds in it for every
pair: the third item of the third clause of [AFK26, Definition 2.4] and the second clause of
[AFK26, Definition 2.5]. -/
def SatisfiesPairs (D : Set (DiagramPair L)) (M : Type*) [L.Structure M] : Prop :=
  ∀ π ∈ D, ∀ x : Fin π.1 → M, RelMap π.2.1 x → π.2.2.Realize x

/-- **An invariance diagram** [AFK26, Definition 2.4]: a set of pairs of formulas, one field for
each clause. -/
structure InvarianceDiagram where
  /-- The pairs of formulas. -/
  pairs : Set (DiagramPair L)
  /-- First clause: in a pair `(P(x), ψ)`, `P ∈ L_b` and `ψ` is an atomic formula or the negation
  of one (its variables are among `x` by the type of `ψ`). -/
  mem_pairs : ∀ π ∈ pairs, σ.IsInvariant π.2.1 ∧
    (π.2.2.IsAtomic ∨ ∃ θ : L.Formula (Fin π.1), θ.IsAtomic ∧ π.2.2 = θ.not)
  /-- Second clause: for every `P ∈ L_b^n`, `R ∈ L^k`, and sequence `j` of places, exactly one of
  `(P(x), R(x_j))` and `(P(x), ¬R(x_j))` is a pair. -/
  exactlyOne ⦃n k : ℕ⦄ (P : L.Relations n) (R : L.Relations k) (j : Fin k → Fin n) :
    σ.IsInvariant P → Xor (⟨n, P, atom R j⟩ ∈ pairs) (⟨n, P, (atom R j).not⟩ ∈ pairs)
  /-- Third clause: every invariant `Q` is realized in a (countable) structure with a structured
  geometry that satisfies the pairs. -/
  realized ⦃n : ℕ⦄ (Q : L.Relations n) : σ.IsInvariant Q →
    ∃ (M : Type) (_ : L.Structure M), Countable M ∧ IsStructuredGeometry σ M ∧
      (∃ x : Fin n → M, RelMap Q x) ∧ SatisfiesPairs pairs M

variable {σ}

/-- **A structure compatible with an invariance diagram** [AFK26, Definition 2.5], one field for
each clause. -/
structure InvarianceDiagram.IsCompatible (D : InvarianceDiagram σ) (M : Type*) [L.Structure M] :
    Prop where
  /-- The structure has a structured geometry. -/
  isStructuredGeometry : IsStructuredGeometry σ M
  /-- The structure satisfies every pair of the diagram. -/
  satisfiesPairs : SatisfiesPairs D.pairs M

/-! ### Invariant systems -/

variable (σ) in
/-- **An invariant system** on `L_b` [AFK26, Definition 2.6]: maps `τ_β` of the invariants indexed
by the countable ordinals `β`, one field for each clause. -/
structure InvariantSystem where
  /-- (a) and (b): `τ_β` maps `L_b^n` to `L_b^n` (it is read only at `β < ω₁`). -/
  τ (β : Ordinal.{u}) ⦃n : ℕ⦄ : σ.Invariant n → σ.Invariant n
  /-- (c) For `α ≤ β < ω₁`, `τ_α ∘ τ_β = τ_β ∘ τ_α = τ_α`. -/
  comp ⦃α β : Ordinal.{u}⦄ (hαβ : α ≤ β) (hβ : β < ω₁) ⦃n : ℕ⦄ (Q : σ.Invariant n) :
    τ α (τ β Q) = τ α Q ∧ τ β (τ α Q) = τ α Q
  /-- (d)(i) Countably many `β`-invariants, the invariants fixed by `τ_β`. -/
  countable ⦃β : Ordinal.{u}⦄ (hβ : β < ω₁) :
    {Q : Σ n, σ.Invariant n | τ β Q.2 = Q.2}.Countable
  /-- (d)(ii) Not every invariant is a `β`-invariant. -/
  ne_univ ⦃β : Ordinal.{u}⦄ (hβ : β < ω₁) : {Q : Σ n, σ.Invariant n | τ β Q.2 = Q.2} ≠ Set.univ
  /-- (d)(iii) Every invariant is a `β`-invariant for some countable `β`. -/
  exists_fixed ⦃n : ℕ⦄ (Q : σ.Invariant n) : ∃ β < ω₁, τ β Q = Q

/-- **An invariance diagram and an invariant system are compatible** [AFK26, Definition 2.8], one
field for each clause. -/
structure InvarianceDiagram.IsCompatibleWith (D : InvarianceDiagram σ)
    (S : InvariantSystem.{u} σ) : Prop where
  /-- First clause: a pair `(P(x), Q(x_j))` of invariants is carried by `τ_β` to a pair. -/
  invariant ⦃β : Ordinal.{u}⦄ (hβ : β < ω₁) ⦃n k : ℕ⦄ (P : σ.Invariant n) (Q : σ.Invariant k)
    (j : Fin k → Fin n) : ⟨n, P.1, atom Q.1 j⟩ ∈ D.pairs →
      ⟨n, (S.τ β P).1, atom (S.τ β Q).1 j⟩ ∈ D.pairs
  /-- Second clause: for `P ∈ L_b` and `R ∈ L_c`, `(P(x), R(x_j))` is a pair exactly when
  `(τ_β(P)(x), R(x_j))` is. -/
  base ⦃β : Ordinal.{u}⦄ (hβ : β < ω₁) ⦃n k : ℕ⦄ (P : σ.Invariant n) (R : L.Relations k)
    (j : Fin k → Fin n) : ¬ σ.IsInvariant R →
    (⟨n, P.1, atom R j⟩ ∈ D.pairs ↔ ⟨n, (S.τ β P).1, atom R j⟩ ∈ D.pairs)

/-! ### A legal stage type on every number of points -/

open Finset in
/-- The graded faces of the interval plan on `Fin n`. -/
noncomputable def intervalGradedFaces (n : ℕ) : Finset (Finset (Fin n) × ℕ) :=
  {X ∈ Geometry.intervalPlan univ ×ˢ range (n + 1) | 0 < X.2 ∧ X.2 ≤ #X.1}

open Finset in
/-- The **complete interval scheme** on `n` points: the interval plan on `Fin n`, one cell for each
of its graded faces, and the bottom rows. -/
noncomputable def intervalScheme (n : ℕ) : Scheme.{u} n where
  card := #(intervalGradedFaces n)
  toCellScheme := ⟨univ, Geometry.intervalPlan univ,
    fun d ↦ ((intervalGradedFaces n).equivFin.symm d).1.1,
    fun d ↦ ((intervalGradedFaces n).equivFin.symm d).1.2⟩
  rows := CellScheme.Rows.bot _

open Finset in
/-- **The complete interval scheme is legal**: the bottom rows are consistent and bountiful, and
every graded face is the graded index of a cell. -/
theorem isLegal_intervalScheme (n : ℕ) : (intervalScheme.{u} n).IsLegal where
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ by
    have h := ((intervalGradedFaces n).equivFin.symm d).2
    simp only [intervalGradedFaces, mem_filter, mem_product] at h
    exact ⟨h.1.1, h.2⟩⟩⟩
  isCoded _ _ := WithBot.bot_lt_coe _
  isConsistent := CellScheme.Rows.isConsistent_bot
  isBountiful := CellScheme.Rows.isBountiful_bot
  isComplete X hX := by
    have hX' : X ∈ intervalGradedFaces n := by
      obtain ⟨h₁, h₂, h₃⟩ := hX
      simp only [intervalGradedFaces, mem_filter, mem_product, mem_range]
      exact ⟨⟨h₁, Nat.lt_succ_of_le (h₃.trans ((card_le_univ _).trans_eq (by simp)))⟩, h₂, h₃⟩
    exact ⟨(intervalGradedFaces n).equivFin ⟨X, hX'⟩, by
      simp [CellScheme.gradedIndex, intervalScheme]⟩

/-- **A legal stage type on every number of points**, at every stage: the complete interval
scheme with every label bottom. -/
theorem exists_isLegal (α : Ordinal.{u}) (n : ℕ) : ∃ p : StageType.{u} α n, p.IsLegal :=
  ⟨(isLegal_intervalScheme n).toStageType α, (isLegal_intervalScheme n).isLegal_toStageType α⟩

/-! ### The invariance language of the stage types -/

/-- The relation symbols with `n` places of the invariance language of the stage types: the
symbol `P_n` of the geometry (`closed`), an invariant for each legal stage type at stage `ω₁`
(`invariant`), and a base relation for each relation symbol of the base language, a legal stage
type at stage `ω` (`base`). -/
inductive InvariantSymbol (n : ℕ) : Type (u + 1)
  /-- The symbol `P_n` of the geometry. -/
  | closed : InvariantSymbol n
  /-- The invariant of a legal stage type at stage `ω₁`. -/
  | invariant (p : StageType.{u} ω₁ n) (hp : p.IsLegal) : InvariantSymbol n
  /-- The base relation of a relation symbol of the base language. -/
  | base (r : baseLanguage.{u}.Relations n) : InvariantSymbol n

namespace InvariantSymbol

variable {n k : ℕ}

/-- A symbol is an **invariant** when it is the invariant of a legal stage type. -/
def IsInvariant : InvariantSymbol.{u} n → Prop
  | invariant _ _ => True
  | _ => False

/-- The symbol `s` **holds at** the evaluation `e` of a tuple: `P_n` when the tuple is typed, the
invariant of `p` when its type is `p`, and the base relation of `r` when its type reduces at
stage `ω` to the stage type of `r`. -/
def HoldsAt : InvariantSymbol.{u} n → Option (StageType.{u} ω₁ n) → Prop
  | closed, e => e.isSome
  | invariant p _, e => e = some p
  | base r, e =>
    e.map (StageType.reduce · isSuccLimit_omega0.isSuccPrelimit) = some (baseLanguage.type r)

/-- The symbol `s` **holds in the type `p` along the places `j`**: the places are distinct and
`s` holds at the face of `p` they span. -/
def HoldsIn (s : InvariantSymbol.{u} k) (p : StageType.{u} ω₁ n) (j : Fin k → Fin n) : Prop :=
  ∃ h : Function.Injective j, s.HoldsAt (StageType.restrictFace ⟨j, h⟩ p)

end InvariantSymbol

/-- The **invariance language of the stage types**: the relational language with the symbols
`InvariantSymbol n` of positive arity `n`. -/
def invariantLanguage : Language.{0, u + 1} where
  Functions _ := Empty
  Relations n := {_s : InvariantSymbol.{u} n // 0 < n}

/-- **The signature of the stage types** [AFK26, Convention 2.3]: `L_a` the symbols `P_n`, `L_b`
the invariants of the legal stage types at stage `ω₁`, and `L_c` the symbols `P_n` with the base
relations. -/
def stageSignature : GeometrySignature invariantLanguage.{u} where
  closed n hn := ⟨.closed, hn⟩
  IsInvariant _ R := R.1.IsInvariant
  isEmpty_functions _ := inferInstanceAs (IsEmpty Empty)
  pos_of_relations _ s := s.2
  not_isInvariant_closed _ _ := id
  exists_isInvariant n hn := by
    obtain ⟨p, hp⟩ := exists_isLegal ω₁ n
    exact ⟨⟨.invariant p hp, hn⟩, trivial⟩
  countable_setOf_not_isInvariant n := by
    let g : {x : Option (baseLanguage.{u}.Relations n) // 0 < n} → invariantLanguage.{u}.Relations n
      | ⟨none, h⟩ => ⟨.closed, h⟩
      | ⟨some r, h⟩ => ⟨.base r, h⟩
    refine (Set.countable_range g).mono ?_
    rintro ⟨s, hn⟩ hs
    cases s with
    | closed => exact ⟨⟨none, hn⟩, rfl⟩
    | invariant p hp => exact absurd trivial hs
    | base r => exact ⟨⟨some r, hn⟩, rfl⟩

/-- An invariant of the signature of the stage types is the invariant of a legal stage type. -/
theorem stageSignature.exists_eq_invariant {n : ℕ} (Q : stageSignature.{u}.Invariant n) :
    ∃ (p : StageType.{u} ω₁ n) (hp : p.IsLegal) (hn : 0 < n),
      Q = ⟨⟨.invariant p hp, hn⟩, trivial⟩ := by
  obtain ⟨⟨s, hn⟩, hs⟩ := Q
  cases s with
  | invariant p hp => exact ⟨p, hp, hn, rfl⟩
  | closed => exact absurd hs id
  | base r => exact absurd hs id

/-! ### The invariance diagram of the stage types -/

/-- The place named by a term in the variables `x₀, …, x_{n-1}` (the language has no function
symbols, and a formula has no bound variables). -/
def termIndex {n : ℕ} : invariantLanguage.{u}.Term (Fin n ⊕ Fin 0) → Fin n
  | .var (.inl i) => i
  | .var (.inr i) => i.elim0
  | .func f _ => (f : Empty).elim

/-- A term in the variables names a place: its value is the point at that place. -/
theorem realize_termIndex {M : Type*} [invariantLanguage.{u}.Structure M] {n : ℕ}
    (x : Fin n → M) (v : Fin 0 → M) (t : invariantLanguage.{u}.Term (Fin n ⊕ Fin 0)) :
    t.realize (Sum.elim x v) = x (termIndex t) := by
  match t with
  | .var (.inl i) => rfl
  | .var (.inr i) => exact i.elim0
  | .func f _ => exact (f : Empty).elim

/-- The **literals of a type**: the atomic formulas `R(x_j)` holding in the type `p` and the
negations of those that do not. -/
def Literal {n : ℕ} (p : StageType.{u} ω₁ n) :
    invariantLanguage.{u}.Formula (Fin n) → Prop
  | .rel R ts => R.1.HoldsIn p (termIndex ∘ ts)
  | .imp (.rel R ts) .falsum => ¬ R.1.HoldsIn p (termIndex ∘ ts)
  | _ => False

/-- The pairs of the invariance diagram of the stage types: `(Q_p(x), ψ)` with `ψ` a literal of
the legal stage type `p`. -/
def IsStagePair : DiagramPair invariantLanguage.{u} → Prop
  | ⟨_, ⟨⟨.invariant p _, _⟩, ψ⟩⟩ => Literal p ψ
  | _ => False

/-- A pair `(Q_p(x), R(x_j))` belongs to the invariance diagram of the stage types exactly when
`R` holds in `p` along `j`. -/
theorem isStagePair_atom_iff {n k : ℕ} (p : StageType.{u} ω₁ n) (hp : p.IsLegal) (hn : 0 < n)
    (R : invariantLanguage.{u}.Relations k) (j : Fin k → Fin n) :
    IsStagePair ⟨n, ⟨.invariant p hp, hn⟩, atom R j⟩ ↔ R.1.HoldsIn p j :=
  Iff.rfl

/-- A pair `(Q_p(x), ¬R(x_j))` belongs to the invariance diagram of the stage types exactly when
`R` does not hold in `p` along `j`. -/
theorem isStagePair_not_atom_iff {n k : ℕ} (p : StageType.{u} ω₁ n) (hp : p.IsLegal) (hn : 0 < n)
    (R : invariantLanguage.{u}.Relations k) (j : Fin k → Fin n) :
    IsStagePair ⟨n, ⟨.invariant p hp, hn⟩, (atom R j).not⟩ ↔ ¬ R.1.HoldsIn p j :=
  Iff.rfl

/-- The first two clauses of [AFK26, Definition 2.4] for the pairs of the stage types: every pair
has an invariant as first formula and a literal as second. -/
theorem isStagePair_mem {π : DiagramPair invariantLanguage.{u}} (h : IsStagePair π) :
    stageSignature.IsInvariant π.2.1 ∧ (π.2.2.IsAtomic ∨
      ∃ θ : invariantLanguage.{u}.Formula (Fin π.1), θ.IsAtomic ∧ π.2.2 = θ.not) := by
  obtain ⟨n, ⟨⟨s, hn⟩, ψ⟩⟩ := π
  cases s with
  | closed => exact h.elim
  | base r => exact h.elim
  | invariant p hp =>
    refine ⟨trivial, ?_⟩
    cases ψ with
    | rel R ts => exact .inl (.rel R ts)
    | imp φ χ =>
      cases φ with
      | rel R ts => cases χ <;> first | exact .inr ⟨_, .rel R ts, rfl⟩ | exact h.elim
      | _ => exact h.elim
    | _ => exact h.elim

/-! ### The structure of a realization -/

end VaughtConjecture.Correspondence

namespace VaughtConjecture.Realization

open Correspondence Finset FirstOrder Language Structure Ordinal

variable {M : Type v} (R : Realization.{u, v} ω₁ M) {n k : ℕ}

/-- The **structure of a realization** at stage `ω₁` in the invariance language: a symbol holds
of a tuple of distinct points when it holds at the evaluation of the tuple.  So `P_n` holds of the
typed tuples, the invariant of `p` of the tuples of type `p`, and the base relations are those of
the structure of the reduction of the realization to stage `ω` (`relMap_base_iff`). -/
@[instance_reducible] def toInvariantStructure : invariantLanguage.{u}.Structure M where
  funMap f := (f : Empty).elim
  RelMap s xs := ∃ h : Function.Injective xs, s.1.HoldsAt (R.eval ⟨xs, h⟩)

/-- A symbol holds in the structure of a realization exactly when the tuple is injective and the
symbol holds at its evaluation. -/
theorem relMap_toInvariantStructure (s : invariantLanguage.{u}.Relations n) (xs : Fin n → M) :
    @RelMap _ M R.toInvariantStructure n s xs ↔
      ∃ h : Function.Injective xs, s.1.HoldsAt (R.eval ⟨xs, h⟩) :=
  Iff.rfl

/-- **The base relations are those of the base structure of the reduction to `ω`**: the base
relation of `r` holds in the structure of `R` exactly when `r` holds in the structure, in the
base language, of the reduction of `R` to stage `ω`. -/
theorem relMap_base_iff (r : baseLanguage.{u}.Relations n) (hn : 0 < n) (xs : Fin n → M) :
    @RelMap _ M R.toInvariantStructure n ⟨.base r, hn⟩ xs ↔
      @RelMap _ M (R.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure n r xs :=
  Iff.rfl

/-- **The literals of a typed tuple are those of its type**: if `t` has type `p` in an exactly
consistent realization, a symbol holds of `t ∘ j` exactly when it holds in `p` along `j`. -/
theorem relMap_comp_iff (hR : R.IsConsistent) {t : Fin n ↪ M} {p : StageType.{u} ω₁ n}
    (ht : R.eval t = some p) (s : invariantLanguage.{u}.Relations k) (j : Fin k → Fin n) :
    @RelMap _ M R.toInvariantStructure k s (t ∘ j) ↔ s.1.HoldsIn p j := by
  refine ⟨fun ⟨h, hs⟩ ↦ ⟨h.of_comp, ?_⟩, fun ⟨h, hs⟩ ↦ ⟨t.injective.comp h, ?_⟩⟩
  · have he : R.eval ⟨t ∘ j, h⟩ = StageType.restrictFace ⟨j, h.of_comp⟩ p :=
      hR t p ⟨j, h.of_comp⟩ ht
    rwa [he] at hs
  · have he : R.eval ⟨t ∘ j, t.injective.comp h⟩ = StageType.restrictFace ⟨j, h⟩ p :=
      hR t p ⟨j, h⟩ ht
    rwa [he]

/-- **The supports of an exactly consistent covering realization are closed under
intersection.** -/
theorem isSupport_inter [DecidableEq M] (hR : R.IsConsistent) (hc : R.IsCovering)
    {S T : Finset M} (hS : R.IsSupport S) (hT : R.IsSupport T) : R.IsSupport (S ∩ T) := by
  rw [← finiteHull_eq_self_iff hR hc]
  refine Subset.antisymm (subset_inter ?_ ?_) (subset_finiteHull _)
  · exact finiteHull_subset_of_isSupport hR hc hS inter_subset_left
  · exact finiteHull_subset_of_isSupport hR hc hT inter_subset_right

/-- **Closed tuples are the enumerations of supports** [AFK26, Definition 2.1]: the symbol `P_n`
holds of a tuple in the structure of an exactly consistent realization exactly when the tuple is
injective and its set of points is a support. -/
theorem relMap_closed_iff_isSupport (hR : R.IsConsistent) (hn : 0 < n) (x : Fin n → M) :
    @RelMap _ M R.toInvariantStructure n (stageSignature.closed n hn) x ↔
      ∃ h : Function.Injective x, R.IsSupport (univ.map ⟨x, h⟩) :=
  exists_congr fun h ↦ isSome_eval_iff_isSupport hR ⟨x, h⟩

/-- **Closed tuples are the enumerations of finite closed sets**: the symbol `P_n` holds of a tuple
in the structure of an exactly consistent covering realization exactly when the tuple is injective
and its set of points is closed for the canonical closure. -/
theorem relMap_closed_iff_isClosed (hR : R.IsConsistent) (hc : R.IsCovering) (hn : 0 < n)
    (x : Fin n → M) :
    @RelMap _ M R.toInvariantStructure n (stageSignature.closed n hn) x ↔
      Function.Injective x ∧ (R.closure hR hc).IsClosed (Set.range x) := by
  rw [relMap_closed_iff_isSupport R hR hn]
  refine ⟨fun ⟨h, hS⟩ ↦ ⟨h, ?_⟩, fun ⟨h, hS⟩ ↦ ⟨h, ?_⟩⟩
  · rw [← isClosed_coe_iff hR hc] at hS
    simpa using hS
  · rw [← isClosed_coe_iff hR hc]
    simpa using hS

/-- **The structure of a realization has an `L_a`-geometry** [AFK26, Definition 2.1], under exact
consistency and covering. -/
theorem isGeometry_toInvariantStructure (hR : R.IsConsistent) (hc : R.IsCovering) :
    @IsGeometry _ stageSignature.{u} M R.toInvariantStructure := by
  let := R.toInvariantStructure
  classical
  refine ⟨fun _ _ _ ⟨h, _⟩ ↦ h, fun n hn x e ↦ ?_, fun n hn x hx ↦ ?_, ?_⟩
  · have key (x : Fin n → M) (e : Equiv.Perm (Fin n)) :
        RelMap (stageSignature.closed n hn) x → RelMap (stageSignature.closed n hn) (x ∘ e) :=
      fun ⟨h, hs⟩ ↦ ⟨h.comp e.injective, by
        have he := isSome_eval_equiv_trans hR ⟨x, h⟩ e
        exact he.trans hs⟩
    refine ⟨key x e, fun h ↦ ?_⟩
    have := key _ e.symm h
    rwa [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at this
  · obtain ⟨k, u, hu, hs⟩ := hc.exists_castAdd hR ⟨x, hx⟩
    exact ⟨k, u, congrArg DFunLike.coe hu, u.injective, hs⟩
  · intro n₀ n₁ k h₀ h₁ hk x y z hx hy hz hxyz
    rw [relMap_closed_iff_isSupport R hR] at hx hy ⊢
    obtain ⟨hx, hSx⟩ := hx
    obtain ⟨hy, hSy⟩ := hy
    refine ⟨hz, ?_⟩
    convert isSupport_inter R hR hc hSx hSy using 1
    ext a
    have := congrArg (a ∈ ·) hxyz
    simpa using this

/-- **The structure of a realization with legal types has a structured geometry**
[AFK26, Definition 2.2], under exact consistency and covering. -/
theorem isStructuredGeometry_toInvariantStructure (hR : R.IsConsistent) (hc : R.IsCovering)
    (hl : R.HasLegalTypes) :
    @IsStructuredGeometry _ stageSignature.{u} M R.toInvariantStructure := by
  let := R.toInvariantStructure
  refine ⟨isGeometry_toInvariantStructure R hR hc, fun n hn x ↦ ?_, ?_, ?_⟩
  · refine ⟨fun ⟨h, hs⟩ ↦ ?_, fun ⟨⟨s, _⟩, hs, h, he⟩ ↦ ⟨h, ?_⟩⟩
    · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
      exact ⟨⟨.invariant p (hl _ _ hp), hn⟩, trivial, h, hp⟩
    · cases s with
      | invariant p _ => exact Option.isSome_iff_exists.mpr ⟨p, he⟩
      | closed => exact hs.elim
      | base r => exact hs.elim
  · rintro n ⟨s, hn⟩ ⟨s', _⟩ hs hs' hne x ⟨h, he⟩ ⟨h', he'⟩
    cases s with
    | closed => exact hs.elim
    | base r => exact hs.elim
    | invariant p hp =>
      cases s' with
      | closed => exact hs'.elim
      | base r => exact hs'.elim
      | invariant p' hp' =>
        obtain rfl : p = p' := Option.some_injective _ (he.symm.trans he')
        exact hne rfl
  · rintro n k ⟨s, hn⟩ S i hs x y ⟨hx, hex⟩ ⟨hy, hey⟩
    cases s with
    | closed => exact hs.elim
    | base r => exact hs.elim
    | invariant p hp =>
      change RelMap S (⇑(⟨x, hx⟩ : Fin n ↪ M) ∘ i) ↔ RelMap S (⇑(⟨y, hy⟩ : Fin n ↪ M) ∘ i)
      rw [relMap_comp_iff R hR hex, relMap_comp_iff R hR hey]

/-- An atomic formula `S(t)` holds of a tuple of type `p` exactly when `S` holds in `p` along the
places named by `t`. -/
theorem realize_rel_iff (hR : R.IsConsistent) {t : Fin n ↪ M} {p : StageType.{u} ω₁ n}
    (ht : R.eval t = some p) {l : ℕ} (S : invariantLanguage.{u}.Relations l)
    (ts : Fin l → invariantLanguage.{u}.Term (Fin n ⊕ Fin 0)) :
    @Formula.Realize _ M R.toInvariantStructure _ (BoundedFormula.rel S ts) t ↔
      S.1.HoldsIn p (termIndex ∘ ts) := by
  let := R.toInvariantStructure
  rw [← relMap_comp_iff R hR ht]
  change RelMap S (fun i ↦ (ts i).realize (Sum.elim t default)) ↔ _
  simp only [realize_termIndex]
  rfl

/-- **The structure of a realization satisfies the pairs of the stage types**: a tuple of type `p`
satisfies every literal of `p`, under exact consistency. -/
theorem satisfiesPairs_toInvariantStructure (hR : R.IsConsistent) :
    @SatisfiesPairs _ {π | IsStagePair π} M R.toInvariantStructure := by
  let := R.toInvariantStructure
  rintro ⟨n, ⟨⟨s, hn⟩, ψ⟩⟩ hπ x ⟨h, he⟩
  cases s with
  | closed => exact hπ.elim
  | base r => exact hπ.elim
  | invariant p hp =>
    change R.eval ⟨x, h⟩ = some p at he
    cases ψ with
    | rel S ts => exact (realize_rel_iff R hR he S ts).mpr hπ
    | imp φ χ =>
      cases φ with
      | rel S ts =>
        cases χ with
        | falsum =>
          change ¬ _ at hπ
          exact fun h' ↦ (hπ ((realize_rel_iff R hR he S ts).mp h')).elim
        | _ => exact hπ.elim
      | _ => exact hπ.elim
    | _ => exact hπ.elim

end VaughtConjecture.Realization

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal Order Finset

/-- **The invariance diagram of the stage types** [AFK26, Definition 2.4]: the pairs
`(Q_p(x), ψ)` with `ψ` a literal of the legal stage type `p` at stage `ω₁` (`IsStagePair`).  The
third clause holds by the face realization of `p` (`StageType.faceRealization`), the realization
on the points of `p` in which a tuple has the type of the face it spans. -/
noncomputable def stageDiagram : InvarianceDiagram stageSignature.{u} where
  pairs := {π | IsStagePair π}
  mem_pairs _ h := isStagePair_mem h
  exactlyOne n k P R j hP := by
    obtain ⟨s, hn⟩ := P
    cases s with
    | closed => exact absurd hP id
    | base r => exact absurd hP id
    | invariant p hp =>
      by_cases h : R.1.HoldsIn p j
      · exact .inl ⟨h, fun h' ↦ h' h⟩
      · exact .inr ⟨h, h⟩
  realized n Q hQ := by
    obtain ⟨s, hn⟩ := Q
    cases s with
    | closed => exact absurd hQ id
    | base r => exact absurd hQ id
    | invariant p hp =>
      let R := p.faceRealization
      refine ⟨Fin n, R.toInvariantStructure, inferInstance,
        R.isStructuredGeometry_toInvariantStructure StageType.isConsistent_faceRealization
          StageType.isCovering_faceRealization (StageType.hasLegalTypes_faceRealization hp),
        ⟨id, Function.injective_id, ?_⟩,
        R.satisfiesPairs_toInvariantStructure StageType.isConsistent_faceRealization⟩
      exact p.restrictFace_refl

end VaughtConjecture.Correspondence

namespace VaughtConjecture.Realization

open Correspondence Ordinal

/-- **The structure of a realization with legal types is compatible with the invariance diagram
of the stage types** [AFK26, Definition 2.5], under exact consistency and covering. -/
theorem isCompatible_toInvariantStructure {M : Type v} (R : Realization.{u, v} ω₁ M)
    (hR : R.IsConsistent) (hc : R.IsCovering) (hl : R.HasLegalTypes) :
    @InvarianceDiagram.IsCompatible _ _ stageDiagram.{u} M R.toInvariantStructure := by
  let := R.toInvariantStructure
  exact ⟨R.isStructuredGeometry_toInvariantStructure hR hc hl,
    R.satisfiesPairs_toInvariantStructure hR⟩

end VaughtConjecture.Realization

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal Order

/-! ### The structures compatible with the diagram are the structures of realizations -/

/-- The invariance language is relational. -/
instance invariantLanguage.isRelational : invariantLanguage.{u}.IsRelational :=
  fun _ ↦ inferInstanceAs (IsEmpty Empty)

/-- The legal stage type on no points at stage `ω₁`. -/
noncomputable def emptyType : StageType.{u} ω₁ 0 :=
  (isLegal_intervalScheme 0).toStageType ω₁

/-- The relation symbol of the invariant of a legal stage type. -/
def invariantRel {n : ℕ} (p : StageType.{u} ω₁ n) (hp : p.IsLegal) (hn : 0 < n) :
    invariantLanguage.{u}.Relations n :=
  ⟨.invariant p hp, hn⟩

namespace invariantLanguage

variable (N : Type v) [invariantLanguage.{u}.Structure N]

open Classical in
/-- The **realization of a structure** of the invariance language: the empty tuple has the stage
type on no points, and a tuple of positive length has the stage type of an invariant holding of
it, and no type if none does. -/
noncomputable def toRealization : Realization.{u, v} ω₁ N where
  eval {n} t := match n, t with
    | 0, _ => some emptyType
    | k + 1, t =>
      if h : ∃ (p : StageType.{u} ω₁ (k + 1)) (hp : p.IsLegal),
          RelMap (invariantRel p hp k.succ_pos) ⇑t
      then some h.choose else none

variable {N}

/-- The empty tuple has the stage type on no points. -/
theorem toRealization_eval_zero (t : Fin 0 ↪ N) : (toRealization N).eval t = some emptyType :=
  rfl

/-- An atomic formula `R(x_j)` holds of `x` exactly when `R` holds of `x ∘ j`. -/
theorem realize_atom {n k : ℕ} (R : invariantLanguage.{u}.Relations k) (j : Fin k → Fin n)
    (x : Fin n → N) : (atom R j).Realize x ↔ RelMap R (x ∘ j) := by
  simp only [atom, Formula.realize_rel, Term.realize_var]
  rfl

variable (hN : stageDiagram.{u}.IsCompatible N)
include hN

/-- **A tuple with an invariant has the literals of its type** in a structure compatible with the
invariance diagram of the stage types. -/
theorem relMap_comp_iff {n k : ℕ} {p : StageType.{u} ω₁ n} {hp : p.IsLegal} {hn : 0 < n}
    {x : Fin n → N}
    (hx : RelMap (invariantRel p hp hn) x)
    (R : invariantLanguage.{u}.Relations k) (j : Fin k → Fin n) :
    RelMap R (x ∘ j) ↔ R.1.HoldsIn p j := by
  by_cases h : R.1.HoldsIn p j
  · exact iff_of_true ((realize_atom R j x).mp
      (hN.satisfiesPairs ⟨n, ⟨.invariant p hp, hn⟩, atom R j⟩ h x hx)) h
  · exact iff_of_false (fun h' ↦ (Formula.realize_not.mp
      (hN.satisfiesPairs ⟨n, ⟨.invariant p hp, hn⟩, (atom R j).not⟩ h x hx))
        ((realize_atom R j x).mpr h')) h

open Classical in
/-- In a compatible structure, a tuple of positive length has the type `p` in the realization of
the structure exactly when the invariant of `p` holds of it. -/
theorem toRealization_eval_eq_some_iff {n : ℕ} (hn : 0 < n) (t : Fin n ↪ N)
    (p : StageType.{u} ω₁ n) :
    (toRealization N).eval t = some p ↔ ∃ hp : p.IsLegal, RelMap (invariantRel p hp hn) ⇑t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  change (if h : ∃ (p : StageType.{u} ω₁ (k + 1)) (hp : p.IsLegal),
      RelMap (invariantRel p hp k.succ_pos) ⇑t then some h.choose else none) = some p ↔ _
  split_ifs with h
  · rw [Option.some_inj]
    refine ⟨fun he ↦ he ▸ h.choose_spec, fun ⟨hp, hr⟩ ↦ ?_⟩
    obtain ⟨hp', hr'⟩ := h.choose_spec
    by_contra hne
    refine hN.isStructuredGeometry.exclusive (invariantRel _ hp' _) (invariantRel p hp _) trivial
      trivial ?_ _ hr' hr
    intro heq
    injection heq with heq
    injection heq
    exact hne ‹_›
  · exact ⟨fun h' ↦ by simp at h', fun h' ↦ (h ⟨p, h'⟩).elim⟩

/-- In a compatible structure, a tuple of positive length is untyped in the realization of the
structure exactly when `P_n` does not hold of it. -/
theorem toRealization_eval_eq_none_iff {n : ℕ} (hn : 0 < n) (t : Fin n ↪ N) :
    (toRealization N).eval t = none ↔ ¬ RelMap (stageSignature.{u}.closed n hn) ⇑t := by
  rw [hN.isStructuredGeometry.closed_iff, ← Option.not_isSome_iff_eq_none,
    Option.isSome_iff_exists]
  refine not_congr ⟨fun ⟨p, hp⟩ ↦ ?_, fun ⟨⟨s, _⟩, hs, hr⟩ ↦ ?_⟩
  · obtain ⟨hl, hr⟩ := (toRealization_eval_eq_some_iff hN hn t p).mp hp
    exact ⟨invariantRel p hl hn, trivial, hr⟩
  · cases s with
    | invariant p hp => exact ⟨p, (toRealization_eval_eq_some_iff hN hn t p).mpr ⟨hp, hr⟩⟩
    | closed => exact absurd hs id
    | base r => exact absurd hs id

/-- In a compatible structure, a tuple of positive length satisfying `P_n` is typed in the
realization of the structure. -/
theorem isSome_toRealization_eval {n : ℕ} (hn : 0 < n) (t : Fin n ↪ N)
    (h : RelMap (stageSignature.{u}.closed n hn) ⇑t) : ((toRealization N).eval t).isSome := by
  rw [Option.isSome_iff_ne_none, Ne, toRealization_eval_eq_none_iff hN hn]
  exact not_not.mpr h

/-- **The realization of a compatible structure is exactly consistent.** -/
theorem isConsistent_toRealization : (toRealization N).IsConsistent := by
  have hzero (n : ℕ) (t : Fin n ↪ N) (p : StageType.{u} ω₁ n) (f : Fin 0 ↪ Fin n) :
      (toRealization N).eval (f.trans t) = StageType.restrictFace f p := by
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (p.isSome_restrictFace_of_zero f)
    rw [hq, toRealization_eval_zero]
    exact congrArg some (StageType.eq_of_zero _ _)
  intro m n t p f ht
  cases m with
  | zero => exact hzero n t p f
  | succ l =>
    cases n with
    | zero => exact isEmptyElim (f 0)
    | succ k =>
      obtain ⟨hp, hx⟩ := (toRealization_eval_eq_some_iff hN k.succ_pos t p).mp ht
      have key (k' : ℕ) (R : invariantLanguage.{u}.Relations k') (j : Fin k' → Fin (k + 1)) :=
        relMap_comp_iff hN hx R j
      cases hf : StageType.restrictFace f p with
      | none =>
        refine (toRealization_eval_eq_none_iff hN l.succ_pos _).mpr fun h ↦ ?_
        obtain ⟨hj, h'⟩ := (key _ _ f).mp h
        change (StageType.restrictFace f p).isSome at h'
        rw [hf] at h'
        exact Bool.false_ne_true h'
      | some q =>
        exact (toRealization_eval_eq_some_iff hN l.succ_pos _ q).mpr
          ⟨hp.restrictFace f hf, (key _ (invariantRel q (hp.restrictFace f hf) l.succ_pos) f).mpr
            ⟨f.injective, hf⟩⟩

/-- **The realization of a compatible structure is covering**: the empty tuple is typed, and every
other tuple of distinct points extends to a tuple satisfying `P_n` (the second clause of
[AFK26, Definition 2.1]). -/
theorem isCovering_toRealization : (toRealization N).IsCovering := by
  intro n t
  cases n with
  | zero => exact ⟨0, t, Function.Embedding.refl _, rfl, rfl⟩
  | succ k =>
    obtain ⟨l, y, hy, hc⟩ :=
      hN.isStructuredGeometry.isGeometry.exists_closed k.succ_pos ⇑t t.injective
    have hyi := hN.isStructuredGeometry.isGeometry.injective _ y hc
    refine ⟨k + 1 + l, ⟨y, hyi⟩, Fin.castAddEmb l, ?_, ?_⟩
    · ext i
      exact congrFun hy i
    · exact isSome_toRealization_eval hN _ ⟨y, hyi⟩ hc

/-- **The realization of a compatible structure has legal types.** -/
theorem hasLegalTypes_toRealization : (toRealization N).HasLegalTypes := by
  intro n t p hp
  cases n with
  | zero =>
    rw [toRealization_eval_zero, Option.some_inj] at hp
    exact hp ▸ (isLegal_intervalScheme 0).isLegal_toStageType ω₁
  | succ k => exact ((toRealization_eval_eq_some_iff hN k.succ_pos t p).mp hp).1

omit hN in
/-- **Every relation holds or fails of a tuple according to the type of a closed tuple through
which it factors**: in a compatible structure, every tuple of positive length is a sequence of
places of a tuple with an invariant. -/
theorem exists_relMap_invariant_comp (hN : stageDiagram.{u}.IsCompatible N) {k : ℕ} (hk : 0 < k)
    (xs : Fin k → N) : ∃ (n : ℕ) (y : Fin n → N) (p : StageType.{u} ω₁ n) (hp : p.IsLegal)
      (hn : 0 < n) (j : Fin k → Fin n),
      RelMap (invariantRel p hp hn) y ∧ xs = y ∘ j := by
  classical
  set S := Finset.univ.image xs
  have hS : 0 < S.card := Finset.card_pos.mpr ⟨xs ⟨0, hk⟩, Finset.mem_image_of_mem _ (by simp)⟩
  set e := S.equivFin
  obtain ⟨l, y, hy, hc⟩ := hN.isStructuredGeometry.isGeometry.exists_closed hS
    (fun i ↦ (e.symm i).1) fun i i' h ↦ e.symm.injective (Subtype.ext h)
  obtain ⟨⟨s, hn⟩, hs, hr⟩ := (hN.isStructuredGeometry.closed_iff _ y).mp hc
  cases s with
  | closed => exact absurd hs id
  | base r => exact absurd hs id
  | invariant p hp =>
    refine ⟨_, y, p, hp, hn, fun i ↦ Fin.castAdd l (e ⟨xs i, Finset.mem_image_of_mem _ (by simp)⟩),
      hr, funext fun i ↦ ?_⟩
    have := congrFun hy (e ⟨xs i, Finset.mem_image_of_mem _ (by simp)⟩)
    simp only [Function.comp_apply, Equiv.symm_apply_apply] at this
    exact this.symm

end invariantLanguage

/-- **A compatible structure is determined by its invariants**: two structures of the invariance
language on one carrier, both compatible with the invariance diagram of the stage types, in which
the same invariants hold of the same tuples, are equal. -/
theorem structure_eq_of_isCompatible {N : Type v} (s₁ s₂ : invariantLanguage.{u}.Structure N)
    (h₁ : @InvarianceDiagram.IsCompatible _ _ stageDiagram.{u} N s₁)
    (h₂ : @InvarianceDiagram.IsCompatible _ _ stageDiagram.{u} N s₂)
    (h : ∀ (n : ℕ) (p : StageType.{u} ω₁ n) (hp : p.IsLegal) (hn : 0 < n) (y : Fin n → N),
      @RelMap _ N s₁ n (invariantRel p hp hn) y ↔ @RelMap _ N s₂ n (invariantRel p hp hn) y) :
    s₁ = s₂ := by
  refine Structure.ext_of_isRelational fun k R xs ↦ ?_
  obtain ⟨n, y, p, hp, hn, j, hy, rfl⟩ :=
    @invariantLanguage.exists_relMap_invariant_comp N s₁ h₁ k R.2 xs
  rw [@invariantLanguage.relMap_comp_iff N s₁ h₁ _ _ _ _ _ _ hy,
    @invariantLanguage.relMap_comp_iff N s₂ h₂ _ _ _ _ _ _ ((h n p hp hn y).mp hy)]

namespace invariantLanguage

variable {N : Type v} [invariantLanguage.{u}.Structure N]

/-- **Round trip on structures**: the structure of the realization of a structure compatible with
the invariance diagram of the stage types is the structure. -/
theorem toInvariantStructure_toRealization (hN : stageDiagram.{u}.IsCompatible N) :
    (toRealization N).toInvariantStructure = ‹invariantLanguage.{u}.Structure N› := by
  refine structure_eq_of_isCompatible _ _ ((toRealization N).isCompatible_toInvariantStructure
    (isConsistent_toRealization hN) (isCovering_toRealization hN)
    (hasLegalTypes_toRealization hN)) hN fun n p hp hn y ↦ ?_
  refine ⟨fun ⟨hy, he⟩ ↦ ?_, fun hr ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨hp', hr⟩ := (toRealization_eval_eq_some_iff hN hn ⟨y, hy⟩ p).mp he
    exact hr
  · exact hN.isStructuredGeometry.isGeometry.injective hn y
      ((hN.isStructuredGeometry.closed_iff hn y).mpr ⟨invariantRel p hp hn, trivial, hr⟩)
  · exact (toRealization_eval_eq_some_iff hN hn _ p).mpr ⟨hp, hr⟩

end invariantLanguage

/-- **Round trip on realizations**: the realization of the structure of an exactly consistent
covering realization with legal types at stage `ω₁` is the realization. -/
theorem toRealization_toInvariantStructure {M : Type v} {R : Realization.{u, v} ω₁ M}
    (hR : R.IsConsistent) (hc : R.IsCovering) (hl : R.HasLegalTypes) :
    @invariantLanguage.toRealization M R.toInvariantStructure = R := by
  let := R.toInvariantStructure
  have hN := R.isCompatible_toInvariantStructure hR hc hl
  ext n t : 1
  cases n with
  | zero =>
    rw [invariantLanguage.toRealization_eval_zero]
    obtain ⟨m, u, f, rfl, hu⟩ := hc t
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hu
    obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp (q.isSome_restrictFace_of_zero f)
    rw [hR u q f hq, hq']
    exact congrArg some (StageType.eq_of_zero _ _)
  | succ k =>
    refine Option.ext fun p ↦
      (invariantLanguage.toRealization_eval_eq_some_iff hN k.succ_pos t p).trans
      ⟨fun ⟨_, _, he⟩ ↦ he, fun he ↦ ⟨hl _ _ he, t.injective, he⟩⟩

/-- **The structures compatible with the invariance diagram of the stage types are exactly the
structures of the exactly consistent covering realizations with legal types at stage `ω₁`**, by
the mutually inverse maps `Realization.toInvariantStructure` and `invariantLanguage.toRealization`
(`invariantLanguage.toInvariantStructure_toRealization`, `toRealization_toInvariantStructure`). -/
theorem isCompatible_iff_exists_toInvariantStructure_eq {N : Type v}
    [inst : invariantLanguage.{u}.Structure N] :
    stageDiagram.{u}.IsCompatible N ↔ ∃ R : Realization.{u, v} ω₁ N,
      R.IsConsistent ∧ R.IsCovering ∧ R.HasLegalTypes ∧ R.toInvariantStructure = inst := by
  refine ⟨fun hN ↦ ⟨_, invariantLanguage.isConsistent_toRealization hN,
    invariantLanguage.isCovering_toRealization hN, invariantLanguage.hasLegalTypes_toRealization hN,
    invariantLanguage.toInvariantStructure_toRealization hN⟩, ?_⟩
  rintro ⟨R, hR, hc, hl, rfl⟩
  exact R.isCompatible_toInvariantStructure hR hc hl

/-! ### Projections of stage types -/

end VaughtConjecture.Correspondence

namespace VaughtConjecture.StageType

open Ordinal Order Label

variable {n m : ℕ} {γ δ : Ordinal.{u}} (p : StageType.{u} ω₁ n)

/-- The **projection** of a stage type at stage `ω₁` to a stage `γ` that is zero or a limit: its
reduction to `γ`, read again at stage `ω₁`. -/
noncomputable def project (hγ : IsSuccPrelimit γ) : StageType.{u} ω₁ n :=
  (p.reduce hγ).reduce (Cardinal.isSuccLimit_omega 1).isSuccPrelimit

/-- Projection keeps the scheme. -/
@[simp] theorem project_toScheme (hγ : IsSuccPrelimit γ) : (p.project hγ).toScheme = p.toScheme :=
  rfl

/-- Projection to a countable stage reduces every label to that stage. -/
theorem label_project (hγ : IsSuccPrelimit γ) (hγω : γ ≤ ω₁) (d : Fin p.card) :
    (p.project hγ).label d = Label.reduce γ (p.label d) :=
  (p.reduce hγ).reduce_label_of_le _ hγω d

/-- Reading a label reduced to a stage `γ ≤ ω₁` at stage `ω₁` does not change it. -/
theorem reduce_omega_one_reduce (hγω : γ ≤ ω₁) (x : Label.{u}) :
    Label.reduce ω₁ (Label.reduce γ x) = Label.reduce γ x :=
  ((atStage_reduce γ x).mono hγω).reduce_eq

/-- Projection preserves legality. -/
theorem IsLegal.project {p : StageType.{u} ω₁ n} (hp : p.IsLegal) (hγ : IsSuccPrelimit γ) :
    (p.project hγ).IsLegal :=
  hp

/-- **A stage type is fixed by projection to `γ` exactly when its labels occur at stage `γ`.** -/
theorem project_eq_self_iff (hγ : IsSuccPrelimit γ) (hγω : γ ≤ ω₁) :
    p.project hγ = p ↔ ∀ d, AtStage γ (p.label d) := by
  refine ⟨fun h d ↦ ?_, fun h ↦ ext rfl fun i j hij ↦ ?_⟩
  · rw [← reduce_eq_self_iff, ← p.label_project hγ hγω]
    exact label_congr h rfl
  · rw [Fin.ext hij, label_project _ hγ hγω]
    exact (h j).reduce_eq

/-- **Projections compose to the lower one**: `τ_γ ∘ τ_δ = τ_γ` for `γ ≤ δ ≤ ω₁`. -/
theorem project_project_of_le (hγ : IsSuccPrelimit γ) (hδ : IsSuccPrelimit δ) (hγδ : γ ≤ δ)
    (hδω : δ ≤ ω₁) : (p.project hδ).project hγ = p.project hγ :=
  ext rfl fun i j hij ↦ by
    have hij' : (i : Fin p.card) = j := Fin.ext hij
    change Label.reduce ω₁ (Label.reduce γ (Label.reduce ω₁ (Label.reduce δ (p.label i)))) =
      Label.reduce ω₁ (Label.reduce γ (p.label j))
    rw [hij', reduce_omega_one_reduce hδω, reduce_reduce_of_le hγδ]

/-- **Projections compose to the lower one**: `τ_δ ∘ τ_γ = τ_γ` for `γ ≤ δ ≤ ω₁`. -/
theorem project_project_of_le' (hγ : IsSuccPrelimit γ) (hδ : IsSuccPrelimit δ) (hγδ : γ ≤ δ)
    (hδω : δ ≤ ω₁) : (p.project hγ).project hδ = p.project hγ :=
  ext rfl fun i j hij ↦ by
    have hij' : (i : Fin p.card) = j := Fin.ext hij
    change Label.reduce ω₁ (Label.reduce δ (Label.reduce ω₁ (Label.reduce γ (p.label i)))) =
      Label.reduce ω₁ (Label.reduce γ (p.label j))
    rw [hij', reduce_omega_one_reduce (hγδ.trans hδω), reduce_omega_one_reduce hδω]
    exact ((atStage_reduce γ _).mono hγδ).reduce_eq

/-- **Projection commutes with face maps**, including definedness. -/
theorem restrictFace_project (hγ : IsSuccPrelimit γ) (f : Fin m ↪ Fin n) :
    restrictFace f (p.project hγ) = (restrictFace f p).map (project · hγ) := by
  rw [project, restrictFace_reduce, restrictFace_reduce, Option.map_map]
  rfl

/-- **Projection to a stage at least `ω` does not change the reduction to `ω`.** -/
theorem reduce_omega0_project (hγ : IsSuccPrelimit γ) (hωγ : ω ≤ γ) :
    (p.project hγ).reduce isSuccLimit_omega0.isSuccPrelimit =
      p.reduce isSuccLimit_omega0.isSuccPrelimit := by
  rw [project, reduce_reduce _ _ _ (omega0_lt_omega_one.le), reduce_reduce _ _ _ hωγ]

end VaughtConjecture.StageType

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal Order

/-! ### The invariant systems of the stage types -/

namespace InvariantSymbol

variable {n : ℕ} {γ : Ordinal.{u}}

/-- The **projection of a symbol** to a stage `γ`: the invariant of `p` goes to the invariant of
the projection of `p`, and every other symbol is fixed. -/
noncomputable def project (hγ : IsSuccPrelimit γ) : InvariantSymbol.{u} n → InvariantSymbol.{u} n
  | invariant p hp => invariant (p.project hγ) (hp.project hγ)
  | s => s

/-- The projection of an invariant is an invariant. -/
theorem IsInvariant.project {s : InvariantSymbol.{u} n} (hs : s.IsInvariant)
    (hγ : IsSuccPrelimit γ) : (s.project hγ).IsInvariant := by
  cases s with
  | invariant p hp => trivial
  | closed => exact absurd hs id
  | base r => exact absurd hs id

end InvariantSymbol

/-- The **projection of an invariant** to the stage `γ`. -/
noncomputable def projectInvariant {γ : Ordinal.{u}} (hγ : IsSuccPrelimit γ) {n : ℕ}
    (Q : stageSignature.{u}.Invariant n) : stageSignature.{u}.Invariant n :=
  ⟨⟨Q.1.1.project hγ, Q.1.2⟩, Q.2.project hγ⟩

/-- The projection of the invariant of `p` is the invariant of the projection of `p`. -/
@[simp] theorem projectInvariant_invariant {γ : Ordinal.{u}} (hγ : IsSuccPrelimit γ) {n : ℕ}
    (p : StageType.{u} ω₁ n) (hp : p.IsLegal) (hn : 0 < n) :
    projectInvariant hγ ⟨⟨.invariant p hp, hn⟩, trivial⟩ =
      ⟨⟨.invariant (p.project hγ) (hp.project hγ), hn⟩, trivial⟩ :=
  rfl

/-- Two invariants of legal stage types are equal exactly when the stage types are. -/
theorem invariant_eq_invariant_iff {n : ℕ} {p q : StageType.{u} ω₁ n} {hp : p.IsLegal}
    {hq : q.IsLegal} {hn : 0 < n} :
    (⟨⟨.invariant p hp, hn⟩, trivial⟩ : stageSignature.{u}.Invariant n) =
      ⟨⟨.invariant q hq, hn⟩, trivial⟩ ↔ p = q := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  have h' := congrArg (fun Q : stageSignature.{u}.Invariant n ↦ Q.1.1) h
  simp only at h'
  injection h'

variable (f : Ordinal.{u} → Ordinal.{u})

/-- **The invariant system of the projections along a stage function `f`**
[AFK26, Definition 2.6]: `τ_β` is the projection of the invariants to the stage `f β`.  It is an
invariant system when every `f β` is zero or a limit, `f` is monotone, countable at countable
arguments, and unbounded below `ω₁`. -/
noncomputable def reductionSystem (hf : ∀ β, IsSuccPrelimit (f β)) (hmono : Monotone f)
    (hlt : ∀ β < ω₁, f β < ω₁) (hunb : ∀ o < ω₁, ∃ β < ω₁, o < f β) :
    InvariantSystem.{u} stageSignature.{u} where
  τ β _ := projectInvariant (hf β)
  comp α β hαβ hβ n Q := by
    obtain ⟨p, hp, hn, rfl⟩ := stageSignature.exists_eq_invariant Q
    simp only [projectInvariant_invariant, invariant_eq_invariant_iff]
    exact ⟨p.project_project_of_le _ _ (hmono hαβ) (hlt β hβ).le,
      p.project_project_of_le' _ _ (hmono hαβ) (hlt β hβ).le⟩
  countable β hβ := by
    have := fun n ↦ StageType.countable_of_lt_omega_one (hlt β hβ) n
    let g : (Σ n, {q : StageType.{u} (f β) n // q.IsLegal ∧ 0 < n}) →
        Σ n, stageSignature.{u}.Invariant n := fun q ↦
      ⟨q.1, ⟨⟨.invariant (q.2.1.reduce (Cardinal.isSuccLimit_omega 1).isSuccPrelimit) q.2.2.1,
        q.2.2.2⟩, trivial⟩⟩
    refine (Set.countable_range g).mono ?_
    rintro ⟨n, Q⟩ hQ
    obtain ⟨p, hp, hn, rfl⟩ := stageSignature.exists_eq_invariant Q
    refine ⟨⟨n, p.reduce (hf β), hp, hn⟩, ?_⟩
    simp only [Set.mem_ofPred_eq, projectInvariant_invariant] at hQ ⊢
    simp only [g, Sigma.mk.injEq, heq_eq_eq, true_and]
    exact invariant_eq_invariant_iff.mpr (invariant_eq_invariant_iff.mp hQ)
  ne_univ β hβ := by
    obtain ⟨d, hd, i, -, hi⟩ := StageType.exists_onePoint_label (α := ω₁) (c := f β + 1)
      (by simpa using Label.isSelfVisible_coe_add (k := 1) (K := 1) (hf β) le_rfl)
      ((Cardinal.isSuccLimit_omega 1).succ_lt (hlt β hβ))
    intro h
    have hfix : (⟨1, ⟨⟨.invariant d hd, one_pos⟩, trivial⟩⟩ : Σ n, stageSignature.{u}.Invariant n) ∈
        {Q : Σ n, stageSignature.{u}.Invariant n | projectInvariant (hf β) Q.2 = Q.2} :=
      h ▸ Set.mem_univ _
    simp only [Set.mem_ofPred_eq, projectInvariant_invariant, invariant_eq_invariant_iff,
      d.project_eq_self_iff _ (hlt β hβ).le] at hfix
    have := hfix i
    rw [hi, Label.atStage_coe] at this
    exact (lt_add_one (f β)).not_ge this.le |>.elim
  exists_fixed n Q := by
    obtain ⟨p, hp, hn, rfl⟩ := stageSignature.exists_eq_invariant Q
    have hd (d : Fin p.card) : ∃ β < ω₁, Label.AtStage (f β) (p.label d) := by
      rcases Label.atStage_iff.mp (p.atStage d) with h | ⟨o, ho, h⟩ | h
      · exact ⟨0, omega_pos 1, h ▸ Label.atStage_bot⟩
      · obtain ⟨β, hβ, hoβ⟩ := hunb o ho
        exact ⟨β, hβ, h ▸ Label.atStage_coe.mpr hoβ⟩
      · exact ⟨0, omega_pos 1, h ▸ Label.atStage_top⟩
    choose g hg hgd using hd
    refine ⟨Finset.univ.sup g, (Finset.sup_lt_iff (omega_pos 1)).mpr fun d _ ↦ hg d, ?_⟩
    simp only [projectInvariant_invariant, invariant_eq_invariant_iff]
    refine (p.project_eq_self_iff _ (hlt _ ?_).le).mpr fun d ↦
      (hgd d).mono (hmono (Finset.le_sup (Finset.mem_univ d)))
    exact (Finset.sup_lt_iff (omega_pos 1)).mpr fun d _ ↦ hg d

/-- **The invariant system of the block stages**: `τ_ξ` is the projection to the block stage
`λ_ξ = ω + ω · ξ`. -/
noncomputable def blockSystem : InvariantSystem.{u} stageSignature.{u} :=
  reductionSystem blockStage isSuccPrelimit_blockStage blockStage_mono
    (fun _ h ↦ blockStage_lt_omega_one h) fun o ho ↦
      ⟨o + 1, (Cardinal.isSuccLimit_omega 1).succ_lt ho,
        (lt_add_one o).trans_le (le_blockStage (o + 1))⟩

/-- **The invariant system of the printed indexing**: `τ_β` is the projection to the stage
`ω · β`, as in [AFK26, Definition 3.18] and the definition of `τ_β` in [AFK26, §4.2]. -/
noncomputable def omega0MulSystem : InvariantSystem.{u} stageSignature.{u} :=
  reductionSystem (ω * ·) (fun β ↦ isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right ω β))
    (isNormal_mul_right omega0_pos).strictMono.monotone
    (fun _ h ↦ isPrincipal_mul_omega 1 omega0_lt_omega_one h)
    fun o ho ↦ ⟨o + 1, (Cardinal.isSuccLimit_omega 1).succ_lt ho,
      (lt_add_one o).trans_le (le_mul_right (o + 1) omega0_pos)⟩

/-- The projection of an invariant depends only on the stage. -/
theorem projectInvariant_congr {γ δ : Ordinal.{u}} (h : γ = δ) (hγ : IsSuccPrelimit γ)
    (hδ : IsSuccPrelimit δ) {n : ℕ} (Q : stageSignature.{u}.Invariant n) :
    projectInvariant hγ Q = projectInvariant hδ Q := by
  subst h
  rfl

/-- **The printed projection of index `1 + ξ` is the projection of the block stage `λ_ξ`**: the
two invariant systems differ by the reindexing `ξ ↦ 1 + ξ` (`blockStage_eq_mul`). -/
theorem omega0MulSystem_τ_one_add (ξ : Ordinal.{u}) {n : ℕ}
    (Q : stageSignature.{u}.Invariant n) : omega0MulSystem.τ (1 + ξ) Q = blockSystem.τ ξ Q :=
  projectInvariant_congr (blockStage_eq_mul ξ).symm _ _ Q

/-- **The reduction systems at stages at least `ω` are compatible with the invariance diagram of
the stage types** [AFK26, Definition 2.8]: projection carries a face of a type to the face of its
projection, keeps the closed faces, and keeps the reductions to `ω`. -/
theorem isCompatibleWith_reductionSystem (f : Ordinal.{u} → Ordinal.{u})
    (hf : ∀ β, IsSuccPrelimit (f β)) (hmono : Monotone f) (hlt : ∀ β < ω₁, f β < ω₁)
    (hunb : ∀ o < ω₁, ∃ β < ω₁, o < f β) (hω : ∀ β < ω₁, ω ≤ f β) :
    stageDiagram.IsCompatibleWith (reductionSystem f hf hmono hlt hunb) := by
  refine ⟨fun β hβ n k P Q j hPQ ↦ ?_, fun β hβ n k P R j hR ↦ ?_⟩
  · obtain ⟨p, hp, hn, rfl⟩ := stageSignature.exists_eq_invariant P
    obtain ⟨q, hq, hk, rfl⟩ := stageSignature.exists_eq_invariant Q
    obtain ⟨hj, he⟩ : ∃ hj : Function.Injective j, StageType.restrictFace ⟨j, hj⟩ p = some q :=
      hPQ
    refine ⟨hj, ?_⟩
    change StageType.restrictFace ⟨j, hj⟩ (p.project (hf β)) = some (q.project (hf β))
    rw [StageType.restrictFace_project, he, Option.map_some]
  · obtain ⟨p, hp, hn, rfl⟩ := stageSignature.exists_eq_invariant P
    obtain ⟨s, hk⟩ := R
    change InvariantSymbol.HoldsIn s p j ↔ InvariantSymbol.HoldsIn s (p.project (hf β)) j
    refine exists_congr fun hj ↦ ?_
    rw [StageType.restrictFace_project]
    cases s with
    | closed => simp [InvariantSymbol.HoldsAt]
    | invariant q hq => exact absurd trivial hR
    | base r =>
      simp only [InvariantSymbol.HoldsAt, Option.map_map]
      congr! 2
      funext q
      exact (q.reduce_omega0_project (hf β) (hω β hβ)).symm

/-- **The block system is compatible with the invariance diagram of the stage types**
[AFK26, Definition 2.8]: every block stage is at least `ω`. -/
theorem isCompatibleWith_blockSystem : stageDiagram.{u}.IsCompatibleWith blockSystem :=
  isCompatibleWith_reductionSystem _ _ _ _ _ fun β _ ↦ omega0_le_blockStage β

/-- **The printed indexing is not compatible with the invariance diagram of the stage types**: at
the printed index `0` the projection is the reduction to the stage `0`, which sends the label `1`
of a legal one-point type to the top, and so changes its base relation at `ω`.  This is why the
block stages start at `ω` (`VaughtConjecture.Correspondence.StageIndexing`). -/
theorem not_isCompatibleWith_omega0MulSystem :
    ¬ stageDiagram.{u}.IsCompatibleWith omega0MulSystem := by
  intro h
  have hω : IsSuccPrelimit (ω : Ordinal.{u}) := isSuccLimit_omega0.isSuccPrelimit
  obtain ⟨d, hd, i, -, hi⟩ := StageType.exists_onePoint_label (α := ω₁) (c := 1)
    (by simp) (one_lt_omega0.trans omega0_lt_omega_one)
  have key := h.base (β := 0) (omega_pos 1) ⟨⟨.invariant d hd, one_pos⟩, trivial⟩
    ⟨.base (baseLanguage.symbol (d.reduce hω) (hd.reduce hω)), one_pos⟩ id id
  have hl : InvariantSymbol.HoldsIn (.base (baseLanguage.symbol (d.reduce hω) (hd.reduce hω))) d
      id := ⟨Function.injective_id, by
    change (StageType.restrictFace (Function.Embedding.refl _) d).map _ = _
    rw [StageType.restrictFace_refl]
    rfl⟩
  have hm : InvariantSymbol.HoldsIn (.base (baseLanguage.symbol (d.reduce hω) (hd.reduce hω)))
      (d.project (isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right ω 0))) id :=
    key.mp hl
  obtain ⟨hj, he⟩ := hm
  change (StageType.restrictFace (Function.Embedding.refl _) _).map _ = _ at he
  rw [StageType.restrictFace_refl, Option.map_some, Option.some_inj] at he
  have hlab := StageType.label_congr he (i := i) (j := i) rfl
  change Label.reduce ω (Label.reduce ω₁ (Label.reduce (ω * 0) (d.label i))) =
    Label.reduce ω (d.label i) at hlab
  rw [hi, mul_zero] at hlab
  simp only [WithTop.coe_one, WithBot.coe_one, WithTop.coe_zero, WithBot.coe_zero, zero_le_one,
    Label.reduce_of_le, le_top, WithBot.one_lt_coe, WithTop.one_lt_coe, one_lt_omega0,
    Label.reduce_of_lt] at hlab
  exact Label.not_isProper_top (hlab ▸ Label.isProper_one)

end VaughtConjecture.Correspondence
