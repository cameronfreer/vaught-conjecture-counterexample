/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.StageType
import VaughtConjecture.Realization.Model

/-!
# Correspondence: models

Roadmap, "Manuscript concordance", row 11.  The printed definition of a model of `S^α`
[Kni26, Definition 3.2.1] is compiled clause by clause (`Realization.PrintedModel`), with its
guards and the order of its quantifiers, and identified with `Realization.IsModel`.

## The setting

The printed model is a partial function `M` from the finite tuples on a nonempty set `M` to the
type spaces `S^α n`.  Here it is a family `F n : (Fin n → M) → Option (StageType α n)`, the
arity built into the type; a type in `S^α n` is a legal stage type (row 8,
`StageType.isLegal_iff_printedType`), the map `S^α f` is `StageType.restrictFace f` (row 8,
`StageType.restrictFace_eq_some_iff_exists_printedFaceMap`, with the codes of the cells forgotten
and the cells of a face numbered by the positions of the corresponding cells, as in row 7), the
inclusion `ι_{n,n+1}` is
`Fin.castSuccEmb`, the concatenation `x⌢y` is `Fin.snoc x y`, and `a⌢x` is `Fin.append a x`.  A
realization evaluates only the injective tuples; read on all tuples it is
`Realization.tupleEval`, undefined at a tuple with a repeated entry, and every such partial
function is one (`Realization.ofTupleEval_tupleEval`, `Realization.tupleEval_ofTupleEval`).

| Printed clause | Field of `PrintedModel` | Field of `IsModel` |
| --- | --- | --- |
| `M` is a nonempty set | `nonempty` | `nonempty` |
| 1. `M(x)` is undefined if `x` has a repeated entry | `eq_none_of_not_injective` | (departure 1) |
| 1. `M(x) ∈ S^α n` if defined, `x` non-repeating | `isLegal_of_eq_some` | `isLegal` |
| 2. Consistency | `consistency` | `isConsistent` |
| 3. Covering | `covering` | `isCovering` (departure 4) |
| 4(a)i. Generalized saturation | `saturation` | `saturation` (departures 2, 3) |
| 4(a)ii. the bottom pattern of `q'` | `bottomPattern` | `bottomPattern` (departures 2, 3, 5) |
| 4(b). Uniformity | `uniformity` | `uniformity` (departure 2) |
| 4(c). High-arity Dominance | `dominance` | `dominance` (departure 2) |

**Reading of clause 4.**  Clause 4 asks, for `M(x) = p` and a set `U` "of one of the four kinds",
a subset of `(S^α ι_{n,n+1})⁻¹(p)`, for `y` and `q ∈ U` with `M(x⌢y) = q`.  Each kind is read
as a subset of `(S^α ι_{n,n+1})⁻¹(p)`: `U` is the set of the `q` in `(S^α ι_{n,n+1})⁻¹(p)`
satisfying the condition of the kind (for clause (a)ii, the `q ∈ S^α (n + 1)` there).  The
inclusion `U ⊆ (S^α ι_{n,n+1})⁻¹(p)` is thus part of the definition of `U`, not a further
hypothesis on the set of all `q` satisfying the condition.  This is the reading of the manuscript
itself: [Kni26, Lemma 4.4.1] states that every such `U` is nonempty, and
[Kni26, Lemmas 4.4.2 and 4.4.3] prove it in the form "some `q` with `q_a = p` satisfies the
condition of the kind".  Every other guard is kept: in (a)i
and (a)ii, `D` is a domain on a plan on `n + 1` with `D⟨n,n⟩ = dom p`; in (a)ii, `q'` respects
the semantics of `D` and `q'↾dom p = p`; in (b), `γ` is not a successor and `0 ≤ γ < α`; in (c),
`γ < α`.  The quantifiers are in the printed order: `x` and `p`, then the parameters of `U` with
their guards, then `y` and `q`.

**Identification.**  At a stage `α ≤ ω₁` that is zero or a limit (the printed `α` is a limit
`≤ ω₁`), a realization is a model as printed exactly when it is a model
(`Realization.printedModel_tupleEval_iff`).  Every printed clause is met by this theorem; the
two directions are `Realization.PrintedModel.isModel` and `Realization.IsModel.printedModel`.

**Departures**, each proved equivalent by named theorems at the stated stages.
1. *Tuples with a repeated entry.*  A realization evaluates only injective tuples, so the first
   half of clause 1 holds by construction (`Realization.tupleEval_of_not_injective`), and a
   partial function satisfying it is the reading of a unique realization
   (`Realization.tupleEval_ofTupleEval`, `Realization.ofTupleEval_tupleEval`).
2. *The conclusions of clause 4.*  The four clauses of `IsModel` ask for a typed tuple whose type
   lies in the family, not in the family and in `(S^α ι_{n,n+1})⁻¹(p)`; under clauses 1 and 2 a
   realized type is in `(S^α ι_{n,n+1})⁻¹(p)` (`Realization.RealizesOver.inter_cofaces`).
3. *The guards of clauses 4(a)i and 4(a)ii.*  `IsModel` quantifies over every scheme `S` on
   `n + 1` points (and every labelling `ρ` of its cells), guarded by the nonemptiness of the
   family among the cofaces of `p`.  At a stage that is zero or a limit this guard is the printed
   one: for saturation, `S` is legal, the first `n` points span a closed face, and the face there
   is the scheme of `p` (`StageType.nonempty_cofaces_inter_saturationFamily_iff`); for the bottom
   pattern, moreover, the family is that of a lawful section extending the labels of `p`
   (`StageType.nonempty_cofaces_inter_bottomPatternFamily_iff`).  The printed `D⟨n,n⟩ = dom p` is
   `S.comap Fin.castSuccEmb = p.toScheme`; that the first `n` points then span a closed face of
   `S` follows from the completeness of `p` (`Scheme.map_univ_mem_faces_of_comap_eq`).
4. *Covering.*  `Realization.IsCovering` asks every injective tuple to be a face of a typed
   tuple, the printed clause 3 an initial segment `a⌢x`; under clause 2 these agree
   (`Realization.isCovering_iff_exists_castAdd`).
5. *The labelling of clause 4(a)ii.*  The printed `q'` respects the semantics of `D`, so takes
   values in `{-∞} ∪ ω₁ ∪ {∞}` (`CellScheme.Rows.PrintedRespects` at `ω₁`, row 4); the labelling
   `ρ` of `IsModel` is any labelling.  A nonempty bottom-pattern family is that of the labels of
   any of its members, which lie at stage `α ≤ ω₁`
   (`StageType.nonempty_cofaces_inter_bottomPatternFamily_iff`).
6. *The stage.*  `IsModel` is defined at every stage; the identification is at the stages
   `α ≤ ω₁` that are zero or limits.
7. *Domains and types* are those of rows 7 (C, the corrected domains) and 8.  The domains have
   a part still to be proved, bountifulness at `ω₁` (row 6, S): the identification is over legal
   schemes, both for `S^α n` in clause 1 and for the domains `D` of clause 4(a), so the status of
   the row is P with its domains still to be proved (row 6).

## Placement

The concordance and its notes are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".
-/

universe u v

namespace VaughtConjecture

open Finset Label StageType

/-! ### The initial segment of a coface -/

namespace Scheme

/-- **The face of a scheme equal to a type spans a closed face**: if the restriction of a
well-formed scheme along `f` is the scheme of a complete stage type, the range of `f` is a closed
face of the scheme. -/
theorem map_univ_mem_faces_of_comap_eq {n m : ℕ} {α : Ordinal.{u}} {S : Scheme.{u} n}
    (hS : S.IsWellFormed) {f : Fin m ↪ Fin n} {p : StageType.{u} α m}
    (hp : p.toCellScheme.IsComplete) (h : S.comap f = p.toScheme) :
    univ.map f ∈ S.toCellScheme.faces := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using hS.isPlan.empty_mem
  · have hc : (S.comap f).toCellScheme.IsComplete := h ▸ hp
    have hX : ((univ : Finset (Fin m)), m) ∈ (S.comap f).toCellScheme.gradedFaces := by
      rw [h]
      exact ⟨p.univ_mem_faces, hm, by simp⟩
    obtain ⟨d, hd⟩ := hc _ hX
    have hsc : (S.comap f).toCellScheme.scope d = univ := congrArg Prod.fst hd
    rw [← hsc, map_comap_scope]
    exact hS.isWellFormed.scope_mem _

end Scheme

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {n : ℕ}

/-! ### Realizations on all finite tuples -/

section TupleEval

variable (R : Realization.{u, v} α M)

open scoped Classical in
/-- **A realization on all finite tuples** [Kni26, Definition 3.2.1]: the type of an injective
tuple, and undefined at a tuple with a repeated entry. -/
noncomputable def tupleEval (n : ℕ) (x : Fin n → M) : Option (StageType.{u} α n) :=
  if h : Function.Injective x then R.eval ⟨x, h⟩ else none

/-- The realization reading a partial function on finite tuples on the injective tuples. -/
def ofTupleEval (F : ∀ n : ℕ, (Fin n → M) → Option (StageType.{u} α n)) :
    Realization.{u, v} α M :=
  ⟨fun t ↦ F _ t⟩

variable {R} {x : Fin n → M}

/-- At an injective tuple the reading on all tuples is the evaluation. -/
theorem tupleEval_eq_eval (hx : Function.Injective x) : R.tupleEval n x = R.eval ⟨x, hx⟩ := by
  simp [tupleEval, hx]

/-- At an embedding the reading on all tuples is the evaluation. -/
@[simp] theorem tupleEval_embedding (t : Fin n ↪ M) : R.tupleEval n t = R.eval t :=
  tupleEval_eq_eval t.injective

/-- A tuple with a repeated entry is undefined. -/
theorem tupleEval_of_not_injective (hx : ¬ Function.Injective x) : R.tupleEval n x = none := by
  simp [tupleEval, hx]

/-- A tuple with a value is injective. -/
theorem injective_of_tupleEval_isSome (h : (R.tupleEval n x).isSome) : Function.Injective x := by
  by_contra hx
  simp [tupleEval_of_not_injective hx] at h

/-- A tuple with a value is injective. -/
theorem injective_of_tupleEval_eq_some {p : StageType.{u} α n} (h : R.tupleEval n x = some p) :
    Function.Injective x :=
  injective_of_tupleEval_isSome (by rw [h]; rfl)

/-- A realization is the realization of its reading on all tuples. -/
@[simp] theorem ofTupleEval_tupleEval (R : Realization.{u, v} α M) :
    ofTupleEval R.tupleEval = R :=
  ext fun t ↦ tupleEval_embedding t

/-- A partial function on finite tuples undefined at the tuples with a repeated entry is the
reading on all tuples of the realization it defines. -/
theorem tupleEval_ofTupleEval {F : ∀ n : ℕ, (Fin n → M) → Option (StageType.{u} α n)}
    (hF : ∀ n (x : Fin n → M), ¬ Function.Injective x → F n x = none) :
    (ofTupleEval F).tupleEval = F := by
  funext n x
  by_cases hx : Function.Injective x
  · rw [tupleEval_eq_eval hx]
    rfl
  · rw [tupleEval_of_not_injective hx, hF n x hx]

/-- **Realizing over a tuple, on all tuples**: `R` realizes a member of `U` over `t` exactly when
some `y` gives a concatenation `t⌢y` whose value is in `U`. -/
theorem realizesOver_iff_exists_tupleEval {t : Fin n ↪ M} {U : Set (StageType.{u} α (n + 1))} :
    R.RealizesOver t U ↔
      ∃ y : M, ∃ q ∈ U, R.tupleEval (n + 1) (Fin.snoc (α := fun _ ↦ M) t y) = some q := by
  constructor
  · rintro ⟨u, hu, q, hq, he⟩
    have hsnoc : (Fin.snoc (α := fun _ ↦ M) t (u (Fin.last n))) = ⇑u := by
      funext i
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · simp
      · rw [Fin.snoc_castSucc, ← hu]
        rfl
    exact ⟨u (Fin.last n), q, hq, by rw [hsnoc, tupleEval_embedding, he]⟩
  · rintro ⟨y, q, hq, he⟩
    have hinj := injective_of_tupleEval_eq_some he
    refine ⟨⟨_, hinj⟩, ?_, q, hq, (tupleEval_eq_eval hinj).symm.trans he⟩
    ext i
    simp

end TupleEval

/-! ### Models as printed -/

/-- **Models** [Kni26, Definition 3.2.1] at stage `α`, for a partial function `F` from the finite
tuples on `M` to the stage types at stage `α`, the arity built into the type: the clauses of the
definition with their guards, in the printed order of the quantifiers.  A set `U` of clause 4 is
the set of the members of `(S^α ι_{n,n+1})⁻¹(p)` satisfying the condition of its kind. -/
structure PrintedModel (α : Ordinal.{u}) (F : ∀ n : ℕ, (Fin n → M) → Option (StageType.{u} α n)) :
    Prop where
  /-- [Kni26, Definition 3.2.1]: `M` is a nonempty set. -/
  nonempty : Nonempty M
  /-- Clause 1 of [Kni26, Definition 3.2.1], arity preservation: `M(x)` is undefined if `x`
  contains a repeated entry. -/
  eq_none_of_not_injective : ∀ n (x : Fin n → M), ¬ Function.Injective x → F n x = none
  /-- Clause 1 of [Kni26, Definition 3.2.1], arity preservation: for a non-repeating tuple `x` of
  arity `n`, `M(x) ∈ S^α n` if it is defined (a legal stage type, row 8). -/
  isLegal_of_eq_some : ∀ n (x : Fin n → M), Function.Injective x →
    ∀ p : StageType.{u} α n, F n x = some p → p.IsLegal
  /-- Clause 2 of [Kni26, Definition 3.2.1], consistency: if `M(x) ∈ S^α n` and `f : m → n` is
  one-to-one, then `M(x ∘ f) = (S^α f)(M(x))` if this exists, and is undefined if not. -/
  consistency : ∀ n (x : Fin n → M) (p : StageType.{u} α n), F n x = some p →
    ∀ m (f : Fin m ↪ Fin n), (∀ q, restrictFace f p = some q → F m (x ∘ f) = some q) ∧
      (restrictFace f p = none → F m (x ∘ f) = none)
  /-- Clause 3 of [Kni26, Definition 3.2.1], covering: for every non-repeating tuple `a` there is
  a tuple `x` with `a⌢x ∈ dom M`. -/
  covering : ∀ n (a : Fin n → M), Function.Injective a →
    ∃ (k : ℕ) (x : Fin k → M), (F (n + k) (Fin.append a x)).isSome
  /-- Clause 4(a)i of [Kni26, Definition 3.2.1], generalized saturation: for `M(x) = p` and a
  domain `D` on a plan on `n + 1` with `D⟨n,n⟩ = dom p`, some `y` and some `q` in
  `(S^α ι_{n,n+1})⁻¹(p)` with `dom q = D` have `M(x⌢y) = q`. -/
  saturation : ∀ n (x : Fin n → M) (p : StageType.{u} α n), F n x = some p →
    ∀ D : Scheme.{u} (n + 1), D.IsLegal → D.comap Fin.castSuccEmb = p.toScheme →
      ∃ y : M, ∃ q : StageType.{u} α (n + 1),
        ((q.IsLegal ∧ restrictFace Fin.castSuccEmb q = some p) ∧ q.toScheme = D) ∧
          F (n + 1) (Fin.snoc (α := fun _ ↦ M) x y) = some q
  /-- Clause 4(a)ii of [Kni26, Definition 3.2.1]: for `M(x) = p`, a domain `D` on a plan on
  `n + 1` with `D⟨n,n⟩ = dom p`, and a labelling `q'` respecting the semantics of `D` with
  `q'↾dom p = p`, some `y` and some `q ∈ S^α (n + 1)` in `(S^α ι_{n,n+1})⁻¹(p)` with `dom q = D`,
  and `q(Θ) = -∞` exactly when `q'(Θ) = -∞` for `Θ ∈ D_{≤n}`, have `M(x⌢y) = q`. -/
  bottomPattern : ∀ n (x : Fin n → M) (p : StageType.{u} α n), F n x = some p →
    ∀ D : Scheme.{u} (n + 1), D.IsLegal → D.comap Fin.castSuccEmb = p.toScheme →
      ∀ q' : Fin D.card → Label.{u}, (∀ d, AtStage (Ordinal.omega.{u} 1) (q' d)) →
        D.rows.PrintedRespects (Ordinal.omega.{u} 1) q' →
        (∀ (i : Fin (D.comap Fin.castSuccEmb).card) (j : Fin p.card), (i : ℕ) = j →
          q' (D.cellMap Fin.castSuccEmb i) = p.label j) →
        ∃ y : M, ∃ q : StageType.{u} α (n + 1),
          ((q.IsLegal ∧ restrictFace Fin.castSuccEmb q = some p) ∧ q.toScheme = D ∧
            ∀ (i : Fin q.card) (j : Fin D.card), (i : ℕ) = j →
              j ∈ D.toCellScheme.below (univ, n) → (q.label i = ⊥ ↔ q' j = ⊥)) ∧
          F (n + 1) (Fin.snoc (α := fun _ ↦ M) x y) = some q
  /-- Clause 4(b) of [Kni26, Definition 3.2.1], uniformity: for `M(x) = p` and `γ` not a
  successor with `0 ≤ γ < α`, some `y` and some `q` in `(S^α ι_{n,n+1})⁻¹(p)` with
  `ran q ∩ [γ, γ + ω) ≠ ∅` have `M(x⌢y) = q`. -/
  uniformity : ∀ n (x : Fin n → M) (p : StageType.{u} α n), F n x = some p →
    ∀ γ : Ordinal.{u}, Order.IsSuccPrelimit γ → 0 ≤ γ → γ < α →
      ∃ y : M, ∃ q : StageType.{u} α (n + 1),
        ((q.IsLegal ∧ restrictFace Fin.castSuccEmb q = some p) ∧
          (Set.range q.label ∩
            Set.Ico (γ : Label.{u}) ((γ + Ordinal.omega0 : Ordinal.{u}) : Label.{u})).Nonempty) ∧
          F (n + 1) (Fin.snoc (α := fun _ ↦ M) x y) = some q
  /-- Clause 4(c) of [Kni26, Definition 3.2.1], high-arity dominance: for `M(x) = p` and
  `γ < α`, some `y` and some `q` in `(S^α ι_{n,n+1})⁻¹(p)` with `q(Σ) > γ` for some `Σ` of arity
  `n + 1` have `M(x⌢y) = q`. -/
  dominance : ∀ n (x : Fin n → M) (p : StageType.{u} α n), F n x = some p →
    ∀ γ : Ordinal.{u}, γ < α →
      ∃ y : M, ∃ q : StageType.{u} α (n + 1),
        ((q.IsLegal ∧ restrictFace Fin.castSuccEmb q = some p) ∧
          ∃ d, q.toCellScheme.grade d = n + 1 ∧ (γ : Label.{u}) < q.label d) ∧
          F (n + 1) (Fin.snoc (α := fun _ ↦ M) x y) = some q

variable {R : Realization.{u, v} α M}

/-- Grades of cells at equal positions of equal schemes are equal. -/
private theorem grade_congr {S T : Scheme.{u} (n + 1)} (h : S = T) {i : Fin S.card}
    {j : Fin T.card} (hij : (i : ℕ) = j) : S.toCellScheme.grade i = T.toCellScheme.grade j := by
  subst h
  rw [Fin.ext hij]

/-- **Models are models as printed** [Kni26, Definition 3.2.1]: at a stage that is zero or a
limit, a model satisfies every printed clause. -/
theorem IsModel.printedModel (hR : R.IsModel) (hα : Order.IsSuccPrelimit α) :
    PrintedModel α R.tupleEval where
  nonempty := hR.nonempty
  eq_none_of_not_injective _ _ hx := tupleEval_of_not_injective hx
  isLegal_of_eq_some _ _ hx p h := hR.isLegal ⟨_, hx⟩ p ((tupleEval_eq_eval hx).symm.trans h)
  consistency n x p h m f := by
    have hx := injective_of_tupleEval_eq_some h
    have he : R.tupleEval m (x ∘ f) = restrictFace f p := by
      rw [tupleEval_eq_eval (hx.comp f.injective)]
      exact hR.isConsistent ⟨x, hx⟩ p f ((tupleEval_eq_eval hx).symm.trans h)
    exact ⟨fun q hq ↦ he.trans hq, fun hq ↦ he.trans hq⟩
  covering n a ha := by
    obtain ⟨k, u, hu, hs⟩ :=
      (isCovering_iff_exists_castAdd hR.isConsistent).mp hR.isCovering ⟨a, ha⟩
    have hua (i : Fin n) : u (Fin.castAdd k i) = a i := DFunLike.congr_fun hu i
    have happ : Fin.append a (fun i ↦ u (Fin.natAdd n i)) = ⇑u := by
      funext i
      refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
      · rw [Fin.append_left, hua]
      · rw [Fin.append_right]
    exact ⟨k, fun i ↦ u (Fin.natAdd n i), by rwa [happ, tupleEval_embedding]⟩
  saturation n x p h D hD hp := by
    have hx := injective_of_tupleEval_eq_some h
    let o : R.Occurrence := ⟨n, ⟨x, hx⟩, p, (tupleEval_eq_eval hx).symm.trans h⟩
    have hf := Scheme.map_univ_mem_faces_of_comap_eq hD.isWellFormed
      (hR.isLegal _ _ o.eval_tuple).isComplete hp
    obtain ⟨y, q, ⟨hq, hqD⟩, he⟩ :=
      realizesOver_iff_exists_tupleEval.mp (hR.saturation_of_isLegal hα o hD hf hp)
    exact ⟨y, q, ⟨hq, hqD⟩, he⟩
  bottomPattern n x p h D hD hp q' hq' hres hext := by
    have hx := injective_of_tupleEval_eq_some h
    let o : R.Occurrence := ⟨n, ⟨x, hx⟩, p, (tupleEval_eq_eval hx).symm.trans h⟩
    have hf := Scheme.map_univ_mem_faces_of_comap_eq hD.isWellFormed
      (hR.isLegal _ _ o.eval_tuple).isComplete hp
    have hl : D.rows.IsLawful q' := (D.rows.printedRespects_omega_one_iff
      hD.isWellFormed.isWellFormed.gradedIndex_mem hD.isCoded.atStage_omega_one hq').mp hres
    obtain ⟨y, q, ⟨hq, hqD, hpat⟩, he⟩ := realizesOver_iff_exists_tupleEval.mp
      (hR.bottomPattern_of_isLawful hα o hD hf hp hl hext)
    refine ⟨y, q, ⟨hq, hqD, fun i j hij hj ↦ hpat i j hij ?_⟩, he⟩
    rw [grade_congr hqD hij]
    exact ((CellScheme.gradedIndex_le_iff _).mp hj).2
  uniformity n x p h γ hγ _ hγα := by
    have hx := injective_of_tupleEval_eq_some h
    let o : R.Occurrence := ⟨n, ⟨x, hx⟩, p, (tupleEval_eq_eval hx).symm.trans h⟩
    obtain ⟨y, q, ⟨hq, d, hd⟩, he⟩ := realizesOver_iff_exists_tupleEval.mp
      ((hR.uniformity o γ hγ hγα).inter_cofaces hR.isConsistent hR.isLegal)
    exact ⟨y, q, ⟨hq, _, ⟨d, rfl⟩, hd⟩, he⟩
  dominance n x p h γ hγα := by
    have hx := injective_of_tupleEval_eq_some h
    let o : R.Occurrence := ⟨n, ⟨x, hx⟩, p, (tupleEval_eq_eval hx).symm.trans h⟩
    obtain ⟨y, q, ⟨hq, hd⟩, he⟩ := realizesOver_iff_exists_tupleEval.mp
      ((hR.dominance o γ hγα).inter_cofaces hR.isConsistent hR.isLegal)
    exact ⟨y, q, ⟨hq, hd⟩, he⟩

/-- **Models as printed are models** [Kni26, Definition 3.2.1]: at a stage `α ≤ ω₁` that is zero
or a limit, a realization satisfying every printed clause is a model. -/
theorem PrintedModel.isModel (h : PrintedModel α R.tupleEval) (hα : Order.IsSuccPrelimit α)
    (hαω : α ≤ Ordinal.omega.{u} 1) : R.IsModel := by
  have hcons : R.IsConsistent := fun m n t p f ht ↦ by
    obtain ⟨h₁, h₂⟩ := h.consistency n t p ((tupleEval_embedding t).trans ht) m f
    rw [← tupleEval_embedding (f.trans t)]
    cases hq : restrictFace f p with
    | none => exact h₂ hq
    | some q => exact h₁ q hq
  have htuple (o : R.Occurrence) : R.tupleEval o.arity o.tuple = some o.type :=
    (tupleEval_embedding _).trans o.eval_tuple
  refine ⟨h.nonempty, fun n t p ht ↦ h.isLegal_of_eq_some n t t.injective p
    ((tupleEval_embedding t).trans ht), hcons, ?_, fun o D hne ↦ ?_, fun o D ρ hne ↦ ?_,
    fun o γ hγ hγα ↦ ?_, fun o γ hγα ↦ ?_⟩
  · refine (isCovering_iff_exists_castAdd hcons).mpr fun n t ↦ ?_
    obtain ⟨k, x, hs⟩ := h.covering n t t.injective
    have hinj := injective_of_tupleEval_isSome hs
    refine ⟨k, ⟨_, hinj⟩, ?_, by rwa [← tupleEval_eq_eval hinj]⟩
    ext i
    simp
  · obtain ⟨hD, -, hp⟩ := (nonempty_cofaces_inter_saturationFamily_iff hα).mp hne
    obtain ⟨y, q, ⟨-, hqD⟩, he⟩ := h.saturation _ _ _ (htuple o) D hD hp
    exact realizesOver_iff_exists_tupleEval.mpr ⟨y, q, hqD, he⟩
  · obtain ⟨q₀, hq₀, hq₀D, hpat₀⟩ := hne
    subst hq₀D
    obtain ⟨hf, hqp⟩ := (restrictFace_eq_some_iff _ _).mp hq₀.2
    have hat (d : Fin q₀.card) : AtStage (Ordinal.omega.{u} 1) (q₀.label d) :=
      (q₀.atStage d).mono hαω
    have hres := (q₀.rows.printedRespects_omega_one_iff
      hq₀.1.isWellFormed.isWellFormed.gradedIndex_mem hq₀.1.isCoded.atStage_omega_one hat).mpr
      q₀.isLawful
    obtain ⟨y, q, ⟨-, hqD, hpat⟩, he⟩ := h.bottomPattern _ _ _ (htuple o) q₀.toScheme hq₀.1
      (comap_toScheme_of_mem_cofaces hq₀) q₀.label hat hres fun i j hij ↦ label_congr hqp hij
    refine realizesOver_iff_exists_tupleEval.mpr ⟨y, q, ⟨hqD, fun i j hij hg ↦ ?_⟩, he⟩
    have hgj : q₀.toCellScheme.grade j ≤ o.arity := (grade_congr hqD hij).symm.trans_le hg
    rw [hpat i j hij ((CellScheme.gradedIndex_le_iff _).mpr ⟨subset_univ _, hgj⟩)]
    exact hpat₀ j j rfl hgj
  · obtain ⟨y, q, ⟨-, _, ⟨d, rfl⟩, hd⟩, he⟩ :=
      h.uniformity _ _ _ (htuple o) γ hγ zero_le hγα
    exact realizesOver_iff_exists_tupleEval.mpr ⟨y, q, ⟨d, hd⟩, he⟩
  · obtain ⟨y, q, ⟨-, hd⟩, he⟩ := h.dominance _ _ _ (htuple o) γ hγα
    exact realizesOver_iff_exists_tupleEval.mpr ⟨y, q, hd, he⟩

/-- **Models are the models as printed** [Kni26, Definition 3.2.1]: at a stage `α ≤ ω₁` that is
zero or a limit, a realization, read on all finite tuples, is a model as printed exactly when it
is a model. -/
theorem printedModel_tupleEval_iff (hα : Order.IsSuccPrelimit α)
    (hαω : α ≤ Ordinal.omega.{u} 1) : PrintedModel α R.tupleEval ↔ R.IsModel :=
  ⟨fun h ↦ h.isModel hα hαω, fun h ↦ h.printedModel hα⟩

end Realization

end VaughtConjecture
