/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Logic.Equiv.Fintype
import VaughtConjecture.Stage.Basic

/-!
# Realizations: exact partial evaluation, consistency, and covering

Roadmap, Library conventions (raw data separate from their laws; an occurrence owns its literal
tuple and evaluated type) and Layer 2 (realizations with exact partial evaluation, consistency,
and covering); semantic contract, items 4–5 (a tuple's partial type is exact under face maps;
absence of a face is mathematical information; the original exact consistency and covering
clauses); the expositions, §1.

A **realization** `R : Realization α M` at stage `α` on a carrier `M` assigns to every injective
finite tuple `t : Fin n ↪ M` an optional stage type `R.eval t : Option (StageType α n)`.  It is
raw data.  Its two structural laws are separate propositions:

* **exact consistency** (`Realization.IsConsistent`): for every tuple `t` with an actual type
  `R.eval t = some p` and every `f : Fin m ↪ Fin n`, the face tuple `f.trans t` has exactly the
  partial restriction, `R.eval (f.trans t) = restrictFace f p`.  This includes the `none` case:
  an invisible face of a typed tuple is untyped.  The law is conditional on an actual parent; it
  says nothing about the subtuples of an untyped tuple, which may or may not be typed.
* **covering** (`Realization.IsCovering`): every injective finite tuple is a face
  `f.trans u` of a typed tuple `u`.

An **occurrence** (`Realization.Occurrence`) is a typed tuple together with its type.  Under
consistency every visible face of an occurrence is an occurrence with its literal face tuple
(`Realization.eval_face`, `Realization.Occurrence.face`), and reindexing a tuple along a
bijection of coordinates reindexes its type, including definedness
(`Realization.eval_equiv_trans`, `Realization.Occurrence.reindex`).  Under consistency, covering
is equivalent to the form of the source, with the given tuple as an *initial segment* of a typed
tuple (`Realization.IsCovering.exists_castAdd`, `Realization.isCovering_iff_exists_castAdd`).

## References

Realizations are the models of [Kni26, Definition 3.2.1] without the existential-closure clause:
consistency is its clause 2 and covering its clause 3, for R. W. Knight, *A counterexample to
Vaught's Conjecture using generalised Stone spaces* (draft, 20 February 2026).
-/

universe u v

namespace VaughtConjecture

open Finset

/-- A **realization** at stage `α` on the carrier `M`: an optional stage type for every injective
finite tuple.  This is raw data; the laws are `Realization.IsConsistent` and
`Realization.IsCovering`. -/
structure Realization (α : Ordinal.{u}) (M : Type v) where
  /-- The partial evaluation: the type of an injective tuple, if it has one. -/
  eval {n : ℕ} : (Fin n ↪ M) → Option (StageType.{u} α n)

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {m n k : ℕ} (R : Realization.{u, v} α M)

/-- **Extensionality** for realizations: equal evaluations at every tuple. -/
@[ext] theorem ext {R R' : Realization.{u, v} α M}
    (h : ∀ {n : ℕ} (t : Fin n ↪ M), R.eval t = R'.eval t) : R = R' := by
  obtain ⟨e⟩ := R
  obtain ⟨e'⟩ := R'
  congr
  funext n t
  exact h t

/-- **Exact consistency** [Kni26, §3.2]: every face of a typed tuple has exactly the partial
restriction of its type, including `none` at an invisible face.  Nothing is required of the faces
of an untyped tuple. -/
def IsConsistent : Prop :=
  ∀ ⦃m n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n) (f : Fin m ↪ Fin n),
    R.eval t = some p → R.eval (f.trans t) = StageType.restrictFace f p

/-- **Covering** [Kni26, §3.2]: every injective finite tuple is a face of a typed tuple. -/
def IsCovering : Prop :=
  ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M),
    ∃ (m : ℕ) (u : Fin m ↪ M) (f : Fin n ↪ Fin m), f.trans u = t ∧ (R.eval u).isSome

/-! ### Occurrences -/

/-- An **occurrence** in a realization: a typed tuple with its type. -/
structure Occurrence where
  /-- The number of points. -/
  arity : ℕ
  /-- The literal tuple. -/
  tuple : Fin arity ↪ M
  /-- The evaluated type. -/
  type : StageType.{u} α arity
  /-- The type is the evaluation of the tuple. -/
  eval_tuple : R.eval tuple = some type

attribute [simp] Occurrence.eval_tuple

variable {R}

/-- **Faces of an occurrence**: under consistency, the face of an occurrence along `f` has
exactly the partial restriction of its type. -/
theorem eval_face (hR : R.IsConsistent) (x : R.Occurrence) (f : Fin m ↪ Fin x.arity) :
    R.eval (f.trans x.tuple) = StageType.restrictFace f x.type :=
  hR _ _ f x.eval_tuple

/-- A face of an occurrence is typed exactly when it is a closed face of its type. -/
theorem isSome_eval_face_iff (hR : R.IsConsistent) (x : R.Occurrence) (f : Fin m ↪ Fin x.arity) :
    (R.eval (f.trans x.tuple)).isSome ↔ univ.map f ∈ x.type.toCellScheme.faces := by
  rw [eval_face hR, StageType.isSome_restrictFace_iff]

/-- A typed face of a typed tuple determines the restriction of the parent type. -/
theorem restrictFace_eq_of_eval (hR : R.IsConsistent) {t : Fin n ↪ M} {p : StageType.{u} α n}
    (ht : R.eval t = some p) (f : Fin m ↪ Fin n) {q : StageType.{u} α m}
    (hq : R.eval (f.trans t) = some q) : StageType.restrictFace f p = some q :=
  (hR t p f ht).symm.trans hq

namespace Occurrence

section LiteralFace

variable (hR : R.IsConsistent) {x y : R.Occurrence} {f : Fin x.arity ↪ Fin y.arity}
include hR

/-- **Literal faces**: if the tuple of `x` is the face of the tuple of `y` along `f`, the type of
`y` restricts along `f` to the type of `x`. -/
theorem restrictFace_eq_some_of_trans_eq (hf : f.trans y.tuple = x.tuple) :
    StageType.restrictFace f y.type = some x.type := by
  rw [← eval_face hR, hf, x.eval_tuple]

/-- **Literal faces keep labels and grades**: every cell of the type of a literal face has a cell
of the type of the larger occurrence with the same label and the same grade. -/
theorem exists_label_grade_eq_of_trans_eq (hf : f.trans y.tuple = x.tuple)
    (j : Fin x.type.card) : ∃ z : Fin y.type.card, y.type.label z = x.type.label j ∧
      y.type.toCellScheme.grade z = x.type.toCellScheme.grade j := by
  obtain ⟨hmem, h⟩ :=
    (StageType.restrictFace_eq_some_iff _ _).mp (restrictFace_eq_some_of_trans_eq hR hf)
  have hgrade : ∀ {t t' : StageType.{u} α x.arity} (_ : t = t') (i : Fin t.card) (i' : Fin t'.card),
      (i : ℕ) = i' → t.toCellScheme.grade i = t'.toCellScheme.grade i' := by
    rintro t _ rfl i i' hii'
    rw [Fin.ext hii']
  exact ⟨_, StageType.label_congr h (i := Fin.cast (congrArg (·.card) h).symm j) rfl,
    hgrade h (Fin.cast (congrArg (·.card) h).symm j) j rfl⟩

/-- Every label of a literal face is a label of the larger occurrence (the labels of
`exists_label_grade_eq_of_trans_eq`). -/
theorem exists_label_eq_of_trans_eq (hf : f.trans y.tuple = x.tuple) (j : Fin x.type.card) :
    ∃ z : Fin y.type.card, y.type.label z = x.type.label j :=
  (exists_label_grade_eq_of_trans_eq hR hf j).imp fun _ ↦ And.left

end LiteralFace

/-- The **face** of an occurrence along a closed face `f` of its type: the literal face tuple with
the restricted type. -/
noncomputable def face (hR : R.IsConsistent) (x : R.Occurrence) (f : Fin m ↪ Fin x.arity)
    (hf : univ.map f ∈ x.type.toCellScheme.faces) : R.Occurrence where
  arity := m
  tuple := f.trans x.tuple
  type := x.type.comap f hf
  eval_tuple := by rw [eval_face hR, StageType.restrictFace_of_mem _ _ hf]

/-- The tuple of a face is the literal face tuple. -/
@[simp] theorem face_tuple (hR : R.IsConsistent) (x : R.Occurrence) (f : Fin m ↪ Fin x.arity)
    (hf : univ.map f ∈ x.type.toCellScheme.faces) : (x.face hR f hf).tuple = f.trans x.tuple :=
  rfl

/-- The type of a face is the restriction of the type. -/
@[simp] theorem face_type (hR : R.IsConsistent) (x : R.Occurrence) (f : Fin m ↪ Fin x.arity)
    (hf : univ.map f ∈ x.type.toCellScheme.faces) : (x.face hR f hf).type = x.type.comap f hf :=
  rfl

end Occurrence

/-! ### Reindexing along bijections of coordinates -/

/-- **Reindexing a typed tuple**: along a bijection `e` of coordinates, the reindexed tuple has
the reindexed type. -/
theorem eval_equiv_trans_of_eval (hR : R.IsConsistent) {t : Fin n ↪ M} {p : StageType.{u} α n}
    (ht : R.eval t = some p) (e : Fin m ≃ Fin n) :
    R.eval (e.toEmbedding.trans t) = some (p.reindex e) := by
  rw [hR t p _ ht, StageType.restrictFace_equiv]

/-- **Permutation invariance of evaluation**: reindexing a tuple along a bijection of
coordinates reindexes its evaluation; in particular it is typed exactly when the original tuple
is. -/
theorem eval_equiv_trans (hR : R.IsConsistent) (t : Fin n ↪ M) (e : Fin m ≃ Fin n) :
    R.eval (e.toEmbedding.trans t) = (R.eval t).map (StageType.reindex · e) := by
  cases ht : R.eval t with
  | some p => exact eval_equiv_trans_of_eval hR ht e
  | none =>
    cases hs : R.eval (e.toEmbedding.trans t) with
    | none => rfl
    | some q =>
      have h := eval_equiv_trans_of_eval hR hs e.symm
      rw [← Function.Embedding.trans_assoc, ← Equiv.trans_toEmbedding, Equiv.symm_trans_self,
        Equiv.refl_toEmbedding, Function.Embedding.refl_trans, ht] at h
      exact absurd h (Option.some_ne_none _).symm

/-- A tuple reindexed along a bijection of coordinates is typed exactly when the original tuple
is. -/
@[simp] theorem isSome_eval_equiv_trans (hR : R.IsConsistent) (t : Fin n ↪ M)
    (e : Fin m ≃ Fin n) : (R.eval (e.toEmbedding.trans t)).isSome = (R.eval t).isSome := by
  rw [eval_equiv_trans hR, Option.isSome_map]

/-- The **reindexing** of an occurrence along a bijection of coordinates. -/
noncomputable def Occurrence.reindex (hR : R.IsConsistent) (x : R.Occurrence)
    (e : Fin m ≃ Fin x.arity) : R.Occurrence where
  arity := m
  tuple := e.toEmbedding.trans x.tuple
  type := x.type.reindex e
  eval_tuple := eval_equiv_trans_of_eval hR x.eval_tuple e

/-- The tuple of a reindexed occurrence is the reindexed tuple. -/
@[simp] theorem Occurrence.reindex_tuple (hR : R.IsConsistent) (x : R.Occurrence)
    (e : Fin m ≃ Fin x.arity) : (x.reindex hR e).tuple = e.toEmbedding.trans x.tuple :=
  rfl

/-- The type of a reindexed occurrence is the reindexed type. -/
@[simp] theorem Occurrence.reindex_type (hR : R.IsConsistent) (x : R.Occurrence)
    (e : Fin m ≃ Fin x.arity) : (x.reindex hR e).type = x.type.reindex e :=
  rfl

/-! ### Covering -/

/-- Under covering there is an occurrence (a typed tuple, for instance one covering the empty
tuple). -/
theorem IsCovering.nonempty_occurrence (hc : R.IsCovering) : Nonempty R.Occurrence := by
  obtain ⟨m, u, -, -, hu⟩ := hc (Function.Embedding.ofIsEmpty : Fin 0 ↪ M)
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hu
  exact ⟨⟨m, u, p, hp⟩⟩

/-- **Covering by initial segments** [Kni26, §3.2]: under consistency and covering, every
injective tuple is the initial segment of a typed tuple.  The covering typed tuple is reindexed
so that the given tuple comes first. -/
theorem IsCovering.exists_castAdd (hR : R.IsConsistent) (hc : R.IsCovering) (t : Fin n ↪ M) :
    ∃ (k : ℕ) (u : Fin (n + k) ↪ M), (Fin.castAddEmb k).trans u = t ∧ (R.eval u).isSome := by
  obtain ⟨m, u, f, rfl, hu⟩ := hc t
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le
    (by simpa using Fintype.card_le_of_embedding f : n ≤ m)
  obtain ⟨e, he⟩ :=
    Equiv.Perm.exists_extending_pair (Fin.castAdd k) f (Fin.castAdd_injective n k) f.injective
  refine ⟨k, e.toEmbedding.trans u, ?_, by rwa [isSome_eval_equiv_trans hR]⟩
  ext i
  simp [he]

/-- **Covering by initial segments, characterized**: an exactly consistent realization is covering
exactly when every injective tuple is the initial segment of a typed tuple. -/
theorem isCovering_iff_exists_castAdd (hR : R.IsConsistent) :
    R.IsCovering ↔ ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), ∃ (k : ℕ) (u : Fin (n + k) ↪ M),
      (Fin.castAddEmb k).trans u = t ∧ (R.eval u).isSome := by
  refine ⟨fun hc _ ↦ hc.exists_castAdd hR, fun h n t ↦ ?_⟩
  obtain ⟨k, u, hu, hs⟩ := h t
  exact ⟨_, u, _, hu, hs⟩

end Realization

end VaughtConjecture
