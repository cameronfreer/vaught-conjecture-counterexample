/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.Model

/-!
# Partial realizations of stage charts

A stage type `P` on `k` points is a finite **chart**: a tuple `f : Fin n ↪ Fin k` of its points
has the type `restrictFace f P` of the face it spans when that face is closed, and no type when it
is not.  This module reads a chart as a realization, on its own points and on `ℕ`.

**The face realization of a chart** (`StageType.faceRealization`) is the realization on `Fin k`
whose evaluation is the face map of the chart.  It is exactly consistent, by the guarded
composition law of face maps (`StageType.restrictFace_trans`), covering, since every tuple of
points is a face of the identity tuple, and its types are legal when the chart is
(`StageType.isConsistent_faceRealization`, `StageType.isCovering_faceRealization`,
`StageType.hasLegalTypes_faceRealization`).

**Supported tuples.**  A chart on `k` points is placed on the initial segment `{0, …, k - 1}` of
`ℕ`.  A tuple `t : Fin n ↪ ℕ` is **supported** by the chart (`StageType.IsSupported k t`) when its
points lie in that segment; it then spans the face `IsSupported.face` of the chart.  Faces of a
supported tuple are supported (`IsSupported.trans`), and a supported tuple stays supported by
every larger chart (`IsSupported.mono`).

**The partial realization of a chart** (`StageType.chartRealization`) is the face realization
placed on `ℕ`: it gives a supported tuple the type of the face it spans, and an unsupported tuple
no type.  There are therefore two kinds of untyped tuples:

* a **supported invisible** tuple: its points are points of the chart, but they do not span a
  closed face (`StageType.chartRealization_eval_eq_none_iff`).  This is a property of the chart:
  a larger chart whose face on `{0, …, k - 1}` is the given chart gives every supported tuple the
  same evaluation (`StageType.chartRealization_eval_of_restrictFace_eq_some`), so the tuple stays
  untyped there;
* an **unsupported** tuple: some point is not a point of the chart
  (`StageType.chartRealization_eval_of_not_isSupported`).  The chart says nothing about it, and a
  larger chart containing its points may give it a type.

The partial realization of a chart is exactly consistent
(`StageType.isConsistent_chartRealization`), its types are legal when the chart is
(`StageType.hasLegalTypes_chartRealization`), it gives the points of the chart, in order, the type
of the whole chart (`StageType.chartRealization_eval_valEmbedding`), and its typed tuples are
supported (`StageType.isSupported_of_isSome_chartRealization_eval`).  It is not covering: a point
outside `{0, …, k - 1}` lies in no typed tuple.

**Role.**  The face realization of a chart gives the relations of the finite structure of the
chart on its points (roadmap, Layer 2): its visible faces with their types, an invisible face
carrying no relation.  The partial realization is its placement on `ℕ`, and restricted to the
points `{0, …, k - 1}` it gives the same relations.  It is the local input of the reconstruction
of a realization from the classical limit of the age of top-free charts: the evaluation at a
tuple of the limit is the evaluation at a tuple of the points of one chart through which it
factors, a supported tuple.  Exact consistency of the reconstruction is therefore checked in one
partial realization.

## Placement

The use of these statements in the construction of the top-free witnesses (the finite charts, the
reconstruction of partial evaluation, and its exact consistency) is described in
`roadmap/README.md`, Layer 2 and "The top-free witnesses: the finite age and its classical limit".

## References

Realizations, exact consistency, and covering are [Kni26, Definition 3.2.1], clauses 2 and 3, for
R. W. Knight, *A counterexample to Vaught's Conjecture using generalised Stone spaces* (draft,
20 February 2026).  The partial realization of a chart and the distinction between supported
invisible and unsupported tuples make explicit the finite charts of the construction of
[Kni26, Proposition 4.4.5].
-/

universe u

namespace VaughtConjecture

open Finset

variable {α : Ordinal.{u}} {k m n : ℕ}

namespace StageType

/-! ### Supported tuples -/

/-- A tuple of natural numbers is **supported** by a chart on `k` points when its points lie in the
initial segment `{0, …, k - 1}`. -/
def IsSupported (k : ℕ) (t : Fin n ↪ ℕ) : Prop :=
  ∀ i, t i < k

instance (k : ℕ) (t : Fin n ↪ ℕ) : Decidable (IsSupported k t) :=
  inferInstanceAs (Decidable (∀ i, t i < k))

namespace IsSupported

variable {t : Fin n ↪ ℕ}

/-- The face of a chart on `k` points spanned by a supported tuple. -/
def face (h : IsSupported k t) : Fin n ↪ Fin k :=
  ⟨fun i ↦ ⟨t i, h i⟩, fun _ _ hij ↦ t.injective (congrArg Fin.val hij)⟩

/-- The points of the face spanned by a supported tuple are the points of the tuple. -/
@[simp] theorem val_face (h : IsSupported k t) (i : Fin n) : (h.face i : ℕ) = t i :=
  rfl

/-- A supported tuple is its face, placed on the initial segment. -/
@[simp] theorem face_trans_valEmbedding (h : IsSupported k t) :
    h.face.trans Fin.valEmbedding = t :=
  rfl

/-- A supported tuple is supported by every larger chart. -/
theorem mono (h : IsSupported k t) (hk : k ≤ m) : IsSupported m t :=
  fun i ↦ (h i).trans_le hk

/-- In a larger chart, the face of a supported tuple is its face in the smaller chart, moved along
the initial segment. -/
theorem face_mono (h : IsSupported k t) (hk : k ≤ m) :
    (h.mono hk).face = h.face.trans (Fin.castLEEmb hk) :=
  rfl

/-- Faces of a supported tuple are supported. -/
theorem trans (h : IsSupported k t) (f : Fin m ↪ Fin n) : IsSupported k (f.trans t) :=
  fun i ↦ h (f i)

/-- The face spanned by a face of a supported tuple is the composite face. -/
theorem face_trans (h : IsSupported k t) (f : Fin m ↪ Fin n) :
    (h.trans f).face = f.trans h.face :=
  rfl

end IsSupported

/-- A face of the chart, placed on the initial segment, is supported. -/
theorem isSupported_trans_valEmbedding (f : Fin n ↪ Fin k) :
    IsSupported k (f.trans Fin.valEmbedding) :=
  fun i ↦ (f i).isLt

/-- The face spanned by a face of the chart, placed on the initial segment, is that face. -/
@[simp] theorem face_isSupported_trans_valEmbedding (f : Fin n ↪ Fin k) :
    (isSupported_trans_valEmbedding f).face = f :=
  rfl

/-! ### The face realization of a chart -/

variable (P : StageType.{u} α k)

/-- The **face realization** of a chart: the realization on its points `Fin k` in which a tuple of
points has the type of the face it spans, and no type when that face is not closed. -/
noncomputable def faceRealization : Realization.{u, 0} α (Fin k) where
  eval f := restrictFace f P

variable {P}

/-- A tuple of points of a chart has, in its face realization, the type of the face it spans. -/
@[simp] theorem faceRealization_eval (f : Fin n ↪ Fin k) :
    P.faceRealization.eval f = restrictFace f P :=
  rfl

/-- **The face realization of a chart is exactly consistent**: face maps compose. -/
theorem isConsistent_faceRealization : P.faceRealization.IsConsistent :=
  fun _ _ t _ f h ↦ (restrictFace_trans P t f h).symm

/-- **The face realization of a chart is covering**: every tuple of points is a face of the
identity tuple, which has the type of the whole chart. -/
theorem isCovering_faceRealization : P.faceRealization.IsCovering :=
  fun _ t ↦ ⟨k, Function.Embedding.refl _, t, by ext; simp, by simp⟩

/-- The types of the face realization of a legal chart are legal. -/
theorem hasLegalTypes_faceRealization (hP : P.IsLegal) : P.faceRealization.HasLegalTypes :=
  fun _ t _ h ↦ hP.restrictFace t h

/-! ### The partial realization of a chart -/

variable (P)

/-- The **partial realization of a chart** on the initial segment `{0, …, k - 1}` of `ℕ`: the face
realization placed on `ℕ`.  A supported tuple has the type of the face it spans, and an
unsupported tuple has no type. -/
noncomputable def chartRealization : Realization.{u, 0} α ℕ where
  eval t := if h : IsSupported k t then P.faceRealization.eval h.face else none

variable {P} {t : Fin n ↪ ℕ}

/-- A supported tuple has the type of the face it spans. -/
theorem chartRealization_eval_of_isSupported (h : IsSupported k t) :
    P.chartRealization.eval t = restrictFace h.face P :=
  dite_eq_left h

/-- **Unsupported tuples** have no type: the chart says nothing about them. -/
theorem chartRealization_eval_of_not_isSupported (h : ¬ IsSupported k t) :
    P.chartRealization.eval t = none :=
  dite_eq_right h

/-- **Supported invisible tuples**: a supported tuple has no type exactly when the face it spans is
not closed. -/
theorem chartRealization_eval_eq_none_iff (h : IsSupported k t) :
    P.chartRealization.eval t = none ↔ univ.map h.face ∉ P.toCellScheme.faces := by
  rw [chartRealization_eval_of_isSupported h, restrictFace_eq_none_iff]

/-- A typed tuple is supported. -/
theorem isSupported_of_isSome_chartRealization_eval (h : (P.chartRealization.eval t).isSome) :
    IsSupported k t := by
  by_contra hn
  rw [chartRealization_eval_of_not_isSupported hn] at h
  exact Bool.false_ne_true h

/-- A face of the chart, placed on the initial segment, has the type of that face. -/
@[simp] theorem chartRealization_eval_trans_valEmbedding (f : Fin n ↪ Fin k) :
    P.chartRealization.eval (f.trans Fin.valEmbedding) = restrictFace f P :=
  chartRealization_eval_of_isSupported (isSupported_trans_valEmbedding f)

/-- The points of the chart, in order, have the type of the whole chart. -/
@[simp] theorem chartRealization_eval_valEmbedding :
    P.chartRealization.eval (Fin.valEmbedding : Fin k ↪ ℕ) = some P := by
  simpa using chartRealization_eval_trans_valEmbedding (P := P) (Function.Embedding.refl _)

/-- **Restriction to a smaller chart**: if the face of a chart `Q` on the initial segment
`{0, …, k - 1}` is the chart `P`, then `Q` gives every tuple supported by `P` its evaluation in the
partial realization of `P`.  Typed tuples keep their types, and supported invisible tuples stay
untyped. -/
theorem chartRealization_eval_of_restrictFace_eq_some (hk : k ≤ m) {Q : StageType.{u} α m}
    (hQ : restrictFace (Fin.castLEEmb hk) Q = some P) (h : IsSupported k t) :
    Q.chartRealization.eval t = P.chartRealization.eval t := by
  rw [chartRealization_eval_of_isSupported (h.mono hk), chartRealization_eval_of_isSupported h,
    h.face_mono hk, ← restrictFace_trans Q _ _ hQ]

/-- **The partial realization of a chart is exactly consistent.** -/
theorem isConsistent_chartRealization : P.chartRealization.IsConsistent := by
  intro m n t p f ht
  have hs : IsSupported k t := isSupported_of_isSome_chartRealization_eval (by rw [ht]; rfl)
  rw [chartRealization_eval_of_isSupported hs] at ht
  rw [chartRealization_eval_of_isSupported (hs.trans f), hs.face_trans]
  exact (restrictFace_trans P _ f ht).symm

/-- The types of the partial realization of a legal chart are legal. -/
theorem hasLegalTypes_chartRealization (hP : P.IsLegal) : P.chartRealization.HasLegalTypes := by
  intro n t p ht
  have hs : IsSupported k t := isSupported_of_isSome_chartRealization_eval (by rw [ht]; rfl)
  rw [chartRealization_eval_of_isSupported hs] at ht
  exact hP.restrictFace _ ht

end StageType

end VaughtConjecture
