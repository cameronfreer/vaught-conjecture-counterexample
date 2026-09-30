/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Language.Structure

/-!
# Finite partial realizations and unions of chains

Roadmap, Layer 2 (the countable chain construction: a condition has one finite master chart, and
its partial realization is derived from it rather than stored as a second synchronized state; a
supported invisible face is distinguished from an unsupported tuple; the union theorem is
established once); semantic contract, items 4–5 (a tuple's partial type is exact under face maps;
absence of a face is mathematical information).

**The partial realization of a chart.**  A stage type `P` on `k` points is a *finite master
chart*: a tuple `t : Fin n ↪ Fin k` of its points has the type `restrictFace t P` of the face it
spans, if that face is closed, and these types are exactly consistent by the guarded composition
law of face maps (`StageType.restrictFace_trans`).

The countable carrier of the construction is `ℕ`, and a chart on `k` points is placed on the
initial segment `{0, …, k - 1}`.  A tuple `t : Fin n ↪ ℕ` is **supported** by the chart
(`Construction.IsSupported k t`) when its points lie in that segment; it then spans the face
`IsSupported.face` of the chart.  The **partial realization of the chart**
(`StageType.chartRealization`) gives a supported tuple the type of its face, and an unsupported
tuple no type.  There are therefore two kinds of untyped tuples:

* a **supported invisible** tuple: its points are points of the chart, but they do not span a
  closed face (`StageType.chartRealization_eval_eq_none_iff`).  This is exact information about
  the chart, and it is never revised: every extension of the chart keeps it untyped;
* an **unsupported** tuple: some point is not yet a point of the chart
  (`StageType.chartRealization_eval_of_not_isSupported`).  Nothing has been decided about it; a
  later chart containing its points may type it.

The partial realization of a chart is exactly consistent (`StageType.isConsistent_chartRealization`)
and has the types of the faces of the chart, which are legal when the chart is
(`StageType.hasLegalTypes_chartRealization`); it covers exactly the supported tuples.

**Conditions and extension.**  A **condition** (`Construction.Condition α`) is a legal master
chart at stage `α` on an initial segment of `ℕ`, and its partial realization
(`Condition.realization`) is derived from the chart.  A condition `d` **extends** `c`
(`c ≤ d`) when `d` has at least as many points and the face of the chart of `d` on the points of
`c` is literally the chart of `c`.  This is a preorder, and under it the partial realization of
`d` restricts exactly to that of `c` on the supported tuples of `c`
(`Condition.realization_eval_of_le`): typed tuples keep their types and supported invisible tuples
stay invisible.  A one-point extension of the chart is an extension of the condition
(`Condition.snoc`, `Condition.le_snoc`).

**Unions of chains.**  The **union** of a sequence of conditions (`Construction.chainUnion`) gives
a tuple the type it has in the first condition supporting it.  Along a monotone sequence the
evaluations stabilize, so this is its type in every condition supporting it
(`chainUnion_eval_of_isSupported`); in particular the union of a constant sequence is the partial
realization of its condition (`chainUnion_const`).  The union of a monotone sequence is exactly
consistent (`isConsistent_chainUnion`) and has legal types (`hasLegalTypes_chainUnion`), and it is
covering exactly when every point of `ℕ` is eventually a point of the chart
(`isCovering_chainUnion_iff`).

## References

Realizations, exact consistency, and covering are [Kni26, Definition 3.2.1], clauses 2 and 3, for
R. W. Knight, *A counterexample to Vaught's Conjecture using generalised Stone spaces* (draft,
20 February 2026).  The finite master chart, its derived partial realization, and the distinction
between supported invisible and unsupported tuples are the bookkeeping of the chain construction
of [Kni26, Proposition 4.4.5], made explicit.
-/

universe u

namespace VaughtConjecture

open Finset

variable {α : Ordinal.{u}} {k m n : ℕ}

/-! ### Supported tuples -/

namespace Construction

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

/-- The tuples supported by some chart in a sequence whose number of points is unbounded: every
tuple is supported from some index on. -/
theorem exists_isSupported {c : ℕ → ℕ} (hc : ∀ j, ∃ i, j < c i) (t : Fin n ↪ ℕ) :
    ∃ i, IsSupported (c i) t := by
  obtain ⟨i, hi⟩ := hc (univ.sup t)
  exact ⟨i, fun j ↦ (le_sup (f := t) (mem_univ j)).trans_lt hi⟩

end Construction

/-! ### The partial realization of a chart -/

namespace StageType

open Construction

variable (P : StageType.{u} α k)

/-- The **partial realization of a chart** on the initial segment `{0, …, k - 1}` of `ℕ`: a
supported tuple has the type of the face it spans, and an unsupported tuple has no type. -/
noncomputable def chartRealization : Realization.{u, 0} α ℕ where
  eval t := if h : IsSupported k t then restrictFace h.face P else none

variable {P} {t : Fin n ↪ ℕ}

/-- A supported tuple has the type of the face it spans. -/
theorem chartRealization_eval_of_isSupported (h : IsSupported k t) :
    P.chartRealization.eval t = restrictFace h.face P :=
  dite_eq_left h

/-- **Unsupported tuples** have no type: nothing has been decided about them yet. -/
theorem chartRealization_eval_of_not_isSupported (h : ¬ IsSupported k t) :
    P.chartRealization.eval t = none :=
  dite_eq_right h

/-- **Supported invisible tuples**: a supported tuple has no type exactly when the face it spans is
not closed. -/
theorem chartRealization_eval_eq_none_iff (h : IsSupported k t) :
    P.chartRealization.eval t = none ↔ univ.map h.face ∉ P.toCellScheme.faces := by
  rw [chartRealization_eval_of_isSupported h, restrictFace_eq_none_iff]

/-- A typed tuple is supported. -/
theorem isSupported_of_isSome (h : (P.chartRealization.eval t).isSome) : IsSupported k t := by
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

/-- The partial realization of a chart is exactly consistent. -/
theorem isConsistent_chartRealization : P.chartRealization.IsConsistent := by
  intro m n t p f ht
  have hs : IsSupported k t := isSupported_of_isSome (by rw [ht]; rfl)
  rw [chartRealization_eval_of_isSupported hs] at ht
  rw [chartRealization_eval_of_isSupported (hs.trans f), hs.face_trans]
  exact (restrictFace_trans P _ f ht).symm

/-- The types of the partial realization of a legal chart are legal. -/
theorem hasLegalTypes_chartRealization (hP : P.IsLegal) : P.chartRealization.HasLegalTypes := by
  intro n t p ht
  have hs : IsSupported k t := isSupported_of_isSome (by rw [ht]; rfl)
  rw [chartRealization_eval_of_isSupported hs] at ht
  exact hP.restrictFace _ ht

end StageType

/-! ### Conditions -/

namespace Construction

open StageType

/-- A **condition** at stage `α`: a legal finite master chart, placed on the initial segment of
`ℕ` with as many points.  Its partial realization is derived from the chart
(`Condition.realization`). -/
structure Condition (α : Ordinal.{u}) where
  /-- The number of points. -/
  card : ℕ
  /-- The master chart. -/
  chart : StageType.{u} α card
  /-- The master chart is legal. -/
  isLegal : chart.IsLegal

namespace Condition

variable (c d e : Condition.{u} α)

/-- The **partial realization** of a condition: the partial realization of its master chart. -/
noncomputable def realization : Realization.{u, 0} α ℕ :=
  c.chart.chartRealization

/-- Extension of conditions: `c ≤ d` when `d` has at least as many points and the face of the
chart of `d` on the points of `c` is literally the chart of `c`. -/
instance : Preorder (Condition.{u} α) where
  le c d := ∃ h : c.card ≤ d.card, restrictFace (Fin.castLEEmb h) d.chart = some c.chart
  le_refl c := ⟨le_rfl, by
    rw [show Fin.castLEEmb (le_refl c.card) = Function.Embedding.refl _ from
      Function.Embedding.ext fun _ ↦ rfl, restrictFace_refl]⟩
  le_trans c d e := fun ⟨h, hcd⟩ ⟨h', hde⟩ ↦ ⟨h.trans h', by
    rw [← hcd, restrictFace_trans e.chart _ _ hde]
    rfl⟩

variable {c d e}

/-- Extension of conditions, unfolded. -/
theorem le_def : c ≤ d ↔
    ∃ h : c.card ≤ d.card, restrictFace (Fin.castLEEmb h) d.chart = some c.chart :=
  Iff.rfl

/-- An extension has at least as many points. -/
theorem card_le (h : c ≤ d) : c.card ≤ d.card :=
  h.1

variable {t : Fin n ↪ ℕ}

/-- A supported tuple has the type of the face it spans in the chart. -/
theorem realization_eval_of_isSupported (h : IsSupported c.card t) :
    c.realization.eval t = restrictFace h.face c.chart :=
  StageType.chartRealization_eval_of_isSupported h

/-- An unsupported tuple has no type. -/
theorem realization_eval_of_not_isSupported (h : ¬ IsSupported c.card t) :
    c.realization.eval t = none :=
  StageType.chartRealization_eval_of_not_isSupported h

/-- A typed tuple is supported. -/
theorem isSupported_of_isSome (h : (c.realization.eval t).isSome) : IsSupported c.card t :=
  StageType.isSupported_of_isSome h

/-- **Extension is literal restriction**: an extension of `c` gives every tuple supported by `c`
its type in `c`.  Typed tuples keep their types, and supported invisible tuples stay invisible. -/
theorem realization_eval_of_le (hcd : c ≤ d) (h : IsSupported c.card t) :
    d.realization.eval t = c.realization.eval t := by
  obtain ⟨hk, hd⟩ := hcd
  rw [realization_eval_of_isSupported (h.mono hk), realization_eval_of_isSupported h,
    h.face_mono hk, ← restrictFace_trans d.chart _ _ hd]

/-- The partial realization of a condition is exactly consistent. -/
theorem isConsistent_realization : c.realization.IsConsistent :=
  StageType.isConsistent_chartRealization

/-- The types of the partial realization of a condition are legal. -/
theorem hasLegalTypes_realization : c.realization.HasLegalTypes :=
  StageType.hasLegalTypes_chartRealization c.isLegal

/-- The points of a condition, in order, have the type of its chart. -/
@[simp] theorem realization_eval_valEmbedding :
    c.realization.eval (Fin.valEmbedding : Fin c.card ↪ ℕ) = some c.chart :=
  StageType.chartRealization_eval_valEmbedding

/-- A realized member over a tuple stays realized in every extension. -/
theorem realizesOver_of_le (hcd : c ≤ d) {U : Set (StageType.{u} α (n + 1))}
    (h : c.realization.RealizesOver t U) : d.realization.RealizesOver t U := by
  obtain ⟨u, hu, q, hq, he⟩ := h
  refine ⟨u, hu, q, hq, ?_⟩
  rw [realization_eval_of_le hcd (isSupported_of_isSome (by rw [he]; rfl)), he]

/-- The **one-point extension** of a condition by a one-point extension of its chart (a coface of
the chart): the new point is `c.card`. -/
def snoc (c : Condition.{u} α) (Q : StageType.{u} α (c.card + 1)) (hQ : Q ∈ c.chart.cofaces) :
    Condition.{u} α :=
  ⟨c.card + 1, Q, hQ.1⟩

/-- The number of points of a one-point extension. -/
@[simp] theorem card_snoc (Q : StageType.{u} α (c.card + 1)) (hQ : Q ∈ c.chart.cofaces) :
    (c.snoc Q hQ).card = c.card + 1 :=
  rfl

/-- The chart of a one-point extension. -/
@[simp] theorem chart_snoc (Q : StageType.{u} α (c.card + 1)) (hQ : Q ∈ c.chart.cofaces) :
    (c.snoc Q hQ).chart = Q :=
  rfl

/-- A one-point extension is an extension. -/
theorem le_snoc (Q : StageType.{u} α (c.card + 1)) (hQ : Q ∈ c.chart.cofaces) :
    c ≤ c.snoc Q hQ :=
  ⟨Nat.le_succ _, hQ.2⟩

end Condition

/-! ### Unions of chains -/

/-- The **union** of a sequence of conditions: a tuple has its type in the first condition that
supports it, and no type if no condition does. -/
noncomputable def chainUnion (c : ℕ → Condition.{u} α) : Realization.{u, 0} α ℕ where
  eval t := by
    classical
    exact if h : ∃ i, IsSupported (c i).card t then (c (Nat.find h)).realization.eval t else none

variable {c : ℕ → Condition.{u} α} {t : Fin n ↪ ℕ}

/-- **Stabilization**: along a monotone sequence, a tuple supported by a condition of the
sequence has its type there in the union. -/
theorem chainUnion_eval_of_isSupported (hc : Monotone c) {i : ℕ}
    (h : IsSupported (c i).card t) : (chainUnion c).eval t = (c i).realization.eval t := by
  have hex : ∃ i, IsSupported (c i).card t := ⟨i, h⟩
  dsimp only [chainUnion]
  rw [dite_eq_left hex]
  exact (Condition.realization_eval_of_le (hc (Nat.find_min' hex h)) (Nat.find_spec hex)).symm

/-- A tuple supported by no condition of the sequence has no type in the union. -/
theorem chainUnion_eval_of_forall_not_isSupported (h : ∀ i, ¬ IsSupported (c i).card t) :
    (chainUnion c).eval t = none :=
  dite_eq_right fun ⟨i, hi⟩ ↦ h i hi

/-- A tuple typed in the union is supported by a condition of the sequence. -/
theorem exists_isSupported_of_isSome_chainUnion (h : ((chainUnion c).eval t).isSome) :
    ∃ i, IsSupported (c i).card t := by
  by_contra hn
  rw [chainUnion_eval_of_forall_not_isSupported (not_exists.mp hn)] at h
  exact Bool.false_ne_true h

/-- A tuple typed in the union has its type in a condition of the sequence that supports it. -/
theorem exists_eval_eq_of_chainUnion_eval_eq_some (hc : Monotone c)
    {p : StageType.{u} α n} (h : (chainUnion c).eval t = some p) :
    ∃ i, IsSupported (c i).card t ∧ (c i).realization.eval t = some p := by
  obtain ⟨i, hi⟩ := exists_isSupported_of_isSome_chainUnion (by rw [h]; rfl)
  exact ⟨i, hi, (chainUnion_eval_of_isSupported hc hi).symm.trans h⟩

/-- The union of a constant sequence is the partial realization of its condition. -/
@[simp] theorem chainUnion_const (c₀ : Condition.{u} α) :
    chainUnion (fun _ ↦ c₀) = c₀.realization := by
  refine Realization.ext fun t ↦ ?_
  by_cases h : IsSupported c₀.card t
  · exact chainUnion_eval_of_isSupported (i := 0) monotone_const h
  · rw [chainUnion_eval_of_forall_not_isSupported fun _ ↦ h,
      Condition.realization_eval_of_not_isSupported h]

/-- **The union of a chain is exactly consistent.** -/
theorem isConsistent_chainUnion (hc : Monotone c) : (chainUnion c).IsConsistent := by
  intro m n t p f ht
  obtain ⟨i, hi, hp⟩ := exists_eval_eq_of_chainUnion_eval_eq_some hc ht
  rw [chainUnion_eval_of_isSupported hc (hi.trans f)]
  exact (c i).isConsistent_realization t p f hp

/-- **The union of a chain of conditions has legal types.** -/
theorem hasLegalTypes_chainUnion (hc : Monotone c) : (chainUnion c).HasLegalTypes := by
  intro n t p ht
  obtain ⟨i, -, hp⟩ := exists_eval_eq_of_chainUnion_eval_eq_some hc ht
  exact (c i).hasLegalTypes_realization t p hp

/-- **Covering of the union**: the union of a chain is covering exactly when every point of `ℕ` is
eventually a point of the chart. -/
theorem isCovering_chainUnion_iff (hc : Monotone c) :
    (chainUnion c).IsCovering ↔ ∀ j, ∃ i, j < (c i).card := by
  refine ⟨fun h j ↦ ?_, fun h n t ↦ ?_⟩
  · obtain ⟨m, u, f, hu, hs⟩ := h (⟨fun _ ↦ j, fun _ _ _ ↦ Subsingleton.elim _ _⟩ : Fin 1 ↪ ℕ)
    obtain ⟨i, hi⟩ := exists_isSupported_of_isSome_chainUnion hs
    have hj : u (f 0) = j := DFunLike.congr_fun hu 0
    exact ⟨i, hj ▸ hi (f 0)⟩
  · obtain ⟨i, hi⟩ := exists_isSupported (fun j ↦ h j) t
    exact ⟨_, Fin.valEmbedding, hi.face, hi.face_trans_valEmbedding, by
      rw [chainUnion_eval_of_isSupported hc (i := i) fun j ↦ j.isLt,
        Condition.realization_eval_valEmbedding]
      rfl⟩

end Construction

end VaughtConjecture
