/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Amalgamation
import VaughtConjecture.Continuation.Terminal
import VaughtConjecture.MainTheorem.CoatomExtensionTheorem

/-!
# Finite spans of mutual rigidity: the statements

Process rank `ω₁`, the finite part of the count of the classes with a globally rigid core.

**Same scheme and top pattern.**  Two stage types `p` and `q` on `n` points have the **same
scheme and top pattern** (`StageType.SameSchemeTopPattern`) when their schemes are equal (cells,
scopes, grades, faces and rows) and a cell is labelled `⊤` in `p` exactly when the cell at the
same position is labelled `⊤` in `q`.  Their proper labels may differ completely.

**Spans of mutual rigidity.**  A legal stage type `D` with faces `p` along `i` and `q` along `j`,
in which both cores are rigid (`StageType.IsRigidCoreIn`), is a **span of mutual rigidity** of `p`
and `q` (`StageType.IsMutualRigidSpan`).  Exact receiving at a rigid core
(`Realization.exists_covers_of_isRigidCoreIn`) then places the same larger type `D` over a
globally rigid core of type `p` in one model and over one of type `q` in another, a common start
for the rooted comparison (`VaughtConjecture.ProcessRank.SpanComparison`).

**The targets.**

* `StageType.MutualRigidSpanTarget`: at a limit stage, two legal types with the same scheme and
  top pattern have a span of mutual rigidity on `n + n` points along embeddings with disjoint
  ranges.  Stated.
* `StageType.MutualForcingSpanTarget`: the construction target, a legal type on `n + n` points
  with disjoint faces `p` and `q` in which every admissible top support keeping the top cells of
  either face keeps those of the other (`StageType.ForcesTopsOf`).  Stated.
* `StageType.PruneTarget`: the pruning step.  From mutual forcing in a legal `D`, a witness of an
  inclusion-minimal admissible top support containing the top cells of the first face is a legal
  type on the scheme of `D` with the same two faces, in which both cores are rigid: an admissible
  top support of the witness is one of `D` (its non-top labels are those of `D`, the tops it drops
  stay proper), so minimality makes the first core rigid, and mutual forcing the second.  Stated.
* `StageType.mutualRigidSpanTarget_of_prune`: the two targets give the first.  Proved.
* `StageType.exists_mutualRigidSpan_zero`: the case `n = 0`.  Proved.
* `StageType.exists_isMutualRigidSpan_of_isTopFree`: the case without top cells, along embeddings
  whose ranges need not be disjoint, on some number of points: the top-free amalgam over the empty
  face (`StageType.exists_isTopFree_amalgam`, from the compiled coatom extension property).  Proved.
  The disjoint form on `n + n` points is `StageType.MutualRigidSpanTopFreeTarget`.  Stated.
* `StageType.MixedGradeExamplePairTarget` and `StageType.MixedGradeSpanExampleTarget`: the first
  example to be compiled before the general theorem, two legal types on two points with a top cell
  of grade one, a top cell of grade two and different proper labels.  Stated.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-- Two stage types have the **same scheme and top pattern**: equal schemes, and a cell is
labelled `⊤` in `p` exactly when the cell at the same position is labelled `⊤` in `q`. -/
def SameSchemeTopPattern (p q : StageType.{u} α n) : Prop :=
  p.toScheme = q.toScheme ∧
    ∀ (i : Fin p.card) (j : Fin q.card), (i : ℕ) = j → (p.label i = ⊤ ↔ q.label j = ⊤)

/-- A **span of mutual rigidity** of `p` and `q`: a legal stage type `D` with face `p` along `i`
and face `q` along `j`, in which both cores are rigid. -/
def IsMutualRigidSpan (p q : StageType.{u} α n) (D : StageType.{u} α m) (i j : Fin n ↪ Fin m) :
    Prop :=
  D.IsLegal ∧ restrictFace i D = some p ∧ restrictFace j D = some q ∧ D.IsRigidCoreIn i ∧
    D.IsRigidCoreIn j

/-- **Target: spans of mutual rigidity.**  At a limit stage, two legal stage types on `n` points
with the same scheme and top pattern have a span of mutual rigidity on `n + n` points, along
embeddings with disjoint ranges.  Stated. -/
def MutualRigidSpanTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α → ∀ ⦃n : ℕ⦄ ⦃p q : StageType.{u} α n⦄,
    p.IsLegal → q.IsLegal → SameSchemeTopPattern p q →
      ∃ (D : StageType.{u} α (n + n)) (i j : Fin n ↪ Fin (n + n)),
        Disjoint (Set.range i) (Set.range j) ∧ IsMutualRigidSpan p q D i j

/-- **Target: spans of mutual rigidity, on some number of points.**  The form used by the
comparison: at a limit stage, two legal stage types with the same scheme and top pattern have a
span of mutual rigidity on some number of points.  Stated. -/
def ExistsMutualRigidSpanTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α → ∀ ⦃n : ℕ⦄ ⦃p q : StageType.{u} α n⦄,
    p.IsLegal → q.IsLegal → SameSchemeTopPattern p q →
      ∃ (m : ℕ) (D : StageType.{u} α m) (i j : Fin n ↪ Fin m), IsMutualRigidSpan p q D i j

/-- The disjoint form gives the form on some number of points. -/
theorem existsMutualRigidSpanTarget_of_mutualRigidSpanTarget (h : MutualRigidSpanTarget.{u}) :
    ExistsMutualRigidSpanTarget.{u} := fun _ hα _ _ _ hp hq hs ↦
  let ⟨D, i, j, _, hD⟩ := h hα hp hq hs
  ⟨_, D, i, j, hD⟩

/-- In `D`, the top cells supported on the core along `i` **force** those supported on the core
along `j`: every admissible top support containing the top cells visible through `i` contains the
top cells visible through `j`. -/
def ForcesTopsOf (D : StageType.{u} α m) (i : Fin n ↪ Fin m) (j : Fin k ↪ Fin m) : Prop :=
  ∀ H : Set (Fin D.card), D.IsAdmissibleTopSupport H →
    (∀ d ∈ D.visibleCells i, D.label d = ⊤ → d ∈ H) → ∀ d ∈ D.visibleCells j, D.label d = ⊤ → d ∈ H

/-- **Target: the construction of mutual forcing.**  At a limit stage, two legal stage types on
`n` points with the same scheme and top pattern are the faces, along embeddings with disjoint
ranges, of one legal stage type on `n + n` points in which each of the two cores forces the top
cells of the other.  This is the finite construction (the cutoff-free admission, the master
levels, their mirroring onto the mixed faces, and the recognition of the active top controllers).
Stated. -/
def MutualForcingSpanTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α → ∀ ⦃n : ℕ⦄ ⦃p q : StageType.{u} α n⦄,
    p.IsLegal → q.IsLegal → SameSchemeTopPattern p q →
      ∃ (D : StageType.{u} α (n + n)) (i j : Fin n ↪ Fin (n + n)), D.IsLegal ∧
        Disjoint (Set.range i) (Set.range j) ∧ restrictFace i D = some p ∧
          restrictFace j D = some q ∧ D.ForcesTopsOf i j ∧ D.ForcesTopsOf j i

/-- **Target: pruning.**  In a legal stage type `D` in which the cores along `i` and `j` force the
top cells of each other, a witness of an inclusion-minimal admissible top support containing the
top cells visible through `i` is a legal stage type on the scheme of `D`, with the same faces along
`i` and `j`, in which both cores are rigid.  Only the definition of an admissible top support
(`StageType.IsAdmissibleTopSupport`) enters: an admissible top support of the witness is one of
`D`.  Stated. -/
def PruneTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄ (D : StageType.{u} α m) (i j : Fin n ↪ Fin m), D.IsLegal →
    D.ForcesTopsOf i j → D.ForcesTopsOf j i →
      ∃ D' : StageType.{u} α m, D'.IsLegal ∧ D'.toScheme = D.toScheme ∧
        restrictFace i D' = restrictFace i D ∧ restrictFace j D' = restrictFace j D ∧
          D'.IsRigidCoreIn i ∧ D'.IsRigidCoreIn j

/-- **Pruning a span of mutual forcing gives a span of mutual rigidity.**  Proved, conditional on
the two named targets. -/
theorem mutualRigidSpanTarget_of_prune (hprune : PruneTarget.{u})
    (hforce : MutualForcingSpanTarget.{u}) : MutualRigidSpanTarget.{u} := by
  intro α hα n p q hp hq hs
  obtain ⟨D, i, j, hD, hdisj, hi, hj, hij, hji⟩ := hforce hα hp hq hs
  obtain ⟨D', hD', -, hi', hj', hri, hrj⟩ := hprune D i j hD hij hji
  exact ⟨D', i, j, hdisj, hD', hi'.trans hi, hj'.trans hj, hri, hrj⟩

/-- The face of a stage type on no points is the given type on no points. -/
theorem restrictFace_eq_of_zero (t : StageType.{u} α n) (e : Fin 0 ↪ Fin n)
    (p : StageType.{u} α 0) : restrictFace e t = some p := by
  obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (t.isSome_restrictFace_of_zero e)
  rw [hp', eq_of_zero p' p]

/-- **Spans of mutual rigidity on no points**: a legal stage type on no points is a span of
mutual rigidity of any two stage types on no points (all equal), along the empty embeddings. -/
theorem exists_mutualRigidSpan_zero {p q : StageType.{u} α 0} (hp : p.IsLegal) :
    ∃ (D : StageType.{u} α (0 + 0)) (i j : Fin 0 ↪ Fin (0 + 0)),
      Disjoint (Set.range i) (Set.range j) ∧ IsMutualRigidSpan p q D i j := by
  refine ⟨p, Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, by simp, hp,
    restrictFace_eq_of_zero _ _ _, restrictFace_eq_of_zero _ _ _, ?_, ?_⟩ <;>
  exact isRigidCoreIn_of_isTopFree (isTopFree_of_zero p) _

/-- Two stage types with the same scheme and top pattern are top-free together. -/
theorem SameSchemeTopPattern.isTopFree {p q : StageType.{u} α n} (hs : SameSchemeTopPattern p q)
    (hp : p.IsTopFree) : q.IsTopFree := fun d hd ↦ by
  have hc : p.card = q.card := congrArg Scheme.card hs.1
  exact hp (Fin.cast hc.symm d) ((hs.2 (Fin.cast hc.symm d) d rfl).mpr hd)

/-- **Spans of mutual rigidity without top cells**: at a limit stage, two legal stage types with
the same scheme and top pattern, without top cells, have a span of mutual rigidity on some number
of points: a top-free amalgam over the empty face (`StageType.exists_isTopFree_amalgam`, with the
compiled coatom extension property `StageType.hasCoatomExtensions`), in which every core is
rigid. -/
theorem exists_isMutualRigidSpan_of_isTopFree (hα : Order.IsSuccLimit α) {p q : StageType.{u} α n}
    (hp : p.IsLegal) (hq : q.IsLegal) (hs : SameSchemeTopPattern p q) (hpt : p.IsTopFree) :
    ∃ (m : ℕ) (D : StageType.{u} α m) (i j : Fin n ↪ Fin m), IsMutualRigidSpan p q D i j := by
  have hqt := hs.isTopFree hpt
  obtain ⟨p₀, hp₀⟩ := Option.isSome_iff_exists.mp
    (p.isSome_restrictFace_of_zero Function.Embedding.ofIsEmpty)
  obtain ⟨N, Q, i, j, hQ, hQt, hQp, hQq, -⟩ := exists_isTopFree_amalgam
    (hasCoatomExtensions hα.isSuccPrelimit) hα.isSuccPrelimit (pos_iff_ne_zero.mpr hα.ne_bot)
    hp hpt hq hqt hp₀ (restrictFace_eq_of_zero q Function.Embedding.ofIsEmpty p₀)
  exact ⟨N, Q, i, j, hQ, hQp, hQq, isRigidCoreIn_of_isTopFree hQt i,
    isRigidCoreIn_of_isTopFree hQt j⟩

/-- **Target: spans of mutual rigidity without top cells, disjoint form**: at a limit stage, two
legal top-free stage types on `n` points with the same scheme have a span of mutual rigidity on
`n + n` points along embeddings with disjoint ranges (a disjoint top-free amalgam on exactly
`n + n` points).  Stated. -/
def MutualRigidSpanTopFreeTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α → ∀ ⦃n : ℕ⦄ ⦃p q : StageType.{u} α n⦄,
    p.IsLegal → q.IsLegal → SameSchemeTopPattern p q → p.IsTopFree →
      ∃ (D : StageType.{u} α (n + n)) (i j : Fin n ↪ Fin (n + n)),
        Disjoint (Set.range i) (Set.range j) ∧ IsMutualRigidSpan p q D i j

/-! ### The first example -/

/-- **The mixed-grade example pair**: legal stage types `p` and `q` on two points with the same
scheme and top pattern, a top cell of grade one, a top cell of grade two, and a cell at which both
labels are proper and different. -/
def IsMixedGradeExamplePair (p q : StageType.{u} α 2) : Prop :=
  p.IsLegal ∧ q.IsLegal ∧ SameSchemeTopPattern p q ∧
    (∃ d, p.toCellScheme.grade d = 1 ∧ p.label d = ⊤) ∧
    (∃ d, p.toCellScheme.grade d = 2 ∧ p.label d = ⊤) ∧
    ∃ (i : Fin p.card) (j : Fin q.card), (i : ℕ) = j ∧ (p.label i).IsProper ∧
      (q.label j).IsProper ∧ p.label i ≠ q.label j

/-- **Target: the mixed-grade example pair exists**, at the limit stage `ω ^ 2`.  The intended pair
has the cells `({0}, 1)`, `({1}, 1)`, `({0, 1}, 1)` and `({0, 1}, 2)`, labelled `⊤`, `λ`, `⊤`, `⊤`
(availability from `({0}, 1)` forces `⊤` at `({0, 1}, 1)`), with `λ = ω + 1` in `p` and
`λ = ω * 2 + 1` in `q` (both self-visible at the grade one), on one scheme.  Stated. -/
def MixedGradeExamplePairTarget : Prop :=
  ∃ p q : StageType.{u} (Ordinal.omega0 ^ 2) 2, IsMixedGradeExamplePair p q

/-- **Target: the span of the mixed-grade example**: every mixed-grade example pair at a limit
stage has a span of mutual rigidity on four points along embeddings with disjoint ranges.  It is to
be compiled through the generic mirrored master before the general theorem.  Stated. -/
def MixedGradeSpanExampleTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α → ∀ ⦃p q : StageType.{u} α 2⦄,
    IsMixedGradeExamplePair p q →
      ∃ (D : StageType.{u} α (2 + 2)) (i j : Fin 2 ↪ Fin (2 + 2)),
        Disjoint (Set.range i) (Set.range j) ∧ IsMutualRigidSpan p q D i j

end StageType

end VaughtConjecture
