/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.BackAndForth

/-!
# The graded back-and-forth theorem

A *graded back-and-forth system of height `h`* between `L`-structures `M` and `N`
(`GradedBFSystem L M N h`) is a family of relations `R α n a b` between `n`-tuples `a` of `M` and
`b` of `N`, indexed by ordinals `α`, repeated coordinates and the empty tuple allowed, such that:

* (zero) `R 0 n a b` implies that `a` and `b` have the same atomic type (`SameAtomicType`);
* (descent) `R α n a b` implies `R β n a b` whenever `β ≤ α ≤ h`;
* (forth) if `α + 1 ≤ h` and `R (α + 1) n a b`, then for every `x : M` there is `y : N` with
  `R α (n + 1) (Fin.snoc a x) (Fin.snoc b y)`;
* (back) if `α + 1 ≤ h` and `R (α + 1) n a b`, then for every `y : N` there is `x : M` with
  `R α (n + 1) (Fin.snoc a x) (Fin.snoc b y)`.

Descent contains both the successor step, from `R (α + 1)` to `R α`, and the limit step, from
`R λ` to every `R β` with `β < λ`.  The graded back-and-forth theorem,
`GradedBFSystem.bfEquiv`, states that `R α n a b` implies InfinitaryLogic's `BFEquiv α n a b` for
every `α ≤ h`.  The proof is an induction on `α` through `BFEquiv.zero`, `BFEquiv.succ`, and
`BFEquiv.limit`.

**The height bound.**  The clauses are required only up to the height `h`, and the conclusion is
drawn only for `α ≤ h`, because the relations of the intended applications are defined only up to
a level: the observations of a presentation up to its level, the reductions of types at `λ_η` up
to `η`.

**The initial match.**  The theorem produces no related pair.  In each application the *initial
match*, a pair related at the height, is a separate hypothesis, never a consequence of the
clauses: the empty system `GradedBFSystem.empty` satisfies all of them and relates nothing.  The
diagonal system `GradedBFSystem.diagonal` on one structure relates every tuple to itself; through
the theorem it recovers InfinitaryLogic's reflexivity `BFEquiv.refl` below the height.

**Intended applications.**  The theorem is the common form of two intended applications:
approximate comparison of full presentations (`roadmap/README.md`, "Reduction to full
presentations"; initial match a given pair of closed tuples with equal observations), and the
back-and-forth form of condition 3 of the reduction to expansion domains (`roadmap/README.md`,
"Condition 3 from back-and-forth"; initial match the common empty chart).  Neither is compiled
through it yet.

**Language and universes.**  No relational hypothesis is assumed: at the pinned InfinitaryLogic,
`BFEquiv` and the lemmas `BFEquiv.zero`, `BFEquiv.succ`, and `BFEquiv.limit` used here hold for
every language.  Both applications are in a relational language, as the passage from `BFEquiv` to
agreement on sentences of bounded quantifier rank (`BFEquiv_implies_agreeQR`) requires.  The
ordinal index lives in an arbitrary universe; both applications take `h : Ordinal.{0}`, the
universe of quantifier ranks of `L_{ω₁ω}` formulas.

## Placement

This file belongs to Layer 0 of `roadmap/README.md`.
-/

namespace VaughtConjecture.Comparison

open FirstOrder Language

universe u

/-- A graded back-and-forth system of height `h` between `M` and `N`: relations `R α n a b`
between `n`-tuples of `M` and `N`, indexed by ordinals, with the zero, descent, forth, and back
clauses up to the height. -/
structure GradedBFSystem (L : Language) (M N : Type*) [L.Structure M] [L.Structure N]
    (h : Ordinal.{u}) where
  /-- The relation at level `α` between `n`-tuples of `M` and of `N`. -/
  R : Ordinal.{u} → (n : ℕ) → (Fin n → M) → (Fin n → N) → Prop
  /-- Related pairs at level `0` have the same atomic type. -/
  zero : ∀ {n : ℕ} {a : Fin n → M} {b : Fin n → N}, R 0 n a b → SameAtomicType (L := L) a b
  /-- Up to the height, the relation at a level implies the relation at every lower level. -/
  descent : ∀ {α β : Ordinal.{u}} {n : ℕ} {a : Fin n → M} {b : Fin n → N},
    β ≤ α → α ≤ h → R α n a b → R β n a b
  /-- Forth: a pair related at `α + 1 ≤ h` extends, for every point of `M`, to a pair related
  at `α`. -/
  forth : ∀ {α : Ordinal.{u}} {n : ℕ} {a : Fin n → M} {b : Fin n → N},
    α + 1 ≤ h → R (α + 1) n a b → ∀ x : M, ∃ y : N, R α (n + 1) (Fin.snoc a x) (Fin.snoc b y)
  /-- Back: a pair related at `α + 1 ≤ h` extends, for every point of `N`, to a pair related
  at `α`. -/
  back : ∀ {α : Ordinal.{u}} {n : ℕ} {a : Fin n → M} {b : Fin n → N},
    α + 1 ≤ h → R (α + 1) n a b → ∀ y : N, ∃ x : M, R α (n + 1) (Fin.snoc a x) (Fin.snoc b y)

namespace GradedBFSystem

variable {L : Language} {M N : Type*} [L.Structure M] [L.Structure N] {h : Ordinal.{u}}

/-- **The graded back-and-forth theorem.**  In a graded back-and-forth system of height `h`, a
pair related at a level `α ≤ h` is back-and-forth equivalent at `α`.  The theorem produces no
related pair: the initial match, a pair related at the height, is the hypothesis `hR` supplied by
each application. -/
theorem bfEquiv (S : GradedBFSystem L M N h) {α : Ordinal.{u}} (hα : α ≤ h) {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} (hR : S.R α n a b) : BFEquiv (L := L) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero => exact (BFEquiv.zero a b).mpr (S.zero hR)
  | add_one β ih =>
    have hβ : β ≤ h := (Order.le_succ β).trans hα
    rw [← Order.succ_eq_add_one, BFEquiv.succ]
    refine ⟨ih hβ (S.descent (Order.le_succ β) hα hR), fun x ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨y, hy⟩ := S.forth hα hR x
      exact ⟨y, ih hβ hy⟩
    · obtain ⟨x, hx⟩ := S.back hα hR y
      exact ⟨x, ih hβ hx⟩
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ]
    exact fun γ hγ ↦ ih γ hγ (hγ.le.trans hα) (S.descent hγ.le hα hR)

variable (L M N h)

/-- The empty system, relating no pair at any level.  It satisfies every clause, so the clauses
alone give no related pair: the initial match is a separate hypothesis. -/
def empty : GradedBFSystem L M N h where
  R _ _ _ _ := False
  zero := False.elim
  descent _ _ := False.elim
  forth _ := False.elim
  back _ := False.elim

/-- The empty system relates no pair. -/
theorem not_empty_R {α : Ordinal.{u}} {n : ℕ} {a : Fin n → M} {b : Fin n → N} :
    ¬ (empty L M N h).R α n a b :=
  id

/-- The diagonal system on one structure, relating every tuple to itself at every level. -/
def diagonal : GradedBFSystem L M M h where
  R _ _ a b := a = b
  zero := by rintro _ a _ rfl; exact SameAtomicType.refl a
  descent _ _ := id
  forth := by rintro _ _ a _ _ rfl x; exact ⟨x, rfl⟩
  back := by rintro _ _ a _ _ rfl y; exact ⟨y, rfl⟩

/-- Through the diagonal system, the theorem recovers InfinitaryLogic's `BFEquiv.refl` below the
height. -/
example {α : Ordinal.{u}} (hα : α ≤ h) {n : ℕ} (a : Fin n → M) : BFEquiv (L := L) α n a a :=
  (diagonal L M h).bfEquiv hα rfl

/-- The instance of the applications: the ordinal index in `Ordinal.{0}`. -/
example (h : Ordinal.{0}) (S : GradedBFSystem L M N h) {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hR : S.R h n a b) : BFEquiv (L := L) h n a b :=
  S.bfEquiv le_rfl hR

end GradedBFSystem

end VaughtConjecture.Comparison
