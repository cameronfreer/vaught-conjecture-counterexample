/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fintype.Order
import VaughtConjecture.Stage.Legal
import VaughtConjecture.Stage.TopFree

/-!
# Capped stage types

**Capping a stage type.**  Let `t` be a stage type at stage `α` on `n` points and `c < α` an
ordinal self-visible at `n`.  The **capped stage type** `t.cap c` (`StageType.cap`) has the scheme
of `t` and the labels `min (t.label d) c`; its section is lawful by capping at a cap self-visible at
a bound of the grades ([Kni26, Lemma 2.5.8], `CellScheme.Rows.IsLawful.min_const_of_isSelfVisible`),
the grades of a cell being at most `n` (`StageType.grade_le`).  It is legal exactly when `t` is
(`StageType.isLegal_cap`), it is top-free since `c` is a proper label (`StageType.isTopFree_cap`),
and along a closed face whose labels are at most `c` it restricts to the same stage type as `t`,
labels included (`StageType.restrictFace_cap`).

**The cap.**  At a limit stage, such a cap exists above the labels of any two top-free stage types,
self-visible at any arity (`StageType.exists_cap`, from `Label.exists_lt_lt_isSelfVisible`): a
top-free label at a nonzero stage is bounded by an ordinal below the stage
(`StageType.IsTopFree.exists_label_le`).  Capping assumes nothing about the stage; the existence of
the cap assumes that the stage is zero or a limit and nonzero, that is, a limit ordinal.

**Bounds on the labels.**  At a nonzero stage, the labels of any stage type other than `⊤` are at
most one ordinal below the stage (`StageType.exists_label_le`); the bound for top-free stage types
is the case without top labels.  At a limit stage the successor of that ordinal is still below the
stage, so some ordinal below the stage lies strictly above every label other than `⊤`
(`StageType.exists_lt_forall_label_lt`): the cutoff at which a donor is received in the rigid-core
comparison (`VaughtConjecture.Continuation.Comparison`).

Capping makes the amalgam of two top-free stage types top-free
(`VaughtConjecture.ClassicalLimit.Amalgamation`), gives the received coface in finite-cut
receiving (`VaughtConjecture.ClassicalLimit.Receiving`), and shows that the empty core is rigid in
a legal type at a limit stage only when the type is top-free
(`VaughtConjecture.Continuation.Terminal`).

## Placement

This file belongs to Layer 1 of `roadmap/README.md`.

## References

Capping a lawful section is [Kni26, Lemma 2.5.8].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-! ### Capping a stage type -/

/-- The **capped stage type** of a stage type `t` on `n` points at an ordinal `c` below the stage
and self-visible at `n`: the scheme of `t` with the labels `min (t.label d) c`, a lawful section by
[Kni26, Lemma 2.5.8]. -/
noncomputable def cap (t : StageType.{u} α n) (c : Ordinal.{u}) (hc : IsSelfVisible n (c : Label))
    (hcα : c < α) : StageType.{u} α n where
  toScheme := t.toScheme
  label d := min (t.label d) c
  isWellFormed := t.isWellFormed
  isCoded := t.isCoded
  isLawful := t.isLawful.min_const_of_isSelfVisible t.grade_le hc
  atStage _ := .inl ((min_le_right _ _).trans_lt (atStage_coe.mpr hcα |>.resolve_right
    (WithBot.coe_injective.ne WithTop.coe_ne_top)))

variable {t : StageType.{u} α n} {c : Ordinal.{u}} {hc : IsSelfVisible n (c : Label)}
  {hcα : c < α}

/-- The scheme of a capped stage type is the scheme of the stage type. -/
@[simp] theorem cap_toScheme : (t.cap c hc hcα).toScheme = t.toScheme := rfl

/-- The labels of a capped stage type are the labels capped at the cap. -/
@[simp] theorem cap_label (d : Fin t.card) :
    (t.cap c hc hcα).label d = min (t.label d) c := rfl

/-- A capped stage type is legal exactly when the stage type is: legality concerns the scheme. -/
@[simp] theorem isLegal_cap : (t.cap c hc hcα).IsLegal ↔ t.IsLegal :=
  Iff.rfl

/-- A capped stage type is top-free: its labels are at most the cap, a proper label. -/
theorem isTopFree_cap : (t.cap c hc hcα).IsTopFree := fun d h ↦ by
  have hle : (t.cap c hc hcα).label d ≤ c := min_le_right _ _
  rw [h, top_le_iff] at hle
  exact WithBot.coe_injective.ne WithTop.coe_ne_top hle

/-- **Literal restriction of a capped stage type.**  Along a closed face whose labels are at most
the cap, a capped stage type restricts to the same stage type as the stage type itself. -/
theorem restrictFace_cap {f : Fin m ↪ Fin n} {p : StageType.{u} α m}
    (hp : restrictFace f t = some p) (hpc : ∀ d, p.label d ≤ c) :
    restrictFace f (t.cap c hc hcα) = some p := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t f).mp hp
  rw [restrictFace_of_mem (t.cap c hc hcα) f hf]
  refine congrArg some (ext rfl fun i j hij ↦ ?_)
  obtain rfl : i = j := Fin.ext hij
  exact min_eq_left (hpc i)

/-! ### The cap -/

/-- A top-free label at a nonzero stage is at most an ordinal below the stage. -/
private theorem exists_le_of_atStage {x : Label.{u}} (hx : AtStage α x) (htop : x ≠ ⊤)
    (h0 : 0 < α) : ∃ o < α, x ≤ (o : Label) := by
  induction x using WithBot.recBotCoe with
  | bot => exact ⟨0, h0, bot_le⟩
  | coe y =>
    induction y using WithTop.recTopCoe with
    | top => exact absurd rfl htop
    | coe o => exact ⟨o, atStage_coe.mp hx, le_rfl⟩

/-- **The labels other than `⊤` are bounded below the stage**: at a nonzero stage `α`, every
label of a stage type other than `⊤` is at most one ordinal below `α`. -/
theorem exists_label_le (t : StageType.{u} α n) (h0 : 0 < α) :
    ∃ o < α, ∀ d, t.label d ≠ ⊤ → t.label d ≤ (o : Label) := by
  have key (d : Fin t.card) : ∃ o < α, t.label d ≠ ⊤ → t.label d ≤ (o : Label) := by
    by_cases hd : t.label d = ⊤
    · exact ⟨0, h0, fun h ↦ absurd hd h⟩
    · obtain ⟨o, ho, hle⟩ := exists_le_of_atStage (t.atStage d) hd h0
      exact ⟨o, ho, fun _ ↦ hle⟩
  have : Nonempty (Set.Iio α) := ⟨⟨0, h0⟩⟩
  choose g hg hgle using key
  obtain ⟨⟨o, ho⟩, hmax⟩ := Finite.exists_le fun d ↦ (⟨g d, hg d⟩ : Set.Iio α)
  exact ⟨o, ho, fun d hd ↦ (hgle d hd).trans (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
    (Subtype.coe_le_coe.mpr (hmax d))))⟩

/-- **The labels of a top-free stage type are bounded below the stage**: at a nonzero stage `α`,
every label of a top-free stage type is at most one ordinal below `α`. -/
theorem IsTopFree.exists_label_le (ht : t.IsTopFree) (h0 : 0 < α) :
    ∃ o < α, ∀ d, t.label d ≤ (o : Label) :=
  let ⟨o, ho, hle⟩ := t.exists_label_le h0
  ⟨o, ho, fun d ↦ hle d (ht d)⟩

/-- **A strict bound at a limit stage**: at a limit stage, some ordinal below the stage lies
above every label of a stage type other than `⊤`. -/
theorem exists_lt_forall_label_lt (hα : Order.IsSuccLimit α) (D : StageType.{u} α m) :
    ∃ δ < α, ∀ j, D.label j ≠ ⊤ → D.label j < (δ : Label.{u}) := by
  obtain ⟨o, ho, hle⟩ := D.exists_label_le hα.bot_lt
  exact ⟨Order.succ o, hα.succ_lt ho, fun j hj ↦
    (hle j hj).trans_lt (by exact_mod_cast Order.lt_succ o)⟩

/-- **The cap.**  At a limit stage `α`, for two top-free stage types and every arity `K` there is
an ordinal below `α`, self-visible at `K`, above every label of the two stage types. -/
theorem exists_cap (hα : Order.IsSuccPrelimit α) (h0 : 0 < α) {P : StageType.{u} α n}
    {R : StageType.{u} α m} (hP : P.IsTopFree) (hR : R.IsTopFree) (K : ℕ) :
    ∃ c : Ordinal.{u}, c < α ∧ IsSelfVisible K (c : Label) ∧ (∀ d, P.label d ≤ c) ∧
      ∀ d, R.label d ≤ c := by
  obtain ⟨o, ho, hPo⟩ := hP.exists_label_le h0
  obtain ⟨o', ho', hRo⟩ := hR.exists_label_le h0
  obtain ⟨c, hoc, hcα, hc⟩ := exists_lt_lt_isSelfVisible hα (max_lt ho ho') K
  have hle (x : Ordinal.{u}) (hx : x ≤ max o o') : (x : Label) ≤ c :=
    WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (hx.trans hoc.le))
  exact ⟨c, hcα, hc, fun d ↦ (hPo d).trans (hle o (le_max_left _ _)),
    fun d ↦ (hRo d).trans (hle o' (le_max_right _ _))⟩

end StageType

end VaughtConjecture
