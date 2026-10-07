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

**Capping the cells through a point.**  For a point `a`, the stage type `t.capThrough a c`
(`StageType.capThrough`) caps at `c` only the cells whose scope contains `a`.  It is lawful when
every cell whose scope avoids `a` and lies in the scope of a cell of the same grade containing `a`
is labelled at most `c` (`CellScheme.Rows.IsLawful.min_const_of_mem_scope`), and its faces along
embeddings whose range avoids `a` are those of `t` (`StageType.restrictFace_capThrough`).  Capping
the cells through the new point of a coface lowers its new top labels while keeping its private
face (`VaughtConjecture.Continuation.AnchoredDetermination`).

**Capping an upper set of cells.**  More generally, for a set `Z` of cells closed upward in the
graded order, `t.capOn Z c` (`StageType.capOn`) caps at `c` only the cells of `Z`.  It is lawful
when every cell outside `Z` whose scope lies in the scope of a cell of `Z` of the same grade is
labelled at most `c` (`CellScheme.Rows.IsLawful.min_const_of_upper`), and its faces along
embeddings whose visible cells are outside `Z` are those of `t` (`StageType.restrictFace_capOn`).
The cells through a point of grade above a bound are such a set
(`VaughtConjecture.Continuation.AvailableTopDetermination`), and so are the cells of grade at least
a bound (`VaughtConjecture.Continuation.AvailableTopDeterminationCounterexample`).

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

/-! ### Capping the cells through a point -/

/-- The **stage type capped through a point** `a`: the scheme of `t` with the cells whose scope
contains `a` capped at `c` and the other labels kept.  It is lawful when availability carries no
label above `c` into the cells through `a` (`CellScheme.Rows.IsLawful.min_const_of_mem_scope`):
every cell whose scope avoids `a` and lies in the scope of a cell of the same grade containing `a`
is labelled at most `c`. -/
noncomputable def capThrough (t : StageType.{u} α n) (a : Fin n) (c : Ordinal.{u})
    (hc : IsSelfVisible n (c : Label)) (hcα : c < α)
    (havail : ∀ s s', t.toCellScheme.scope s ⊆ t.toCellScheme.scope s' →
      t.toCellScheme.grade s = t.toCellScheme.grade s' → a ∉ t.toCellScheme.scope s →
      a ∈ t.toCellScheme.scope s' → t.label s ≤ c) : StageType.{u} α n where
  toScheme := t.toScheme
  label d := if a ∈ t.toCellScheme.scope d then min (t.label d) c else t.label d
  isWellFormed := t.isWellFormed
  isCoded := t.isCoded
  isLawful := t.isLawful.min_const_of_mem_scope a t.grade_le hc havail
  atStage d := by
    split_ifs
    · exact (t.cap c hc hcα).atStage d
    · exact t.atStage d

section CapThrough

variable {a : Fin n} {havail : ∀ s s',
  t.toCellScheme.scope s ⊆ t.toCellScheme.scope s' →
    t.toCellScheme.grade s = t.toCellScheme.grade s' → a ∉ t.toCellScheme.scope s →
    a ∈ t.toCellScheme.scope s' → t.label s ≤ c}

/-- The scheme of a type capped through a point is the scheme of the type. -/
@[simp] theorem capThrough_toScheme : (t.capThrough a c hc hcα havail).toScheme = t.toScheme :=
  rfl

/-- The labels of a type capped through `a`: capped at the cells through `a`, kept elsewhere. -/
theorem capThrough_label (d : Fin t.card) : (t.capThrough a c hc hcα havail).label d =
    if a ∈ t.toCellScheme.scope d then min (t.label d) c else t.label d :=
  rfl

/-- **Faces avoiding the point are unchanged**: along `f` whose range avoids `a`, a type capped
through `a` restricts as the type does, definedness included. -/
theorem restrictFace_capThrough {f : Fin m ↪ Fin n} (hf : a ∉ Set.range f) :
    restrictFace f (t.capThrough a c hc hcα havail) = restrictFace f t := by
  by_cases hfm : univ.map f ∈ t.toCellScheme.faces
  · rw [restrictFace_of_mem t f hfm, restrictFace_of_mem (t.capThrough a c hc hcα havail) f hfm]
    refine congrArg some (ext rfl fun i j hij ↦ ?_)
    obtain rfl : i = j := Fin.ext hij
    -- the cell of `t` under `i` is visible through `f`, so its scope avoids `a`
    have ha : a ∉ t.toCellScheme.scope (t.cellMap f i) := fun ha ↦
      hf (Scheme.mem_visibleCells.mp (t.cellMap_mem f i) (mem_coe.mpr ha))
    -- the capped type has the scheme of `t`, so its cell under `i` is that of `t`; unfold the
    -- capped label there (`StageType.capThrough_label`)
    change (if a ∈ t.toCellScheme.scope (t.cellMap f i) then _ else _) = t.label (t.cellMap f i)
    simp only [ha, ↓reduceIte]
    rfl
  · rw [restrictFace_of_notMem t f hfm,
      restrictFace_of_notMem (t.capThrough a c hc hcα havail) f hfm]

end CapThrough

/-! ### Capping an upper set of cells -/

/-- The **stage type capped on an upper set** `Z` of cells (closed upward in the graded order):
the scheme of `t` with the cells of `Z` capped at `c` and the other labels kept.  It is lawful
when availability carries no label above `c` into `Z`
(`CellScheme.Rows.IsLawful.min_const_of_upper`): every cell outside `Z` whose scope lies in the
scope of a cell of `Z` of the same grade is labelled at most `c`. -/
noncomputable def capOn (t : StageType.{u} α n) (Z : Fin t.card → Prop) [DecidablePred Z]
    (c : Ordinal.{u}) (hc : IsSelfVisible n (c : Label)) (hcα : c < α)
    (hZ : ∀ d s, Z d → t.toCellScheme.gradedIndex d ≤ t.toCellScheme.gradedIndex s → Z s)
    (havail : ∀ s s', t.toCellScheme.scope s ⊆ t.toCellScheme.scope s' →
      t.toCellScheme.grade s = t.toCellScheme.grade s' → ¬ Z s → Z s' → t.label s ≤ c) :
    StageType.{u} α n where
  toScheme := t.toScheme
  label d := if Z d then min (t.label d) c else t.label d
  isWellFormed := t.isWellFormed
  isCoded := t.isCoded
  isLawful := t.isLawful.min_const_of_upper Z hZ t.grade_le hc havail
  atStage d := by
    split_ifs
    · exact (t.cap c hc hcα).atStage d
    · exact t.atStage d

section CapOn

variable {Z : Fin t.card → Prop} [DecidablePred Z]
  {hZ : ∀ d s, Z d → t.toCellScheme.gradedIndex d ≤ t.toCellScheme.gradedIndex s → Z s}
  {havail : ∀ s s', t.toCellScheme.scope s ⊆ t.toCellScheme.scope s' →
    t.toCellScheme.grade s = t.toCellScheme.grade s' → ¬ Z s → Z s' → t.label s ≤ c}

/-- The scheme of a type capped on an upper set is the scheme of the type. -/
@[simp] theorem capOn_toScheme : (t.capOn Z c hc hcα hZ havail).toScheme = t.toScheme :=
  rfl

/-- The labels of a type capped on `Z`: capped at the cells of `Z`, kept elsewhere. -/
theorem capOn_label (d : Fin t.card) : (t.capOn Z c hc hcα hZ havail).label d =
    if Z d then min (t.label d) c else t.label d :=
  rfl

/-- **Faces outside the upper set are unchanged**: along `f` whose visible cells are outside `Z`,
a type capped on `Z` restricts as the type does, definedness included. -/
theorem restrictFace_capOn {f : Fin m ↪ Fin n} (hf : ∀ d ∈ t.visibleCells f, ¬ Z d) :
    restrictFace f (t.capOn Z c hc hcα hZ havail) = restrictFace f t := by
  by_cases hfm : univ.map f ∈ t.toCellScheme.faces
  · rw [restrictFace_of_mem t f hfm, restrictFace_of_mem (t.capOn Z c hc hcα hZ havail) f hfm]
    refine congrArg some (ext rfl fun i j hij ↦ ?_)
    obtain rfl : i = j := Fin.ext hij
    have hZi : ¬ Z (t.cellMap f i) := hf _ (t.cellMap_mem f i)
    -- the capped type has the scheme of `t`, so its cell under `i` is that of `t`; unfold the
    -- capped label there (`StageType.capOn_label`)
    change (if Z (t.cellMap f i) then _ else _) = t.label (t.cellMap f i)
    simp only [hZi, ↓reduceIte]
    rfl
  · rw [restrictFace_of_notMem t f hfm,
      restrictFace_of_notMem (t.capOn Z c hc hcα hZ havail) f hfm]

end CapOn

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
