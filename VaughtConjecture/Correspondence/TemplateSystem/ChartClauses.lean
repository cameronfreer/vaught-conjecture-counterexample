/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.TemplateSystem.ChosenSymbols

/-!
# The clauses for `P_k` and `R_t` of the chart of a template

Numbering as in the current draft of [AFK26].  [AFK26, Definition 4.18] lets a symbol hold of
`x_{i_0}, …, x_{i_{k-1}}` in the chart of a template `T` on `[n]` by three clauses.  The clause for
`Q_t` is read in `VaughtConjecture.Correspondence.TemplateSystem.RepresentativeDictionary` and
`VaughtConjecture.Correspondence.TemplateSystem.ChosenSymbols`.  This file states the other two,
each as a test on the index map `xs : Fin k → Fin n` itself, and compares each with the reading of
the chart in the library: the relations of the structure on `T.TemplateChart`, which are
`StageType.Holds` ([AFK26, Definition 4.18] as read in
`VaughtConjecture.Correspondence.Charts.Chart`).

* **`P_k`** (`StageType.PrintedClosed`): the entries of `xs` are distinct and its range is closed
  in the plan of `T` (a member of `T.toCellScheme.faces`).  `ClosedClauseTarget`: for `0 < k`,
  the printed test is the chart's reading of `TemplateSymbol.closed`.  **Proved**
  (`closedClauseTarget`).
* **`R_t`** (`StageType.PrintedBaseHolds`): with the same coordinates, `xs` is injective, the face
  of `T` along `xs` is defined, and `t` is the chosen representative of the class of the
  truncation at `ω = ω + ω · 0` of that face (`StageType.project` at `blockStage 0`).
  `BaseClauseTarget`: for a chosen template `t` whose class is fixed by the truncation at `ω`, the
  printed test is the chart's reading of `TemplateSymbol.base` at the legal class of `t`.
  **Stated.**

**Non-injective index maps.**  Both printed tests require `xs` to be injective, and so does
`StageType.Holds`; for a non-injective `xs` both sides of each comparison are false.  The two
targets quantify over every `xs`, injective or not.

**Arity zero.**  There are no symbols of arity `0`: `TemplateSymbol 0` is empty (every symbol has
positive arity, `TemplateSymbol.pos`), and so is `ChosenSymbol 0` (`arityZeroTarget`).  The printed
test for `P_k` is still meaningful at `k = 0` and holds of the empty tuple (the empty set is
closed); the printed symbols `P_n` start at `n = 1`.  The comparison targets assume `0 < k`, which
the symbols carry.  `ArityZeroClausesTarget`, **proved** (`arityZeroClausesTarget`).

Sentences are not translated here.
-/

universe u

namespace VaughtConjecture

open FirstOrder Language Structure Finset Ordinal StageType

noncomputable section

/-! ### The printed tests -/

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **The printed test for `P_k`** ([AFK26, Definition 4.18], first clause): the entries of `xs`
are distinct and its range is closed in the plan of `T`.
Correspondence with the printed definitions. -/
def PrintedClosed (T : StageType.{u} α n) (xs : Fin k → Fin n) : Prop :=
  Function.Injective xs ∧ univ.image xs ∈ T.toCellScheme.faces

/-- **The printed test for `R_t`** ([AFK26, Definition 4.18], third clause, with the template
system of chosen representatives): `xs` is injective, the face of `T` along `xs` is defined, and
`t` is the chosen representative of the class of the truncation at `ω` of that face.
Correspondence with the printed definitions. -/
def PrintedBaseHolds (T : StageType.{u} ω₁ n) (t : StageType.{u} ω₁ k) (xs : Fin k → Fin n) :
    Prop :=
  ∃ h : Function.Injective xs, ∃ s, restrictFace ⟨xs, h⟩ T = some s ∧
    chosenTemplateRepresentative ((s.project (isSuccPrelimit_blockStage 0)).toClass) = t

end StageType

/-! ### `P_k` -/

/-- **Target: the clause for `P_k`.**  For `0 < k` and every `xs : Fin k → Fin n`, injective or
not, the printed test for `P_k` on `xs` is the reading of `TemplateSymbol.closed` of `xs` in the
chart `T.TemplateChart` of `T`.  Proved (`closedClauseTarget`).
Correspondence with the printed definitions. -/
def ClosedClauseTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (T : StageType.{u} α n) (hk : 0 < k) (xs : Fin k → Fin n),
    T.PrintedClosed xs ↔
      RelMap (L := templateLanguage.{u}) (M := T.TemplateChart) (TemplateSymbol.closed hk) xs

/-- **The clause for `P_k`, proved**: the face map is defined exactly at the closed faces
(`StageType.isSome_restrictFace_iff`). -/
theorem closedClauseTarget : ClosedClauseTarget.{u} := by
  intro α n k T hk xs
  change _ ↔ T.Holds _ xs
  constructor
  · rintro ⟨h, hf⟩
    have hsome : (restrictFace ⟨xs, h⟩ T).isSome :=
      (isSome_restrictFace_iff T ⟨xs, h⟩).mpr (by simpa [Finset.map_eq_image] using hf)
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨h, s, hs, trivial⟩
  · rintro ⟨h, s, hs, -⟩
    have hmem := (isSome_restrictFace_iff T ⟨xs, h⟩).mp (by simp [hs])
    exact ⟨h, by simpa [Finset.map_eq_image] using hmem⟩

/-! ### `R_t` -/

/-- **Target: the clause for `R_t`.**  For a chosen template `t` on `[k]` whose class is fixed by
the truncation at `ω` (the printed condition `τ₀(Q_t) = Q_t`), and every `xs : Fin k → Fin n`,
injective or not, the printed test for `R_t` on `xs` is the reading of `TemplateSymbol.base` of
the legal class of `t` on `xs` in the chart `T.TemplateChart` of `T`.  Stated.
Correspondence with the printed definitions. -/
def BaseClauseTarget : Prop :=
  ∀ ⦃n k : ℕ⦄ (T : StageType.{u} ω₁ n) (t : ChosenSymbol.{u} k)
    (h0 : t.toLegalClass.1.project (isSuccPrelimit_blockStage 0) = t.toLegalClass.1)
    (xs : Fin k → Fin n),
      T.PrintedBaseHolds t.1 xs ↔
        RelMap (L := templateLanguage.{u}) (M := T.TemplateChart)
          (TemplateSymbol.base t.toLegalClass h0 t.pos) xs

/-! ### Arity zero -/

/-- **Target: arity zero for the clauses.**  There are no symbols of `templateLanguage` and no
chosen symbols of arity `0`, while the printed test for `P_k` holds of the empty tuple in every
template.  Proved (`arityZeroClausesTarget`).  Correspondence with the printed definitions. -/
def ArityZeroClausesTarget : Prop :=
  IsEmpty (TemplateSymbol.{u} 0) ∧ IsEmpty (ChosenSymbol.{u} 0) ∧
    ∀ ⦃α : Ordinal.{u}⦄ ⦃n : ℕ⦄ (T : StageType.{u} α n) (xs : Fin 0 → Fin n), T.PrintedClosed xs

/-- **Arity zero for the clauses, proved**: symbols have positive arity, and the empty set is
closed in every plan. -/
theorem arityZeroClausesTarget : ArityZeroClausesTarget.{u} := by
  refine ⟨⟨fun r ↦ (lt_irrefl 0) r.pos⟩, arityZeroTarget.1, fun α n T xs ↦ ⟨fun a ↦ a.elim0, ?_⟩⟩
  rw [univ_eq_empty, image_empty]
  exact T.isWellFormed.isWellFormed.isPlan.empty_mem

end

end VaughtConjecture
