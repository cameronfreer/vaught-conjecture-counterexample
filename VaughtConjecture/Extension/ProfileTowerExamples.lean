/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ProfileTowerCompletion
import VaughtConjecture.Extension.ThinCompletionTLTL

/-!
# Tests of the completion at every arity: `seedL` and a seed on six points

Two compiled instances of `ProfileTower.nonempty_completionBelowFullGrade_of_three_le`:

* at `m = 3`, the asymmetric seed `seedL`, where the step of the tower fails at the grade `3`
  (`TwoFaceLiftExistsCounterexample.not_towerInvariant_three_seedL`), has the completion through
  the levels of rank-normalized profiles (`ProfileTowerExamples.seedL_completion`);
* at `m = 4`, the seed `ProfileTowerExamples.seed6 hα` on six points: its coatom types are legal
  stage types on five points with face `TL` along `Fin.castSuccEmb`, the coatom extensions with
  apex of `seedL` and of `seedLL` (`TowerProfile.completion`,
  `CompletionBelowFullGrade.exists_coatomExtension`).  Their faces along
  `extendByLast Fin.castSuccEmb` are `T5` and `TL` (`ProfileTowerExamples.seed6_faces`), so the
  two coatoms of the seed carry different types on the second point set.  It has a completion
  below the full grade and the coatom extension with apex (`ProfileTowerExamples.seed6_completion`,
  `ProfileTowerExamples.exists_coatomExtension_seed6`); compiled in this repository (theorem
  named).
-/

universe u

namespace VaughtConjecture.ProfileTowerExamples

open Finset TwoFaceLiftExistsCounterexample

/-- **The test at `seedL`, through the levels**: the asymmetric seed, where the step of the tower
fails at the grade `3`, has a completion below the full grade. -/
theorem seedL_completion (α : Ordinal.{u}) :
    Nonempty (CompletionBelowFullGrade (seedL α)) ∧ ¬ (seedL α).TowerInvariant 3 :=
  ⟨ProfileTower.nonempty_completionBelowFullGrade_of_three_le _ le_rfl,
    not_towerInvariant_three_seedL α⟩

variable {α : Ordinal.{u}}

/-- The coatom extension with apex of `seedL`, on five points. -/
theorem exists_extension_seedL (hα : Order.IsSuccPrelimit α) :
    ∃ t : StageType.{u} α 5, t.IsLegal ∧
      StageType.restrictFace Fin.castSuccEmb t = some (TL α) ∧
      StageType.restrictFace (extendByLast Fin.castSuccEmb) t =
        some (CaseSplitCounterexample.T5 α) ∧
      ∃ d, t.toCellScheme.gradedIndex d = (univ, 5) ∧ ∀ e, t.label e ≤ t.label d :=
  (TowerProfile.completion (seedL α)).exists_coatomExtension hα

/-- The coatom extension with apex of `seedLL`, on five points. -/
theorem exists_extension_seedLL (hα : Order.IsSuccPrelimit α) :
    ∃ t : StageType.{u} α 5, t.IsLegal ∧
      StageType.restrictFace Fin.castSuccEmb t = some (TL α) ∧
      StageType.restrictFace (extendByLast Fin.castSuccEmb) t = some (TL α) ∧
      ∃ d, t.toCellScheme.gradedIndex d = (univ, 5) ∧ ∀ e, t.label e ≤ t.label d :=
  (TowerProfile.completion (seedLL α)).exists_coatomExtension hα

/-- **A seed on six points**: the coatom extensions of `seedL` and of `seedLL`, over their common
face `TL` along `Fin.castSuccEmb`. -/
noncomputable def seed6 (hα : Order.IsSuccPrelimit α) : Seed.{u} α 4 :=
  Seed.ofCoatoms (exists_extension_seedL hα).choose_spec.1
    (exists_extension_seedLL hα).choose_spec.1
    (exists_extension_seedL hα).choose_spec.2.1 (exists_extension_seedLL hα).choose_spec.2.1

/-- The faces of the two coatom types of `seed6` along `extendByLast Fin.castSuccEmb` are `T5`
and `TL`. -/
theorem seed6_faces (hα : Order.IsSuccPrelimit α) :
    StageType.restrictFace (extendByLast Fin.castSuccEmb) (seed6 hα).left =
        some (CaseSplitCounterexample.T5 α) ∧
      StageType.restrictFace (extendByLast Fin.castSuccEmb) (seed6 hα).right = some (TL α) :=
  ⟨(exists_extension_seedL hα).choose_spec.2.2.1, (exists_extension_seedLL hα).choose_spec.2.2.1⟩

/-- **The test at `m = 4`**: `seed6` has a completion below the full grade
(`ProfileTower.nonempty_completionBelowFullGrade_of_three_le`). -/
theorem seed6_completion (hα : Order.IsSuccPrelimit α) :
    Nonempty (CompletionBelowFullGrade (seed6 hα)) :=
  ProfileTower.nonempty_completionBelowFullGrade_of_three_le _ (by omega)

/-- **The coatom extension with apex of `seed6`**, on seven points. -/
theorem exists_coatomExtension_seed6 (hα : Order.IsSuccPrelimit α) :
    ∃ t : StageType.{u} α 6, t.IsLegal ∧
      StageType.restrictFace Fin.castSuccEmb t = some (seed6 hα).left ∧
      StageType.restrictFace (extendByLast Fin.castSuccEmb) t = some (seed6 hα).right ∧
      ∃ d, t.toCellScheme.gradedIndex d = (univ, 6) ∧ ∀ e, t.label e ≤ t.label d :=
  (seed6_completion hα).some.exists_coatomExtension hα

end VaughtConjecture.ProfileTowerExamples
