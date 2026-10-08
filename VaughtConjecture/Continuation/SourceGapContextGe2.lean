/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapContext
import VaughtConjecture.Continuation.AvailableTopDetermination

/-!
# Source-gap contexts of grade at least two: the acquisition (work file)

WORK FILE (branch `research/work-twolift`).  No `sorry`.

The grade `K` of an acquired source-gap context is the top-grade supremum of the model
(`Realization.exists_covers_isSourceGapContextAt`: every occurrence above the tail has top grade
`K`, and the owner has grade `K`).  It is fixed by the model, not by the choice of occurrence.  So
the acquisition restricted to `2 ≤ K` (`Realization.IsSourceGapContextGe2`) holds **exactly when no
model at a limit stage with no cover that is a globally rigid core has top-grade supremum `1`**
(`Realization.residualAcquisition_ge2_iff`).  Whether such a model exists is not decided here.
-/

universe u w

namespace VaughtConjecture.Realization

/-- **A source-gap context of grade at least two.** -/
def IsSourceGapContextGe2 {α : Ordinal.{u}} {n k : ℕ} (K : ℕ) (t' : StageType.{u} α k)
    (h : Fin n ↪ Fin k) : Prop :=
  t'.IsSourceGapContext K h ∧ 2 ≤ K

/-- **The acquisition at grade at least two is the exclusion of the residual grade `1`**: residual
acquisition of source-gap contexts of grade at least two holds if and only if every model at a
limit stage with no cover that is a globally rigid core has top-grade supremum other than `1`.
Forward: the empty tuple covers a stage type on no points, and the acquired context has grade the
top-grade supremum.  Backward: the supremum is at least `1` (`IsModel.one_le_topGradeSup`), so at
least `2`, and the acquisition is `residualAcquisition_isSourceGapContext`. -/
theorem residualAcquisition_ge2_iff :
    ResidualAcquisition.{u, w} (fun K t' h ↦ IsSourceGapContextGe2 K t' h) ↔
      ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄,
        Order.IsSuccLimit α → R.IsModel →
        (¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
          R.IsGloballyRigidCore c) → R.topGradeSup ≠ 1 := by
  constructor
  · intro hacq α M R hα hR hcore h1
    obtain ⟨p, hp⟩ := hR.exists_covers_zero
    obtain ⟨_, _, _, _, _, _, -, h2⟩ :=
      hacq.exists_context (K := 1) hα hR hcore (by exact_mod_cast h1) p ![] hp
    omega
  · intro hne
    refine ⟨fun α M R K hα hR hcore hK n t c hc ↦ ?_⟩
    obtain ⟨k, t', c', h, hc', hcc', hP⟩ :=
      residualAcquisition_isSourceGapContext.exists_context hα hR hcore hK t c hc
    have h1 : (1 : ℕ∞) ≤ K := hK ▸ hR.one_le_topGradeSup hα hcore
    have hK1 : K ≠ 1 := fun e ↦ hne hα hR hcore (by rw [hK, e]; rfl)
    have : 1 ≤ K := by exact_mod_cast h1
    exact ⟨k, t', c', h, hc', hcc', hP, by omega⟩

end VaughtConjecture.Realization
