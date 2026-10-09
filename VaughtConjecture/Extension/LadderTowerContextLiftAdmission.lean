/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderTowerContextLift
import VaughtConjecture.MainTheorem.SeedLadderCarrier

/-!
# The lift of the ladder tower from the context coatom below the threshold

Roadmap, Layer 3 ((R3) and (R4), the bountifulness of the recognizing growth carrier).

For the admission predicate of the ladder tower (`Seed.towerAdmits`), a state vanishing above a
grade below the threshold is admitted: its cap value is `⊥`
(`Seed.towerAdmits_of_vanishing`).  So at every grade `j` with `2 ≤ j` and `j` below the threshold
the state lift from the context coatom holds (`Seed.contextStateLift_towerAdmits`), and the lift of
the ladder tower from the context coatom into `(univ, j)` follows from the coding of states at `j`
alone (`Seed.cappedLift_context_of_lt_threshold`).

From the threshold on, the state lift asks admission of a state reading the prescription on the
context; that case is not treated here.

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {e₀ : Fin n ↪ Fin m}
  {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (e₀.trans Fin.castSuccEmb)) I.amalgam = some d}

/-- The cell of the amalgam at the cap has the grade of the cap, the threshold. -/
theorem grade_ctxCell (x : Fin I.left.card) :
    I.amalgam.toCellScheme.grade (I.ctxCell x) = I.left.toCellScheme.grade x :=
  I.amalgam.toScheme.grade_faceCell I.comap_left_amalgam_scheme x

/-- **A state vanishing above a grade below the threshold is admitted**: its cap value is `⊥`. -/
theorem towerAdmits_of_vanishing (Q : StageType.GrowthRequests I.left d.toScheme) {j k : ℕ}
    (hjN : j < Q.threshold) {P : Fin I.amalgam.card → Label.{u}}
    (hP : ∀ a, j < I.amalgam.toCellScheme.grade a → P a = ⊥) : I.towerAdmits hd Q k P := by
  intro _ _ hcap
  refine absurd ?_ hcap
  have hg : I.amalgam.toCellScheme.grade (I.ctxCell Q.cap) = Q.threshold := grade_ctxCell Q.cap
  change (if _ then _ else _) = _
  rw [hg, ite_eq_left le_rfl]
  exact hP _ (hg ▸ hjN)

/-- **The state lift from the context coatom below the threshold**, for the admission predicate
of the ladder tower. -/
theorem contextStateLift_towerAdmits (H : ℕ) (Γ : Finset Label.{u}) (B' : ℕ)
    (Q : StageType.GrowthRequests I.left d.toScheme) {j : ℕ} (hj : 0 < j) (hjm : j ≤ m + 1)
    (hjN : j < Q.threshold) : ContextStateLift I H Γ (I.towerAdmits hd Q) B' j :=
  contextStateLift_of_vanishing hj hjm fun _ _ hP ↦ towerAdmits_of_vanishing Q hjN hP

/-- **The lift of the ladder tower from the context coatom below the threshold**, from the coding
of states: at a grade `j` with `2 ≤ j ≤ m + 1` below the threshold, the coding of states at `j`
gives the capped lift from `(univ.erase (Fin.last (m + 1)), j)` to `(univ, j)`. -/
theorem cappedLift_context_of_lt_threshold {H : ℕ} {Γ : Finset Label.{u}} {B' : ℕ}
    (hH : 0 < H) (hcard : I.amalgam.card ≤ H) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (Q : StageType.GrowthRequests I.left d.toScheme) {j : ℕ} (hj : 2 ≤ j) (hjm : j ≤ m + 1)
    (hjN : j < Q.threshold) (hC : StateCoding I H Γ (I.towerAdmits hd Q) B' j) :
    (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.rows.CappedLift
      (X := (univ.erase (Fin.last (m + 1)), j)) (Y := ((univ : Finset (Fin (m + 2))), j))
      ⟨erase_subset _ _, le_rfl⟩ :=
  cappedLift_context_of_stateLift hH hcard hΓ (fun k R h ↦ I.towerAdmits_succ hd Q k R h)
    (contextStateLift_towerAdmits H Γ B' Q (by omega) hjm hjN) hC

end Seed

end VaughtConjecture
