/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderTowerContextLift
import VaughtConjecture.Continuation.GrowthFaceAdmission
import VaughtConjecture.MainTheorem.SeedLadderCarrier

/-!
# The lift of the ladder tower from the context coatom below the threshold

Roadmap, Layer 3 ((R3) and (R4), the bountifulness of the recognizing growth carrier).

**Superseded.**  The carrier is now built over the replicated scheme of the attachment
(`Seed.replicated`), not over the ladder tower of the amalgam; the context lift there is reduced in
`VaughtConjecture.Extension.LadderTowerContextLiftReplicated` and
`VaughtConjecture.Extension.LadderTowerContextLiftState`.  This file is kept; its statements are
about the amalgam tower only.

For the admission predicate of the ladder tower (`Seed.towerAdmits`), a state vanishing above a
grade below the threshold is admitted: its cap value is `⊥`
(`Seed.towerAdmits_of_vanishing`).  So at every grade `j` with `2 ≤ j` and `j` below the threshold
the state lift from the context coatom holds (`Seed.contextStateLift_towerAdmits`), and the lift of
the ladder tower from the context coatom into `(univ, j)` follows from the coding of states at `j`
alone (`Seed.cappedLift_context_of_lt_threshold`).

From the threshold on, the state lift asks admission of a state reading the prescription on the
context.  **At a low cap** (the prescription's value at the cap below the cap `c`), admission
transfers from the ambient (`Seed.towerAdmits_of_min_eq`, through
`StageType.GrowthRequests.AdmitsOnClass.of_min_eq`), so the amalgam lift is admitted as soon as the
ambient, read on the amalgam, is (`Seed.exists_stateLift_of_lowCap`).  Two inputs stay open: the
admission of the ambient's state (a recognition statement for the sections of the tower below
`(univ, j)`), and the high cap (the prescription's value at the cap at least `c`), where the donor
values must be chosen by a relative lift through the second coatom type.

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

/-! ### From the threshold on: the low cap -/

/-- **Admission transfers to a state agreeing capped above the cap value**: if `S` satisfies the
admission predicate, `P` agrees with `S` capped at `c ≠ ⊥` at the cells of grade at most the
threshold, and the cap value of `S` is below `c` and self-visible at the threshold, then `P`
satisfies the admission predicate (`StageType.GrowthRequests.AdmitsOnClass.of_min_eq`). -/
theorem towerAdmits_of_min_eq (Q : StageType.GrowthRequests I.left d.toScheme) {k : ℕ}
    {S P : Fin I.amalgam.card → Label.{u}} (hS : I.towerAdmits hd Q k S) {c : Label.{u}}
    (hc0 : c ≠ ⊥) (hag : ∀ a, I.amalgam.toCellScheme.grade a ≤ Q.threshold →
      min (P a) c = min (S a) c)
    (hcap : S (I.ctxCell Q.cap) < c) (hvis : IsSelfVisible Q.threshold (S (I.ctxCell Q.cap)))
    (hoff : ∀ j ∈ Q.exacts, Q.offset j ≤ Q.threshold) (hR : Q.markerOffset ≤ Q.threshold) :
    I.towerAdmits hd Q k P := by
  intro hk
  have hhat (a : Fin I.amalgam.card) :
      min (I.hatAt Q.threshold P a) c = min (I.hatAt Q.threshold S a) c := by
    unfold hatAt
    by_cases h : I.amalgam.toCellScheme.grade a ≤ Q.threshold
    · rw [ite_eq_left h, ite_eq_left h]
      exact hag a h
    · rw [ite_eq_right h, ite_eq_right h]
  have hg : I.amalgam.toCellScheme.grade (I.ctxCell Q.cap) = Q.threshold := grade_ctxCell Q.cap
  have hhatcap : I.hatAt Q.threshold S (I.ctxCell Q.cap) = S (I.ctxCell Q.cap) := by
    unfold hatAt
    rw [hg, ite_eq_left le_rfl]
  exact GrowthRequests.AdmitsOnClass.of_min_eq (Q := Q) (hS hk) hc0 (fun x ↦ hhat _)
    (fun j ↦ hhat _) (hhatcap ▸ hcap) (hhatcap ▸ hvis) hoff hR

/-- The cell of the amalgam at a cell of the context lies in the context coatom. -/
theorem scope_ctxCell_subset (x : Fin I.left.card) :
    I.amalgam.toCellScheme.scope (I.ctxCell x) ⊆ ctxCoatom m := by
  rw [ctxCell, Scheme.scope_faceCell]
  intro y hy
  obtain ⟨z, -, rfl⟩ := mem_map.mp hy
  simp [ctxCoatom, Fin.castSucc_ne_last]

/-- **The state lift from the threshold on, at a low cap**: at a grade `j` with the threshold at
most `j`, if the ambient read on the amalgam (extended by `⊥` above the grade) satisfies the
admission predicate and the prescription's value at the cap is below the cap `c`, the amalgam lift
(`Seed.exists_amalgamLift`) satisfies the admission predicate
(`Seed.towerAdmits_of_min_eq`). -/
theorem exists_stateLift_of_lowCap {H : ℕ} {Γ : Finset Label.{u}} {B' : ℕ}
    (Q : StageType.GrowthRequests I.left d.toScheme)
    (hoff : ∀ j ∈ Q.exacts, Q.offset j ≤ Q.threshold) (hR : Q.markerOffset ≤ Q.threshold)
    {j : ℕ} (hj : 0 < j) (hjm : j ≤ m + 1) (hNj : Q.threshold ≤ j) (c : Label.{u})
    (hc : IsSelfVisible j c)
    (p : (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.toCellScheme.below (ctxCoatom m, j) →
      Label.{u})
    (q : (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) → Label.{u})
    (hp : (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.rows.IsLawfulBelow (ctxCoatom m, j) p)
    (hq : (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.rows.IsLawfulBelow
      ((univ : Finset (Fin (m + 2))), j) q)
    (hpq : ∀ d, min (q (Set.inclusion (CellScheme.below_mono _ (ctxCoatom_le j)) d)) c =
      min (p d) c)
    (S : Fin I.amalgam.card → Label.{u}) (hamb : I.towerAdmits hd Q (m + 2) S)
    (hSq : ∀ (d : (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j)) a,
      I.towerAmalgamEmb H Γ (I.towerAdmits hd Q) B' a = d.1 → S a = q d)
    (hlow : ∀ (d : (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.toCellScheme.below
        (ctxCoatom m, j)),
      I.towerAmalgamEmb H Γ (I.towerAdmits hd Q) B' (I.ctxCell Q.cap) = d.1 → p d < c) :
    ∃ P : Fin I.amalgam.card → Label.{u}, I.amalgam.rows.IsLawful P ∧
      I.towerAdmits hd Q (m + 2) P ∧
      (∀ (d : (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.toCellScheme.below
          (ctxCoatom m, j)) a,
        I.towerAmalgamEmb H Γ (I.towerAdmits hd Q) B' a = d.1 → P a = p d) ∧
      ∀ (d : (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j)) a,
        I.towerAmalgamEmb H Γ (I.towerAdmits hd Q) B' a = d.1 → min (P a) c = min (q d) c := by
  obtain ⟨P, hPl, -, hPp, hPq⟩ := exists_amalgamLift hj hjm c hc p q hp hq hpq
  refine ⟨P, hPl, ?_, hPp, hPq⟩
  set φ := I.towerAmalgamEmb H Γ (I.towerAdmits hd Q) B'
  have hmemY (a : Fin I.amalgam.card) (ha : I.amalgam.toCellScheme.grade a ≤ j) :
      φ a ∈ (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j) :=
    (towerAmalgamEmb_mem_below_iff a _).mpr ⟨subset_univ _, ha⟩
  have hg : I.amalgam.toCellScheme.grade (I.ctxCell Q.cap) = Q.threshold := grade_ctxCell Q.cap
  have hcg : I.amalgam.toCellScheme.grade (I.ctxCell Q.cap) ≤ j := hg ▸ hNj
  have hcapX : φ (I.ctxCell Q.cap) ∈
      (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.toCellScheme.below (ctxCoatom m, j) :=
    (towerAmalgamEmb_mem_below_iff _ _).mpr ⟨scope_ctxCell_subset Q.cap, hcg⟩
  have hPcap : P (I.ctxCell Q.cap) < c := by
    rw [hPp ⟨_, hcapX⟩ _ rfl]
    exact hlow ⟨_, hcapX⟩ rfl
  have hScap : S (I.ctxCell Q.cap) = P (I.ctxCell Q.cap) := by
    have h1 := hPq ⟨_, hmemY _ hcg⟩ _ rfl
    rw [← hSq ⟨_, hmemY _ hcg⟩ _ rfl, min_eq_left hPcap.le] at h1
    rcases le_total (S (I.ctxCell Q.cap)) c with hle | hle
    · rw [min_eq_left hle] at h1
      exact h1.symm
    · rw [min_eq_right hle] at h1
      exact absurd h1 hPcap.ne
  have hc0 : c ≠ ⊥ := fun h ↦ not_lt_bot (h ▸ hPcap)
  refine towerAdmits_of_min_eq Q hamb hc0 (fun a ha ↦ ?_) (hScap ▸ hPcap) ?_ hoff hR
  · rw [hPq ⟨_, hmemY a (ha.trans hNj)⟩ a rfl, hSq ⟨_, hmemY a (ha.trans hNj)⟩ a rfl]
  · rw [hSq ⟨_, hmemY _ hcg⟩ _ rfl]
    have hgT : (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.toCellScheme.grade
        (φ (I.ctxCell Q.cap)) = Q.threshold :=
      (congrArg Prod.snd ((I.isLowerEmbedding_towerAmalgamEmb H Γ _ B').gradedIndex_eq_of_scope_eq
        (I.scope_towerAmalgamEmb H Γ _ B') (I.ctxCell Q.cap))).trans hg
    have ho : IsSelfVisible ((I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.toCellScheme.grade
        (φ (I.ctxCell Q.cap))) (q ⟨_, hmemY _ hcg⟩) := hq.orderly ⟨_, hmemY _ hcg⟩
    rw [hgT] at ho
    exact ho

end Seed

end VaughtConjecture
