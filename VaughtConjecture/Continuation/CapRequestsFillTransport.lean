/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapRequestsFill
import VaughtConjecture.Extension.SuppressedTransport

/-!
# The fill at `⊥` when the donor follows the root through a transformation

Roadmap, Layer 3 ((R4) of the table of 3.4); the fill of
`CapRequests.capFillBotAt_of_donorFollowsRoot` with the witness bounded by the grade replaced by a
transformation with any suppressor, the form that the locality of a lawful labelling at the cap
gives.

* **The donor follows the root through a transformation** (`CapRequests.DonorFollowsRoot'`): every
  labelling `f` lawful below the private coatom at `k` with the cap not `⊥` is, on the common face
  at the grades `≤ k`, the transformation `d ↦ min (σ (L d)) (g (grade d))` of the glued
  labelling `L` by a witness `(g, σ)` whose shifter reflects `⊥`, whose suppressor is not `⊥` at
  `k`, and which reads the cells of `T` at least as the cap of `f`.
* **It generalizes the donor following the root**
  (`CapRequests.DonorFollowsRoot.donorFollowsRoot'`): a witness bounded by `k` fixing `⊤` is the
  case `g = stepSuppressor k`.
* **The fill** (`CapRequests.capFillBotAt_of_donorFollowsRoot'`): the private prescription with the
  transformed glued labelling on the donor side, lawful by the transport through any suppressor
  (`CellScheme.Rows.IsLawfulBelow.transform_of_apply_eq_bot`), is correct: the cells of `T` are at
  least the cap.  `Z` is read through the shifter (`⊥` to `⊥`) and `F` is empty.

Compiled in this repository (theorem named).

## Placement

The (R4) fills of the engine of the restricted catalogue (`roadmap/README.md`, Layer 3, 3.1, under
"(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme ProfileTower

namespace CapRequests

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {xp xd : Fin (m + 2)}

variable (r xp xd) in
/-- **The donor follows the root through a transformation** at the grade `k`: for every labelling
`f` lawful below the private coatom at `k` with the cap not `⊥`, some witness `(g, σ)` with `σ`
reflecting `⊥`, `g k ≠ ⊥`, and `min (σ ⊤) (g (grade y))` at least the cap of `f` at every `y ∈ T`,
carries the glued labelling to `f` at every cell of the common face of grade at most `k`. -/
def DonorFollowsRoot' (k : ℕ) : Prop :=
  ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) (fun d ↦ f d) → f r.cap ≠ ⊥ →
    ∃ (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}), IsWitness g σ ∧
      (∀ x, σ x = ⊥ → x = ⊥) ∧ g k ≠ ⊥ ∧
      (∀ y ∈ r.T, f r.cap ≤ min (σ ⊤) (g (I.amalgam.toCellScheme.grade y))) ∧
      ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∩ univ.erase xd →
        I.amalgam.toCellScheme.grade d ≤ k →
          min (σ (I.amalgam.label d)) (g (I.amalgam.toCellScheme.grade d)) = f d

/-- **The donor following the root through a witness bounded by the grade** is the case of the step
suppressor, when the cells of `T` have grade at most `k`. -/
theorem DonorFollowsRoot.donorFollowsRoot' {k : ℕ} (h : DonorFollowsRoot r xp xd k)
    (hTk : ∀ y ∈ r.T, I.amalgam.toCellScheme.grade y ≤ k) : DonorFollowsRoot' r xp xd k := by
  intro f hf hc
  obtain ⟨ν, hν, hνbot, hνtop, hνf⟩ := h f hf hc
  refine ⟨stepSuppressor k, ν, hν, hνbot, by simp, fun y hy ↦ ?_, fun d hd hdk ↦ ?_⟩
  · rw [hνtop, stepSuppressor_of_le (hTk y hy), min_self]
    exact le_top
  · rw [stepSuppressor_of_le hdk, min_top_right]
    exact hνf d hd hdk

/-- **The fill at `⊥` from the private coatom when the donor follows the root through a
transformation**, at every grade `0 < k ≤ m + 1`: at a prescription with the cap `⊥` (or above the
grade), the canonical fill; otherwise the private prescription with the transformed glued
labelling on the donor side.  With the glued labelling `⊤` on `T` and `⊥` on `Z`, these cells off
the private coatom, and `F` empty. -/
theorem capFillBotAt_of_donorFollowsRoot' (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hm : 0 < m) (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) (hne : xd ≠ xp) {k : ℕ} (hk : 0 < k)
    (hkm : k ≤ m + 1) (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp)
    (hfol : DonorFollowsRoot' r xp xd k)
    (hT : ∀ y ∈ r.T, I.amalgam.label y = ⊤ ∧ ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp)
    (hZ : ∀ z ∈ r.Z, I.amalgam.label z = ⊥ ∧ ¬ I.amalgam.toCellScheme.scope z ⊆ univ.erase xp)
    (hF : r.F = ∅) : CapFillBotAt r xp k := by
  classical
  intro f hf
  by_cases hck : I.amalgam.toCellScheme.grade r.cap ≤ k ∧ f r.cap ≠ ⊥
  swap
  · obtain ⟨W, hW, hWf, -⟩ := exists_isCutLawful_of_coatom_le hm hk hkm hxp (isSelfVisible_bot k)
      (P := fun _ ↦ ⊥) ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ hf
      fun _ _ ↦ by simp
    refine ⟨W, hW, hWf, isCorrect_of_cap_eq_bot ?_⟩
    by_cases hg : I.amalgam.toCellScheme.grade r.cap ≤ k
    · rw [hat_of_le hg, hWf _ ⟨hcapC, hg⟩]
      exact not_not.mp fun h ↦ hck ⟨hg, h⟩
    · exact hat_of_lt (not_le.mp hg)
  obtain ⟨hg, hc⟩ := hck
  obtain ⟨g, σ, hw, hσbot, hgk, hTc, hσf⟩ := hfol f hf hc
  set ψ : Prof I := fun d ↦ min (σ (I.amalgam.label d)) (g (I.amalgam.toCellScheme.grade d))
    with hψ
  set W : Prof I := fun d ↦
    if d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) then f d else ψ d with hW
  have hWf (d) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k)) : W d = f d := by
    rw [hW]; simp only [hd, ite_true]
  have hWC : I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) fun d ↦ W d :=
    (Rows.isLawfulBelow_congr (w := f) (w' := W) fun d hd ↦ (hWf d hd).symm).mp hf
  have hψA : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ ψ d := by
    refine (I.amalgam.isLawful.isLawfulBelow (univ.erase xd, k)).transform_of_apply_eq_bot hw
      fun d hd ↦ ?_
    have hgd : g (I.amalgam.toCellScheme.grade d.1) ≠ ⊥ :=
      ne_bot_of_le_ne_bot hgk (hw.antitone d.2.2)
    rw [min_eq_bot, or_iff_left hgd] at hd
    exact hσbot _ hd
  have hWD : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ W d := by
    refine (Rows.isLawfulBelow_congr (w := ψ) (w' := W) fun d hd ↦ ?_).mp hψA
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k)
    · rw [hWf d hdC]
      exact hσf d (subset_inter hdC.1 hd.1) hdC.2
    · rw [hW]; simp only [hdC, ite_false]
  have hoff {y : Fin I.amalgam.card} (hy : ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp) :
      W y = ψ y := by
    rw [hW]
    exact ite_eq_right fun h ↦ hy h.1
  have hWcap : W r.cap = f r.cap := hWf _ ⟨hcapC, hg⟩
  refine ⟨W, lawful_pair hxp hxd hne.symm hWC hWD, hWf, ?_⟩
  refine isCorrect_of_forall (fun z hz ↦ ?_) (fun f' hf' ↦ by simp [hF] at hf') fun y hy ↦ ?_
  · rw [hat_of_le ((hgr.grade_le_of_mem_Z z hz).trans hg), hoff (hZ z hz).2, hψ]
    simp only [(hZ z hz).1, hw.map_bot, min_bot_left]
  · -- the marker value is at most the cap, which is at most the transformed `⊤` at `y`
    rw [hat_of_le ((hgr.grade_le_of_mem_T y hy).trans hg), hoff (hT y hy).2]
    refine (min_le_right _ _).trans ?_
    rw [hat_of_le hg, hWcap]
    refine (hTc y hy).trans ?_
    rw [hψ]
    simp only [(hT y hy).1, le_refl]

end CapRequests

end VaughtConjecture
