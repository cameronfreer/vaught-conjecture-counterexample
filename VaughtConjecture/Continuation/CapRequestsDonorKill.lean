/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapRequestsGrade
import VaughtConjecture.Extension.BlockKill

/-!
# The donor lift at `⊥` by killing the cap

Roadmap, Layer 3 ((R4) of the table of 3.4); the lift at `⊥` from the donor coatom
(`ProfileTower.BotLiftProvisionOf`) over a live common face, by setting the cap to `⊥`.

The fill of the private coatom (`ProfileTower.exists_isCutLawful_of_coatom_le`) is modified by
killing a set `K` of private cells containing the cap (`CellScheme.Rows.IsLawfulBelow.kill`): every
kept cell not `⊥` must read the cells of `K` in the blocks below some multiple of `ω` and the other
cells at or above it, and availability must be served by kept cells.  Compiled in this repository
(theorem named):

* **A kill set at a fill** (`CapRequests.DonorKillAt`, a named condition on the seed and the
  requests): every profile lawful on the cut at `k` admits such a set `K` of private cells (off
  the donor coatom) containing the cap.
* **The lift at `⊥` from a kill set** (`CapRequests.botLiftProvisionOf_donor_of_kill`): the killed
  fill agrees with the prescription below the donor coatom, is lawful on the cut, and has the cap
  `⊥`, so its splice is correct.

The block-separated clause (`StageType.CapNonDominating`) is the condition at one reader per live
cell; a kill set asks it of every kept reader above the cap, and asks kept servers at every graded
index from the grade of the cap (argued; the derivation of `CapRequests.DonorKillAt` from the
clause is open).

## Placement

The (R4) instance of the engine of the restricted catalogue (`roadmap/README.md`, Layer 3, 3.1,
under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme ProfileTower
open scoped Ordinal

namespace CapRequests

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {xp xd : Fin (m + 2)}

variable (r xp xd) in
/-- **A kill set at every fill** at the grade `k`: for every profile `W₀` lawful on the cut at `k`,
a set `K` of cells off the donor coatom containing the cap, such that every kept cell below the
private coatom not `⊥` in `W₀` reads exactly the cells of `K` (up to cells `⊥` in `W₀`) below some
`ω * β`, and availability below the private coatom is served by kept cells. -/
def DonorKillAt (k : ℕ) : Prop :=
  ∀ W₀ : Prof I, IsCutLawful I k W₀ → ∃ K : Set (Fin I.amalgam.card), r.cap ∈ K ∧
    (∀ d ∈ K, d ∉ I.amalgam.toCellScheme.below (univ.erase xd, k)) ∧
    (∀ e ∈ I.amalgam.toCellScheme.below (univ.erase xp, k), e ∉ K → W₀ e ≠ ⊥ →
      ∃ β : Ordinal.{u}, ∀ d : I.amalgam.toCellScheme.below
          (I.amalgam.toCellScheme.gradedIndex e),
        (I.amalgam.rows.row e d < ((ω * β : Ordinal.{u}) : Label.{u}) → d.1 ∈ K ∨ W₀ d = ⊥) ∧
        (¬ I.amalgam.rows.row e d < ((ω * β : Ordinal.{u}) : Label.{u}) → d.1 ∉ K)) ∧
    ∀ s t, t ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) → s ∉ K → W₀ s ≠ ⊥ →
      I.amalgam.toCellScheme.scope s ⊆ I.amalgam.toCellScheme.scope t →
      I.amalgam.toCellScheme.grade s = I.amalgam.toCellScheme.grade t →
        ∃ u, I.amalgam.toCellScheme.gradedIndex u = I.amalgam.toCellScheme.gradedIndex t ∧
          u ∉ K ∧ W₀ s ≤ W₀ u

/-- **The lift at `⊥` from the donor coatom by killing the cap**, at every grade `k` from the cap:
the fill of the private coatom, killed on a kill set, is lawful on the cut, agrees with the
prescription below the donor coatom, and has the cap `⊥`. -/
theorem botLiftProvisionOf_donor_of_kill (hm : 0 < m)
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade) {k : ℕ}
    (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k) (hkm : k ≤ m + 1)
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hxd : xd ∈ (Pts : Finset (Fin (m + 2))))
    (hne : xd ≠ xp) (hkill : DonorKillAt r xp xd k) :
    BotLiftProvisionOf r.IsCorrect k xd := fun f hf ↦ by
  classical
  have hk0 : 0 < k := (I.amalgam.isWellFormed.isWellFormed.grade_pos r.cap).trans_le hNk
  obtain ⟨W₀, hW₀, hW₀f, -⟩ := exists_isCutLawful_of_coatom_le hm hk0 hkm hxd
    (isSelfVisible_bot _) (P := fun _ ↦ ⊥)
    ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ hf fun _ _ ↦ by simp
  obtain ⟨K, hcK, hKD, hloc, havail⟩ := hkill W₀ hW₀
  set W : Prof I := fun d ↦ if d ∈ K then ⊥ else W₀ d with hWdef
  have hWC : I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) fun d ↦ W d :=
    (hW₀.erase hxp).kill K hloc havail
  have hWD : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ W d :=
    (Rows.isLawfulBelow_congr (w := W₀) (w' := W) fun d hd ↦ by
      simp only [hWdef, show d ∉ K from fun h ↦ hKD d h hd, ite_false]).mp (hW₀.erase hxd)
  have hW : IsCutLawful I k W := lawful_pair hxp hxd hne.symm hWC hWD
  have hWcap : W r.cap = ⊥ := by simp only [hWdef, hcK, ite_true]
  refine ⟨W, hW, fun d hd ↦ ?_, code_mem_rowCat_of_hat hgr hW
    (isCorrect_of_cap_eq_bot (by rw [hat_of_le hNk, hWcap]))⟩
  simp only [hWdef, show d ∉ K from fun h ↦ hKD d h hd, ite_false]
  exact hW₀f d hd

end CapRequests

end VaughtConjecture
