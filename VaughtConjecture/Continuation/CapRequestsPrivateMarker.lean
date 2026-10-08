/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.CapRequestsDonorFace

/-!
# A private marker does not lift the donor obstruction

Roadmap, Layer 3 ((R4) of the table of 3.4); the lift at `⊥` from the donor coatom of
`VaughtConjecture.Continuation.CapRequestsDonorFace` when the marker lies off the common face.

The obstruction `CapRequests.not_botLiftProvisionOf_donor` takes the marker on the common face, so
that the prescription fixes it.  With the marker off the common face (private), the lift may try
to set the marker to `⊥`, which makes the marker value `⊥` and the reading of `T` vacuous.  This is
impossible as soon as the cap reads the dominated cell no higher than the block of the marker.
Compiled in this repository (theorem named):

* **Keeping a cell keeps the block above it**
  (`CellScheme.Rows.IsLawfulBelow.ne_bot_of_row_le_block`): a labelling lawful below a pair, not
  `⊥` at a cell `C` and at a cell `y` that the row of `C` reads at most `μ + j`, is not `⊥` at a
  cell `x` that the row of `C` reads at `μ + i` (`μ` zero or a limit); the locality form of
  `CellScheme.Rows.IsLawful.eq_bot_of_row_le_block`.
* **The marker covers a cell** (`CapRequests.MarkerCovers`): the row of the cap reads the marker at
  an ordinal `μ + i` and the cell at most `μ + j`.
* **The obstruction with a private marker**
  (`CapRequests.not_exists_correct_lift_donor_of_markerCovers`,
  `CapRequests.not_botLiftProvisionOf_donor_of_markerCovers`): a common-face cell `a` of the grade
  of the cap, dominated by the cap and covered by the marker, and a labelling lawful below the donor
  coatom not `⊥` at `a` and `⊥` at a cell of `T`, leave no correct lift, wherever the marker lies:
  the cap is at least the value at `a`, so not `⊥`; the marker is then not `⊥` (the block above
  `a`); and correctness asks the marker value, not `⊥`, below the value `⊥` at the cell of `T`.

So requiring the marker to be private does not remove the obstruction: the needed clause is on the
cap's readings of the live common-face cells of its grade (that some cell of the graded index of
the cap reads each of them above the cap, the negation of `CapRequests.CapDominates`, or that the
marker does not cover them), a condition on the context alone
(`StageType.FirstCoatomInput.capDominates_leftCell_iff`).

## Placement

The (R4) instance of the engine of the restricted catalogue (`roadmap/README.md`, Layer 3, 3.1,
under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme ProfileTower

namespace CellScheme.Rows.IsLawfulBelow

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}}

/-- **Keeping a cell keeps the block above it**: a labelling lawful below `X`, not `⊥` at a cell
`C` below `X` and at a cell `y` read by the row of `C` at most `μ + j`, is not `⊥` at a cell `x`
read by the row of `C` at `μ + i` (`μ` zero or a limit). -/
theorem ne_bot_of_row_le_block {X : Finset α × ℕ} {w : ι → Label.{u}}
    (hw : R.IsLawfulBelow X fun d ↦ w d) {C : ι} (hCX : C ∈ D.below X) {x y : ι}
    (hx : x ∈ D.below (D.gradedIndex C)) (hy : y ∈ D.below (D.gradedIndex C))
    {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) {i j : ℕ}
    (hrx : R.row C ⟨x, hx⟩ = ((μ + i : Ordinal.{u}) : Label.{u}))
    (hry : R.row C ⟨y, hy⟩ ≤ ((μ + j : Ordinal.{u}) : Label.{u})) (hC : w C ≠ ⊥)
    (hwy : w y ≠ ⊥) : w x ≠ ⊥ := by
  intro hwx
  obtain ⟨-, hloc, -⟩ := isLawfulBelow_iff_forall.mp hw
  obtain ⟨g, σ, hwit, heq⟩ := hloc C hCX
  have hCC : min (w C) (w C) = min (σ (R.row C ⟨C, D.mem_below_gradedIndex C⟩))
      (g (D.grade C)) := heq ⟨C, D.mem_below_gradedIndex C⟩
  rw [min_self] at hCC
  have hg : g (D.grade x) ≠ ⊥ := by
    have hle : g (D.grade C) ≤ g (D.grade x) := hwit.antitone ((D.mem_below).mp hx).2
    intro h0
    exact hC (le_bot_iff.mp (hCC ▸ (min_le_right _ _).trans (hle.trans_eq h0)))
  have hσ : σ ((μ + i : Ordinal.{u}) : Label.{u}) = ⊥ := by
    have hxC : min (w x) (w C) = min (σ ((μ + i : Ordinal.{u}) : Label.{u}))
        (g (D.grade x)) := by
      rw [← hrx]; exact heq ⟨x, hx⟩
    rw [hwx, min_eq_left bot_le] at hxC
    exact (min_eq_bot.mp hxC.symm).resolve_right hg
  have hvr := visibilityReplace_coe_add_natCast (n := max i j + 1) hμ
    (show i < max i j + 1 by omega) j
  have hcomm := hwit.visibilityReplace_comm ((μ + i : Ordinal.{u}) : Label.{u}) (max i j + 1)
    (by rw [hσ]; exact bot_le) j (by omega)
  rw [hvr, hσ, visibilityReplace_bot] at hcomm
  have hσy : σ (R.row C ⟨y, hy⟩) = ⊥ := le_bot_iff.mp (hcomm ▸ hwit.monotone hry)
  have hyC : min (w y) (w C) = min (σ (R.row C ⟨y, hy⟩)) (g (D.grade y)) := heq ⟨y, hy⟩
  rw [hσy, min_eq_left bot_le] at hyC
  exact hwy ((min_eq_bot.mp hyC).resolve_right hC)

end CellScheme.Rows.IsLawfulBelow

namespace CapRequests

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {xp xd : Fin (m + 2)}

variable (r) in
/-- **The marker covers a cell `a`**: the row of the cap reads the marker at an ordinal `μ + i`
(`μ` zero or a limit) and `a` at most `μ + j`. -/
def MarkerCovers (a : Fin I.amalgam.card) : Prop :=
  ∃ (μ : Ordinal.{u}) (i j : ℕ), Order.IsSuccPrelimit μ ∧
    I.amalgam.toScheme.rowAt r.cap r.marker = ((μ + i : Ordinal.{u}) : Label.{u}) ∧
    I.amalgam.toScheme.rowAt r.cap a ≤ ((μ + j : Ordinal.{u}) : Label.{u})

/-- **The donor lift at `⊥` with a dominated, covered, live common-face cell has no correct code**,
wherever the marker lies (below the cap). -/
theorem not_exists_correct_lift_donor_of_markerCovers
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade) (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    {k : ℕ} (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k)
    (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp)
    (hmC : r.marker ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex r.cap))
    {a : Fin I.amalgam.card}
    (has : I.amalgam.toCellScheme.scope a ⊆ I.amalgam.toCellScheme.scope r.cap)
    (hag : I.amalgam.toCellScheme.grade a = I.amalgam.toCellScheme.grade r.cap)
    (hdom : r.CapDominates a) (hcov : r.MarkerCovers a) {f : Prof I}
    (ha : a ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) (hfa : f a ≠ ⊥)
    {y : Fin I.amalgam.card} (hy : y ∈ r.T)
    (hyk : y ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) (hfy : f y = ⊥) :
    ¬ ∃ W : Prof I, IsCutLawful I k W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k), W d = f d) ∧
        code k W ∈ rowCat r.IsCorrect k := by
  rintro ⟨W, hW, hWf, hc⟩
  have hcorr := (mem_rowCat.mp hc).2
  have hcb : r.cap ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) := ⟨hcapC, hNk⟩
  have hWC := hW.erase hxp
  have hle : W a ≤ W r.cap := le_cap_of_capDominates hWC hcb has hag hdom
  have hWa : W a ≠ ⊥ := by rw [hWf a ha]; exact hfa
  have hWc : W r.cap ≠ ⊥ := ne_bot_of_le_ne_bot hWa hle
  have haC : a ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex r.cap) :=
    ⟨has, hag.le⟩
  obtain ⟨μ, i, j, hμ, hrm, hra⟩ := hcov
  rw [Scheme.rowAt_of_mem hmC] at hrm
  rw [Scheme.rowAt_of_mem haC] at hra
  have hWm : W r.marker ≠ ⊥ :=
    Rows.IsLawfulBelow.ne_bot_of_row_le_block hWC hcb hmC haC hμ hrm hra hWc hWa
  have hs {d : Fin I.amalgam.card} (hd : I.amalgam.toCellScheme.grade d ≤ k) :
      hat I k (code k W) d = ⊥ ↔ W d = ⊥ := by
    rw [hat_of_le hd, code, orbitCode_apply, orbitMap_eq_bot_iff, hat_of_le hd]
  have hyN : I.amalgam.toCellScheme.grade y ≤ k := (hgr.grade_le_of_mem_T y hy).trans hNk
  have hmN : I.amalgam.toCellScheme.grade r.marker ≤ k := hgr.grade_marker_le.trans hNk
  have hsy : hat I k (code k W) y = ⊥ := (hs hyN).mpr (by rw [hWf y hyk]; exact hfy)
  have h := hcorr.markerValue_le y hy
  rw [hsy, min_bot_left, le_bot_iff, markerValue, min_eq_bot, visibilityReplace_eq_bot_iff,
    hs hmN, hs hNk] at h
  rcases h with h | h
  · exact hWm h
  · exact hWc h

/-- **The lift provision at `⊥` from the donor coatom fails** at such a prescription, wherever the
marker lies. -/
theorem not_botLiftProvisionOf_donor_of_markerCovers
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade) (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    {k : ℕ} (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k)
    (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp)
    (hmC : r.marker ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex r.cap))
    {a : Fin I.amalgam.card}
    (has : I.amalgam.toCellScheme.scope a ⊆ I.amalgam.toCellScheme.scope r.cap)
    (hag : I.amalgam.toCellScheme.grade a = I.amalgam.toCellScheme.grade r.cap)
    (hdom : r.CapDominates a) (hcov : r.MarkerCovers a) {f : Prof I}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ f d)
    (ha : a ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) (hfa : f a ≠ ⊥)
    {y : Fin I.amalgam.card} (hy : y ∈ r.T)
    (hyk : y ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) (hfy : f y = ⊥) :
    ¬ BotLiftProvisionOf r.IsCorrect k xd := fun hprov ↦
  not_exists_correct_lift_donor_of_markerCovers hgr hxp hNk hcapC hmC has hag hdom hcov ha hfa hy
    hyk hfy (hprov f hf)

end CapRequests

end VaughtConjecture
