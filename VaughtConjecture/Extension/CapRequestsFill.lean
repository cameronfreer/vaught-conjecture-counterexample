/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapRequestsGrade

/-!
# The fills from the private coatom over a dead common face

Roadmap, Layer 3 ((R4) of the table of 3.4); the fills from the private coatom
(`CapRequests.CapFillBotAt`, `CapRequests.CapFillPosAt`) that the correct completion asks.

Let `I` be a seed on `m + 2` points, `Cp = univ.erase xp` the private coatom and
`Dd = univ.erase xd` the donor coatom, and `r` cap requests graded by the grades of the amalgam
whose requested cells (`T`, `Z`) lie off the private coatom.  The common face `Cp ∩ Dd` is **dead**
(`CapRequests.IsDeadFace`) when every cell of scope inside it reads itself as `⊥`: then every
labelling lawful below a pair is `⊥` at its cells of the common face
(`CapRequests.eq_bot_of_isDeadFace`), and the two coatoms share no live cell.

* **The fill at `⊥`** (`CapRequests.capFillBotAt_of_isDeadFace`): over a dead common face, with the
  glued labelling `⊤` on `T`, `⊥` on `Z`, and `F` empty, every labelling of the private coatom is
  completed by the glued labelling on the donor side; it is lawful on both coatoms (they agree on
  the dead common face), and its splice is correct (`⊤` on `T`, `⊥` on `Z`; or the cap is `⊥`
  above the grade).
* **The fill at the positive caps** asks the donor side to agree with a prescribed correct profile
  `P` capped at `h` and to be correct for the private prescription above `h`.  The natural donor
  side, `P` raised to `⊤` above `h`, is not a transport by a witness bounded by the grade `k` of the
  layer when `h` is short and self-visible at `k` (`CapRequests.not_isWitness_of_raises`): a short
  self-visible cap at `k` has finite part exactly `k`, and the replacement at the threshold `k`
  with the value `k` crosses it.  So the witness method of the raise reaches only the layers above
  the grades of the raised cells, and the positive fill at the grade of the requested cells is
  left open.

**Where the dead face fails** (`CapRequests.not_isDeadFace_of_label_ne_bot`): over a dead common
face the glued labelling is `⊥` on it, so a seed whose common face carries a live label (for an
(R4) input, a root cell or another cell of the coatom face labelled other than `⊥`) is not covered.

## Placement

The (R4) instance of the engine of the restricted catalogue at the reading grades
(`roadmap/README.md`, Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme ProfileTower

namespace CapRequests

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- The common face of the coatoms `univ.erase xp` and `univ.erase xd` is **dead**: every cell of
scope inside it reads itself as `⊥`. -/
def IsDeadFace (I : Seed.{u} α m) (xp xd : Fin (m + 2)) : Prop :=
  ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∩ univ.erase xd →
    I.amalgam.rows.row d ⟨d, CellScheme.mem_below_gradedIndex _ d⟩ = ⊥

/-- **A lawful labelling is `⊥` at a cell that reads itself as `⊥`.** -/
theorem eq_bot_of_row_self_eq_bot {X : Finset (Fin (m + 2)) × ℕ}
    {w : Fin I.amalgam.card → Label.{u}}
    (hw : I.amalgam.rows.IsLawfulBelow X fun d ↦ w d) {d : Fin I.amalgam.card}
    (hd : d ∈ I.amalgam.toCellScheme.below X)
    (hdead : I.amalgam.rows.row d ⟨d, CellScheme.mem_below_gradedIndex _ d⟩ = ⊥) : w d = ⊥ := by
  obtain ⟨-, hloc, -⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  have h := (hloc d hd).eq_bot (d := ⟨d, CellScheme.mem_below_gradedIndex _ d⟩) hdead
  simpa using h

/-- **Over a dead common face, lawful labellings are `⊥` on it.** -/
theorem eq_bot_of_isDeadFace {xp xd : Fin (m + 2)} (hdead : IsDeadFace I xp xd)
    {X : Finset (Fin (m + 2)) × ℕ} {w : Fin I.amalgam.card → Label.{u}}
    (hw : I.amalgam.rows.IsLawfulBelow X fun d ↦ w d) {d : Fin I.amalgam.card}
    (hd : d ∈ I.amalgam.toCellScheme.below X)
    (hface : I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∩ univ.erase xd) : w d = ⊥ :=
  eq_bot_of_row_self_eq_bot hw hd (hdead d hface)

/-- **A dead common face carries no live glued label**: over a dead common face the glued labelling
is `⊥` there.  So the dead-face fill does not apply to a seed whose common face (the root of an
(R4) input among it) carries a label other than `⊥`. -/
theorem not_isDeadFace_of_label_ne_bot {xp xd : Fin (m + 2)} {d : Fin I.amalgam.card}
    (hface : I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∩ univ.erase xd)
    (hd : I.amalgam.label d ≠ ⊥) : ¬ IsDeadFace I xp xd := fun hdead ↦
  hd (eq_bot_of_row_self_eq_bot (X := I.amalgam.toCellScheme.gradedIndex d)
    (I.amalgam.isLawful.isLawfulBelow _) (CellScheme.mem_below_gradedIndex _ d) (hdead d hface))

variable {r : CapRequests (Fin I.amalgam.card)} {xp xd : Fin (m + 2)}

/-- **The fill at `⊥` from the private coatom over a dead common face**, at every grade `k`: with
the glued labelling `⊤` on `T` and `⊥` on `Z`, these cells off the private coatom, and `F` empty,
every labelling of the private coatom is completed by the glued labelling. -/
theorem capFillBotAt_of_isDeadFace (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hxd : xd ∈ (Pts : Finset (Fin (m + 2))))
    (hne : xd ≠ xp) (hdead : IsDeadFace I xp xd)
    (hT : ∀ y ∈ r.T, I.amalgam.label y = ⊤ ∧ ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp)
    (hZ : ∀ z ∈ r.Z, I.amalgam.label z = ⊥ ∧ ¬ I.amalgam.toCellScheme.scope z ⊆ univ.erase xp)
    (hF : r.F = ∅) (k : ℕ) : CapFillBotAt r xp k := by
  classical
  intro f hf
  set W : Prof I := fun d ↦
    if d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) then f d else I.amalgam.label d
    with hW
  have hWC : I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) fun d ↦ W d :=
    (Rows.isLawfulBelow_congr fun d hd ↦ (ite_eq_left hd).symm).mp hf
  have hlab : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ I.amalgam.label d :=
    I.amalgam.isLawful.isLawfulBelow _
  have hWD : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ W d := by
    refine (Rows.isLawfulBelow_congr fun d hd ↦ ?_).mp hlab
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k)
    · have hface := subset_inter hdC.1 hd.1
      rw [hW]
      simp only [hdC, ite_true]
      rw [eq_bot_of_isDeadFace hdead hlab hd hface, eq_bot_of_isDeadFace hdead hf hdC hface]
    · rw [hW]
      simp only [hdC, ite_false]
  -- A cell off the private coatom keeps its glued label.
  have hoff {y : Fin I.amalgam.card} (hy : ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp) :
      W y = I.amalgam.label y := by
    rw [hW]
    exact ite_eq_right fun h ↦ hy h.1
  refine ⟨W, lawful_pair hxp hxd hne.symm hWC hWD, fun d hd ↦ ite_eq_left hd, ?_⟩
  by_cases hck : I.amalgam.toCellScheme.grade r.cap ≤ k
  · refine isCorrect_of_forall (fun z hz ↦ ?_) (fun f' hf' ↦ by simp [hF] at hf') fun y hy ↦ ?_
    · rw [hat_of_le ((hgr.grade_le_of_mem_Z z hz).trans hck), hoff (hZ z hz).2, (hZ z hz).1]
    · rw [hat_of_le ((hgr.grade_le_of_mem_T y hy).trans hck), hoff (hT y hy).2, (hT y hy).1]
      exact le_top
  · exact isCorrect_of_cap_eq_bot (hat_of_lt (not_le.mp hck))

end CapRequests

/-! ### The raise at a short cap is not a witness bounded by its grade -/

namespace CapRequests

/-- **No map raising above a short self-visible cap is a witness bounded by its grade**: if `σ`
sends every label at least `h` to `⊤` and fixes the labels below `h`, with `h = μ + k` (`μ` zero or
a limit, `0 < k`), then `σ` is not a witness with suppressor `stepSuppressor k`: the replacement at
the threshold `k` with the value `k` sends `μ` to `h`. -/
theorem not_isWitness_of_raises {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) {k : ℕ}
    (hk : 0 < k) {σ : Label.{u} → Label.{u}}
    (hup : ∀ x, ((μ + k : Ordinal.{u}) : Label.{u}) ≤ x → σ x = ⊤)
    (hdown : ∀ x, x < ((μ + k : Ordinal.{u}) : Label.{u}) → σ x = x) :
    ¬ IsWitness (stepSuppressor k) σ := by
  intro hw
  have hμlt : ((μ : Ordinal.{u}) : Label.{u}) < ((μ + k : Ordinal.{u}) : Label.{u}) := by
    exact_mod_cast (lt_add_of_pos_right μ (by exact_mod_cast hk : (0 : Ordinal.{u}) < k))
  have hrep : visibilityReplace k k ((μ : Ordinal.{u}) : Label.{u}) =
      ((μ + k : Ordinal.{u}) : Label.{u}) := by
    have := visibilityReplace_coe_add_natCast (k := 0) (n := k) hμ hk k
    simpa using this
  have h := hw.visibilityReplace_comm (μ : Label.{u}) k (by
    rw [stepSuppressor_of_le le_rfl]; exact le_top) k le_rfl
  rw [hdown _ hμlt, hrep, hup _ le_rfl] at h
  have hne : ((μ + k : Ordinal.{u}) : Label.{u}) ≠ ⊤ := fun h' ↦
    WithTop.coe_ne_top (WithBot.coe_injective h')
  exact hne h.symm

end CapRequests

end VaughtConjecture
