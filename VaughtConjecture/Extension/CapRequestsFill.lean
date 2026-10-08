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
* **The fill at the positive caps** (`CapRequests.capFillPosAt_of_isDeadFace`), at a grade `k ≥ 2`
  **above the grades of the requested cells**, over a dead common face, with `F` empty: the donor
  coatom is filled at the ambient `P`, raised to `⊤` above the cap `h` below the grade `k`
  (`Label.raise`, a witness bounded by `k - 1` because `h` is self-visible at `k`), and lifted back
  to the grade `k` at the cap `h` within the donor coatom (bountifulness of the amalgam).  The tops
  are `⊤` where the fill is at least `h`, and read the marker value through `P` below `h`
  (`CapRequests.min_markerValue_eq`).
* At the grade of the requested cells the raise is not available: no map raising above a short
  self-visible cap at `k` is a witness bounded by `k` (`CapRequests.not_isWitness_of_raises`).

**The donor following the root** (`CapRequests.DonorFollowsRoot`,
`CapRequests.capFillBotAt_of_donorFollowsRoot`): over a live common face, the fill at `⊥` holds
when every prescription with the cap not `⊥` is, on the common face, the image of the glued
labelling under a witness bounded by `k`, reflecting `⊥` and fixing `⊤`: the donor side is the glued
labelling transported along it.  The transport fails across a tie of the glued labelling that the
prescription separates (`CapRequests.not_exists_transport_of_tie`) and across an inversion
(`CapRequests.not_exists_transport_of_inversion`).

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

/-- The capped marker values agree when the states agree capped at a cap `h` self-visible at the
threshold. -/
theorem min_markerValue_eq {s s' : Fin I.amalgam.card → Label.{u}} {h : Label.{u}}
    (hh : IsSelfVisible r.N h) (hag : ∀ d, min (s d) h = min (s' d) h) :
    min (r.markerValue s) h = min (r.markerValue s') h := by
  have hR : min (visibilityReplace r.N r.R (s r.marker)) h =
      min (visibilityReplace r.N r.R (s' r.marker)) h := by
    rw [← visibilityReplace_min_of_isSelfVisible r.R_lt_N.le hh,
      ← visibilityReplace_min_of_isSelfVisible r.R_lt_N.le hh, hag]
  calc min (r.markerValue s) h
      = min (min (visibilityReplace r.N r.R (s r.marker)) h) (min (s r.cap) h) := by
        rw [markerValue, min_min_min_comm, min_self]
    _ = min (min (visibilityReplace r.N r.R (s' r.marker)) h) (min (s' r.cap) h) := by
        rw [hR, hag]
    _ = min (r.markerValue s') h := by rw [markerValue, min_min_min_comm, min_self]

/-- **The fill at the positive caps from the private coatom over a dead common face**, at a grade
`k ≥ 2` above the grades of the requested cells: the other coatom is filled at the ambient `P`,
raised to `⊤` above the cap `h` below the grade `k` (`Label.raise`, a witness bounded by `k - 1`
since `h` is self-visible at `k`), and lifted back to the grade `k` at the cap `h` within the donor
coatom.  The tops then read the private marker: below `h` through the correctness of `P`, above `h`
as `⊤`.  With `F` empty, `T` and `Z` off the private coatom and of grade below `k`, and the cap on
the private coatom. -/
theorem capFillPosAt_of_isDeadFace (hgr : r.IsGraded I.amalgam.toCellScheme.grade) (hm : 0 < m)
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hxd : xd ∈ (Pts : Finset (Fin (m + 2))))
    (hne : xd ≠ xp) (hdead : IsDeadFace I xp xd) {k : ℕ} (hk : 2 ≤ k) (hkm : k ≤ m + 1)
    (hT : ∀ y ∈ r.T, ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp ∧
      I.amalgam.toCellScheme.grade y < k)
    (hZ : ∀ z ∈ r.Z, ¬ I.amalgam.toCellScheme.scope z ⊆ univ.erase xp ∧
      I.amalgam.toCellScheme.grade z < k)
    (hF : r.F = ∅) (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp) :
    CapFillPosAt r xp k := by
  classical
  intro h hh _ hb P hP hPc f hf hfP
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  -- The fill of the donor coatom at the ambient `P`.
  obtain ⟨W₀, hW₀, hW₀f, hW₀P⟩ := exists_isCutLawful_of_coatom_le hm (by omega) hkm hxp hh hP hf hfP
  -- The raise below the grade `k`, within the donor coatom.
  have hDK : ((univ.erase xd, K) : Finset (Fin (m + 2)) × ℕ) ≤ (univ.erase xd, K + 1) :=
    ⟨subset_rfl, Nat.le_succ K⟩
  have hp : I.amalgam.rows.IsLawfulBelow (univ.erase xd, K)
      fun d ↦ Label.raise h (W₀ d) :=
    ((hW₀.erase hxd).mono (X := (univ.erase xd, K)) hDK).map_of_apply_eq_bot (fun d ↦ d.2.2)
      (isWitness_raise hh hb) (fun _ ↦ eq_bot_of_raise_eq_bot)
  have hXf : ((univ.erase xd, K) : Finset (Fin (m + 2)) × ℕ) ∈
      I.amalgam.toCellScheme.gradedFaces :=
    ⟨I.erase_mem_faces hxd, by omega, by simp only; rw [Seed.card_erase]; omega⟩
  have hYf : ((univ.erase xd, K + 1) : Finset (Fin (m + 2)) × ℕ) ∈
      I.amalgam.toCellScheme.gradedFaces :=
    ⟨I.erase_mem_faces hxd, by omega, by simp only; rw [Seed.card_erase]; omega⟩
  obtain ⟨v, hv, hvP, hvp⟩ := (Rows.cappedLift_iff_forall_exists hDK).mp
    (I.isBountiful hXf hYf hDK) h hh (fun d ↦ Label.raise h (W₀ d)) (fun d ↦ P d) hp
    (hP.erase hxd) fun d ↦ by rw [min_raise, hW₀P]
  -- The fill.
  set W : Prof I := fun d ↦
    if d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1) then f d
    else if hD : d ∈ I.amalgam.toCellScheme.below (univ.erase xd, K + 1) then v ⟨d, hD⟩
    else P d with hW
  have hWv (d) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase xd, K + 1))
      (hdC : d ∉ I.amalgam.toCellScheme.below (univ.erase xp, K + 1)) : W d = v ⟨d, hd⟩ := by
    rw [hW]; simp only [hdC, hd, ite_false, dite_true]
  have hvext : I.amalgam.rows.IsLawfulBelow (univ.erase xd, K + 1)
      fun d ↦ Rows.extendBot (univ.erase xd, K + 1) v d := Rows.isLawfulBelow_extendBot.mpr hv
  have hWf (d) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1)) : W d = f d := by
    rw [hW]; simp only [hd, ite_true]
  have hWC : I.amalgam.rows.IsLawfulBelow (univ.erase xp, K + 1) fun d ↦ W d :=
    (Rows.isLawfulBelow_congr (w := f) (w' := W) fun d hd ↦ (hWf d hd).symm).mp hf
  have hWD : I.amalgam.rows.IsLawfulBelow (univ.erase xd, K + 1) fun d ↦ W d := by
    refine (Rows.isLawfulBelow_congr (w' := W) fun d hd ↦ ?_).mp hvext
    rw [Rows.extendBot_of_mem v hd]
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1)
    · have hface := subset_inter hdC.1 hd.1
      have h1 := eq_bot_of_isDeadFace hdead hvext hd hface
      rw [Rows.extendBot_of_mem v hd] at h1
      rw [h1, hW]
      simp only [hdC, ite_true]
      rw [eq_bot_of_isDeadFace hdead hf hdC hface]
    · exact (hWv d hd hdC).symm
  -- The fill agrees with `P` capped at `h`.
  have hWP (d : Fin I.amalgam.card) : min (W d) h = min (P d) h := by
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1)
    · rw [hW]; simp only [hdC, ite_true]; exact hfP d hdC
    by_cases hdD : d ∈ I.amalgam.toCellScheme.below (univ.erase xd, K + 1)
    · rw [hWv d hdD hdC]; exact hvP ⟨d, hdD⟩
    · rw [hW]; simp only [hdC, hdD, ite_false, dite_false]
  refine ⟨W, lawful_pair hxp hxd hne.symm hWC hWD, hWf, hWP, ?_⟩
  -- Correctness of the splice.
  by_cases hck : I.amalgam.toCellScheme.grade r.cap ≤ K + 1
  swap
  · exact isCorrect_of_cap_eq_bot (hat_of_lt (not_le.mp hck))
  have hcapW : W r.cap = f r.cap := hWf _ ⟨hcapC, hck⟩
  by_cases hc0 : W r.cap = ⊥
  · exact isCorrect_of_cap_eq_bot (by rw [hat_of_le hck, hc0])
  -- A requested donor cell below the grade `K + 1` carries the raised fill.
  have hdon {d : Fin I.amalgam.card} (hdC : ¬ I.amalgam.toCellScheme.scope d ⊆ univ.erase xp)
      (hdK : I.amalgam.toCellScheme.grade d < K + 1) : W d = Label.raise h (W₀ d) := by
    have hdD : d ∈ I.amalgam.toCellScheme.below (univ.erase xd, K + 1) :=
      ⟨(I.scope_subset_or hxp hxd hne.symm d).resolve_left hdC, hdK.le⟩
    rw [hWv d hdD fun h' ↦ hdC h'.1]
    exact hvp ⟨d, (I.scope_subset_or hxp hxd hne.symm d).resolve_left hdC,
      show I.amalgam.toCellScheme.grade d ≤ K by omega⟩
  have hhN : IsSelfVisible r.N h := hh.mono (hgr.le_grade_cap.trans hck)
  refine isCorrect_of_forall (fun z hz ↦ ?_) (fun f' hf' ↦ by simp [hF] at hf') fun y hy ↦ ?_
  · -- `Z`: through the correctness of `P`.
    rw [hat_of_le (hZ z hz).2.le, hdon (hZ z hz).1 (hZ z hz).2]
    have h1 := hPc.eq_bot z hz
    rw [hat_of_le (hZ z hz).2.le, hat_of_le hck, min_eq_bot] at h1
    rcases h1 with h1 | h1
    · have h2 := hW₀P z
      rw [h1, min_bot_left, min_eq_bot] at h2
      rw [h2.resolve_right hb.ne', raise_bot hb]
    · exfalso
      have h2 := hWP r.cap
      rw [h1, min_bot_left, min_eq_bot] at h2
      exact hc0 (h2.resolve_right hb.ne')
  · -- `T`: `⊤` above `h`, the marker value of `P` below.
    rw [hat_of_le (hT y hy).2.le, hdon (hT y hy).1 (hT y hy).2]
    by_cases hy0 : h ≤ W₀ y
    · rw [Label.raise, ite_eq_left hy0]; exact le_top
    rw [Label.raise, ite_eq_right hy0]
    have hlt : W₀ y < h := not_le.mp hy0
    have hmv := min_markerValue_eq (r := r) hhN (fun d ↦ min_hat_eq (k := K + 1) hWP d)
    have hP1 : r.markerValue (hat I (K + 1) P) ≤ P y := by
      have := hPc.markerValue_le y hy
      rw [hat_of_le (hT y hy).2.le] at this
      exact this.trans (min_le_left _ _)
    have hPy : min (P y) h = W₀ y := by rw [← hW₀P, min_eq_left hlt.le]
    have h3 : min (r.markerValue (hat I (K + 1) W)) h ≤ W₀ y := by
      rw [hmv, ← hPy]
      exact min_le_min_right _ hP1
    have h4 : min (r.markerValue (hat I (K + 1) W)) h < h := h3.trans_lt hlt
    rwa [min_eq_left (not_le.mp fun h5 ↦ (min_eq_right h5 ▸ h4).false).le] at h3

/-! ### The donor following the root -/

variable (r xp xd) in
/-- **The donor follows the root** at the grade `k`: for every labelling `f` lawful below the
private coatom at `k` with the cap not `⊥`, some witness `ν` bounded by `k`, reflecting `⊥` and
fixing `⊤`, carries the glued labelling to `f` at every cell of the common face of grade at most
`k`. -/
def DonorFollowsRoot (k : ℕ) : Prop :=
  ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) (fun d ↦ f d) → f r.cap ≠ ⊥ →
    ∃ ν : Label.{u} → Label.{u}, IsWitness (stepSuppressor k) ν ∧ (∀ x, ν x = ⊥ → x = ⊥) ∧
      ν ⊤ = ⊤ ∧ ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∩ univ.erase xd →
        I.amalgam.toCellScheme.grade d ≤ k → ν (I.amalgam.label d) = f d

/-- **The fill at `⊥` from the private coatom when the donor follows the root**, at every grade
`0 < k ≤ m + 1`, over a live common face: at a prescription with the cap `⊥` (or above the grade),
the canonical fill; otherwise the private prescription with the glued labelling transported along
the witness on the donor side (lawful by transport,
`CellScheme.Rows.IsLawfulBelow.map_of_apply_eq_bot`; it agrees with the prescription on the common
face).  With the glued labelling `⊤` on `T` and `⊥` on
`Z`, these cells off the private coatom, and `F` empty. -/
theorem capFillBotAt_of_donorFollowsRoot (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hm : 0 < m) (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) (hne : xd ≠ xp) {k : ℕ} (hk : 0 < k)
    (hkm : k ≤ m + 1) (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp)
    (hfol : DonorFollowsRoot r xp xd k)
    (hT : ∀ y ∈ r.T, I.amalgam.label y = ⊤ ∧ ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp)
    (hZ : ∀ z ∈ r.Z, I.amalgam.label z = ⊥ ∧ ¬ I.amalgam.toCellScheme.scope z ⊆ univ.erase xp)
    (hF : r.F = ∅) : CapFillBotAt r xp k := by
  classical
  intro f hf
  by_cases hck : I.amalgam.toCellScheme.grade r.cap ≤ k ∧ f r.cap ≠ ⊥
  swap
  · -- The cap is `⊥` in the splice: the canonical fill.
    obtain ⟨W, hW, hWf, -⟩ := exists_isCutLawful_of_coatom_le hm hk hkm hxp (isSelfVisible_bot k)
      (P := fun _ ↦ ⊥) ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ hf
      fun _ _ ↦ by simp
    refine ⟨W, hW, hWf, isCorrect_of_cap_eq_bot ?_⟩
    by_cases hg : I.amalgam.toCellScheme.grade r.cap ≤ k
    · rw [hat_of_le hg, hWf _ ⟨hcapC, hg⟩]
      exact not_not.mp fun h ↦ hck ⟨hg, h⟩
    · exact hat_of_lt (not_le.mp hg)
  obtain ⟨hg, hc⟩ := hck
  obtain ⟨ν, hν, hνbot, hνtop, hνf⟩ := hfol f hf hc
  set W : Prof I := fun d ↦
    if d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) then f d else ν (I.amalgam.label d)
    with hW
  have hWf (d) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k)) : W d = f d := by
    rw [hW]; simp only [hd, ite_true]
  have hWC : I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) fun d ↦ W d :=
    (Rows.isLawfulBelow_congr (w := f) (w' := W) fun d hd ↦ (hWf d hd).symm).mp hf
  have hνA : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ ν (I.amalgam.label d) :=
    (I.amalgam.isLawful.isLawfulBelow (univ.erase xd, k)).map_of_apply_eq_bot (fun d ↦ d.2.2) hν
      fun _ h ↦ hνbot _ h
  have hWD : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ W d := by
    refine (Rows.isLawfulBelow_congr (w := fun d ↦ ν (I.amalgam.label d)) (w' := W)
      fun d hd ↦ ?_).mp hνA
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k)
    · rw [hWf d hdC]
      exact hνf d (subset_inter hdC.1 hd.1) hdC.2
    · rw [hW]; simp only [hdC, ite_false]
  have hoff {y : Fin I.amalgam.card} (hy : ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp) :
      W y = ν (I.amalgam.label y) := by
    rw [hW]
    exact ite_eq_right fun h ↦ hy h.1
  refine ⟨W, lawful_pair hxp hxd hne.symm hWC hWD, hWf, ?_⟩
  refine isCorrect_of_forall (fun z hz ↦ ?_) (fun f' hf' ↦ by simp [hF] at hf') fun y hy ↦ ?_
  · rw [hat_of_le ((hgr.grade_le_of_mem_Z z hz).trans hg), hoff (hZ z hz).2, (hZ z hz).1,
      hν.map_bot]
  · rw [hat_of_le ((hgr.grade_le_of_mem_T y hy).trans hg), hoff (hT y hy).2, (hT y hy).1, hνtop]
    exact le_top

/-- **The donor cannot follow the root across a tie**: if the glued labelling ties two cells that
a prescription separates, no map carries the one to the other. -/
theorem not_exists_transport_of_tie {f : Prof I} {d₁ d₂ : Fin I.amalgam.card}
    (htie : I.amalgam.label d₁ = I.amalgam.label d₂) (hsep : f d₁ ≠ f d₂) :
    ¬ ∃ ν : Label.{u} → Label.{u}, ν (I.amalgam.label d₁) = f d₁ ∧
      ν (I.amalgam.label d₂) = f d₂ :=
  fun ⟨_, h₁, h₂⟩ ↦ hsep (h₁.symm.trans (htie ▸ h₂))

/-- **The donor cannot follow the root across an inversion**: if the glued labelling orders two
cells one way and a prescription strictly the other way, no monotone map carries the one to the
other. -/
theorem not_exists_transport_of_inversion {f : Prof I} {d₁ d₂ : Fin I.amalgam.card}
    (hlt : I.amalgam.label d₁ ≤ I.amalgam.label d₂) (hinv : f d₂ < f d₁) :
    ¬ ∃ ν : Label.{u} → Label.{u}, Monotone ν ∧ ν (I.amalgam.label d₁) = f d₁ ∧
      ν (I.amalgam.label d₂) = f d₂ :=
  fun ⟨_, hν, h₁, h₂⟩ ↦ (h₁ ▸ h₂ ▸ hν hlt).not_gt hinv

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

/-! ### The (R4) completion reading the tops -/

namespace VaughtConjecture

open Finset Label ProfileTower CapRequests

/-- **The correct completion reading the tops (R4)**: for a seed on `m + 2 ≥ 4` points and cap
requests graded by the grades of the amalgam, with
* the cap of scope the private coatom `univ.erase xp` and grade `N ≥ 3`,
* the common face carrying no cell of grade at least `N` (`hface`),
* `T` labelled `⊤` and `Z` labelled `⊥` in the glued labelling, off the private coatom and of grade
  below `N` (the margin (M3)), and `F` empty,
* the common face dead, or the donor following the root at every grade `N ≤ k ≤ m + 1` together
  with the fill at the positive caps there,

some completion below the full grade has every row of full scope at the grades `≥ N` correct.  The
fills are `CapRequests.capFillBotAt_of_isDeadFace`, `CapRequests.capFillPosAt_of_isDeadFace` and
`CapRequests.capFillBotAt_of_donorFollowsRoot`; the glued labelling is correct (`⊤` on `T`, `⊥` on
`Z`), so its code is (`CapRequests.IsCorrect.code`). -/
theorem Seed.exists_correctCompletion_T {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (hm : 2 ≤ m)
    {r : CapRequests (Fin I.amalgam.card)} (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    {xp xd : Fin (m + 2)} (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) (hne : xd ≠ xp)
    (hcapC : I.amalgam.toCellScheme.scope r.cap = univ.erase xp)
    (hN3 : 3 ≤ I.amalgam.toCellScheme.grade r.cap)
    (hface : ∀ x ∈ (Pts : Finset (Fin (m + 2))), x ≠ xp → ∀ d,
      I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∩ univ.erase x →
      I.amalgam.toCellScheme.grade d < I.amalgam.toCellScheme.grade r.cap)
    (hT : ∀ y ∈ r.T, I.amalgam.label y = ⊤ ∧
      ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp ∧
      I.amalgam.toCellScheme.grade y < I.amalgam.toCellScheme.grade r.cap)
    (hZ : ∀ z ∈ r.Z, I.amalgam.label z = ⊥ ∧
      ¬ I.amalgam.toCellScheme.scope z ⊆ univ.erase xp ∧
      I.amalgam.toCellScheme.grade z < I.amalgam.toCellScheme.grade r.cap)
    (hF : r.F = ∅)
    (hfill : IsDeadFace I xp xd ∨ ∀ k, I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 →
      DonorFollowsRoot r xp xd k ∧ CapFillPosAt r xp k) :
    ∃ F : CompletionBelowFullGrade I,
      F.HasAdmittedRows (I.amalgam.toCellScheme.grade r.cap) r.IsCorrect := by
  have hT' (y) (hy : y ∈ r.T) := (⟨(hT y hy).1, (hT y hy).2.1⟩ :
    I.amalgam.label y = ⊤ ∧ ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp)
  have hZ' (z) (hz : z ∈ r.Z) := (⟨(hZ z hz).1, (hZ z hz).2.1⟩ :
    I.amalgam.label z = ⊥ ∧ ¬ I.amalgam.toCellScheme.scope z ⊆ univ.erase xp)
  -- The glued labelling and its code are correct.
  have hglued : r.IsCorrect fun d ↦ I.amalgam.label d :=
    isCorrect_of_forall (fun z hz ↦ (hZ z hz).1) (fun f hf ↦ by simp [hF] at hf)
      fun y hy ↦ by rw [(hT y hy).1]; exact le_top
  have hlab := (hglued.code hgr (m + 1)).hat hgr (m + 1)
  refine I.exists_correctCompletion hm hgr hxp hcapC hN3 hface (fun k hk hkm ↦ ?_)
    (fun k hk hkm ↦ ?_) hlab
  · rcases hfill with hdead | hfol
    · exact capFillBotAt_of_isDeadFace hgr hxp hxd hne hdead hT' hZ' hF k
    · exact capFillBotAt_of_donorFollowsRoot hgr (by omega) hxp hxd hne (by omega) hkm hcapC.le
        (hfol k hk hkm).1 hT' hZ' hF
  · rcases hfill with hdead | hfol
    · exact capFillPosAt_of_isDeadFace hgr (by omega) hxp hxd hne hdead (by omega) hkm
        (fun y hy ↦ ⟨(hT y hy).2.1, (hT y hy).2.2.trans_le hk⟩)
        (fun z hz ↦ ⟨(hZ z hz).2.1, (hZ z hz).2.2.trans_le hk⟩) hF hcapC.le
    · exact (hfol k hk hkm).2

/-- **The reading of the tops (R4)**: under the hypotheses of `Seed.exists_correctCompletion_T`,
some completion below the full grade reads, in every labelling `q` lawful below `(univ, N)` with
the marker at `λ + i` (`i < N`) at most the cap and the cap at least `λ + R`, every cell of `T`
above every `γ < λ + R` (`CompletionBelowFullGrade.lt_label_of_hasAdmittedRows`). -/
theorem Seed.exists_completion_lt_label_T {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)
    (hm : 2 ≤ m) {r : CapRequests (Fin I.amalgam.card)}
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    {xp xd : Fin (m + 2)} (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) (hne : xd ≠ xp)
    (hcapC : I.amalgam.toCellScheme.scope r.cap = univ.erase xp)
    (hN3 : 3 ≤ I.amalgam.toCellScheme.grade r.cap)
    (hface : ∀ x ∈ (Pts : Finset (Fin (m + 2))), x ≠ xp → ∀ d,
      I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∩ univ.erase x →
      I.amalgam.toCellScheme.grade d < I.amalgam.toCellScheme.grade r.cap)
    (hT : ∀ y ∈ r.T, I.amalgam.label y = ⊤ ∧
      ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp ∧
      I.amalgam.toCellScheme.grade y < I.amalgam.toCellScheme.grade r.cap)
    (hZ : ∀ z ∈ r.Z, I.amalgam.label z = ⊥ ∧
      ¬ I.amalgam.toCellScheme.scope z ⊆ univ.erase xp ∧
      I.amalgam.toCellScheme.grade z < I.amalgam.toCellScheme.grade r.cap)
    (hF : r.F = ∅)
    (hfill : IsDeadFace I xp xd ∨ ∀ k, I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 →
      DonorFollowsRoot r xp xd k ∧ CapFillPosAt r xp k) :
    ∃ F : CompletionBelowFullGrade I, ∀ q : Fin F.scheme.card → Label.{u},
      F.scheme.rows.IsLawfulBelow
        ((univ : Finset (Fin (m + 2))), I.amalgam.toCellScheme.grade r.cap) (fun z ↦ q z) →
      ∀ y ∈ r.T, ∀ (lam : Ordinal.{u}), Order.IsSuccPrelimit lam → ∀ i < r.N,
        q (F.embed r.marker) = ((lam + i : Ordinal.{u}) : Label.{u}) →
        q (F.embed r.marker) ≤ q (F.embed r.cap) →
        ((lam + r.R : Ordinal.{u}) : Label.{u}) ≤ q (F.embed r.cap) →
        ∀ γ : Label.{u}, γ < ((lam + r.R : Ordinal.{u}) : Label.{u}) → γ < q (F.embed y) := by
  obtain ⟨F, hF'⟩ := I.exists_correctCompletion_T hm hgr hxp hxd hne hcapC hN3 hface hT hZ hF hfill
  exact ⟨F, fun q hq y hy lam hlam i hi ha hmc hc γ hγ ↦
    CompletionBelowFullGrade.lt_label_of_hasAdmittedRows hgr hF' hq hy (hT y hy).2.2.le hlam hi ha
      hmc hc hγ⟩

end VaughtConjecture
