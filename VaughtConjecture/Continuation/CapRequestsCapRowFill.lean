/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapRequestsGrade
import VaughtConjecture.Extension.SuppressedTransport

/-!
# The private fills at the grade of the cap, through the row of the cap

Roadmap, Layer 3 ((R4) of the table of 3.4); the fills from the private coatom
(`CapRequests.CapFillBotAt`, `CapRequests.CapFillPosAt`) for cap requests whose cap has scope the
private coatom `Cp = univ.erase xp` and grade `N`.

At the grade `N` every cell below the private coatom lies below the cap, so the locality of a
labelling `f` lawful below the private coatom at the cap gives a witness `(g, σ)` with
`min (f d) (f cap) = min (σ (row_cap d)) (g (grade d))` at every such cell, and `f cap` is
self-visible at `N`.  Compiled in this repository (theorem named):

* **An extension of the row of the cap** (`CapRequests.CapRowExtension`): a profile `P₀` equal to
  the row of the cap below the cap, correct for the requests, whose transformations by every
  witness with suppressor not `⊥` at `N` are lawful below the donor coatom at `N` (a lawful
  companion of the same bottoms suffices, `CellScheme.Rows.IsLawfulBelow.transform_of_bot_iff`).
* **The fill at `⊥` at the grade of the cap** (`CapRequests.capFillBotAt_of_capRowExtension`): the
  transformation of `P₀` by the witness of the locality of `f` at the cap is lawful on the cut and
  correct (`CapRequests.IsCorrect.map`) and agrees with `f` capped at `f cap` below the private
  coatom; the fill of the other coatom at the cap `f cap`
  (`ProfileTower.exists_isCutLawful_of_coatom_le`) gives a profile equal to `f` below the private
  coatom whose splice is correct, since correctness reads only the state capped at the cap
  (`CapRequests.IsCorrect.of_min_eq`).
* **The fill at `⊥` at every grade `k` from the cap** (`CapRequests.CapRowExtensionAt`,
  `CapRequests.CapFillBotUncoveredAt`, `CapRequests.capFillBotAt_of_capRowExtensionAt`): with a
  cell `E` of graded index `(Cp, k)` at least the cap in `f`, the same argument runs at `E` (every
  cell below the private coatom lies below `E`, and `f E` is self-visible at `k`); the prescriptions
  with every such cell strictly below the cap (for instance the top grade killed) are the
  **uncovered** case, a named hypothesis.
* **The fill at the positive caps outside the band** (`CapRequests.CapFillPosBandAt`,
  `CapRequests.capFillPosAt_of_band`): at a positive cap `h` with `f cap ≤ h` the fill of the other
  coatom along the prescribed profile `P` is correct (the state capped at `f cap` is `P` capped at
  `f cap`); so the fill at the positive caps reduces, at every grade from the cap, to the **band**
  `h < f cap`, a named hypothesis.

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

variable (r xd) in
/-- **An extension of the row of the cap**: a profile equal to the row of the cap below the cap,
correct for the requests, whose transformation by every witness `(g, σ)` with `g N ≠ ⊥` (`N` the
grade of the cap) is lawful below the donor coatom `univ.erase xd` at the grade `N`. -/
def CapRowExtension : Prop :=
  ∃ P₀ : Prof I,
    (∀ d (hd : d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex r.cap)),
      P₀ d = I.amalgam.rows.row r.cap ⟨d, hd⟩) ∧
    r.IsCorrect P₀ ∧
    ∀ (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}), IsWitness g σ →
      g (I.amalgam.toCellScheme.grade r.cap) ≠ ⊥ →
      I.amalgam.rows.IsLawfulBelow (univ.erase xd, I.amalgam.toCellScheme.grade r.cap)
        fun d ↦ min (σ (P₀ d)) (g (I.amalgam.toCellScheme.grade d))

/-- **The fill at `⊥` from the private coatom at the grade of the cap, from an extension of the row
of the cap.** -/
theorem capFillBotAt_of_capRowExtension (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hm : 0 < m) (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) (hne : xd ≠ xp)
    (hcapC : I.amalgam.toCellScheme.scope r.cap = univ.erase xp)
    (hext : CapRowExtension r xd) :
    CapFillBotAt r xp (I.amalgam.toCellScheme.grade r.cap) := by
  classical
  intro f hf
  set N := I.amalgam.toCellScheme.grade r.cap with hNdef
  have hN0 : 0 < N := I.amalgam.isWellFormed.isWellFormed.grade_pos r.cap
  have hNm : N ≤ m + 1 := by have := I.grade_lt r.cap; omega
  have hX : I.amalgam.toCellScheme.gradedIndex r.cap = (univ.erase xp, N) := Prod.ext hcapC rfl
  have hcb : r.cap ∈ I.amalgam.toCellScheme.below (univ.erase xp, N) := by
    rw [CellScheme.mem_below, ← hX]
  by_cases hc0 : f r.cap = ⊥
  · obtain ⟨W, hW, hWf, -⟩ := exists_isCutLawful_of_coatom_le hm hN0 hNm hxp
      (isSelfVisible_bot _) (P := fun _ ↦ ⊥)
      ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ hf fun _ _ ↦ by simp
    refine ⟨W, hW, hWf, isCorrect_of_cap_eq_bot ?_⟩
    rw [hat_of_le le_rfl, hWf _ hcb, hc0]
  obtain ⟨hord, hloc, -⟩ := Rows.isLawfulBelow_iff_forall.mp hf
  obtain ⟨g, σ, hw, heq⟩ := hloc r.cap hcb
  have hgN : g N ≠ ⊥ := by
    have h : min (f r.cap) (f r.cap) = min (σ (I.amalgam.rows.row r.cap
        ⟨r.cap, CellScheme.mem_below_gradedIndex _ _⟩)) (g N) :=
      heq ⟨r.cap, CellScheme.mem_below_gradedIndex _ _⟩
    rw [min_self] at h
    exact ne_bot_of_le_ne_bot hc0 (h.le.trans (min_le_right _ _))
  set c := f r.cap with hcdef
  have hcsv : IsSelfVisible N c := hord r.cap hcb
  obtain ⟨P₀, hP₀row, hP₀c, hP₀D⟩ := hext
  set W' : Prof I := fun d ↦ min (σ (P₀ d)) (g (I.amalgam.toCellScheme.grade d)) with hW'def
  have hW'C (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, N)) :
      W' d = min (f d) c := by
    have hd' : d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex r.cap) := by
      rw [hX]; exact hd
    rw [hW'def]
    dsimp only
    rw [hP₀row d hd']
    exact (heq ⟨d, hd'⟩).symm
  have hfc : I.amalgam.rows.IsLawfulBelow (univ.erase xp, N) fun d ↦ min (f d) c :=
    Rows.isLawfulBelow_iff.mpr ((Rows.isLawfulBelow_iff.mp hf).min_const_of_isSelfVisible
      (K := N) (fun d ↦ d.2.2) hcsv)
  have hW'Cl : I.amalgam.rows.IsLawfulBelow (univ.erase xp, N) fun d ↦ W' d :=
    (Rows.isLawfulBelow_congr (w := fun d ↦ min (f d) c) (w' := W')
      fun d hd ↦ (hW'C d hd).symm).mp hfc
  have hW'cut : IsCutLawful I N W' := lawful_pair hxp hxd hne.symm hW'Cl (hP₀D g σ hw hgN)
  have hW'corr : r.IsCorrect W' := hP₀c.map hgr hw
  obtain ⟨W, hW, hWf, hWW'⟩ := exists_isCutLawful_of_coatom_le hm hN0 hNm hxp hcsv hW'cut hf
    fun d hd ↦ by rw [hW'C d hd, min_assoc, min_self]
  refine ⟨W, hW, hWf, ?_⟩
  have hs : r.IsCorrect (hat I N fun d ↦ min (W' d) c) :=
    (hW'corr.cap hgr.off_le (hcsv.mono hgr.le_grade_cap)).hat hgr N
  have hscap : hat I N (fun d ↦ min (W' d) c) r.cap = c := by
    rw [hat_of_le le_rfl]
    show min (W' r.cap) c = c
    rw [hW'C _ hcb, min_self, min_self]
  have hWcap : hat I N W r.cap = c := by rw [hat_of_le le_rfl, hWf _ hcb]
  refine hs.of_min_eq (hWcap.trans hscap.symm) (by rw [hscap]; exact hcsv.mono hgr.le_grade_cap)
    (fun x ↦ ?_) hgr.off_le
  rw [hWcap, hscap]
  by_cases hx : I.amalgam.toCellScheme.grade x ≤ N
  · rw [hat_of_le hx, hat_of_le hx, hWW' x]
    simp only [min_assoc, min_self]
  · rw [hat_of_lt (not_le.mp hx), hat_of_lt (not_le.mp hx)]

/-! ### The fill at `⊥` at every grade from the cap -/

variable (r xd) in
/-- **An extension of the row of a cell `E` at the grade `k`**: a profile equal to the row of `E`
below `E`, correct for the requests, whose transformation by every witness `(g, σ)` with
`g k ≠ ⊥` is lawful below the donor coatom `univ.erase xd` at `k`. -/
def CapRowExtensionAt (k : ℕ) (E : Fin I.amalgam.card) : Prop :=
  ∃ P₀ : Prof I,
    (∀ d (hd : d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex E)),
      P₀ d = I.amalgam.rows.row E ⟨d, hd⟩) ∧
    r.IsCorrect P₀ ∧
    ∀ (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}), IsWitness g σ → g k ≠ ⊥ →
      I.amalgam.rows.IsLawfulBelow (univ.erase xd, k)
        fun d ↦ min (σ (P₀ d)) (g (I.amalgam.toCellScheme.grade d))

variable (r xp) in
/-- **The uncovered fill at `⊥`** at the grade `k`: the statement of `CapRequests.CapFillBotAt` for
the prescriptions whose cap is not `⊥` and lies strictly above the prescription at every cell of
graded index `(univ.erase xp, k)`. -/
def CapFillBotUncoveredAt (k : ℕ) : Prop :=
  ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) (fun d ↦ f d) →
    f r.cap ≠ ⊥ →
    (∀ E, I.amalgam.toCellScheme.gradedIndex E = (univ.erase xp, k) → f E < f r.cap) →
    ∃ W : Prof I, IsCutLawful I k W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k), W d = f d) ∧
      r.IsCorrect (hat I k W)

/-- **The fill at `⊥` from the private coatom at every grade from the cap**, from extensions of the
rows of the cells of graded index `(univ.erase xp, k)` and the uncovered fill.  A prescription `f`
with a cell `E` of that graded index at least its cap is transported along the locality of `f` at
`E` (every cell below the private coatom lies below `E`, and `f E` is self-visible at `k`); the
fill of the other coatom at `f E` is correct since `f cap ≤ f E`. -/
theorem capFillBotAt_of_capRowExtensionAt (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hm : 0 < m) (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) (hne : xd ≠ xp)
    (hcapC : I.amalgam.toCellScheme.scope r.cap = univ.erase xp) {k : ℕ}
    (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k) (hkm : k ≤ m + 1)
    (hext : ∀ E, I.amalgam.toCellScheme.gradedIndex E = (univ.erase xp, k) →
      CapRowExtensionAt r xd k E)
    (hunc : CapFillBotUncoveredAt r xp k) : CapFillBotAt r xp k := by
  classical
  intro f hf
  have hk0 : 0 < k := (I.amalgam.isWellFormed.isWellFormed.grade_pos r.cap).trans_le hNk
  have hcb : r.cap ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) := ⟨hcapC.le, hNk⟩
  by_cases hc0 : f r.cap = ⊥
  · obtain ⟨W, hW, hWf, -⟩ := exists_isCutLawful_of_coatom_le hm hk0 hkm hxp
      (isSelfVisible_bot _) (P := fun _ ↦ ⊥)
      ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ hf fun _ _ ↦ by simp
    refine ⟨W, hW, hWf, isCorrect_of_cap_eq_bot ?_⟩
    rw [hat_of_le hNk, hWf _ hcb, hc0]
  by_cases hcov : ∃ E, I.amalgam.toCellScheme.gradedIndex E = (univ.erase xp, k) ∧
      f r.cap ≤ f E
  swap
  · simp only [not_exists, not_and, not_le] at hcov
    exact hunc f hf hc0 hcov
  obtain ⟨E, hE, hcE⟩ := hcov
  have hEb : E ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) := by
    rw [CellScheme.mem_below, hE]
  obtain ⟨hord, hloc, -⟩ := Rows.isLawfulBelow_iff_forall.mp hf
  obtain ⟨g, σ, hw, heq⟩ := hloc E hEb
  have hE0 : f E ≠ ⊥ := ne_bot_of_le_ne_bot hc0 hcE
  have hgk : g k ≠ ⊥ := by
    have h : min (f E) (f E) = min (σ (I.amalgam.rows.row E
        ⟨E, CellScheme.mem_below_gradedIndex _ _⟩)) (g (I.amalgam.toCellScheme.grade E)) :=
      heq ⟨E, CellScheme.mem_below_gradedIndex _ _⟩
    rw [min_self, show I.amalgam.toCellScheme.grade E = k from congrArg Prod.snd hE] at h
    exact ne_bot_of_le_ne_bot hE0 (h.le.trans (min_le_right _ _))
  set hE' := f E with hE'def
  set c := f r.cap with hcdef
  have hEsv : IsSelfVisible k hE' := by
    have := hord E hEb
    rwa [show I.amalgam.toCellScheme.grade E = k from congrArg Prod.snd hE] at this
  have hcsv : IsSelfVisible (I.amalgam.toCellScheme.grade r.cap) c := hord r.cap hcb
  obtain ⟨P₀, hP₀row, hP₀c, hP₀D⟩ := hext E hE
  set W' : Prof I := fun d ↦ min (σ (P₀ d)) (g (I.amalgam.toCellScheme.grade d)) with hW'def
  have hW'C (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k)) :
      W' d = min (f d) hE' := by
    have hd' : d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex E) := by
      rw [hE]; exact hd
    rw [hW'def]
    dsimp only
    rw [hP₀row d hd']
    exact (heq ⟨d, hd'⟩).symm
  have hfE : I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) fun d ↦ min (f d) hE' :=
    Rows.isLawfulBelow_iff.mpr ((Rows.isLawfulBelow_iff.mp hf).min_const_of_isSelfVisible
      (K := k) (fun d ↦ d.2.2) hEsv)
  have hW'Cl : I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) fun d ↦ W' d :=
    (Rows.isLawfulBelow_congr (w := fun d ↦ min (f d) hE') (w' := W')
      fun d hd ↦ (hW'C d hd).symm).mp hfE
  have hW'cut : IsCutLawful I k W' := lawful_pair hxp hxd hne.symm hW'Cl (hP₀D g σ hw hgk)
  have hW'corr : r.IsCorrect W' := hP₀c.map hgr hw
  obtain ⟨W, hW, hWf, hWW'⟩ := exists_isCutLawful_of_coatom_le hm hk0 hkm hxp hEsv hW'cut hf
    fun d hd ↦ by rw [hW'C d hd, min_assoc, min_self]
  refine ⟨W, hW, hWf, ?_⟩
  have hNN : r.N ≤ I.amalgam.toCellScheme.grade r.cap := hgr.le_grade_cap
  have hs : r.IsCorrect (hat I k fun d ↦ min (W' d) c) :=
    (hW'corr.cap hgr.off_le (hcsv.mono hNN)).hat hgr k
  have hscap : hat I k (fun d ↦ min (W' d) c) r.cap = c := by
    rw [hat_of_le hNk]
    show min (W' r.cap) c = c
    rw [hW'C _ hcb, min_eq_left hcE]
    exact min_self _
  have hWcap : hat I k W r.cap = c := by rw [hat_of_le hNk, hWf _ hcb]
  refine hs.of_min_eq (hWcap.trans hscap.symm) (by rw [hscap]; exact hcsv.mono hNN)
    (fun x ↦ ?_) hgr.off_le
  rw [hWcap, hscap]
  have e (y : Label.{u}) : min y c = min (min y hE') c := by rw [min_assoc, min_eq_right hcE]
  by_cases hx : I.amalgam.toCellScheme.grade x ≤ k
  · rw [hat_of_le hx, hat_of_le hx, e (W x), hWW' x, ← e]
    simp only [min_assoc, min_self]
  · rw [hat_of_lt (not_le.mp hx), hat_of_lt (not_le.mp hx)]

variable (r xp) in
/-- **The band of the fill at the positive caps** at the grade `k`: the statement of
`CapRequests.CapFillPosAt` for the prescriptions `f` whose cap lies strictly above the cap `h` of
the lift. -/
def CapFillPosBandAt (k : ℕ) : Prop :=
  ∀ h : Label.{u}, IsSelfVisible k h → IsShort k h → ⊥ < h → ∀ P : Prof I,
    IsCutLawful I k P → r.IsCorrect (hat I k P) →
    ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) (fun d ↦ f d) →
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k), min (f d) h = min (P d) h) →
      h < f r.cap →
      ∃ W : Prof I, IsCutLawful I k W ∧
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k), W d = f d) ∧
        (∀ d, min (W d) h = min (P d) h) ∧ r.IsCorrect (hat I k W)

/-- **The fill at the positive caps from the band**: at every grade `k` from the cap, a prescription
whose cap is at most the cap `h` of the lift is filled along the prescribed profile, so the fill
at the positive caps holds as soon as it holds in the band. -/
theorem capFillPosAt_of_band (hgr : r.IsGraded I.amalgam.toCellScheme.grade) (hm : 0 < m)
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hcapC : I.amalgam.toCellScheme.scope r.cap = univ.erase xp) {k : ℕ}
    (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k) (hkm : k ≤ m + 1)
    (hband : CapFillPosBandAt r xp k) : CapFillPosAt r xp k := by
  intro h hh hsh hb P hP hPc f hf hfP
  by_cases hfc : h < f r.cap
  · exact hband h hh hsh hb P hP hPc f hf hfP hfc
  have hk0 : 0 < k := (I.amalgam.isWellFormed.isWellFormed.grade_pos r.cap).trans_le hNk
  have hcb : r.cap ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) := ⟨hcapC.le, hNk⟩
  obtain ⟨W, hW, hWf, hWP⟩ := exists_isCutLawful_of_coatom_le hm hk0 hkm hxp hh hP hf hfP
  refine ⟨W, hW, hWf, hWP, ?_⟩
  set c := f r.cap
  have hch : c ≤ h := not_lt.mp hfc
  have hcsv : IsSelfVisible (I.amalgam.toCellScheme.grade r.cap) c :=
    (Rows.isLawfulBelow_iff_forall.mp hf).1 r.cap hcb
  have hNN : r.N ≤ I.amalgam.toCellScheme.grade r.cap := hgr.le_grade_cap
  -- the cap of `P` is at least `c`
  have hPc' : c ≤ P r.cap := by
    have h1 := hfP r.cap hcb
    rw [min_eq_left hch] at h1
    rw [h1]
    exact min_le_left _ _
  have hs : r.IsCorrect fun d ↦ min (hat I k P d) c := hPc.cap hgr.off_le (hcsv.mono hNN)
  have hscap : min (hat I k P r.cap) c = c := by rw [hat_of_le hNk, min_eq_right hPc']
  have hWcap : hat I k W r.cap = c := by rw [hat_of_le hNk, hWf _ hcb]
  refine hs.of_min_eq (hWcap.trans hscap.symm) (by rw [hscap]; exact hcsv.mono hNN)
    (fun x ↦ ?_) hgr.off_le
  rw [hWcap, hscap]
  have e (y : Label.{u}) : min y c = min (min y h) c := by rw [min_assoc, min_eq_right hch]
  by_cases hx : I.amalgam.toCellScheme.grade x ≤ k
  · rw [hat_of_le hx, hat_of_le hx, e (W x), hWP x, ← e, min_assoc, min_self]
  · rw [hat_of_lt (not_le.mp hx), hat_of_lt (not_le.mp hx)]
    simp

end CapRequests

end VaughtConjecture
