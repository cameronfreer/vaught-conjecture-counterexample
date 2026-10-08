/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapSeparationObstruction
import VaughtConjecture.Extension.CanonicalCode

/-!
# The LOW lift provisions at the twisted seed

Roadmap, Layer 3 ((R2) of the table of 3.4); the go/no-go test of bountifulness of the completion at
the arity one with its catalogue at the grade `2` restricted to LOW-admitted entries, at the seed of
the input `SeparationObstruction.T α` with the twisted donor (`TwistedDonor.seedU`, in
`VaughtConjecture.Continuation.SourceGapTwistedEntry`).

The lift of an admitted layer from a coatom into `(univ, k)` holds under two **lift provisions** (at
the cap `⊥` and at the positive caps): every boundary labelling lawful below the coatom, agreeing
with an admitted profile capped at `h`, agrees below the coatom with a profile lawful on the cut,
agreeing with the admitted profile capped at `h` and admitted.  At this seed the profiles are pairs
of labellings of the two faces sharing the root `y`, and the provisions are statements about such
pairs.

* **The lawful labellings of the input** (`SeparationObstruction.eq_lab_of_isLawful`): exactly the
  labellings `(v, ⊥, v, w, s)` with `w ≤ v` and `min v s = min w s` (the converse of
  `SeparationObstruction.isLawful_lab`).
* **The LOW clause at the seed** (`SeparationObstruction.LowVia L R`), in partner form with **the
  owner `o` as the partner**: if `max e' r' < o` then `max o frontier ≤ z'` and `≤ o'`; it reads
  `o'` and `z'` against `o` (`SeparationObstruction.lowVia_iff`).
* **The provision from the donor coatom** (`SeparationObstruction.capProvision_donor`), at every cap
  `h` self-visible at `2`, `⊥` included: an admitted pair `(L, R)` and a lawful donor face `f`
  agreeing with `R` capped at `h` are served by the context face `L` capped at `h` at `o` and `r`
  (with the root of `f`), lawful, agreeing with `L` capped at `h`, and admitted with `f`.  This is
  the lift at which the full-catalogue completion used the twisted entry (context `⊤`, `o'`
  lowered): the admitted replacement lowers `o` and `r` with `o'`.
* **The provision from the context coatom** (`SeparationObstruction.capProvision_context`): a lawful
  context face `f` agreeing with `L` capped at `h` is served by the donor face of `R` when its `o'`
  is below `h` (the admission of `(L, R)` and the strict gap at the donor root force `f o = o`
  there), and otherwise by the donor face with `o'` raised to `max h (f o)`.

**The self seed** (the input with itself; `SeparationObstruction.LowViaSelf`: the designated tops
`z'`, `o'`, `r'`, the designated cell below the top `e'`, the partner the owner): the mixed state
(the context at `⊤`, `o'` and `r'` below `⊤`) is not admitted
(`SeparationObstruction.not_lowViaSelf_mixed`), the actual state is
(`SeparationObstruction.lowViaSelf_T`), and both provisions hold at every cap self-visible at `2`
(`SeparationObstruction.capProvisionSelf_donor`, `SeparationObstruction.capProvisionSelf_context`).

**Status.**  Go at the level of the states: at both seeds no boundary labelling fails a LOW
provision, from either coatom, at any cap.  Not compiled here: the gluing of the two faces into a
profile of the amalgam (lawfulness on the cut), the transfer of the admission to the orbit code of
the profile (`SourceGapRequests.AdmitsLowVia.code` of the admission lane, with every designated
cell, the owner, the lost top and the partner of grade at most `2`), and the admitted layer at the
arity one itself (the admitted-lift theorem of the admission lane is stated for the levels of the
profile tower).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.SeparationObstruction

open Finset Label CellScheme SeparatedInstance

/-! ### The lawful labellings of the input -/

/-- **The lawful labellings of the input are the labellings `(v, ⊥, v, w, s)`** with `w ≤ v` and
`min v s = min w s` (the converse of `SeparationObstruction.isLawful_lab`): `e` is `⊥` (its row is
`⊥` at itself), `z` is `y` (the row of `z` reads both alike, and `y` lies below the only cell of the
graded index of `z`), `o ≤ y` (the row of `o`), and `min y r = min o r` (the row of `r` reads `y`
and `o` alike, and `r` is at most the suppressor at the grade `2`). -/
theorem eq_lab_of_isLawful {P : Fin 5 → Label.{u}} (hP : S.{u}.rows.IsLawful P) :
    P = lab (P 0) (P 3) (P 4) ∧ P 3 ≤ P 0 ∧ min (P 0) (P 4) = min (P 3) (P 4) := by
  have hmem (c d : Fin 5) (h : cells.gradedIndex d ≤ cells.gradedIndex c) :
      d ∈ cells.below (cells.gradedIndex c) := h
  -- `e` is `⊥`
  have h1 : P 1 = ⊥ := hP.eq_bot_of_row_self_eq_bot 1 rfl
  -- `z` is `y`
  have hzy : P 2 ≤ P 0 := by
    have := (hP.locality 2).le_of_le (d := ⟨2, hmem 2 2 le_rfl⟩) (d' := ⟨0, hmem 2 0 (by decide)⟩)
      le_rfl le_rfl
    simpa using this
  have hyz : P 0 ≤ P 2 := by
    obtain ⟨u, hu, hle⟩ := hP.availability 0 2 (by decide) rfl
    have key : ∀ u : Fin 5, cells.gradedIndex u = cells.gradedIndex 2 → u = 2 := by decide
    rwa [key u hu] at hle
  -- `o ≤ y`
  have hoy : P 3 ≤ P 0 := by
    have := (hP.locality 3).le_of_le (d := ⟨3, hmem 3 3 le_rfl⟩) (d' := ⟨0, hmem 3 0 (by decide)⟩)
      le_rfl (show cells.grade 0 ≤ cells.grade 3 by decide)
    simp only [min_self] at this
    exact this.trans (min_le_left _ _)
  -- `min y r = min o r`
  have hyr : min (P 0) (P 4) = min (P 3) (P 4) := by
    obtain ⟨g, σ, hw, he⟩ := hP.locality 4
    have e0 := he ⟨0, hmem 4 0 (by decide)⟩
    have e3 := he ⟨3, hmem 4 3 (by decide)⟩
    have e4 := he ⟨4, hmem 4 4 le_rfl⟩
    simp only [min_self] at e0 e3 e4
    change min (P 0) (P 4) = min (σ low) (g 1) at e0
    change min (P 3) (P 4) = min (σ low) (g 2) at e3
    change P 4 = min (σ omegaAddTwo) (g 2) at e4
    refine le_antisymm ?_ (min_le_min_right _ hoy)
    rw [e3]
    refine le_min ?_ ?_
    · rw [e0]; exact min_le_left _ _
    · exact (min_le_right _ _).trans (by rw [e4]; exact min_le_right _ _)
  refine ⟨funext fun d ↦ ?_, hoy, hyr⟩
  fin_cases d
  · rfl
  · exact h1
  · exact le_antisymm hzy hyz
  · rfl
  · rfl

/-! ### The LOW clause at the twisted seed, read on the two faces -/

/-- **The LOW clause at the seed in partner form**, read on the two faces: `L` the labelling of the
context face, `R` that of the donor face (both labellings of the scheme of the input, sharing the
root cell `y`).  The owner is the cell `o` (`3`) of `L`, the lost top the cell `r` (`4`) of `L`,
`K = 2`; the designated donor cells below the top are `e'` (`1`) and `r'` (`4`) of `R`, the
designated tops `z'` (`2`) and `o'` (`3`) of `R`; **the partner is the owner** (the field is the
value at `o`).  This is `SourceGapRequests.AdmitsLowVia` of the admission lane at these data. -/
def LowVia (L R : Fin 5 → Label.{u}) : Prop :=
  max (R 1) (R 4) < L 3 →
    max (L 3) (min (L 3) (visibilityReplace 2 2 (L 4))) ≤ R 2 ∧
    max (L 3) (min (L 3) (visibilityReplace 2 2 (L 4))) ≤ R 3

/-- The LOW clause with the partner at the owner reads `o'` and `z'` against `o`. -/
theorem lowVia_iff {L R : Fin 5 → Label.{u}} :
    LowVia L R ↔ (max (R 1) (R 4) < L 3 → L 3 ≤ R 2 ∧ L 3 ≤ R 3) := by
  rw [LowVia, max_eq_left (min_le_left _ _)]

/-- Agreement capped at `h` above `h` stays above `h`. -/
theorem le_of_min_eq_of_le {x y h : Label.{u}} (e : min x h = min y h) (hy : h ≤ y) : h ≤ x := by
  rw [min_eq_right hy] at e
  exact min_eq_right_iff.mp e

/-! ### The lift provision from the donor coatom -/

/-- **The LOW lift provision from the donor coatom**, at every cap `h` self-visible at `2` (`⊥`
included): let `(L, R)` be an admitted state (lawful faces sharing `y`), and `f` a lawful labelling
of the donor face agreeing with `R` capped at `h`.  Then the context face `W` obtained from `L` by
capping `o` and `r` at `h`, with the root `y` of `f`, is lawful, agrees with `L` capped at `h`, and
`(W, f)` is admitted.  So the twisted entry is not needed: the lift from the donor coatom is served
by an admitted state. -/
theorem capProvision_donor {h : Label.{u}} (hh : IsSelfVisible 2 h) {L R f : Fin 5 → Label.{u}}
    (hL : S.{u}.rows.IsLawful L) (hR : S.{u}.rows.IsLawful R) (hy : L 0 = R 0)
    (hadm : LowVia L R) (hf : S.{u}.rows.IsLawful f) (hfR : ∀ d, min (f d) h = min (R d) h) :
    ∃ W : Fin 5 → Label.{u}, S.{u}.rows.IsLawful W ∧ W 0 = f 0 ∧
      (∀ d, min (W d) h = min (L d) h) ∧ LowVia W f := by
  obtain ⟨hLe, hwa, has⟩ := eq_lab_of_isLawful hL
  obtain ⟨hRe, hw'a, has'⟩ := eq_lab_of_isLawful hR
  obtain ⟨hfe, -, -⟩ := eq_lab_of_isLawful hf
  set a := L 0
  set w := L 3
  set s := L 4
  rw [← hy] at hw'a has'
  have ha : min (f 0) h = min a h := (hfR 0).trans (by rw [hy])
  have hw3 : min (f 3) h = min (R 3) h := hfR 3
  have hs4 : min (f 4) h = min (R 4) h := hfR 4
  have hvw : IsSelfVisible 2 w := hL.orderly 3
  have hvs : IsSelfVisible 2 s := hL.orderly 4
  -- the context face, capped at `h` at `o` and `r`
  have h1 : min w h ≤ f 0 := by
    rcases lt_or_ge w h with hwh | hwh
    · rcases lt_or_ge a h with hah | hah
      · rw [Label.eq_of_min_eq_of_lt ha.symm hah, min_eq_left hwh.le]; exact hwa
      · exact (min_le_right _ _).trans (le_of_min_eq_of_le ha hah)
    · exact (min_le_right _ _).trans (le_of_min_eq_of_le ha (hwh.trans hwa))
  have h2 : min (f 0) (min s h) = min (min w h) (min s h) := by
    rcases lt_or_ge w h with hwh | hwh
    · rw [min_eq_left hwh.le]
      rcases lt_or_ge a h with hah | hah
      · rw [Label.eq_of_min_eq_of_lt ha.symm hah, ← min_assoc, has, min_assoc]
      · have hfa : h ≤ f 0 := le_of_min_eq_of_le ha hah
        have hsw : s ≤ w := by
          by_contra hsw
          have hws : w < s := not_le.mp hsw
          have hlt : w < min a s := lt_min (hwh.trans_le hah) hws
          rw [has, min_eq_left hws.le] at hlt
          exact lt_irrefl _ hlt
        rw [min_eq_right ((min_le_right _ _).trans hfa), min_eq_right ((min_le_left _ _).trans hsw)]
    · have hfa : h ≤ f 0 := le_of_min_eq_of_le ha (hwh.trans hwa)
      rw [min_eq_right hwh, min_eq_right ((min_le_right _ _).trans hfa),
        min_eq_right (min_le_right _ _)]
  have hL1 : L 1 = ⊥ := by rw [hLe]; rfl
  have hL2 : L 2 = a := by rw [hLe]; rfl
  have hR1 : R 1 = ⊥ := by rw [hRe]; rfl
  have hf1 : f 1 = ⊥ := by rw [hfe]; rfl
  have hf2 : f 2 = f 0 := by rw [hfe]; rfl
  refine ⟨lab (f 0) (min w h) (min s h),
    isLawful_lab (hf.orderly 0) (hvw.min hh) (hvs.min hh) h1 h2, rfl, fun d ↦ ?_, ?_⟩
  · fin_cases d
    · exact ha
    · change min ⊥ h = min (L 1) h; rw [hL1]
    · change min (f 0) h = min (L 2) h; rw [hL2]; exact ha
    · change min (min w h) h = min w h; rw [min_assoc, min_self]
    · change min (min s h) h = min s h; rw [min_assoc, min_self]
  · rw [lowVia_iff]
    intro hlt
    change max (f 1) (f 4) < min w h at hlt
    rw [hf1, max_eq_right bot_le] at hlt
    refine ⟨by rw [hf2]; exact h1, ?_⟩
    have hf4h : f 4 < h := hlt.trans_le (min_le_right _ _)
    have hR4 : R 4 = f 4 := Label.eq_of_min_eq_of_lt hs4 hf4h
    have hwR : w ≤ R 3 := ((lowVia_iff.mp hadm) (by
      rw [hR1, max_eq_right bot_le, hR4]; exact hlt.trans_le (min_le_left _ _))).2
    change min w h ≤ f 3
    rcases lt_or_ge (f 3) h with h3 | h3
    · rw [← Label.eq_of_min_eq_of_lt hw3 h3]; exact (min_le_left _ _).trans hwR
    · exact (min_le_right _ _).trans h3

/-! ### The lift provision from the context coatom -/

/-- **The LOW lift provision from the context coatom**, at every cap `h` self-visible at `2` (`⊥`
included): let `(L, R)` be an admitted state, and `f` a lawful labelling of the context face
agreeing with `L` capped at `h`.  Then some lawful donor face `W` with the root of `f` agrees with
`R` capped at `h`, and `(f, W)` is admitted: below `h` the donor face of `R` is kept (admission of
`(L, R)` and the strict gap force it), at or above `h` the donor's `o'` is raised to
`max h (f o)`. -/
theorem capProvision_context {h : Label.{u}} (hh : IsSelfVisible 2 h) {L R f : Fin 5 → Label.{u}}
    (hL : S.{u}.rows.IsLawful L) (hR : S.{u}.rows.IsLawful R) (hy : L 0 = R 0)
    (hadm : LowVia L R) (hf : S.{u}.rows.IsLawful f) (hfL : ∀ d, min (f d) h = min (L d) h) :
    ∃ W : Fin 5 → Label.{u}, S.{u}.rows.IsLawful W ∧ W 0 = f 0 ∧
      (∀ d, min (W d) h = min (R d) h) ∧ LowVia f W := by
  obtain ⟨hLe, hwa, -⟩ := eq_lab_of_isLawful hL
  obtain ⟨hRe, hw'a, has'⟩ := eq_lab_of_isLawful hR
  obtain ⟨hfe, hfwa, -⟩ := eq_lab_of_isLawful hf
  set a := L 0
  set w := L 3
  rw [← hy] at hw'a has'
  have ha : min (f 0) h = min a h := hfL 0
  have hR1 : R 1 = ⊥ := by rw [hRe]; rfl
  have hR2 : R 2 = a := by rw [hRe, ← hy]; rfl
  have hf1 : f 1 = ⊥ := by rw [hfe]; rfl
  have hf2 : f 2 = f 0 := by rw [hfe]; rfl
  have hadm' := lowVia_iff.mp hadm
  rw [hR1, max_eq_right bot_le] at hadm'
  -- the strict gap on the donor face: above `h` at the root, `r'` is at most `o'`
  have hs'w' (hah : h ≤ a) (hw'h : R 3 < h) : R 4 ≤ R 3 := by
    by_contra hsw
    have hws : R 3 < R 4 := not_le.mp hsw
    have hlt : R 3 < min a (R 4) := lt_min (hw'h.trans_le hah) hws
    rw [has', min_eq_left hws.le] at hlt
    exact lt_irrefl _ hlt
  rcases lt_or_ge (R 3) h with hw'h | hw'h
  · -- below `h`: keep the donor face of `R`
    have hwh : w < h := by
      by_contra hwh
      have hhw : h ≤ w := not_lt.mp hwh
      have hs := hs'w' (hhw.trans hwa) hw'h
      exact absurd ((hadm' (hs.trans_lt (hw'h.trans_le hhw))).2.trans_lt hw'h) (not_lt.mpr hhw)
    have hf3 : f 3 = w := Label.eq_of_min_eq_of_lt (hfL 3).symm hwh
    have h1 : R 3 ≤ f 0 := by
      rcases lt_or_ge a h with hah | hah
      · rw [Label.eq_of_min_eq_of_lt ha.symm hah]; exact hw'a
      · exact hw'h.le.trans (le_of_min_eq_of_le ha hah)
    have h2 : min (f 0) (R 4) = min (R 3) (R 4) := by
      rcases lt_or_ge a h with hah | hah
      · rw [Label.eq_of_min_eq_of_lt ha.symm hah]; exact has'
      · have hs := hs'w' hah hw'h
        have hfa : h ≤ f 0 := le_of_min_eq_of_le ha hah
        rw [min_eq_right (hs.trans (hw'h.le.trans hfa)), min_eq_right hs]
    refine ⟨lab (f 0) (R 3) (R 4), isLawful_lab (hf.orderly 0) (hR.orderly 3) (hR.orderly 4) h1 h2,
      rfl, fun d ↦ ?_, ?_⟩
    · fin_cases d
      · exact ha.trans (by rw [hy]; rfl)
      · change min ⊥ h = min (R 1) h; rw [hR1]
      · change min (f 0) h = min (R 2) h; rw [hR2]; exact ha
      · rfl
      · rfl
    · rw [lowVia_iff]
      intro hlt
      change max ⊥ (R 4) < f 3 at hlt
      rw [max_eq_right bot_le, hf3] at hlt
      exact ⟨hfwa, by rw [hf3]; exact (hadm' hlt).2⟩
  · -- at or above `h`: raise `o'` to `max h (f o)`
    have hfa : h ≤ f 0 := le_of_min_eq_of_le ha (hw'h.trans hw'a)
    set M := max h (f 3)
    have hM : IsSelfVisible 2 M := hh.max (hf.orderly 3)
    have h1 : M ≤ f 0 := max_le hfa hfwa
    have h2 : min (f 0) (min (R 4) M) = min M (min (R 4) M) := by
      rw [min_eq_right ((min_le_right _ _).trans h1), min_eq_right (min_le_right _ _)]
    refine ⟨lab (f 0) M (min (R 4) M), isLawful_lab (hf.orderly 0) hM ((hR.orderly 4).min hM) h1 h2,
      rfl, fun d ↦ ?_, ?_⟩
    · fin_cases d
      · exact ha.trans (by rw [hy]; rfl)
      · change min ⊥ h = min (R 1) h; rw [hR1]
      · change min (f 0) h = min (R 2) h; rw [hR2]; exact ha
      · change min M h = min (R 3) h
        rw [min_eq_right (le_max_left _ _), min_eq_right hw'h]
      · change min (min (R 4) M) h = min (R 4) h
        rw [min_assoc, min_eq_right (le_max_left _ _)]
    · rw [lowVia_iff]
      intro _
      exact ⟨hfwa, le_max_right _ _⟩

/-! ### The self seed: the donor is the context -/

/-- **The LOW clause at the self seed** (the input with itself) in partner form, the partner the
owner: as `SeparationObstruction.LowVia`, with the designated donor cell below the top `e'` only and
the designated tops `z'`, `o'`, `r'` (all `⊤` in the donor `T`). -/
def LowViaSelf (L R : Fin 5 → Label.{u}) : Prop :=
  R 1 < L 3 →
    max (L 3) (min (L 3) (visibilityReplace 2 2 (L 4))) ≤ R 2 ∧
    max (L 3) (min (L 3) (visibilityReplace 2 2 (L 4))) ≤ R 3 ∧
    max (L 3) (min (L 3) (visibilityReplace 2 2 (L 4))) ≤ R 4

theorem lowViaSelf_iff {L R : Fin 5 → Label.{u}} :
    LowViaSelf L R ↔ (R 1 < L 3 → L 3 ≤ R 2 ∧ L 3 ≤ R 3 ∧ L 3 ≤ R 4) := by
  rw [LowViaSelf, max_eq_left (min_le_left _ _)]

/-- **The mixed state is excluded at the self seed**: the context at `⊤` with the donor's `o'`,
`r'` at a label `c < ⊤` is not admitted. -/
theorem not_lowViaSelf_mixed {c : Label.{u}} (hc : c < ⊤) :
    ¬ LowViaSelf (lab ⊤ ⊤ ⊤) (lab ⊤ c c) := fun h ↦ by
  rw [lowViaSelf_iff] at h
  have := (h (by change (⊥ : Label.{u}) < ⊤; exact bot_lt_top)).2.1
  exact hc.not_ge this

/-- The actual state of the self seed is admitted. -/
theorem lowViaSelf_T : LowViaSelf (lab ⊤ ⊤ ⊤ : Fin 5 → Label.{u}) (lab ⊤ ⊤ ⊤) := by
  rw [lowViaSelf_iff]
  exact fun _ ↦ ⟨le_rfl, le_rfl, le_rfl⟩

/-- **The provision from the donor coatom at the self seed**, at every cap self-visible at `2`: as
`SeparationObstruction.capProvision_donor`, the context capped at `h` at `o` and `r`. -/
theorem capProvisionSelf_donor {h : Label.{u}} (hh : IsSelfVisible 2 h)
    {L R f : Fin 5 → Label.{u}} (hL : S.{u}.rows.IsLawful L) (hR : S.{u}.rows.IsLawful R)
    (hy : L 0 = R 0) (hadm : LowViaSelf L R) (hf : S.{u}.rows.IsLawful f)
    (hfR : ∀ d, min (f d) h = min (R d) h) :
    ∃ W : Fin 5 → Label.{u}, S.{u}.rows.IsLawful W ∧ W 0 = f 0 ∧
      (∀ d, min (W d) h = min (L d) h) ∧ LowViaSelf W f := by
  obtain ⟨hLe, hwa, has⟩ := eq_lab_of_isLawful hL
  obtain ⟨hRe, -, -⟩ := eq_lab_of_isLawful hR
  obtain ⟨hfe, -, -⟩ := eq_lab_of_isLawful hf
  set a := L 0
  set w := L 3
  set s := L 4
  have ha : min (f 0) h = min a h := (hfR 0).trans (by rw [hy])
  have hvw : IsSelfVisible 2 w := hL.orderly 3
  have hvs : IsSelfVisible 2 s := hL.orderly 4
  have hR1 : R 1 = ⊥ := by rw [hRe]; rfl
  have hadm' := lowViaSelf_iff.mp hadm
  rw [hR1] at hadm'
  have h1 : min w h ≤ f 0 := by
    rcases lt_or_ge w h with hwh | hwh
    · rcases lt_or_ge a h with hah | hah
      · rw [Label.eq_of_min_eq_of_lt ha.symm hah, min_eq_left hwh.le]; exact hwa
      · exact (min_le_right _ _).trans (le_of_min_eq_of_le ha hah)
    · exact (min_le_right _ _).trans (le_of_min_eq_of_le ha (hwh.trans hwa))
  have h2 : min (f 0) (min s h) = min (min w h) (min s h) := by
    rcases lt_or_ge w h with hwh | hwh
    · rw [min_eq_left hwh.le]
      rcases lt_or_ge a h with hah | hah
      · rw [Label.eq_of_min_eq_of_lt ha.symm hah, ← min_assoc, has, min_assoc]
      · have hfa : h ≤ f 0 := le_of_min_eq_of_le ha hah
        have hsw : s ≤ w := by
          by_contra hsw
          have hws : w < s := not_le.mp hsw
          have hlt : w < min a s := lt_min (hwh.trans_le hah) hws
          rw [has, min_eq_left hws.le] at hlt
          exact lt_irrefl _ hlt
        rw [min_eq_right ((min_le_right _ _).trans hfa), min_eq_right ((min_le_left _ _).trans hsw)]
    · have hfa : h ≤ f 0 := le_of_min_eq_of_le ha (hwh.trans hwa)
      rw [min_eq_right hwh, min_eq_right ((min_le_right _ _).trans hfa),
        min_eq_right (min_le_right _ _)]
  have hL1 : L 1 = ⊥ := by rw [hLe]; rfl
  have hL2 : L 2 = a := by rw [hLe]; rfl
  have hf2 : f 2 = f 0 := by rw [hfe]; rfl
  -- a donor cell of `f` below `h` is the donor cell of `R`, read at least as `o`
  have hdon (x : Fin 5) (hx : x = 3 ∨ x = 4) (hw0 : ⊥ < w) : min w h ≤ f x := by
    rcases lt_or_ge (f x) h with hxh | hxh
    · rw [← Label.eq_of_min_eq_of_lt (hfR x) hxh]
      refine (min_le_left _ _).trans ?_
      rcases hx with rfl | rfl
      exacts [(hadm' hw0).2.1, (hadm' hw0).2.2]
    · exact (min_le_right _ _).trans hxh
  refine ⟨lab (f 0) (min w h) (min s h),
    isLawful_lab (hf.orderly 0) (hvw.min hh) (hvs.min hh) h1 h2, rfl, fun d ↦ ?_, ?_⟩
  · fin_cases d
    · exact ha
    · change min ⊥ h = min (L 1) h; rw [hL1]
    · change min (f 0) h = min (L 2) h; rw [hL2]; exact ha
    · change min (min w h) h = min w h; rw [min_assoc, min_self]
    · change min (min s h) h = min s h; rw [min_assoc, min_self]
  · rw [lowViaSelf_iff]
    intro hlt
    have hw0 : ⊥ < w := (bot_le.trans_lt hlt).trans_le (min_le_left _ _)
    exact ⟨by rw [hf2]; exact h1, hdon 3 (.inl rfl) hw0, hdon 4 (.inr rfl) hw0⟩

/-- **The provision from the context coatom at the self seed**, at every cap self-visible at `2`:
the donor cells `o'`, `r'` of `R` are kept below `h`, and raised to `max h (f o)` at or above it. -/
theorem capProvisionSelf_context {h : Label.{u}} (hh : IsSelfVisible 2 h)
    {L R f : Fin 5 → Label.{u}} (hL : S.{u}.rows.IsLawful L) (hR : S.{u}.rows.IsLawful R)
    (hy : L 0 = R 0) (hadm : LowViaSelf L R) (hf : S.{u}.rows.IsLawful f)
    (hfL : ∀ d, min (f d) h = min (L d) h) :
    ∃ W : Fin 5 → Label.{u}, S.{u}.rows.IsLawful W ∧ W 0 = f 0 ∧
      (∀ d, min (W d) h = min (R d) h) ∧ LowViaSelf f W := by
  obtain ⟨-, hwa, -⟩ := eq_lab_of_isLawful hL
  obtain ⟨hRe, hw'a, has'⟩ := eq_lab_of_isLawful hR
  obtain ⟨hfe, hfwa, -⟩ := eq_lab_of_isLawful hf
  set a := L 0
  set w := L 3
  rw [← hy] at hw'a has'
  have ha : min (f 0) h = min a h := hfL 0
  have hR1 : R 1 = ⊥ := by rw [hRe]; rfl
  have hR2 : R 2 = a := by rw [hRe, ← hy]; rfl
  have hf1 : f 1 = ⊥ := by rw [hfe]; rfl
  have hadm' := lowViaSelf_iff.mp hadm
  rw [hR1] at hadm'
  -- a donor cell of `R` below `h` puts `o` below `h`, and then `f o = o` reads below it
  have hwlt (x : Fin 5) (hx : x = 3 ∨ x = 4) (hxh : R x < h) : w < h := by
    by_contra hwh
    have hhw : h ≤ w := not_lt.mp hwh
    have hw0 : ⊥ < w := (bot_le.trans_lt hxh).trans_le hhw
    have hle : w ≤ R x := by
      rcases hx with rfl | rfl
      exacts [(hadm' hw0).2.1, (hadm' hw0).2.2]
    exact absurd (hle.trans_lt hxh) (not_lt.mpr hhw)
  have hf3le (hwh : w < h) (x : Fin 5) (hx : x = 3 ∨ x = 4) : f 3 ≤ R x := by
    rw [Label.eq_of_min_eq_of_lt (hfL 3).symm hwh]
    change w ≤ R x
    rcases eq_bot_or_bot_lt w with hw0 | hw0
    · rw [hw0]; exact bot_le
    · rcases hx with rfl | rfl
      exacts [(hadm' hw0).2.1, (hadm' hw0).2.2]
  have hs'w' (hah : h ≤ a) (hw'h : R 3 < h) : R 4 ≤ R 3 := by
    by_contra hsw
    have hws : R 3 < R 4 := not_le.mp hsw
    have hlt : R 3 < min a (R 4) := lt_min (hw'h.trans_le hah) hws
    rw [has', min_eq_left hws.le] at hlt
    exact lt_irrefl _ hlt
  have hagr (W3 W4 : Label.{u}) (h3 : min W3 h = min (R 3) h) (h4 : min W4 h = min (R 4) h) (d) :
      min (lab (f 0) W3 W4 d) h = min (R d) h := by
    fin_cases d
    · exact ha.trans (by rw [hy]; rfl)
    · change min ⊥ h = min (R 1) h; rw [hR1]
    · change min (f 0) h = min (R 2) h; rw [hR2]; exact ha
    · exact h3
    · exact h4
  rcases lt_or_ge (R 3) h with hw'h | hw'h
  · -- `o'` below `h`: keep the donor face of `R`
    have hwh := hwlt 3 (.inl rfl) hw'h
    have h1 : R 3 ≤ f 0 := by
      rcases lt_or_ge a h with hah | hah
      · rw [Label.eq_of_min_eq_of_lt ha.symm hah]; exact hw'a
      · exact hw'h.le.trans (le_of_min_eq_of_le ha hah)
    have h2 : min (f 0) (R 4) = min (R 3) (R 4) := by
      rcases lt_or_ge a h with hah | hah
      · rw [Label.eq_of_min_eq_of_lt ha.symm hah]; exact has'
      · have hs := hs'w' hah hw'h
        have hfa : h ≤ f 0 := le_of_min_eq_of_le ha hah
        rw [min_eq_right (hs.trans (hw'h.le.trans hfa)), min_eq_right hs]
    refine ⟨lab (f 0) (R 3) (R 4), isLawful_lab (hf.orderly 0) (hR.orderly 3) (hR.orderly 4) h1 h2,
      rfl, hagr _ _ rfl rfl, ?_⟩
    rw [lowViaSelf_iff]
    intro _
    exact ⟨hfwa, hf3le hwh 3 (.inl rfl), hf3le hwh 4 (.inr rfl)⟩
  · have hfa : h ≤ f 0 := le_of_min_eq_of_le ha (hw'h.trans hw'a)
    set M := max h (f 3)
    have hM : IsSelfVisible 2 M := hh.max (hf.orderly 3)
    have h1 : M ≤ f 0 := max_le hfa hfwa
    rcases lt_or_ge (R 4) h with hs'h | hs'h
    · -- `o'` at or above `h`, `r'` below: raise `o'`, keep `r'`
      have hwh := hwlt 4 (.inr rfl) hs'h
      have h2 : min (f 0) (R 4) = min M (R 4) := by
        rw [min_eq_right (hs'h.le.trans hfa), min_eq_right (hs'h.le.trans (le_max_left _ _))]
      refine ⟨lab (f 0) M (R 4), isLawful_lab (hf.orderly 0) hM (hR.orderly 4) h1 h2, rfl,
        hagr _ _ (by rw [min_eq_right (le_max_left _ _), min_eq_right hw'h]) rfl, ?_⟩
      rw [lowViaSelf_iff]
      intro _
      exact ⟨hfwa, le_max_right _ _, hf3le hwh 4 (.inr rfl)⟩
    · -- both at or above `h`: raise both
      refine ⟨lab (f 0) M M, isLawful_lab (hf.orderly 0) hM hM h1
        (by rw [min_eq_right h1, min_self]),
        rfl, hagr _ _ (by rw [min_eq_right (le_max_left _ _), min_eq_right hw'h])
          (by rw [min_eq_right (le_max_left _ _), min_eq_right hs'h]), ?_⟩
      rw [lowViaSelf_iff]
      intro _
      exact ⟨hfwa, le_max_right _ _, le_max_right _ _⟩

end VaughtConjecture.SeparationObstruction
