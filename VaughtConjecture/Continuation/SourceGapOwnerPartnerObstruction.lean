/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapLowProvision
import VaughtConjecture.Continuation.SourceGapTwistedEntry

/-!
# The owner as the partner of the LOW clause fails at a legal source-gap context

Roadmap, Layer 3 ((R2) of the table of 3.4); the arity-one LOW-admitted completion of
`VaughtConjecture.Continuation.SourceGapAdmittedSeed` and the lift provisions of
`VaughtConjecture.Continuation.SourceGapLowProvision`.

At the input `SeparationObstruction.T α` the LOW clause with the owner `o` as the partner
(`SeparationObstruction.LowVia`: if `max e' r' < o` then `o ≤ z'` and `o ≤ o'`) has both lift
provisions at every cap.  The provision from the context coatom uses that the row of the owner
reads the root `y` and the owner `o` alike, so `o ≤ y` in every lawful labelling of the context:
then the donor's tops, which the root bounds from below, can be raised to `o`.

**The input** (`OwnerPartner.t2`).  The scheme of `T` with one entry changed: the owner `o` reads
itself at `ω·2 + 2` (above its reading `ω + 2` of `y`, `z`).

| cell     | scope    | grade | row                                                    | label |
|----------|----------|-------|--------------------------------------------------------|-------|
| 0 (`y`)  | `{0}`    | 1     | `y ↦ 2`                                                | `⊤`   |
| 1 (`e`)  | `{1}`    | 1     | `⊥`                                                    | `⊥`   |
| 2 (`z`)  | `univ`   | 1     | `y ↦ 2`, `z ↦ 2`                                       | `⊤`   |
| 3 (`o`)  | `univ`   | 2     | `y ↦ ω + 2`, `z ↦ ω + 2`, `o ↦ ω·2 + 2`, `r ↦ 2`       | `⊤`   |
| 4 (`r`)  | `univ`   | 2     | `y ↦ 2`, `z ↦ 2`, `o ↦ 2`, `r ↦ ω + 2`                 | `⊤`   |

It is legal (`OwnerPartner.isLegal_t2`), a source-gap context of grade `2` along the root `{0}`
with owner `o` and lost top `r` (`OwnerPartner.isSourceGapContextAt_t2`; the gaps are
`2 < ω·2 + 2` at the owner and `2 < ω + 2` at `y`), and its face on the root is that of `T`
(`OwnerPartner.restrictFace_t2`), so the twisted donor `TwistedDonor.Utop`, labelled
`(⊤, ⊥, ⊤, ⊤, v)`, is a legal donor over the same root.

**The violation** (`OwnerPartner.not_capProvision_context`).  For `v < h < ⊤`, `h` self-visible
at `2`: the state (the labels of `t2`, the labels of the donor) is admitted, and `(h, ⊥, h, ⊤, h)`
is lawful on the context and agrees with its labels capped at `h`; but no lawful donor face with
root `h` agreeing with the donor capped at `h` is admitted with it: such a face has `o' ≤ y' = h`
and `r' = v`, so its designated cells below the top are below `⊤ = o` and the clause asks
`⊤ ≤ o'`.  So the provision from the context coatom of the owner-as-partner clause is false at a
legal two-point source-gap context with a legal donor: the hypothesis `o ≤ y` (on every lawful
labelling of the context) cannot be dropped from the owner-as-partner design.

**The frontier alone serves** (`OwnerPartner.exists_frontier_context`, feasibility at this input
only): the donor face `(h, ⊥, h, h, v)` is lawful, has root `h`, agrees with the donor capped at
`h`, and its designated tops are at least the frontier `min o (visibilityReplace 2 2 r) = h`.  The
universal arity-one design therefore needs the plan's LOW clause with the frontier and a separate
cutoff field, not the owner's value as the field.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

namespace Scheme

/-- **Restrictions of schemes with the same cells** agree when the rows agree at the visible
cells. -/
theorem comap_mk_eq {k n m : ℕ} {D : CellScheme (Fin k) (Fin n)} {R R' : D.Rows.{u}}
    (f : Fin m ↪ Fin n)
    (h : ∀ s (t : D.below (D.gradedIndex s)),
      s ∈ (⟨k, D, R⟩ : Scheme.{u} n).visibleCells f → R.row s t = R'.row s t) :
    (⟨k, D, R⟩ : Scheme.{u} n).comap f = (⟨k, D, R'⟩ : Scheme.{u} n).comap f := by
  refine Scheme.ext rfl rfl rfl (fun i j hij ↦ ?_) (fun i j hij ↦ ?_) fun s s' t t' hs ht ↦ ?_
  · obtain rfl := Fin.ext hij
    rfl
  · obtain rfl := Fin.ext hij
    rfl
  · obtain rfl := Fin.ext hs
    obtain rfl : t = t' := Subtype.ext (Fin.ext ht)
    exact h _ _ (Scheme.cellMap_mem _ _ s)

/-- Schemes with the same cells have the same cell maps. -/
theorem cellMap_mk_eq {k n m : ℕ} {D : CellScheme (Fin k) (Fin n)} {R R' : D.Rows.{u}}
    (f : Fin m ↪ Fin n) (i : Fin ((⟨k, D, R⟩ : Scheme.{u} n).comap f).card) :
    (⟨k, D, R⟩ : Scheme.{u} n).cellMap f i = (⟨k, D, R'⟩ : Scheme.{u} n).cellMap f i :=
  rfl

end Scheme

namespace OwnerPartner

open Finset Label CellScheme StageType SeparationObstruction
open SeparatedInstance (omegaAddTwo)
open scoped Ordinal

/-! ### A three-valued shifter -/

theorem isSuccPrelimit_omega0_mul_two : Order.IsSuccPrelimit ((ω : Ordinal.{u}) * 2) :=
  Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _)

/-- The label `ω·2 + 2`, the high row value. -/
noncomputable abbrev high : Label.{u} :=
  ((ω * 2 + ((2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})

theorem omegaAddTwo_lt_omega0_mul_two :
    omegaAddTwo.{u} < (((ω : Ordinal.{u}) * 2 : Ordinal.{u}) : Label.{u}) := by
  refine WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ?_)
  rw [Ordinal.mul_two]
  exact (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 2)

theorem not_high_lt : ¬ high.{u} < (((ω : Ordinal.{u}) * 2 : Ordinal.{u}) : Label.{u}) :=
  fun h ↦ (not_lt.mpr le_self_add) (WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h))

theorem coe_omega0_le_omegaAddTwo : ((ω : Ordinal.{u}) : Label.{u}) ≤ omegaAddTwo.{u} :=
  not_lt.mp not_omegaAddTwo_lt'

theorem omegaAddTwo_lt_high : omegaAddTwo.{u} < high.{u} :=
  omegaAddTwo_lt_omega0_mul_two.trans_le (not_lt.mp not_high_lt)

theorem isSelfVisible_high : IsSelfVisible 2 high.{u} :=
  isSelfVisible_coe_add isSuccPrelimit_omega0_mul_two le_rfl

/-- The shifter sending `⊥` to `⊥`, every other label below `ω` to `a`, every label in `[ω, ω·2)`
to `b`, and every label at least `ω·2` to `c`. -/
noncomputable def threeLevel (a b c x : Label.{u}) : Label.{u} :=
  if x < ((ω : Ordinal.{u}) : Label.{u}) then (if x = ⊥ then ⊥ else a)
  else if x < (((ω : Ordinal.{u}) * 2 : Ordinal.{u}) : Label.{u}) then b else c

/-- **The three-valued shifter is a witness** with the step suppressor at `K`, for `a ≤ b ≤ c`
self-visible at `K`. -/
theorem isWitness_threeLevel_step (K : ℕ) {a b c : Label.{u}} (ha : IsSelfVisible K a)
    (hb : IsSelfVisible K b) (hc : IsSelfVisible K c) (hab : a ≤ b) (hbc : b ≤ c) :
    IsWitness (stepSuppressor K) (threeLevel a b c) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := by simp [threeLevel, WithBot.bot_lt_coe]
  monotone := by
    intro x y hxy
    simp only [threeLevel]
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;>
      first
      | exact bot_le
      | exact le_rfl
      | exact hab
      | exact hbc
      | exact hab.trans hbc
      | exact absurd (hxy.trans_lt ‹_›) ‹_›
      | (subst_vars; exact absurd (le_bot_iff.mp hxy) ‹_›)
  visibilityReplace_comm x k hx i hi := by
    have hinv : threeLevel a b c (visibilityReplace k i x) = threeLevel a b c x := by
      simp only [threeLevel,
        Label.visibilityReplace_lt_iff Ordinal.isSuccLimit_omega0.isSuccPrelimit,
        Label.visibilityReplace_lt_iff isSuccPrelimit_omega0_mul_two,
        visibilityReplace_eq_bot_iff]
    rw [hinv]
    have hsv : IsSelfVisible K (threeLevel a b c x) := by
      simp only [threeLevel]
      split_ifs
      exacts [isSelfVisible_bot _, ha, hb, hc]
    by_cases hk : k ≤ K
    · exact ((hsv.mono hk).visibilityReplace_eq i).symm
    · rw [stepSuppressor_of_lt (by omega), le_bot_iff] at hx
      rw [hx, visibilityReplace_bot]

/-- Rows of grade at most `K` with values `⊥`, `2`, `ω + 2`, `ω·2 + 2` transform to sections with
values `⊥`, `a`, `b`, `c` at the same cells. -/
theorem transformsTo_threeLevel_step {E : Type*} {grade : E → ℕ} {K : ℕ}
    (hg : ∀ d, grade d ≤ K) {r t : E → Label.{u}} {a b c : Label.{u}} (ha : IsSelfVisible K a)
    (hb : IsSelfVisible K b) (hc : IsSelfVisible K c) (hab : a ≤ b) (hbc : b ≤ c)
    (h : ∀ d, (r d = ⊥ ∧ t d = ⊥) ∨ (r d = low ∧ t d = a) ∨ (r d = omegaAddTwo ∧ t d = b) ∨
      (r d = high ∧ t d = c)) :
    TransformsTo grade r t :=
  ⟨_, _, isWitness_threeLevel_step K ha hb hc hab hbc, fun d ↦ by
    rw [stepSuppressor_of_le (hg d), min_top_right]
    rcases h d with ⟨hr, ht⟩ | ⟨hr, ht⟩ | ⟨hr, ht⟩ | ⟨hr, ht⟩ <;> rw [hr, ht, threeLevel]
    · simp [WithBot.bot_lt_coe]
    · rw [ite_eq_left low_lt_coe_omega0, ite_eq_right (by simp [low])]
    · rw [ite_eq_right not_omegaAddTwo_lt', ite_eq_left omegaAddTwo_lt_omega0_mul_two]
    · rw [ite_eq_right (fun h ↦ not_omegaAddTwo_lt'
        (omegaAddTwo_lt_high.trans h)), ite_eq_right not_high_lt]⟩

/-! ### The input -/

/-- The rows: those of `SeparationObstruction.S`, except that `o` reads itself at `ω·2 + 2`. -/
noncomputable def rowValue2 : Fin 5 → Fin 5 → Label.{u} :=
  ![![low, ⊥, low, ⊥, ⊥], fun _ ↦ ⊥, ![low, ⊥, low, ⊥, ⊥],
    ![omegaAddTwo, ⊥, omegaAddTwo, high, low], ![low, ⊥, low, low, omegaAddTwo]]

/-- The scheme on two points, with the cells of `SeparationObstruction.S`. -/
noncomputable abbrev S2 : Scheme.{u} 2 := ⟨5, cells, ⟨fun s d ↦ rowValue2 s d.1⟩⟩

/-- **Lawful sections**: `(v, ⊥, v, w, s)` is lawful when `v` is self-visible at `1`, `w`, `s` and
`min v w` at `2`, `min s w ≤ min v w`, and `min v s = min w s`. -/
theorem isLawful_lab2 {v w s : Label.{u}} (hv : IsSelfVisible 1 v) (hw : IsSelfVisible 2 w)
    (hs : IsSelfVisible 2 s) (hvw : IsSelfVisible 2 (min v w)) (hsw : min s w ≤ min v w)
    (hvs : min v s = min w s) :
    S2.{u}.rows.IsLawful (lab v w s) where
  orderly d := by
    fin_cases d
    exacts [hv, isSelfVisible_bot _, hv, hw, hs]
  locality c := by
    have hg : ∀ (c : Fin 5) (d : cells.below (cells.gradedIndex c)),
        cells.grade d ≤ cells.grade c :=
      fun c d ↦ d.2.2
    fin_cases c
    · -- `y`: the row reads `y` at `2`; the section is `v` there
      refine transformsTo_twoLevel_step (K := 1) (fun d ↦ hg 0 d) hv hv le_rfl fun ⟨d, hd⟩ ↦ ?_
      have hd' : cells.gradedIndex d ≤ cells.gradedIndex 0 := hd
      fin_cases d <;> first | exact absurd hd' (by decide) | simp [lab, rowValue2]
    · convert TransformsTo.bot _ _ using 1
      funext d
      -- the transformed section at the dead cell `e`
      change min _ (lab v w s 1) = ⊥
      simp [lab]
    · -- `z`: the row reads `y`, `z` at `2`; the section is `v` there
      refine transformsTo_twoLevel_step (K := 1) (fun d ↦ hg 2 d) hv hv le_rfl fun ⟨d, hd⟩ ↦ ?_
      have hd' : cells.gradedIndex d ≤ cells.gradedIndex 2 := hd
      fin_cases d <;> first | exact absurd hd' (by decide) | simp [lab, rowValue2]
    · -- `o`: the section capped at `w` is `min v w` at `y`, `z`, `w` at `o`, `min s w` at `r`
      refine transformsTo_threeLevel_step (K := 2) (fun d ↦ hg 3 d) (hs.min hw) hvw hw hsw
        (min_le_right _ _) fun ⟨d, hd⟩ ↦ ?_
      fin_cases d <;> simp [lab, rowValue2]
    · -- `r`: the section capped at `s` is `min w s` at `y`, `z`, `o` and `s` at `r`
      refine transformsTo_twoLevel_step (K := 2) (fun d ↦ hg 4 d) (hw.min hs) hs
        (min_le_right _ _) fun ⟨d, hd⟩ ↦ ?_
      fin_cases d <;> simp [lab, rowValue2, hvs]
  availability c t hct hg := by
    have key : ∀ c t : Fin 5, cells.scope c ⊆ cells.scope t → cells.grade c = cells.grade t →
        cells.gradedIndex c = cells.gradedIndex t ∨ (t = 2 ∧ (c = 0 ∨ c = 1)) := by decide
    rcases key c t hct hg with h | ⟨rfl, rfl | rfl⟩
    · exact ⟨c, h, le_rfl⟩
    · exact ⟨2, rfl, le_rfl⟩
    · exact ⟨2, rfl, bot_le⟩

/-- A lawful section gives lawful labellings below every pair. -/
private theorem isLawfulBelow_of_isLawful {w : Fin 5 → Label.{u}} (h : S2.{u}.rows.IsLawful w)
    (X : Finset (Fin 2) × ℕ) : S2.{u}.rows.IsLawfulBelow X (fun d ↦ w d) :=
  CellScheme.Rows.isLawfulBelow_iff_forall.mpr
    ⟨fun d _ ↦ h.orderly d, fun s _ ↦ h.locality s, fun s t _ hst hg ↦ h.availability s t hst hg⟩

/-- A section below `X`, extended by `⊥`, is lawful below `X`. -/
private theorem isLawfulBelow_extendBot {X : Finset (Fin 2) × ℕ} {q : cells.below X → Label.{u}}
    (hq : S2.{u}.rows.IsLawfulBelow X q) :
    S2.{u}.rows.IsLawfulBelow X (fun d ↦ CellScheme.Rows.extendBot X q d) := by
  convert hq using 1
  funext d
  exact CellScheme.Rows.extendBot_of_mem q d.2

/-- **Lawful sections below `(univ, 1)`**, necessary conditions: `e` is `⊥` and `z` equals `y`. -/
private theorem conditions_univ_one {w : Fin 5 → Label.{u}}
    (hq : S2.{u}.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 1) (fun d ↦ w d)) :
    w 1 = ⊥ ∧ w 0 = w 2 := by
  obtain ⟨-, hl, ha⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hq
  have m : ∀ i : Fin 5, i = 0 ∨ i = 1 ∨ i = 2 → cells.gradedIndex i ≤ ((univ : Finset (Fin 2)), 1)
    := by decide
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · have := (hl 1 (m 1 (by decide))).eq_bot (d := ⟨1, CellScheme.mem_below_gradedIndex _ 1⟩) rfl
    simpa using this
  · obtain ⟨u, hu, hle⟩ := ha 0 2 (m 2 (by decide)) (by decide) rfl
    have : ∀ u : Fin 5, cells.gradedIndex u = cells.gradedIndex 2 → u = 2 := by decide
    rwa [this u hu] at hle
  · have := (hl 2 (m 2 (by decide))).le_of_le (d := ⟨2, CellScheme.mem_below_gradedIndex _ 2⟩)
      (d' := ⟨0, show cells.gradedIndex 0 ≤ cells.gradedIndex 2 by decide⟩) le_rfl le_rfl
    simpa using this

/-- **The capped lift from `({0}, 1)` to `(univ, 1)`**: the prescription `v` at `y` lifts to
`(v, ⊥, v, ⊥, ⊥)`. -/
private theorem cappedLift_zero
    (h : (({0} : Finset (Fin 2)), 1) ≤ ((univ : Finset (Fin 2)), 1)) :
    S2.{u}.rows.CappedLift h := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨hq1, hq02⟩ := conditions_univ_one (isLawfulBelow_extendBot hq)
  set wq := CellScheme.Rows.extendBot ((univ : Finset (Fin 2)), 1) q
  have hqw : ∀ d, q d = wq d := fun d ↦ (CellScheme.Rows.extendBot_of_mem q d.2).symm
  have m0 : cells.gradedIndex 0 ≤ (({0} : Finset (Fin 2)), 1) := by decide
  set v := p ⟨0, m0⟩
  have hv : IsSelfVisible 1 v := hp.orderly ⟨0, m0⟩
  have hc0 : min (wq 0) c = min v c := by
    have := hpq ⟨0, m0⟩; rwa [hqw] at this
  refine ⟨fun d ↦ lab v ⊥ ⊥ d, isLawfulBelow_of_isLawful
    (isLawful_lab2 hv (isSelfVisible_bot _) (isSelfVisible_bot _) (by simp)
      (by simp) (by simp)) _,
    fun ⟨d, hd⟩ ↦ ?_, fun ⟨d, hd⟩ ↦ ?_⟩
  · rw [hqw]
    have hd' : cells.gradedIndex d ≤ ((univ : Finset (Fin 2)), 1) := hd
    fin_cases d
    · exact hc0.symm
    · -- the lift at `e` is `⊥`
      change min ⊥ c = min (wq 1) c
      rw [hq1]
    · -- the lift at `z` is the prescription at `y`
      change min v c = min (wq 2) c
      rw [← hq02, hc0]
    · exact absurd hd' (by decide)
    · exact absurd hd' (by decide)
  · have hd' : cells.gradedIndex d ≤ (({0} : Finset (Fin 2)), 1) := hd
    have key : ∀ d : Fin 5, cells.gradedIndex d ≤ (({0} : Finset (Fin 2)), 1) → d = 0 := by
      decide
    obtain rfl := key d hd'
    rfl

/-- **The capped lift from `({1}, 1)` to `(univ, 1)`**: the cell `e` is `⊥` in every lawful
labelling, so the ambient labelling is a lift. -/
private theorem cappedLift_one
    (h : (({1} : Finset (Fin 2)), 1) ≤ ((univ : Finset (Fin 2)), 1)) :
    S2.{u}.rows.CappedLift h := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦
    ⟨q, hq, fun _ ↦ rfl, fun ⟨d, hd⟩ ↦ ?_⟩
  have hd' : cells.gradedIndex d ≤ (({1} : Finset (Fin 2)), 1) := hd
  have key : ∀ d : Fin 5, cells.gradedIndex d ≤ (({1} : Finset (Fin 2)), 1) → d = 1 := by
    decide
  obtain rfl := key d hd'
  have hq1 := (conditions_univ_one (isLawfulBelow_extendBot hq)).1
  rw [CellScheme.Rows.extendBot_of_mem q
    (show cells.gradedIndex 1 ≤ ((univ : Finset (Fin 2)), 1) by decide)] at hq1
  have hp1 : p ⟨1, hd⟩ = ⊥ := by
    have := (hp.locality ⟨1, hd⟩).eq_bot (d := ⟨⟨1, hd⟩,
      le_refl ((S2.{u}.toCellScheme.reindex Subtype.val).gradedIndex ⟨1, hd⟩)⟩) rfl
    simpa using this
  rw [hp1]
  exact hq1

/-- **The scheme is legal.** -/
theorem isLegal_S2 : S2.{u}.IsLegal where
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ by
    have key : ∀ d : Fin 5, cells.scope d ∈ cells.faces ∧ 0 < cells.grade d ∧
        cells.grade d ≤ #(cells.scope d) := by decide
    exact key d⟩⟩
  isCoded s t := by
    have key : ∀ s d : Fin 5, rowValue2.{u} s d = ⊥ ∨ rowValue2.{u} s d = low ∨
        rowValue2.{u} s d = omegaAddTwo ∨ rowValue2.{u} s d = high := by
      intro s d
      fin_cases s <;> fin_cases d <;> simp [rowValue2]
    -- the rows of `S2` are `rowValue2`
    change rowValue2 s t.1 < _
    rcases key s t.1 with h | h | h | h <;> rw [h]
    · exact WithBot.bot_lt_coe _
    · exact natCast_label_lt_omega0_sq 2
    · exact lt_omega0_sq_iff.mpr (.inr ⟨1, 2, by simp [omegaAddTwo]⟩)
    · exact lt_omega0_sq_iff.mpr (.inr ⟨2, 2, by simp [high]⟩)
  isConsistent c := by
    have key : ∀ c : Fin 5, c = 1 ∨ ∃ v w s' : Label.{u},
        (∀ d, rowValue2 c d = lab v w s' d) ∧ S2.{u}.rows.IsLawful (lab v w s') := by
      have hl0 := isLawful_lab2 (v := low.{u}) (w := ⊥) (s := ⊥)
        (isSelfVisible_low.mono (by omega)) (isSelfVisible_bot _) (isSelfVisible_bot _)
        (by simp) (by simp) (by simp)
      intro c
      fin_cases c
      · exact .inr ⟨low, ⊥, ⊥, fun d ↦ by fin_cases d <;> rfl, hl0⟩
      · exact .inl rfl
      · exact .inr ⟨low, ⊥, ⊥, fun d ↦ by fin_cases d <;> rfl, hl0⟩
      · refine .inr ⟨omegaAddTwo, high, low, fun d ↦ by fin_cases d <;> rfl,
          isLawful_lab2 (isSelfVisible_omegaAddTwo_two.mono (by omega)) isSelfVisible_high
            isSelfVisible_low ?_ ?_ ?_⟩
        · rw [min_eq_left omegaAddTwo_lt_high.le]
          exact isSelfVisible_omegaAddTwo_two
        · rw [min_eq_left (low_lt_omegaAddTwo.trans omegaAddTwo_lt_high).le,
            min_eq_left omegaAddTwo_lt_high.le]
          exact low_lt_omegaAddTwo.le
        · rw [min_eq_right low_lt_omegaAddTwo.le,
            min_eq_right (low_lt_omegaAddTwo.trans omegaAddTwo_lt_high).le]
      · exact .inr ⟨low, low, omegaAddTwo, fun d ↦ by fin_cases d <;> rfl,
          isLawful_lab2 (isSelfVisible_low.mono (by omega)) isSelfVisible_low
            isSelfVisible_omegaAddTwo_two (by rw [min_self]; exact isSelfVisible_low)
            (by rw [min_self]; exact min_le_right _ _) rfl⟩
    -- consistency at `c` is lawfulness of its row below its graded index
    change S2.{u}.rows.IsLawfulBelow (cells.gradedIndex c) (S2.{u}.rows.row c)
    rcases key c with hc | ⟨v, w, s', he, hl⟩
    · have : S2.{u}.rows.row c = fun _ ↦ ⊥ := by
        funext d
        -- the row of `c` is `rowValue2 c`
        change rowValue2 c d.1 = ⊥
        have h1 : ∀ c' : Fin 5, c' = 1 → ∀ d', rowValue2.{u} c' d' = ⊥ := by
          rintro c' rfl d'
          rfl
        exact h1 c hc d.1
      rw [this]
      exact CellScheme.Rows.isLawfulBelow_const_bot _
    · have : S2.{u}.rows.row c = fun d ↦ lab v w s' d.1 := funext fun d ↦ he d.1
      rw [this]
      exact isLawfulBelow_of_isLawful hl _
  isBountiful := by
    refine CellScheme.Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
    obtain ⟨B, j⟩ := X
    obtain ⟨C, k⟩ := Y
    obtain ⟨-, hj0, hjB⟩ := hX
    obtain ⟨hBC, -⟩ := h
    have key : ∀ B C : Finset (Fin 2), B ⊆ C → B ≠ ∅ →
        B = C ∨ (B = {0} ∧ C = Finset.univ) ∨ (B = {1} ∧ C = Finset.univ) := by decide
    have hB : B ≠ ∅ := by
      rintro rfl
      simp at hjB
      omega
    rcases key B C hBC hB with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact CellScheme.Rows.cappedLift_of_fst_eq _ rfl
    · obtain rfl : j = 1 := by simp at hjB; omega
      exact cappedLift_zero _
    · obtain rfl : j = 1 := by simp at hjB; omega
      exact cappedLift_one _
  isComplete X hX := by
    obtain ⟨B, j⟩ := X
    obtain ⟨-, hj0, hjB⟩ := hX
    have hj2 : j ≤ 2 := hjB.trans (by simpa using card_le_univ B)
    have key : ∀ B : Finset (Fin 2), ∀ j : Fin 3, 0 < (j : ℕ) → (j : ℕ) ≤ #B →
        ∃ d : Fin 5, cells.gradedIndex d = (B, (j : ℕ)) := by decide
    exact key B ⟨j, by omega⟩ hj0 hjB

/-! ### The context -/

/-- **The input**: the scheme `S2` labelled `⊤` at `y`, `z`, `o`, `r` and `⊥` at the dead cell. -/
noncomputable def t2 (α : Ordinal.{u}) : StageType.{u} α 2 where
  toScheme := S2
  label := lab ⊤ ⊤ ⊤
  isWellFormed := isLegal_S2.isWellFormed
  isCoded := isLegal_S2.isCoded
  isLawful := isLawful_lab2 (isSelfVisible_top 1) (isSelfVisible_top 2) (isSelfVisible_top 2)
    (by simp) le_rfl rfl
  atStage d := by fin_cases d <;> simp [lab]

/-- The cells of the input, by their index. -/
abbrev cellt2 (α : Ordinal.{u}) (i : Fin 5) : Fin (t2 α).card := i

/-- **The input is legal.** -/
theorem isLegal_t2 (α : Ordinal.{u}) : (t2 α).IsLegal := isLegal_S2

/-- **The input is a source-gap context** of grade `2` along the root `{0}`, with lost point `1`,
owner `o` and lost top `r`: the row of `o` reads `r` at `2`, and `o` at `ω·2 + 2` and `y` at
`ω + 2`. -/
theorem isSourceGapContextAt_t2 (α : Ordinal.{u}) :
    (t2 α).IsSourceGapContextAt 2 (Fin.castSuccEmb : Fin 1 ↪ Fin 2) 1 (cellt2 α 3)
      (cellt2 α 4) where
  notMem_range := fun ⟨i, hi⟩ ↦ (Fin.castSucc_lt_last i).ne hi
  topGrade_eq := le_antisymm (topGrade_le_iff.mpr fun d _ ↦ (t2 α).grade_le d)
    (grade_le_topGrade (t := t2 α) (d := cellt2 α 3) rfl :)
  scope_owner := rfl
  grade_owner := rfl
  label_owner := rfl
  label_lost := rfl
  mem_scope_lost := mem_univ _
  gap_owner := by
    rw [Scheme.rowAt_of_mem (show cells.gradedIndex 4 ≤ cells.gradedIndex 3 by decide),
      Scheme.rowAt_of_mem (show cells.gradedIndex 3 ≤ cells.gradedIndex 3 from le_rfl)]
    -- the row of `o` reads `r` at `2` and `o` at `ω·2 + 2`
    change visibilityReplace 2 2 low < high
    simpa [low] using low_lt_omegaAddTwo.{u}.trans omegaAddTwo_lt_high
  gap_retained a ha hla := by
    have key : ∀ a : Fin 5, 1 ∉ cells.scope a → a = 0 ∨ a = 1 := by decide
    rcases key a hla with rfl | rfl
    · -- the cell `0` is `y`
      change visibilityReplace 2 2 ((t2 α).rowAt (cellt2 α 3) (cellt2 α 4)) <
        (t2 α).rowAt (cellt2 α 3) (cellt2 α 0)
      rw [Scheme.rowAt_of_mem (show cells.gradedIndex 4 ≤ cells.gradedIndex 3 by decide),
        Scheme.rowAt_of_mem (show cells.gradedIndex 0 ≤ cells.gradedIndex 3 by decide)]
      -- the row of `o` reads `r` at `2` and `y` at `ω + 2`
      change visibilityReplace 2 2 low < omegaAddTwo
      simpa [low] using low_lt_omegaAddTwo.{u}
    · exact absurd ha (by simp [t2, lab])

/-- The only cell of the input visible on the root `{0}` is `y`. -/
theorem eq_zero_of_mem_visibleCells2 (d : Fin 5)
    (hd : d ∈ S2.{u}.visibleCells (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) : d = 0 := by
  rw [Scheme.mem_visibleCells] at hd
  have hd' : cells.scope d ⊆ univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) := by
    intro x hx
    obtain ⟨i, hi⟩ := hd hx
    exact mem_map.mpr ⟨i, mem_univ _, hi⟩
  clear hd
  revert hd'
  revert d
  decide

/-- The only cell of `SeparationObstruction.S` visible on the root `{0}` is `y`. -/
theorem eq_zero_of_mem_visibleCells (d : Fin 5)
    (hd : d ∈ S.{u}.visibleCells (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) : d = 0 := by
  rw [Scheme.mem_visibleCells] at hd
  have hd' : cells.scope d ⊆ univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) := by
    intro x hx
    obtain ⟨i, hi⟩ := hd hx
    exact mem_map.mpr ⟨i, mem_univ _, hi⟩
  clear hd
  revert hd'
  revert d
  decide

/-- The row of `y` is unchanged (entrywise: a definitional comparison of the two row tables makes
the kernel compare `ω + 2` with `ω·2 + 2`). -/
theorem rowValue2_zero (d : Fin 5) : rowValue2.{u} 0 d = rowValue 0 d := by
  fin_cases d <;> simp [rowValue2, rowValue]

/-- **The input has the face of `SeparationObstruction.T` on the root `{0}`**: the only cell
visible there is `y`, with the same row and the label `⊤` in both. -/
theorem restrictFace_t2 (α : Ordinal.{u}) :
    restrictFace Fin.castSuccEmb (t2 α) = restrictFace Fin.castSuccEmb (T α) := by
  rw [restrictFace_of_mem _ _ TwistedDonor.mem_faces,
    restrictFace_of_mem _ _ TwistedDonor.mem_faces]
  congr 1
  refine StageType.ext (Scheme.comap_mk_eq (R := S2.{u}.rows) (R' := S.{u}.rows) _
    fun c t hc ↦ ?_) fun i j _ ↦ ?_
  · obtain rfl := eq_zero_of_mem_visibleCells2 c hc
    exact rowValue2_zero t.1
  · -- the labels at `y`, compared without identifying the two cell types
    change lab ⊤ ⊤ ⊤ (S2.cellMap _ i) = lab ⊤ ⊤ ⊤ (S.cellMap _ j)
    rw [eq_zero_of_mem_visibleCells2 _ (S2.cellMap_mem _ i),
      eq_zero_of_mem_visibleCells _ (S.cellMap_mem _ j)]

/-! ### The violation -/

/-- **The provision from the context coatom fails for the owner as the partner.**  Let `v < h < ⊤`
with `h` self-visible at `2`.  The state (the labels `(⊤, ⊥, ⊤, ⊤, ⊤)` of the input, the labels
`(⊤, ⊥, ⊤, ⊤, v)` of the donor) is admitted; the labelling `(h, ⊥, h, ⊤, h)` of the input is
lawful and agrees with its labels capped at `h`; and no lawful labelling of the donor's scheme with
root `h`, agreeing with the donor capped at `h`, is admitted with it: it has `o' ≤ h` and `r' = v`,
while the clause asks `⊤ ≤ o'`. -/
theorem not_capProvision_context {v h : Label.{u}} (hh : IsSelfVisible 2 h) (hvh : v < h)
    (hht : h ≠ ⊤) :
    LowVia (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v) ∧ S2.{u}.rows.IsLawful (lab h ⊤ h) ∧
      (∀ d, min (lab h ⊤ h d) h = min (lab ⊤ ⊤ ⊤ d) h) ∧
      ¬ ∃ W : Fin 5 → Label.{u}, S.{u}.rows.IsLawful W ∧ W 0 = h ∧
        (∀ d, min (W d) h = min (lab ⊤ ⊤ v d) h) ∧ LowVia (lab h ⊤ h) W := by
  refine ⟨fun _ ↦ ⟨le_top, le_top⟩,
    isLawful_lab2 (hh.mono (by omega)) (isSelfVisible_top 2) hh (by simpa using hh) (by simp)
      (by simp),
    fun d ↦ by fin_cases d <;> simp [lab], ?_⟩
  rintro ⟨W, hW, hW0, hWR, hlow⟩
  obtain ⟨hWe, hW30, -⟩ := eq_lab_of_isLawful hW
  have hW1 : W 1 = ⊥ := by rw [hWe]; rfl
  -- `r'` is `v`, below `⊤`
  have hW4 : W 4 < ⊤ := by
    have e : min (W 4) h = min v h := hWR 4
    rw [min_eq_left hvh.le] at e
    by_contra hc
    rw [not_lt_top_iff.mp hc, min_eq_right le_top] at e
    exact hvh.ne e.symm
  have hlt : max (W 1) (W 4) < lab h ⊤ h 3 := by
    rw [hW1, max_eq_right bot_le]
    exact hW4
  have := ((lowVia_iff.mp hlow) hlt).2
  -- `o' ≤ y' = h < ⊤`
  exact hht (top_le_iff.mp (this.trans (hW30.trans hW0.le)))

/-- **The frontier alone serves at this input** (feasibility only): with `v` self-visible at `2`,
the donor labelling `(h, ⊥, h, h, v)` is lawful, has root `h`, agrees with the donor capped at `h`,
and its designated tops are at least the frontier `min o (visibilityReplace 2 2 r) = h` of the
labelling `(h, ⊥, h, ⊤, h)` of the input. -/
theorem exists_frontier_context {v h : Label.{u}} (hv : IsSelfVisible 2 v)
    (hh : IsSelfVisible 2 h) (hvh : v < h) :
    ∃ W : Fin 5 → Label.{u}, S.{u}.rows.IsLawful W ∧ W 0 = h ∧
      (∀ d, min (W d) h = min (lab ⊤ ⊤ v d) h) ∧
      min (lab h ⊤ h 3) (visibilityReplace 2 2 (lab h ⊤ h 4)) ≤ W 2 ∧
      min (lab h ⊤ h 3) (visibilityReplace 2 2 (lab h ⊤ h 4)) ≤ W 3 := by
  have hfr : min (lab h ⊤ h 3) (visibilityReplace 2 2 (lab h ⊤ h 4)) = h := by
    change min ⊤ (visibilityReplace 2 2 h) = h
    rw [hh.visibilityReplace_eq, min_eq_right le_top]
  refine ⟨lab h h v, isLawful_lab (hh.mono (by omega)) hh hv le_rfl rfl, rfl,
    fun d ↦ ?_, hfr.le, hfr.le⟩
  fin_cases d <;> simp [lab, min_eq_left hvh.le]

end OwnerPartner

end VaughtConjecture
