/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapSeparatedInstance

/-!
# Separation through the lost top fails: the separated pinned extension property is false

Roadmap, Layer 3 ((R2) of the table of 3.4); the separated pinned extensions of
`VaughtConjecture.Continuation.SourceGapDetermination`.

**The obstruction.**  Let `D'` be a legal one-point coface of a source-gap context `t'` that
separates the new tops through the lost top `r` at grade `K` (`StageType.SeparatesThrough`), and
let `q` be a lawful labelling of `D'` in which `r` is `⊤` and has grade `K`.  Availability puts `r`
below a cell `u` of graded index `(univ, K)` labelled `⊤`, and `u` reads every new top at least as
`r`, so every new top is `⊤` in `q` (`CellScheme.Rows.IsLawful.eq_top_of_row_le`).  Every lawful
labelling of `t'` extends to `D'` (bountifulness at the cap `⊥`,
`StageType.exists_isLawful_extend_of_restrictFace`).  So if `t'` has a lawful labelling with `r` at
`⊤` and a root cell `y` not at `⊤`, and the donor bounds a new top `x` by `y` in every lawful
labelling, no such `D'` exists.  The strict gaps do not prevent this: the owner can be lowered
below `y`, and `r` itself, of full scope and grade `K`, serves availability.

**The input** (`SeparationObstruction.T`, `SeparationObstruction.isLegal_T`).  On two points with
the interval plan, five cells:

| cell     | scope    | grade | row                                                | label |
|----------|----------|-------|----------------------------------------------------|-------|
| 0 (`y`)  | `{0}`    | 1     | `y ↦ 2`                                            | `⊤`   |
| 1 (`e`)  | `{1}`    | 1     | `⊥`                                                | `⊥`   |
| 2 (`z`)  | `univ`   | 1     | `y ↦ 2`, `z ↦ 2`                                   | `⊤`   |
| 3 (`o`)  | `univ`   | 2     | `y ↦ ω + 2`, `z ↦ ω + 2`, `o ↦ ω + 2`, `r ↦ 2`     | `⊤`   |
| 4 (`r`)  | `univ`   | 2     | `y ↦ 2`, `z ↦ 2`, `o ↦ 2`, `r ↦ ω + 2`             | `⊤`   |

(rows read `e` at `⊥`).  It is a legal source-gap context of grade `2` along the root `{0}`, with
lost point `1`, owner `o` and lost top `r` (`SeparationObstruction.isSourceGapContextAt_T`): the
gap at the owner is `visibilityReplace 2 2 2 = 2 < ω + 2`, at the owner and at the retained top
`y`.  The labelling `(2, ⊥, 2, 2, ⊤)` is lawful: `r` at `⊤`, the root top `y` at `2`.  The donor is
`T` itself, a legal one-point coface of its face on `{0}`, with the new top `z`: the row of `z`
reads `y` and `z` alike, so every lawful labelling has `z ≤ y`.

**The result** (compiled in this repository).  No legal one-point coface of `T` with face `T`
along the root followed by the new point separates the new tops through `r` at grade `2`
(`SeparationObstruction.not_exists_separatesThrough`); so the separated pinned extension property
`StageType.HasSeparatedPinnedExtensions α` is false at every stage
(`SeparationObstruction.not_hasSeparatedPinnedExtensions`), with no hypothesis.  The reductions
compiled from it (`Realization.cutoffDetermination_isSourceGapContext`,
`Realization.residualReceiving_of_hasSeparatedPinnedExtensions` and the block-stage forms) are
correct but have a false hypothesis; this says nothing about cutoff determination for source-gap
contexts or about (R2).  Separating through another cell (the owner, or a cell depending on the
donor) is not refuted here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.SeparationObstruction

open Finset Label CellScheme StageType SeparatedInstance
open scoped Ordinal

/-! ### A two-valued shifter at a grade bound -/

/-- The label `2`, the low row value. -/
noncomputable abbrev low : Label.{u} := ((2 : ℕ) : Label.{u})

theorem low_lt_coe_omega0 : low.{u} < ((ω : Ordinal.{u}) : Label.{u}) := by
  rw [low, natCast_label]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (Ordinal.natCast_lt_omega0 2))

theorem not_omegaAddTwo_lt' : ¬ omegaAddTwo.{u} < ((ω : Ordinal.{u}) : Label.{u}) :=
  fun h ↦ (not_lt.mpr le_self_add) (WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h))

theorem low_lt_omegaAddTwo : low.{u} < omegaAddTwo.{u} :=
  low_lt_coe_omega0.trans_le (not_lt.mp not_omegaAddTwo_lt')

theorem isSelfVisible_low : IsSelfVisible 2 low.{u} := by simp [low]

theorem isSelfVisible_omegaAddTwo_two : IsSelfVisible 2 omegaAddTwo.{u} :=
  isSelfVisible_coe_add Ordinal.isSuccLimit_omega0.isSuccPrelimit le_rfl

/-- **The two-valued shifter is a witness** with the step suppressor at `K`, for `a ≤ b`
self-visible at `K`. -/
theorem isWitness_twoLevel_step (K : ℕ) {a b : Label.{u}} (ha : IsSelfVisible K a)
    (hb : IsSelfVisible K b) (hab : a ≤ b) : IsWitness (stepSuppressor K) (twoLevel a b) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := by simp [twoLevel, WithBot.bot_lt_coe]
  monotone := by
    intro x y hxy
    simp only [twoLevel]
    by_cases hy : y < ((ω : Ordinal.{u}) : Label.{u})
    · rw [ite_eq_left (hxy.trans_lt hy), ite_eq_left hy]
      by_cases hx0 : x = ⊥
      · rw [ite_eq_left hx0]
        exact bot_le
      · rw [ite_eq_right hx0,
          ite_eq_right (show ¬ y = ⊥ from fun h ↦ hx0 (le_bot_iff.mp (h ▸ hxy)))]
    · rw [ite_eq_right hy]
      split_ifs <;> first | exact bot_le | exact hab | exact le_rfl
  visibilityReplace_comm x k hx i hi := by
    have hinv : twoLevel a b (visibilityReplace k i x) = twoLevel a b x := by
      simp only [twoLevel, Label.visibilityReplace_lt_iff Ordinal.isSuccLimit_omega0.isSuccPrelimit,
        visibilityReplace_eq_bot_iff]
    rw [hinv]
    have hsv : IsSelfVisible K (twoLevel a b x) := by
      simp only [twoLevel]
      split_ifs
      exacts [isSelfVisible_bot _, ha, hb]
    by_cases hk : k ≤ K
    · exact ((hsv.mono hk).visibilityReplace_eq i).symm
    · rw [stepSuppressor_of_lt (by omega), le_bot_iff] at hx
      rw [hx, visibilityReplace_bot]


/-- Rows of grade at most `K` with values `⊥`, `2`, `ω + 2` transform to sections with values
`⊥`, `a`, `b` at the same cells. -/
theorem transformsTo_twoLevel_step {E : Type*} {grade : E → ℕ} {K : ℕ} (hg : ∀ d, grade d ≤ K)
    {r t : E → Label.{u}} {a b : Label.{u}} (ha : IsSelfVisible K a) (hb : IsSelfVisible K b)
    (hab : a ≤ b)
    (h : ∀ d, (r d = ⊥ ∧ t d = ⊥) ∨ (r d = low ∧ t d = a) ∨ (r d = omegaAddTwo ∧ t d = b)) :
    TransformsTo grade r t :=
  ⟨_, _, isWitness_twoLevel_step K ha hb hab, fun d ↦ by
    rw [stepSuppressor_of_le (hg d), min_top_right]
    rcases h d with ⟨hr, ht⟩ | ⟨hr, ht⟩ | ⟨hr, ht⟩ <;> rw [hr, ht, twoLevel]
    · simp [WithBot.bot_lt_coe]
    · rw [ite_eq_left low_lt_coe_omega0, ite_eq_right (by simp [low])]
    · rw [ite_eq_right not_omegaAddTwo_lt']⟩

/-! ### The input -/

/-- The cells on `Fin 2`, with faces the intervals: `y` (`0`) of scope `{0}`, the dead cell `e`
(`1`) of scope `{1}`, `z` (`2`) of scope `univ`, all of grade `1`, and `o` (`3`), `r` (`4`) of
scope `univ` and grade `2`. -/
def cells : CellScheme (Fin 5) (Fin 2) :=
  ⟨univ, Geometry.intervalPlan univ, ![{0}, {1}, univ, univ, univ], ![1, 1, 1, 2, 2]⟩

/-- The rows: `y` and `z` read `y`, `z` at `2`; `o` reads `y`, `z`, `o` at `ω + 2` and `r` at `2`;
`r` reads `y`, `z`, `o` at `2` and `r` at `ω + 2`; every row reads `e` at `⊥`, and `e` reads `⊥`.
Entries at cells not below the reading cell are never read. -/
noncomputable def rowValue : Fin 5 → Fin 5 → Label.{u} :=
  ![![low, ⊥, low, ⊥, ⊥], fun _ ↦ ⊥, ![low, ⊥, low, ⊥, ⊥],
    ![omegaAddTwo, ⊥, omegaAddTwo, omegaAddTwo, low], ![low, ⊥, low, low, omegaAddTwo]]

/-- The scheme on two points. -/
noncomputable abbrev S : Scheme.{u} 2 := ⟨5, cells, ⟨fun s d ↦ rowValue s d.1⟩⟩

/-- The labelling `(v, ⊥, v, w, s)`. -/
noncomputable def lab (v w s : Label.{u}) : Fin 5 → Label.{u} := ![v, ⊥, v, w, s]

/-- **Lawful sections**: `(v, ⊥, v, w, s)` is lawful when `v` is self-visible at `1`, `w` and `s`
at `2`, `w ≤ v`, and `min v s = min w s`. -/
theorem isLawful_lab {v w s : Label.{u}} (hv : IsSelfVisible 1 v) (hw : IsSelfVisible 2 w)
    (hs : IsSelfVisible 2 s) (hwv : w ≤ v) (hvs : min v s = min w s) :
    S.{u}.rows.IsLawful (lab v w s) where
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
      fin_cases d <;> first | exact absurd hd' (by decide) | simp [lab, rowValue]
    · convert TransformsTo.bot _ _ using 1
      funext d
      -- the transformed section at the dead cell `e`
      change min _ (lab v w s 1) = ⊥
      simp [lab]
    · -- `z`: the row reads `y`, `z` at `2`; the section is `v` there
      refine transformsTo_twoLevel_step (K := 1) (fun d ↦ hg 2 d) hv hv le_rfl fun ⟨d, hd⟩ ↦ ?_
      have hd' : cells.gradedIndex d ≤ cells.gradedIndex 2 := hd
      fin_cases d <;> first | exact absurd hd' (by decide) | simp [lab, rowValue]
    · -- `o`: the section capped at `w` is `w` at `y`, `z`, `o` and `min s w` at `r`
      refine transformsTo_twoLevel_step (K := 2) (fun d ↦ hg 3 d) (hs.min hw) hw
        (min_le_right _ _) fun ⟨d, hd⟩ ↦ ?_
      fin_cases d <;> simp [lab, rowValue, min_eq_right hwv]
    · -- `r`: the section capped at `s` is `min w s` at `y`, `z`, `o` and `s` at `r`
      refine transformsTo_twoLevel_step (K := 2) (fun d ↦ hg 4 d) (hw.min hs) hs
        (min_le_right _ _) fun ⟨d, hd⟩ ↦ ?_
      fin_cases d <;> simp [lab, rowValue, hvs]
  availability c t hct hg := by
    have key : ∀ c t : Fin 5, cells.scope c ⊆ cells.scope t → cells.grade c = cells.grade t →
        cells.gradedIndex c = cells.gradedIndex t ∨ (t = 2 ∧ (c = 0 ∨ c = 1)) := by decide
    rcases key c t hct hg with h | ⟨rfl, rfl | rfl⟩
    · exact ⟨c, h, le_rfl⟩
    · exact ⟨2, rfl, le_rfl⟩
    · exact ⟨2, rfl, bot_le⟩

/-- A lawful section gives lawful labellings below every pair. -/
private theorem isLawfulBelow_of_isLawful {w : Fin 5 → Label.{u}} (h : S.{u}.rows.IsLawful w)
    (X : Finset (Fin 2) × ℕ) : S.{u}.rows.IsLawfulBelow X (fun d ↦ w d) :=
  CellScheme.Rows.isLawfulBelow_iff_forall.mpr
    ⟨fun d _ ↦ h.orderly d, fun s _ ↦ h.locality s, fun s t _ hst hg ↦ h.availability s t hst hg⟩

/-- A section below `X`, extended by `⊥`, is lawful below `X`. -/
private theorem isLawfulBelow_extendBot {X : Finset (Fin 2) × ℕ} {q : cells.below X → Label.{u}}
    (hq : S.{u}.rows.IsLawfulBelow X q) :
    S.{u}.rows.IsLawfulBelow X (fun d ↦ CellScheme.Rows.extendBot X q d) := by
  convert hq using 1
  funext d
  exact CellScheme.Rows.extendBot_of_mem q d.2

/-- **Lawful sections below `(univ, 1)`**, necessary conditions: `e` is `⊥` and `z` equals `y`
(`z` reads `y` as itself, and `y` lies below `z`). -/
private theorem conditions_univ_one {w : Fin 5 → Label.{u}}
    (hq : S.{u}.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 1) (fun d ↦ w d)) :
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
    S.{u}.rows.CappedLift h := by
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
    (isLawful_lab hv (isSelfVisible_bot _) (isSelfVisible_bot _) bot_le (by simp)) _,
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
    S.{u}.rows.CappedLift h := by
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
      le_refl ((S.{u}.toCellScheme.reindex Subtype.val).gradedIndex ⟨1, hd⟩)⟩) rfl
    simpa using this
  rw [hp1]
  exact hq1

/-- **The scheme is legal.** -/
theorem isLegal_S : S.{u}.IsLegal where
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ by
    have key : ∀ d : Fin 5, cells.scope d ∈ cells.faces ∧ 0 < cells.grade d ∧
        cells.grade d ≤ #(cells.scope d) := by decide
    exact key d⟩⟩
  isCoded s t := by
    have key : ∀ s d : Fin 5, rowValue.{u} s d = ⊥ ∨ rowValue.{u} s d = low ∨
        rowValue.{u} s d = omegaAddTwo := by
      intro s d
      fin_cases s <;> fin_cases d <;> simp [rowValue]
    -- the rows of `S` are `rowValue`
    change rowValue s t.1 < _
    rcases key s t.1 with h | h | h <;> rw [h]
    · exact WithBot.bot_lt_coe _
    · exact natCast_label_lt_omega0_sq 2
    · exact lt_omega0_sq_iff.mpr (.inr ⟨1, 2, by simp [omegaAddTwo]⟩)
  isConsistent c := by
    have key : ∀ c : Fin 5, c = 1 ∨ ∃ v w s' : Label.{u},
        (∀ d, rowValue c d = lab v w s' d) ∧ S.{u}.rows.IsLawful (lab v w s') := by
      have hl0 := isLawful_lab (v := low.{u}) (w := ⊥) (s := ⊥)
        (isSelfVisible_low.mono (by omega)) (isSelfVisible_bot _) (isSelfVisible_bot _) bot_le
        (by simp)
      intro c
      fin_cases c
      · exact .inr ⟨low, ⊥, ⊥, fun d ↦ by fin_cases d <;> rfl, hl0⟩
      · exact .inl rfl
      · exact .inr ⟨low, ⊥, ⊥, fun d ↦ by fin_cases d <;> rfl, hl0⟩
      · exact .inr ⟨omegaAddTwo, omegaAddTwo, low, fun d ↦ by fin_cases d <;> rfl,
          isLawful_lab (isSelfVisible_omegaAddTwo_two.mono (by omega))
            isSelfVisible_omegaAddTwo_two isSelfVisible_low le_rfl rfl⟩
      · exact .inr ⟨low, low, omegaAddTwo, fun d ↦ by fin_cases d <;> rfl,
          isLawful_lab (isSelfVisible_low.mono (by omega)) isSelfVisible_low
            isSelfVisible_omegaAddTwo_two le_rfl rfl⟩
    -- consistency at `c` is lawfulness of its row below its graded index
    change S.{u}.rows.IsLawfulBelow (cells.gradedIndex c) (S.{u}.rows.row c)
    rcases key c with hc | ⟨v, w, s', he, hl⟩
    · have : S.{u}.rows.row c = fun _ ↦ ⊥ := by
        funext d
        -- the row of `c` is `rowValue c`
        change rowValue c d.1 = ⊥
        have h1 : ∀ c' : Fin 5, c' = 1 → ∀ d', rowValue.{u} c' d' = ⊥ := by
          rintro c' rfl d'
          rfl
        exact h1 c hc d.1
      rw [this]
      exact CellScheme.Rows.isLawfulBelow_const_bot _
    · have : S.{u}.rows.row c = fun d ↦ lab v w s' d.1 := funext fun d ↦ he d.1
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

/-- **The input**: the scheme `S` labelled `⊤` at `y`, `z`, `o`, `r` and `⊥` at the dead cell. -/
noncomputable def T (α : Ordinal.{u}) : StageType.{u} α 2 where
  toScheme := S
  label := lab ⊤ ⊤ ⊤
  isWellFormed := isLegal_S.isWellFormed
  isCoded := isLegal_S.isCoded
  isLawful := isLawful_lab (isSelfVisible_top 1) (isSelfVisible_top 2) (isSelfVisible_top 2)
    le_rfl rfl
  atStage d := by fin_cases d <;> simp [lab]

/-- The cells of the input, by their index. -/
abbrev cellT (α : Ordinal.{u}) (i : Fin 5) : Fin (T α).card := i

/-- **The input is legal.** -/
theorem isLegal_T (α : Ordinal.{u}) : (T α).IsLegal := isLegal_S

/-- In every lawful labelling of the input, `z` is at most `y`: the row of `z` reads both alike. -/
theorem le_of_isLawful {α : Ordinal.{u}} {P : Fin (T α).card → Label.{u}}
    (hP : (T α).rows.IsLawful P) : P (cellT α 2) ≤ P (cellT α 0) := by
  have := (hP.locality (cellT α 2)).le_of_le
    (d := ⟨cellT α 2, CellScheme.mem_below_gradedIndex _ _⟩)
    (d' := ⟨cellT α 0, show cells.gradedIndex 0 ≤ cells.gradedIndex 2 by decide⟩) le_rfl le_rfl
  simpa using this

/-- **The input is a source-gap context** of grade `2` along the root `{0}`, with lost point `1`,
owner `o` and lost top `r`. -/
theorem isSourceGapContextAt_T (α : Ordinal.{u}) :
    (T α).IsSourceGapContextAt 2 (Fin.castSuccEmb : Fin 1 ↪ Fin 2) 1 (cellT α 3) (cellT α 4) where
  notMem_range := fun ⟨i, hi⟩ ↦ (Fin.castSucc_lt_last i).ne hi
  topGrade_eq := le_antisymm (topGrade_le_iff.mpr fun d _ ↦ (T α).grade_le d)
    (grade_le_topGrade (t := T α) (d := cellT α 3) rfl :)
  scope_owner := rfl
  grade_owner := rfl
  label_owner := rfl
  label_lost := rfl
  mem_scope_lost := mem_univ _
  gap_owner := by
    rw [Scheme.rowAt_of_mem (show cells.gradedIndex 4 ≤ cells.gradedIndex 3 by decide),
      Scheme.rowAt_of_mem (show cells.gradedIndex 3 ≤ cells.gradedIndex 3 from le_rfl)]
    -- the row of `o` reads `r` at `2` and `o` at `ω + 2`
    change visibilityReplace 2 2 low < omegaAddTwo
    simpa [low] using low_lt_omegaAddTwo.{u}
  gap_retained a ha hla := by
    have key : ∀ a : Fin 5, 1 ∉ cells.scope a → a = 0 ∨ a = 1 := by decide
    rcases key a hla with rfl | rfl
    · -- the cell `0` is `y`
      change visibilityReplace 2 2 ((T α).rowAt (cellT α 3) (cellT α 4)) <
        (T α).rowAt (cellT α 3) (cellT α 0)
      rw [Scheme.rowAt_of_mem (show cells.gradedIndex 4 ≤ cells.gradedIndex 3 by decide),
        Scheme.rowAt_of_mem (show cells.gradedIndex 0 ≤ cells.gradedIndex 3 by decide)]
      -- the row of `o` reads `r` at `2` and `y` at `ω + 2`
      change visibilityReplace 2 2 low < omegaAddTwo
      simpa [low] using low_lt_omegaAddTwo.{u}
    · exact absurd ha (by simp [T, lab])

/-! ### The obstruction -/

/-- **No legal one-point coface of the input with face the input along the root `{0}` followed by
the new point separates the new tops through the lost top `r` at grade `2`.**  The lawful
labelling `(2, ⊥, 2, 2, ⊤)` of the input extends to such a coface; its face along the root followed
by the new point keeps the new top `z` at most `y`, which is `2`; but `r` is `⊤` of grade `2`, so a
cell of graded index `(univ, 2)` is `⊤`, and it reads `z` at least as `r`, so `z` is `⊤`. -/
theorem not_exists_separatesThrough (α : Ordinal.{u}) :
    ¬ ∃ (D' : StageType.{u} α 3) (hD' : D' ∈ (T α).cofaces),
      restrictFace (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) D' = some (T α) ∧
        SeparatesThrough hD'.2 (Fin.castSuccEmb : Fin 1 ↪ Fin 2) 2 (cellT α 4) := by
  rintro ⟨D', ⟨hD'l, h₁⟩, h₂, hsep⟩
  -- the lawful labelling `(2, ⊥, 2, 2, ⊤)` of the input, extended to `D'`
  have hA : (T α).rows.IsLawful (lab low low ⊤) :=
    isLawful_lab (isSelfVisible_low.mono (by omega)) isSelfVisible_low (isSelfVisible_top 2)
      le_rfl rfl
  obtain ⟨q, hq, hqA⟩ := exists_isLawful_extend_of_restrictFace hD'l h₁ hA
  -- the donor face keeps `z` at most `y`
  have hzy := le_of_isLawful (isLawful_comp_faceCell h₂ hq)
  -- the cell `y` of the donor face is the cell `y` of the context face
  have hy : faceCell h₂ (cellT α 0) = faceCell h₁ (cellT α 0) := by
    have hsc : D'.toCellScheme.scope (faceCell h₂ (cellT α 0)) =
        (cells.scope 0).map (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) :=
      scope_faceCell h₂ _
    obtain ⟨z, hz⟩ := exists_faceCell_eq_of_last_notMem h₁ (s := faceCell h₂ (cellT α 0)) (by
      rw [hsc]
      decide)
    have hsz : (cells.scope z).map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) =
        (cells.scope 0).map (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) := by
      rw [← hsc, ← hz, scope_faceCell]
      rfl
    have key : ∀ z : Fin 5, (cells.scope z).map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) =
        (cells.scope 0).map (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) → z = 0 := by
      decide
    rw [← hz, key z hsz]
  rw [hy, hqA] at hzy
  -- the lost top is `⊤` in `q`, so a cell of graded index `(univ, 2)` is `⊤`
  have hr : q (faceCell h₁ (cellT α 4)) = ⊤ := hqA _
  obtain ⟨u₀, hu₀⟩ := (isLegal_iff.mp hD'l).2.2 (univ, 2)
    ⟨D'.univ_mem_faces, by omega, by simp⟩
  obtain ⟨u, hu, hqu⟩ := hq.availability (faceCell h₁ (cellT α 4)) u₀
    (by rw [show D'.toCellScheme.scope u₀ = univ from congrArg Prod.fst hu₀]
        exact subset_univ _)
    (by rw [grade_faceCell, show D'.toCellScheme.grade u₀ = 2 from congrArg Prod.snd hu₀]; rfl)
  rw [hu₀] at hu
  rw [hr, top_le_iff] at hqu
  -- the new top `z` of the donor face
  set x := faceCell h₂ (cellT α 2)
  have hx : x ∈ D'.visibleCells (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) :=
    D'.toScheme.faceCell_mem_visibleCells _ _
  have hxl : Fin.last 2 ∈ D'.toCellScheme.scope x := by
    rw [scope_faceCell, mem_map]
    exact ⟨Fin.last 1, mem_univ _, extendByLast_last _⟩
  have hxt : D'.label x = ⊤ := (label_faceCell h₂ _).trans rfl
  have hread := hsep x hx hxl hxt u hu
  have hmem {c : Fin D'.card} (hc : D'.toCellScheme.grade c ≤ 2) :
      c ∈ D'.toCellScheme.below (D'.toCellScheme.gradedIndex u) := by
    rw [CellScheme.mem_below, hu]
    exact ⟨subset_univ _, hc⟩
  have hgr : D'.toCellScheme.grade (faceCell h₁ (cellT α 4)) ≤ 2 := by
    rw [grade_faceCell]; exact le_rfl
  have hgx : D'.toCellScheme.grade x ≤ 2 := by
    rw [grade_faceCell]; exact (by decide : (1 : ℕ) ≤ 2)
  rw [Scheme.rowAt_of_mem (hmem hgr), Scheme.rowAt_of_mem (hmem hgx)] at hread
  have hxtop := hq.eq_top_of_row_le (s := ⟨_, hmem hgr⟩) (x := ⟨x, hmem hgx⟩) hqu hr hread
  rw [hxtop] at hzy
  exact (low_lt_omegaAddTwo.trans_le le_top).ne (top_le_iff.mp hzy)

/-- **The separated pinned extension property is false at every stage**: at the input `T α`,
along the root `{0}`, with the donor `T α` itself (a legal one-point coface of its face on `{0}`,
of top grade `2`), no separating coface exists. -/
theorem not_hasSeparatedPinnedExtensions (α : Ordinal.{u}) :
    ¬ HasSeparatedPinnedExtensions α := fun hsep ↦ by
  have hf : univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∈ (T α).toCellScheme.faces := by
    -- the faces of the input are the interval plan
    change _ ∈ Geometry.intervalPlan univ
    decide
  have ht : restrictFace Fin.castSuccEmb (T α) = some ((T α).comap _ hf) :=
    restrictFace_of_mem _ _ hf
  obtain ⟨D', hD', hD'd, hsp⟩ := hsep (T α) _ _ _ _ (isLegal_T α) (isSourceGapContextAt_T α) _ ht
    (T α) ⟨isLegal_T α, ht⟩ (topGrade_le_iff.mpr fun d _ ↦ (T α).grade_le d)
  exact not_exists_separatesThrough α ⟨D', hD', hD'd, hsp⟩

end VaughtConjecture.SeparationObstruction
