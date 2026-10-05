/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CaseSplitCounterexample

/-!
# A legal seed on which the existential two-face lift at the grade two fails

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the recursion on the grade; here a legal seed for
which the hypothesis of the step of the tower, stated exactly, fails at the grade `2`); semantic
contract, items 2–4.

The existential two-face lift `2FL∃(j)` (`Seed.TwoFaceLiftExists`, module
`VaughtConjecture.Extension.TwoFaceLiftExists`) is the hypothesis of the step of the tower from the
grade `j` to `j + 1`, stated exactly (`Seed.towerInvariant_succ_iff_twoFaceLiftExists`, for
`j ≤ m` and under the invariant at `j`), and the invariant at the top grade holds exactly when
`2FL∃(j)` holds at the grades `2 ≤ j < m` (`Seed.towerInvariant_top_iff`).  This module shows that
`2FL∃(2)` fails for a legal seed on five points (`not_twoFaceLiftExists_two_seedL`), at every
stage.  So the step fails for that seed: the invariant of its tower fails at the grade `3` and at
the top grade `4` (`not_towerInvariant_three_seedL`, `not_towerInvariant_top_seedL`), and the
tower does not complete every seed.  `2FL∃(j)` at the grades `2 ≤ j < m` is false as a statement
about every seed, at every stage (`not_forall_twoFaceLiftExists`), and so are the raised union
fill at the grade `2` (`not_raisedUnionFill_two_seedL`) and the case split
`2FL(2) ∨ Seed.DeadAt 2` (`not_twoFaceLift_or_deadAt_seedL`) for that seed.

**The left type `TL`** (`TL`, `isLegal_TL`).  The scheme `SL` on four points has the cells of the
type `T5` of the module `VaughtConjecture.Extension.CaseSplitCounterexample` (nineteen cells, one
at every graded face of grade at most `3` of the interval plan) and the same live cells: the cells
of grade `1` whose scope contains the point `3`, the cell at `(univ, 2)`, and the cells of grade
`3` at `{0, 1, 2}` and at `univ` (the cells `16` and `18`).  `TL` is `SL` with the apex added.
The rows are those of `T5` except the row of the cell `18`, at `(univ, 3)`: it reads the live
cells of grade `1` at the ordinal `1` and the other live cells at `ω + 3`.

**The lawful labellings** (`isLawfulBelow_iff`).  Below every pair, the lawful labellings are the
restrictions of `labelling A F G` (`⊥` at the dead cells and `A`, `F`, `G` at the live cells of
grade `1`, `2`, `3`), for `A`, `F`, `G` self-visible at `1`, `2`, `3` with `G ≤ F` and
`VisibilityReplaceFixedOfLT A G`: if `A < G`, then `visibilityReplace 3 1 A = A`, that is, if the
finite part of `A` is below `3`, it is `1`.  So the parameter `G` of grade `3` is coupled to `F`
only, while in `T5` it is coupled to `A` and to `F` (`G ≤ A`, `G ≤ F`).  Locality at the cell
`18`, whose row has equal entries at the cells `15` and `18`, gives `G ≤ F`; and it gives
`VisibilityReplaceFixedOfLT A G` (`visibilityReplaceFixedOfLT_of_transformsTo`): if `A < G`, a
witness `(g, σ)` at the cell `18` has `σ 1 = A ≤ g 3`, and its commutation with
`visibilityReplace 3 1` at the natural number `1` gives `A = visibilityReplace 3 1 A`.
Sufficiency uses at the cell `18` the *strip shifter at the grade `3`* (`strip3`,
`isWitness_strip3`), the strip shifter of `T4` one grade up: it sends `⊥` to `⊥`, a natural number
`n` to `visibilityReplace 3 (min n 3) A`, and every label `≥ ω` to `⊤`; under
`VisibilityReplaceFixedOfLT A G`, `min (visibilityReplace 3 1 A) G = min A G`
(`min_visibilityReplace_three_one`).  Every pair lifts capped to every larger one
(`cappedLift_all`; the lifted parameters satisfy `VisibilityReplaceFixedOfLT` by
`visibilityReplaceFixedOfLT_lift`), so `TL` is legal.

**The seed** (`seedL`).  The rows of `TL` and `T5` differ only at the cell `18` and at the apex,
whose scopes are not in `{0, 1, 2}`, so the two types have the same face on `{0, 1, 2}`
(`comap_TL_eq`, through `Scheme.comap_mk_congr`).  The *asymmetric seed* `seedL` is the seed of
`TL` and `T5` over that face (`Seed.ofCoatoms`), with coatoms `C = {0, 1, 2, 3}` (of type `TL`)
and `D = {0, 1, 2, 4}` (of type `T5`) and common face `E = {0, 1, 2}`, which carries one live cell
`g`, at `({0, 1, 2}, 3)`.  Both types have exactly one cell at each graded index.  The labellings
of the amalgam used are `tripleLabelling A_C F_C A_D F_D G` of the module
`VaughtConjecture.Extension.CaseSplitCounterexample`, lawful below both coatoms at the grade `3`
when `G ≤ F_C`, `VisibilityReplaceFixedOfLT A_C G`, `G ≤ A_D` and `G ≤ F_D`
(`isLawfulBelow_tripleLabelling`).  The refutation is proved for every seed on five points whose
left coatom type is `TL` and whose right coatom type is `T5` (`not_twoFaceLiftExists_two_of`) and
specialized to `seedL` by `rfl`.

**The failure** (`not_twoFaceLiftExists_two_of`).  Take `d₁` the cell at `({3}, 1)` on `C`, `d₂`
the cell at `({4}, 1)` on `D`, and `s_C` the cell at `({0, 1, 2, 3}, 2)`.

1. As for `T4`, a catalogue entry `b₀` of the layer at the grade `2` takes one value `β₁ = ω·B + 1`
   at `d₁` and `d₂`, below its strip cap `h₂ = ω·B + 2`, and the extension of `b₀` through that
   layer agrees with its field row capped at `h₂`.
2. The old cells of grade `3` are not set to `⊥`: they carry `γ = ω·(B − 1) + 4`, and the
   resulting labelling, lawful below `(univ, 3)` (`γ ≤ β₁` for the coupling of `T5`), gives a
   catalogue entry `a` at the grade `3`.  The cap is `h = a(g)`, the orbit code of `γ`.
3. A new cell at `(univ, 2)` where `a` reaches `h` has key at least `γ` at the grade `3`.  The
   agreement heights below `h₂` are `⊥` or `ω·c + 2` with `c < B`, of key `ω·c + 3 < γ`; so the
   entry of that cell agrees with `b₀` capped at `h₂`, and its row reads `d₁` and `d₂` at the same
   value `β₁`.
4. The prescription `w_C` on `C` is `a(d₁)` at the live cells of grade `1` and `⊤` at the live
   cells of grade `2` and `3`; it is lawful in `TL` (`a(d₁)` has finite part `1`) and agrees with
   `a` capped at `h`.
5. Every `w_D` lawful below `(D, 3)` and equal to `w_C` on `E` is `⊤` at `g`, hence `⊤` at `d₂` by
   the coupling `G ≤ A` of `T5` (`le_of_isLawfulBelow_right`).  The two-face extension is `⊤` at
   `s_C`, hence, by availability, `⊤` at a new cell `u` at `(univ, 2)`, where `a ≥ h`; locality at
   `u` gives `⊤ = w_D(d₂) ≤ w_C(d₁) = a(d₁) < ⊤`.

The argument concerns the existence of `w_D` and of the extension: `2FL∃(2)` lets the step choose
both, and no choice works.  In the argument for `T4` the cap is `ω·(2ρ − 1) + 3`, with `ρ` the key
rank of `β₁` at the grade `3`, and a coupling of `g` below `d₂` would keep the label of `g` in the
catalogue entry below that cap, so it would not constrain `w_D`; this holds for that cap only.
With the cap `h = a(g)` used here, the coupling forces `w_D(d₂) = ⊤`.

**What is not refuted.**  Nothing is claimed about a completion below the full grade of `seedL`
built by another construction, nor about `StageType.HasApexCoatomExtensions` or
`StageType.HasCoatomExtensions`.  What fails is the step of the tower, and so the tower as a
completion of `seedL`.

**The open point.**  Whether `seedL` has a completion below the full grade at all (at a stage
that is zero or a limit, one would give a legal stage type with an apex whose faces along the two
coatoms are `TL` and `T5`, `CompletionBelowFullGrade.exists_coatomExtension`).  A necessary
condition, argued and not formalized: for a cap `c`, the prescription `(A, ⊤, ⊤)` on `C` with `A`
of finite part `1`, and every labelling `q` lawful below `(univ, 3)` that agrees with it capped at
`c`, some cell `u` of the completion at `(univ, 2)` with `q(u) ≥ c` *separates* `d₁` and `d₂`: its
row reads `d₁` strictly below `d₂`.  The tower never meets it: in step 3, every cell at
`(univ, 2)` where `a` reaches `h` reads `d₁` and `d₂` at the same value.  A candidate, prospective
and not constructed, is a completion with one new cell at each `(univ, k)`, whose cell at
`(univ, 2)` has an *ordered* row, reading the cells of grade `1` of `C` strictly below those of
`D`.

**Redesigns examined** (argued, not formalized).  The identified obstruction survives the
redesigns examined:

* more catalogue entries at the grade `2`: a new cell at `(univ, 2)` whose value in the extension
  of `b₀` is below `h₂` is an agreement height of key below `γ`, so step 3 is unchanged;
* a finer finite grid of agreement heights, self-visible at the grade `2`: `γ` is chosen with a
  finite part above those of the grid, still with `γ ≤ β₁`;
* the choice of `w_D`, of the extension, of the order of the coatoms, or an owner seeing both
  faces: `2FL∃(2)` already quantifies existentially over `w_D` and the extension, and an owner
  changes only how the extension is found.

Not examined: rows of the layers that are not entries of catalogue entries at the old cells (such
as the ordered rows above), a catalogue at the grade `j + 1` restricted so that its entries do not
reach the cap only at cells reading `d₁` and `d₂` alike, and completions not built as a tower.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.TwoFaceLiftExistsCounterexample

open Finset Label CellScheme
open Ordinal hiding univ
open TwoFaceLiftCounterexample (cellScope cellGrade cells v1 v2 gradedIndex_cells
  gradedIndex_injective complete_below mem_below_of_le stripShifter isWitness_stripShifter
  stripShifter_bot stripShifter_v1 stripShifter_v2 v1_eq Q_le_Q)
open CaseSplitCounterexample (live v3 labelling tripleLabelling tripleKind live_le_live live_up
  live_grade grade_le_three grade_three_cases live_cases le_eighteen three_le_of_grade_one
  eq_fifteen_of_grade_two sixteen_le_of_grade_three eighteen_mem_below labelling_dead labelling_one
  labelling_two labelling_three isSelfVisible_labelling lift_le tripleLabelling_left
  tripleLabelling_right tripleLabelling_eq_of_le_two)

/-! ### The strip shifter at the grade `3` -/

/-- The **strip shifter at the grade `3`** of `A`: `⊥ ↦ ⊥`; the natural numbers `n` go to
`visibilityReplace 3 (min n 3) A`; every label `≥ ω` goes to `⊤`. -/
noncomputable def strip3 (A x : Label.{u}) : Label.{u} :=
  if x = ⊥ then ⊥ else if x < ((ω : Ordinal.{u}) : Label.{u}) then
    (if x = 0 then visibilityReplace 3 0 A else if x = 1 then visibilityReplace 3 1 A
      else if x = 2 then visibilityReplace 3 2 A else visibilityReplace 3 3 A)
  else ⊤

theorem strip3_natCast (A : Label.{u}) (n : ℕ) :
    strip3 A (n : Label.{u}) = visibilityReplace 3 (min n 3) A := by
  unfold strip3
  rw [ite_eq_right (natCast_label_ne_bot n), ite_eq_left (natCast_label_lt_omega n)]
  have h0 : ((n : Label.{u}) = 0) ↔ n = 0 := by
    rw [show (0 : Label.{u}) = ((0 : ℕ) : Label.{u}) by simp]; exact natCast_label_inj
  have h1 : ((n : Label.{u}) = 1) ↔ n = 1 := by
    rw [show (1 : Label.{u}) = ((1 : ℕ) : Label.{u}) by simp]; exact natCast_label_inj
  have h2 : ((n : Label.{u}) = 2) ↔ n = 2 := by
    rw [show (2 : Label.{u}) = ((2 : ℕ) : Label.{u}) by simp]; exact natCast_label_inj
  by_cases hn0 : n = 0
  · rw [ite_eq_left (h0.mpr hn0), hn0]; rfl
  · rw [ite_eq_right (mt h0.mp hn0)]
    by_cases hn1 : n = 1
    · rw [ite_eq_left (h1.mpr hn1), hn1]; rfl
    · rw [ite_eq_right (mt h1.mp hn1)]
      by_cases hn2 : n = 2
      · rw [ite_eq_left (h2.mpr hn2), hn2]; rfl
      · rw [ite_eq_right (mt h2.mp hn2)]
        congr 1; omega

theorem strip3_of_not_lt {A x : Label.{u}} (hx : x ≠ ⊥)
    (hxω : ¬ x < ((ω : Ordinal.{u}) : Label.{u})) : strip3 A x = ⊤ := by
  unfold strip3
  rw [ite_eq_right hx, ite_eq_right hxω]

theorem strip3_bot (A : Label.{u}) : strip3 A ⊥ = ⊥ := by
  unfold strip3; rw [ite_eq_left rfl]

theorem monotone_strip3 (A : Label.{u}) : Monotone (strip3 A) := by
  intro x y hxy
  by_cases hx : x = ⊥
  · rw [hx, strip3_bot]; exact bot_le
  have hy : y ≠ ⊥ := fun hy ↦ hx (le_bot_iff.mp (hy ▸ hxy))
  by_cases hyω : y < ((ω : Ordinal.{u}) : Label.{u})
  · have hxω := hxy.trans_lt hyω
    obtain ⟨n, rfl⟩ := exists_natCast_of_lt_omega hx hxω
    obtain ⟨m, rfl⟩ := exists_natCast_of_lt_omega hy hyω
    rw [strip3_natCast, strip3_natCast]
    exact visibilityReplace_le_visibilityReplace (min_le_min_right 3 (natCast_label_le.mp hxy)) A
  · rw [strip3_of_not_lt hy hyω]; exact le_top

/-- **The strip shifter at the grade `3` is a witness** for the suppressor `G` up to the grade
`3`. -/
theorem isWitness_strip3 {A G : Label.{u}} (hG : IsSelfVisible 3 G) :
    IsWitness (constStepSuppressor 3 G) (strip3 A) where
  antitone := antitone_constStepSuppressor 3 G
  isSelfVisible := isSelfVisible_constStepSuppressor hG
  map_bot := strip3_bot A
  monotone := monotone_strip3 A
  visibilityReplace_comm x k hx i hi := by
    by_cases hx0 : x = ⊥
    · rw [hx0, visibilityReplace_bot, strip3_bot, visibilityReplace_bot]
    by_cases hxω : x < ((ω : Ordinal.{u}) : Label.{u})
    · obtain ⟨n, rfl⟩ := exists_natCast_of_lt_omega hx0 hxω
      rw [Label.visibilityReplace_natCast]
      have hcast : ((if n < k then (i : Label.{u}) else n) : Label.{u}) =
          ((if n < k then i else n : ℕ) : Label.{u}) := by split_ifs <;> rfl
      rw [hcast, strip3_natCast, strip3_natCast]
      by_cases hk : k ≤ 3
      · rw [visibilityReplace_visibilityReplace_of_le hk]
        congr 1
        split_ifs <;> omega
      · rw [strip3_natCast, constStepSuppressor, ite_eq_right hk, le_bot_iff,
          visibilityReplace_eq_bot_iff] at hx
        rw [hx]; simp
    · rw [strip3_of_not_lt hx0 hxω, visibilityReplace_top,
        strip3_of_not_lt (by rwa [Ne, visibilityReplace_eq_bot_iff])
          (not_lt_omega_visibilityReplace hx0 hxω k i)]

/-! ### The scheme -/

/-- The row value of the cell `18` at the live cells of grade `2` and `3`: `ω + 3`. -/
noncomputable abbrev v3' : Label.{u} := gridPoint 3 1

/-- The rows of `TL`: those of `T5`, except that the cell `18` reads the live cells of grade `1`
at `v1 = 1` and the other live cells at `v3' = ω + 3`. -/
noncomputable def rowsL : cells.Rows.{u} :=
  ⟨fun s t ↦ if live s = true ∧ live t.1 = true then
    (if s = 18 then (if cellGrade t.1 = 1 then v1 else v3')
      else if cellGrade s = 3 then v3 else if cellGrade t.1 = 1 then v1 else v2) else ⊥⟩

/-- The scheme on four points. -/
noncomputable def SL : Scheme.{u} 4 := ⟨19, cells, rowsL⟩

/-- The condition of `TL` on its parameters `A` (of grade `1`) and `G` (of grade `3`): if `A < G`,
then `visibilityReplace 3 1 A = A`, that is, if the finite part of `A` is below `3`, it is `1`. -/
def VisibilityReplaceFixedOfLT (A G : Label.{u}) : Prop := A < G → visibilityReplace 3 1 A = A

/-- Below the cell `16`, the only live cell is `16`. -/
private theorem eq_sixteen_of_le : ∀ d : Fin 19, live d = true →
    cells.gradedIndex d ≤ cells.gradedIndex 16 → d = 16 := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

private theorem v3'_not_lt : ¬ (v3' : Label.{u}) < ((ω : Ordinal.{u}) : Label.{u}) := by
  rw [not_lt, v3', gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe]
  simp only [Nat.cast_one, mul_one]
  exact le_self_add

private theorem v3'_ne_bot : (v3' : Label.{u}) ≠ ⊥ := gridPoint_ne_bot 3 1

/-- The key identity at the cell `18`: under `VisibilityReplaceFixedOfLT A G`,
`min (vr 3 1 A) G = min A G`. -/
theorem min_visibilityReplace_three_one {A G : Label.{u}} (hG : IsSelfVisible 3 G)
    (hc : VisibilityReplaceFixedOfLT A G) : min (visibilityReplace 3 1 A) G = min A G := by
  rcases lt_or_ge A G with hlt | hle
  · rw [hc hlt]
  · rw [min_eq_right hle, min_eq_right]
    calc G = visibilityReplace 3 1 G := (hG.visibilityReplace_eq 1).symm
      _ ≤ visibilityReplace 3 1 A := monotone_visibilityReplace (by omega) hle

/-- **`labelling A F G` is lawful in `TL`** when `A`, `F`, `G` are self-visible at `1`, `2`, `3`,
`G ≤ F` and `VisibilityReplaceFixedOfLT A G`. -/
theorem isLawful_labelling {A F G : Label.{u}} (hA : IsSelfVisible 1 A) (hF : IsSelfVisible 2 F)
    (hG : IsSelfVisible 3 G) (hGF : G ≤ F) (hc : VisibilityReplaceFixedOfLT A G) :
    rowsL.IsLawful (labelling A F G) where
  orderly d := isSelfVisible_labelling hA hF hG d
  locality s := by
    by_cases hs : live s = true
    · rcases live_grade s hs with hs1 | hs2 | hs3
      · have hs18 : s ≠ 18 := by rintro rfl; exact absurd hs1 (by decide)
        refine ⟨constStepSuppressor 1 A, topShifter,
          isWitness_topShifter (antitone_constStepSuppressor _ _)
            (isSelfVisible_constStepSuppressor hA),
          fun d ↦ ?_⟩
        have hds : cells.gradedIndex d.1 ≤ cells.gradedIndex s := d.2
        -- Unfold the restriction of `labelling A F G` and the row of `s` in `rowsL`.
        change min (labelling A F G d.1) (labelling A F G s) =
          min (topShifter (if live s = true ∧ live d.1 = true then
            (if s = 18 then (if cellGrade d.1 = 1 then v1 else v3')
              else if cellGrade s = 3 then v3 else if cellGrade d.1 = 1 then v1 else v2) else ⊥))
            (constStepSuppressor 1 A (cellGrade d.1))
        by_cases hd : live d.1 = true
        · have hd1 : cellGrade d.1 = 1 := by
            rcases live_le_live s d.1 hs hd hds with h | ⟨_, h⟩ | h <;> omega
          rw [ite_eq_left ⟨hs, hd⟩, ite_eq_right hs18, ite_eq_right (by omega : ¬ cellGrade s = 3),
            ite_eq_left hd1, topShifter, ite_eq_right (gridPoint_ne_bot 1 0),
            constStepSuppressor, ite_eq_left hd1.le, min_top_left]
          simp [labelling, hs, hd, hd1, hs1]
        · have : labelling A F G d.1 = ⊥ := by simp [labelling, hd]
          rw [this, ite_eq_right (fun h ↦ hd h.2), topShifter, ite_eq_left rfl]
          simp
      · have hs18 : s ≠ 18 := by rintro rfl; exact absurd hs2 (by decide)
        refine ⟨constStepSuppressor 2 F, stripShifter A, isWitness_stripShifter hF, fun d ↦ ?_⟩
        have hds : cells.gradedIndex d.1 ≤ cells.gradedIndex s := d.2
        -- Unfold the restriction of `labelling A F G` and the row of `s` in `rowsL`.
        change min (labelling A F G d.1) (labelling A F G s) =
          min (stripShifter A (if live s = true ∧ live d.1 = true then
            (if s = 18 then (if cellGrade d.1 = 1 then v1 else v3')
              else if cellGrade s = 3 then v3 else if cellGrade d.1 = 1 then v1 else v2) else ⊥))
            (constStepSuppressor 2 F (cellGrade d.1))
        have hlabs : labelling A F G s = F := by simp [labelling, hs, hs2]
        rw [hlabs]
        by_cases hd : live d.1 = true
        · rw [ite_eq_left ⟨hs, hd⟩, ite_eq_right hs18, ite_eq_right (by omega : ¬ cellGrade s = 3)]
          rcases live_le_live s d.1 hs hd hds with h | ⟨h1, _⟩ | h
          · have hd2 : cellGrade d.1 = 2 := h.trans hs2
            rw [ite_eq_right (by omega), stripShifter_v2, constStepSuppressor,
              ite_eq_left hd2.le, min_top_left]
            simp [labelling, hd, hd2]
          · rw [ite_eq_left h1, stripShifter_v1 hA, constStepSuppressor, ite_eq_left (by omega)]
            simp [labelling, hd, h1]
          · omega
        · have : labelling A F G d.1 = ⊥ := by simp [labelling, hd]
          rw [this, ite_eq_right (fun h ↦ hd h.2), stripShifter_bot]
          simp
      · have hlabs : labelling A F G s = G := by simp [labelling, hs, hs3]
        rcases grade_three_cases s hs hs3 with rfl | rfl
        · -- The cell `16`: only itself is live below it.
          refine ⟨constStepSuppressor 3 G, topShifter,
            isWitness_topShifter (antitone_constStepSuppressor _ _)
              (isSelfVisible_constStepSuppressor hG),
            fun d ↦ ?_⟩
          -- Unfold the restriction of `labelling A F G` and the row of the cell `16` in `rowsL`.
          change min (labelling A F G d.1) (labelling A F G 16) =
            min (topShifter (if live 16 = true ∧ live d.1 = true then
              (if (16 : Fin 19) = 18 then (if cellGrade d.1 = 1 then v1 else v3')
                else if cellGrade 16 = 3 then v3 else if cellGrade d.1 = 1 then v1 else v2)
                else ⊥))
              (constStepSuppressor 3 G (cellGrade d.1))
          rw [hlabs]
          by_cases hd : live d.1 = true
          · obtain h16 := eq_sixteen_of_le d.1 hd d.2
            rw [ite_eq_left ⟨hs, hd⟩, ite_eq_right (by decide), ite_eq_left hs3, topShifter,
              ite_eq_right (gridPoint_ne_bot 3 0), constStepSuppressor,
              ite_eq_left (grade_le_three d.1), min_top_left, h16, hlabs, min_self]
          · have : labelling A F G d.1 = ⊥ := by simp [labelling, hd]
            rw [this, ite_eq_right (fun h ↦ hd h.2), topShifter, ite_eq_left rfl]
            simp
        · -- The cell `18`: the strip shifter at the grade `3`.
          refine ⟨constStepSuppressor 3 G, strip3 A, isWitness_strip3 hG, fun d ↦ ?_⟩
          -- Unfold the restriction of `labelling A F G` and the row of the cell `18` in `rowsL`.
          change min (labelling A F G d.1) (labelling A F G 18) =
            min (strip3 A (if live 18 = true ∧ live d.1 = true then
              (if (18 : Fin 19) = 18 then (if cellGrade d.1 = 1 then v1 else v3')
                else if cellGrade 18 = 3 then v3 else if cellGrade d.1 = 1 then v1 else v2)
                else ⊥))
              (constStepSuppressor 3 G (cellGrade d.1))
          rw [hlabs]
          by_cases hd : live d.1 = true
          · rw [ite_eq_left ⟨hs, hd⟩, ite_eq_left rfl, constStepSuppressor,
              ite_eq_left (grade_le_three d.1)]
            rcases live_grade d.1 hd with h1 | h2 | h3
            · rw [ite_eq_left h1, v1_eq, strip3_natCast, labelling_one hd h1]
              exact (min_visibilityReplace_three_one hG hc).symm
            · rw [ite_eq_right (by omega), strip3_of_not_lt v3'_ne_bot v3'_not_lt, min_top_left,
                labelling_two hd h2]
              exact min_eq_right hGF
            · rw [ite_eq_right (by omega), strip3_of_not_lt v3'_ne_bot v3'_not_lt, min_top_left,
                labelling_three hd h3, min_self]
          · have : labelling A F G d.1 = ⊥ := by simp [labelling, hd]
            rw [this, ite_eq_right (fun h ↦ hd h.2), strip3_bot]
            simp
    · have : labelling A F G s = ⊥ := by simp [labelling, hs]
      simp only [this, min_bot_right]
      exact TransformsTo.bot _ _
  availability s t hst hg := by
    refine ⟨t, rfl, ?_⟩
    by_cases hs : live s = true
    · have ht := live_up s t hs hst hg
      have hg' : cellGrade s = cellGrade t := hg
      simp [labelling, hs, ht, hg']
    · simp [labelling, hs]

/-! ### The lawful labellings below a pair -/

private theorem row18_three : (rowsL.{u}.row 18 ⟨3, le_eighteen 3⟩) = v1 := by
  simp [rowsL, live, cellGrade]

private theorem row18_eighteen :
    (rowsL.{u}.row 18 ⟨18, cells.mem_below_gradedIndex 18⟩) = v3' := by
  have hg : ¬ cellGrade 18 = 1 := by decide
  simp [rowsL, live, hg]

private theorem visibilityReplace_three_one_v1 : visibilityReplace 3 1 (v1 : Label.{u}) = v1 := by
  rw [v1_eq, Label.visibilityReplace_natCast]; simp

/-- **Necessity of `VisibilityReplaceFixedOfLT`**: locality at the cell `18` forces
`x 3 < x 18 → vr 3 1 (x 3) = x 3`. -/
private theorem visibilityReplaceFixedOfLT_of_transformsTo {x : Fin 19 → Label.{u}}
    (hT : TransformsTo (fun d : cells.below (cells.gradedIndex 18) ↦ cells.grade d.1)
      (rowsL.row 18) fun d ↦ min (x d.1) (x 18)) : VisibilityReplaceFixedOfLT (x 3) (x 18) := by
  intro hlt
  obtain ⟨g, σ, hw, heq⟩ := hT
  have h3 := heq ⟨3, le_eighteen 3⟩
  have h18 := heq ⟨18, cells.mem_below_gradedIndex 18⟩
  dsimp only at h3 h18
  rw [row18_three] at h3
  rw [row18_eighteen, min_self] at h18
  -- Read the grades of the cells `3` and `18`: `1` and `3`.
  change min (x 3) (x 18) = min (σ v1) (g 1) at h3
  change x 18 = min (σ v3') (g 3) at h18
  have hg3 : x 18 ≤ g 3 := h18 ▸ min_le_right _ _
  have hg1 : g 3 ≤ g 1 := hw.antitone (by omega)
  rw [min_eq_left hlt.le] at h3
  have hσ : σ v1 = x 3 := by
    rcases le_total (σ v1) (g 1) with h | h
    · rw [min_eq_left h] at h3; exact h3.symm
    · rw [min_eq_right h] at h3
      exact absurd (h3 ▸ hlt.trans_le (hg3.trans hg1)) (lt_irrefl _)
  have hguard : σ v1 ≤ g 3 := hσ ▸ (hlt.le.trans hg3)
  have := hw.visibilityReplace_comm v1 3 hguard 1 (by omega)
  rw [visibilityReplace_three_one_v1, hσ] at this
  exact this.symm

/-- **The lawful labellings below a pair** are the restrictions of the labellings
`labelling A F G` with `A`, `F`, `G` self-visible at `1`, `2`, `3`, `G ≤ F` and
`VisibilityReplaceFixedOfLT A G`. -/
theorem isLawfulBelow_iff {Y : Finset (Fin 4) × ℕ} {x : Fin 19 → Label.{u}} :
    rowsL.IsLawfulBelow Y (fun d ↦ x d) ↔ ∃ A F G : Label.{u}, IsSelfVisible 1 A ∧
      IsSelfVisible 2 F ∧ IsSelfVisible 3 G ∧ G ≤ F ∧ VisibilityReplaceFixedOfLT A G ∧
      ∀ d ∈ cells.below Y, x d = labelling A F G d := by
  classical
  constructor
  · intro hx
    obtain ⟨ho, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hx
    have hdead : ∀ d ∈ cells.below Y, live d = false → x d = ⊥ := by
      intro d hd hdl
      have := (hl d hd).eq_bot (d := ⟨d, cells.mem_below_gradedIndex d⟩)
        (by simp [rowsL, hdl])
      simpa using this
    have hloc : ∀ s ∈ cells.below Y, ∀ d, live s = true → live d = true →
        cellGrade s = 1 → cells.gradedIndex d ≤ cells.gradedIndex s → x s ≤ x d := by
      intro s hs d hsl hdl hs1 hds
      have hd1 : cellGrade d = 1 := by
        rcases live_le_live s d hsl hdl hds with h | ⟨_, h⟩ | h <;> omega
      have hs18 : s ≠ 18 := by rintro rfl; exact absurd hs1 (by decide)
      have := (hl s hs).le_of_le (d := ⟨s, cells.mem_below_gradedIndex s⟩) (d' := ⟨d, hds⟩)
        (by simp [rowsL, hsl, hdl, hd1, hs1, hs18]) hds.2
      simp only [min_self] at this
      exact this.trans (min_le_left _ _)
    have havail : ∀ s t, t ∈ cells.below Y → cellScope s ⊆ cellScope t →
        cellGrade s = cellGrade t → x s ≤ x t := by
      intro s t ht hst hg
      obtain ⟨u, hu, hle⟩ := ha s t ht hst hg
      rwa [gradedIndex_injective hu] at hle
    -- Locality at the cell `18`: the live cells of grade `2` and `3` carry at least its label.
    have h18 : (18 : Fin 19) ∈ cells.below Y → ∀ d, live d = true → 2 ≤ cellGrade d →
        x 18 ≤ x d := by
      intro h18 d hdl hd2
      have hl18 : live 18 = true := rfl
      have hd1 : cellGrade d ≠ 1 := by omega
      have hg18 : ¬ cellGrade 18 = 1 := by decide
      have := (hl 18 h18).le_of_le (d := ⟨18, cells.mem_below_gradedIndex 18⟩)
        (d' := ⟨d, le_eighteen d⟩) (by simp [rowsL, hdl, hl18, hd1, hg18]) (grade_le_three d)
      simp only [min_self] at this
      exact this.trans (min_le_left _ _)
    have h1618 : (18 : Fin 19) ∈ cells.below Y → x 16 = x 18 := fun h18m ↦
      le_antisymm (havail 16 18 h18m (by decide +kernel) rfl) (h18 h18m 16 rfl (by decide))
    set A : Label.{u} := if (3 : Fin 19) ∈ cells.below Y then x 3 else ⊤ with hA_def
    set F : Label.{u} := if (15 : Fin 19) ∈ cells.below Y then x 15 else ⊤ with hF_def
    set G : Label.{u} := if (16 : Fin 19) ∈ cells.below Y then x 16 else ⊥ with hG_def
    have hA : IsSelfVisible 1 A := by
      rw [hA_def]; split_ifs with h3
      · exact ho 3 h3
      · exact isSelfVisible_top 1
    have hF : IsSelfVisible 2 F := by
      rw [hF_def]; split_ifs with h15
      · exact ho 15 h15
      · exact isSelfVisible_top 2
    have hG : IsSelfVisible 3 G := by
      rw [hG_def]; split_ifs with h16
      · exact ho 16 h16
      · exact isSelfVisible_bot 3
    have hGF : G ≤ F := by
      rw [hG_def, hF_def]
      split_ifs with h16 h15
      · have h18m := eighteen_mem_below h16 (.inr h15)
        rw [h1618 h18m]; exact h18 h18m 15 rfl (by decide)
      · exact le_top
      · exact bot_le
      · exact bot_le
    have hc : VisibilityReplaceFixedOfLT A G := by
      rw [hG_def, hA_def]
      split_ifs with h3 h16 h16
      · have h18m := eighteen_mem_below h16 (.inl h3)
        rw [h1618 h18m]
        exact visibilityReplaceFixedOfLT_of_transformsTo (hl 18 h18m)
      · exact fun h ↦ absurd h (not_lt.mpr bot_le)
      · exact fun h ↦ absurd h (not_lt.mpr le_top)
      · exact fun h ↦ absurd h (not_lt.mpr bot_le)
    refine ⟨A, F, G, hA, hF, hG, hGF, hc, fun d hd ↦ ?_⟩
    rcases live_cases d with hdl | ⟨hdl, hg⟩ | ⟨hdl, hg⟩ | ⟨hdl, hg⟩
    · rw [labelling_dead hdl, hdead d hd hdl]
    · have h3 : (3 : Fin 19) ∈ cells.below Y :=
        mem_below_of_le hd (three_le_of_grade_one d hdl hg)
      rw [labelling_one hdl hg, hA_def, ite_eq_left h3]
      refine le_antisymm (hloc d hd 3 hdl rfl hg (three_le_of_grade_one d hdl hg)) ?_
      exact havail 3 d hd (three_le_of_grade_one d hdl hg).1 (hg ▸ rfl)
    · obtain rfl := eq_fifteen_of_grade_two d hdl hg
      rw [labelling_two hdl hg, hF_def, ite_eq_left hd]
    · have h16 : (16 : Fin 19) ∈ cells.below Y :=
        mem_below_of_le hd (sixteen_le_of_grade_three d hdl hg)
      rw [labelling_three hdl hg, hG_def, ite_eq_left h16]
      rcases grade_three_cases d hdl hg with rfl | rfl
      · rfl
      · exact (h1618 hd).symm
  · rintro ⟨A, F, G, hA, hF, hG, hGF, hc, hx⟩
    have := (isLawful_labelling hA hF hG hGF hc).isLawfulBelow Y
    convert this using 1
    funext d
    exact hx d d.2

/-! ### Bountifulness -/

/-- The condition `VisibilityReplaceFixedOfLT` passes to the lifted parameters. -/
private theorem visibilityReplaceFixedOfLT_lift {Ap Aq Gp Gq c : Label.{u}} {P3 P16 b : Prop}
    [Decidable P3] [Decidable P16] [Decidable b] (hcp : VisibilityReplaceFixedOfLT Ap Gp)
    (hcq : VisibilityReplaceFixedOfLT Aq Gq)
    (h3 : P3 → min Aq c = min Ap c) (h16 : P16 → min Gq c = min Gp c) :
    VisibilityReplaceFixedOfLT (if P3 then Ap else if Aq < c then Aq else ⊤)
      (if P16 then Gp else if Gq < c then Gq else if b then c else ⊥) := by
  intro hlt
  by_cases hP3 : P3
  · rw [ite_eq_left hP3] at hlt ⊢
    by_cases hP16 : P16
    · rw [ite_eq_left hP16] at hlt; exact hcp hlt
    · rw [ite_eq_right hP16] at hlt
      by_cases hGq : Gq < c
      · rw [ite_eq_left hGq] at hlt
        have hAq : Aq = Ap := eq_of_min_eq_of_lt (h3 hP3).symm (hlt.trans hGq)
        rw [← hAq] at hlt ⊢; exact hcq hlt
      · rw [ite_eq_right hGq] at hlt
        by_cases hb : b
        · rw [ite_eq_left hb] at hlt
          have hAq : Aq = Ap := eq_of_min_eq_of_lt (h3 hP3).symm hlt
          rw [← hAq] at hlt ⊢; exact hcq (hlt.trans_le (not_lt.mp hGq))
        · rw [ite_eq_right hb] at hlt; exact absurd hlt (not_lt.mpr bot_le)
  · rw [ite_eq_right hP3] at hlt ⊢
    by_cases hAq : Aq < c
    · rw [ite_eq_left hAq] at hlt ⊢
      by_cases hP16 : P16
      · rw [ite_eq_left hP16] at hlt
        apply hcq
        by_cases hGp : Gp < c
        · rw [eq_of_min_eq_of_lt (h16 hP16).symm hGp]; exact hlt
        · have hm := h16 hP16
          rw [min_eq_right (not_lt.mp hGp)] at hm
          exact hAq.trans_le (min_eq_right_iff.mp hm)
      · rw [ite_eq_right hP16] at hlt
        by_cases hGq : Gq < c
        · rw [ite_eq_left hGq] at hlt; exact hcq hlt
        · exact hcq (hAq.trans_le (not_lt.mp hGq))
    · rw [ite_eq_right hAq] at hlt; exact absurd hlt (not_lt.mpr le_top)

/-- **Every pair lifts capped to every larger pair** in `TL` (the lift of `T5`). -/
theorem cappedLift_all {X Y : Finset (Fin 4) × ℕ} (h : X ≤ Y) : rowsL.CappedLift.{u} h := by
  classical
  refine (Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨Ap, Fp, Gp, hAp, hFp, hGp, hGFp, hcp, hpx⟩ :=
    isLawfulBelow_iff.mp (Rows.isLawfulBelow_extendBot.mpr hp)
  obtain ⟨Aq, Fq, Gq, hAq, hFq, hGq, hGFq, hcq, hqx⟩ :=
    isLawfulBelow_iff.mp (Rows.isLawfulBelow_extendBot.mpr hq)
  have hpd (d : cells.below X) : p d = labelling Ap Fp Gp d := by
    rw [← hpx d d.2, Rows.extendBot_of_mem p d.2]
  have hqd (d : cells.below Y) : q d = labelling Aq Fq Gq d := by
    rw [← hqx d d.2, Rows.extendBot_of_mem q d.2]
  have hcap3 (h3 : (3 : Fin 19) ∈ cells.below X) : min Aq c = min Ap c := by
    have := hpq ⟨3, h3⟩
    rwa [hqd, hpd] at this
  have hcap15 (h15 : (15 : Fin 19) ∈ cells.below X) : min Fq c = min Fp c := by
    have := hpq ⟨15, h15⟩
    rwa [hqd, hpd] at this
  have hcap16 (h16 : (16 : Fin 19) ∈ cells.below X) : min Gq c = min Gp c := by
    have := hpq ⟨16, h16⟩
    rwa [hqd, hpd] at this
  set A' : Label.{u} := if (3 : Fin 19) ∈ cells.below X then Ap else (if Aq < c then Aq else ⊤)
    with hA'
  set F' : Label.{u} := if (15 : Fin 19) ∈ cells.below X then Fp else (if Fq < c then Fq else ⊤)
    with hF'
  set G' : Label.{u} := if (16 : Fin 19) ∈ cells.below X then Gp else
    (if Gq < c then Gq else if 3 ≤ Y.2 then c else ⊥) with hG'
  have hSA : IsSelfVisible 1 A' := by
    rw [hA']; split_ifs
    · exact hAp
    · exact hAq
    · exact isSelfVisible_top 1
  have hSF : IsSelfVisible 2 F' := by
    rw [hF']; split_ifs
    · exact hFp
    · exact hFq
    · exact isSelfVisible_top 2
  have hSG : IsSelfVisible 3 G' := by
    rw [hG']; split_ifs with _ _ h3
    · exact hGp
    · exact hGq
    · exact hc.mono h3
    · exact isSelfVisible_bot 3
  have hGF' : G' ≤ F' := lift_le hGFp hGFq hcap15 hcap16
  have hc' : VisibilityReplaceFixedOfLT A' G' :=
    visibilityReplaceFixedOfLT_lift hcp hcq hcap3 hcap16
  refine ⟨fun d ↦ labelling A' F' G' d,
    isLawfulBelow_iff.mpr ⟨A', F', G', hSA, hSF, hSG, hGF', hc', fun _ _ ↦ rfl⟩,
    fun d ↦ ?_, fun d ↦ ?_⟩
  · rw [hqd]
    -- Beta-reduce the lifted labelling at `d`.
    change min (labelling A' F' G' d.1) c = min (labelling Aq Fq Gq d.1) c
    rcases live_cases d.1 with hdl | ⟨hdl, hg⟩ | ⟨hdl, hg⟩ | ⟨hdl, hg⟩
    · rw [labelling_dead hdl, labelling_dead hdl]
    · rw [labelling_one hdl hg, labelling_one hdl hg, hA']
      split_ifs with h3 hlt
      · exact (hcap3 h3).symm
      · rfl
      · rw [min_top_left, min_eq_right (not_lt.mp hlt)]
    · rw [labelling_two hdl hg, labelling_two hdl hg, hF']
      split_ifs with h15 hlt
      · exact (hcap15 h15).symm
      · rfl
      · rw [min_top_left, min_eq_right (not_lt.mp hlt)]
    · have hY3 : 3 ≤ Y.2 := by
        have h2 := d.2.2
        -- The grade of `d` in `cells` is `cellGrade d`, at most `Y.2` since `d` is below `Y`.
        change cellGrade d.1 ≤ Y.2 at h2
        omega
      rw [labelling_three hdl hg, labelling_three hdl hg, hG']
      split_ifs with h16 hlt
      · exact (hcap16 h16).symm
      · rfl
      · rw [min_self, min_eq_right (not_lt.mp hlt)]
  · rw [hpd]
    -- Beta-reduce the lifted labelling at the inclusion of `d` into the cells below `Y`.
    change labelling A' F' G' d.1 = labelling Ap Fp Gp d.1
    rcases live_cases d.1 with hdl | ⟨hdl, hg⟩ | ⟨hdl, hg⟩ | ⟨hdl, hg⟩
    · rw [labelling_dead hdl, labelling_dead hdl]
    · have h3 : (3 : Fin 19) ∈ cells.below X :=
        mem_below_of_le d.2 (three_le_of_grade_one d.1 hdl hg)
      rw [labelling_one hdl hg, labelling_one hdl hg, hA', ite_eq_left h3]
    · have h15 : (15 : Fin 19) ∈ cells.below X := by
        rw [← eq_fifteen_of_grade_two d.1 hdl hg]; exact d.2
      rw [labelling_two hdl hg, labelling_two hdl hg, hF', ite_eq_left h15]
    · have h16 : (16 : Fin 19) ∈ cells.below X :=
        mem_below_of_le d.2 (sixteen_le_of_grade_three d.1 hdl hg)
      rw [labelling_three hdl hg, labelling_three hdl hg, hG', ite_eq_left h16]

theorem isBountiful_rowsL : rowsL.{u}.IsBountiful := fun _ _ _ _ h ↦ cappedLift_all h

/-! ### Legality -/

theorem isConsistent_rowsL : rowsL.{u}.IsConsistent := by
  intro s
  have hv3 (k : ℕ) (hk : k ≤ 3) : IsSelfVisible k (v3 : Label.{u}) :=
    (isSelfVisible_gridPoint 3 0).mono hk
  have hv3' (k : ℕ) (hk : k ≤ 3) : IsSelfVisible k (v3' : Label.{u}) :=
    (isSelfVisible_gridPoint 3 1).mono hk
  set As : Label.{u} := if live s = true then
    (if s = 18 then v1 else if cellGrade s = 3 then v3 else v1) else ⊥ with hAs
  set Fs : Label.{u} := if live s = true then
    (if s = 18 then v3' else if cellGrade s = 3 then v3 else v2) else ⊥ with hFs
  set Gs : Label.{u} := if live s = true ∧ cellGrade s = 3 then
    (if s = 18 then v3' else v3) else ⊥ with hGs
  have hA : IsSelfVisible 1 As := by
    rw [hAs]; split_ifs
    · exact isSelfVisible_gridPoint 1 0
    · exact hv3 1 (by omega)
    · exact isSelfVisible_gridPoint 1 0
    · exact isSelfVisible_bot 1
  have hF : IsSelfVisible 2 Fs := by
    rw [hFs]; split_ifs
    · exact hv3' 2 (by omega)
    · exact hv3 2 (by omega)
    · exact isSelfVisible_gridPoint 2 1
    · exact isSelfVisible_bot 2
  have hG : IsSelfVisible 3 Gs := by
    rw [hGs]; split_ifs
    · exact hv3' 3 le_rfl
    · exact hv3 3 le_rfl
    · exact isSelfVisible_bot 3
  have hl18 : live 18 = true := rfl
  have hg18 : cellGrade 18 = 3 := rfl
  have hGF : Gs ≤ Fs := by
    rw [hGs, hFs]
    by_cases h18 : s = 18
    · subst h18; simp [hl18, hg18]
    · by_cases hs : live s = true <;> by_cases hs3 : cellGrade s = 3 <;> simp [hs, hs3, h18]
  have hc : VisibilityReplaceFixedOfLT As Gs := by
    intro hlt
    rw [hGs, hAs] at hlt; rw [hAs]
    by_cases h18 : s = 18
    · subst h18
      rw [ite_eq_left hl18, ite_eq_left (rfl : (18 : Fin 19) = 18)]
      exact visibilityReplace_three_one_v1
    · by_cases hs : live s = true <;> by_cases hs3 : cellGrade s = 3 <;>
        simp [hs, hs3, h18] at hlt ⊢
  have := (isLawfulBelow_iff (Y := cells.gradedIndex s)
    (x := fun d ↦ if live s = true ∧ live d = true then
      (if s = 18 then (if cellGrade d = 1 then (v1 : Label.{u}) else v3')
        else if cellGrade s = 3 then v3 else if cellGrade d = 1 then v1 else v2)
      else ⊥)).mpr ⟨As, Fs, Gs, hA, hF, hG, hGF, hc, fun d hd ↦ ?_⟩
  · exact this
  · have hds : cellGrade d ≤ cellGrade s := hd.2
    have hs3' := grade_le_three s
    rcases live_cases d with hdl | ⟨hdl, hg⟩ | ⟨hdl, hg⟩ | ⟨hdl, hg⟩
    · simp [labelling_dead hdl, hdl]
    · rw [labelling_one hdl hg, hAs]
      by_cases hs : live s = true <;> by_cases hs3 : cellGrade s = 3 <;>
        by_cases h18 : s = 18 <;> simp [hs, hdl, hg, hs3, h18]
    · rw [labelling_two hdl hg, hFs]
      by_cases hs : live s = true <;> by_cases hs3 : cellGrade s = 3 <;>
        by_cases h18 : s = 18 <;> simp [hs, hdl, hg, hs3, h18]
    · have hs3 : cellGrade s = 3 := by omega
      rw [labelling_three hdl hg, hGs]
      by_cases hs : live s = true <;> by_cases h18 : s = 18 <;>
        simp [hs, hdl, hs3, hg, h18, hl18, hg18]

theorem isWellFormed_SL : SL.{u}.IsWellFormed where
  ground_eq := rfl
  isWellFormed := ⟨inferInstance, Geometry.isPlan_intervalPlan univ, fun d ↦ by
    simp only [mem_gradedFaces]
    revert d; decide +kernel⟩

theorem isCoded_SL : SL.{u}.IsCoded := by
  intro s t
  dsimp only [SL, rowsL]
  split_ifs
  · exact gridPoint_lt_omega0_sq 1 0
  · exact gridPoint_lt_omega0_sq 3 1
  · exact gridPoint_lt_omega0_sq 3 0
  · exact gridPoint_lt_omega0_sq 1 0
  · exact gridPoint_lt_omega0_sq 2 1
  · exact WithBot.bot_lt_coe _

theorem isLegalBelowFullGrade_SL : SL.{u}.IsLegalBelowFullGrade where
  isWellFormed := isWellFormed_SL
  isCoded := isCoded_SL
  isConsistent := isConsistent_rowsL
  isBountiful := isBountiful_rowsL
  grade_lt d := (by decide : ∀ d : Fin 19, cellGrade d < 4) d
  exists_gradedIndex_eq X hX hX4 := by
    obtain ⟨d, hd1, hd2⟩ := complete_below X.1 hX.1 X.2 hX4 hX.2.1 hX.2.2
    exact ⟨d, Prod.ext hd1 hd2⟩

/-- The stage type of `SL` with every label `⊥`. -/
noncomputable def TL₀ (α : Ordinal.{u}) : StageType.{u} α 4 where
  toScheme := SL
  label _ := ⊥
  isWellFormed := isWellFormed_SL
  isCoded := isCoded_SL
  isLawful := Rows.isLawful_const_bot
  atStage _ := atStage_bot

/-- **The left type** `TL`: `SL` with the apex added. -/
noncomputable def TL (α : Ordinal.{u}) : StageType.{u} α 4 :=
  (TL₀ α).addApex isLegalBelowFullGrade_SL (by omega)

/-- **`TL` is legal**, at every stage. -/
theorem isLegal_TL (α : Ordinal.{u}) : (TL α).IsLegal :=
  StageType.isLegal_addApex _ _

/-! ### The face of `TL` is the face of `T5` -/

section Face

variable {α : Ordinal.{u}}

theorem face_mem_TL : univ.map (Coatom.face 3) ∈ (TL α).toCellScheme.faces := by
  -- The faces of `TL` are those of the interval plan on four points.
  change univ.map (Coatom.face 3) ∈ Geometry.intervalPlan univ
  decide +kernel

private theorem rowsL_eq_rows_of_ne {s : Fin 19} (hs : s ≠ 18) :
    rowsL.{u}.row s = CaseSplitCounterexample.rows.row s := by
  funext t
  simp [rowsL, CaseSplitCounterexample.rows, hs]

/-- The cells visible on the face `{0, 1, 2}` are old and are not the cell `18`. -/
private theorem visible_cases (s : Fin (SL.{u}.card + 1))
    (hs : (Scheme.appendFullCellScheme SL.{u} 4).scope s ⊆ univ.map (Coatom.face 3)) :
    ∃ hl : s ≠ Fin.last _, ((s.castPred hl : Fin SL.{u}.card) : ℕ) ≠ 18 := by
  induction s using Fin.lastCases with
  | last =>
    rw [Scheme.appendFullCellScheme_scope_last] at hs
    exact absurd hs (by decide)
  | cast d =>
    refine ⟨Fin.castSucc_ne_last d, ?_⟩
    rw [Fin.castPred_castSucc]
    rw [Scheme.appendFullCellScheme_scope_castSucc] at hs
    have key : ∀ e : Fin 19, cellScope e ⊆ univ.map (Coatom.face 3) → (e : ℕ) ≠ 18 := by
      decide
    exact key d hs

theorem comap_TL_eq :
    (TL α).comap (Coatom.face 3) face_mem_TL = CaseSplitCounterexample.faceT5 α := by
  refine StageType.ext ?_ (fun i j h ↦ ?_)
  · -- Both sides are comaps of `SL` with the full cell appended, with the rows of `TL` and `T5`.
    change (Scheme.mk (SL.card + 1) (Scheme.appendFullCellScheme SL 4) _).comap (Coatom.face 3) =
      (Scheme.mk (SL.card + 1) (Scheme.appendFullCellScheme SL 4) _).comap (Coatom.face 3)
    refine Scheme.comap_mk_congr _ fun s hs ↦ ?_
    rw [Scheme.mem_visibleCells] at hs
    obtain ⟨hl, h18⟩ := visible_cases s (by simpa [← coe_subset] using hs)
    funext t
    have hl' : s ≠ Fin.last (TL₀ α).card := hl
    have hl'' : s ≠ Fin.last (CaseSplitCounterexample.T5₀ α).card := hl
    dsimp only
    split_ifs with h1 h2 h2
    · exact absurd h1 hl'
    · exact absurd h1 hl'
    · exact absurd h2 hl''
    exact congrFun (rowsL_eq_rows_of_ne (s := s.castPred hl) fun h ↦ h18 (congrArg Fin.val h)) _
  · obtain rfl : i = j := Fin.ext h
    rfl

end Face

/-! ### The asymmetric seed -/

section Seed

variable {α : Ordinal.{u}}

theorem restrictFace_TL (α : Ordinal.{u}) :
    StageType.restrictFace (Coatom.face 3) (TL α) = some (CaseSplitCounterexample.faceT5 α) := by
  rw [StageType.restrictFace_of_mem _ _ face_mem_TL, comap_TL_eq]

/-- **The asymmetric seed**: the left coatom type `TL` (the grade-`3` parameter coupled to `F`
only) and the right coatom type `T5` (coupled to `A` and `F`), over their common face. -/
noncomputable def seedL (α : Ordinal.{u}) : Seed.{u} α 3 :=
  Seed.ofCoatoms (isLegal_TL α) (CaseSplitCounterexample.isLegal_T5 α) (restrictFace_TL α)
    (CaseSplitCounterexample.restrictFace_T5 α)

theorem gradedIndex_TL_castSucc (d : Fin 19) :
    (TL α).toCellScheme.gradedIndex (Fin.castSucc d) = cells.gradedIndex d :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc SL 4 d

theorem isLawfulBelow_TL_iff {X : Finset (Fin 4) × ℕ}
    (hX : ¬ ((univ : Finset (Fin 4)), 4) ≤ X) {w : Fin (TL α).card → Label.{u}} :
    (TL α).rows.IsLawfulBelow X (fun d ↦ w d) ↔
      rowsL.IsLawfulBelow X (fun d ↦ w (Fin.castSucc d.1)) :=
  Scheme.isLawfulBelow_appendFullCell_iff (h := isLegalBelowFullGrade_SL.not_le) hX

private theorem isLawfulBelow_coatomL {A F G : Label.{u}} (hA : IsSelfVisible 1 A)
    (hF : IsSelfVisible 2 F) (hG : IsSelfVisible 3 G) (hGF : G ≤ F)
    (hc : VisibilityReplaceFixedOfLT A G)
    {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (TL α)) {Lf : Finset (Fin 5) × ℕ → Label.{u}}
    (hL : ∀ d, Lf (Prod.map (Finset.map f) id (cells.gradedIndex d)) = labelling A F G d) :
    Am.rows.IsLawfulBelow (univ.map f, 3) (fun d ↦ Lf (Am.toCellScheme.gradedIndex d)) := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (TL α).toScheme := congrArg StageType.toScheme he
  have hlaw : ∀ x : Fin (Am.toScheme.comap f).card → Label.{u},
      (∀ i, x i = Lf (Prod.map (Finset.map f) id
        ((Am.toScheme.comap f).toCellScheme.gradedIndex i))) →
      (Am.toScheme.comap f).rows.IsLawfulBelow ((univ : Finset (Fin 4)), 3) (fun i ↦ x i) := by
    rw [heq]
    intro x hx
    refine (isLawfulBelow_TL_iff (fun h ↦ absurd h.2 (by decide))).mpr ?_
    convert (isLawful_labelling hA hF hG hGF hc).isLawfulBelow ((univ : Finset (Fin 4)), 3)
      using 1
    funext d
    refine (hx _).trans ?_
    rw [gradedIndex_TL_castSucc]
    exact hL d.1
  exact (Scheme.isLawfulBelow_comap_cellMap_iff Am.toScheme f ((univ : Finset (Fin 4)), 3)
    fun d ↦ Lf (Am.toCellScheme.gradedIndex d)).mp
    (hlaw _ fun i ↦ congrArg Lf (Am.toScheme.map_comap_gradedIndex f i).symm)

/-- **`tripleLabelling` is lawful below both coatoms at the grade `3`** on a seed whose left type
is `TL` and right type `T5`: on the left under `G ≤ F_C` and `VisibilityReplaceFixedOfLT A_C G`;
on the right under `G ≤ A_D`, `G ≤ F_D`. -/
theorem isLawfulBelow_tripleLabelling {I : Seed.{u} α 3} (hIL : I.left = TL α)
    (hIR : I.right = CaseSplitCounterexample.T5 α) {AC FC AD FD G : Label.{u}}
    (hAC : IsSelfVisible 1 AC) (hFC : IsSelfVisible 2 FC) (hAD : IsSelfVisible 1 AD)
    (hFD : IsSelfVisible 2 FD) (hG : IsSelfVisible 3 G) (hGFC : G ≤ FC)
    (hcC : VisibilityReplaceFixedOfLT AC G)
    (hGAD : G ≤ AD) (hGFD : G ≤ FD) :
    I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last 4), 3)
        (fun d ↦ tripleLabelling AC FC AD FD G (I.amalgam.toCellScheme.gradedIndex d)) ∧
      I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 3)), 3)
        (fun d ↦ tripleLabelling AC FC AD FD G (I.amalgam.toCellScheme.gradedIndex d)) := by
  constructor
  · rw [← Coatom.univ_map_left]
    exact isLawfulBelow_coatomL hAC hFC hG hGFC hcC (hIL ▸ I.restrictFace_left)
      (tripleLabelling_left AC FC AD FD G)
  · rw [← Coatom.univ_map_right]
    exact CaseSplitCounterexample.isLawfulBelow_coatom hAD hFD hG hGAD hGFD
      (hIR ▸ I.restrictFace_right)
      (tripleLabelling_right AC FC AD FD G)

private theorem exists_cellL {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (TL α)) (d : Fin 19) :
    ∃ e : Fin Am.card, Am.toCellScheme.gradedIndex e =
      Prod.map (Finset.map f) id (cells.gradedIndex d) := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (TL α).toScheme := congrArg StageType.toScheme he
  obtain ⟨i, hi⟩ : ∃ i : Fin (Am.toScheme.comap f).card,
      (Am.toScheme.comap f).toCellScheme.gradedIndex i = cells.gradedIndex d := by
    rw [heq]; exact ⟨Fin.castSucc d, gradedIndex_TL_castSucc d⟩
  exact ⟨Am.toScheme.cellMap f i, by rw [← Am.toScheme.map_comap_gradedIndex f i, hi]⟩

private theorem right_eq_three : ∀ c : Fin 19,
    Prod.map (Finset.map (Coatom.right 3)) id (cells.gradedIndex c) =
      (({4} : Finset (Fin 5)), 1) → c = 3 := by decide +kernel

private theorem right_eq_sixteen : ∀ c : Fin 19,
    Prod.map (Finset.map (Coatom.right 3)) id (cells.gradedIndex c) =
      (({0, 1, 2} : Finset (Fin 5)), 3) → c = 16 := by decide +kernel

/-- **On the right coatom, the cell `({4}, 1)` carries at least the label of the cell of the
common face of grade `3`**: the coupling `G ≤ A` of `T5`. -/
theorem le_of_isLawfulBelow_right {I : Seed.{u} α 3}
    (hIR : I.right = CaseSplitCounterexample.T5 α) {w : Fin I.amalgam.card → Label.{u}}
    (hw : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 3)), 2 + 1)
      fun d ↦ w d)
    {d₂ g : Fin I.amalgam.card}
    (hd₂ : I.amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1))
    (hg : I.amalgam.toCellScheme.gradedIndex g = (({0, 1, 2} : Finset (Fin 5)), 3)) :
    w g ≤ w d₂ := by
  rw [← Coatom.univ_map_right] at hw
  obtain ⟨A, F, G, -, -, -, hGA, -, hall⟩ :=
    CaseSplitCounterexample.exists_labelling_of_comap (hIR ▸ I.restrictFace_right) (k := 2 + 1)
      (by omega) w hw
  have hmem2 : d₂ ∈ I.amalgam.toCellScheme.below (univ.map (Coatom.right 3), 2 + 1) := by
    -- Membership below a pair is comparison of graded indices.
    change I.amalgam.toCellScheme.gradedIndex d₂ ≤ _
    rw [hd₂, Coatom.univ_map_right]; decide +kernel
  have hmemg : g ∈ I.amalgam.toCellScheme.below (univ.map (Coatom.right 3), 2 + 1) := by
    -- Membership below a pair is comparison of graded indices.
    change I.amalgam.toCellScheme.gradedIndex g ≤ _
    rw [hg, Coatom.univ_map_right]; decide +kernel
  obtain ⟨c₂, hc₂, hw₂⟩ := hall d₂ hmem2
  obtain ⟨cg, hcg, hwg⟩ := hall g hmemg
  obtain rfl := right_eq_three c₂ (hc₂.symm.trans hd₂)
  obtain rfl := right_eq_sixteen cg (hcg.symm.trans hg)
  rw [hw₂, hwg]
  -- The matched cells of `T5` are its cells `16` (at `({0, 1, 2}, 3)`) and `3` (at `({4}, 1)`).
  change labelling A F G 16 ≤ labelling A F G 3
  rw [labelling_three rfl rfl, labelling_one rfl rfl]
  exact hGA

end Seed

/-! ### The refutation of `2FL∃(2)` -/

section Refutation

variable {α : Ordinal.{u}}

open TowerExamples (Q Q_ne_bot isSelfVisible_Q)

private theorem tripleLabelling_map {f : Label.{u} → Label.{u}} (hf : f ⊥ = ⊥)
    (AC FC AD FD G : Label.{u}) (X : Finset (Fin 5) × ℕ) :
    f (tripleLabelling AC FC AD FD G X) =
      tripleLabelling (f AC) (f FC) (f AD) (f FD) (f G) X := by
  unfold tripleLabelling
  generalize tripleKind X = c
  fin_cases c <;> simp [hf]

/-- The key of a grid point of the grade `2` at the grade `3`. -/
private theorem visibilityReplace_three_gridPoint_two (c : ℕ) :
    visibilityReplace 3 3 (gridPoint.{u} 2 c) = gridPoint 3 c := by
  rw [gridPoint, gridPoint, visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast]
  simp

private theorem gridPoint_three_lt_gridPoint_four {c B : ℕ} (h : c < B) :
    gridPoint.{u} 3 c < gridPoint 4 (B - 1) := by
  rw [gridPoint, gridPoint, WithBot.coe_lt_coe, WithTop.coe_lt_coe, ← not_le,
    omega0_mul_add_natCast_le_iff]
  rintro (h' | ⟨-, h'⟩)
  · exact absurd (Nat.cast_lt.mp h') (by omega)
  · exact absurd h' (by omega)

/-- **`2FL∃(2)` fails on every seed on five points whose left coatom type is `TL` and whose right
coatom type is `T5`.**

The proof follows the steps 1–5 of the module docstring, which are numbered in the proof.  In
step 2 the labelling of `T 2` is the extension `r₂` of `b₀` below `(univ, 2)` and
`tripleLabelling β₁ φ β₁ φ γ` on the old cells, with `φ` the value of `b₀` at the old live cells
of grade `2`, and `a` is the orbit code at `3` of its splice. -/
theorem not_twoFaceLiftExists_two_of {I : Seed.{u} α 3} (hIL : I.left = TL α)
    (hIR : I.right = CaseSplitCounterexample.T5 α) : ¬ I.TwoFaceLiftExists 2 := by
  classical
  intro H
  -- The cells.
  obtain ⟨d₁, hd₁⟩ : ∃ e : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex e = (({3} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := exists_cellL (hIL ▸ I.restrictFace_left) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sC, hsC⟩ : ∃ e : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex e = (({0, 1, 2, 3} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := exists_cellL (hIL ▸ I.restrictFace_left) 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨gE, hgE⟩ : ∃ e : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex e = (({0, 1, 2} : Finset (Fin 5)), 3) := by
    obtain ⟨e, he⟩ := exists_cellL (hIL ▸ I.restrictFace_left) 16
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨d₂, hd₂⟩ : ∃ e : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex e = (({4} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIR ▸ I.restrictFace_right) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  have hg₁ : I.amalgam.toCellScheme.grade d₁ = 1 := congrArg Prod.snd hd₁
  have hg₂ : I.amalgam.toCellScheme.grade d₂ = 1 := congrArg Prod.snd hd₂
  have hgs : I.amalgam.toCellScheme.grade sC = 2 := congrArg Prod.snd hsC
  have hgg : I.amalgam.toCellScheme.grade gE = 3 := congrArg Prod.snd hgE
  have hk₁ : tripleKind (({3} : Finset (Fin 5)), 1) = 1 := by decide
  have hk₂ : tripleKind (({4} : Finset (Fin 5)), 1) = 3 := by decide
  have hks : tripleKind (({0, 1, 2, 3} : Finset (Fin 5)), 2) = 2 := by decide
  have hkg : tripleKind (({0, 1, 2} : Finset (Fin 5)), 3) = 5 := by decide
  set x : Fin (3 + 2) := Fin.last (3 + 1) with hx_def
  set y : Fin (3 + 2) := Fin.castSucc (Fin.last 3) with hy_def
  have hx : x ∈ ({Fin.last (3 + 1), Fin.castSucc (Fin.last 3)} : Finset (Fin (3 + 2))) := by
    rw [hx_def]; exact mem_insert_self _ _
  have hy : y ∈ ({Fin.last (3 + 1), Fin.castSucc (Fin.last 3)} : Finset (Fin (3 + 2))) := by
    rw [hy_def]; exact mem_insert_of_mem (mem_singleton_self _)
  have hxy : x ≠ y := by decide
  have hd₁C : d₁ ∈ I.amalgam.toCellScheme.below (univ.erase x, 2 + 1) := by
    -- Membership below a pair is comparison of graded indices.
    change I.amalgam.toCellScheme.gradedIndex d₁ ≤ _; rw [hd₁]; decide +kernel
  have hd₂C : d₂ ∉ I.amalgam.toCellScheme.below (univ.erase x, 2 + 1) := by
    intro h
    have h' : I.amalgam.toCellScheme.gradedIndex d₂ ≤ (univ.erase x, 2 + 1) := h
    rw [hd₂] at h'; revert h'; decide +kernel
  have hsCC : sC ∈ I.amalgam.toCellScheme.below (univ.erase x, 2 + 1) := by
    -- Membership below a pair is comparison of graded indices.
    change I.amalgam.toCellScheme.gradedIndex sC ≤ _; rw [hsC]; decide +kernel
  have hgC : gE ∈ I.amalgam.toCellScheme.below (univ.erase x, 2 + 1) := by
    -- Membership below a pair is comparison of graded indices.
    change I.amalgam.toCellScheme.gradedIndex gE ≤ _; rw [hgE]; decide +kernel
  have hgD : gE ∈ I.amalgam.toCellScheme.below (univ.erase y, 2 + 1) := by
    -- Membership below a pair is comparison of graded indices.
    change I.amalgam.toCellScheme.gradedIndex gE ≤ _; rw [hgE]; decide +kernel
  -- 1. The catalogue entry `b₀` at the grade `2` and its strip.
  have hsv11 : IsSelfVisible 1 (Q.{u} 1 1) := isSelfVisible_Q.mpr le_rfl
  have hsv22 : IsSelfVisible 2 (Q.{u} 1 2) := isSelfVisible_Q.mpr le_rfl
  have hcondP : VisibilityReplaceFixedOfLT (Q.{u} 1 1) ⊥ := fun h ↦ absurd h (not_lt.mpr bot_le)
  set P : Fin I.amalgam.card → Label.{u} := fun d ↦
    tripleLabelling (Q 1 1) (Q 1 2) (Q 1 1) (Q 1 2) ⊥ (I.amalgam.toCellScheme.gradedIndex d)
    with hP
  obtain ⟨hPC, hPD⟩ := isLawfulBelow_tripleLabelling (I := I) hIL hIR hsv11 hsv22 hsv11 hsv22
    (isSelfVisible_bot 3) bot_le hcondP bot_le bot_le
  have hPC2 : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (3 + 1)), 2) fun d ↦ P d :=
    hPC.mono (X := (univ.erase (Fin.last 4), 2)) ⟨subset_rfl, by omega⟩
  have hPD2 : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 3)), 2)
      fun d ↦ P d :=
    hPD.mono (X := (univ.erase (Fin.castSucc (Fin.last 3)), 2)) ⟨subset_rfl, by omega⟩
  obtain ⟨t, hb₀, ht⟩ := Seed.exists_orbitCode_mem_catalogue_two I (w := P) hPC2 hPD2
  have hP₁ : P d₁ = Q 1 1 := by simp only [hP, tripleLabelling, hd₁, hk₁]; rfl
  set b₀ := orbitCode 2 t with hb₀_def
  set β₁ := orbitMap 2 t (Q 1 1) with hβ₁_def
  set φ := orbitMap 2 t (Q 1 2) with hφ_def
  have hb₀old (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 2) :
      b₀ (I.towerEmbed 1 d) =
        tripleLabelling β₁ φ β₁ φ ⊥ (I.amalgam.toCellScheme.gradedIndex d) := by
    rw [hb₀_def, orbitCode_apply, ht d hd, hP]
    dsimp only
    rw [tripleLabelling_map (f := orbitMap 2 t) orbitMap_bot, orbitMap_bot]
  have hb₀₁ : b₀ (I.towerEmbed 1 d₁) = β₁ := by
    rw [hb₀old d₁ (by omega), hd₁]; simp only [tripleLabelling, hk₁]; rfl
  have hb₀₂ : b₀ (I.towerEmbed 1 d₂) = β₁ := by
    rw [hb₀old d₂ (by omega), hd₂]; simp only [tripleLabelling, hk₂]; rfl
  have hb₀L := (Scheme.mem_catalogue.mp hb₀).1
  have hβ₁sv1 : IsSelfVisible 1 β₁ := by
    have := hb₀L.orderly (I.towerEmbed 1 d₁)
    rwa [Seed.grade_towerEmbed, hg₁, hb₀₁] at this
  have hφsv2 : IsSelfVisible 2 φ := by
    have := hb₀L.orderly (I.towerEmbed 1 sC)
    have hφs : tripleLabelling β₁ φ β₁ φ ⊥ (({0, 1, 2, 3} : Finset (Fin 5)), 2) = φ := by
      simp only [tripleLabelling, hks]; rfl
    rwa [Seed.grade_towerEmbed, hgs, hb₀old sC (by omega), hsC, hφs] at this
  have hβφ : β₁ ≤ φ := monotone_orbitMap 2 t (Q_le_Q (by omega))
  have hkey2 : IsOrbitKey 2 t (Q 1 1) := by
    have := isOrbitKey_of_not_isSelfVisible (k := 2) (w := t) (d := I.towerEmbed 1 d₁)
      (by rw [ht d₁ (by omega), hP₁, isSelfVisible_Q]; omega)
    rwa [ht d₁ (by omega), hP₁] at this
  set B := codeBlock 2 t (Q 1 1) with hB_def
  have hB : 1 ≤ B := by
    have hnat : ¬ (IsOrbitKey 2 t (Q 1 1) ∧ visibilityReplace 2 2 (Q.{u} 1 1) = gridPoint 2 0) := by
      rintro ⟨-, h⟩
      rw [Q, gridPoint, visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast,
        WithBot.coe_inj, WithTop.coe_inj] at h
      have := (omega0_mul_add_natCast_le_iff (a := ((1 : ℕ) : Ordinal.{u}))
        (b := ((0 : ℕ) : Ordinal.{u}))).mp h.le
      rcases this with h' | ⟨h', -⟩
      · exact absurd h' (by simp)
      · exact absurd h' (by simp)
    have h1 := le_codeBlock hnat
    have h2 := one_le_keyRank hkey2.isKey
    omega
  have hβ₁eq :
      β₁ = ((ω * (B : Ordinal.{u}) + ((1 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) := by
    rw [hβ₁_def, orbitMap_of_isOrbitKey hkey2, gridPoint, Q, moveToBlock_omega0_mul_add]
    rfl
  set h₂ := visibilityReplace 2 2 β₁ with hh₂_def
  have hh₂ : h₂ = gridPoint 2 B := visibilityReplace_orbitMap (Q_ne_bot 1 1)
  have hβ₁h₂ : β₁ < h₂ := by
    rw [hh₂, hβ₁eq, gridPoint, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
    exact add_lt_add_right (by exact_mod_cast (by omega : (1 : ℕ) < 2)) _
  -- The extension `r₂` of `b₀` through the layer at the grade `2`, at the cap `h₂`.
  obtain ⟨r₂, hr₂, hr₂b, hr₂cap⟩ : ∃ r : (I.tower 2).toCellScheme.below (univ, 2) → Label.{u},
      (I.tower 2).rows.IsLawfulBelow (univ, 2) r ∧
      (∀ d (hd : (I.tower 1).toCellScheme.grade d ≤ 2),
        r ⟨Fin.castAdd _ d, Scheme.castAdd_mem_below (hS := I.not_univ_succ_le_tower 1) hd⟩ =
          b₀ d) ∧
      ∀ x, min (r x) h₂ = min ((I.tower 1).fieldRow 2 b₀ x.1) h₂ :=
    Scheme.exists_extension_fieldLayer (S := I.tower 1) (k := 2)
    (hS := I.not_univ_succ_le_tower 1) (p := b₀) (hb₀L.isLawfulBelow _) hb₀ (h := h₂)
    (by rw [hh₂]; exact isSelfVisible_gridPoint 2 _)
    (by rw [hh₂]; exact bot_lt_iff_ne_bot.mpr (gridPoint_ne_bot 2 _))
    (.inl (by rw [hh₂]; exact isShort_gridPoint 2 _)) (fun _ _ ↦ rfl)
  -- 2. The labelling `p₃` of `T 2`: `r₂` below `(univ, 2)`, and `γ` at the live old cells of
  -- grade `3`.
  set γ : Label.{u} := gridPoint 4 (B - 1) with hγ_def
  have hγsv3 : IsSelfVisible 3 γ := (isSelfVisible_gridPoint 4 _).mono (by omega)
  have hγ0 : γ ≠ ⊥ := gridPoint_ne_bot 4 _
  have hγβ : γ < β₁ := by
    rw [hγ_def, hβ₁eq, gridPoint, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
    exact omega0_mul_add_natCast_lt (by exact_mod_cast (by omega : B - 1 < B)) _ _
  have hγφ : γ ≤ φ := hγβ.le.trans hβφ
  set L₃ : Fin I.amalgam.card → Label.{u} := fun d ↦
    tripleLabelling β₁ φ β₁ φ γ (I.amalgam.toCellScheme.gradedIndex d) with hL₃
  obtain ⟨hL₃C, hL₃D⟩ := isLawfulBelow_tripleLabelling (I := I) hIL hIR hβ₁sv1 hφsv2 hβ₁sv1
    hφsv2 hγsv3 hγφ (fun h ↦ absurd h (not_lt.mpr hγβ.le)) hγβ.le hγφ
  set W : Fin (I.tower 2).card → Label.{u} := Function.extend (I.towerEmbed 2) L₃ (fun _ ↦ ⊥)
    with hW
  have hWe (d : Fin I.amalgam.card) : W (I.towerEmbed 2 d) = L₃ d :=
    (I.towerEmbed 2).injective.extend_apply _ _ _
  set p₃ : Fin (I.tower 2).card → Label.{u} := fun e ↦
    if he : e ∈ (I.tower 2).toCellScheme.below (univ, 2) then r₂ ⟨e, he⟩ else W e with hp₃
  have hold2 (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 2) :
      r₂ ⟨I.towerEmbed 2 d, I.towerEmbed_mem_below hd⟩ = L₃ d := by
    refine (hr₂b (I.towerEmbed 1 d) (by rw [Seed.grade_towerEmbed]; exact hd)).trans ?_
    rw [hb₀old d hd, hL₃]
    exact tripleLabelling_eq_of_le_two hd _ _ _ _ _ _
  have hpW (z : Fin (3 + 2)) (e : Fin (I.tower 2).card)
      (he : e ∈ (I.tower 2).toCellScheme.below (univ.erase z, 2 + 1)) : p₃ e = W e := by
    obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed 2 e fun hu ↦
      Seed.ne_univ_erase z (univ_subset_iff.mp (hu.ge.trans he.1))
    rw [hp₃]
    dsimp only
    split_ifs with hu
    · have hd : I.amalgam.toCellScheme.grade d ≤ 2 := (I.grade_towerEmbed 2 d).symm.trans_le hu.2
      rw [hWe, ← hold2 d hd]
    · rfl
  have hWlaw (z : Fin (3 + 2)) (hL : I.amalgam.rows.IsLawfulBelow (univ.erase z, 2 + 1)
      fun d ↦ L₃ d) :
      (I.tower 2).rows.IsLawfulBelow (univ.erase z, 2 + 1) fun e ↦ p₃ e := by
    have hW' : (I.tower 2).rows.IsLawfulBelow (univ.erase z, 2 + 1) fun e ↦ W e := by
      rw [I.isLawfulBelow_tower_iff (Seed.ne_univ_erase z)]
      simpa only [hWe] using hL
    convert hW' using 1
    exact funext fun e ↦ hpW z e e.2
  have hp₃V : (I.tower 2).rows.IsLawfulBelow (univ, 2) fun e ↦ p₃ e := by
    convert hr₂ using 1
    funext e
    rw [hp₃]; exact dite_eq_left e.2
  have hp₃L : (I.tower 2).rows.IsLawfulBelow (univ, 2 + 1) fun e ↦ p₃ e :=
    Rows.IsLawfulBelow.glue₃ (U := (univ.erase x, 2 + 1)) (V := (univ, 2))
      (W := (univ.erase y, 2 + 1)) (hWlaw x hL₃C) hp₃V (hWlaw y hL₃D)
      (I.mem_below_cover_tower hx hy hxy)
  set t₃ := (I.tower 2).toCellScheme.splice 3 (fun _ ↦ ⊥) p₃ with ht₃_def
  set a := orbitCode 3 t₃ with ha_def
  have ha : a ∈ (I.tower 2).catalogue (2 + 1) := Scheme.orbitCode_splice_bot_mem_catalogue hp₃L
  have ht₃L : (I.tower 2).rows.IsLawful t₃ := Scheme.isLawful_splice_bot hp₃L
  have ht₃below (e : Fin (I.tower 2).card) (he : e ∈ (I.tower 2).toCellScheme.below (univ, 2)) :
      t₃ e = r₂ ⟨e, he⟩ := by
    rw [ht₃_def, CellScheme.splice_of_le (he.2.trans (by omega)), hp₃]
    exact dite_eq_left he
  have ht₃old (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 3) :
      t₃ (I.towerEmbed 2 d) = L₃ d := by
    rw [ht₃_def, CellScheme.splice_of_le (by rw [Seed.grade_towerEmbed]; exact hd), hp₃]
    dsimp only
    split_ifs with hu
    · exact hold2 d ((I.grade_towerEmbed 2 d).symm.trans_le hu.2)
    · exact hWe d
  -- The cap `h`: the code of `γ`.
  have ht₃g : t₃ (I.towerEmbed 2 gE) = γ := by
    rw [ht₃old gE (by omega), hL₃]; dsimp only; rw [hgE]; simp only [tripleLabelling, hkg]; rfl
  set h := orbitMap 3 t₃ γ with hh_def
  have hkeyγ : IsKey 3 t₃ γ := ⟨I.towerEmbed 2 gE, by rw [ht₃g]; exact hγ0, by rw [ht₃g]⟩
  have hhsv : IsSelfVisible 3 h := (isSelfVisible_orbitMap_iff hγ0).mpr (.inr hγsv3)
  have hhgrid : h = gridPoint 3 (codeBlock 3 t₃ γ) := by
    rw [← visibilityReplace_orbitMap hγ0]; exact hhsv.symm
  have hhs : IsShort 3 h := isShort_orbitMap _
  have hhbot : ⊥ < h := by
    rw [hhgrid]; exact bot_lt_iff_ne_bot.mpr (gridPoint_ne_bot 3 _)
  have hlow (z : Fin (I.tower 2).card) (hz : visibilityReplace 3 3 (t₃ z) < γ) : a z < h := by
    by_cases hz0 : t₃ z = ⊥
    · rw [ha_def, orbitCode_apply, hz0, orbitMap_bot]; exact hhbot
    have hcb := codeBlock_lt_codeBlock hz0 hkeyγ (by rwa [hγsv3])
    rw [ha_def, orbitCode_apply, hhgrid]
    exact (orbitMap_le_gridPoint _).trans_lt (gridPoint_lt_gridPoint.mpr hcb)
  -- The labels of `a` at the old cells.
  set A₃ := orbitMap 3 t₃ β₁ with hA₃_def
  set F₃ := orbitMap 3 t₃ φ with hF₃_def
  have haold (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 3) :
      a (I.towerEmbed 2 d) =
        tripleLabelling A₃ F₃ A₃ F₃ h (I.amalgam.toCellScheme.gradedIndex d) := by
    rw [ha_def, orbitCode_apply, ht₃old d hd, hL₃]
    exact tripleLabelling_map (f := orbitMap 3 t₃) orbitMap_bot _ _ _ _ _ _
  have hhA : h ≤ A₃ := monotone_orbitMap 3 t₃ hγβ.le
  have hAF : A₃ ≤ F₃ := monotone_orbitMap 3 t₃ hβφ
  have hA₃top : A₃ ≠ ⊤ := orbitMap_ne_top _
  have hA₃d₁ : a (I.towerEmbed 2 d₁) = A₃ := by
    rw [haold d₁ (by omega), hd₁]; simp only [tripleLabelling, hk₁]; rfl
  have hA₃sv : IsSelfVisible 1 A₃ := by
    have := (Scheme.mem_catalogue.mp ha).1.orderly (I.towerEmbed 2 d₁)
    rwa [Seed.grade_towerEmbed, hg₁, hA₃d₁] at this
  -- `A₃` has finite part `1`, so `VisibilityReplaceFixedOfLT A₃ ⊤`.
  have hL₃d₁ : L₃ d₁ = β₁ := by
    rw [hL₃]; dsimp only; rw [hd₁]; simp only [tripleLabelling, hk₁]; rfl
  have hkey3 : IsOrbitKey 3 t₃ β₁ := by
    have hns : ¬ IsSelfVisible 3 (t₃ (I.towerEmbed 2 d₁)) := by
      rw [ht₃old d₁ (by omega), hL₃d₁]
      intro hsv
      have h2 : IsSelfVisible 2 β₁ := hsv.mono (by omega)
      rw [hh₂_def] at hβ₁h₂
      exact absurd h2.symm hβ₁h₂.ne
    have := isOrbitKey_of_not_isSelfVisible hns
    rwa [ht₃old d₁ (by omega), hL₃d₁] at this
  have hA₃eq : A₃ = ((ω * ((codeBlock 3 t₃ β₁ : ℕ) : Ordinal.{u}) + ((1 : ℕ) : Ordinal.{u}) :
      Ordinal.{u}) : Label.{u}) := by
    rw [hA₃_def, orbitMap_of_isOrbitKey hkey3]
    conv_lhs => arg 2; rw [hβ₁eq]
    rw [gridPoint, moveToBlock_omega0_mul_add]
  have hcondA₃ : VisibilityReplaceFixedOfLT A₃ ⊤ := fun _ ↦ by
    rw [hA₃eq, visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast]
    simp
  -- 4. The prescription `w_C`.
  set wC : Fin I.amalgam.card → Label.{u} := fun d ↦
    tripleLabelling A₃ ⊤ ⊤ ⊤ ⊤ (I.amalgam.toCellScheme.gradedIndex d) with hwC_def
  have hwC : I.amalgam.rows.IsLawfulBelow (univ.erase x, 2 + 1) fun d ↦ wC d :=
    (isLawfulBelow_tripleLabelling (I := I) hIL hIR hA₃sv (isSelfVisible_top 2)
      (isSelfVisible_top 1) (isSelfVisible_top 2) (isSelfVisible_top 3) le_rfl hcondA₃ le_rfl
      le_rfl).1
  have hag : ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, 2 + 1),
      min (wC d) h = min (a (I.towerEmbed 2 d)) h := by
    intro d hd
    rw [haold d hd.2, hwC_def]
    dsimp only
    unfold tripleLabelling
    generalize tripleKind (I.amalgam.toCellScheme.gradedIndex d) = c
    fin_cases c <;> simp [min_eq_right hhA, min_eq_right (hhA.trans hAF)]
  -- 5. The existential two-face lift.
  obtain ⟨wD, hwD, hDE, -, r, hr, hrw, hra⟩ :=
    H x hx y hy hxy a ha h hhsv hhs hhbot wC hwC hag
  have hwDg : wD gE = ⊤ := by
    rw [hDE gE hgC hgD, hwC_def]; dsimp only; rw [hgE]; simp only [tripleLabelling, hkg]; rfl
  have hwD₂ : wD d₂ = ⊤ := top_le_iff.mp (hwDg ▸ le_of_isLawfulBelow_right hIR hwD hd₂ hgE)
  -- Availability at `sC`, labelled `⊤`: a new cell `u` at `(univ, 2)`.
  obtain ⟨-, hloc, havail⟩ := Rows.isLawfulBelow_iff_forall.mp (Rows.isLawfulBelow_extendBot.mpr hr)
  obtain ⟨t0, ht0⟩ := I.exists_gradedIndex_eq_univ_tower 1
  have hsCm : I.towerEmbed 2 sC ∈ (I.tower 2).toCellScheme.below (univ, 2) :=
    I.towerEmbed_mem_below (by omega)
  have hwsC : Rows.extendBot (univ, 2) r (I.towerEmbed 2 sC) = ⊤ := by
    rw [Rows.extendBot_of_mem r hsCm, hrw sC (by omega), ite_eq_left hsCC, hwC_def]
    dsimp only; rw [hsC]; simp only [tripleLabelling, hks]; rfl
  obtain ⟨u, hu, hle⟩ := havail (I.towerEmbed 2 sC) t0 ht0.le
    (by rw [show (I.tower 2).toCellScheme.scope t0 = univ from congrArg Prod.fst ht0]
        exact subset_univ _)
    (by rw [Seed.grade_towerEmbed, hgs]; exact (congrArg Prod.snd ht0).symm)
  have hu' : (I.tower 2).toCellScheme.gradedIndex u = (univ, 2) := hu.trans ht0
  have hum : u ∈ (I.tower 2).toCellScheme.below (univ, 2) := hu'.le
  have hRu : Rows.extendBot (univ, 2) r u = ⊤ := top_le_iff.mp (hwsC ▸ hle)
  have hru : r ⟨u, hum⟩ = ⊤ := (Rows.extendBot_of_mem r hum).symm.trans hRu
  have hau : h ≤ a u := by
    have := hra ⟨u, hum⟩
    rw [hru, min_top_left] at this
    exact min_eq_right_iff.mp this.symm
  -- 3. So the key of `t₃ u` is at least `γ`, and `r₂ u` is at least the strip cap `h₂`.
  have hkeyu : γ ≤ visibilityReplace 3 3 (t₃ u) :=
    not_lt.mp fun hlt ↦ absurd hau (not_le.mpr (hlow u hlt))
  obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq (S := I.tower 1) (k := 2)
    (hS := I.not_univ_succ_le_tower 1) (u := u) hu'
  have hcap := hr₂cap ⟨_, hum⟩
  rw [Scheme.fieldRow_natAdd] at hcap
  obtain ⟨hAHmem, hagree⟩ := agreementHeight_spec (bot_mem_grid _ _) b₀
    ((I.tower 1).catalogueEntry 2 i)
  have hh₂u : h₂ ≤ r₂ ⟨_, hum⟩ := by
    by_contra hlt
    rw [not_le] at hlt
    rw [min_eq_left hlt.le] at hcap
    set AH := agreementHeight ((I.tower 1).fieldGrid 2) b₀ ((I.tower 1).catalogueEntry 2 i)
      with hAH
    have hAHlt : AH < h₂ := by
      by_contra hge
      rw [not_lt] at hge
      rw [min_eq_right hge] at hcap
      exact absurd hcap hlt.ne
    rw [min_eq_left hAHlt.le] at hcap
    rw [ht₃below _ hum, hcap] at hkeyu
    rcases mem_grid.mp hAHmem with h0 | ⟨c, -, hc⟩
    · rw [h0, visibilityReplace_bot] at hkeyu
      exact absurd hkeyu (not_le.mpr (bot_lt_iff_ne_bot.mpr hγ0))
    · rw [hc, visibilityReplace_three_gridPoint_two] at hkeyu
      have hcB : c < B := by
        rw [hc, hh₂] at hAHlt; exact gridPoint_lt_gridPoint.mp hAHlt
      exact absurd hkeyu (not_le.mpr (gridPoint_three_lt_gridPoint_four hcB))
  have hah := le_of_min_eq_of_le hcap hh₂u
  have hagree₂ (e : Fin (I.tower 1).card) :
      min (b₀ e) h₂ = min ((I.tower 1).catalogueEntry 2 i e) h₂ := by
    calc min (b₀ e) h₂ = min (min (b₀ e) (agreementHeight ((I.tower 1).fieldGrid 2) b₀
          ((I.tower 1).catalogueEntry 2 i))) h₂ := by rw [min_assoc, min_eq_right hah]
      _ = min (min ((I.tower 1).catalogueEntry 2 i e) (agreementHeight
          ((I.tower 1).fieldGrid 2) b₀ ((I.tower 1).catalogueEntry 2 i))) h₂ := by
          rw [hagree e]
      _ = _ := by rw [min_assoc, min_eq_right hah]
  have he₁ : (I.tower 1).catalogueEntry 2 i (I.towerEmbed 1 d₁) = β₁ :=
    eq_of_min_eq_of_lt (by rw [← hagree₂, hb₀₁]) hβ₁h₂
  have he₂ : (I.tower 1).catalogueEntry 2 i (I.towerEmbed 1 d₂) = β₁ :=
    eq_of_min_eq_of_lt (by rw [← hagree₂, hb₀₂]) hβ₁h₂
  -- Locality at `u`.
  have hrow (d : Fin I.amalgam.card)
      (hd : I.towerEmbed 2 d ∈ (I.tower 2).toCellScheme.below
        ((I.tower 2).toCellScheme.gradedIndex (Fin.natAdd _ i))) :
      (I.tower 2).rows.row (Fin.natAdd _ i) ⟨I.towerEmbed 2 d, hd⟩ =
        (I.tower 1).catalogueEntry 2 i (I.towerEmbed 1 d) := by
    have := Scheme.fieldLayer_row_natAdd (S := I.tower 1) (k := 2)
      (hS := I.not_univ_succ_le_tower 1) i ⟨I.towerEmbed 2 d, hd⟩
    exact this.trans (Scheme.fieldRow_castAdd _ _)
  have hm (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 2) :
      I.towerEmbed 2 d ∈ (I.tower 2).toCellScheme.below
        ((I.tower 2).toCellScheme.gradedIndex (Fin.natAdd _ i)) := by
    rw [hu']; exact I.towerEmbed_mem_below hd
  have hlocu := hloc _ hum
  have h21 := hlocu.le_of_le (d := ⟨I.towerEmbed 2 d₂, hm d₂ (by omega)⟩)
    (d' := ⟨I.towerEmbed 2 d₁, hm d₁ (by omega)⟩)
    (by rw [hrow, hrow, he₁, he₂])
    (by simp only [Seed.grade_towerEmbed, hg₁, hg₂, le_refl])
  simp only at h21
  have hle₁ : I.amalgam.toCellScheme.grade d₁ ≤ 2 := by omega
  have hle₂ : I.amalgam.toCellScheme.grade d₂ ≤ 2 := by omega
  rw [Rows.extendBot_of_mem r (I.towerEmbed_mem_below hle₂),
    Rows.extendBot_of_mem r (I.towerEmbed_mem_below hle₁),
    hRu, hrw d₂ hle₂, hrw d₁ hle₁, ite_eq_right hd₂C, ite_eq_left hd₁C, hwD₂, hwC_def] at h21
  simp only [hd₁, tripleLabelling, hk₁, min_top_right] at h21
  exact hA₃top (top_le_iff.mp h21)

/-- **`2FL∃(2)` fails for the asymmetric seed.** -/
theorem not_twoFaceLiftExists_two_seedL : ¬ (seedL α).TwoFaceLiftExists 2 :=
  not_twoFaceLiftExists_two_of rfl rfl

end Refutation

/-- **The invariant of the tower fails at the grade `3` for the asymmetric seed**: it would give
`2FL∃(2)` (`Seed.twoFaceLiftExists_of_towerInvariant`). -/
theorem not_towerInvariant_three_seedL (α : Ordinal.{u}) : ¬ (seedL α).TowerInvariant 3 :=
  fun h ↦ not_twoFaceLiftExists_two_seedL ((seedL α).twoFaceLiftExists_of_towerInvariant h)

/-- **Nor at the top grade `4`** (`Seed.towerInvariant_top_iff`): the tower of the asymmetric seed
is not a completion below the full grade (its top scheme is not bountiful). -/
theorem not_towerInvariant_top_seedL (α : Ordinal.{u}) : ¬ (seedL α).TowerInvariant (3 + 1) :=
  fun h ↦ not_twoFaceLiftExists_two_seedL
    ((seedL α).towerInvariant_top_iff.mp h 2 le_rfl (by omega))

/-- **`2FL∃(j)` at the grades `2 ≤ j < m` fails as a statement about every legal seed**, at every
stage: the tower does not complete every seed (`Seed.towerInvariant_top_iff`). -/
theorem not_forall_twoFaceLiftExists (α : Ordinal.{u}) :
    ¬ ∀ (m : ℕ) (I : Seed.{u} α m) (j : ℕ), 2 ≤ j → j < m → I.TwoFaceLiftExists j :=
  fun h ↦ not_twoFaceLiftExists_two_seedL (h 3 (seedL α) 2 le_rfl (by omega))

/-- **The raised union fill fails at the grade `2` for the asymmetric seed**: the invariant at the
grade `2` holds (from `2FL(1)`), and with it the raised union fill would give `2FL∃(2)`
(`Seed.twoFaceLiftExists_of_raisedUnionFill`). -/
theorem not_raisedUnionFill_two_seedL (α : Ordinal.{u}) : ¬ (seedL α).RaisedUnionFill 2 := fun h ↦
  not_twoFaceLiftExists_two_seedL ((seedL α).twoFaceLiftExists_of_raisedUnionFill
    ((seedL α).towerInvariant_succ (by omega) (seedL α).towerInvariant_one
      (seedL α).twoFaceLift_one) h)

/-- **Both per-seed hypotheses of the library fail as well**: `2FL(2)` (it would give `2FL∃(2)`,
`2 ≤ m = 3`) and deadness at the grade `3` (with the invariant at `2`). -/
theorem not_twoFaceLift_or_deadAt_seedL (α : Ordinal.{u}) :
    ¬ ((seedL α).TwoFaceLift 2 ∨ (seedL α).DeadAt 2) := by
  rintro (h | h)
  · exact not_twoFaceLiftExists_two_seedL ((seedL α).twoFaceLiftExists_of_twoFaceLift (by omega) h)
  · exact not_twoFaceLiftExists_two_seedL ((seedL α).twoFaceLiftExists_of_deadAt
      ((seedL α).towerInvariant_succ (by omega) (seedL α).towerInvariant_one
        (seedL α).twoFaceLift_one) h)

end VaughtConjecture.TwoFaceLiftExistsCounterexample
