/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryFullCap

/-!
# The row of the cap reads every reference cell at its finite part

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the private cap and the decoder of (R4)); semantic contract, item 8.

`VaughtConjecture.Continuation.StableRecoveryFullCap` reduces stable recovery schemes for the graded
cap calibration to cap-reading extensions (`StageType.HasCapReadingExtensions`, open): legal
extensions whose cells at the graded face `(univ, N)` read the new cells of the coface `D`
through a full-scope cap of grade `N` (`StageType.ReadsThroughCap`).  The instances compiled so far
designed the context and the reading rows together.  This file removes that design from the
reading clause: the cap's own row is a reading row, at every legal `T⁺`.  Each item below is
compiled in this repository (theorem named), unless marked otherwise.

**The finite part at a reference cell** (`Label.TransformsTo.exists_eq_omega0_mul_add`,
`StageType.exists_row_eq_omega0_mul_add`).  Let a lawful section `p` have a cell `b` of grade `N`
(the cap) and a cell `a` below it with `p a = μ + i`, `μ` zero or a limit, `i < N` and
`μ + i < p b`.  Then the row of `b` reads `a` at `ω · c + i` for some ordinal `c`: the same finite
part.  Locality at `b` gives a witness `(g, σ)` with `g N ≥ p b`, so `σ` sends the value at `a` to
`μ + i`; commuting with visibility replacement at the threshold `N` excludes `⊥`, `⊤` and every
finite part at least `N`, and fixes the finite part `i`.

**One code per block** (`Label.TransformsTo.eq_of_eq_omega0_mul_add`,
`StageType.eq_of_row_eq_omega0_mul_add`).  Two such cells of one block `μ` are read in one block
`ω · c`: the shifter sends `ω · c + j` to `μ + j` for every `j ≤ N`, and a strictly larger code
`c'` would send `ω · c'` to `μ` below `σ (ω · c + N) = μ + N`.  So the row of the cap defines a
code of the blocks of its reference cells (`StageType.capBlockCode`), and the **cap code** of a
label (`StageType.capCode`): `⊥` for `⊥`, the cap's value at itself for `⊤`, and
`ω · capBlockCode μ + n` for `μ + n` (`StageType.row_eq_capBlockCode`, `StageType.capCode_coe_add`).

**The cap row reads through the cap** (`StageType.readsThroughCap_of_capRow`).  Let `T⁺` be a
stage type at `λ_{ξ+1}`, `b` a full-scope graded cap of `T⁺` for `D` and `γ`
(`StageType.IsGradedCap`), and `E` a scheme on one more point with face `T⁺` along the first
points.  A cell `u` of `E` above the cap whose row agrees with the cap's row of `T⁺` on the cells
of that face and reads a new cell `e` at the cap code of a label `ℓ` of `D` reads `e` through the
cap as a cell labelled `ℓ`.  The reference cell is the one given by the calibration, read by the
cap row at its finite part; the code of its block is the cap code of `ℓ`.  No context is designed:
the statement holds for every legal `T⁺`, every full-scope graded cap and every scheme `E`.

**Cap-row extensions** (`StageType.IsCapRowExtension`, `StageType.HasCapRowExtensions`, a new
named statement, open).  A cap-row extension is a legal scheme `E` with the faces `T⁺` and `D` in
which every cell at `(univ, N)` agrees with the cap row on the old cells and reads every new cell
of `D` at the cap code of its label.  It is a cap-reading extension
(`StageType.IsCapRowExtension.isCapReadingExtension`), so `StageType.HasCapRowExtensions ξ` implies
`StageType.HasCapReadingExtensions ξ` (`StageType.HasCapRowExtensions.hasCapReadingExtensions`).
It prescribes the whole row at `(univ, N)` on the old cells, so it is stronger than needed: the
reading needs only the reference cells read in the block of their new cells.  Whether the cap row
on the old cells always extends to a lawful row at `(univ, N)` is not known (argued, not
formalized: on the face of `D` the block codes of the cap row need room for the values of the
donor's locality witnesses; the coded copy of the capped labels has that room by construction).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label StageType
open Ordinal hiding univ

/-! ### The finite part at a reference cell -/

namespace Label

variable {ι : Type*} {grade : ι → ℕ} {r q : ι → Label.{u}} {g : ℕ → Label.{u}}
  {σ : Label.{u} → Label.{u}}

/-- The coercion of ordinals to labels is injective. -/
private theorem coe_ordinal_injective :
    Function.Injective (fun o : Ordinal.{u} ↦ (o : Label.{u})) :=
  WithBot.coe_injective.comp WithTop.coe_injective

/-- `μ + j = μ + i` as labels forces `j = i`. -/
private theorem natCast_eq_of_coe_add_eq {μ : Ordinal.{u}} {i j : ℕ}
    (h : ((μ + j : Ordinal.{u}) : Label.{u}) = ((μ + i : Ordinal.{u}) : Label.{u})) : j = i := by
  have h' : μ + (j : Ordinal.{u}) = μ + i := coe_ordinal_injective h
  exact_mod_cast add_left_cancel h'

/-- **Under the cap the shifter is exact**: if `q d = min (σ (r d)) (g (grade d))` for every
`d`, a cell `a` of grade at most that of `b` with `q a = x < q b` has `σ (r a) = x`, and `x` lies
below the suppressor at the grade of `b`. -/
private theorem apply_eq_of_lt (hw : IsWitness g σ)
    (heq : ∀ d, q d = min (σ (r d)) (g (grade d))) {a b : ι} {x : Label.{u}}
    (hab : grade a ≤ grade b) (hqa : q a = x) (hxb : x < q b) :
    σ (r a) = x ∧ x ≤ g (grade b) := by
  have hgb : q b ≤ g (grade b) := (heq b).trans_le (min_le_right _ _)
  refine ⟨?_, (hxb.trans_le hgb).le⟩
  have h1 := heq a
  rw [hqa] at h1
  have hg : x < g (grade a) := (hxb.trans_le hgb).trans_le (hw.antitone hab)
  rcases le_total (σ (r a)) (g (grade a)) with h2 | h2
  · rw [min_eq_left h2] at h1
    exact h1.symm
  · rw [min_eq_right h2] at h1
    exact absurd h1 hg.ne

/-- **The shifter on a block.**  If a witness sends `ω · c + i` to `μ + i` (`μ` zero or a limit,
`i < N`) below its suppressor at `N`, it sends `ω · c + j` to `μ + j` for every `j ≤ N`: it
commutes with the visibility replacement at the threshold `N` that turns `i` into `j`. -/
theorem IsWitness.apply_omega0_mul_add (hw : IsWitness g σ) {μ c : Ordinal.{u}}
    (hμ : Order.IsSuccPrelimit μ) {N i j : ℕ} (hi : i < N) (hj : j ≤ N)
    (hσ : σ ((ω * c + i : Ordinal.{u}) : Label.{u}) = ((μ + i : Ordinal.{u}) : Label.{u}))
    (hg : ((μ + i : Ordinal.{u}) : Label.{u}) ≤ g N) :
    σ ((ω * c + j : Ordinal.{u}) : Label.{u}) = ((μ + j : Ordinal.{u}) : Label.{u}) := by
  have hc : Order.IsSuccPrelimit (ω * c) :=
    Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _)
  have h := hw.visibilityReplace_comm _ N (hσ ▸ hg) j hj
  rwa [visibilityReplace_coe_add_natCast hc hi, hσ, visibilityReplace_coe_add_natCast hμ hi] at h

/-- **The finite part at a reference cell** (the reading of the cap row).  Let `r` transform to
`q` over the grades `grade`, and let `a`, `b` be cells with the grade of `a` at most that of `b`.
If `q a = μ + i` for `μ` zero or a limit, `i` below the grade of `b`, and `μ + i < q b`, then
`r a = ω · c + i` for some ordinal `c`: `r` reads `a` at the finite part of its target. -/
theorem TransformsTo.exists_eq_omega0_mul_add (h : TransformsTo grade r q) {μ : Ordinal.{u}}
    (hμ : Order.IsSuccPrelimit μ) {a b : ι} {i : ℕ} (hab : grade a ≤ grade b)
    (hi : i < grade b) (hqa : q a = ((μ + i : Ordinal.{u}) : Label.{u}))
    (hib : ((μ + i : Ordinal.{u}) : Label.{u}) < q b) :
    ∃ c : Ordinal.{u}, r a = ((ω * c + i : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨g, σ, hw, heq⟩ := h
  obtain ⟨hσa, hg⟩ := apply_eq_of_lt hw heq hab hqa hib
  -- commuting with visibility replacement at the grade of `b` and a value `j`
  have hcm (j : ℕ) (hj : j ≤ grade b) :
      σ (visibilityReplace (grade b) j (r a)) = ((μ + j : Ordinal.{u}) : Label.{u}) := by
    rw [hw.visibilityReplace_comm _ _ (hσa ▸ hg) j hj, hσa,
      visibilityReplace_coe_add_natCast hμ hi]
  -- a replacement with a value other than `i` cannot fix the value at `a`
  have hne (j : ℕ) (hj : j ≤ grade b) (hji : j ≠ i)
      (hfix : visibilityReplace (grade b) j (r a) = r a) : False :=
    hji (natCast_eq_of_coe_add_eq ((hcm j hj).symm.trans (by rw [hfix, hσa])))
  generalize hx : r a = x at hσa hcm hne ⊢
  induction x using recBotCoeTop with
  | bot =>
    rw [hw.map_bot] at hσa
    exact absurd hσa WithBot.bot_ne_coe
  | top => exact (hne _ le_rfl hi.ne' (visibilityReplace_top _ _)).elim
  | coe o =>
    obtain ⟨μ', hμ', j, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o
    obtain ⟨c, rfl⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hμ'
    refine ⟨c, ?_⟩
    rcases lt_or_ge j (grade b) with hj | hj
    · rcases eq_or_ne j i with rfl | hji
      · rfl
      · exact (hne j hj.le hji (visibilityReplace_coe_add_natCast hμ' hj j)).elim
    · exact (hne _ le_rfl hi.ne' ((isSelfVisible_coe_add hμ' hj).visibilityReplace_eq _)).elim

/-- `ω · c + N < ω · c'` for `c < c'` and `N` finite. -/
private theorem omega0_mul_add_natCast_lt {c c' : Ordinal.{u}} (h : c < c') (N : ℕ) :
    ω * c + N < ω * c' := by
  calc ω * c + N < ω * c + ω := (add_lt_add_iff_left _).mpr (natCast_lt_omega0 N)
    _ = ω * Order.succ c := (Ordinal.mul_succ ω c).symm
    _ ≤ ω * c' := mul_le_mul_right (Order.succ_le_of_lt h) _

/-- **One code per block.**  Let `r` transform to `q` over the grades `grade`.  If two cells `a`
and `a'` of grades at most that of `b` have targets `μ + i` and `μ + i'` in one block `μ` (zero or
a limit), with `i, i'` below the grade of `b` and both targets below `q b`, and `r` reads them at
`ω · c + i` and `ω · c' + i'`, then `c = c'`. -/
theorem TransformsTo.eq_of_eq_omega0_mul_add (h : TransformsTo grade r q) {μ : Ordinal.{u}}
    (hμ : Order.IsSuccPrelimit μ) {a a' b : ι} {i i' : ℕ} {c c' : Ordinal.{u}}
    (hab : grade a ≤ grade b) (ha'b : grade a' ≤ grade b) (hi : i < grade b)
    (hi' : i' < grade b) (hqa : q a = ((μ + i : Ordinal.{u}) : Label.{u}))
    (hqa' : q a' = ((μ + i' : Ordinal.{u}) : Label.{u}))
    (hib : ((μ + i : Ordinal.{u}) : Label.{u}) < q b)
    (hi'b : ((μ + i' : Ordinal.{u}) : Label.{u}) < q b)
    (hra : r a = ((ω * c + i : Ordinal.{u}) : Label.{u}))
    (hra' : r a' = ((ω * c' + i' : Ordinal.{u}) : Label.{u})) : c = c' := by
  obtain ⟨g, σ, hw, heq⟩ := h
  obtain ⟨hσa, hg⟩ := apply_eq_of_lt hw heq hab hqa hib
  obtain ⟨hσa', hg'⟩ := apply_eq_of_lt hw heq ha'b hqa' hi'b
  rw [hra] at hσa
  rw [hra'] at hσa'
  have h₁ (j : ℕ) (hj : j ≤ grade b) := hw.apply_omega0_mul_add hμ hi hj hσa hg
  have h₂ (j : ℕ) (hj : j ≤ grade b) := hw.apply_omega0_mul_add hμ hi' hj hσa' hg'
  -- a strictly smaller code would be sent above a strictly larger one
  have key {d d' : Ordinal.{u}}
      (hd : ∀ j ≤ grade b, σ ((ω * d + j : Ordinal.{u}) : Label.{u}) =
        ((μ + j : Ordinal.{u}) : Label.{u}))
      (hd' : ∀ j ≤ grade b, σ ((ω * d' + j : Ordinal.{u}) : Label.{u}) =
        ((μ + j : Ordinal.{u}) : Label.{u})) : ¬ d < d' := by
    intro hlt
    have hle : ((ω * d + grade b : Ordinal.{u}) : Label.{u}) ≤
        ((ω * d' + (0 : ℕ) : Ordinal.{u}) : Label.{u}) := by
      rw [Nat.cast_zero, add_zero]
      exact_mod_cast (omega0_mul_add_natCast_lt hlt _).le
    have hσ := hw.monotone hle
    rw [hd _ le_rfl, hd' 0 (Nat.zero_le _)] at hσ
    have hle' : μ + (grade b : Ordinal.{u}) ≤ μ + ((0 : ℕ) : Ordinal.{u}) := by exact_mod_cast hσ
    have : (grade b : Ordinal.{u}) ≤ ((0 : ℕ) : Ordinal.{u}) := (add_le_add_iff_left μ).mp hle'
    have : grade b ≤ 0 := by exact_mod_cast this
    omega
  exact le_antisymm (not_lt.mp (key h₂ h₁)) (not_lt.mp (key h₁ h₂))

/-- The **block quotient** of a label: `o / ω` at an ordinal `o`, and `0` at `⊥` and `⊤`; the code
`c` of a value `ω · c + i`. -/
noncomputable def blockQuot : Label.{u} → Ordinal.{u} :=
  recBotCoeTop (motive := fun _ ↦ Ordinal.{u}) 0 (fun o ↦ o / ω) 0

/-- The block quotient of `ω · c + i` is `c`. -/
theorem blockQuot_omega0_mul_add (c : Ordinal.{u}) (i : ℕ) :
    blockQuot ((ω * c + i : Ordinal.{u}) : Label.{u}) = c := by
  -- the block quotient of an ordinal label is its quotient by `ω`
  change (ω * c + i) / ω = c
  rw [Ordinal.mul_add_div _ omega0_ne_zero, Ordinal.div_eq_zero_of_lt (natCast_lt_omega0 i),
    add_zero]

end Label

/-! ### The row of the cap -/

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ}

/-- **The cap row reads a reference cell at its finite part**: in a stage type `T`, let `b` be a
cell (the cap) and `a` a cell below its graded index labelled `μ + i` (`μ` zero or a limit), with
`i` below the grade of `b` and `μ + i` below the label of `b`.  Then the row of `b` reads `a` at
`ω · c + i` for some ordinal `c`. -/
theorem exists_row_eq_omega0_mul_add (T : StageType.{u} α n) {a b : Fin T.card}
    (ha : a ∈ T.toCellScheme.below (T.toCellScheme.gradedIndex b)) {μ : Ordinal.{u}}
    (hμ : Order.IsSuccPrelimit μ) {i : ℕ} (hi : i < T.toCellScheme.grade b)
    (hTa : T.label a = ((μ + i : Ordinal.{u}) : Label.{u}))
    (hab : ((μ + i : Ordinal.{u}) : Label.{u}) < T.label b) :
    ∃ c : Ordinal.{u}, T.rows.row b ⟨a, ha⟩ = ((ω * c + i : Ordinal.{u}) : Label.{u}) :=
  (T.isLawful.locality b).exists_eq_omega0_mul_add (a := ⟨a, ha⟩)
    (b := ⟨b, T.toCellScheme.mem_below_gradedIndex b⟩) hμ ha.2 hi (by
      -- the labelling of locality at `b` is `d ↦ min (T.label d) (T.label b)`
      change min (T.label a) (T.label b) = _
      rw [min_eq_left (hTa ▸ hab).le, hTa]) (by
      -- the same labelling, at `b`
      change _ < min (T.label b) (T.label b)
      rwa [min_self])

/-- **The cap row has one code per block**: two cells below the cap `b` labelled `μ + i` and
`μ + i'` in one block, both below the label of `b` with `i, i'` below its grade, are read by the
row of `b` in one block `ω · c`. -/
theorem eq_of_row_eq_omega0_mul_add (T : StageType.{u} α n) {a a' b : Fin T.card}
    (ha : a ∈ T.toCellScheme.below (T.toCellScheme.gradedIndex b))
    (ha' : a' ∈ T.toCellScheme.below (T.toCellScheme.gradedIndex b)) {μ : Ordinal.{u}}
    (hμ : Order.IsSuccPrelimit μ) {i i' : ℕ} {c c' : Ordinal.{u}}
    (hi : i < T.toCellScheme.grade b) (hi' : i' < T.toCellScheme.grade b)
    (hTa : T.label a = ((μ + i : Ordinal.{u}) : Label.{u}))
    (hTa' : T.label a' = ((μ + i' : Ordinal.{u}) : Label.{u}))
    (hab : ((μ + i : Ordinal.{u}) : Label.{u}) < T.label b)
    (ha'b : ((μ + i' : Ordinal.{u}) : Label.{u}) < T.label b)
    (hra : T.rows.row b ⟨a, ha⟩ = ((ω * c + i : Ordinal.{u}) : Label.{u}))
    (hra' : T.rows.row b ⟨a', ha'⟩ = ((ω * c' + i' : Ordinal.{u}) : Label.{u})) : c = c' := by
  have hq (x : Fin T.card) (hx : x ∈ T.toCellScheme.below (T.toCellScheme.gradedIndex b))
      {o : Ordinal.{u}} (hx' : T.label x = (o : Label.{u})) (hxb : (o : Label.{u}) < T.label b) :
      (fun d : T.toCellScheme.below (T.toCellScheme.gradedIndex b) ↦
        min (T.label d) (T.label b)) ⟨x, hx⟩ = (o : Label.{u}) := by
    -- the labelling of locality at `b`, at `x`
    change min (T.label x) (T.label b) = _
    rw [min_eq_left (hx' ▸ hxb).le, hx']
  have hqb {o : Ordinal.{u}} (h : (o : Label.{u}) < T.label b) :
      (o : Label.{u}) < (fun d : T.toCellScheme.below (T.toCellScheme.gradedIndex b) ↦
        min (T.label d) (T.label b)) ⟨b, T.toCellScheme.mem_below_gradedIndex b⟩ := by
    -- the labelling of locality at `b`, at `b`
    change _ < min (T.label b) (T.label b)
    rwa [min_self]
  exact (T.isLawful.locality b).eq_of_eq_omega0_mul_add (a := ⟨a, ha⟩) (a' := ⟨a', ha'⟩)
    (b := ⟨b, T.toCellScheme.mem_below_gradedIndex b⟩) hμ ha.2 ha'.2 hi hi' (hq a ha hTa hab)
    (hq a' ha' hTa' ha'b) (hqb hab) (hqb ha'b) hra hra'

open Classical in
/-- The **block code of the cap** for a block `μ`: the block quotient of the value of the row of the
cap `b` at some cell below `b` labelled `μ + i`, with `i` below the grade of `b` and `μ + i`
below the label of `b`, if there is one, and `0` otherwise.  It does not depend on the cell
(`StageType.row_eq_capBlockCode`). -/
noncomputable def capBlockCode (T : StageType.{u} α n) (b : Fin T.card) (μ : Ordinal.{u}) :
    Ordinal.{u} :=
  if h : ∃ (a : T.toCellScheme.below (T.toCellScheme.gradedIndex b)) (i : ℕ),
      T.label a = ((μ + i : Ordinal.{u}) : Label.{u}) ∧ i < T.toCellScheme.grade b ∧
        ((μ + i : Ordinal.{u}) : Label.{u}) < T.label b
  then blockQuot (T.rows.row b h.choose) else 0

/-- **The cap row reads every reference cell at the cap's block code**: for a cell `a` below the
cap `b` labelled `μ + i` (`μ` zero or a limit), with `i` below the grade of `b` and `μ + i` below
the label of `b`, the row of `b` reads `a` at `ω · capBlockCode μ + i`. -/
theorem row_eq_capBlockCode (T : StageType.{u} α n) {a b : Fin T.card}
    (ha : a ∈ T.toCellScheme.below (T.toCellScheme.gradedIndex b)) {μ : Ordinal.{u}}
    (hμ : Order.IsSuccPrelimit μ) {i : ℕ} (hi : i < T.toCellScheme.grade b)
    (hTa : T.label a = ((μ + i : Ordinal.{u}) : Label.{u}))
    (hab : ((μ + i : Ordinal.{u}) : Label.{u}) < T.label b) :
    T.rows.row b ⟨a, ha⟩ = ((ω * T.capBlockCode b μ + i : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨c, hc⟩ := T.exists_row_eq_omega0_mul_add ha hμ hi hTa hab
  have hex : ∃ (a : T.toCellScheme.below (T.toCellScheme.gradedIndex b)) (i : ℕ),
      T.label a = ((μ + i : Ordinal.{u}) : Label.{u}) ∧ i < T.toCellScheme.grade b ∧
        ((μ + i : Ordinal.{u}) : Label.{u}) < T.label b := ⟨⟨a, ha⟩, i, hTa, hi, hab⟩
  rw [capBlockCode, dite_eq_left hex]
  obtain ⟨i', hTa', hi', ha'b⟩ := hex.choose_spec
  obtain ⟨c', hc'⟩ := T.exists_row_eq_omega0_mul_add hex.choose.2 hμ hi' hTa' ha'b
  rw [hc', blockQuot_omega0_mul_add, hc,
    T.eq_of_row_eq_omega0_mul_add ha hex.choose.2 hμ hi hi' hTa hTa' hab ha'b hc hc']

/-- The **cap code** of a label for the cap `b`: `⊥` at `⊥`; the value of the row of `b` at `b`
itself at the formal top; and at an ordinal `μ + n` (`μ` zero or a limit), `ω · c + n` for the
block code `c = capBlockCode μ` of the cap. -/
noncomputable def capCode (T : StageType.{u} α n) (b : Fin T.card) : Label.{u} → Label.{u} :=
  recBotCoeTop ⊥
    (fun o ↦ ((ω * T.capBlockCode b (ω * (o / ω)) + o % ω : Ordinal.{u}) : Label.{u}))
    (T.rows.row b ⟨b, T.toCellScheme.mem_below_gradedIndex b⟩)

/-- The cap code of `⊥` is `⊥`. -/
@[simp] theorem capCode_bot (T : StageType.{u} α n) (b : Fin T.card) : T.capCode b ⊥ = ⊥ := rfl

/-- The cap code of the formal top is the value of the row of the cap at itself. -/
@[simp] theorem capCode_top (T : StageType.{u} α n) (b : Fin T.card) :
    T.capCode b ⊤ = T.rows.row b ⟨b, T.toCellScheme.mem_below_gradedIndex b⟩ := rfl

/-- The cap code of `μ + n`, for `μ` zero or a limit: `ω · capBlockCode μ + n`. -/
theorem capCode_coe_add (T : StageType.{u} α n) (b : Fin T.card) {μ : Ordinal.{u}}
    (hμ : Order.IsSuccPrelimit μ) (k : ℕ) :
    T.capCode b ((μ + k : Ordinal.{u}) : Label.{u}) =
      ((ω * T.capBlockCode b μ + k : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨c, rfl⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hμ
  -- the cap code at an ordinal, unfolded
  change ((ω * T.capBlockCode b (ω * ((ω * c + k) / ω)) + (ω * c + k) % ω : Ordinal.{u}) :
    Label.{u}) = _
  rw [Ordinal.mul_add_div _ omega0_ne_zero, Ordinal.div_eq_zero_of_lt (natCast_lt_omega0 k),
    add_zero, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (natCast_lt_omega0 k)]

/-! ### The cap row reads through the cap -/

section CapRow

variable {ξ : Ordinal.{u}} {m k : ℕ}

/-- Equal schemes have equal scopes at cells with equal positions. -/
private theorem scope_congr {S S' : Scheme.{u} m} (h : S = S') {i : Fin S.card}
    {j : Fin S'.card} (hij : (i : ℕ) = j) : S.toCellScheme.scope i = S'.toCellScheme.scope j := by
  subst h
  rw [Fin.ext hij]

/-- **The cap row reads through the cap.**  Let `b₀` be a graded cap of full scope of `T⁺` for `D`
and `γ` (`StageType.IsGradedCap`), and let `E` be a scheme on one more point whose face along the
first points is the scheme of `T⁺`, with `b` the cell of that face at the position of `b₀`.  Let
the row of a cell `u` of `E` agree with the row of the cap `b₀` of `T⁺` on the cells of that face
below `u`, and read a cell `e` at the cap code (`StageType.capCode`) of the label of a cell `j` of
`D`.  Then `u` reads `e` through the cap as a cell labelled `D.label j`
(`StageType.ReadsThroughCap`).  The reference cell is the one of the calibration: the cap row reads
it at its finite part, in the block of the cap code (`StageType.row_eq_capBlockCode`). -/
theorem readsThroughCap_of_capRow {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}} {b₀ : Fin Tp.card}
    (hbu : Tp.toCellScheme.scope b₀ = univ) (hcap : IsGradedCap ξ Tp D γ b₀)
    {E : Scheme.{u} (m + 1)} (hT : E.comap Fin.castSuccEmb = Tp.toScheme)
    {b : Fin (E.comap Fin.castSuccEmb).card} (hbb₀ : (b : ℕ) = b₀) {u e : Fin E.card}
    (hold : ∀ (a : Fin (E.comap Fin.castSuccEmb).card) (a₀ : Fin Tp.card), (a : ℕ) = a₀ →
      ∀ (ha : E.cellMap Fin.castSuccEmb a ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u))
        (ha₀ : a₀ ∈ Tp.toCellScheme.below (Tp.toCellScheme.gradedIndex b₀)),
        E.rows.row u ⟨_, ha⟩ = Tp.rows.row b₀ ⟨a₀, ha₀⟩)
    (j : Fin D.card)
    (hnew : ∀ he : e ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u),
      E.rows.row u ⟨e, he⟩ = Tp.capCode b₀ (D.label j)) :
    Tp.ReadsThroughCap E b u e (D.label j) := by
  obtain ⟨hb₀, -, -, href⟩ := hcap
  have hcard : (E.comap Fin.castSuccEmb).card = Tp.card := congrArg Scheme.card hT
  have hgb : E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b) = Tp.toCellScheme.grade b₀ :=
    Scheme.grade_congr hT hbb₀
  have hscb : E.toCellScheme.scope (E.cellMap Fin.castSuccEmb b) =
      univ.map (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) := by
    rw [← Scheme.map_comap_scope, scope_congr hT hbb₀, hbu]
  intro he hb
  refine ⟨fun h ↦ by rw [hnew he, h, capCode_bot], fun h ↦ ?_, fun μ n hμ h ↦ ?_⟩
  · rw [hnew he, h, capCode_top, hold b b₀ hbb₀ hb]
  -- the reference cell of the calibration, in the block `μ`
  obtain ⟨μ', n', i, a₀, hμ', ho, hn, hi, ha₀N, ha₀⟩ := href j (μ + n) h
  obtain ⟨rfl, rfl⟩ := (add_natCast_eq_add_natCast_iff hμ hμ').mp ho
  -- the block `μ` is at most `λ_ξ`, since the label of `D` lies below `λ_{ξ+1}`
  have hlt : μ + n < blockStage ξ + ω := by
    rcases D.atStage j with h' | h'
    · rw [h, blockStage_add_one] at h'
      exact_mod_cast h'
    · rw [h] at h'
      exact absurd h' (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne
  have hμξ : μ ≤ blockStage ξ := by
    by_contra hμξ
    exact (add_omega0_le_of_isSuccPrelimit hμ (not_le.mp hμξ)).not_gt
      ((le_self_add).trans_lt hlt)
  -- the reference value lies below the cap
  have hab : ((μ + i : Ordinal.{u}) : Label.{u}) < Tp.label b₀ := by
    refine lt_of_lt_of_le ?_ hb₀
    have : μ + i < blockStage ξ + Tp.toCellScheme.grade b₀ := by
      rcases hμξ.lt_or_eq with hμξ | rfl
      · exact ((isSuccPrelimit_blockStage ξ).add_natCast_lt hμξ i).trans_le le_self_add
      · exact add_lt_add_right (Nat.cast_lt.mpr hi) _
    exact_mod_cast this
  have ha₀b : a₀ ∈ Tp.toCellScheme.below (Tp.toCellScheme.gradedIndex b₀) := by
    refine ⟨?_, ha₀N⟩
    -- the scope of `b₀` is all the points of `T⁺`
    change Tp.toCellScheme.scope a₀ ⊆ Tp.toCellScheme.scope b₀
    rw [hbu]
    exact subset_univ _
  -- the reference cell in the face of `E`, below `u`
  set a : Fin (E.comap Fin.castSuccEmb).card := Fin.cast hcard.symm a₀
  have ha : E.cellMap Fin.castSuccEmb a ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u) := by
    refine ⟨?_, ?_⟩
    · -- the scope of the reference cell lies in that of the cap, of full scope
      change E.toCellScheme.scope (E.cellMap Fin.castSuccEmb a) ⊆ _
      rw [← Scheme.map_comap_scope]
      exact (map_subset_map.mpr (subset_univ _)).trans (hscb ▸ hb.1)
    · exact (Scheme.grade_congr hT rfl).trans_le (ha₀N.trans (hgb.symm.trans_le hb.2))
  refine ⟨hgb ▸ hn, a, a₀, i, Tp.capBlockCode b₀ μ, rfl, ha₀, hgb ▸ hi, ha, ?_, ?_⟩
  · rw [hold a a₀ rfl ha ha₀b, Tp.row_eq_capBlockCode ha₀b hμ hi ha₀ hab]
  · rw [hnew he, h, capCode_coe_add _ _ hμ]

/-- A **cap-row extension** of `T⁺` along `f` for `D` and a cell `b` of `T⁺` of grade `N`: a legal
scheme `E` on `m + 1` points with the faces of a cap-reading extension
(`StageType.IsCapReadingExtension`) in which every cell `u` at the graded face `(univ, N)`

* agrees with the row of the cap `b` of `T⁺` on the cells of the face along the first points below
  it; and
* reads every new cell of `D` (a cell whose scope contains the new point) at the cap code
  (`StageType.capCode`) of its label. -/
def IsCapRowExtension {α : Ordinal.{u}} (Tp : StageType.{u} α m) (f : Fin k ↪ Fin m)
    (D : StageType.{u} α (k + 1)) (b : Fin Tp.card) (E : Scheme.{u} (m + 1)) : Prop :=
  E.IsLegal ∧ univ.map Fin.castSuccEmb ∈ E.toCellScheme.faces ∧
    E.comap Fin.castSuccEmb = Tp.toScheme ∧ univ.map (extendByLast f) ∈ E.toCellScheme.faces ∧
    E.comap (extendByLast f) = D.toScheme ∧
    ∀ u, E.toCellScheme.gradedIndex u =
        ((univ : Finset (Fin (m + 1))), Tp.toCellScheme.grade b) →
      (∀ (a : Fin (E.comap Fin.castSuccEmb).card) (a₀ : Fin Tp.card), (a : ℕ) = a₀ →
        ∀ (ha : E.cellMap Fin.castSuccEmb a ∈
            E.toCellScheme.below (E.toCellScheme.gradedIndex u))
          (ha₀ : a₀ ∈ Tp.toCellScheme.below (Tp.toCellScheme.gradedIndex b)),
          E.rows.row u ⟨_, ha⟩ = Tp.rows.row b ⟨a₀, ha₀⟩) ∧
      ∀ (i : Fin (E.comap (extendByLast f)).card) (j : Fin D.card), (i : ℕ) = j →
        Fin.last k ∈ D.toCellScheme.scope j →
        ∀ he : E.cellMap (extendByLast f) i ∈
            E.toCellScheme.below (E.toCellScheme.gradedIndex u),
          E.rows.row u ⟨_, he⟩ = Tp.capCode b (D.label j)

/-- **A cap-row extension for a full-scope graded cap is a cap-reading extension**
(`StageType.readsThroughCap_of_capRow` at every cell of `(univ, N)` and every new cell of `D`). -/
theorem IsCapRowExtension.isCapReadingExtension {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {f : Fin k ↪ Fin m} {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    {b : Fin Tp.card} (hbu : Tp.toCellScheme.scope b = univ) (hcap : IsGradedCap ξ Tp D γ b)
    {E : Scheme.{u} (m + 1)} (h : IsCapRowExtension Tp f D b E) :
    IsCapReadingExtension Tp f D b E := by
  obtain ⟨hE, hc, hcT, hf, hED, hrow⟩ := h
  have hcard : (E.comap Fin.castSuccEmb).card = Tp.card := congrArg Scheme.card hcT
  exact ⟨hE, hc, hcT, hf, hED, Fin.cast hcard.symm b, rfl, fun u hu i j hij hj ↦
    readsThroughCap_of_capRow hbu hcap hcT rfl (hrow u hu).1 j ((hrow u hu).2 i j hij hj)⟩

variable (ξ) in
/-- **Cap-row extensions at `ξ`** (a new named statement; open): `StageType.HasCapReadingExtensions`
with the cap-row extension (`StageType.IsCapRowExtension`) in place of the cap-reading extension.
For every legal `T⁺` at `λ_{ξ+1}`, embedding `f` of `k > 0` points with face `P`, coface `D` of
`P`, `γ < λ_{ξ+1}` and full-scope graded cap `b` of `T⁺` for `D` and `γ`, there is a cap-row
extension.  It prescribes the rows at `(univ, N)` on all the old cells, so it is stronger than
`StageType.HasCapReadingExtensions`; whether such rows are always lawful is not known. -/
def HasCapRowExtensions : Prop :=
  ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
    (P : StageType.{u} (blockStage (ξ + 1)) k), Tp.IsLegal → 0 < k →
    restrictFace f Tp = some P → ∀ D ∈ P.cofaces, ∀ γ : Ordinal.{u}, γ < blockStage (ξ + 1) →
      ∀ b : Fin Tp.card, Tp.toCellScheme.scope b = univ → IsGradedCap ξ Tp D γ b →
        ∃ E : Scheme.{u} (m + 1), IsCapRowExtension Tp f D b E

/-- **Cap-row extensions give cap-reading extensions**
(`StageType.IsCapRowExtension.isCapReadingExtension`).  Both statements are open; this is the
implication only. -/
theorem HasCapRowExtensions.hasCapReadingExtensions (h : HasCapRowExtensions ξ) :
    HasCapReadingExtensions ξ := by
  intro m k Tp f P hT hk hP D hD γ hγ b hbu hcap
  obtain ⟨E, hE⟩ := h Tp f P hT hk hP D hD γ hγ b hbu hcap
  exact ⟨E, hE.isCapReadingExtension hbu hcap⟩

end CapRow

end StageType

end VaughtConjecture
