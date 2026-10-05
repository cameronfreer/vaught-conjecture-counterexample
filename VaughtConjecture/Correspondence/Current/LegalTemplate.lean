/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Current.Bountiful
import VaughtConjecture.Geometry.IntervalPlan
import VaughtConjecture.Stage.Legal

/-!
# Correspondence with the legal templates of [AFK26]

Roadmap, "Manuscript concordance", row 45.  [AFK26, Definition 4.27] calls a template
`t = (c, (ℓ_d)_{d ∈ D})` over a plan `(A, P)` *legal* if

1. `range(c) = GradedFace[P]`: every graded face has a cell;
2. each `ℓ_d` is lawful;
3. the rows of `(ℓ_d)_{d ∈ D}` are bountiful;
4. `range(ℓ_d) ⊆ {-∞} ∪ {ω · n + i : n ∈ ω, i ≤ g(d)}` for each `d`.

The clauses are compared with `Scheme.IsLegal` (`Stage/Legal`), with the coding clause
`Scheme.IsCoded` (`Stage/Scheme`).  The setting is that of
`VaughtConjecture.Correspondence.Current.LocalLabelling` (row 43): a frame is a cell scheme `D`
with its gradings, and the row system is the rows `R`.  As in rows 43 and 44, the definition is
stated at a stage `θ` (`CellScheme.Rows.PrintedLegal θ`); [AFK26] takes `θ = ω₁`.

| Printed clause | `PrintedLegal` | `CorrectedLegal` | `Scheme.IsLegal` |
| --- | --- | --- | --- |
| the frame: `c : D → GradedFace[P]` | `gradedIndex_mem` | `gradedIndex_mem` | `isWellFormed` |
| 1. every graded face has a cell | `exists_gradedIndex_eq` | `isComplete` | `isComplete` |
| 2. each `ℓ_d` lawful (row 43) | `lawful` | `lawful` | `isConsistent` |
| 3. the rows bountiful (row 44) | `bountiful` | `bountiful` | `isBountiful` |
| 4. `range(ℓ_d) ⊆ {-∞} ∪ {ω · n + i : i ≤ g(d)}` | `range` | `range` | `isCoded` (weaker) |

**Correction of clause 1** (status C).  A printed graded face may have grade `0`
([AFK26, Definition 4.2]), so clause 1 asks for a cell of grade `0` on every face, `∅` among them.
The frames of this development have cells of positive grade, as in [Kni26, Definition 2.1.8], and
no such frame satisfies clause 1 as printed (`CellScheme.Rows.not_printedLegal`).  The corrected
clause asks for a cell on every graded face of positive grade, which is completeness
(`CellScheme.IsComplete`, field `isComplete` of `CellScheme.Rows.CorrectedLegal`); the typing of the
frame is corrected in the same way (field `gradedIndex_mem`).

**Clauses 2–4** (status S).
* Clause 2 is consistency of the rows (`CellScheme.Rows.IsConsistent`), by the identification of
  row 43 (`CellScheme.Rows.printedLawfulLocal_iff`).
* Clause 3 is the printed definition of row 44, which is bountifulness only at every stage and with
  the extension of lawful labellings (the cap `-∞`;
  `CellScheme.Rows.isBountiful_iff_forall_printedBountifulRows`).
* Clause 4 (`CellScheme.Rows.HasPrintedRange`) is strictly stronger than the coding clause
  `Scheme.IsCoded` (row values below `ω ^ 2`): it implies it
  (`CellScheme.Rows.HasPrintedRange.row_lt`), and a legal scheme on one point whose row has the
  value `2` at a cell of grade `1` violates it (`Scheme.exists_isLegal_not_hasPrintedRange`).  So
  the legal schemes of this development form a larger class than the legal templates of [AFK26];
  whether every legal scheme is equivalent to one satisfying clause 4 is not proved here.

**What is compiled.**  A legal scheme satisfying clause 4 satisfies the corrected definition at
every stage `θ ≥ ω ^ 2` that is zero or a limit (`Scheme.IsLegal.correctedLegal`), in particular
at `ω₁` (`Scheme.IsLegal.correctedLegal_omega_one`).  Conversely, a well-formed scheme satisfying
the corrected definition at every such stage, whose lawful labellings extend between graded faces,
is legal and satisfies clause 4; the two together are an equivalence
(`Scheme.isLegal_and_hasPrintedRange_iff`).  No theorem here derives `Scheme.IsLegal` from the
corrected definition at the single stage `ω₁`.

**The statements that follow** (statements only, rows 46 and 47).  [AFK26, Lemma 4.28]: a template
system of legal templates representing every legal template up to relabelling isomorphism; here the
legal stage types are closed under the face maps (`StageType.IsLegal.restrictFace`), reindexing
(`StageType.IsLegal.reindex`), and stage reduction (`StageType.isLegal_reduce_iff`), with one
relation symbol of the base language for each legal stage type at stage `ω`.
[AFK26, Theorem 4.29], the counterexample, corresponds to the main theorem in its conditional
composition `vaughtCounterexample_of_expansionDomains` (`MainTheorem/Assembly`), with the density
sentence for `σ[L]`; both rows are still to be proved.

## Placement

The concordance and its notes are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".
-/

universe u

namespace VaughtConjecture

open Finset Label Ordinal

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} (R : D.Rows.{u}) {θ : Ordinal.{u}}

/-- **The range clause of [AFK26, Definition 4.27]**: every value of the row of a cell `d` is `-∞`
or an ordinal `ω · n + i` with `n ∈ ω` and `i ≤ g(d)`. -/
def HasPrintedRange : Prop :=
  ∀ s (t : D.below (D.gradedIndex s)), R.row s t = ⊥ ∨
    ∃ n i : ℕ, i ≤ D.grade s ∧ R.row s t = ((ω * n + i : Ordinal.{u}) : Label.{u})

/-- **Legal templates as printed** [AFK26, Definition 4.27], at stage `θ`: the frame takes values
among the printed graded faces (grade `0` allowed), and the four printed clauses. -/
structure PrintedLegal (θ : Ordinal.{u}) : Prop where
  /-- The frame of [AFK26, Definition 4.4]: `c : D → GradedFace[P]`. -/
  gradedIndex_mem : ∀ d, D.gradedIndex d ∈ D.printedGradedFaces
  /-- Clause 1 of [AFK26, Definition 4.27]: every graded face has a cell. -/
  exists_gradedIndex_eq : ∀ X ∈ D.printedGradedFaces, ∃ d, D.gradedIndex d = X
  /-- Clause 2 of [AFK26, Definition 4.27]: each `ℓ_d` is lawful. -/
  lawful : ∀ d, R.PrintedLawfulLocal θ (D.gradedIndex d) (R.row d)
  /-- Clause 3 of [AFK26, Definition 4.27]: the rows are bountiful. -/
  bountiful : R.PrintedBountifulRows θ
  /-- Clause 4 of [AFK26, Definition 4.27]: `range(ℓ_d) ⊆ {-∞} ∪ {ω · n + i : i ≤ g(d)}`. -/
  range : R.HasPrintedRange

/-- **Legal templates, corrected** [AFK26, Definition 4.27], at stage `θ`: as printed, with the
graded faces of clause 1 and of the frame those of positive grade. -/
structure CorrectedLegal (θ : Ordinal.{u}) : Prop where
  /-- The frame of [AFK26, Definition 4.4], corrected: every cell has a graded face of positive
  grade. -/
  gradedIndex_mem : ∀ d, D.gradedIndex d ∈ D.gradedFaces
  /-- Clause 1 of [AFK26, Definition 4.27], corrected: every graded face of positive grade has a
  cell. -/
  isComplete : D.IsComplete
  /-- Clause 2 of [AFK26, Definition 4.27]: each `ℓ_d` is lawful. -/
  lawful : ∀ d, R.PrintedLawfulLocal θ (D.gradedIndex d) (R.row d)
  /-- Clause 3 of [AFK26, Definition 4.27]: the rows are bountiful. -/
  bountiful : R.PrintedBountifulRows θ
  /-- Clause 4 of [AFK26, Definition 4.27]: `range(ℓ_d) ⊆ {-∞} ∪ {ω · n + i : i ≤ g(d)}`. -/
  range : R.HasPrintedRange

variable {R}

/-- **Clause 1 as printed fails for the frames here**: if every cell has a graded face of positive
grade and the plan has a face, no rows are legal as printed, since the face with grade `0` has no
cell. -/
theorem not_printedLegal (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces) (hF : D.faces.Nonempty) :
    ¬ R.PrintedLegal θ := fun h ↦ by
  obtain ⟨B, hB⟩ := hF
  obtain ⟨d, hd⟩ := h.exists_gradedIndex_eq (B, 0) ⟨hB, Nat.zero_le _⟩
  have := (hD d).2.1
  rw [hd] at this
  exact absurd this (lt_irrefl 0)

/-- An ordinal `ω · n + i` with `n`, `i` finite is below `ω ^ 2`. -/
private theorem omega0_mul_add_natCast_lt_omega0_sq (n i : ℕ) :
    ω * (n : Ordinal.{u}) + i < ω ^ 2 :=
  calc ω * (n : Ordinal.{u}) + i < ω * n + ω := (add_lt_add_iff_left _).mpr (natCast_lt_omega0 i)
    _ = ω * ((n + 1 : ℕ) : Ordinal.{u}) := by push_cast; rw [mul_add_one]
    _ < ω * ω := mul_lt_mul_of_pos_left (natCast_lt_omega0 _) omega0_pos
    _ = ω ^ 2 := (sq ω).symm

/-- **The range clause implies the coding clause**: the rows take values below `ω ^ 2`. -/
theorem HasPrintedRange.row_lt (h : R.HasPrintedRange) (s : ι) (t : D.below (D.gradedIndex s)) :
    R.row s t < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := by
  rcases h s t with h | ⟨n, i, -, h⟩
  · rw [h]
    exact WithBot.bot_lt_coe _
  · rw [h]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (omega0_mul_add_natCast_lt_omega0_sq n i))

end CellScheme.Rows

namespace Scheme

open CellScheme CellScheme.Rows

variable {n : ℕ} {S : Scheme.{u} n} {θ : Ordinal.{u}}

/-- `ω ^ 2` is zero or a limit. -/
private theorem isSuccPrelimit_omega0_sq : Order.IsSuccPrelimit (ω ^ 2 : Ordinal.{u}) :=
  isSuccPrelimit_iff_omega0_dvd.mpr (dvd_pow_self ω two_ne_zero)

/-- The rows of a scheme with coded rows take values at every stage `θ ≥ ω ^ 2`. -/
theorem IsCoded.atStage (hS : S.IsCoded) (hθ : ω ^ 2 ≤ θ) (s t) : AtStage θ (S.rows.row s t) :=
  .inl ((hS s t).trans_le (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hθ)))

/-- **Legal schemes are legal templates, with the range clause** [AFK26, Definition 4.27]: a legal
scheme whose rows satisfy clause 4 satisfies the corrected definition at every stage `θ ≥ ω ^ 2`
that is zero or a limit. -/
theorem IsLegal.correctedLegal (hS : S.IsLegal) (hr : S.rows.HasPrintedRange)
    (hθ : Order.IsSuccPrelimit θ) (hθ2 : ω ^ 2 ≤ θ) : S.rows.CorrectedLegal θ where
  gradedIndex_mem := hS.isWellFormed.isWellFormed.gradedIndex_mem
  isComplete := hS.isComplete
  lawful d := (printedLawfulLocal_iff hθ (hS.isCoded.atStage hθ2)
    (hS.isCoded.atStage hθ2 d)).mpr (hS.isConsistent d)
  bountiful := hS.isBountiful.printedBountifulRows hθ hS.isWellFormed.isWellFormed.gradedIndex_mem
    (hS.isCoded.atStage hθ2)
  range := hr

/-- `ω ^ 2 < ω₁`. -/
private theorem omega0_sq_lt_omega_one : (ω ^ 2 : Ordinal.{u}) < Ordinal.omega 1 := by
  rw [sq, ← add_zero (ω * ω)]
  exact_mod_cast (omega0_mul_add_natCast_lt_omega_one_iff ω 0).mpr omega0_lt_omega_one

/-- **Legal schemes are legal templates of [AFK26, Definition 4.27] at `ω₁`**, corrected, when their
rows satisfy clause 4. -/
theorem IsLegal.correctedLegal_omega_one (hS : S.IsLegal) (hr : S.rows.HasPrintedRange) :
    S.rows.CorrectedLegal (Ordinal.omega 1) :=
  hS.correctedLegal hr (Cardinal.isSuccLimit_omega 1).isSuccPrelimit omega0_sq_lt_omega_one.le

/-- **Legal schemes with the range clause are the legal templates of [AFK26, Definition 4.27] at
every stage, with the extension of lawful labellings**: a scheme is legal and satisfies clause 4
exactly when it is well formed, satisfies the corrected definition at every stage `θ ≥ ω ^ 2` that
is zero or a limit, and every labelling lawful below a graded face extends to one lawful below
every larger graded face. -/
theorem isLegal_and_hasPrintedRange_iff :
    S.IsLegal ∧ S.rows.HasPrintedRange ↔
      S.IsWellFormed ∧
        (∀ θ : Ordinal.{u}, Order.IsSuccPrelimit θ → ω ^ 2 ≤ θ → S.rows.CorrectedLegal θ) ∧
        ∀ ⦃X Y : Finset (Fin n) × ℕ⦄, X ∈ S.toCellScheme.gradedFaces →
          Y ∈ S.toCellScheme.gradedFaces → ∀ hXY : X ≤ Y,
          Set.SurjOn (fun q' ↦ q' ∘ Set.inclusion (S.toCellScheme.below_mono hXY))
            {q | S.rows.IsLawfulBelow Y q} {p | S.rows.IsLawfulBelow X p} := by
  refine ⟨fun ⟨hS, hr⟩ ↦ ⟨hS.isWellFormed, fun θ hθ hθ2 ↦ hS.correctedLegal hr hθ hθ2,
    fun _ _ hX hY hXY ↦ IsBountiful.surjOn_isLawfulBelow _ hS.isBountiful hX hY hXY⟩,
    fun ⟨hw, h, hbot⟩ ↦ ?_⟩
  have h₀ := h _ isSuccPrelimit_omega0_sq le_rfl
  have hc : S.IsCoded := h₀.range.row_lt
  have := hw.isWellFormed.finite
  refine ⟨⟨hw, hc, fun d ↦ (printedLawfulLocal_iff isSuccPrelimit_omega0_sq
    (hc.atStage le_rfl) (hc.atStage le_rfl d)).mp (h₀.lawful d), ?_, h₀.isComplete⟩, h₀.range⟩
  exact isBountiful_of_forall_printedBountifulRows (ω ^ 2)
    (fun θ hθ hθ2 _ ↦ (h θ hθ hθ2).bountiful) hbot

/-! ### A legal scheme outside the range clause -/

/-- The one-point scheme with one cell of scope `{0}` and grade `1`, the faces `∅` and `{0}`, and
the row of value `2` at the cell. -/
private def rowTwo : Scheme.{0} 1 where
  card := 1
  toCellScheme := ⟨Finset.univ, Geometry.intervalPlan Finset.univ, fun _ ↦ Finset.univ, fun _ ↦ 1⟩
  rows := ⟨fun _ _ ↦ 2⟩

/-- The only graded face of `rowTwo` is `({0}, 1)`. -/
private theorem rowTwo_gradedFaces {X : Finset (Fin 1) × ℕ}
    (hX : X ∈ rowTwo.toCellScheme.gradedFaces) : X = (Finset.univ, 1) := by
  obtain ⟨C, j⟩ := X
  obtain ⟨_, hpos, hle⟩ := hX
  have hC : #C ≤ 1 := card_le_univ C
  simp only at hpos hle
  have hC' : C = Finset.univ := (card_eq_iff_eq_univ C).mp (by simp; omega)
  subst hC'
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  rw [show j = 1 by omega]

private theorem two_lt_omega0_sq : (2 : Label.{0}) < ((ω ^ 2 : Ordinal.{0}) : Label.{0}) := by
  have h2 : (2 : Ordinal.{0}) < ω ^ 2 := by
    calc (2 : Ordinal.{0}) < ω := (natCast_lt_omega0 2).trans_eq' (by simp)
      _ ≤ ω * ω := le_mul_left ω omega0_pos
      _ = ω ^ 2 := (sq ω).symm
  have e : ((2 : Ordinal.{0}) : Label.{0}) = 2 := by simp
  rw [← e]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr h2)

private theorem isLegal_rowTwo : rowTwo.IsLegal where
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun _ ↦ by
    simp [CellScheme.gradedIndex, rowTwo]⟩⟩
  isCoded _ _ := two_lt_omega0_sq
  isConsistent s := isLawfulBelow_iff.mpr
    { orderly := fun _ ↦ (isSelfVisible_ofNat 2).mpr (show 1 ≤ 2 by omega)
      locality := fun _ ↦ by
        convert TransformsTo.refl _ _ using 2
        exact min_self _
      availability := fun _ t _ _ ↦ ⟨t, rfl, le_rfl⟩ }
  isBountiful X Y hX hY h := by
    obtain rfl := rowTwo_gradedFaces hX
    obtain rfl := rowTwo_gradedFaces hY
    exact cappedLift_refl _
  isComplete X hX := ⟨(0 : Fin 1), by rw [rowTwo_gradedFaces hX]; rfl⟩

/-- **The range clause is not part of legality**: the one-point scheme whose row has the value `2`
at its cell of grade `1` is legal, and violates clause 4 of [AFK26, Definition 4.27]. -/
theorem exists_isLegal_not_hasPrintedRange :
    ∃ S : Scheme.{0} 1, S.IsLegal ∧ ¬ S.rows.HasPrintedRange := by
  refine ⟨rowTwo, isLegal_rowTwo, fun h ↦ ?_⟩
  rcases h (0 : Fin 1) ⟨(0 : Fin 1), CellScheme.mem_below_gradedIndex _ _⟩ with h | ⟨k, i, hi, h⟩
  · exact absurd h (by simp [rowTwo])
  · have hi1 : i ≤ 1 := hi
    have h2 : (2 : Ordinal.{0}) = ω * k + i := by
      have : ((2 : Ordinal.{0}) : Label.{0}) = ((ω * k + i : Ordinal.{0}) : Label.{0}) := by
        simpa [rowTwo] using h
      exact WithTop.coe_injective (WithBot.coe_injective this)
    cases k with
    | zero =>
      simp only [Nat.cast_zero, mul_zero, zero_add] at h2
      have : (2 : ℕ) = i := by exact_mod_cast h2
      omega
    | succ m =>
      have : ω ≤ ω * ((m + 1 : ℕ) : Ordinal.{0}) + i :=
        (le_mul_left ω (by exact_mod_cast Nat.succ_pos m)).trans le_self_add
      rw [← h2] at this
      exact absurd this (not_le.mpr ((natCast_lt_omega0 2).trans_eq' (by simp)))

end Scheme

end VaughtConjecture
