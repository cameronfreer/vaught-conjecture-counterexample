/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryCoatom
import VaughtConjecture.Extension.CodedSection

/-!
# A coded reading labelling on every labelled extension

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the private cap and the decoder of (R4)) with 3.1 (the completion of the coatom extension);
semantic contract, items 3 and 8.

The reading coatom completion (`StageType.HasReadingCoatomCompletions`, open) asks for the cells of
full scope at `(univ, N)` of a coatom extension to read the new cells of the coface `D` through the
cap.  Such a row is a labelling of the cells below `(univ, N)`: it must be lawful there
(consistency) and coded, and it must read the reference cells and the new cells of `D` in one block
per label block.  This file shows that the cells of every labelled extension carry such a
labelling, whatever the intermediate coface, so the open part of the reading coatom completion is
the completion at the cells of full scope.  Each item below is compiled in this repository (theorem
named), unless marked otherwise.

**Reading through the cap at the level of values** (`StageType.ReadsThroughCapAt`).  A labelling
`r` of the cells of a scheme `E` reads a cell `e` through the cap `b` as a cell labelled `ℓ` when
`r e` is `⊥` for `ℓ = ⊥`, `r e = r b` for `ℓ = ⊤`, and for `ℓ = μ + n` (`μ` zero or a limit) `r`
reads `e` at `ω · c + n` and some reference cell of `T⁺` labelled `μ + i` at `ω · c + i`, with
`n, i` below the grade of the cap.  A cell at `(univ, N)` whose row agrees with `r` reads `e`
through the cap (`StageType.readsThroughCap_of_row_eq`): the reading clause of
`StageType.ReadsThroughCap` is a condition on the values of one labelling.

**The coded reading labelling** (`StageType.exists_codedReadingLabelling`).  Let `A` be a stage
type at `λ_{ξ+1}` on `m + 1` points whose faces along the first points and along `f` followed by
the new point are `T⁺` and `D`, labels included (for instance the amalgam of a seed, whose labels
are the glued labels, or any coatom extension), and let `b` be a graded cap of `T⁺` for `D`
(`StageType.IsGradedCap`) of grade `N`.  The labels of `A` capped at the label of the cap are
lawful below `(univ, N)` (the cap is self-visible at `N`, `CellScheme.Rows.IsLawfulBelow.min_const_
of_isSelfVisible`); their coded copy (`Label.blockEncode`, `CellScheme.Rows.IsLawful.exists_
blockEncode`) is lawful below `(univ, N)`, coded, at most its value at the cap, and reads every new
cell of `D` through the cap: a label `μ + n` and its reference value `μ + i` lie in one value block
and are coded as `ω · r + n` and `ω · r + i`; the formal top is capped to the label of the cap;
`⊥` is coded as `⊥`.  The scope of the cap is not used.

**What is left of the reading coatom completion** (argued, not formalized).  In a completion of the
amalgam of the last coatom pair, a cell at `(univ, N)` whose row is the coded reading labelling on
the old cells reads through the cap (`StageType.readsThroughCap_of_row_eq`); the labelling is
lawful for the rows of the old cells, whatever the intermediate coface.  What is not constructed is
the rest: the rows of the new cells of full scope at every grade, the values of the reading rows at
the new cells of grade at most `N`, and consistency and bountifulness across them; that is, a
completion below the full grade (`CompletionBelowFullGrade`) whose layer at `(univ, N)` reads
through the cap.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label StageType
open Ordinal hiding univ

namespace StageType

variable {m k : ℕ}

/-! ### Reading through the cap at the level of values -/

/-- A labelling `r` of the cells of a scheme `E` on `m + 1` points **reads `e` through the cap `b`**
(a cell of the face along the first `m` points) as a cell labelled `ℓ`, relative to a stage type
`T⁺` on those points: `r e = ⊥` if `ℓ = ⊥`; `r e = r b` if `ℓ = ⊤`; and if `ℓ = μ + n` with `μ`
zero or a limit, `n` is below the grade of `b` and `r` reads `e` at `ω · c + n` and a reference
cell of `T⁺` labelled `μ + i` at `ω · c + i`, with `i` below the grade of `b` and the reference cell
of grade at most that of `b`. -/
def ReadsThroughCapAt {α : Ordinal.{u}} (Tp : StageType.{u} α m) (E : Scheme.{u} (m + 1))
    (r : Fin E.card → Label.{u}) (b : Fin (E.comap Fin.castSuccEmb).card) (e : Fin E.card)
    (ℓ : Label.{u}) : Prop :=
  (ℓ = ⊥ → r e = ⊥) ∧ (ℓ = ⊤ → r e = r (E.cellMap Fin.castSuccEmb b)) ∧
    ∀ (μ : Ordinal.{u}) (n : ℕ), Order.IsSuccPrelimit μ →
      ℓ = ((μ + n : Ordinal.{u}) : Label.{u}) →
        n < E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b) ∧
        ∃ (a : Fin (E.comap Fin.castSuccEmb).card) (a₀ : Fin Tp.card) (i : ℕ) (c : Ordinal.{u}),
          (a : ℕ) = a₀ ∧ Tp.label a₀ = ((μ + i : Ordinal.{u}) : Label.{u}) ∧
          i < E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b) ∧
          E.toCellScheme.grade (E.cellMap Fin.castSuccEmb a) ≤
            E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b) ∧
          r (E.cellMap Fin.castSuccEmb a) = ((ω * c + i : Ordinal.{u}) : Label.{u}) ∧
          r e = ((ω * c + n : Ordinal.{u}) : Label.{u})

/-- **A row agreeing with a reading labelling reads through the cap**: if the row of a cell `u` at
the graded face `(univ, N)`, `N` the grade of the cap `b`, agrees with a labelling `r` on the cells
below `u`, and `r` reads `e` through `b` as a cell labelled `ℓ` (`StageType.ReadsThroughCapAt`),
then `u` reads `e` through `b` (`StageType.ReadsThroughCap`).  The reference cell lies below `u`,
being of grade at most `N`. -/
theorem readsThroughCap_of_row_eq {α : Ordinal.{u}} {Tp : StageType.{u} α m}
    {E : Scheme.{u} (m + 1)} {r : Fin E.card → Label.{u}}
    {b : Fin (E.comap Fin.castSuccEmb).card} {u e : Fin E.card} {ℓ : Label.{u}}
    (hu : E.toCellScheme.gradedIndex u =
      ((univ : Finset (Fin (m + 1))), E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b)))
    (hrow : ∀ (d : Fin E.card) (hd : d ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u)),
      E.rows.row u ⟨d, hd⟩ = r d)
    (h : Tp.ReadsThroughCapAt E r b e ℓ) : Tp.ReadsThroughCap E b u e ℓ := by
  obtain ⟨hbot, htop, hord⟩ := h
  intro he hb
  refine ⟨fun hℓ ↦ by rw [hrow, hbot hℓ], fun hℓ ↦ by rw [hrow, hrow, htop hℓ],
    fun μ n hμ hℓ ↦ ?_⟩
  obtain ⟨hn, a, a₀, i, c, haa₀, ha₀, hi, hag, hra, hre⟩ := hord μ n hμ hℓ
  have ha : E.cellMap Fin.castSuccEmb a ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u) := by
    rw [CellScheme.mem_below, hu]
    exact ⟨subset_univ _, hag⟩
  exact ⟨hn, a, a₀, i, c, haa₀, ha₀, hi, ha, by rw [hrow, hra], by rw [hrow, hre]⟩

/-- **A cap-reading extension from one reading labelling**: a legal scheme `E` with the faces of a
cap-reading extension, a cell `b'` of its first face at the position of `b`, and a labelling `r`
reading every new cell of `D` through `b'` (`StageType.ReadsThroughCapAt`), such that every cell at
`(univ, N)` has `r` as its row, is a cap-reading extension (`StageType.IsCapReadingExtension`). -/
theorem IsCapReadingExtension.of_row_eq {α : Ordinal.{u}} {Tp : StageType.{u} α m}
    {f : Fin k ↪ Fin m} {D : StageType.{u} α (k + 1)} {b : Fin Tp.card} {E : Scheme.{u} (m + 1)}
    (hE : E.IsLegal) (hc : univ.map Fin.castSuccEmb ∈ E.toCellScheme.faces)
    (hT : E.comap Fin.castSuccEmb = Tp.toScheme)
    (hf : univ.map (extendByLast f) ∈ E.toCellScheme.faces)
    (hED : E.comap (extendByLast f) = D.toScheme) {b' : Fin (E.comap Fin.castSuccEmb).card}
    (hb' : (b' : ℕ) = b) {r : Fin E.card → Label.{u}}
    (hread : ∀ (i : Fin (E.comap (extendByLast f)).card) (j : Fin D.card), (i : ℕ) = j →
      Fin.last k ∈ D.toCellScheme.scope j →
        Tp.ReadsThroughCapAt E r b' (E.cellMap (extendByLast f) i) (D.label j))
    (hrow : ∀ u, E.toCellScheme.gradedIndex u =
        ((univ : Finset (Fin (m + 1))), Tp.toCellScheme.grade b) →
      ∀ (d : Fin E.card) (hd : d ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u)),
        E.rows.row u ⟨d, hd⟩ = r d) :
    IsCapReadingExtension Tp f D b E := by
  have hg : E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b') = Tp.toCellScheme.grade b :=
    Scheme.grade_congr hT hb'
  refine ⟨hE, hc, hT, hf, hED, b', hb', fun u hu i j hij hj ↦ ?_⟩
  exact readsThroughCap_of_row_eq (hu.trans (by rw [hg])) (hrow u hu) (hread i j hij hj)

/-! ### The coded reading labelling -/

variable {ξ : Ordinal.{u}}

/-- **The coded reading labelling.**  Let `A` be a stage type at `λ_{ξ+1}` on `m + 1` points whose
faces along the first points and along `f` followed by the new point are `T⁺` and `D`, labels
included, and let `b` be a graded cap of `T⁺` for `D` and `γ` (`StageType.IsGradedCap`) of grade
`N`.  Then some labelling `r` of the cells of `A` is lawful below `(univ, N)`, coded (below
`ω ^ 2`), at most its value at the cap, and reads every new cell of `D` through the cap
(`StageType.ReadsThroughCapAt`).  It is the coded copy (`Label.blockEncode`) of the labels of `A`
capped at the label of the cap. -/
theorem exists_codedReadingLabelling {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {f : Fin k ↪ Fin m} {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    {b : Fin Tp.card} (hcap : IsGradedCap ξ Tp D γ b)
    {A : StageType.{u} (blockStage (ξ + 1)) (m + 1)}
    (hAT : restrictFace Fin.castSuccEmb A = some Tp)
    (hAD : restrictFace (extendByLast f) A = some D) :
    ∃ r : Fin A.card → Label.{u},
      A.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), Tp.toCellScheme.grade b)
        (fun d ↦ r d) ∧
      (∀ d, r d < ((ω ^ 2 : Ordinal.{u}) : Label.{u})) ∧
      ∀ b' : Fin (A.toScheme.comap Fin.castSuccEmb).card, (b' : ℕ) = b →
        (∀ d, r d ≤ r (A.cellMap Fin.castSuccEmb b')) ∧
        ∀ (i : Fin (A.toScheme.comap (extendByLast f)).card) (j : Fin D.card), (i : ℕ) = j →
          Fin.last k ∈ D.toCellScheme.scope j →
            Tp.ReadsThroughCapAt A.toScheme r b' (A.cellMap (extendByLast f) i) (D.label j) := by
  obtain ⟨hcT, hAT'⟩ := (restrictFace_eq_some_iff A _).mp hAT
  obtain ⟨hcD, hAD'⟩ := (restrictFace_eq_some_iff A _).mp hAD
  obtain ⟨hb₀, hkN, -, href⟩ := hcap
  set N := Tp.toCellScheme.grade b
  set c := Tp.label b
  set X : Finset (Fin (m + 1)) × ℕ := ((univ : Finset (Fin (m + 1))), N)
  -- the labels of `A` capped at the label of the cap, lawful below `(univ, N)`
  have hcN : IsSelfVisible N c := Tp.isLawful.orderly b
  have hl : A.rows.IsLawfulBelow X (fun d ↦ min (A.label d) c) :=
    (A.isLawful.isLawfulBelow X).min_const_of_isSelfVisible hcN
  obtain ⟨V, hV, hVl⟩ :=
    CellScheme.Rows.IsLawful.exists_blockEncode (CellScheme.Rows.isLawfulBelow_iff.mp hl)
      (K := N) fun d ↦ d.2.2
  refine ⟨fun d ↦ blockEncode V N (min (A.label d) c), CellScheme.Rows.isLawfulBelow_iff.mpr hVl,
    fun d ↦ blockEncode_lt _, fun b' hb' ↦ ?_⟩
  -- the cap of `A`: its label is that of the cap of `T⁺`
  have hlb : A.label (A.cellMap Fin.castSuccEmb b') = c := label_congr hAT' hb'
  have hgb : A.toCellScheme.grade (A.cellMap Fin.castSuccEmb b') = N :=
    Scheme.grade_congr (congrArg StageType.toScheme hAT') hb'
  refine ⟨fun d ↦ monotone_blockEncode (by rw [hlb, min_self]; exact min_le_right _ _),
    fun i j hij hj ↦ ?_⟩
  have hle : A.label (A.cellMap (extendByLast f) i) = D.label j := label_congr hAD' hij
  refine ⟨fun h ↦ by simp only [hle, h, bot_le, min_eq_left, blockEncode_bot],
    fun h ↦ by simp only [hle, h, hlb, min_self, le_top, min_eq_right], ?_⟩
  intro μ n hμ h
  -- the reference cell of the calibration, in the block `μ`
  obtain ⟨μ', n', i, a₀, hμ', ho, hn, hi, ha₀N, ha₀⟩ := href j (μ + n) h
  obtain ⟨rfl, rfl⟩ := (add_natCast_eq_add_natCast_iff hμ hμ').mp ho
  obtain ⟨c₀, rfl⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hμ
  -- the block `ω · c₀` is at most `λ_ξ`, since the label of `D` lies below `λ_{ξ+1}`
  have hlt : ω * c₀ + n < blockStage ξ + ω := by
    rcases D.atStage j with h' | h'
    · rw [h, blockStage_add_one] at h'
      exact_mod_cast h'
    · rw [h] at h'
      exact absurd h' (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne
  have hμξ : ω * c₀ ≤ blockStage ξ := by
    by_contra hμξ
    exact (add_omega0_le_of_isSuccPrelimit hμ (not_le.mp hμξ)).not_gt
      ((le_self_add).trans_lt hlt)
  -- every value `ω · c₀ + x` with `x < N` lies below the cap
  have hbelow (x : ℕ) (hx : x < N) : ((ω * c₀ + x : Ordinal.{u}) : Label.{u}) < c := by
    refine lt_of_lt_of_le ?_ hb₀
    have : ω * c₀ + x < blockStage ξ + N := by
      rcases hμξ.lt_or_eq with hμξ | hμξ
      · exact ((isSuccPrelimit_blockStage ξ).add_natCast_lt hμξ x).trans_le le_self_add
      · rw [hμξ]
        exact add_lt_add_right (Nat.cast_lt.mpr hx) _
    exact_mod_cast this
  -- the reference cell in `A`, and its capped label in the value set
  have hcard : (A.toScheme.comap Fin.castSuccEmb).card = Tp.card :=
    congrArg (fun t : StageType.{u} _ m ↦ t.card) hAT'
  set a : Fin (A.toScheme.comap Fin.castSuccEmb).card := Fin.cast hcard.symm a₀
  have hla : A.label (A.cellMap Fin.castSuccEmb a) = ((ω * c₀ + i : Ordinal.{u}) : Label.{u}) :=
    (label_congr hAT' rfl).trans ha₀
  have hga : A.toCellScheme.grade (A.cellMap Fin.castSuccEmb a) = Tp.toCellScheme.grade a₀ :=
    Scheme.grade_congr (congrArg StageType.toScheme hAT') rfl
  have haX : A.cellMap Fin.castSuccEmb a ∈ A.toCellScheme.below X := by
    rw [CellScheme.mem_below]
    exact ⟨subset_univ _, hga.trans_le ha₀N⟩
  have hmin (x : ℕ) (hx : x < N) :
      min ((ω * c₀ + x : Ordinal.{u}) : Label.{u}) c = ((ω * c₀ + x : Ordinal.{u}) : Label.{u}) :=
    min_eq_left (hbelow x hx).le
  have hV' : ((ω * c₀ + i : Ordinal.{u}) : Label.{u}) ∈ V := by
    have := hV ⟨_, haX⟩
    simp only [hla, hmin i hi] at this
    exact this
  have hblock : (ω * c₀ + i) / ω ∈ valueBlocks V := div_mem_valueBlocks hV'
  -- the coding of a value of the block `ω · c₀`
  have hcode (x : ℕ) : blockEncode V N ((ω * c₀ + x : Ordinal.{u}) : Label.{u}) =
      ((ω * (codeRank V c₀ : Ordinal.{u}) + x : Ordinal.{u}) : Label.{u}) := by
    have hdiv (y : ℕ) : (ω * c₀ + y) / ω = c₀ := by
      rw [Ordinal.mul_add_div _ omega0_ne_zero, Ordinal.div_eq_zero_of_lt (natCast_lt_omega0 y),
        add_zero]
    rw [hdiv] at hblock
    rw [blockEncode_coe, blockEncodeOrd, hdiv, ite_eq_left hblock, Ordinal.mul_add_mod_self,
      Ordinal.mod_eq_of_lt (natCast_lt_omega0 x)]
  refine ⟨hgb ▸ hn, a, a₀, i, (codeRank V c₀ : Ordinal.{u}), rfl, ha₀, hgb ▸ hi,
    by rw [hga, hgb]; exact ha₀N, ?_, ?_⟩
  · simp only [hla, hmin i hi, hcode]
  · simp only [hle, h, hmin n hn, hcode]

end StageType

end VaughtConjecture
