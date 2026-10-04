/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Tactic.FinCases
import VaughtConjecture.Geometry.IntervalPlan
import VaughtConjecture.Realization.Expansion
import VaughtConjecture.Stage.Threshold

/-!
# Examples for forcing thresholds and the provisional offset

Special cases of `VaughtConjecture.Stage.Threshold`:

* at the block index `η = 0` (`λ_0 = ω`, `λ_1 = ω + ω`): forcing by the order law, and the label
  of the offset `3`, which is `ω + 3`;
* the infinite offset: its label is the formal top, which is not `β + ω`;
* forcing is never vacuous: the type read at the larger stage reduces to it;
* forcing along a composite of two extensions, and along a permutation of the root (an embedding
  that is not monotone);
* **a tie**: a stage type at `ω` on two points with cells `e = ({0}, 1)` and `C = ({0, 1}, 2)`,
  both labelled the formal top, the reduction of the type at `ω + ω` with both labels and every
  row value `ω + 2`; the tie lemma forces the threshold `2` at `e`, above the grade `1` of `e`
  given by the order law;
* the threshold characterization of a supremum needs `n ≠ 0`: over an empty index the supremum is
  `0`, which is at least `0` although no term is.

## Placement

This file belongs to Layer 1 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Stage.ThresholdExamples

open Finset Ordinal StageType

variable {α β : Ordinal.{u}} {hβ : Order.IsSuccPrelimit β} {k m m' m'' : ℕ}

/-! ### The block index `η = 0` -/

/-- The block stages at `η = 0`: `λ_0 = ω` and `λ_1 = ω + ω`. -/
example : blockStage (0 + 1 : Ordinal.{u}) = ω + ω := by
  rw [blockStage_add_one, blockStage_zero]

/-- Forcing by the order law at `λ_0 = ω`: a pair restricting to the root forces the grade of a
cell whose label is the formal top. -/
example {q : StageType.{u} (blockStage 0) m} {f : Fin k ↪ Fin m}
    {p : StageType.{u} (blockStage 0) k} {d : Fin p.card} (hfp : restrictFace f q = some p)
    (hd : p.label d = ⊤) :
    ForcesThreshold (blockStage (0 + 1)) (isSuccPrelimit_blockStage 0) q f p d
      (p.toCellScheme.grade d) :=
  forcesThreshold_of_le_grade hfp hd le_rfl

/-- The label of the offset `3` above `λ_0` is `ω + 3`. -/
example : Label.ofOffset (blockStage (0 : Ordinal.{u})) ((3 : ℕ) : ℕ∞) =
    ((ω + 3 : Ordinal.{u}) : Label.{u}) := by
  rw [Label.ofOffset_natCast, blockStage_zero, Nat.cast_ofNat]

/-! ### The infinite offset -/

/-- The label of the infinite offset is the formal top, which is not `β + ω`. -/
example : Label.ofOffset β ⊤ = ⊤ ∧ Label.ofOffset β ⊤ ≠ ((β + ω : Ordinal.{u}) : Label.{u}) :=
  ⟨Label.ofOffset_top, Label.ofOffset_ne_coe_add_omega0⟩

/-- The thresholds of the infinite offset: every `β + n` lies below it. -/
example (n : ℕ) : ((β + n : Ordinal.{u}) : Label.{u}) ≤ Label.ofOffset β ⊤ :=
  Label.coe_add_le_ofOffset_iff.mpr le_top

/-! ### Forcing is never vacuous -/

/-- **Forcing is never vacuous**: for `β ≤ α`, the type `q` read at `α` reduces to `q`, so the
stage types quantified over in `ForcesThreshold` include it. -/
example (h : β ≤ α) (q : StageType.{u} β m) : (q.castLE h).reduce hβ = q := by
  rw [reduce_castLE, reduce_self]

/-! ### Forcing along extensions and permutations -/

/-- **Forcing along a composite of two extensions**: a threshold forced at `(q, f)` is forced at
`(q'', (f.trans g).trans g')` when `q` is the face of `q'` along `g` and `q'` that of `q''` along
`g'`; the provisional offset can only grow. -/
example {q : StageType.{u} β m} {q' : StageType.{u} β m'} {q'' : StageType.{u} β m''}
    {f : Fin k ↪ Fin m} {g : Fin m ↪ Fin m'} {g' : Fin m' ↪ Fin m''} {p : StageType.{u} β k}
    {d : Fin p.card} {n : ℕ} (hg : restrictFace g q' = some q)
    (hg' : restrictFace g' q'' = some q') (h : ForcesThreshold α hβ q f p d n) :
    ForcesThreshold α hβ q'' ((f.trans g).trans g') p d n ∧
      (n : ℕ∞) ≤ provisionalOffset α hβ q'' ((f.trans g).trans g') p d :=
  have h'' := (h.trans_face hg).trans_face hg'
  ⟨h'', h''.le_provisionalOffset⟩

/-- **Forcing along a permutation of the root**: the face of `q` along a bijection `e` is the
reindexed type, and the order law forces the grade of a cell labelled the formal top there.  The
embedding `e` need not be monotone. -/
example (q : StageType.{u} β k) (e : Fin k ≃ Fin k) {d : Fin (q.reindex e).card}
    (hd : (q.reindex e).label d = ⊤) :
    ForcesThreshold α hβ q e.toEmbedding (q.reindex e) d
      ((q.reindex e).toCellScheme.grade d) :=
  forcesThreshold_of_le_grade (restrictFace_equiv q e) hd le_rfl

/-- The provisional offset is at least the grade, by the order law. -/
example {q : StageType.{u} β m} {f : Fin k ↪ Fin m} {p : StageType.{u} β k} {d : Fin p.card}
    (hfp : restrictFace f q = some p) (hd : p.label d = ⊤) :
    (p.toCellScheme.grade d : ℕ∞) ≤ provisionalOffset α hβ q f p d :=
  grade_le_provisionalOffset hfp hd

/-! ### A tie -/

/-- The cell scheme on two points with the cells `e = ({0}, 1)` and `C = ({0, 1}, 2)`, whose faces
are the intervals. -/
private def tieCells : CellScheme (Fin 2) (Fin 2) :=
  ⟨univ, Geometry.intervalPlan univ, ![{0}, univ], ![1, 2]⟩

/-- The label `ω + 2`. -/
private abbrev omegaTwo : Label.{0} := ((ω + (2 : ℕ) : Ordinal.{0}) : Label.{0})

/-- The ordinal `ω + 2` lies below `ω + ω`. -/
private theorem omegaTwo_lt : (ω + (2 : ℕ) : Ordinal.{0}) < ω + ω :=
  add_lt_add_right (natCast_lt_omega0 2) ω

/-- The ordinal `ω + 2` lies below `ω ^ 2`: its row values are coded. -/
private theorem omegaTwo_lt_sq : (ω + (2 : ℕ) : Ordinal.{0}) < ω ^ (2 : ℕ) := by
  have h : ω < (ω ^ (2 : ℕ) : Ordinal.{0}) := by
    rw [pow_two]; exact lt_mul_of_one_lt_right omega0_pos one_lt_omega0
  have h2 : ((2 : ℕ) : Ordinal.{0}) < ω ^ (2 : ℕ) := (natCast_lt_omega0 2).trans h
  rw [← opow_natCast] at h h2 ⊢
  exact isPrincipal_add_omega0_opow _ h h2

/-- A stage type at `ω + ω` on two points with the cells `tieCells`, every label and every row
value `ω + 2`. -/
private def tieUp : StageType.{0} (blockStage (0 + 1)) 2 where
  card := 2
  toCellScheme := tieCells
  rows := ⟨fun _ _ ↦ omegaTwo⟩
  label _ := omegaTwo
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, by
    intro d; fin_cases d <;> simp [tieCells, CellScheme.gradedIndex, Geometry.mem_intervalPlan]⟩⟩
  isCoded _ _ := WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr omegaTwo_lt_sq)
  isLawful :=
    { orderly d := Label.isSelfVisible_coe_add isSuccLimit_omega0.isSuccPrelimit
        (by fin_cases d <;> simp [tieCells])
      locality _ := by simpa only [min_self] using Label.TransformsTo.refl _ _
      availability _ t _ _ := ⟨t, rfl, le_rfl⟩ }
  atStage _ := Label.atStage_coe.mpr (by
    rw [blockStage_add_one, blockStage_zero]; exact omegaTwo_lt)

/-- The stage type at `ω`: the reduction of `tieUp`, with both labels the formal top. -/
private noncomputable def tie : StageType.{0} (blockStage 0) 2 :=
  tieUp.reduce (isSuccPrelimit_blockStage 0)

/-- **A tie forcing above the order law**: at `(tie, id)`, the threshold `2` (the grade of `C`) is
forced at `e`, whose grade is `1`. -/
example : ForcesThreshold (blockStage (0 + 1)) (isSuccPrelimit_blockStage 0) tie
      (Function.Embedding.refl _) tie ⟨0, Nat.two_pos⟩ 2 ∧
    tie.toCellScheme.grade ⟨0, Nat.two_pos⟩ = 1 := by
  refine ⟨forcesThreshold_of_row_le (C := ⟨1, Nat.one_lt_two⟩) (e := ⟨0, Nat.two_pos⟩)
    (restrictFace_refl tie) (fun i hi ↦ ?_) ?_ ?_ le_rfl, rfl⟩
  · exact (tie.cellMap_eq_of_strictMono (Function.Embedding.refl _) strictMono_id
      (fun d ↦ by simp [Function.Embedding.coe_refl]) (j := i) hi.symm).symm
  · refine Label.reduce_of_le (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ?_))
    rw [blockStage_zero]
    exact le_self_add
  · change (⟨0, Nat.two_pos⟩ : Fin 2) ∈ tieCells.below (tieCells.gradedIndex ⟨1, Nat.one_lt_two⟩)
    simp [tieCells, CellScheme.gradedIndex, Prod.le_def]

/-! ### Suprema in `ℕ∞` -/

/-- The characterization of `n ≤ ⨆ i, f i` by a single term needs `n ≠ 0`: over an empty index the
supremum is `0`, at least `0`, but there is no term. -/
example (f : Empty → ℕ∞) : ((0 : ℕ) : ℕ∞) ≤ ⨆ i, f i ∧ ¬ ∃ i, ((0 : ℕ) : ℕ∞) ≤ f i :=
  ⟨zero_le, fun ⟨i, _⟩ ↦ i.elim⟩

end VaughtConjecture.Stage.ThresholdExamples
