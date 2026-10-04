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
* forcing at a reindexed root is forcing at the transported cell
  (`ForcesThreshold.trans_comap_iff` along a bijection, which need not be monotone);
* the collapse above `ω + 3` sends `ω + 5` to the formal top and keeps `ω + 2`;
* **twins**: a scheme on two points with three cells of grade `1`, `s₀ = ({0}, 1)` and two twins of
  graded index `({0, 1}, 1)`, and two stage types at `ω + ω` on it, with the labels
  `(ω + 2, ω + 2, ω + 1)` and `(ω + 2, ω + 1, ω + 2)`, reducing to the same stage type at `ω`; the
  pointwise minimum of their labels satisfies the order law and locality
  (`Label.TransformsTo.inf`) but not availability, so it is the label section of no stage type on
  that scheme.  This shows why availability of a pointwise minimum of lifts is not unconditional;
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
  · -- `tie.toCellScheme` is `tieCells` by definition: `tie` is the reduction of `tieUp`, and the
    -- reduction keeps the cell scheme.
    change (⟨0, Nat.two_pos⟩ : Fin 2) ∈ tieCells.below (tieCells.gradedIndex ⟨1, Nat.one_lt_two⟩)
    simp [tieCells, CellScheme.gradedIndex, Prod.le_def]

/-! ### Faces of the root -/

/-- **Forcing at a reindexed root**: if `q` restricts to `p` along `h`, then for a bijection `e` of
the coordinates of `p`, forcing at `(q, e.trans h)` for the reindexed root at a cell `i` is forcing
at `(q, h)` for `p` at the transported cell; `e` need not be monotone, and cells are matched by
position. -/
example {q : StageType.{u} β m} {h : Fin k ↪ Fin m} {p : StageType.{u} β k}
    (hp : restrictFace h q = some p) (e : Fin k ≃ Fin k) (i : Fin (p.reindex e).card) (n : ℕ) :
    ForcesThreshold α hβ q (e.toEmbedding.trans h) (p.reindex e) i n ↔
      ForcesThreshold α hβ q h p (p.cellMap e.toEmbedding i) n :=
  ForcesThreshold.trans_comap_iff hp _ i

/-! ### Collapse above a threshold -/

/-- The collapse above `ω + 3` sends `ω + 5` to the formal top and keeps `ω + 2`. -/
example : Label.collapse ω 3 ((ω + (5 : ℕ) : Ordinal.{u}) : Label.{u}) = ⊤ ∧
    Label.collapse ω 3 ((ω + (2 : ℕ) : Ordinal.{u}) : Label.{u}) =
      ((ω + (2 : ℕ) : Ordinal.{u}) : Label.{u}) := by
  refine ⟨Label.reduce_of_le ?_, Label.reduce_of_lt (not_le.mp fun h ↦ ?_)⟩ <;>
    simp only [WithBot.coe_le_coe, WithTop.coe_le_coe, add_le_add_iff_left, Nat.cast_le] at *
  · omega
  · exact absurd (Nat.cast_le.mp h) (by omega)

/-! ### Twins: the pointwise minimum of two lawful lifts -/

/-- Three cells of grade `1` on two points: `s₀ = 0` of scope `{0}`, and the twins `1` and `2` of
scope `{0, 1}`, which share their graded index. -/
private def twinCells : CellScheme (Fin 3) (Fin 2) :=
  ⟨univ, Geometry.intervalPlan univ, ![{0}, univ, univ], fun _ ↦ 1⟩

/-- The label `ω + 1`. -/
private abbrev omegaOne : Label.{0} := ((ω + (1 : ℕ) : Ordinal.{0}) : Label.{0})

/-- `ω + 1 < ω + 2`. -/
private theorem omegaOne_lt_omegaTwo : omegaOne < omegaTwo :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (add_lt_add_right (Nat.cast_lt.mpr one_lt_two) ω))

/-- The first lift: `ω + 2` at `s₀` and at the first twin, `ω + 1` at the second. -/
private def twinSection₁ : Fin 3 → Label.{0} := ![omegaTwo, omegaTwo, omegaOne]

/-- The second lift: `ω + 2` at `s₀` and at the second twin, `ω + 1` at the first. -/
private def twinSection₂ : Fin 3 → Label.{0} := ![omegaTwo, omegaOne, omegaTwo]

/-- The rows: the constant `ω + 2` at `s₀`, and the labels of the lift that is high at the twin
itself at each twin. -/
private def twinRows : twinCells.Rows.{0} :=
  ⟨fun s d ↦ if s = 1 then twinSection₁ d.1 else if s = 2 then twinSection₂ d.1 else omegaTwo⟩

/-- Every label of the twins example is `ω + 1` or `ω + 2`. -/
private theorem twin_values (d : Fin 3) :
    (twinSection₁ d = omegaOne ∨ twinSection₁ d = omegaTwo) ∧
      (twinSection₂ d = omegaOne ∨ twinSection₂ d = omegaTwo) := by
  fin_cases d <;> simp [twinSection₁, twinSection₂]

/-- Every label of the twins example is at most `ω + 2`. -/
private theorem twin_le (d : Fin 3) : twinSection₁ d ≤ omegaTwo ∧ twinSection₂ d ≤ omegaTwo := by
  fin_cases d <;> simp [twinSection₁, twinSection₂, omegaOne_lt_omegaTwo.le]

/-- Below `s₀` there is only `s₀`. -/
private theorem eq_zero_of_mem_below {d : Fin 3}
    (hd : d ∈ twinCells.below (twinCells.gradedIndex 0)) : d = 0 := by
  have hs : twinCells.scope d ⊆ {0} := hd.1
  revert hs
  fin_cases d <;> decide

/-- Locality of the twins example from the cap rule: if `min (p d) (p s)` agrees with the row of
`s`, capped at `p s`, below `s`, then locality holds at `s`. -/
private theorem locality_twin {p : Fin 3 → Label.{0}} (s : Fin 3) (hs : Label.IsSelfVisible 1 (p s))
    (h : ∀ d : twinCells.below (twinCells.gradedIndex s),
      min (p d) (p s) = min (twinRows.row s d) (p s)) :
    Label.TransformsTo (fun d : twinCells.below (twinCells.gradedIndex s) ↦ twinCells.grade d)
      (twinRows.row s) (fun d ↦ min (p d) (p s)) := by
  have := (Label.TransformsTo.refl (fun d : twinCells.below (twinCells.gradedIndex s) ↦
    twinCells.grade d) (twinRows.row s)).min_const (K := 1) (fun _ ↦ le_rfl) hs
  convert this using 1
  exact funext h

/-- `ω + 1` and `ω + 2` are self-visible at the grade `1`. -/
private theorem isSelfVisible_twin {x : Label.{0}} (hx : x = omegaOne ∨ x = omegaTwo) :
    Label.IsSelfVisible 1 x := by
  rcases hx with rfl | rfl <;>
    exact Label.isSelfVisible_coe_add isSuccLimit_omega0.isSuccPrelimit (by omega)

/-- The first lift is lawful. -/
private theorem isLawful_twinSection₁ : twinRows.IsLawful twinSection₁ where
  orderly d := isSelfVisible_twin (twin_values d).1
  locality s := locality_twin s (isSelfVisible_twin (twin_values s).1) fun ⟨d, hd⟩ ↦ by
    fin_cases s
    · obtain rfl := eq_zero_of_mem_below hd; rfl
    · fin_cases d <;> simp [twinRows, twinSection₁, omegaOne_lt_omegaTwo.le]
    · fin_cases d <;> simp [twinRows, twinSection₁, twinSection₂, omegaOne_lt_omegaTwo.le]
  availability s t _ _ := ⟨if t = 0 then 0 else 1, by fin_cases t <;> rfl,
    (twin_le s).1.trans_eq (by fin_cases t <;> rfl)⟩

/-- The second lift is lawful. -/
private theorem isLawful_twinSection₂ : twinRows.IsLawful twinSection₂ where
  orderly d := isSelfVisible_twin (twin_values d).2
  locality s := locality_twin s (isSelfVisible_twin (twin_values s).2) fun ⟨d, hd⟩ ↦ by
    fin_cases s
    · obtain rfl := eq_zero_of_mem_below hd; rfl
    · fin_cases d <;> simp [twinRows, twinSection₁, twinSection₂, omegaOne_lt_omegaTwo.le]
    · fin_cases d <;> simp [twinRows, twinSection₂, omegaOne_lt_omegaTwo.le]
  availability s t _ _ := ⟨if t = 0 then 0 else 2, by fin_cases t <;> rfl,
    (twin_le s).2.trans_eq (by fin_cases t <;> rfl)⟩

/-- Every row value of the twins example is at most `ω + 2`. -/
private theorem twinRows_le (s : Fin 3) (d : twinCells.below (twinCells.gradedIndex s)) :
    twinRows.row s d ≤ omegaTwo := by
  unfold twinRows
  dsimp only
  split_ifs
  exacts [(twin_le _).1, (twin_le _).2, le_rfl]

/-- The stage type at `λ_1 = ω + ω` on the scheme of the twins example with a lawful labelling
bounded by `ω + 2`. -/
private noncomputable def twinUp (p : Fin 3 → Label.{0}) (hp : twinRows.IsLawful p)
    (hle : ∀ d, p d ≤ omegaTwo) : StageType.{0} (blockStage (0 + 1)) 2 where
  card := 3
  toCellScheme := twinCells
  rows := twinRows
  label := p
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, by
    intro d; fin_cases d <;> simp [twinCells, CellScheme.gradedIndex, Geometry.mem_intervalPlan]⟩⟩
  isCoded s d := (twinRows_le s d).trans_lt
    (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr omegaTwo_lt_sq))
  isLawful := hp
  atStage d := Or.inl ((hle d).trans_lt (by
    rw [blockStage_add_one, blockStage_zero]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr omegaTwo_lt)))

/-- **Twins**: two stage types at `λ_1 = ω + ω` on one scheme, with the labels
`(ω + 2, ω + 2, ω + 1)` and `(ω + 2, ω + 1, ω + 2)`, are lifts of one stage type at `λ_0 = ω`
(their reductions are equal, every label reducing to the formal top).  The pointwise minimum
`(ω + 2, ω + 1, ω + 1)` of their labels satisfies the order law and locality, the latter by
`Label.TransformsTo.inf`, but not availability: `s₀` has the scope `{0} ⊆ {0, 1}` and the grade of
the twins, and in the pointwise minimum both twins carry `ω + 1`, below its label `ω + 2`.  So no
stage type on this scheme carries the pointwise minimum.  This is a statement about stage types
only; no realization is involved.  It is why availability of a pointwise minimum of lifts is not
unconditional. -/
example :
    (twinUp _ isLawful_twinSection₁ fun d ↦ (twin_le d).1).reduce (isSuccPrelimit_blockStage 0) =
      (twinUp _ isLawful_twinSection₂ fun d ↦ (twin_le d).2).reduce (isSuccPrelimit_blockStage 0) ∧
    (∀ d, Label.IsSelfVisible (twinCells.grade d) ((twinSection₁ ⊓ twinSection₂) d)) ∧
    (∀ s, Label.TransformsTo (fun d : twinCells.below (twinCells.gradedIndex s) ↦ twinCells.grade d)
      (twinRows.row s) (fun d ↦ min ((twinSection₁ ⊓ twinSection₂) d)
        ((twinSection₁ ⊓ twinSection₂) s))) ∧
    ¬ twinRows.IsLawful (twinSection₁ ⊓ twinSection₂) := by
  have hω (x : Label.{0}) (hx : x = omegaOne ∨ x = omegaTwo) :
      Label.reduce (blockStage 0) x = ⊤ := by
    rw [blockStage_zero]
    exact Label.reduce_of_le (by rcases hx with rfl | rfl <;>
      exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add))
  refine ⟨StageType.ext rfl fun i j hij ↦ ?_,
    fun d ↦ (isLawful_twinSection₁.orderly d).min (isLawful_twinSection₂.orderly d),
    fun s ↦ ?_, fun h ↦ ?_⟩
  · obtain rfl : (i : Fin 3) = j := Fin.ext hij
    exact (hω _ (twin_values i).1).trans (hω _ (twin_values i).2).symm
  · convert (isLawful_twinSection₁.locality s).inf (isLawful_twinSection₂.locality s) using 1
    funext d
    exact inf_inf_inf_comm _ _ _ _
  · obtain ⟨u, hu, hle⟩ := h.availability 0 1 (by simp [twinCells]) rfl
    have h0 : (twinSection₁ ⊓ twinSection₂) 0 = omegaTwo := inf_idem _
    rw [h0] at hle
    fin_cases u
    · simp [twinCells, CellScheme.gradedIndex] at hu
    · exact not_le.mpr omegaOne_lt_omegaTwo
        (hle.trans_eq (inf_eq_right.mpr omegaOne_lt_omegaTwo.le))
    · exact not_le.mpr omegaOne_lt_omegaTwo
        (hle.trans_eq (inf_eq_left.mpr omegaOne_lt_omegaTwo.le))

/-! ### Suprema in `ℕ∞` -/

/-- The characterization of `n ≤ ⨆ i, f i` by a single term needs `n ≠ 0`: over an empty index the
supremum is `0`, at least `0`, but there is no term. -/
example (f : Empty → ℕ∞) : ((0 : ℕ) : ℕ∞) ≤ ⨆ i, f i ∧ ¬ ∃ i, ((0 : ℕ) : ℕ∞) ≤ f i :=
  ⟨zero_le, fun ⟨i, _⟩ ↦ i.elim⟩

end VaughtConjecture.Stage.ThresholdExamples
