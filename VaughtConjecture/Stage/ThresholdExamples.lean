/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.Expansion
import VaughtConjecture.Stage.Threshold

/-!
# Examples for forcing thresholds and the provisional offset

Special cases of `VaughtConjecture.Stage.Threshold`:

* at the block index `η = 0` (`λ_0 = ω`, `λ_1 = ω + ω`): forcing by the order law, and the label
  of the offset `3`, which is `ω + 3`;
* the infinite offset: its label is the formal top, which is not `β + ω`;
* forcing along a composite of two extensions, and along a permutation of the root (an embedding
  that is not monotone);
* the threshold characterization of a supremum needs `n ≠ 0`: over an empty index the supremum is
  `0`, which is at least `0` although no term is.

## Placement

This file belongs to Layer 1 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Stage.ThresholdExamples

open Ordinal StageType

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

/-! ### Suprema in `ℕ∞` -/

/-- The characterization of `n ≤ ⨆ i, f i` by a single term needs `n ≠ 0`: over an empty index the
supremum is `0`, at least `0`, but there is no term. -/
example (f : Empty → ℕ∞) : ((0 : ℕ) : ℕ∞) ≤ ⨆ i, f i ∧ ¬ ∃ i, ((0 : ℕ) : ℕ∞) ≤ f i :=
  ⟨zero_le, fun ⟨i, _⟩ ↦ i.elim⟩

end VaughtConjecture.Stage.ThresholdExamples
