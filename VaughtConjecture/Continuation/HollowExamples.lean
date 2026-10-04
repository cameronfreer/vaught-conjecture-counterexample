/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Hollow

/-!
# Examples for cover-hollowness and stable labels

Special cases of `VaughtConjecture.Continuation.Hollow`:

* **the block index `ξ = 0`** (`λ_0 = ω`, `λ_1 = ω + ω`): at a cell of an occurrence labelled the
  formal top, the stable label is the formal top or `ω + n` with `n` at least the grade of the cell
  (the order law, read through the trivial rooted cover); the stable offset `3` gives the stable
  label `ω + 3`;
* **anchors**: the bound of an anchor at the top is positive, and an anchor is a finite bound on the
  stable offset;
* **top-free realizations**: a realization whose occurrences all have arity `0` is top-free, hence
  cover-hollow vacuously; in a cover-hollow realization every threshold at a cell labelled the
  formal top is forced by some compatible rooted cover;
* **position matching**: along a permutation `e` of the root, the stable offset at the reindexed
  root and the tuple `c ∘ e` is the stable offset at the transported cell, with no hypothesis on the
  realization: along a permutation the rooted covers correspond.  The comparison along an
  arbitrary face of a typed tuple (output 1 of Layer 4) uses exact consistency and covering
  (`Realization.stableOffset_comap`, in `VaughtConjecture.Continuation.Candidate`).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture.Continuation.HollowExamples

open Ordinal Realization StageType

variable {α β ξ : Ordinal.{u}} {hβ : Order.IsSuccPrelimit β} {M : Type v} {k : ℕ}

/-! ### The block index `ξ = 0` -/

/-- **The order law for stable labels at `ξ = 0`**: at a cell labelled the formal top, the stable
label is the formal top or `ω + n` with `n` at least the grade of the cell. -/
example (R : Realization.{u, v} (blockStage 0) M) (x : R.Occurrence) (a : Fin x.type.card)
    (ha : x.type.label a = ⊤) :
    R.stableLabel (blockStage (0 + 1)) (isSuccPrelimit_blockStage 0) x.tuple x.type a = ⊤ ∨
      ∃ n : ℕ, x.type.toCellScheme.grade a ≤ n ∧
        R.stableLabel (blockStage (0 + 1)) (isSuccPrelimit_blockStage 0) x.tuple x.type a =
          ((ω + n : Ordinal.{u}) : Label.{u}) := by
  have hg : (x.type.toCellScheme.grade a : ℕ∞) ≤
      R.stableOffset (blockStage (0 + 1)) (isSuccPrelimit_blockStage 0) x.tuple x.type a :=
    (natCast_le_stableOffset_iff (covers_of_eval _ x.eval_tuple) ha).mpr
      ⟨⟨x.arity, x.type, Function.Embedding.refl _⟩,
        forcesThreshold_of_le_grade (restrictFace_refl _) ha le_rfl,
        x.tuple, rfl, covers_of_eval _ x.eval_tuple⟩
  rw [stableLabel]
  induction h : R.stableOffset (blockStage (0 + 1)) (isSuccPrelimit_blockStage 0) x.tuple x.type a
    using ENat.recTopCoe with
  | top => exact Or.inl Label.ofOffset_top
  | coe n =>
    rw [h] at hg
    exact Or.inr ⟨n, Nat.cast_le.mp hg, by rw [Label.ofOffset_natCast, blockStage_zero]⟩

/-- At `ξ = 0`, the stable offset `3` gives the stable label `ω + 3`. -/
example (R : Realization.{u, v} (blockStage 0) M) {c : Fin k → M}
    {p : StageType.{u} (blockStage 0) k} {d : Fin p.card}
    (h : R.stableOffset (blockStage (0 + 1)) (isSuccPrelimit_blockStage 0) c p d = (3 : ℕ)) :
    R.stableLabel (blockStage (0 + 1)) (isSuccPrelimit_blockStage 0) c p d =
      ((ω + 3 : Ordinal.{u}) : Label.{u}) := by
  rw [stableLabel, h, Label.ofOffset_natCast, blockStage_zero, Nat.cast_ofNat]

/-! ### Anchors -/

variable {R : Realization.{u, v} (blockStage ξ) M}

/-- The bound of an anchor at the top is positive. -/
example {x : R.Occurrence} {a : Fin x.type.card} {N : ℕ} (h : R.IsTopAnchor x a N) : 0 < N :=
  Nat.pos_of_ne_zero fun hN ↦ not_isTopAnchor_zero x a (hN ▸ h)

/-- **An anchor bounds the stable label**: an anchor `(x, a, N)` at the top gives a stable label
below `λ_ξ + N`. -/
example {x : R.Occurrence} {a : Fin x.type.card} {N : ℕ} (h : R.IsTopAnchor x a N) :
    R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) x.tuple x.type a <
      ((blockStage ξ + N : Ordinal.{u}) : Label.{u}) :=
  not_le.mp fun hle ↦ (isTopAnchor_iff_not_natCast_le_stableOffset h.1).mp h
    (Label.coe_add_le_ofOffset_iff.mp hle)

/-! ### Top-free realizations -/

/-- **A realization whose occurrences all have arity `0` is cover-hollow**, vacuously: a stage type
on no points has no cells. -/
example (h : ∀ x : R.Occurrence, x.arity = 0) : R.IsCoverHollow :=
  isCoverHollow_of_isTopFree fun x ↦ by
    obtain ⟨n, u, t, ht⟩ := x
    obtain rfl : n = 0 := h ⟨n, u, t, ht⟩
    exact isTopFree_of_zero t

/-- **Cover-hollowness, unfolded**: in a cover-hollow realization, every threshold at a cell of an
occurrence labelled the formal top is forced by some compatible rooted cover. -/
example (hh : R.IsCoverHollow) (x : R.Occurrence) (a : Fin x.type.card) (ha : x.type.label a = ⊤)
    (N : ℕ) : ∃ y : Σ m : ℕ, StageType.{u} (blockStage ξ) m × (Fin x.arity ↪ Fin m),
      ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) y.2.1 y.2.2 x.type a N ∧
        R.ExtendsToCover x.tuple y := by
  by_contra hN
  push Not at hN
  exact hh ⟨x, a, N, ha, fun y hy hf ↦ hN y hf hy⟩

/-! ### Position matching along a permutation of the root -/

/-- Forcing at a reindexed root is forcing at the transported cell, for every embedding `h`: when
`q` does not restrict to `p` along `h`, neither side holds. -/
private theorem forcesThreshold_reindex_iff {m : ℕ} {q : StageType.{u} β m} (h : Fin k ↪ Fin m)
    {p : StageType.{u} β k} (e : Fin k ≃ Fin k) (i : Fin (p.reindex e).card) (n : ℕ) :
    ForcesThreshold α hβ q (e.toEmbedding.trans h) (p.reindex e) i n ↔
      ForcesThreshold α hβ q h p (p.cellMap e.toEmbedding i) n := by
  by_cases hp : restrictFace h q = some p
  · exact ForcesThreshold.trans_comap_iff hp _ i
  refine iff_of_false (fun hf ↦ hp ?_) fun hf ↦ hp hf.1
  have h1 := restrictFace_trans q (e.toEmbedding.trans h) e.symm.toEmbedding hf.1
  rw [restrictFace_equiv, reindex_reindex, Equiv.symm_trans_self, reindex_refl] at h1
  rw [h1]
  congr 1
  ext j
  simp

/-- **Position matching along a permutation of the root**: for a bijection `e` of the coordinates,
the stable offset at the tuple `c ∘ e`, for the reindexed root at the cell `i`, is the stable
offset at `c`, for the root, at the transported cell.  No hypothesis on `S` is needed. -/
example (S : Realization.{u, v} β M) (c : Fin k → M) (p : StageType.{u} β k) (e : Fin k ≃ Fin k)
    (i : Fin (p.reindex e).card) :
    S.stableOffset α hβ (c ∘ e) (p.reindex e) i =
      S.stableOffset α hβ c p (p.cellMap e.toEmbedding i) := by
  have hprov (m : ℕ) (q : StageType.{u} β m) (h : Fin k ↪ Fin m) :
      provisionalOffset α hβ q (e.toEmbedding.trans h) (p.reindex e) i =
        provisionalOffset α hβ q h p (p.cellMap e.toEmbedding i) := by
    simp only [provisionalOffset, forcesThreshold_reindex_iff]
  refine le_antisymm (iSup₂_le fun x hx ↦ ?_) (iSup₂_le fun x hx ↦ ?_)
  · obtain ⟨s, hs, hcov⟩ := hx
    have hg : x.2.2 = e.toEmbedding.trans (e.symm.toEmbedding.trans x.2.2) := by
      ext j
      simp
    rw [hg, hprov]
    refine le_iSup₂_of_le (f := fun (y : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m)) _ ↦
      provisionalOffset α hβ y.2.1 y.2.2 p (p.cellMap e.toEmbedding i))
      ⟨x.1, x.2.1, e.symm.toEmbedding.trans x.2.2⟩ ⟨s, funext fun j ↦ ?_, hcov⟩ le_rfl
    simpa using congrFun hs (e.symm j)
  · obtain ⟨s, hs, hcov⟩ := hx
    rw [← hprov]
    refine le_iSup₂_of_le (f := fun (y : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m)) _ ↦
      provisionalOffset α hβ y.2.1 y.2.2 (p.reindex e) i)
      ⟨x.1, x.2.1, e.toEmbedding.trans x.2.2⟩ ⟨s, funext fun j ↦ ?_, hcov⟩ le_rfl
    simp [← hs]

end VaughtConjecture.Continuation.HollowExamples
