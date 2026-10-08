/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapOffsets

/-!
# The acquired marked-cap contexts: relabelling, roots not onto, and the coatom form

Roadmap, Layer 3 ((R3) of the table of 3.4).

The acquired marked-cap contexts (`TiedRootCapRelabel.MarkedCapContextBelow`: a marked-cap context
whose root offsets lie below the grade of its top cap) have the three properties the coatom route
of hollow cutoff determination asks of a predicate (each compiled in this repository (theorem
named)): hollow acquisition with no hypothesis
(`Realization.hollowAcquisition_isMarkedCapContextBelow`), roots never onto
(`TiedRootCapRelabel.MarkedCapContextBelow.not_surjective`), and invariance under relabelling the
points (`TiedRootCapRelabel.MarkedCapContextBelow.reindex`); together
`TiedRootCapRelabel.markedCapContextBelow_routeInputs`.

`rowAt_reindex`, `mem_below_reindex_iff` and `HollowCoatomCutoffDetermination` are copied
verbatim from the compositions lane (`Stage/MarkedCapRelabel.lean`,
`MainTheorem/CoatomDetermination.lean` there), in their own namespace.  On that lane the coatom
form gives hollow cutoff determination for every predicate with roots never onto and invariant
under relabelling (`Realization.HollowCoatomCutoffDetermination.hollowCutoffDetermination`), and
the route theorem `densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations` takes the
acquisition, the coatom form, and these two properties; neither is compiled here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Finset Label

namespace TiedRootCapRelabel

open StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-! ### Rows and the lower sets under reindexing -/

/-- **Rows under reindexing**: the row of a cell of `t.reindex σ` at a cell is the row of the
corresponding cells of `t`. -/
theorem rowAt_reindex (t : StageType.{u} α k) (σ : Equiv.Perm (Fin k))
    (i j : Fin (t.reindex σ).card) :
    (t.reindex σ).rowAt i j =
      t.rowAt (t.toScheme.cellMap σ.toEmbedding i) (t.toScheme.cellMap σ.toEmbedding j) := by
  have hle := t.toScheme.isLowerEmbedding_comap σ.toEmbedding
  change (t.toScheme.comap σ.toEmbedding).rowAt i j = t.rowAt _ _
  unfold Scheme.rowAt
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((hle.le_iff j i).mpr h1) h2
  · exact absurd ((hle.le_iff j i).mp h2) h1
  · rfl

/-- **Below under reindexing**: a cell of `t.reindex σ` lies below another exactly when the
corresponding cells of `t` do. -/
theorem mem_below_reindex_iff (t : StageType.{u} α k) (σ : Equiv.Perm (Fin k))
    (i j : Fin (t.reindex σ).card) :
    j ∈ (t.reindex σ).toCellScheme.below ((t.reindex σ).toCellScheme.gradedIndex i) ↔
      t.toScheme.cellMap σ.toEmbedding j ∈
        t.toCellScheme.below (t.toCellScheme.gradedIndex (t.toScheme.cellMap σ.toEmbedding i)) :=
  ((t.toScheme.isLowerEmbedding_comap σ.toEmbedding).le_iff j i).symm

/-! ### The acquired predicate -/

/-- The **acquired marked-cap context** along `h`: a marked-cap context with top cap `c` and
marker `r` whose root offsets lie below the grade of `c`. -/
def MarkedCapContextBelow (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) : Prop :=
  ∃ c r, t'.IsMarkedCapContextAt h c r ∧ t'.RootOffsetsBelow h (t'.toCellScheme.grade c)

/-- **The root of an acquired context is not onto**: its top cap has grade above `n + 1`, at most
the number `k` of points. -/
theorem MarkedCapContextBelow.not_surjective {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    (ht : MarkedCapContextBelow t' h) : ¬ Function.Surjective h := by
  obtain ⟨c, -, ⟨-, -, hn, -⟩, -⟩ := ht
  intro hs
  have hkn : k ≤ n := by simpa using Fintype.card_le_of_surjective h hs
  have := t'.grade_le c
  omega

/-- **The acquired context is invariant under relabelling**: if `t'` is one along `h`, then
`t'.reindex σ` is one along `h.trans σ⁻¹`; the top cap, the marker and the cells of the root
correspond through the cell map of `σ`, with their labels, grades and rows. -/
theorem MarkedCapContextBelow.reindex {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    (ht : MarkedCapContextBelow t' h) (σ : Equiv.Perm (Fin k)) :
    MarkedCapContextBelow (t'.reindex σ) (h.trans σ.symm.toEmbedding) := by
  obtain ⟨c, r, ⟨⟨hcs, hcl, hcg⟩, ⟨hrl, hrb, hrm⟩, hn, hroot⟩, hoff⟩ := ht
  have hsurj := t'.toScheme.surjective_cellMap_equiv σ
  obtain ⟨c', rfl⟩ := hsurj c
  obtain ⟨r', rfl⟩ := hsurj r
  -- the cells of the reindexed root are cells of the root
  have hvis (a : Fin (t'.reindex σ).card)
      (ha : a ∈ (t'.reindex σ).visibleCells (h.trans σ.symm.toEmbedding)) :
      t'.toScheme.cellMap σ.toEmbedding a ∈ t'.visibleCells h := by
    rw [Scheme.mem_visibleCells] at ha ⊢
    intro y hy
    have hy' : σ.symm y ∈ ((t'.reindex σ).toCellScheme.scope a : Set (Fin k)) := by
      change σ.symm y ∈ (t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding a)).preimage
        σ.toEmbedding σ.toEmbedding.injective.injOn
      simpa using hy
    obtain ⟨i, hi⟩ := ha hy'
    exact ⟨i, by simpa using congrArg σ hi⟩
  refine ⟨c', r', ⟨⟨?_, hcl, fun x hx ↦ hcg _ hx⟩,
    ⟨hrl, (mem_below_reindex_iff t' σ c' r').mpr hrb, fun x hx hxb ↦ ?_⟩, hn,
      fun a ha hat ↦ ?_⟩, fun a ha μ f hμ hf ↦ hoff _ (hvis a ha) μ f hμ hf⟩
  · change (t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding c')).preimage
      σ.toEmbedding σ.toEmbedding.injective.injOn = univ
    rw [hcs]
    exact Finset.preimage_univ _
  · exact (rowAt_reindex t' σ c' r').trans_le
      ((hrm _ hx ((mem_below_reindex_iff t' σ c' x).mp hxb)).trans_eq
        (rowAt_reindex t' σ c' x).symm)
  · exact (congrArg (visibilityReplace _ (n + 1)) (rowAt_reindex t' σ c' r')).trans_le
      ((hroot _ (hvis a ha) hat).trans_eq (rowAt_reindex t' σ c' a).symm)

/-! ### The coatom form of hollow cutoff determination -/

/-- **Hollow coatom cutoff determination** for `P` (as on the compositions lane): over a legal
`t'` on `k + 1` points with `P t' (g.trans Fin.castSuccEmb)` and face `p` along `Fin.castSuccEmb`,
every legal coface `tb` of `p` whose face along `extendByLast g` is `d` has a coface `D'` of `t'`
with face `tb` and a permitted cutoff `δ` determining `d` within the receiving family of `D'`.
Not proved for any `P` here. -/
structure HollowCoatomCutoffDetermination
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop) : Prop where
  /-- Every donor through a coface of the coatom face is determined at a cutoff. -/
  exists_coface ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α (k + 1))
    (g : Fin n ↪ Fin k) (p : StageType.{u} α k) :
    Order.IsSuccLimit α → t'.IsLegal → P t' (g.trans Fin.castSuccEmb) →
      restrictFace Fin.castSuccEmb t' = some p → ∀ tb ∈ p.cofaces, ∀ d : StageType.{u} α (n + 1),
        restrictFace (extendByLast g) tb = some d →
          ∃ D' ∈ t'.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
            ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
              IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d

/-- **The inputs of the coatom route for the acquired predicate**: its hollow acquisition (with no
hypothesis), roots never onto, and invariance under relabelling.  With
`HollowCoatomCutoffDetermination` for it, these are the hypotheses `hacq₃`, `hns₃`, `hinv₃` of the
route theorem `densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations` on the
compositions lane. -/
theorem markedCapContextBelow_routeInputs :
    Realization.HollowAcquisition.{u, w} Realization.IsCoverHollowAtBlock
        (fun t' h ↦ MarkedCapContextBelow t' h) ∧
      (∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
        MarkedCapContextBelow t' h → ¬ Function.Surjective h) ∧
      (∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
        (σ : Equiv.Perm (Fin k)), MarkedCapContextBelow t' h →
          MarkedCapContextBelow (t'.reindex σ) (h.trans σ.symm.toEmbedding)) :=
  ⟨Realization.hollowAcquisition_isMarkedCapContextBelow, fun _ _ _ _ _ ht ↦ ht.not_surjective,
    fun _ _ _ _ _ σ ht ↦ ht.reindex σ⟩

end TiedRootCapRelabel

end VaughtConjecture
