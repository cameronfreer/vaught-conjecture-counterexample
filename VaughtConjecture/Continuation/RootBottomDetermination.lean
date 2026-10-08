/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapRootBottom

/-!
# Cutoff determination at contexts respecting the root bottoms

Roadmap, Layer 3 ((R3) of the table of 3.4).

The predicate `TiedRootCapRelabel.MarkedCapContextBelow'` (marked-cap contexts whose root offsets
lie below the grade of the cap and whose cap reads the root cells labelled `⊥` as `⊥`) is acquired
with no hypothesis (`Realization.rootBottomAcquisition`).  This file states cutoff determination and
gives the route inputs for this predicate; the composition with the receiving route is in
`VaughtConjecture.MainTheorem.RootBottomRoute`.

* **Hollow cutoff determination** (`Realization.HollowCutoffDetermination`, a named statement, not
  proved for any predicate here) and its **coatom form**
  (`Realization.HollowCoatomCutoffDetermination`, likewise): over a legal context `t'` with the
  predicate, every one-point coface of the root face (in the coatom form: every donor through a
  coface of the face of `t'` along `Fin.castSuccEmb`) is determined within the receiving family,
  at a permitted cutoff, of some coface of `t'`.
* **The reduction from the coatom form** (`Realization.CoatomCutoffReduction`, a named statement,
  not compiled here): the coatom form gives the hollow form for every predicate whose roots are
  never onto and which is invariant under relabelling (through the exact pinned extension and a
  relabelling putting the root in the first coatom).
* **(R3) from acquisition and cutoff determination**
  (`Realization.hollowReceiving_of_hollowCutoffDetermination`, compiled in this repository
  (theorem named)): the coface is realized over the acquired context by finite-cut receiving.
* **The route inputs for the predicate** (compiled): the roots are never onto
  (`TiedRootCapRelabel.MarkedCapContextBelow'.not_surjective`), the predicate is invariant under
  relabelling (`TiedRootCapRelabel.MarkedCapContextBelow'.reindex`, with
  `TiedRootCapRelabel.rowAt_reindex` and `TiedRootCapRelabel.mem_below_reindex_iff`), and it is
  acquired (`Realization.rootBottomAcquisition`); together
  `Realization.markedCapContextBelow'_routeInputs`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label

/-! ### Relabelling the acquired predicate -/

namespace TiedRootCapRelabel

open StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **Rows under reindexing**: the row of a cell of `t.reindex σ` at another is the row of the
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

/-- **The root of an acquired context is not onto**: its top cap has grade above `n + 1`, at most
the number `k` of points. -/
theorem MarkedCapContextBelow'.not_surjective {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    (ht : MarkedCapContextBelow' t' h) : ¬ Function.Surjective h := by
  obtain ⟨c, -, ⟨-, -, hn, -⟩, -⟩ := ht
  intro hs
  have hkn : k ≤ n := by simpa using Fintype.card_le_of_surjective h hs
  have := t'.grade_le c
  omega

/-- **Invariance under relabelling**: the top cap, the marker and the root correspond through the
cell map of `σ`, with their labels and rows. -/
theorem MarkedCapContextBelow'.reindex {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    (ht : MarkedCapContextBelow' t' h) (σ : Equiv.Perm (Fin k)) :
    MarkedCapContextBelow' (t'.reindex σ) (h.trans σ.symm.toEmbedding) := by
  obtain ⟨c, r, hctx, hoff, hbot⟩ := ht
  have hsurj := t'.toScheme.surjective_cellMap_equiv σ
  obtain ⟨c', rfl⟩ := hsurj c
  obtain ⟨r', rfl⟩ := hsurj r
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
  refine ⟨c', r', ?_, ?_, fun a ha hab ↦ ?_⟩
  · obtain ⟨⟨hcs, hcl, hcg⟩, ⟨hrl, hrb, hrm⟩, hn, hroot⟩ := hctx
    refine ⟨⟨?_, hcl, fun x hx ↦ hcg _ hx⟩, ⟨hrl, (mem_below_reindex_iff t' σ c' r').mpr hrb,
      fun x hx hxb ↦ ?_⟩, hn, fun a ha hat ↦ ?_⟩
    · change (t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding c')).preimage
        σ.toEmbedding σ.toEmbedding.injective.injOn = univ
      rw [hcs]
      exact Finset.preimage_univ _
    · exact (rowAt_reindex t' σ c' r').trans_le
        ((hrm _ hx ((mem_below_reindex_iff t' σ c' x).mp hxb)).trans_eq
          (rowAt_reindex t' σ c' x).symm)
    · exact (congrArg (visibilityReplace _ (n + 1)) (rowAt_reindex t' σ c' r')).trans_le
        ((hroot _ (hvis a ha) hat).trans_eq (rowAt_reindex t' σ c' a).symm)
  · exact fun a ha μ f hμ hf ↦ hoff _ (hvis a ha) μ f hμ hf
  · exact (rowAt_reindex t' σ c' a).trans (hbot _ (hvis a ha) hab)

end TiedRootCapRelabel

/-! ### Hollow cutoff determination and its coatom form -/

namespace Realization

open StageType

/-- **Hollow cutoff determination** for `P`, a statement about stage types: at a limit stage, over
every legal `t'` with `P t' h`, every one-point coface `d` of the face of `t'` along `h` is
determined over `t'` along `h` within the receiving family, at a permitted cutoff, of some coface
of `t'`.  The coface and the cutoff are chosen for the input, before any member of the family.
The statement of `CutoffDetermination` without the bound on the top grade of `d`.  Not proved for
any `P` here. -/
structure HollowCutoffDetermination
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop) : Prop where
  /-- Every coface of the face is determined at a cutoff. -/
  exists_coface ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) :
    Order.IsSuccLimit α → t'.IsLegal → P t' h → ∀ t : StageType.{u} α n,
      StageType.restrictFace h t' = some t → ∀ d ∈ t.cofaces,
        ∃ D' ∈ t'.cofaces, ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
          StageType.IsDeterminedWithin (StageType.receivingFamily D' δ) t' h d

/-- **Hollow coatom cutoff determination** for `P`: the statement of `CoatomCutoffDetermination`
without the bound on the top grade of the donor.  Not proved for any `P` here. -/
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

/-- **The reduction from the coatom form** (a named statement, not compiled on this branch): for
every predicate `P` whose roots are never onto and which is invariant under relabelling the points
of the context with the root relabelled along, hollow coatom cutoff determination gives hollow
cutoff determination (through the exact pinned extension and a relabelling putting the root in
the first coatom). -/
def CoatomCutoffReduction : Prop :=
  ∀ (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop),
    HollowCoatomCutoffDetermination.{u} P →
    (∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
      P t' h → ¬ Function.Surjective h) →
    (∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
      (σ : Equiv.Perm (Fin k)), P t' h → P (t'.reindex σ) (h.trans σ.symm.toEmbedding)) →
    HollowCutoffDetermination.{u} P

/-! ### (R3) from acquisition and cutoff determination -/

/-- **(R3) from hollow acquisition and hollow cutoff determination**, for any predicate `P` on
acquired contexts and every predicate `H'` on realizations that implies the acquisition predicate
`H` and finite-cut receiving.  The coface is realized over the acquired context by the finite-cut
receiving of the given model. -/
theorem hollowReceiving_of_hollowCutoffDetermination
    {H H' : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop}
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop}
    (hacq : HollowAcquisition.{u, w} H P) (hdet : HollowCutoffDetermination.{u} P)
    (hH : ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄, H' R →
      H R ∧ R.HasFiniteCutReceiving) :
    HollowReceiving.{u, w} H' where
  exists_covers α M R hα hR hH' htop n t c hc d hd := by
    obtain ⟨k, t', c', h, hc', hcc', hP⟩ := hacq.exists_context hα hR (hH hH').1 htop t c hc
    obtain ⟨D', hD', δ, hδ, hdet'⟩ := hdet.exists_coface t' h hα (hR.isLegal _ _ hc'.eval_eq) hP
      t (restrictFace_of_covers hR.isConsistent hc hc' hcc') d hd
    rw [← hcc']
    exact exists_covers_snoc_of_isDeterminedWithin hR.isConsistent hc'
      ((hH hH').2.realizesOver_receivingFamily hc' hD' hδ) hdet'

/-! ### The acquired predicate -/

/-- **The route inputs for the acquired predicate**: its hollow acquisition (with no hypothesis),
roots never onto, and invariance under relabelling. -/
theorem markedCapContextBelow'_routeInputs :
    HollowAcquisition.{u, w} IsCoverHollowAtBlock
        (fun t' h ↦ TiedRootCapRelabel.MarkedCapContextBelow' t' h) ∧
      (∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
        TiedRootCapRelabel.MarkedCapContextBelow' t' h → ¬ Function.Surjective h) ∧
      (∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
        (σ : Equiv.Perm (Fin k)), TiedRootCapRelabel.MarkedCapContextBelow' t' h →
          TiedRootCapRelabel.MarkedCapContextBelow' (t'.reindex σ)
            (h.trans σ.symm.toEmbedding)) :=
  ⟨rootBottomAcquisition, fun _ _ _ _ _ ht ↦ ht.not_surjective, fun _ _ _ _ _ σ ht ↦ ht.reindex σ⟩

end Realization

end VaughtConjecture
