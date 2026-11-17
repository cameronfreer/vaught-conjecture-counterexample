/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.ClosureCardinality
import VaughtConjecture.Realization.SuffixCharts

/-!
# The descending block

A block of new points of order type `ω*` above a realization `R` on `M`.  The carrier is `M ⊕ ℕ`,
with the old points `Sum.inl a` and the block points `y_j = Sum.inr j`.  The block is descending in
the exterior order: `y_0 > y_1 > y_2 > ⋯`.

**Suffix cuts.**  The suffix cut at `k` (`Realization.suffixCut`) is the set of old points with
the block points `y_j`, `k ≤ j`.  Every suffix cut is closed in the block; the prefix sets (old
points with `y_j`, `j < k`) need not be.

**The statements** (all proved):

* `Realization.DescendingBlockOfChainTarget`: over an exhaustive monotone sequence of occurrences
  of `R` (no countability), an exactly consistent covering realization `S` on `M ⊕ ℕ` with legal
  top-free types keeps every old evaluation, `none` included, and has every suffix cut closed.
  Proof: the suffix charts of `Realization.ExistsSuffixChartsTarget` along the sequence,
  realized by `Realization.ChartChainRealizationTarget`; a finite subset of a suffix cut lies in a
  suffix face of some chart, a closed face, whose points form a support of `S`, so its hull stays
  in the cut (`finiteHull_subset_of_isSupport`).
* `Realization.DescendingBlockTarget`: the same over a countable carrier `M`, through an exhaustive
  chain of occurrences (`Realization.ExistsExhaustiveOccurrenceChainTarget`).
* `Realization.DescendingBlockOrderTarget` (given-realization): if `S` keeps the typed tuples of
  `R` typed and has every suffix cut closed, then for every infinite `B ⊆ M`,
  `y_i ∈ cl(B ∪ {y_j}) ↔ j ≤ i`, every old point lies strictly before every block point, and a
  closed set of `R` is closed in `S`.  The order is `Closure.closedCutOrderTarget` with index
  `ℕᵒᵈ` (a lower cut of `ℕᵒᵈ` is an upper cut of `ℕ`) at the root of all old points, which is
  closed; the root `B` enters by root change (`Closure.exteriorRootChangeTarget`).

Countability is of the old carrier only, and only where an exhaustive chain is built; the stage is
any limit ordinal.

## Placement

This file belongs to the `ℵ₁` companion construction over the density sentence (block types of
the construction); that construction is not yet recorded in `roadmap/COMPANIONS.md`.
-/

universe u v

namespace VaughtConjecture.Realization

variable {M : Type v}

/-- The **suffix cut** at `k` of `M ⊕ ℕ`: the old points and the block points `Sum.inr j` with
`k ≤ j`. -/
def suffixCut (k : ℕ) : Set (M ⊕ ℕ) :=
  Set.range Sum.inl ∪ Sum.inr '' Set.Ici k

/-- **Target: the descending block over an exhaustive chain.**  At a limit stage `α`, let `R` be
an exactly consistent realization with legal top-free types on `M`, and `c` a monotone sequence of
occurrences of `R` whose supports exhaust `M`.  Some exactly consistent covering realization `S`
with legal top-free types on `M ⊕ ℕ` gives every tuple of old points its evaluation in `R`, `none`
included, and has every suffix cut closed for its canonical closure.  No countability.
Construction over a given realization.  Proved (`Realization.descendingBlockOfChainTarget`). -/
def DescendingBlockOfChainTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄, Order.IsSuccLimit α → ∀ (R : Realization.{u, v} α M),
    R.IsConsistent → R.HasLegalTypes → R.HasTopFreeTypes →
    ∀ (c : ℕ → R.Occurrence), Monotone c → (∀ a : M, ∃ k, a ∈ (c k).support) →
      ∃ (S : Realization.{u, v} α (M ⊕ ℕ)) (hS : S.IsConsistent) (hSc : S.IsCovering),
        S.HasLegalTypes ∧ S.HasTopFreeTypes ∧
        (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), S.eval (t.trans Function.Embedding.inl) = R.eval t) ∧
        ∀ k, (S.closure hS hSc).IsClosed (suffixCut k)

/-- **The descending block over an exhaustive chain**, the target form.  The coherent suffix
charts along the chain (`Realization.existsSuffixChartsTarget`) cover `M ⊕ ℕ` and are realized by
one exactly consistent covering realization (`Realization.chartChainRealizationTarget`); its types
are faces of the charts.  A tuple of old points lies in some `c k`, and its evaluation is the
restriction of the chart along the old positions, which is the type of `c k` (the chart is a tower
over it), so it is the evaluation in `R` by exact consistency of `R`.  A finite subset of a suffix
cut lies in a suffix face of a late chart (`Realization.IsSuffixChart.exists_suffix_face`); that
face is typed, so its points form a support, which contains the canonical hull
(`finiteHull_subset_of_isSupport`). -/
theorem descendingBlockOfChainTarget : DescendingBlockOfChainTarget.{u, v} := by
  classical
  intro α M hα R hR hL hT c hmono hex
  obtain ⟨N, w, T, hch, hg⟩ := existsSuffixChartsTarget hα R hR hL hT c hmono
  have hpts : ∀ y : M ⊕ ℕ, ∃ k, y ∈ Set.range (w k) := by
    rintro (a | j)
    · obtain ⟨k, hk⟩ := hex a
      obtain ⟨i, rfl⟩ := (Occurrence.mem_support _).mp hk
      have hiN : (i : ℕ) < N k := by have := (hch k).arity_eq; omega
      exact ⟨k, ⟨⟨i, hiN⟩, by rw [(hch k).apply_eq]; simp⟩⟩
    · have hN := (hch (j + 1)).arity_eq
      refine ⟨j + 1, ⟨⟨(c (j + 1)).arity, by omega⟩, ?_⟩⟩
      rw [(hch _).apply_eq]
      simp
  obtain ⟨S, hS, hSc, hSw, hSf⟩ := chartChainRealizationTarget N w T hg hpts
  refine ⟨S, hS, hSc, fun n t p hp ↦ ?_, fun n t p hp ↦ ?_, fun n t ↦ ?_, fun i ↦ ?_⟩
  · obtain ⟨k, f, -, hf⟩ := hSf t p hp
    exact (hch k).isLegal.restrictFace _ hf
  · obtain ⟨k, f, -, hf⟩ := hSf t p hp
    exact (hch k).isTopFree.restrictFace hf
  · -- a tuple of old points lies in some occurrence of the chain
    choose K hK using hex
    obtain ⟨k, h, hh⟩ : ∃ k, ∃ h : Fin n ↪ Fin (c k).arity, h.trans (c k).tuple = t :=
      ⟨_, (c (Finset.univ.sup fun i ↦ K (t i))).exists_trans_eq fun a ha ↦ by
        obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp ha
        exact hmono (Finset.le_sup (f := fun i ↦ K (t i)) (Finset.mem_univ i)) (hK (t i))⟩
    obtain ⟨o, ho, htow⟩ := (hch k).exists_isTowerOver
    have ht : t.trans Function.Embedding.inl = (h.trans o).trans (w k) := by
      rw [Function.Embedding.trans_assoc, ho, ← Function.Embedding.trans_assoc, hh]
    rw [ht, hS _ _ _ (hSw k), ← StageType.restrictFace_trans _ _ _ htow.restrictFace_eq,
      ← eval_face hR, hh]
  · rw [ClosureOperator.isClosed_iff_closure_le]
    intro y hy
    obtain ⟨F, hF, hyF⟩ := (mem_closure_iff hS hSc).mp hy
    choose K hK using hex
    let J : M ⊕ ℕ → ℕ := Sum.elim K fun j ↦ j + 1
    set k := max i (F.sup J)
    have hFk : ↑F ⊆ suffixPoints (c k).support i k := fun z hz ↦ by
      have hJ : J z ≤ k := (Finset.le_sup (f := J) hz).trans (le_max_right _ _)
      rcases hF hz with ⟨a, rfl⟩ | ⟨j, hj, rfl⟩
      · exact Or.inl ⟨a, hmono hJ (hK a), rfl⟩
      · exact Or.inr ⟨j, ⟨hj, by simp only [J, Sum.elim_inr] at hJ; omega⟩, rfl⟩
    obtain ⟨r, f, hrange, hsome⟩ := (hch k).exists_suffix_face (le_max_left i _)
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome
    have hsup : S.IsSupport (Finset.univ.map (f.trans (w k))) :=
      ⟨⟨r, f.trans (w k), q, by rw [hS _ _ _ (hSw k), hq]⟩, rfl⟩
    have hcoe : (↑(Finset.univ.map (f.trans (w k))) : Set (M ⊕ ℕ)) =
        suffixPoints (c k).support i k := by
      rw [← hrange]
      ext z
      simp
    have hFs : F ⊆ Finset.univ.map (f.trans (w k)) := by
      rw [← Finset.coe_subset, hcoe]
      exact hFk
    have hy' : y ∈ suffixPoints (c k).support i k := by
      rw [← hcoe]
      exact finiteHull_subset_of_isSupport hS hSc hsup hFs hyF
    rcases hy' with ⟨a, -, rfl⟩ | ⟨j, hj, rfl⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨j, hj.1, rfl⟩

/-- **Target: the descending block over a countable realization.**  At a limit stage `α`, let `R`
be an exactly consistent covering realization with legal top-free types on a countable carrier
`M`.  Some exactly consistent covering realization `S` with legal top-free types on `M ⊕ ℕ` gives
every tuple of old points its evaluation in `R`, `none` included, and has every suffix cut closed
for its canonical closure.  Countability is of the old carrier only.  Construction over a given
realization.  Proved (`Realization.descendingBlockTarget`). -/
def DescendingBlockTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ [Countable M], Order.IsSuccLimit α →
    ∀ (R : Realization.{u, v} α M), R.IsConsistent → R.IsCovering → R.HasLegalTypes →
      R.HasTopFreeTypes →
      ∃ (S : Realization.{u, v} α (M ⊕ ℕ)) (hS : S.IsConsistent) (hSc : S.IsCovering),
        S.HasLegalTypes ∧ S.HasTopFreeTypes ∧
        (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), S.eval (t.trans Function.Embedding.inl) = R.eval t) ∧
        ∀ k, (S.closure hS hSc).IsClosed (suffixCut k)

/-- **The descending block over a countable realization**, the target form: an occurrence
(of the empty set, by covering) begins an exhaustive chain of occurrences
(`Realization.existsExhaustiveOccurrenceChainTarget`), and the descending block over that chain is
`Realization.descendingBlockOfChainTarget`. -/
theorem descendingBlockTarget : DescendingBlockTarget.{u, v} := by
  intro α M _ hα R hR hc hL hT
  obtain ⟨x, -⟩ := hc.exists_subset_support ∅
  obtain ⟨c, -, hmono, hex⟩ := existsExhaustiveOccurrenceChainTarget R hc x
  exact descendingBlockOfChainTarget hα R hR hL hT c hmono hex

/-- **Target: the order of a descending block** (given-realization).  Let `R` on `M` and `S` on
`M ⊕ ℕ` be exactly consistent and covering, let `S` give every typed tuple of `R`, read in
`M ⊕ ℕ`, the same type, and let every suffix cut be closed in `S`.  For every infinite `B ⊆ M`:

* the block is descending above `B`: `Sum.inr i` lies in the closure of `B` with `Sum.inr j`
  added exactly when `j ≤ i`;
* every old point lies strictly before every block point in the exterior relation of `B`;
* if `B` is closed for the canonical closure of `R`, it is closed in `S`.

About every pair of realizations satisfying the hypotheses; asserts no existence.  Proved
(`Realization.descendingBlockOrderTarget`). -/
def DescendingBlockOrderTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ (R : Realization.{u, v} α M)
    (S : Realization.{u, v} α (M ⊕ ℕ)) (hR : R.IsConsistent) (hc : R.IsCovering)
    (hS : S.IsConsistent) (hSc : S.IsCovering),
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p →
      S.eval (t.trans Function.Embedding.inl) = some p) →
    (∀ k, (S.closure hS hSc).IsClosed (suffixCut k)) →
    ∀ ⦃B : Set M⦄, B.Infinite →
      (∀ i j : ℕ, Sum.inr i ∈ S.closure hS hSc (insert (Sum.inr j) (Sum.inl '' B)) ↔ j ≤ i) ∧
      (∀ (a : M) (j : ℕ), Sum.inl a ∈ S.closure hS hSc (insert (Sum.inr j) (Sum.inl '' B)) ∧
        Sum.inr j ∉ S.closure hS hSc (insert (Sum.inl a) (Sum.inl '' B))) ∧
      ((R.closure hR hc).IsClosed B → (S.closure hS hSc).IsClosed (Sum.inl '' B))

/-- **The order of a descending block**, the target form.  The old points form an infinite
closed set (the intersection of the suffix cuts).  With index `ℕᵒᵈ`, whose lower cuts are the
upper cuts of `ℕ`, `Closure.closedCutOrderTarget` at the root of all old points gives the
descending order; root change (`Closure.exteriorRootChangeTarget`) passes to `B`, and
`Closure.rootBeforeExteriorTarget` puts the old points first.  A closed set of `R` is closed in
`S` by `Realization.imageClosureOfEvalEmbeddingTarget`. -/
theorem descendingBlockOrderTarget : DescendingBlockOrderTarget.{u, v} := by
  intro α M R S hR hc hS hSc hev hcut B hB
  have hgen := exists_subset_card_le_two_hullClosure_eq hS hSc
  have hBD : Sum.inl '' B ⊆ Set.range (Sum.inl : M → M ⊕ ℕ) := Set.image_subset_range _ _
  have hBi : (Sum.inl '' B : Set (M ⊕ ℕ)).Infinite := hB.image Sum.inl_injective.injOn
  have hDi : (Set.range (Sum.inl : M → M ⊕ ℕ)).Infinite := hBi.mono hBD
  -- the old points form a closed set
  have hD : (S.closure hS hSc).IsClosed (Set.range Sum.inl) := by
    rw [ClosureOperator.isClosed_iff_closure_le]
    rintro (a | j) hy
    · exact ⟨a, rfl⟩
    · have := ClosureOperator.closure_min (c := S.closure hS hSc)
        (Set.subset_union_left : Set.range Sum.inl ⊆ suffixCut (j + 1)) (hcut (j + 1)) hy
      rcases this with ⟨a, ha⟩ | ⟨i, hi, hij⟩
      · exact absurd ha Sum.inl_ne_inr
      · obtain rfl := Sum.inr_injective hij
        exact absurd hi (by simp)
  have hnot : ∀ j : ℕ, (Sum.inr j : M ⊕ ℕ) ∉ Set.range Sum.inl := by
    rintro j ⟨a, ha⟩
    exact Sum.inl_ne_inr ha
  refine ⟨fun i j ↦ ?_, fun a j ↦ ?_, fun hBc ↦ ?_⟩
  · have hrc : S.closure hS hSc (insert (Sum.inr j) (Sum.inl '' B)) =
        S.closure hS hSc (insert (Sum.inr j) (Set.range Sum.inl)) :=
      (Closure.exteriorRootChangeTarget (S.hullClosure hS hSc) hgen hBi hD hBD (hnot j)).symm
    rw [hrc]
    have h := Closure.closedCutOrderTarget (S.hullClosure hS hSc) hgen
      (I := ℕᵒᵈ) (B := Set.range Sum.inl) (fun i ↦ Sum.inr (OrderDual.ofDual i)) hDi
      (fun i i' h ↦ Sum.inr_injective h) (fun i ↦ hnot _) (fun j ↦ ?_)
      (OrderDual.toDual i) (OrderDual.toDual j)
    · exact h.trans OrderDual.toDual_le_toDual
    · have hset : Set.range Sum.inl ∪
          (fun i : ℕᵒᵈ ↦ (Sum.inr (OrderDual.ofDual i) : M ⊕ ℕ)) '' Set.Iic j =
            suffixCut (OrderDual.ofDual j) := by
        refine congrArg (Set.range Sum.inl ∪ ·) (Set.ext fun y ↦ ?_)
        constructor
        · rintro ⟨i, hi, rfl⟩
          exact ⟨OrderDual.ofDual i, hi, rfl⟩
        · rintro ⟨i, hi, rfl⟩
          exact ⟨OrderDual.toDual i, hi, rfl⟩
      rw [hset]
      exact hcut _
  · exact Closure.rootBeforeExteriorTarget (S.hullClosure hS hSc) hgen hBi hD hBD ⟨a, rfl⟩
      (hnot j)
  · have himg := (imageClosureOfEvalEmbeddingTarget R S hR hc hS hSc Function.Embedding.inl
      hev).1 B
    rw [hBc.closure_eq] at himg
    exact (S.closure hS hSc).isClosed_iff.mpr himg.symm

end VaughtConjecture.Realization
