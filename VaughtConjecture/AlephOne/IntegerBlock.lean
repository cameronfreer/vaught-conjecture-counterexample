/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.DescendingBlock
import VaughtConjecture.Closure.ClosedCuts
import VaughtConjecture.Realization.ChartChainUnion
import VaughtConjecture.Realization.PrefixCharts

/-!
# The ascending block and the block of order type `ℤ`

**The ascending block.**  A block of new points `a_0, a_1, …` of order type `ω` above a
realization on `X`, on the carrier `X ⊕ ℕ` with `a_j = Sum.inr j`.  The prefix cut at `n`
(`Realization.prefixCut`) is the set of old points with the block points `a_j`, `j < n`; every
prefix cut is closed (`Realization.AscendingBlockTarget`, over a countable carrier), and then
`a_i ∈ cl(B ∪ {a_j}) ↔ i ≤ j` for every infinite `B ⊆ X` (`Realization.AscendingBlockOrderTarget`,
given-realization; `Closure.closedCutOrderTarget` with index `ℕ`).  The existence statement is
proved in finite charts: the chart chain of towers over the occurrences of an exhaustive chain
with the block points oldest first (`Realization.exists_prefixCharts`), each chart the tower
transfer of the previous one followed by one top-free one-point coface.

**The block of order type `ℤ`.**  An ascending block after a descending block, on
`(M ⊕ ℕ) ⊕ ℕ`: the descending points `y_j = Sum.inl (Sum.inr j)` and the ascending points
`a_j = Sum.inr j`, enumerated by `ℤ` through `Realization.integerBlockPoint` (`a_n` at `n ≥ 0`,
`y_n` at `-(n + 1)`).  The integer cut at `z` (`Realization.integerCut`) is the set of old points
of `M` with the block points enumerated at most `z`: for `z = -(j + 1)` it is the image of the
suffix cut at `j` of the descending block, and for `z = n ≥ 0` the prefix cut at `n + 1` of the
ascending block.  Every integer cut is closed (`Realization.IntegerBlockTarget`), and then the
exterior relation above any infinite `B ⊆ M` is the order of `ℤ`
(`Realization.IntegerBlockOrderTarget`, given-realization; `Closure.closedCutOrderTarget` with
index `ℤ`, and root change).  The exterior order of the block is `ω* + ω`.

With a prescribed request: the ascending block whose first point realizes a given top-free donor
over a given occurrence (`Realization.AscendingBlockServiceTarget`), and the block of order type
`ℤ` whose first ascending point does so over an occurrence of the descending part
(`Realization.IntegerBlockServiceTarget`); one serving point per block.

All statements are proved: `Realization.AscendingBlockTarget`,
`Realization.AscendingBlockOrderTarget`, `Realization.AscendingBlockServiceTarget`,
`Realization.IntegerBlockTarget`, `Realization.IntegerBlockOrderTarget`,
`Realization.IntegerBlockServiceTarget`.  Countability is of the old carrier only; the stage is
any limit ordinal.

## Placement

This file belongs to the `ℵ₁` companion construction over the density sentence (block types of
the construction), recorded in `roadmap/COMPANIONS.md` ("The `ℵ₁` companion construction").
-/

universe u v

namespace VaughtConjecture.Realization

/-! ### The ascending block -/

section Ascending

variable {X : Type v}

/-- The **prefix cut** at `n` of `X ⊕ ℕ`: the old points and the block points `Sum.inr j` with
`j < n`. -/
def prefixCut (n : ℕ) : Set (X ⊕ ℕ) :=
  Set.range Sum.inl ∪ Sum.inr '' Set.Iio n

/-- **Target: the ascending block over a countable realization.**  At a limit stage `α`, let `R`
be an exactly consistent covering realization with legal top-free types on a countable carrier
`X`.  Some exactly consistent covering realization `S` with legal top-free types on `X ⊕ ℕ` gives
every tuple of old points its evaluation in `R`, `none` included, and has every prefix cut closed
for its canonical closure.  Countability is of the old carrier only.  Construction over a given
realization.  Proved (`Realization.ascendingBlockTarget`). -/
def AscendingBlockTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ [Countable X], Order.IsSuccLimit α →
    ∀ (R : Realization.{u, v} α X), R.IsConsistent → R.IsCovering → R.HasLegalTypes →
      R.HasTopFreeTypes →
      ∃ (S : Realization.{u, v} α (X ⊕ ℕ)) (hS : S.IsConsistent) (hSc : S.IsCovering),
        S.HasLegalTypes ∧ S.HasTopFreeTypes ∧
        (∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), S.eval (t.trans Function.Embedding.inl) = R.eval t) ∧
        ∀ n, (S.closure hS hSc).IsClosed (prefixCut n)

/-- **The ascending block from coherent prefix charts.**  Along a monotone sequence `c` of
occurrences of an exactly consistent realization `R` exhausting `X`, coherent prefix charts cover
`X ⊕ ℕ` and are realized by one exactly consistent covering realization `S`
(`Realization.chartChainRealizationTarget`) with legal top-free types, giving each chart its type.
Old evaluations are kept (`Realization.eval_trans_of_chartChain`), and a finite subset of a prefix
cut lies in a prefix face of a late chart, a closed face inside the cut
(`Realization.isClosed_of_chartChain`). -/
theorem exists_ascending_of_prefixCharts {α : Ordinal.{u}} {R : Realization.{u, v} α X}
    (hR : R.IsConsistent) {c : ℕ → R.Occurrence} (hmono : Monotone c)
    (hex : ∀ a : X, ∃ k, a ∈ (c k).support) {N : ℕ → ℕ} {w : ∀ k, Fin (N k) ↪ X ⊕ ℕ}
    {T : ∀ k, StageType.{u} α (N k)} (hch : ∀ k, R.IsPrefixChart (c k) k (w k) (T k))
    (hg : ∀ k, ∃ g : Fin (N k) ↪ Fin (N (k + 1)), g.trans (w (k + 1)) = w k ∧
      StageType.restrictFace g (T (k + 1)) = some (T k)) :
    ∃ (S : Realization.{u, v} α (X ⊕ ℕ)) (hS : S.IsConsistent) (hSc : S.IsCovering),
      S.HasLegalTypes ∧ S.HasTopFreeTypes ∧
      (∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), S.eval (t.trans Function.Embedding.inl) = R.eval t) ∧
      (∀ n, (S.closure hS hSc).IsClosed (prefixCut n)) ∧ ∀ k, S.eval (w k) = some (T k) := by
  have hpts : ∀ y : X ⊕ ℕ, ∃ k, y ∈ Set.range (w k) := by
    rintro (a | j)
    · obtain ⟨k, hk⟩ := hex a
      obtain ⟨i, rfl⟩ := (Occurrence.mem_support _).mp hk
      have hiN : (i : ℕ) < N k := by have := (hch k).arity_eq; omega
      exact ⟨k, ⟨⟨i, hiN⟩, by rw [(hch k).apply_eq]; simp⟩⟩
    · have hN := (hch (j + 1)).arity_eq
      refine ⟨j + 1, ⟨⟨(c (j + 1)).arity + j, by omega⟩, ?_⟩⟩
      rw [(hch _).apply_eq]
      simp
  obtain ⟨S, hS, hSc, hSw, hSf⟩ := chartChainRealizationTarget N w T hg hpts
  choose o ho htow using fun k ↦ (hch k).exists_isTowerOver
  refine ⟨S, hS, hSc, fun n t p hp ↦ ?_, fun n t p hp ↦ ?_, fun n t ↦
    eval_trans_of_chartChain hR hmono hex hS hSw o ho (fun k ↦ (htow k).restrictFace_eq) t,
    fun n ↦ ?_, hSw⟩
  · obtain ⟨k, f, -, hf⟩ := hSf t p hp
    exact (hch k).isLegal.restrictFace _ hf
  · obtain ⟨k, f, -, hf⟩ := hSf t p hp
    exact (hch k).isTopFree.restrictFace hf
  · classical
    refine isClosed_of_chartChain hS hSc hSw fun F hF ↦ ?_
    choose K hK using hex
    let J : X ⊕ ℕ → ℕ := Sum.elim K fun _ ↦ 0
    obtain ⟨r, f, hrange, hsome⟩ := (hch (max n (F.sup J))).exists_prefix_face (le_max_left n _)
    refine ⟨max n (F.sup J), r, f, ?_, ?_, hsome⟩
    · rw [hrange]
      intro z hz
      have hJ : J z ≤ max n (F.sup J) := (Finset.le_sup (f := J) hz).trans (le_max_right _ _)
      rcases hF hz with ⟨a, rfl⟩ | ⟨j, hj, rfl⟩
      · exact Or.inl ⟨a, hmono hJ (hK a), rfl⟩
      · exact Or.inr ⟨j, hj, rfl⟩
    · rw [hrange]
      rintro z (⟨a, -, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inr ⟨j, hj, rfl⟩

/-- **The ascending block over a countable realization**, the target form: coherent prefix charts
(`Realization.exists_prefixCharts`) along an exhaustive chain of occurrences
(`Realization.existsExhaustiveOccurrenceChainTarget`), realized by
`Realization.exists_ascending_of_prefixCharts`. -/
theorem ascendingBlockTarget : AscendingBlockTarget.{u, v} := by
  intro α X _ hα R hR hc hL hT
  obtain ⟨x, -⟩ := hc.exists_subset_support ∅
  obtain ⟨c, -, hmono, hex⟩ := existsExhaustiveOccurrenceChainTarget R hc x
  obtain ⟨N, w, T, hch, hg⟩ := exists_prefixCharts hα R hR hL hT c hmono
  obtain ⟨S, hS, hSc, hSL, hST, hSev, hScut, -⟩ :=
    exists_ascending_of_prefixCharts hR hmono hex hch hg
  exact ⟨S, hS, hSc, hSL, hST, hSev, hScut⟩

/-- **Target: the order of an ascending block** (given-realization).  Let `S` on `X ⊕ ℕ` be
exactly consistent and covering with every prefix cut closed.  For every infinite `B ⊆ X`, the
block is ascending above `B` (`Sum.inr i` lies in the closure of `B` with `Sum.inr j` added
exactly when `i ≤ j`), and every old point lies strictly before every block point in the exterior
relation of `B`.  About every realization satisfying the hypotheses; asserts no existence.
Proved (`Realization.ascendingBlockOrderTarget`). -/
def AscendingBlockOrderTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ (S : Realization.{u, v} α (X ⊕ ℕ)) (hS : S.IsConsistent)
    (hSc : S.IsCovering), (∀ n, (S.closure hS hSc).IsClosed (prefixCut n)) →
    ∀ ⦃B : Set X⦄, B.Infinite →
      (∀ i j : ℕ, Sum.inr i ∈ S.closure hS hSc (insert (Sum.inr j) (Sum.inl '' B)) ↔ i ≤ j) ∧
      ∀ (a : X) (j : ℕ), Sum.inl a ∈ S.closure hS hSc (insert (Sum.inr j) (Sum.inl '' B)) ∧
        Sum.inr j ∉ S.closure hS hSc (insert (Sum.inl a) (Sum.inl '' B))

/-- **The order of an ascending block**, the target form: the old points form the prefix cut
at `0`, a closed set, and the cuts `Set.Iic j` of `ℕ` are the prefix cuts at `j + 1`; the order is
`Closure.mem_setClosure_insert_iff_of_isClosed_cuts` with index `ℕ`, and the old points come first
by `Closure.rootBeforeExteriorTarget`. -/
theorem ascendingBlockOrderTarget : AscendingBlockOrderTarget.{u, v} := by
  intro α X S hS hSc hcut B hB
  have hgen := exists_subset_card_le_two_hullClosure_eq hS hSc
  have hBD : Sum.inl '' B ⊆ Set.range (Sum.inl : X → X ⊕ ℕ) := Set.image_subset_range _ _
  have hBi : (Sum.inl '' B : Set (X ⊕ ℕ)).Infinite := hB.image Sum.inl_injective.injOn
  have hD : (S.closure hS hSc).IsClosed (Set.range Sum.inl) := by
    have h := hcut 0
    rwa [prefixCut, show Set.Iio (0 : ℕ) = ∅ from Set.ext fun i ↦ by simp, Set.image_empty,
      Set.union_empty] at h
  have hnot : ∀ j : ℕ, (Sum.inr j : X ⊕ ℕ) ∉ Set.range Sum.inl := by
    rintro j ⟨a, ha⟩
    exact Sum.inl_ne_inr ha
  have hcut' : ∀ j : ℕ,
      (S.closure hS hSc).IsClosed (Set.range Sum.inl ∪ Sum.inr '' Set.Iic j) := fun j ↦ by
    have h := hcut (j + 1)
    rwa [prefixCut, show Set.Iio (j + 1) = Set.Iic j from
      Set.ext fun i ↦ by simp] at h
  exact ⟨fun i j ↦ Closure.mem_setClosure_insert_iff_of_isClosed_cuts
      (c := S.hullClosure hS hSc) hgen Sum.inr hBi hBD hD Sum.inr_injective hnot hcut' i j,
    fun a j ↦ Closure.rootBeforeExteriorTarget _ hgen hBi hD hBD ⟨a, rfl⟩ (hnot j)⟩

/-- A tuple `t` of old points, read in `X ⊕ ℕ`, followed by the block point `Sum.inr j`. -/
def appendBlockPoint {n : ℕ} (t : Fin n ↪ X) (j : ℕ) : Fin (n + 1) ↪ X ⊕ ℕ :=
  Fin.Embedding.snoc (t.trans Function.Embedding.inl) (a := Sum.inr j) (by simp)

/-- **Target: the ascending block with a prescribed request served.**  At a limit stage `α`, let
`R` be an exactly consistent covering realization with legal top-free types on a countable carrier
`X`, `x` an occurrence of `R` and `d` a top-free coface of its type.  Some exactly consistent
covering realization `S` with legal top-free types on `X ⊕ ℕ` gives every tuple of old points its
evaluation in `R`, `none` included, has every prefix cut closed, and gives the tuple of `x`
followed by the first block point `Sum.inr 0` the type `d`.  Construction over a given
realization.  Proved (`Realization.ascendingBlockServiceTarget`). -/
def AscendingBlockServiceTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ [Countable X], Order.IsSuccLimit α →
    ∀ (R : Realization.{u, v} α X), R.IsConsistent → R.IsCovering → R.HasLegalTypes →
      R.HasTopFreeTypes → ∀ (x : R.Occurrence), ∀ d ∈ x.type.cofaces, d.IsTopFree →
      ∃ (S : Realization.{u, v} α (X ⊕ ℕ)) (hS : S.IsConsistent) (hSc : S.IsCovering),
        S.HasLegalTypes ∧ S.HasTopFreeTypes ∧
        (∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), S.eval (t.trans Function.Embedding.inl) = R.eval t) ∧
        (∀ n, (S.closure hS hSc).IsClosed (prefixCut n)) ∧
        S.eval (appendBlockPoint x.tuple 0) = some d

/-- **The ascending block with a prescribed request served**, the target form: an exhaustive chain
of occurrences beginning at `x` (`Realization.existsExhaustiveOccurrenceChainTarget`) carries
coherent prefix charts whose first block point realizes `d` over `x`
(`Realization.exists_prefixCharts_serving`), realized by
`Realization.exists_ascending_of_prefixCharts`; the tuple of `x` followed by `Sum.inr 0` is a face
of chart `1` with type `d`. -/
theorem ascendingBlockServiceTarget : AscendingBlockServiceTarget.{u, v} := by
  intro α X _ hα R hR hc hL hT x d hd hdt
  obtain ⟨c, rfl, hmono, hex⟩ := existsExhaustiveOccurrenceChainTarget R hc x
  obtain ⟨N, w, T, hch, hg, hserv⟩ := exists_prefixCharts_serving hα R hR hL hT c hmono hd hdt
  obtain ⟨S, hS, hSc, hSL, hST, hSev, hScut, hSw⟩ :=
    exists_ascending_of_prefixCharts hR hmono hex hch hg
  obtain ⟨f, hf, hfd⟩ := hserv (appendBlockPoint (c 0).tuple 0) (Fin.Embedding.init_snoc _ _)
    Fin.Embedding.snoc_last
  exact ⟨S, hS, hSc, hSL, hST, hSev, hScut, by rw [← hf, hS _ _ _ (hSw 1), hfd]⟩

end Ascending

/-! ### The block of order type `ℤ` -/

section Integer

variable {M : Type v}

/-- The **point enumerated by an integer** in the block of order type `ℤ` on `(M ⊕ ℕ) ⊕ ℕ`: the
ascending point `Sum.inr n` at `n ≥ 0`, and the descending point `Sum.inl (Sum.inr n)` at
`-(n + 1)`. -/
def integerBlockPoint : ℤ → (M ⊕ ℕ) ⊕ ℕ
  | Int.ofNat n => Sum.inr n
  | Int.negSucc n => Sum.inl (Sum.inr n)

/-- The **integer cut** at `z`: the old points of `M` and the block points enumerated by integers
at most `z`. -/
def integerCut (z : ℤ) : Set ((M ⊕ ℕ) ⊕ ℕ) :=
  Set.range (fun a : M ↦ Sum.inl (Sum.inl a)) ∪ integerBlockPoint '' Set.Iic z

/-- The enumeration of the block of order type `ℤ` is injective. -/
theorem integerBlockPoint_injective : Function.Injective (integerBlockPoint (M := M)) := by
  intro i j h
  cases i <;> cases j <;> simp_all [integerBlockPoint]

/-- The block points are not old points of `M`. -/
theorem integerBlockPoint_notMem (i : ℤ) :
    integerBlockPoint (M := M) i ∉ Set.range fun a : M ↦ Sum.inl (Sum.inl a) := by
  cases i <;> simp [integerBlockPoint]

/-- The integer cut at `n ≥ 0` is the prefix cut at `n + 1` of the ascending block. -/
theorem integerCut_ofNat (n : ℕ) : integerCut (M := M) (Int.ofNat n) = prefixCut (n + 1) := by
  ext y
  simp only [integerCut, prefixCut, Set.mem_union, Set.mem_range, Set.mem_image, Set.mem_Iic,
    Set.mem_Iio]
  constructor
  · rintro (⟨a, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact Or.inl ⟨_, rfl⟩
    · cases i with
      | ofNat m =>
        simp only [Int.ofNat_eq_natCast, Nat.cast_le] at hi
        exact Or.inr ⟨m, by omega, rfl⟩
      | negSucc m => exact Or.inl ⟨Sum.inr m, rfl⟩
  · rintro (⟨x, rfl⟩ | ⟨m, hm, rfl⟩)
    · cases x with
      | inl a => exact Or.inl ⟨a, rfl⟩
      | inr m =>
        refine Or.inr ⟨Int.negSucc m, ?_, rfl⟩
        simp only [Int.ofNat_eq_natCast, Int.negSucc_eq]
        omega
    · exact Or.inr ⟨Int.ofNat m, by simp only [Int.ofNat_eq_natCast, Nat.cast_le]; omega, rfl⟩

/-- The integer cut at `-(j + 1)` is the image of the suffix cut at `j` of the descending block. -/
theorem integerCut_negSucc (j : ℕ) :
    integerCut (M := M) (Int.negSucc j) = Sum.inl '' suffixCut j := by
  ext y
  simp only [integerCut, suffixCut, Set.mem_union, Set.mem_range, Set.mem_image, Set.mem_Iic,
    Set.mem_Ici]
  constructor
  · rintro (⟨a, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨Sum.inl a, Or.inl ⟨a, rfl⟩, rfl⟩
    · cases i with
      | ofNat m =>
        exfalso
        simp only [Int.ofNat_eq_natCast, Int.negSucc_eq] at hi
        omega
      | negSucc m =>
        refine ⟨Sum.inr m, Or.inr ⟨m, ?_, rfl⟩, rfl⟩
        simp only [Int.negSucc_eq] at hi
        omega
  · rintro ⟨x, ⟨a, rfl⟩ | ⟨m, hm, rfl⟩, rfl⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨Int.negSucc m, by simp only [Int.negSucc_eq]; omega, rfl⟩

/-- **Target: the block of order type `ℤ` over a countable realization.**  At a limit stage `α`,
let `R` be an exactly consistent covering realization with legal top-free types on a countable
carrier `M`.  Some exactly consistent covering realization `U` with legal top-free types on
`(M ⊕ ℕ) ⊕ ℕ` gives every tuple of old points of `M` its evaluation in `R`, `none` included, and
has every integer cut closed for its canonical closure.  Proof: the ascending block
(`Realization.AscendingBlockTarget`) over the descending block
(`Realization.DescendingBlockTarget`), whose suffix cuts stay closed by
`Realization.imageClosureOfEvalEmbeddingTarget`.  Countability is of the old carrier only.
Construction over a given realization.  Proved (`Realization.integerBlockTarget`). -/
def IntegerBlockTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ [Countable M], Order.IsSuccLimit α →
    ∀ (R : Realization.{u, v} α M), R.IsConsistent → R.IsCovering → R.HasLegalTypes →
      R.HasTopFreeTypes →
      ∃ (U : Realization.{u, v} α ((M ⊕ ℕ) ⊕ ℕ)) (hU : U.IsConsistent) (hUc : U.IsCovering),
        U.HasLegalTypes ∧ U.HasTopFreeTypes ∧
        (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M),
          U.eval ((t.trans Function.Embedding.inl).trans Function.Embedding.inl) = R.eval t) ∧
        ∀ z, (U.closure hU hUc).IsClosed (integerCut z)

/-- **Integer cuts after a descending and an ascending block.**  Let `S` on `M ⊕ ℕ` be exactly
consistent and covering with every suffix cut closed, and `U` on `(M ⊕ ℕ) ⊕ ℕ` exactly consistent
and covering, giving every tuple of `M ⊕ ℕ` its evaluation in `S`, with every prefix cut closed.
Then every integer cut is closed in `U`: those at `n ≥ 0` are prefix cuts, and those at `-(j + 1)`
are the images of the suffix cuts of `S` (`Realization.imageClosureOfEvalEmbeddingTarget`). -/
theorem isClosed_integerCut_of {α : Ordinal.{u}} {S : Realization.{u, v} α (M ⊕ ℕ)}
    (hS : S.IsConsistent) (hSc : S.IsCovering)
    (hScut : ∀ k, (S.closure hS hSc).IsClosed (suffixCut k))
    {U : Realization.{u, v} α ((M ⊕ ℕ) ⊕ ℕ)} (hU : U.IsConsistent) (hUc : U.IsCovering)
    (hUev : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M ⊕ ℕ), U.eval (t.trans Function.Embedding.inl) = S.eval t)
    (hUcut : ∀ n, (U.closure hU hUc).IsClosed (prefixCut n)) (z : ℤ) :
    (U.closure hU hUc).IsClosed (integerCut z) := by
  cases z with
  | ofNat n => rw [integerCut_ofNat]; exact hUcut (n + 1)
  | negSucc j =>
    have himg := (imageClosureOfEvalEmbeddingTarget S U hS hSc hU hUc Function.Embedding.inl
      fun n t p hp ↦ (hUev t).trans hp).1 (suffixCut j)
    rw [(hScut j).closure_eq] at himg
    rw [integerCut_negSucc]
    exact (U.closure hU hUc).isClosed_iff.mpr himg.symm

/-- **The block of order type `ℤ` over a countable realization**, the target form: the ascending
block (`Realization.ascendingBlockTarget`) over the descending block
(`Realization.descendingBlockTarget`), with the integer cuts closed by
`Realization.isClosed_integerCut_of`. -/
theorem integerBlockTarget : IntegerBlockTarget.{u, v} := by
  intro α M _ hα R hR hc hL hT
  obtain ⟨S, hS, hSc, hSL, hST, hSev, hScut⟩ := descendingBlockTarget hα R hR hc hL hT
  obtain ⟨U, hU, hUc, hUL, hUT, hUev, hUcut⟩ := ascendingBlockTarget hα S hS hSc hSL hST
  exact ⟨U, hU, hUc, hUL, hUT, fun n t ↦ by rw [hUev, hSev],
    isClosed_integerCut_of hS hSc hScut hU hUc hUev hUcut⟩

/-- **Target: the block of order type `ℤ` with a request served after the descending part.**  At a
limit stage `α`, let `R` be an exactly consistent covering realization with legal top-free types on
a countable carrier `M`.  Some exactly consistent covering realization `S` with legal top-free
types on `M ⊕ ℕ` (the descending part) gives every tuple of old points its evaluation in `R`,
`none` included, and has every suffix cut closed; and for every occurrence `x` of `S` and every
top-free coface `d` of its type, some exactly consistent covering realization `U` with legal
top-free types on `(M ⊕ ℕ) ⊕ ℕ` gives every tuple of `M ⊕ ℕ` its evaluation in `S`, `none`
included, has every integer cut closed, and gives the tuple of `x` followed by the first ascending
point `Sum.inr 0` the type `d`.  The request may involve descending points; no descending point
serves.  Construction over a given realization.  Proved (`Realization.integerBlockServiceTarget`).
-/
def IntegerBlockServiceTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ [Countable M], Order.IsSuccLimit α →
    ∀ (R : Realization.{u, v} α M), R.IsConsistent → R.IsCovering → R.HasLegalTypes →
      R.HasTopFreeTypes →
      ∃ (S : Realization.{u, v} α (M ⊕ ℕ)) (hS : S.IsConsistent) (hSc : S.IsCovering),
        S.HasLegalTypes ∧ S.HasTopFreeTypes ∧
        (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), S.eval (t.trans Function.Embedding.inl) = R.eval t) ∧
        (∀ k, (S.closure hS hSc).IsClosed (suffixCut k)) ∧
        ∀ (x : S.Occurrence), ∀ d ∈ x.type.cofaces, d.IsTopFree →
          ∃ (U : Realization.{u, v} α ((M ⊕ ℕ) ⊕ ℕ)) (hU : U.IsConsistent)
            (hUc : U.IsCovering), U.HasLegalTypes ∧ U.HasTopFreeTypes ∧
            (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M ⊕ ℕ),
              U.eval (t.trans Function.Embedding.inl) = S.eval t) ∧
            (∀ z, (U.closure hU hUc).IsClosed (integerCut z)) ∧
            U.eval (appendBlockPoint x.tuple 0) = some d

/-- **The block of order type `ℤ` with a request served after the descending part**, the target
form: the descending block (`Realization.descendingBlockTarget`), then for each request the
ascending block with that request served (`Realization.ascendingBlockServiceTarget`) over it; the
integer cuts are closed by `Realization.isClosed_integerCut_of`. -/
theorem integerBlockServiceTarget : IntegerBlockServiceTarget.{u, v} := by
  intro α M _ hα R hR hc hL hT
  obtain ⟨S, hS, hSc, hSL, hST, hSev, hScut⟩ := descendingBlockTarget hα R hR hc hL hT
  refine ⟨S, hS, hSc, hSL, hST, hSev, hScut, fun x d hd hdt ↦ ?_⟩
  obtain ⟨U, hU, hUc, hUL, hUT, hUev, hUcut, hUd⟩ :=
    ascendingBlockServiceTarget hα S hS hSc hSL hST x d hd hdt
  exact ⟨U, hU, hUc, hUL, hUT, hUev, isClosed_integerCut_of hS hSc hScut hU hUc hUev hUcut, hUd⟩

/-- **Target: the order of a block of order type `ℤ`** (given-realization).  Let `U` on
`(M ⊕ ℕ) ⊕ ℕ` be exactly consistent and covering with every integer cut closed.  For every
infinite `B ⊆ M`, the block point enumerated by `i` lies in the closure of `B` with the block
point enumerated by `j` added exactly when `i ≤ j`, and every old point of `M` lies strictly before
every block point in the exterior relation of `B`.  About every realization satisfying the
hypotheses; asserts no existence.  Proved (`Realization.integerBlockOrderTarget`). -/
def IntegerBlockOrderTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ (U : Realization.{u, v} α ((M ⊕ ℕ) ⊕ ℕ))
    (hU : U.IsConsistent) (hUc : U.IsCovering),
    (∀ z, (U.closure hU hUc).IsClosed (integerCut z)) →
    ∀ ⦃B : Set M⦄, B.Infinite →
      (∀ i j : ℤ, integerBlockPoint i ∈ U.closure hU hUc
        (insert (integerBlockPoint j) ((fun a : M ↦ Sum.inl (Sum.inl a)) '' B)) ↔ i ≤ j) ∧
      ∀ (a : M) (j : ℤ), Sum.inl (Sum.inl a) ∈ U.closure hU hUc
          (insert (integerBlockPoint j) ((fun a : M ↦ Sum.inl (Sum.inl a)) '' B)) ∧
        integerBlockPoint j ∉ U.closure hU hUc
          (insert (Sum.inl (Sum.inl a)) ((fun a : M ↦ Sum.inl (Sum.inl a)) '' B))

/-- **The order of a block of order type `ℤ`**, the target form: the old points of `M` form a
closed set (`Closure.isClosed_of_isClosed_cuts`, `ℤ` having no least element), and the order is
`Closure.mem_setClosure_insert_iff_of_isClosed_cuts` with index `ℤ`; the old points come first by
`Closure.rootBeforeExteriorTarget`. -/
theorem integerBlockOrderTarget : IntegerBlockOrderTarget.{u, v} := by
  intro α M U hU hUc hcut B hB
  have hgen := exists_subset_card_le_two_hullClosure_eq hU hUc
  have hBD : (fun a : M ↦ (Sum.inl (Sum.inl a) : (M ⊕ ℕ) ⊕ ℕ)) '' B ⊆
      Set.range fun a : M ↦ Sum.inl (Sum.inl a) := Set.image_subset_range _ _
  have hBi : ((fun a : M ↦ (Sum.inl (Sum.inl a) : (M ⊕ ℕ) ⊕ ℕ)) '' B).Infinite :=
    hB.image fun a _ b _ h ↦ by simpa using h
  have hD : (U.closure hU hUc).IsClosed (Set.range fun a : M ↦ Sum.inl (Sum.inl a)) :=
    Closure.isClosed_of_isClosed_cuts (I := ℤ) integerBlockPoint_injective hcut
  exact ⟨fun i j ↦ Closure.mem_setClosure_insert_iff_of_isClosed_cuts
      (c := U.hullClosure hU hUc) hgen integerBlockPoint hBi hBD hD integerBlockPoint_injective
      integerBlockPoint_notMem hcut i j,
    fun a j ↦ Closure.rootBeforeExteriorTarget _ hgen hBi hD hBD ⟨a, rfl⟩
      (integerBlockPoint_notMem j)⟩

end Integer

end VaughtConjecture.Realization
