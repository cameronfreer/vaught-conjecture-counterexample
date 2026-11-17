/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.OptionAttachment
import VaughtConjecture.Extension.TowerTransfer

/-!
# Finite suffix charts over a chain of occurrences

The finite charts of a descending block over a realization `R` on `M`.  The carrier of the block is
`M ⊕ ℕ`: the old points `Sum.inl a` and the block points `y_j = Sum.inr j`.

**Suffix charts.**  A *suffix chart* over an occurrence `x` of `R` with `k` block points
(`Realization.IsSuffixChart`) is a tuple `w` of `M ⊕ ℕ` with a legal top-free stage type `T`:

* `w` lists the old points of `x`, in the order of the tuple of `x`, followed by the block points
  `y_{k-1}, …, y_0`, newest first (`w` is `Realization.suffixTuple`,
  `Realization.IsSuffixChart.eq_suffixTuple`);
* `T` is a tower over the type of `x` along the old positions (`StageType.IsTowerOver`), so the
  old points carry the type that `R` gives them, literally.

Every *suffix face* — the old points of `x` with the block points `y_j` for `i ≤ j < k` — is then
a closed face of `T` (`Realization.IsSuffixChart.exists_suffix_face`): it is the initial segment of
`w` of length `x.arity + (k - i)`, a stage of the tower
(`StageType.IsTowerOver.exists_restrictFace_castLEEmb`).

**The statement** (`Realization.ExistsSuffixChartsTarget`): along any monotone sequence `c` of
occurrences of an exactly consistent realization with legal top-free types, at a limit stage, there
are suffix charts over `c k` with `k` block points, each the face of the next along a literal face
map, as in `Realization.ChartChainRealizationTarget`.  No countability: exhaustion of the carrier
by the occurrences is used only for the union (`VaughtConjecture.AlephOne.DescendingBlock`).
Proved (`Realization.existsSuffixChartsTarget`), by recursion on `k`: chart `k + 1` is the tower
transfer (`StageType.exists_isTopFree_tower_transfer`) of chart `k` onto a top-free one-point
coface of the type of `c (k + 1)` (`StageType.exists_isTopFree_mem_cofaces`), whose new point is
`y_k` (`Realization.IsSuffixChart.exists_succ`).  The position formula of the transfer places the
old block points after `y_k`, in their order.

## Placement

This file belongs to Layer 0 of `roadmap/README.md`, beside
`VaughtConjecture.Realization.ChartChain`; it is used by the descending block of the `ℵ₁`
companion construction.
-/

universe u v

namespace VaughtConjecture.Realization

variable {α : Ordinal.{u}} {M : Type v}

/-- The **suffix points** from `i` to `k` over a finite set `F` of old points: the old points of
`F`, read in `M ⊕ ℕ`, and the block points `Sum.inr j` with `i ≤ j < k`. -/
def suffixPoints (F : Finset M) (i k : ℕ) : Set (M ⊕ ℕ) :=
  Sum.inl '' (F : Set M) ∪ Sum.inr '' Set.Ico i k

/-- The **suffix tuple** on `a + k` points: the tuple `t` of old points, read in `M ⊕ ℕ`, followed
by the block points `Sum.inr (k - 1), …, Sum.inr 0`, newest first.  The number of points is given
up to an equation, so that it can be an arity found by a construction. -/
def suffixTuple {a : ℕ} (t : Fin a ↪ M) (k : ℕ) {N : ℕ} (hN : N = a + k) : Fin N ↪ M ⊕ ℕ where
  toFun i := if hi : (i : ℕ) < a then Sum.inl (t ⟨i, hi⟩) else Sum.inr (k - 1 - (i - a))
  inj' i j hij := by
    have hi' := i.isLt
    have hj' := j.isLt
    simp only at hij
    split_ifs at hij with hi hj
    · exact Fin.ext (by simpa using congrArg Fin.val (t.injective (Sum.inl_injective hij)))
    · exact Fin.ext (by have := Sum.inr_injective hij; omega)

theorem suffixTuple_apply {a : ℕ} (t : Fin a ↪ M) (k : ℕ) {N : ℕ} (hN : N = a + k) (i : Fin N) :
    suffixTuple t k hN i =
      if hi : (i : ℕ) < a then Sum.inl (t ⟨i, hi⟩) else Sum.inr (k - 1 - (i - a)) :=
  rfl

/-- A **suffix chart** over the occurrence `x` with `k` block points: the tuple `w` of `M ⊕ ℕ`
lists the old points of `x` in the order of its tuple, followed by the block points
`Sum.inr (k - 1), …, Sum.inr 0`, newest first; the stage type `T` is legal, top-free and a tower
over the type of `x` along the old positions.  Every suffix face is then closed
(`Realization.IsSuffixChart.exists_suffix_face`). -/
structure IsSuffixChart (R : Realization.{u, v} α M) (x : R.Occurrence) (k : ℕ) {N : ℕ}
    (w : Fin N ↪ M ⊕ ℕ) (T : StageType.{u} α N) : Prop where
  /-- The chart is legal. -/
  isLegal : T.IsLegal
  /-- The chart is top-free. -/
  isTopFree : T.IsTopFree
  /-- The chart has the old points of `x` and `k` block points. -/
  arity_eq : N = x.arity + k
  /-- The chart is a tower over the type of `x` along the old positions, which list the tuple of
  `x`. -/
  exists_isTowerOver : ∃ o : Fin x.arity ↪ Fin N,
    o.trans w = x.tuple.trans Function.Embedding.inl ∧ StageType.IsTowerOver x.type o T
  /-- After the old positions, the block points come newest first. -/
  apply_block : ∀ (s : ℕ) (hs : x.arity + s < N), w ⟨x.arity + s, hs⟩ = Sum.inr (k - 1 - s)

namespace IsSuffixChart

variable {R : Realization.{u, v} α M} {x : R.Occurrence} {k N : ℕ} {w : Fin N ↪ M ⊕ ℕ}
  {T : StageType.{u} α N}

/-- The tuple of a suffix chart is the suffix tuple of the occurrence. -/
theorem eq_suffixTuple (h : R.IsSuffixChart x k w T) : w = suffixTuple x.tuple k h.arity_eq := by
  obtain ⟨o, ho, htow⟩ := h.exists_isTowerOver
  refine Function.Embedding.ext fun i ↦ ?_
  rw [suffixTuple_apply]
  split_ifs with hi
  · have hoi : o ⟨i, hi⟩ = i := Fin.ext (htow.val_apply _)
    simpa [hoi] using DFunLike.congr_fun ho ⟨i, hi⟩
  · have hs : x.arity + (i - x.arity) < N := by omega
    exact (congrArg w (Fin.ext (by simp; omega))).trans (h.apply_block (i - x.arity) hs)

/-- The value of the tuple of a suffix chart at a position. -/
theorem apply_eq (h : R.IsSuffixChart x k w T) (i : Fin N) :
    w i = if hi : (i : ℕ) < x.arity then Sum.inl (x.tuple ⟨i, hi⟩)
      else Sum.inr (k - 1 - (i - x.arity)) := by
  rw [h.eq_suffixTuple, suffixTuple_apply]

/-- **Suffix faces are closed**: for `i ≤ k`, the old points of `x` with the block points
`Sum.inr j`, `i ≤ j < k`, are the points of a closed face of the chart, the initial segment of
length `x.arity + (k - i)`, a stage of the tower. -/
theorem exists_suffix_face (h : R.IsSuffixChart x k w T) {i : ℕ} (hik : i ≤ k) :
    ∃ (r : ℕ) (f : Fin r ↪ Fin N),
      Set.range (f.trans w) = suffixPoints x.support i k ∧
        (StageType.restrictFace f T).isSome := by
  obtain ⟨o, -, htow⟩ := h.exists_isTowerOver
  have hN := h.arity_eq
  have hrN : x.arity + (k - i) ≤ N := by omega
  obtain ⟨q, hq, -⟩ := htow.exists_restrictFace_castLEEmb (Nat.le_add_right _ _) hrN
  refine ⟨_, Fin.castLEEmb hrN, ?_, by simp [hq]⟩
  ext y
  simp only [Set.mem_range, Function.Embedding.trans_apply, suffixPoints, Set.mem_union,
    Set.mem_image, Finset.mem_coe, Occurrence.mem_support, Set.mem_Ico]
  constructor
  · rintro ⟨p, rfl⟩
    have hp := p.isLt
    rw [h.apply_eq]
    split_ifs with hpa
    · exact Or.inl ⟨_, ⟨_, rfl⟩, rfl⟩
    · simp only [Fin.coe_castLEEmb, Fin.val_castLE] at hpa ⊢
      exact Or.inr ⟨_, ⟨by omega, by omega⟩, rfl⟩
  · rintro (⟨a, ⟨j, rfl⟩, rfl⟩ | ⟨j, ⟨hij, hjk⟩, rfl⟩)
    · refine ⟨⟨j, by omega⟩, ?_⟩
      rw [h.apply_eq]
      simp
    · refine ⟨⟨x.arity + (k - 1 - j), by omega⟩, ?_⟩
      rw [h.apply_eq]
      split_ifs with hlt
      · simp at hlt
      · simp only [Sum.inr.injEq, Fin.coe_castLEEmb, Fin.val_castLE]
        omega

/-- The chart over an occurrence with no block points: its tuple and its type. -/
theorem zero (hL : R.HasLegalTypes) (hT : R.HasTopFreeTypes) (x : R.Occurrence) :
    R.IsSuffixChart x 0 (x.tuple.trans Function.Embedding.inl) x.type where
  isLegal := hL _ _ x.eval_tuple
  isTopFree := hT _ _ x.eval_tuple
  arity_eq := rfl
  exists_isTowerOver := ⟨Function.Embedding.refl _, rfl, StageType.IsTowerOver.refl⟩
  apply_block _ hs := absurd hs (by omega)

/-- **The step of the suffix charts.**  At a limit stage, a suffix chart over `x` with `k` block
points is the face, along a literal face map, of a suffix chart over any occurrence `y` having `x`
as a face, with `k + 1` block points: the tower transfer
(`StageType.exists_isTopFree_tower_transfer`) of the chart onto a top-free one-point coface of the
type of `y` (`StageType.exists_isTopFree_mem_cofaces`), whose new point is `Sum.inr k`. -/
theorem exists_succ (hα : Order.IsSuccLimit α) (hL : R.HasLegalTypes) (hT : R.HasTopFreeTypes)
    {y : R.Occurrence} {g : Fin x.arity ↪ Fin y.arity} (hgy : g.trans y.tuple = x.tuple)
    (hgt : StageType.restrictFace g y.type = some x.type) (h : R.IsSuffixChart x k w T) :
    ∃ (N' : ℕ) (w' : Fin N' ↪ M ⊕ ℕ) (T' : StageType.{u} α N'),
      R.IsSuffixChart y (k + 1) w' T' ∧ ∃ G : Fin N ↪ Fin N', G.trans w' = w ∧
        StageType.restrictFace G T' = some T := by
  obtain ⟨E, ⟨hE, hEy⟩, hEt⟩ := StageType.exists_isTopFree_mem_cofaces hα
    (hL _ _ y.eval_tuple) (hT _ _ y.eval_tuple)
  obtain ⟨o, -, htow⟩ := h.exists_isTowerOver
  have hg' : StageType.restrictFace (g.trans Fin.castSuccEmb) E = some x.type := by
    rw [← StageType.restrictFace_trans _ _ _ hEy, hgt]
  obtain ⟨n', Q, e', G, hQ, hQt, htowQ, hGQ, hcomm, -, -, hcard, hord⟩ :=
    StageType.exists_isTopFree_tower_transfer hα h.isLegal h.isTopFree htow hE hEt hg'
  have htow' := (StageType.IsTowerOver.single hEy).trans htowQ
  have hN := h.arity_eq
  have hn' : n' = y.arity + (k + 1) := by omega
  refine ⟨n', suffixTuple y.tuple (k + 1) hn', Q,
    ⟨hQ, hQt, hn', ⟨_, ?_, htow'⟩, fun s hs ↦ ?_⟩, G, ?_, hGQ⟩
  · refine Function.Embedding.ext fun i ↦ ?_
    have hi : ((Fin.castSuccEmb.trans e') i : ℕ) = i := htow'.val_apply i
    simp only [Function.Embedding.trans_apply, Fin.coe_castSuccEmb] at hi
    simp only [Function.Embedding.trans_apply, Fin.coe_castSuccEmb, suffixTuple_apply,
      Function.Embedding.inl_apply]
    split_ifs with hlt
    · congr 2
      exact Fin.ext hi
    · exact absurd (hi.trans_lt i.isLt) hlt
  · simp [suffixTuple_apply]
  · refine Function.Embedding.ext fun j ↦ ?_
    rw [Function.Embedding.trans_apply, h.apply_eq, suffixTuple_apply]
    split_ifs with hGj hj hj
    · -- an old position goes to its old position in `y`
      have hoj : o ⟨j, hj⟩ = j := Fin.ext (htow.val_apply _)
      have hGo := DFunLike.congr_fun hcomm ⟨j, hj⟩
      simp only [Function.Embedding.trans_apply, hoj] at hGo
      have hval : (G j : ℕ) = g ⟨j, hj⟩ := by
        rw [hGo, htowQ.val_apply]
        rfl
      have hgj : (⟨G j, hGj⟩ : Fin y.arity) = g ⟨j, hj⟩ := Fin.ext hval
      rw [hgj, ← DFunLike.congr_fun hgy ⟨j, hj⟩]
      rfl
    · have := hord j (by omega)
      omega
    · exact absurd (by
        have hGo := DFunLike.congr_fun hcomm ⟨j, hj⟩
        have hoj : o ⟨j, hj⟩ = j := Fin.ext (htow.val_apply _)
        simp only [Function.Embedding.trans_apply, hoj] at hGo
        rw [hGo, htowQ.val_apply]
        simp) hGj
    · have := hord j (by omega)
      congr 1
      omega

end IsSuffixChart

/-- **Target: coherent suffix charts along a chain of occurrences.**  At a limit stage `α`, let
`R` be an exactly consistent realization with legal top-free types on `M`, and `c` a monotone
sequence of occurrences of `R`.  There are tuples `w k` of `M ⊕ ℕ` with stage types `T k`, each a
suffix chart over `c k` with `k` block points (`Realization.IsSuffixChart`), and each chart the
face of the next along a literal face map (`g.trans (w (k + 1)) = w k`, restriction `T k`).  No
countability, and the occurrences need not exhaust `M`.  Construction over a given realization.
Proved (`Realization.existsSuffixChartsTarget`). -/
def ExistsSuffixChartsTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄, Order.IsSuccLimit α → ∀ (R : Realization.{u, v} α M),
    R.IsConsistent → R.HasLegalTypes → R.HasTopFreeTypes →
    ∀ (c : ℕ → R.Occurrence), Monotone c →
      ∃ (N : ℕ → ℕ) (w : ∀ k, Fin (N k) ↪ M ⊕ ℕ) (T : ∀ k, StageType.{u} α (N k)),
        (∀ k, R.IsSuffixChart (c k) k (w k) (T k)) ∧
        ∀ k, ∃ g : Fin (N k) ↪ Fin (N (k + 1)), g.trans (w (k + 1)) = w k ∧
          StageType.restrictFace g (T (k + 1)) = some (T k)

/-- **Coherent suffix charts along a chain of occurrences**, the target form: chart `0` is the
occurrence `c 0` with its type (`Realization.IsSuffixChart.zero`), and chart `k + 1` is obtained
from chart `k` by `Realization.IsSuffixChart.exists_succ` along the face map of `c k` in
`c (k + 1)` (`Realization.Occurrence.le_iff_exists_restrictFace`). -/
theorem existsSuffixChartsTarget : ExistsSuffixChartsTarget.{u, v} := by
  intro α M hα R hR hL hT c hc
  choose g hgc hgt using fun k : ℕ ↦ (Occurrence.le_iff_exists_restrictFace hR).mp
    (hc (Nat.le_succ k))
  let A : ℕ → Type _ := fun k ↦
    {s : Σ N, (Fin N ↪ M ⊕ ℕ) × StageType.{u} α N // R.IsSuffixChart (c k) k s.2.1 s.2.2}
  have hstep : ∀ k (s : A k), ∃ s' : A (k + 1), ∃ G : Fin s.1.1 ↪ Fin s'.1.1,
      G.trans s'.1.2.1 = s.1.2.1 ∧ StageType.restrictFace G s'.1.2.2 = some s.1.2.2 :=
    fun k s ↦ by
      obtain ⟨N', w', T', h', G, hG, hGT⟩ := s.2.exists_succ hα hL hT (hgc k) (hgt k)
      exact ⟨⟨⟨N', w', T'⟩, h'⟩, G, hG, hGT⟩
  choose step hstep using hstep
  let s : ∀ k, A k := fun k ↦
    Nat.rec (motive := A) ⟨⟨_, (c 0).tuple.trans Function.Embedding.inl, (c 0).type⟩,
      IsSuffixChart.zero hL hT (c 0)⟩ step k
  exact ⟨fun k ↦ (s k).1.1, fun k ↦ (s k).1.2.1, fun k ↦ (s k).1.2.2, fun k ↦ (s k).2,
    fun k ↦ hstep k (s k)⟩

end VaughtConjecture.Realization
