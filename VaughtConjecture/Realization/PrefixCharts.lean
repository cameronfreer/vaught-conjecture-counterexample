/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.SuffixCharts

/-!
# Finite prefix charts over a chain of occurrences

The finite charts of an ascending block over a realization `R` on `M`, on the carrier `M ⊕ ℕ`
with the old points `Sum.inl a` and the block points `a_j = Sum.inr j`.

**Prefix charts.**  A *prefix chart* over an occurrence `x` of `R` with `k` block points
(`Realization.IsPrefixChart`) is a tuple `w` of `M ⊕ ℕ` with a legal top-free stage type `T`:
`w` lists the old points of `x` in the order of its tuple, followed by the block points
`a_0, …, a_{k-1}`, oldest first (`w` is `Realization.prefixTuple`), and `T` is a tower over the type
of `x` along the old positions.  Every *prefix face* — the old points of `x` with the block points
`a_j`, `j < n ≤ k` — is then a closed face (`Realization.IsPrefixChart.exists_prefix_face`), a
stage of the tower.

**Coherent prefix charts** (`Realization.exists_prefixCharts`, proved): along a monotone sequence
of occurrences of an exactly consistent realization with legal top-free types, at a limit stage,
there are prefix charts over `c k` with `k` block points, each the face of the next along a
literal face map.  Chart `k + 1` is the tower transfer
(`StageType.exists_isTopFree_tower_transfer`) of chart `k` onto the type of `c (k + 1)`, followed
by a top-free one-point coface (`StageType.exists_isTopFree_mem_cofaces`), whose new point is
`a_k` (`Realization.IsPrefixChart.exists_succ`).  No countability.

## Placement

This file belongs to Layer 0 of `roadmap/README.md`, beside
`VaughtConjecture.Realization.SuffixCharts`; it is used by the ascending block of the `ℵ₁`
companion construction (`VaughtConjecture.AlephOne.IntegerBlock`).
-/

universe u v

namespace VaughtConjecture.Realization

variable {α : Ordinal.{u}} {M : Type v}

/-- The **prefix tuple** on `N` points: the tuple `t` of old points, read in `M ⊕ ℕ`, followed by
the block points `Sum.inr 0, …, Sum.inr (N - a - 1)`, oldest first. -/
def prefixTuple {a : ℕ} (t : Fin a ↪ M) (N : ℕ) : Fin N ↪ M ⊕ ℕ where
  toFun i := if hi : (i : ℕ) < a then Sum.inl (t ⟨i, hi⟩) else Sum.inr (i - a)
  inj' i j hij := by
    simp only at hij
    split_ifs at hij with hi hj
    · exact Fin.ext (by simpa using congrArg Fin.val (t.injective (Sum.inl_injective hij)))
    · exact Fin.ext (by have := Sum.inr_injective hij; omega)

theorem prefixTuple_apply {a : ℕ} (t : Fin a ↪ M) (N : ℕ) (i : Fin N) :
    prefixTuple t N i = if hi : (i : ℕ) < a then Sum.inl (t ⟨i, hi⟩) else Sum.inr (i - a) :=
  rfl

/-- A **prefix chart** over the occurrence `x` with `k` block points: the tuple `w` of `M ⊕ ℕ`
lists the old points of `x` in the order of its tuple, followed by the block points
`Sum.inr 0, …, Sum.inr (k - 1)`, oldest first; the stage type `T` is legal, top-free and a tower
over the type of `x` along the old positions. -/
structure IsPrefixChart (R : Realization.{u, v} α M) (x : R.Occurrence) (k : ℕ) {N : ℕ}
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
  /-- After the old positions, the block points come oldest first. -/
  apply_block : ∀ (s : ℕ) (hs : x.arity + s < N), w ⟨x.arity + s, hs⟩ = Sum.inr s

namespace IsPrefixChart

variable {R : Realization.{u, v} α M} {x : R.Occurrence} {k N : ℕ} {w : Fin N ↪ M ⊕ ℕ}
  {T : StageType.{u} α N}

/-- The tuple of a prefix chart is the prefix tuple of the occurrence. -/
theorem eq_prefixTuple (h : R.IsPrefixChart x k w T) : w = prefixTuple x.tuple N := by
  obtain ⟨o, ho, htow⟩ := h.exists_isTowerOver
  refine Function.Embedding.ext fun i ↦ ?_
  rw [prefixTuple_apply]
  split_ifs with hi
  · have hoi : o ⟨i, hi⟩ = i := Fin.ext (htow.val_apply _)
    simpa [hoi] using DFunLike.congr_fun ho ⟨i, hi⟩
  · have hs : x.arity + (i - x.arity) < N := by omega
    exact (congrArg w (Fin.ext (by simp; omega))).trans (h.apply_block (i - x.arity) hs)

/-- The value of the tuple of a prefix chart at a position. -/
theorem apply_eq (h : R.IsPrefixChart x k w T) (i : Fin N) :
    w i = if hi : (i : ℕ) < x.arity then Sum.inl (x.tuple ⟨i, hi⟩) else Sum.inr (i - x.arity) := by
  rw [h.eq_prefixTuple, prefixTuple_apply]

/-- **Prefix faces are closed**: for `n ≤ k`, the old points of `x` with the block points
`Sum.inr j`, `j < n`, are the points of a closed face of the chart, the initial segment of length
`x.arity + n`, a stage of the tower. -/
theorem exists_prefix_face (h : R.IsPrefixChart x k w T) {n : ℕ} (hnk : n ≤ k) :
    ∃ (r : ℕ) (f : Fin r ↪ Fin N),
      Set.range (f.trans w) = Sum.inl '' (x.support : Set M) ∪ Sum.inr '' Set.Iio n ∧
        (StageType.restrictFace f T).isSome := by
  obtain ⟨o, -, htow⟩ := h.exists_isTowerOver
  have hN := h.arity_eq
  have hrN : x.arity + n ≤ N := by omega
  obtain ⟨q, hq, -⟩ := htow.exists_restrictFace_castLEEmb (Nat.le_add_right _ _) hrN
  refine ⟨_, Fin.castLEEmb hrN, ?_, by simp [hq]⟩
  ext y
  simp only [Set.mem_range, Function.Embedding.trans_apply, Set.mem_union, Set.mem_image,
    Finset.mem_coe, Occurrence.mem_support, Set.mem_Iio]
  constructor
  · rintro ⟨p, rfl⟩
    have hp := p.isLt
    rw [h.apply_eq]
    split_ifs with hpa
    · exact Or.inl ⟨_, ⟨_, rfl⟩, rfl⟩
    · simp only [Fin.coe_castLEEmb, Fin.val_castLE] at hpa ⊢
      exact Or.inr ⟨_, by omega, rfl⟩
  · rintro (⟨a, ⟨j, rfl⟩, rfl⟩ | ⟨j, hj, rfl⟩)
    · refine ⟨⟨j, by omega⟩, ?_⟩
      rw [h.apply_eq]
      simp
    · refine ⟨⟨x.arity + j, by omega⟩, ?_⟩
      rw [h.apply_eq]
      split_ifs with hlt
      · simp at hlt
      · simp only [Sum.inr.injEq, Fin.coe_castLEEmb, Fin.val_castLE]
        omega

/-- The chart over an occurrence with no block points: its tuple and its type. -/
theorem zero (hL : R.HasLegalTypes) (hT : R.HasTopFreeTypes) (x : R.Occurrence) :
    R.IsPrefixChart x 0 (x.tuple.trans Function.Embedding.inl) x.type where
  isLegal := hL _ _ x.eval_tuple
  isTopFree := hT _ _ x.eval_tuple
  arity_eq := rfl
  exists_isTowerOver := ⟨Function.Embedding.refl _, rfl, StageType.IsTowerOver.refl⟩
  apply_block _ hs := absurd hs (by omega)

/-- **The step of the prefix charts, with a prescribed donor.**  At a limit stage, a prefix chart
over `x` with `k` block points is the face, along a literal face map, of a prefix chart over any
occurrence `y` having `x` as a face, with `k + 1` block points; moreover the new point `Sum.inr k`
realizes a prescribed legal top-free donor `d` over a closed face `f₀` of the chart: every tuple `u`
listing the points of `f₀` followed by `Sum.inr k` is a face of the new chart with type `d`.  The
new chart is the tower transfer (`StageType.exists_isTopFree_tower_transfer`) of the chart onto the
type of `y`, followed by the top-free pinned extension
(`StageType.exists_isTopFree_pinned_extension`) along the image of `f₀` with donor `d`. -/
theorem exists_succ_donor (hα : Order.IsSuccLimit α) (hL : R.HasLegalTypes)
    (hT : R.HasTopFreeTypes) {y : R.Occurrence} {g : Fin x.arity ↪ Fin y.arity}
    (hgy : g.trans y.tuple = x.tuple) (hgt : StageType.restrictFace g y.type = some x.type)
    (h : R.IsPrefixChart x k w T) {m : ℕ} {f₀ : Fin m ↪ Fin N} {p : StageType.{u} α m}
    (hp : StageType.restrictFace f₀ T = some p) {d : StageType.{u} α (m + 1)} (hd : d.IsLegal)
    (hdt : d.IsTopFree) (hdp : StageType.restrictFace Fin.castSuccEmb d = some p) :
    ∃ (N' : ℕ) (w' : Fin N' ↪ M ⊕ ℕ) (T' : StageType.{u} α N'),
      R.IsPrefixChart y (k + 1) w' T' ∧ (∃ G : Fin N ↪ Fin N', G.trans w' = w ∧
        StageType.restrictFace G T' = some T) ∧
      ∀ u : Fin (m + 1) ↪ M ⊕ ℕ, Fin.castSuccEmb.trans u = f₀.trans w →
        u (Fin.last m) = Sum.inr k →
          ∃ f : Fin (m + 1) ↪ Fin N', f.trans w' = u ∧ StageType.restrictFace f T' = some d := by
  obtain ⟨o, -, htow⟩ := h.exists_isTowerOver
  obtain ⟨n', Q, e', G, hQ, hQt, htowQ, hGQ, hcomm, -, -, hcard, hord⟩ :=
    StageType.exists_isTopFree_tower_transfer hα h.isLegal h.isTopFree htow
      (hL _ _ y.eval_tuple) (hT _ _ y.eval_tuple) hgt
  have hfQ : StageType.restrictFace (f₀.trans G) Q = some p := by
    rw [← StageType.restrictFace_trans _ _ _ hGQ, hp]
  obtain ⟨E, hE, hEt, hEQ, hEd⟩ :=
    StageType.exists_isTopFree_pinned_extension hα hQ hQt hfQ hd hdt hdp
  have htow' := htowQ.snoc hEQ
  have hN := h.arity_eq
  have hn' : n' + 1 = y.arity + (k + 1) := by omega
  have hGw : (G.trans Fin.castSuccEmb).trans (prefixTuple y.tuple (n' + 1)) = w := by
    refine Function.Embedding.ext fun j ↦ ?_
    rw [Function.Embedding.trans_apply, Function.Embedding.trans_apply, h.apply_eq,
      prefixTuple_apply]
    have hc : ((Fin.castSuccEmb (G j) : Fin (n' + 1)) : ℕ) = G j := rfl
    split_ifs with hGj hj hj
    · -- an old position goes to its old position in `y`
      have hoj : o ⟨j, hj⟩ = j := Fin.ext (htow.val_apply _)
      have hGo := DFunLike.congr_fun hcomm ⟨j, hj⟩
      simp only [Function.Embedding.trans_apply, hoj] at hGo
      have hval : ((Fin.castSuccEmb (G j) : Fin (n' + 1)) : ℕ) = g ⟨j, hj⟩ := by
        rw [hc, hGo, htowQ.val_apply]
      have hgj : (⟨_, hGj⟩ : Fin y.arity) = g ⟨j, hj⟩ := Fin.ext hval
      rw [hgj, ← DFunLike.congr_fun hgy ⟨j, hj⟩]
      rfl
    · have := hord j (by omega)
      omega
    · exact absurd (by
        have hGo := DFunLike.congr_fun hcomm ⟨j, hj⟩
        have hoj : o ⟨j, hj⟩ = j := Fin.ext (htow.val_apply _)
        simp only [Function.Embedding.trans_apply, hoj] at hGo
        rw [hc, hGo, htowQ.val_apply]
        simp) hGj
    · have := hord j (by omega)
      congr 1
      omega
  refine ⟨n' + 1, prefixTuple y.tuple (n' + 1), E,
    ⟨hE, hEt, hn', ⟨_, ?_, htow'⟩, fun s hs ↦ ?_⟩, ⟨G.trans Fin.castSuccEmb, hGw, ?_⟩,
    fun u hu hul ↦ ⟨extendByLast (f₀.trans G), ?_, hEd⟩⟩
  · refine Function.Embedding.ext fun i ↦ ?_
    have hi : ((e'.trans Fin.castSuccEmb) i : ℕ) = i := htow'.val_apply i
    simp only [Function.Embedding.trans_apply, Fin.coe_castSuccEmb, Fin.val_castSucc] at hi
    simp only [Function.Embedding.trans_apply, Fin.coe_castSuccEmb, prefixTuple_apply,
      Function.Embedding.inl_apply, Fin.val_castSucc]
    split_ifs with hlt
    · congr 2
      exact Fin.ext hi
    · exact absurd (hi.trans_lt i.isLt) hlt
  · simp [prefixTuple_apply]
  · rw [← StageType.restrictFace_trans _ _ _ hEQ, hGQ]
  · refine Function.Embedding.ext fun i ↦ ?_
    induction i using Fin.lastCases with
    | last =>
      rw [Function.Embedding.trans_apply, extendByLast_last, hul, prefixTuple_apply]
      split_ifs with hlt
      · simp only [Fin.val_last] at hlt
        omega
      · simp only [Fin.val_last, Sum.inr.injEq]
        omega
    | cast i =>
      rw [Function.Embedding.trans_apply, extendByLast_castSucc]
      have h1 := DFunLike.congr_fun hGw (f₀ i)
      have h2 := DFunLike.congr_fun hu i
      simp only [Function.Embedding.trans_apply, Fin.coe_castSuccEmb] at h1 h2
      exact h1.trans h2.symm

/-- **The step of the prefix charts.**  At a limit stage, a prefix chart over `x` with `k` block
points is the face, along a literal face map, of a prefix chart over any occurrence `y` having `x`
as a face, with `k + 1` block points (`Realization.IsPrefixChart.exists_succ_donor` over the empty
face, with a top-free one-point donor from `StageType.exists_isTopFree_mem_cofaces`). -/
theorem exists_succ (hα : Order.IsSuccLimit α) (hL : R.HasLegalTypes) (hT : R.HasTopFreeTypes)
    {y : R.Occurrence} {g : Fin x.arity ↪ Fin y.arity} (hgy : g.trans y.tuple = x.tuple)
    (hgt : StageType.restrictFace g y.type = some x.type) (h : R.IsPrefixChart x k w T) :
    ∃ (N' : ℕ) (w' : Fin N' ↪ M ⊕ ℕ) (T' : StageType.{u} α N'),
      R.IsPrefixChart y (k + 1) w' T' ∧ ∃ G : Fin N ↪ Fin N', G.trans w' = w ∧
        StageType.restrictFace G T' = some T := by
  obtain ⟨p₀, hp₀⟩ := Option.isSome_iff_exists.mp
    (T.isSome_restrictFace_of_zero Function.Embedding.ofIsEmpty)
  obtain ⟨d, ⟨hd, hdp⟩, hdt⟩ := StageType.exists_isTopFree_mem_cofaces hα
    (h.isLegal.restrictFace _ hp₀) (h.isTopFree.restrictFace hp₀)
  obtain ⟨N', w', T', h', hG, -⟩ := h.exists_succ_donor hα hL hT hgy hgt hp₀ hd hdt hdp
  exact ⟨N', w', T', h', hG⟩

end IsPrefixChart

/-- **Coherent prefix charts along a chain of occurrences.**  At a limit stage `α`, let `R` be an
exactly consistent realization with legal top-free types on `M`, and `c` a monotone sequence of
occurrences of `R`.  There are tuples `w k` of `M ⊕ ℕ` with stage types `T k`, each a prefix chart
over `c k` with `k` block points, and each chart the face of the next along a literal face map.  No
countability.  Proved by recursion on `k` (`Realization.IsPrefixChart.zero`,
`Realization.IsPrefixChart.exists_succ`). -/
theorem exists_prefixCharts {α : Ordinal.{u}} {M : Type v} (hα : Order.IsSuccLimit α)
    (R : Realization.{u, v} α M) (hR : R.IsConsistent) (hL : R.HasLegalTypes)
    (hT : R.HasTopFreeTypes) (c : ℕ → R.Occurrence) (hc : Monotone c) :
    ∃ (N : ℕ → ℕ) (w : ∀ k, Fin (N k) ↪ M ⊕ ℕ) (T : ∀ k, StageType.{u} α (N k)),
      (∀ k, R.IsPrefixChart (c k) k (w k) (T k)) ∧
      ∀ k, ∃ g : Fin (N k) ↪ Fin (N (k + 1)), g.trans (w (k + 1)) = w k ∧
        StageType.restrictFace g (T (k + 1)) = some (T k) := by
  choose g hgc hgt using fun k : ℕ ↦ (Occurrence.le_iff_exists_restrictFace hR).mp
    (hc (Nat.le_succ k))
  let A : ℕ → Type _ := fun k ↦
    {s : Σ N, (Fin N ↪ M ⊕ ℕ) × StageType.{u} α N // R.IsPrefixChart (c k) k s.2.1 s.2.2}
  have hstep : ∀ k (s : A k), ∃ s' : A (k + 1), ∃ G : Fin s.1.1 ↪ Fin s'.1.1,
      G.trans s'.1.2.1 = s.1.2.1 ∧ StageType.restrictFace G s'.1.2.2 = some s.1.2.2 :=
    fun k s ↦ by
      obtain ⟨N', w', T', h', G, hG, hGT⟩ := s.2.exists_succ hα hL hT (hgc k) (hgt k)
      exact ⟨⟨⟨N', w', T'⟩, h'⟩, G, hG, hGT⟩
  choose step hstep using hstep
  let s : ∀ k, A k := fun k ↦
    Nat.rec (motive := A) ⟨⟨_, (c 0).tuple.trans Function.Embedding.inl, (c 0).type⟩,
      IsPrefixChart.zero hL hT (c 0)⟩ step k
  exact ⟨fun k ↦ (s k).1.1, fun k ↦ (s k).1.2.1, fun k ↦ (s k).1.2.2, fun k ↦ (s k).2,
    fun k ↦ hstep k (s k)⟩

/-- **Coherent prefix charts whose first block point realizes a prescribed donor.**  As
`Realization.exists_prefixCharts`, and moreover, for a top-free coface `d` of the type of `c 0`,
every tuple `u` listing the tuple of `c 0` followed by `Sum.inr 0` is a face of chart `1` with type
`d`.  The step from chart `0` to chart `1` is `Realization.IsPrefixChart.exists_succ_donor` over the
whole chart `0`; the later steps are `Realization.IsPrefixChart.exists_succ`. -/
theorem exists_prefixCharts_serving {α : Ordinal.{u}} {M : Type v} (hα : Order.IsSuccLimit α)
    (R : Realization.{u, v} α M) (hR : R.IsConsistent) (hL : R.HasLegalTypes)
    (hT : R.HasTopFreeTypes) (c : ℕ → R.Occurrence) (hc : Monotone c)
    {d : StageType.{u} α ((c 0).arity + 1)} (hd : d ∈ (c 0).type.cofaces) (hdt : d.IsTopFree) :
    ∃ (N : ℕ → ℕ) (w : ∀ k, Fin (N k) ↪ M ⊕ ℕ) (T : ∀ k, StageType.{u} α (N k)),
      (∀ k, R.IsPrefixChart (c k) k (w k) (T k)) ∧
      (∀ k, ∃ g : Fin (N k) ↪ Fin (N (k + 1)), g.trans (w (k + 1)) = w k ∧
        StageType.restrictFace g (T (k + 1)) = some (T k)) ∧
      ∀ u : Fin ((c 0).arity + 1) ↪ M ⊕ ℕ,
        Fin.castSuccEmb.trans u = (c 0).tuple.trans Function.Embedding.inl →
        u (Fin.last _) = Sum.inr 0 →
          ∃ f : Fin ((c 0).arity + 1) ↪ Fin (N 1), f.trans (w 1) = u ∧
            StageType.restrictFace f (T 1) = some d := by
  choose g hgc hgt using fun k : ℕ ↦ (Occurrence.le_iff_exists_restrictFace hR).mp
    (hc (Nat.le_succ k))
  let A : ℕ → Type _ := fun k ↦
    {s : Σ N, (Fin N ↪ M ⊕ ℕ) × StageType.{u} α N // R.IsPrefixChart (c k) k s.2.1 s.2.2}
  have hstep : ∀ k (s : A k), ∃ s' : A (k + 1), ∃ G : Fin s.1.1 ↪ Fin s'.1.1,
      G.trans s'.1.2.1 = s.1.2.1 ∧ StageType.restrictFace G s'.1.2.2 = some s.1.2.2 :=
    fun k s ↦ by
      obtain ⟨N', w', T', h', G, hG, hGT⟩ := s.2.exists_succ hα hL hT (hgc k) (hgt k)
      exact ⟨⟨⟨N', w', T'⟩, h'⟩, G, hG, hGT⟩
  choose step hstep using hstep
  have h₀ := IsPrefixChart.zero hL hT (c 0)
  obtain ⟨N₁, w₁, T₁, h₁, ⟨G₀, hG₀w, hG₀T⟩, hserv⟩ := h₀.exists_succ_donor hα hL hT (hgc 0)
    (hgt 0) (StageType.restrictFace_refl _) hd.1 hdt hd.2
  let s₀ : A 0 := ⟨⟨_, (c 0).tuple.trans Function.Embedding.inl, (c 0).type⟩, h₀⟩
  let t : ∀ k, A (k + 1) := fun k ↦
    Nat.rec (motive := fun k ↦ A (k + 1)) ⟨⟨N₁, w₁, T₁⟩, h₁⟩ (fun k s ↦ step (k + 1) s) k
  let s : ∀ k, A k := fun k ↦ Nat.casesOn (motive := A) k s₀ t
  refine ⟨fun k ↦ (s k).1.1, fun k ↦ (s k).1.2.1, fun k ↦ (s k).1.2.2, fun k ↦ (s k).2,
    fun k ↦ ?_, fun u hu hul ↦ hserv u (by simpa using hu) hul⟩
  rcases k with _ | k
  · exact ⟨G₀, hG₀w, hG₀T⟩
  · exact hstep (k + 1) (s (k + 1))

end VaughtConjecture.Realization
