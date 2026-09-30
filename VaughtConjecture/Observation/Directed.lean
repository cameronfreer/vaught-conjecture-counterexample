/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite

/-!
# Monotone natural-number observations on a directed preorder

Roadmap, Layer 0, "Directed finite observations".  A monotone function `f : P → ℕ` on a preorder
either is eventually constant along `Filter.atTop` or tends to `atTop`.  The outcome is recorded
by its `ℕ∞`-valued limit `⨆ p, (f p : ℕ∞)`: a finite value `n` means `f` is eventually `n`, and
`⊤` means `f` escapes every bound.  (That the casts converge to this supremum in the order
topology is Mathlib's `tendsto_atTop_iSup`, and the dichotomy is the `ℕ` case of Mathlib's
topological `tendsto_atTop_of_monotone`; no new notion of convergence is introduced, and the
statements here avoid the topology imports.)

* `eventually_eq_of_iSup_natCast_eq`, `tendsto_atTop_atTop_of_iSup_natCast_eq_top`, and the
  dichotomy `eventually_eq_or_tendsto_atTop`: these hold on any preorder, directed or not.  By
  `Filter.tendsto_atTop` and `Filter.Tendsto.eventually_gt_atTop`, `Tendsto f atTop atTop` is the
  statement `∀ n, ∀ᶠ p in atTop, n < f p`.
* `iSup_natCast_eq_natCast_iff` and `iSup_natCast_eq_top_iff`: on a nonempty directed preorder
  (where `atTop` is a proper filter) the two cases are exclusive and the limit is determined by
  the eventual behaviour.
* `eventually_forall_natCast_eq_iSup_or_lt`: **finite synchronization**.  For finitely many
  monotone functions and a bound `N`, eventually every function with finite limit has reached it
  and every function with infinite limit exceeds `N`.  On a nonempty directed preorder,
  `Filter.eventually_atTop` turns this into a single threshold `p₀`.
* `eventually_comp_eq_iff` and `tendsto_comp_atTop_atTop_iff`: **cofinal reindexing**.  Along a map
  `g : Q → P` with `Tendsto g l atTop` for a proper filter `l` on `Q` (for `l = atTop` and
  monotone `g` on a nonempty directed `Q` this is cofinality of the range, by
  `Monotone.tendsto_atTop_atTop_iff`; for a cofinal subset take `g = Subtype.val`), the eventual
  value and the escape of `f ∘ g` are those of `f`.  These two hold for monotone `f` into any
  partial order, respectively preorder.  The corresponding invariance of the `ℕ∞` limit is
  Mathlib's `Monotone.iSup_comp_tendsto_atTop`.
-/

namespace VaughtConjecture.Observation

open Filter Set

variable {P Q : Type*} [Preorder P] {f : P → ℕ}

/-- A monotone `ℕ`-valued function whose `ℕ∞` supremum is the finite value `n` is eventually equal
to `n`. -/
theorem eventually_eq_of_iSup_natCast_eq (hf : Monotone f) {n : ℕ}
    (h : ⨆ p, (f p : ℕ∞) = n) : ∀ᶠ p in atTop, f p = n := by
  rcases isEmpty_or_nonempty P with hP | hP
  · exact .of_forall isEmptyElim
  obtain ⟨p₀, hp₀⟩ := ENat.exists_eq_iSup_of_lt_top (h ▸ ENat.natCast_lt_top n)
  filter_upwards [eventually_ge_atTop p₀] with p hp
  have hle : (f p : ℕ∞) ≤ n := h ▸ le_iSup (fun p ↦ (f p : ℕ∞)) p
  have hge : (n : ℕ∞) ≤ f p := h ▸ hp₀ ▸ Nat.cast_le.2 (hf hp)
  exact_mod_cast hle.antisymm hge

/-- A monotone `ℕ`-valued function whose `ℕ∞` supremum is `⊤` tends to `atTop`. -/
theorem tendsto_atTop_atTop_of_iSup_natCast_eq_top (hf : Monotone f) (h : ⨆ p, (f p : ℕ∞) = ⊤) :
    Tendsto f atTop atTop :=
  tendsto_atTop_atTop_of_monotone' hf (ENat.iSup_natCast_eq_top.1 h)

/-- **Dichotomy.**  A monotone `ℕ`-valued function on a preorder is eventually constant or tends
to `atTop`. -/
theorem eventually_eq_or_tendsto_atTop (hf : Monotone f) :
    (∃ n : ℕ, ∀ᶠ p in atTop, f p = n) ∨ Tendsto f atTop atTop := by
  by_cases h : ⨆ p, (f p : ℕ∞) = ⊤
  · exact .inr (tendsto_atTop_atTop_of_iSup_natCast_eq_top hf h)
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h
    exact .inl ⟨n, eventually_eq_of_iSup_natCast_eq hf hn.symm⟩

section Directed

variable [Nonempty P] [IsDirectedOrder P]

/-- On a nonempty directed preorder, the `ℕ∞` supremum of a monotone `ℕ`-valued function is the
finite value `n` iff the function is eventually equal to `n`. -/
theorem iSup_natCast_eq_natCast_iff (hf : Monotone f) {n : ℕ} :
    ⨆ p, (f p : ℕ∞) = n ↔ ∀ᶠ p in atTop, f p = n := by
  refine ⟨eventually_eq_of_iSup_natCast_eq hf, fun h ↦ ?_⟩
  obtain ⟨a, ha⟩ := h.exists_forall_of_atTop
  refine le_antisymm (iSup_le fun p ↦ ?_) (le_iSup_of_le a (Nat.cast_le.2 (ha a le_rfl).ge))
  obtain ⟨c, hpc, hac⟩ := exists_ge_ge p a
  exact Nat.cast_le.2 ((hf hpc).trans (ha c hac).le)

/-- On a nonempty directed preorder, the `ℕ∞` supremum of a monotone `ℕ`-valued function is `⊤`
iff the function tends to `atTop`. -/
theorem iSup_natCast_eq_top_iff (hf : Monotone f) : ⨆ p, (f p : ℕ∞) = ⊤ ↔ Tendsto f atTop atTop :=
  ⟨tendsto_atTop_atTop_of_iSup_natCast_eq_top hf,
    fun h ↦ ENat.iSup_natCast_eq_top.2 (not_bddAbove_of_tendsto_atTop h)⟩

end Directed

/-- **Finite synchronization.**  For finitely many monotone `ℕ`-valued functions on a preorder and
a bound `N`, eventually each function either equals its `ℕ∞` supremum, or has supremum `⊤` and
exceeds `N`. -/
theorem eventually_forall_natCast_eq_iSup_or_lt {ι : Type*} [Finite ι] {f : ι → P → ℕ}
    (hf : ∀ i, Monotone (f i)) (N : ℕ) :
    ∀ᶠ p in atTop, ∀ i,
      (f i p : ℕ∞) = ⨆ q, (f i q : ℕ∞) ∨ (⨆ q, (f i q : ℕ∞)) = ⊤ ∧ N < f i p := by
  refine eventually_all.2 fun i ↦ ?_
  by_cases h : ⨆ q, (f i q : ℕ∞) = ⊤
  · filter_upwards [(tendsto_atTop_atTop_of_iSup_natCast_eq_top (hf i) h).eventually_gt_atTop N]
      with p hp using .inr ⟨h, hp⟩
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h
    filter_upwards [eventually_eq_of_iSup_natCast_eq (hf i) hn.symm] with p hp
    exact .inl (by rw [hp, hn])

section Reindex

variable {l : Filter Q} [l.NeBot] {g : Q → P}

/-- **Cofinal reindexing preserves the eventual value.**  Along `g` tending to `atTop` with
respect to a proper filter `l`, a monotone `f` into a partial order is eventually `n` iff `f ∘ g`
is eventually `n`. -/
theorem eventually_comp_eq_iff {β : Type*} [PartialOrder β] {f : P → β} (hf : Monotone f)
    (hg : Tendsto g l atTop) {n : β} :
    (∀ᶠ q in l, f (g q) = n) ↔ ∀ᶠ p in atTop, f p = n := by
  refine ⟨fun h ↦ ?_, fun h ↦ hg.eventually h⟩
  obtain ⟨q₀, hq₀⟩ := h.exists
  filter_upwards [eventually_ge_atTop (g q₀)] with p hp
  obtain ⟨q, hpq, hq⟩ := ((hg.eventually_ge_atTop p).and h).exists
  exact le_antisymm (hq ▸ hf hpq) (hq₀ ▸ hf hp)

/-- **Cofinal reindexing preserves escape.**  Along `g` tending to `atTop` with respect to a
proper filter `l`, a monotone `f` into a preorder tends to `atTop` iff `f ∘ g` does. -/
theorem tendsto_comp_atTop_atTop_iff {β : Type*} [Preorder β] {f : P → β} (hf : Monotone f)
    (hg : Tendsto g l atTop) : Tendsto (f ∘ g) l atTop ↔ Tendsto f atTop atTop :=
  ⟨tendsto_atTop_of_monotone_of_subseq hf, fun h ↦ h.comp hg⟩

end Reindex

end VaughtConjecture.Observation
