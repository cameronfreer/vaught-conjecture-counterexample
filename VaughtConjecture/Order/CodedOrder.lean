/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.SetTheory.Cardinal.Regular
import VaughtConjecture.Order.FiniteInterval
import VaughtConjecture.Order.Tail

/-!
# Coded orders: `ω₁`-sums of copies of `ℕ` and `ℤ`, and recovery of the code from a tail

Pure order theory; no closure, realization or stage type appears.

**The coded order.**  For a bit sequence `b : I → Bool` on a linear order `I`, `CodedOrder b` is
the lexicographic sum over `i ∈ I` of the **block** `ℕ` when `b i = false` and `ℤ` when
`b i = true`.  It is realized as the pairs `(i, n)` of the lexicographic product `I ×ₗ ℤ` with
`0 ≤ n` whenever `b i = false`, with the induced linear order; `CodedOrder.rank` is the first
coordinate and `CodedOrder.block b i` the points of rank `i`.

**Parameters and repetition.**  A parameter is a map `A : J → Bool`.  A **repetition scheme** is
a map `r : I → J` all of whose fibres are unbounded in `I` (`CodedOrder.HasUnboundedFibres`); the
coded order of `A` along `r` is `CodedOrder (A ∘ r)`, so every input bit `A j` is the bit of
unboundedly many blocks.  For `I = J = ω₁` a scheme exists: `I ≃ I × I` followed by the first
projection has fibres of size `ℵ₁`, while bounded sets are countable.

**Recovery.**  The blocks are the classes of finite-interval equivalence (`Order.FiniteInterval`),
so an order isomorphism preserves them; an `ℕ`-block has a least point and a `ℤ`-block does not.
Models determine their exterior order only up to a change of root, that is, up to a tail
(`Order.TailEquivalent`: nonempty upper sets).  An isomorphism `e` between tails `U` and `V` of two
coded orders over an `ω₁`-like well-order `I` (well-founded, countable sets bounded above) induces
an isomorphism between final segments of `I` (the ranks of points of `U` and of `V`), which is the
identity on a whole final segment `Set.Ici γ` (proved: `Order.iciIsoEventuallyIdTarget`).
Above `γ` and above the bottom ranks of `U` and `V` (where the first block of a tail may be cut),
every block of `U` is carried onto the block of the same rank in `V`, so the bits agree on all
ranks `> γ`.  Since every fibre of the scheme meets every final segment, the parameters are
equal.  Agreement on a closed unbounded set of ranks would not suffice, as fibres of the scheme
are only unbounded; the proof gives agreement on a final segment.

**Statements.**
* `finiteIntervalIffRankEqTarget` (proved): finite-interval classes are the blocks.
* `blockHasLeastIffTarget` (proved): a block has a least point exactly when its bit is `false`.
* `blockSubsetOfRankLtTarget` (proved): a tail contains every block above the rank of one of its
  points.
* `TailIsoRankEventuallyTarget`, `TailIsoBitsEventuallyTarget`,
  `TailEquivalentBitsEventuallyTarget`, `TailEquivalentInjectiveTarget`: the recovery chain.
  Stated; open.
* `CountableIioTarget`, `CardEqTarget`: cardinality facts.  Stated; open.
* `ExistsUnboundedFibresOmegaOneTarget`, `OmegaOneSpectrumTarget`: at `I = J = ω₁`, `2 ^ ℵ₁`
  parameters with pairwise tail-inequivalent coded orders of cardinality `ℵ₁` all of whose proper
  initial segments are countable.  Stated; open.
-/

universe u v

namespace VaughtConjecture

open Cardinal Ordinal

/-- The **coded order** of a bit sequence `b : I → Bool`: the lexicographic sum over `I` of `ℕ`
at the indices with bit `false` and `ℤ` at the indices with bit `true`, realized as the pairs
`(i, n)` of `I ×ₗ ℤ` with `0 ≤ n` when `b i = false`. -/
def CodedOrder {I : Type u} [LinearOrder I] (b : I → Bool) : Type u :=
  {p : I ×ₗ ℤ // b (ofLex p).1 = false → 0 ≤ (ofLex p).2}

namespace CodedOrder

variable {I : Type u} [LinearOrder I] {b : I → Bool}

instance : LinearOrder (CodedOrder b) :=
  inferInstanceAs (LinearOrder {p : I ×ₗ ℤ // b (ofLex p).1 = false → 0 ≤ (ofLex p).2})

/-- The point `(i, n)` of the coded order. -/
def mk (i : I) (n : ℤ) (h : b i = false → 0 ≤ n) : CodedOrder b := ⟨toLex (i, n), h⟩

/-- The **rank** of a point: the index of its block. -/
def rank (x : CodedOrder b) : I := (ofLex x.1).1

/-- The position of a point inside its block. -/
def pos (x : CodedOrder b) : ℤ := (ofLex x.1).2

/-- The **block** of index `i`: the points of rank `i`. -/
def block (b : I → Bool) (i : I) : Set (CodedOrder b) := {x | rank x = i}

@[simp] theorem rank_mk (i : I) (n : ℤ) (h : b i = false → 0 ≤ n) : rank (mk i n h) = i := rfl

@[simp] theorem pos_mk (i : I) (n : ℤ) (h : b i = false → 0 ≤ n) : pos (mk i n h) = n := rfl

theorem le_iff {x y : CodedOrder b} :
    x ≤ y ↔ rank x < rank y ∨ rank x = rank y ∧ pos x ≤ pos y :=
  Prod.Lex.le_iff

theorem lt_iff {x y : CodedOrder b} :
    x < y ↔ rank x < rank y ∨ rank x = rank y ∧ pos x < pos y :=
  Prod.Lex.lt_iff

/-- The rank is monotone. -/
theorem rank_mono : Monotone (rank (b := b)) := fun _ _ h ↦ Prod.Lex.monotone_fst _ _ h

/-- A point lies before every point of a strictly larger rank. -/
theorem lt_of_rank_lt {x y : CodedOrder b} (h : rank x < rank y) : x < y :=
  lt_iff.mpr (Or.inl h)

theorem ext_rank_pos {x y : CodedOrder b} (h₁ : rank x = rank y) (h₂ : pos x = pos y) : x = y :=
  Subtype.ext (Prod.ext h₁ h₂)

/-! ### Blocks -/

/-- **Target: finite-interval classes are the blocks.**  In a coded order two points are
finite-interval equivalent exactly when they have the same rank.  Proved
(`CodedOrder.finiteIntervalIffRankEqTarget`). -/
def FiniteIntervalIffRankEqTarget : Prop :=
  ∀ ⦃I : Type u⦄ [LinearOrder I] (b : I → Bool) (x y : CodedOrder b),
    Order.FiniteInterval x y ↔ rank x = rank y

/-- Points of one rank are finite-interval equivalent: the interval between them is carried
injectively into an interval of `ℤ` by the position. -/
theorem finiteInterval_of_rank_eq {x y : CodedOrder b} (h : rank x = rank y) :
    Order.FiniteInterval x y := by
  have hsub : Set.uIcc x y ⊆ (block b (rank x)) ∩ pos ⁻¹' Set.uIcc (pos x) (pos y) := by
    intro z hz
    rcases Set.mem_uIcc.mp hz with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have hr : rank z = rank x :=
        le_antisymm (h ▸ rank_mono h₂) (rank_mono h₁)
      refine ⟨hr, Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩)⟩
      · rcases le_iff.mp h₁ with h' | h'
        · exact absurd hr (ne_of_gt h')
        · exact h'.2
      · rcases le_iff.mp h₂ with h' | h'
        · exact absurd (hr.trans h) (ne_of_lt h')
        · exact h'.2
    · have hr : rank z = rank x :=
        le_antisymm (rank_mono h₂) (h ▸ rank_mono h₁)
      refine ⟨hr, Set.mem_uIcc.mpr (Or.inr ⟨?_, ?_⟩)⟩
      · rcases le_iff.mp h₁ with h' | h'
        · exact absurd (hr.trans h) (ne_of_gt h')
        · exact h'.2
      · rcases le_iff.mp h₂ with h' | h'
        · exact absurd hr (ne_of_lt h')
        · exact h'.2
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.of_finite_image ?_ (f := pos) fun z hz w hw hzw ↦
    ext_rank_pos (hz.1.trans hw.1.symm) hzw
  exact (Set.finite_Icc (pos x ⊓ pos y) (pos x ⊔ pos y)).subset
    (Set.image_subset_iff.mpr fun z hz ↦ hz.2)

/-- Points of different ranks are not finite-interval equivalent: the interval contains the part
of the lower block above the lower point, which is infinite. -/
theorem not_finiteInterval_of_rank_lt {x y : CodedOrder b} (h : rank x < rank y) :
    ¬ Order.FiniteInterval x y := by
  intro hfin
  have hmk (n : ℤ) (hn : pos x ≤ n) : b (rank x) = false → 0 ≤ n := fun hb ↦
    (x.2 hb).trans hn
  have himg : (fun n : Set.Ici (pos x) ↦ mk (b := b) (rank x) n (hmk n n.2)) '' Set.univ ⊆
      Set.uIcc x y := by
    rintro _ ⟨n, -, rfl⟩
    refine Set.mem_uIcc.mpr (Or.inl ⟨le_iff.mpr (Or.inr ⟨rfl, n.2⟩), ?_⟩)
    exact le_of_lt (lt_of_rank_lt h)
  have hinj : Function.Injective fun n : Set.Ici (pos x) ↦ mk (b := b) (rank x) n (hmk n n.2) :=
    fun n m hnm ↦ Subtype.ext (congrArg pos hnm)
  have : (Set.univ : Set (Set.Ici (pos x))).Finite :=
    Set.Finite.of_finite_image (hfin.subset himg) hinj.injOn
  exact Set.Ici_infinite (pos x) (Set.finite_coe_iff.mp (Set.finite_univ_iff.mp this))

/-- **Finite-interval classes are the blocks**, the target form. -/
theorem finiteIntervalIffRankEqTarget : FiniteIntervalIffRankEqTarget.{u} := by
  intro I _ b x y
  refine ⟨fun h ↦ ?_, finiteInterval_of_rank_eq⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact not_finiteInterval_of_rank_lt hlt h
  · exact not_finiteInterval_of_rank_lt hlt h.symm

/-- **Target: the least-point test.**  A block has a least point exactly when its bit is `false`
(an `ℕ`-block); a `ℤ`-block has none.  Proved (`CodedOrder.blockHasLeastIffTarget`). -/
def BlockHasLeastIffTarget : Prop :=
  ∀ ⦃I : Type u⦄ [LinearOrder I] (b : I → Bool) (i : I),
    (∃ x ∈ block b i, ∀ y ∈ block b i, x ≤ y) ↔ b i = false

/-- **The least-point test**, the target form: `(i, 0)` is least in an `ℕ`-block, and below a
point `(i, n)` of a `ℤ`-block lies `(i, n - 1)`. -/
theorem blockHasLeastIffTarget : BlockHasLeastIffTarget.{u} := by
  intro I _ b i
  refine ⟨fun ⟨x, hx, hle⟩ ↦ ?_, fun hb ↦ ?_⟩
  · by_contra hb
    have hb' : b i = true := by simpa using hb
    have hy : mk (b := b) i (pos x - 1) (fun h ↦ absurd (hb'.symm.trans h) (by decide)) ∈
        block b i := rfl
    rcases le_iff.mp (hle _ hy) with h | h
    · exact absurd hx (ne_of_lt h)
    · exact absurd h.2 (by simp)
  · refine ⟨mk i 0 fun _ ↦ le_rfl, rfl, fun y hy ↦ le_iff.mpr (Or.inr ⟨hy.symm, ?_⟩)⟩
    have hyi : rank y = i := hy
    exact y.2 (show b (rank y) = false by rw [hyi]; exact hb)

/-- **Target: a tail contains every block above one of its points.**  If `U` is an upper set of a
coded order and `x ∈ U`, then every block of rank `> rank x` lies in `U`.  Proved
(`CodedOrder.blockSubsetOfRankLtTarget`). -/
def BlockSubsetOfRankLtTarget : Prop :=
  ∀ ⦃I : Type u⦄ [LinearOrder I] (b : I → Bool) ⦃U : Set (CodedOrder b)⦄, IsUpperSet U →
    ∀ ⦃x : CodedOrder b⦄, x ∈ U → ∀ ⦃i : I⦄, rank x < i → block b i ⊆ U

/-- **A tail contains every block above one of its points**, the target form. -/
theorem blockSubsetOfRankLtTarget : BlockSubsetOfRankLtTarget.{u} := by
  intro I _ b U hU x hx i hi y hy
  exact hU (lt_of_rank_lt (hy ▸ hi)).le hx

/-! ### Recovery from a tail -/

/-- **Target: a tail isomorphism eventually preserves ranks.**  Let `I` be a well-order in which
every countable set is bounded above.  For bit sequences `b, c` on `I`, nonempty upper sets `U` of
`CodedOrder b` and `V` of `CodedOrder c` and an order isomorphism `e : U ≃o V`, there is `γ` such
that `e` preserves the rank of every point of rank at least `γ`.  Applied to `e.symm`, the same
holds for the inverse.  Stated; open. -/
def TailIsoRankEventuallyTarget : Prop :=
  ∀ ⦃I : Type u⦄ [LinearOrder I] [WellFoundedLT I], (∀ s : Set I, s.Countable → BddAbove s) →
    ∀ (b c : I → Bool) ⦃U : Set (CodedOrder b)⦄ ⦃V : Set (CodedOrder c)⦄, IsUpperSet U →
      IsUpperSet V → U.Nonempty → ∀ e : U ≃o V, ∃ γ : I,
        ∀ x : U, γ ≤ rank (x : CodedOrder b) → rank ((e x : V) : CodedOrder c) = rank x.1

/-- **Target: a tail isomorphism determines the bits on a final segment.**  Under the hypotheses
of `TailIsoRankEventuallyTarget`, there is `γ` with `b i = c i` for every `i > γ`.  Stated;
open. -/
def TailIsoBitsEventuallyTarget : Prop :=
  ∀ ⦃I : Type u⦄ [LinearOrder I] [WellFoundedLT I], (∀ s : Set I, s.Countable → BddAbove s) →
    ∀ (b c : I → Bool) ⦃U : Set (CodedOrder b)⦄ ⦃V : Set (CodedOrder c)⦄, IsUpperSet U →
      IsUpperSet V → U.Nonempty → Nonempty (U ≃o V) → ∃ γ : I, ∀ i, γ < i → b i = c i

/-- **Target: tail-equivalent coded orders have eventually equal bits.**  Over a well-order in
which every countable set is bounded above, if `CodedOrder b` and `CodedOrder c` are
tail-equivalent, then `b` and `c` agree on all indices above some `γ`.  Stated; open. -/
def TailEquivalentBitsEventuallyTarget : Prop :=
  ∀ ⦃I : Type u⦄ [LinearOrder I] [WellFoundedLT I], (∀ s : Set I, s.Countable → BddAbove s) →
    ∀ (b c : I → Bool), Order.TailEquivalent (CodedOrder b) (CodedOrder c) →
      ∃ γ : I, ∀ i, γ < i → b i = c i

/-- A **repetition scheme**: every fibre of `r : I → J` is unbounded in `I`, so every input index
is repeated at arbitrarily large block indices. -/
def HasUnboundedFibres {I : Type u} {J : Type v} [LT I] (r : I → J) : Prop :=
  ∀ (j : J) (i : I), ∃ k, i < k ∧ r k = j

/-- **Target: recovery of the parameter.**  Over a well-order `I` in which every countable set is
bounded above, along a repetition scheme `r : I → J`, two parameters `A, A' : J → Bool` whose
coded orders are tail-equivalent are equal.  Stated; open. -/
def TailEquivalentInjectiveTarget : Prop :=
  ∀ ⦃I : Type u⦄ ⦃J : Type v⦄ [LinearOrder I] [WellFoundedLT I],
    (∀ s : Set I, s.Countable → BddAbove s) → ∀ ⦃r : I → J⦄, HasUnboundedFibres r →
      ∀ A A' : J → Bool, Order.TailEquivalent (CodedOrder (A ∘ r)) (CodedOrder (A' ∘ r)) →
        A = A'

/-! ### Cardinality -/

/-- **Target: proper initial segments are countable.**  If every proper initial segment of `I`
is countable, then so is every proper initial segment `Set.Iio x` of a coded order over `I` (it
lies in the countably many blocks of rank at most `rank x`).  Stated; open. -/
def CountableIioTarget : Prop :=
  ∀ ⦃I : Type u⦄ [LinearOrder I], (∀ i : I, (Set.Iio i).Countable) →
    ∀ (b : I → Bool) (x : CodedOrder b), (Set.Iio x).Countable

/-- **Target: the cardinality of a coded order.**  Over an infinite `I`, a coded order has the
cardinality of `I` (each of its `#I` blocks is countably infinite).  Stated; open. -/
def CardEqTarget : Prop :=
  ∀ ⦃I : Type u⦄ [LinearOrder I], Infinite I → ∀ b : I → Bool, #(CodedOrder b) = #I

/-! ### At `ω₁` -/

/-- **Target: a repetition scheme on `ω₁`.**  Some map from the countable ordinals to themselves
has unbounded fibres.  Stated; open. -/
def ExistsUnboundedFibresOmegaOneTarget : Prop :=
  ∃ r : (ω₁ : Ordinal.{0}).ToType → (ω₁ : Ordinal.{0}).ToType, HasUnboundedFibres r

/-- **Target: `2 ^ ℵ₁` pairwise tail-inequivalent coded orders.**  There is a repetition scheme
`r` on `ω₁` such that the coded orders of the parameters `A : ω₁ → Bool` (there are `2 ^ ℵ₁` of
them) are pairwise tail-inequivalent, each of cardinality `ℵ₁` with every proper initial segment
countable.  Stated; open. -/
def OmegaOneSpectrumTarget : Prop :=
  ∃ r : (ω₁ : Ordinal.{0}).ToType → (ω₁ : Ordinal.{0}).ToType, HasUnboundedFibres r ∧
    (∀ A A' : (ω₁ : Ordinal.{0}).ToType → Bool,
      Order.TailEquivalent (CodedOrder (A ∘ r)) (CodedOrder (A' ∘ r)) → A = A') ∧
    (∀ A : (ω₁ : Ordinal.{0}).ToType → Bool,
      #(CodedOrder (A ∘ r)) = aleph 1 ∧ ∀ x : CodedOrder (A ∘ r), (Set.Iio x).Countable) ∧
    #((ω₁ : Ordinal.{0}).ToType → Bool) = 2 ^ aleph 1

end CodedOrder

end VaughtConjecture
