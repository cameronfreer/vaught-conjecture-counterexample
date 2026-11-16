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
unboundedly many blocks.  Repetition makes eventual agreement recover the entire parameter,
avoiding any additional cardinal-arithmetic assumption.  For `I = J = ω₁` a scheme exists:
`I ≃ I × I` followed by the first projection has fibres of size `ℵ₁`, while bounded sets are
countable.

**Recovery.**  The blocks are the classes of finite-interval equivalence (`Order.FiniteInterval`),
so an order isomorphism preserves them; an `ℕ`-block has a least point and a `ℤ`-block does not.
Models determine their exterior order only up to a change of root, that is, up to a tail
(`Order.TailEquivalent`: nonempty upper sets).  An isomorphism `e` between tails `U` and `V` of two
coded orders over an `ω₁`-like well-order `I` (well-founded, countable sets bounded above) induces
an isomorphism between final segments of `I` (the ranks of points of `U` and of `V`), which is the
identity on a whole final segment `Set.Ici γ` (proved: `Order.iciIsoEventuallyIdTarget`).
Above `γ` and strictly above the bottom ranks of both `U` and `V`, every block of `U` is a whole
block, carried onto the whole block of the same rank in `V`, so the least-point test gives
agreement of the bits on all those ranks.  The bottom blocks are excluded on both sides: a tail
may cut its first block, and a cut `ℤ`-block can have a least point.  Since every fibre of the
scheme meets every final segment, the parameters are equal.  Agreement on a closed unbounded set
of ranks would not suffice, as fibres of the scheme are only unbounded; the proof gives agreement
on a final segment.

**Statements.**
* `finiteIntervalIffRankEqTarget` (proved): finite-interval classes are the blocks.
* `blockHasLeastIffTarget` (proved): a block has a least point exactly when its bit is `false`.
* `blockSubsetOfRankLtTarget` (proved): a tail contains every block above the rank of one of its
  points.
* `tailIsoRankEventuallyTarget`, `tailIsoBitsEventuallyTarget`,
  `tailEquivalentBitsEventuallyTarget`, `tailEquivalentInjectiveTarget` (proved): the recovery
  chain.
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
holds for the inverse.  Proved (`CodedOrder.tailIsoRankEventuallyTarget`). -/
def TailIsoRankEventuallyTarget : Prop :=
  ∀ ⦃I : Type u⦄ [LinearOrder I] [WellFoundedLT I], (∀ s : Set I, s.Countable → BddAbove s) →
    ∀ (b c : I → Bool) ⦃U : Set (CodedOrder b)⦄ ⦃V : Set (CodedOrder c)⦄, IsUpperSet U →
      IsUpperSet V → U.Nonempty → ∀ e : U ≃o V, ∃ γ : I,
        ∀ x : U, γ ≤ rank (x : CodedOrder b) → rank ((e x : V) : CodedOrder c) = rank x.1

/-- **Target: a tail isomorphism determines the bits on a final segment.**  Under the hypotheses
of `TailIsoRankEventuallyTarget`, there is `γ` with `b i = c i` for every `i > γ`.  Proved
(`CodedOrder.tailIsoBitsEventuallyTarget`). -/
def TailIsoBitsEventuallyTarget : Prop :=
  ∀ ⦃I : Type u⦄ [LinearOrder I] [WellFoundedLT I], (∀ s : Set I, s.Countable → BddAbove s) →
    ∀ (b c : I → Bool) ⦃U : Set (CodedOrder b)⦄ ⦃V : Set (CodedOrder c)⦄, IsUpperSet U →
      IsUpperSet V → U.Nonempty → Nonempty (U ≃o V) → ∃ γ : I, ∀ i, γ < i → b i = c i

/-- **Target: tail-equivalent coded orders have eventually equal bits.**  Over a well-order in
which every countable set is bounded above, if `CodedOrder b` and `CodedOrder c` are
tail-equivalent, then `b` and `c` agree on all indices above some `γ`.  Proved
(`CodedOrder.tailEquivalentBitsEventuallyTarget`). -/
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
coded orders are tail-equivalent are equal.  Proved
(`CodedOrder.tailEquivalentInjectiveTarget`). -/
def TailEquivalentInjectiveTarget : Prop :=
  ∀ ⦃I : Type u⦄ ⦃J : Type v⦄ [LinearOrder I] [WellFoundedLT I],
    (∀ s : Set I, s.Countable → BddAbove s) → ∀ ⦃r : I → J⦄, HasUnboundedFibres r →
      ∀ A A' : J → Bool, Order.TailEquivalent (CodedOrder (A ∘ r)) (CodedOrder (A' ∘ r)) →
        A = A'

/-- Finite-interval equivalence in a coded order is equality of ranks. -/
theorem finiteInterval_iff_rank_eq {x y : CodedOrder b} :
    Order.FiniteInterval x y ↔ rank x = rank y :=
  finiteIntervalIffRankEqTarget b x y

section TailIso

variable {c : I → Bool} {U : Set (CodedOrder b)} {V : Set (CodedOrder c)}

/-- An isomorphism of upper sets of coded orders preserves and reflects equality of ranks: ranks
are finite-interval classes, intervals of an upper set are intervals of the coded order, and
isomorphisms preserve finite-interval equivalence. -/
theorem rank_eq_iff_of_orderIso (hU : IsUpperSet U) (hV : IsUpperSet V) (e : U ≃o V) (x y : U) :
    rank ((e x : V) : CodedOrder c) = rank ((e y : V) : CodedOrder c) ↔
      rank (x : CodedOrder b) = rank (y : CodedOrder b) := by
  rw [← finiteInterval_iff_rank_eq, ← finiteInterval_iff_rank_eq,
    ← Order.finiteInterval_subtype_iff hV.ordConnected,
    ← Order.finiteInterval_subtype_iff hU.ordConnected, e.finiteInterval_iff]

/-- The ranks of the points of a nonempty upper set form a final segment `Set.Ici a`. -/
theorem exists_image_rank_eq_Ici [WellFoundedLT I] (hU : IsUpperSet U) (hne : U.Nonempty) :
    ∃ a, rank '' U = Set.Ici a := by
  obtain ⟨_, ⟨x, hx, rfl⟩, hmin⟩ := wellFounded_lt.has_min (rank '' U) (hne.image rank)
  refine ⟨rank x, Set.Subset.antisymm ?_ fun i hi ↦ ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact not_lt.mp (hmin _ ⟨y, hy, rfl⟩)
  · rcases (Set.mem_Ici.mp hi).eq_or_lt with h | h
    · exact ⟨x, hx, h⟩
    · exact ⟨mk i 0 fun _ ↦ le_rfl, blockSubsetOfRankLtTarget b hU hx h rfl, rfl⟩

end TailIso

/-- **A tail isomorphism eventually preserves ranks**, the target form.  The rank of `e x`
depends only on the rank of `x` (`rank_eq_iff_of_orderIso`); the induced map of ranks is
strictly monotone on the final segment of ranks of `U` with image the final segment of ranks of
`V`, hence the identity on a final segment (`Order.exists_forall_ge_eq_of_strictMonoOn`). -/
theorem tailIsoRankEventuallyTarget : TailIsoRankEventuallyTarget.{u} := by
  intro I _ _ hbdd b c U V hU hV hne e
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨a, ha⟩ := exists_image_rank_eq_Ici hU ⟨x₀, hx₀⟩
  obtain ⟨a', ha'⟩ := exists_image_rank_eq_Ici hV ⟨_, (e ⟨x₀, hx₀⟩).2⟩
  let f : I → I := fun i ↦
    if h : ∃ x : U, rank (x : CodedOrder b) = i then rank ((e h.choose : V) : CodedOrder c) else i
  have hf (x : U) : f (rank (x : CodedOrder b)) = rank ((e x : V) : CodedOrder c) := by
    have h : ∃ y : U, rank (y : CodedOrder b) = rank (x : CodedOrder b) := ⟨x, rfl⟩
    simp only [f, h, ↓reduceDIte]
    exact (rank_eq_iff_of_orderIso hU hV e _ _).mpr h.choose_spec
  have hrep (i : I) (hi : i ∈ Set.Ici a) : ∃ x : U, rank (x : CodedOrder b) = i := by
    obtain ⟨x, hx, hxi⟩ := ha.symm ▸ hi
    exact ⟨⟨x, hx⟩, hxi⟩
  have hmono : StrictMonoOn f (Set.Ici a) := by
    intro i hi j hj hij
    obtain ⟨x, rfl⟩ := hrep i hi
    obtain ⟨y, rfl⟩ := hrep j hj
    rw [hf, hf]
    have hxy : x < y := lt_of_rank_lt hij
    rcases (rank_mono (show ((e x : V) : CodedOrder c) ≤ e y from
      (e.strictMono hxy).le)).lt_or_eq with h | h
    · exact h
    · exact absurd ((rank_eq_iff_of_orderIso hU hV e x y).mp h) hij.ne
  have himg : f '' Set.Ici a = Set.Ici a' := by
    ext j
    refine ⟨?_, fun hj ↦ ?_⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨x, rfl⟩ := hrep i hi
      rw [hf, ← ha']
      exact ⟨_, (e x).2, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := ha'.symm ▸ hj
      refine ⟨rank ((e.symm ⟨y, hy⟩ : U) : CodedOrder b), ha ▸ ⟨_, (e.symm _).2, rfl⟩, ?_⟩
      rw [hf, e.apply_symm_apply]
  obtain ⟨γ, -, -, hγ⟩ := Order.exists_forall_ge_eq_of_strictMonoOn hbdd hmono himg
  exact ⟨γ, fun x hx ↦ (hf x).symm.trans (hγ _ hx)⟩

/-- Whole blocks of the same rank, on which a tail isomorphism and its inverse preserve ranks,
have least points together (one direction). -/
theorem exists_least_block_of_orderIso {c : I → Bool} {U : Set (CodedOrder b)}
    {V : Set (CodedOrder c)} (e : U ≃o V) {i : I} (hBU : block b i ⊆ U) (hBV : block c i ⊆ V)
    (he : ∀ x : U, rank (x : CodedOrder b) = i → rank ((e x : V) : CodedOrder c) = i)
    (he' : ∀ y : V, rank (y : CodedOrder c) = i → rank ((e.symm y : U) : CodedOrder b) = i) :
    (∃ x ∈ block b i, ∀ y ∈ block b i, x ≤ y) → (∃ x ∈ block c i, ∀ y ∈ block c i, x ≤ y) := by
  rintro ⟨x, hx, hle⟩
  refine ⟨(e ⟨x, hBU hx⟩ : CodedOrder c), he ⟨x, hBU hx⟩ hx, fun y hy ↦ ?_⟩
  have h : (⟨x, hBU hx⟩ : U) ≤ e.symm ⟨y, hBV hy⟩ := hle _ (he' ⟨y, hBV hy⟩ hy)
  have h' := e.monotone h
  rw [e.apply_symm_apply] at h'
  exact h'

/-- **A tail isomorphism determines the bits on a final segment**, the target form.  Above the
rank cutoffs of `e` and of `e.symm` and above the bottom ranks of both tails, blocks of either
side are whole blocks inside the tails (a cut bottom block is never compared), each carried onto
the block of the same rank; the least-point test then compares the bits. -/
theorem tailIsoBitsEventuallyTarget : TailIsoBitsEventuallyTarget.{u} := by
  intro I _ _ hbdd b c U V hU hV hne ⟨e⟩
  have hVne : V.Nonempty := ⟨_, (e ⟨hne.some, hne.some_mem⟩).2⟩
  obtain ⟨γ, hγ⟩ := tailIsoRankEventuallyTarget hbdd b c hU hV hne e
  obtain ⟨γ', hγ'⟩ := tailIsoRankEventuallyTarget hbdd c b hV hU hVne e.symm
  obtain ⟨a, ha⟩ := exists_image_rank_eq_Ici hU hne
  obtain ⟨a', ha'⟩ := exists_image_rank_eq_Ici hV hVne
  obtain ⟨x₀, hx₀, hx₀a⟩ : a ∈ rank '' U := ha ▸ Set.mem_Ici.mpr le_rfl
  obtain ⟨y₀, hy₀, hy₀a⟩ : a' ∈ rank '' V := ha' ▸ Set.mem_Ici.mpr le_rfl
  refine ⟨max (max γ γ') (max a a'), fun i hi ↦ ?_⟩
  simp only [max_lt_iff] at hi
  have hBU : block b i ⊆ U := blockSubsetOfRankLtTarget b hU hx₀ (hx₀a ▸ hi.2.1)
  have hBV : block c i ⊆ V := blockSubsetOfRankLtTarget c hV hy₀ (hy₀a ▸ hi.2.2)
  have he (x : U) (hx : rank (x : CodedOrder b) = i) : rank ((e x : V) : CodedOrder c) = i :=
    (hγ x (hx ▸ hi.1.1.le)).trans hx
  have he' (y : V) (hy : rank (y : CodedOrder c) = i) :
      rank ((e.symm y : U) : CodedOrder b) = i :=
    (hγ' y (hy ▸ hi.1.2.le)).trans hy
  have h₁ : b i = false → c i = false := fun h ↦ (blockHasLeastIffTarget c i).mp
    (exists_least_block_of_orderIso e hBU hBV he he' ((blockHasLeastIffTarget b i).mpr h))
  have h₂ : c i = false → b i = false := fun h ↦ (blockHasLeastIffTarget b i).mp
    (exists_least_block_of_orderIso e.symm hBV hBU he' (by simpa using he)
      ((blockHasLeastIffTarget c i).mpr h))
  revert h₁ h₂
  cases b i <;> cases c i <;> simp

/-- **Tail-equivalent coded orders have eventually equal bits**, the target form. -/
theorem tailEquivalentBitsEventuallyTarget : TailEquivalentBitsEventuallyTarget.{u} := by
  rintro I _ _ hbdd b c ⟨U, V, hU, hV, hne, -, he⟩
  exact tailIsoBitsEventuallyTarget hbdd b c hU hV hne he

/-- **Recovery of the parameter**, the target form: the bits agree above some `γ`, and every
input index is the image of some block index above `γ`. -/
theorem tailEquivalentInjectiveTarget : TailEquivalentInjectiveTarget.{u, v} := by
  intro I J _ _ hbdd r hr A A' h
  obtain ⟨γ, hγ⟩ := tailEquivalentBitsEventuallyTarget hbdd _ _ h
  funext j
  obtain ⟨k, hk, rfl⟩ := hr j γ
  exact hγ k hk

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
