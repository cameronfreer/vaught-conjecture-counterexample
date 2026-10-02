/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.GradedMatching

/-!
# The two applications of graded matching

InfinitaryLogic's `FirstOrder.Language.bfEquiv_of_gradedMatching` (`Scott/GradedMatching`) turns
a family `R α n a b` of relations between `n`-tuples of `M` and of `N`, graded by ordinals, that
is atomic at level `0`, lowers (`β ≤ α ≤ height`), and has the forth and back properties from
level `α + 1 ≤ height` to level `α`, into back-and-forth equivalence: a pair related at a level
`α ≤ height` (the *initial match*) is `BFEquiv α`.  Its relation is defined at every ordinal,
while the relations of the two applications below are defined only up to a level.  Each
application therefore puts the height guard `α ≤ η` and a selection of coordinates inside `R`,
and uses height `η`.  The ordinal induction is the upstream one; there is none here.

**(A) Approximate comparison of full presentations** (`roadmap/README.md`, "Reduction to full
presentations").  `FullPresentation.LevelObservations` are countable level sets `S η n` with
projections `τ` that compose exactly; an `ObservedPresentation` of `M` gives its closed tuples
(enumerations of finite closed sets), a closed extension of every closed tuple containing any
given point, and the observations of closed tuples at the levels up to its own.
`ApproxExtension H H' η` is the approximate extension property (AE) at `η`, and
`AtomicAtZero L H H'` the atomic agreement of equal observations at level `0`.  The relation is
`FullPresentation.ObsMatch`: `ObsMatch hη hη' α m a' b'` holds when `α ≤ η` and there are closed
tuples `a`, `b` of one length `n` with equal observations at `α` and a selection
`s : Fin m → Fin n` of coordinates, repetitions allowed, with `a ∘ s = a'` and `b ∘ s = b'`.
The initial match is the given pair of closed tuples with equal observations at `η`, with the
given selection.  `FullPresentation.bfEquiv_comp_of_obs_eq` is the resulting comparison.

**(B) Condition 3 of the reduction to expansion domains, abstract form** (`roadmap/README.md`,
"Condition 3 from back-and-forth").  An `ExpansionMatchData L M N η` records, at each level `α`,
model expansions of the two fixed base structures `M` and `N` to the stage `λ_α`
(`ExpansionM α`, `ExpansionN α`), charts on `k` points (`Chart α k`, the stage types at `λ_α`),
and the *covers*: `coversM e t c` says that the tuple `c` of `M` enumerates an actual occurrence
of the chart `t` in the expansion `e`.  Its four laws are atomic agreement at level `0`,
lowering, forth, and back, each required only at levels at most the height `η`.  The relation
is `ExpansionMatchData.Match`: `D.Match α n a b` holds when `α ≤ η` and there are expansions of
`M` and `N` at `α`, a common chart `t` on `k` points, a cover of `t` in each expansion, and a
selector `s : Fin n → Fin k`, repetitions and the empty tuple allowed, through which `a` and `b`
factor.  The initial match is the common empty chart, from two separate hypotheses: the
existence of an occurrence of an empty chart in each expansion at the height, and the
compatibility of the two empty charts.  `ExpansionMatchData.bfEquiv_of_expansionMatch` concludes
`BFEquiv η 0 ![] ![]`.

This is on abstract hypotheses: nothing here constructs the model expansions, the charts, or the
covers, and nothing proves the laws.  Their instantiation to the expansion domains of the
construction (stage reduction for lowering, the one-block transfer for forth and back, the
closedness of the empty set for existence, `StageType.eq_of_zero` for compatibility) is the work
of Layer 5 and is not elaborated here.

**The initial match is a separate premise.**  The laws are closure conditions, satisfied by the
empty relation, so they relate no pair by themselves (the examples at the end).

**Language.**  Neither `BFEquiv` nor `bfEquiv_of_gradedMatching` assumes `[L.IsRelational]`, and
neither theorem here does.  For a language with function symbols, `SameAtomicType` compares
equalities and relations between coordinates, not terms, so `BFEquiv` is weaker than the usual
back-and-forth equivalence; the base language of both applications is relational, as the
passage to sentences (`BFEquiv_implies_agreeQR`) requires.  The levels are in `Ordinal.{0}`, the
universe of quantifier ranks of `L_{ω₁ω}` formulas.

## Main declarations

* `FullPresentation.ObsMatch` and `FullPresentation.bfEquiv_comp_of_obs_eq`: approximate
  comparison.
* `ExpansionMatchData`, `ExpansionMatchData.Match`, `ExpansionMatchData.bfEquiv_of_match`, and
  `ExpansionMatchData.bfEquiv_of_expansionMatch`: condition 3 in back-and-forth form.

## Placement

This file belongs to Layer 0 of `roadmap/README.md`, "The upstream graded-matching theorem and its
two applications".
-/

namespace VaughtConjecture.Comparison

open FirstOrder Language

universe u v w w' rM rN rC

/-! ### (A) Approximate comparison of full presentations -/

namespace FullPresentation

/-- **Level observations**: countable sets `S η n` of observed invariants of `n`-tuples at each
level `η`, with projections `τ` from a higher level to a lower one that compose exactly. -/
structure LevelObservations where
  /-- The observed invariants of `n`-tuples at level `η`. -/
  S : Ordinal.{0} → ℕ → Type
  /-- Each level set is countable. -/
  countable : ∀ η n, Countable (S η n)
  /-- The projection from level `ξ` down to a level `η ≤ ξ`. -/
  τ : ∀ {η ξ : Ordinal.{0}}, η ≤ ξ → ∀ {n : ℕ}, S ξ n → S η n
  /-- The projection to the same level is the identity. -/
  τ_refl : ∀ {η : Ordinal.{0}} {n : ℕ} (s : S η n), τ le_rfl s = s
  /-- Projections compose. -/
  τ_comp : ∀ {η ξ ζ : Ordinal.{0}} (h₁ : η ≤ ξ) (h₂ : ξ ≤ ζ) {n : ℕ} (s : S ζ n),
    τ h₁ (τ h₂ s) = τ (h₁.trans h₂) s

/-- An **observed presentation** of `M` at level `level`: its closed tuples, with a closed
extension of every closed tuple containing any given point, and the level observations of closed
tuples, coherent under the projections up to `level`.  Observations are defined only on closed
tuples and only at the levels `η ≤ level`; no observation type is required to be inhabited
outside that domain.  Fullness is not part of this structure. -/
structure ObservedPresentation (O : LevelObservations) (M : Type w) where
  /-- The level of the presentation. -/
  level : Ordinal.{0}
  /-- The closed tuples: enumerations of finite closed sets. -/
  IsClosed : ∀ {n : ℕ}, (Fin n → M) → Prop
  /-- Every point lies in a closed extension of every closed tuple. -/
  exists_closed_extension : ∀ {n : ℕ} (a : Fin n → M), IsClosed a → ∀ x : M,
    ∃ (k : ℕ) (c : Fin k → M) (j : Fin (n + k)),
      IsClosed (Fin.append a c) ∧ Fin.append a c j = x
  /-- The observation of a closed tuple at a level `η ≤ level`. -/
  obs : ∀ (η : Ordinal.{0}), η ≤ level → ∀ {n : ℕ} (a : Fin n → M), IsClosed a → O.S η n
  /-- The observations of a closed tuple are coherent under the projections. -/
  obs_τ : ∀ {η ξ : Ordinal.{0}} (h : η ≤ ξ) (hξ : ξ ≤ level) {n : ℕ} (a : Fin n → M)
    (ha : IsClosed a), O.τ h (obs ξ hξ a ha) = obs η (h.trans hξ) a ha

variable {L : Language.{u, v}}
variable {O : LevelObservations} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

variable (L) in
/-- **Atomic recovery at level `0`**, across the two structures: closed tuples with equal
observations at level `0` have the same atomic type in the base language. -/
def AtomicAtZero (H : ObservedPresentation O M) (H' : ObservedPresentation O N) : Prop :=
  ∀ {n : ℕ} (a : Fin n → M) (b : Fin n → N) (ha : H.IsClosed a) (hb : H'.IsClosed b),
    H.obs 0 zero_le a ha = H'.obs 0 zero_le b hb →
      SameAtomicType (L := L) a b

/-- **The approximate extension property (AE) at level `η`**, from `H` to `H'`: for closed tuples
`a` and `b` with equal observations at `η + 1`, every closed extension `a ++ c` in `H` is matched
by a closed extension `b ++ d` in `H'` of the same length, with equal observations at `η`.  The
target tuple `b` is kept literally; only the enlarged tuples are compared, one level down.  It is
asserted when both levels are at least `η + 1`.  (AE) in both directions is this property for
`(H, H')` and for `(H', H)`. -/
def ApproxExtension (H : ObservedPresentation O M) (H' : ObservedPresentation O N)
    (η : Ordinal.{0}) : Prop :=
  ∀ (hH : Order.succ η ≤ H.level) (hH' : Order.succ η ≤ H'.level) {n : ℕ} (a : Fin n → M)
    (b : Fin n → N) (ha : H.IsClosed a) (hb : H'.IsClosed b),
    H.obs (Order.succ η) hH a ha = H'.obs (Order.succ η) hH' b hb →
    ∀ {k : ℕ} (c : Fin k → M) (hc : H.IsClosed (Fin.append a c)),
      ∃ (d : Fin k → N) (hd : H'.IsClosed (Fin.append b d)),
        H.obs η ((Order.le_succ η).trans hH) (Fin.append a c) hc =
          H'.obs η ((Order.le_succ η).trans hH') (Fin.append b d) hd

/-- **The match of approximate comparison** at height `η`: `ObsMatch hη hη' α m a' b'` holds when
`α ≤ η` and `a'` and `b'` are corresponding selections `a ∘ s` and `b ∘ s`, repetitions allowed,
of closed tuples `a` of `H` and `b` of `H'` with equal observations at `α`.  The height guard and
the selection are part of the relation because observations are defined only up to the levels of
the presentations. -/
def ObsMatch (H : ObservedPresentation O M) (H' : ObservedPresentation O N) {η : Ordinal.{0}}
    (hη : η ≤ H.level) (hη' : η ≤ H'.level) (α : Ordinal.{0}) (m : ℕ) (a' : Fin m → M)
    (b' : Fin m → N) : Prop :=
  ∃ hα : α ≤ η, ∃ (n : ℕ) (a : Fin n → M) (b : Fin n → N) (ha : H.IsClosed a)
    (hb : H'.IsClosed b), H.obs α (hα.trans hη) a ha = H'.obs α (hα.trans hη') b hb ∧
      ∃ s : Fin m → Fin n, a ∘ s = a' ∧ b ∘ s = b'

/-- Equal observations at a level `ξ` give equal observations at every level `ζ ≤ ξ`, by the
coherence of the observations under the projections. -/
theorem obs_eq_of_le (H : ObservedPresentation O M) (H' : ObservedPresentation O N)
    {ζ ξ : Ordinal.{0}} (h : ζ ≤ ξ) (hξ : ξ ≤ H.level) (hξ' : ξ ≤ H'.level) {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} {ha : H.IsClosed a} {hb : H'.IsClosed b}
    (hobs : H.obs ξ hξ a ha = H'.obs ξ hξ' b hb) :
    H.obs ζ (h.trans hξ) a ha = H'.obs ζ (h.trans hξ') b hb :=
  (H.obs_τ h hξ a ha).symm.trans ((congrArg (O.τ h) hobs).trans (H'.obs_τ h hξ' b hb))

/-- The forth law of `ObsMatch`, from (AE) at `α` from `H` to `H'`: include the requested point
with the closed tuple in one closed extension, match it by (AE), and select the coordinates. -/
theorem ObsMatch.forth {H : ObservedPresentation O M} {H' : ObservedPresentation O N}
    {η : Ordinal.{0}} {hη : η ≤ H.level} {hη' : η ≤ H'.level} {α : Ordinal.{0}}
    (hae : ApproxExtension H H' α) (hα : α + 1 ≤ η) {m : ℕ} {a' : Fin m → M} {b' : Fin m → N}
    (hR : ObsMatch H H' hη hη' (α + 1) m a' b') (x : M) :
    ∃ y : N, ObsMatch H H' hη hη' α (m + 1) (Fin.snoc a' x) (Fin.snoc b' y) := by
  obtain ⟨_, n, a, b, ha, hb, hobs, s, rfl, rfl⟩ := hR
  obtain ⟨k, c, j, hc, rfl⟩ := H.exists_closed_extension a ha x
  obtain ⟨d, hd, hcd⟩ := hae (hα.trans hη) (hα.trans hη') a b ha hb hobs c hc
  refine ⟨Fin.append b d j, (Order.le_succ α).trans hα, n + k, _, _, hc, hd, hcd,
    Fin.snoc (Fin.castAdd k ∘ s) j, ?_, ?_⟩ <;>
  · rw [Fin.comp_snoc, ← Function.comp_assoc]
    congr 2
    exact funext (Fin.append_left _ _)

/-- The back law of `ObsMatch`, from (AE) at `α` from `H'` to `H`. -/
theorem ObsMatch.back {H : ObservedPresentation O M} {H' : ObservedPresentation O N}
    {η : Ordinal.{0}} {hη : η ≤ H.level} {hη' : η ≤ H'.level} {α : Ordinal.{0}}
    (hae : ApproxExtension H' H α) (hα : α + 1 ≤ η) {m : ℕ} {a' : Fin m → M} {b' : Fin m → N}
    (hR : ObsMatch H H' hη hη' (α + 1) m a' b') (y : N) :
    ∃ x : M, ObsMatch H H' hη hη' α (m + 1) (Fin.snoc a' x) (Fin.snoc b' y) := by
  obtain ⟨_, n, a, b, ha, hb, hobs, s, rfl, rfl⟩ := hR
  obtain ⟨k, d, j, hd, rfl⟩ := H'.exists_closed_extension b hb y
  obtain ⟨c, hc, hcd⟩ := hae (hα.trans hη') (hα.trans hη) b a hb ha hobs.symm d hd
  refine ⟨Fin.append a c j, (Order.le_succ α).trans hα, n + k, _, _, hc, hd, hcd.symm,
    Fin.snoc (Fin.castAdd k ∘ s) j, ?_, ?_⟩ <;>
  · rw [Fin.comp_snoc, ← Function.comp_assoc]
    congr 2
    exact funext (Fin.append_left _ _)

/-- **Approximate comparison.**  If two presentations of levels at least `η` satisfy the atomic
condition at `0` and (AE) in both directions at every level below `η`, then closed tuples with
equal observations at `η` are back-and-forth equivalent at `η` in the base structures, and so is
every corresponding selection `s` of their coordinates, repetitions allowed (`m = 0` compares the
structures).  The proof applies InfinitaryLogic's `bfEquiv_of_gradedMatching` with height `η` to
the relation `ObsMatch`; the initial match is the given pair `a`, `b` with the selection `s`.
The library's `SameAtomicType` covers relations and equalities on variables, not terms: for a
language with function symbols the conclusion is weaker than the usual `≡_η`; the base language
of the application is relational. -/
theorem bfEquiv_comp_of_obs_eq (H : ObservedPresentation O M) (H' : ObservedPresentation O N)
    (hzero : AtomicAtZero L H H') {η : Ordinal.{0}}
    (hae : ∀ ζ, ζ < η → ApproxExtension H H' ζ ∧ ApproxExtension H' H ζ)
    (hη : η ≤ H.level) (hη' : η ≤ H'.level)
    {n : ℕ} (a : Fin n → M) (b : Fin n → N) (ha : H.IsClosed a) (hb : H'.IsClosed b)
    (hobs : H.obs η hη a ha = H'.obs η hη' b hb) {m : ℕ} (s : Fin m → Fin n) :
    BFEquiv (L := L) η m (a ∘ s) (b ∘ s) :=
  bfEquiv_of_gradedMatching (ObsMatch H H' hη hη') (height := η)
    (fun ⟨_, _, _, _, ha, hb, hobs, s, hs, hs'⟩ ↦
      hs ▸ hs' ▸ (hzero _ _ ha hb hobs).relabel s)
    (fun hβα _ ⟨hα, _, _, _, ha, hb, hobs, s, hs, hs'⟩ ↦
      ⟨hβα.trans hα, _, _, _, ha, hb, obs_eq_of_le H H' hβα _ _ hobs, s, hs, hs'⟩)
    (fun hα hR x ↦ (hR.forth (hae _ (Order.add_one_le_iff.mp hα)).1 hα x))
    (fun hα hR y ↦ (hR.back (hae _ (Order.add_one_le_iff.mp hα)).2 hα y))
    le_rfl ⟨le_rfl, n, a, b, ha, hb, hobs, s, rfl, rfl⟩

end FullPresentation

/-! ### (B) Condition 3 of the reduction to expansion domains, abstract form -/

/-- **Expansion-match data at height `η`** between `L`-structures `M` and `N`: at each level `α`,
the model expansions of `M` and of `N` to the stage `λ_α`, the charts on `k` points at `α` (the
stage types at `λ_α`), and the covers of a chart in an expansion (`coversM e t c`: the tuple `c`
of `M` enumerates an actual occurrence of `t` in `e`), with four laws, each only at levels at
most `η`: atomic agreement at level `0`, lowering, forth, and back.  These are abstract
hypotheses: nothing here constructs the expansions or proves the laws. -/
structure ExpansionMatchData (L : Language.{u, v}) (M : Type w) (N : Type w') [L.Structure M]
    [L.Structure N] (η : Ordinal.{0}) where
  /-- The model expansions of `M` to the stage `λ_α`. -/
  ExpansionM : Ordinal.{0} → Type rM
  /-- The model expansions of `N` to the stage `λ_α`. -/
  ExpansionN : Ordinal.{0} → Type rN
  /-- The charts on `k` points at level `α` (stage types at `λ_α` on `k` points). -/
  Chart : Ordinal.{0} → ℕ → Type rC
  /-- `coversM e t c`: the tuple `c` enumerates an actual occurrence of the chart `t` in the
  expansion `e` of `M`. -/
  coversM : ∀ {α : Ordinal.{0}} {k : ℕ}, ExpansionM α → Chart α k → (Fin k → M) → Prop
  /-- `coversN f t d`: the tuple `d` enumerates an actual occurrence of the chart `t` in the
  expansion `f` of `N`. -/
  coversN : ∀ {α : Ordinal.{0}} {k : ℕ}, ExpansionN α → Chart α k → (Fin k → N) → Prop
  /-- **Atomic agreement at level `0`**: two covers of one chart at level `0` have the same
  atomic type in the base language. -/
  atomic : ∀ {k : ℕ} {e : ExpansionM 0} {f : ExpansionN 0} {t : Chart 0 k} {c : Fin k → M}
    {d : Fin k → N}, coversM e t c → coversN f t d → SameAtomicType (L := L) c d
  /-- **Lowering**: for `β ≤ α ≤ η`, two covers of one chart at level `α` are covers, by the same
  tuples, of one chart at level `β` in some expansions at `β` (in the application, the
  reductions of the expansions and of the chart; no uniqueness of expansions is used). -/
  lower : ∀ {α β : Ordinal.{0}}, β ≤ α → α ≤ η → ∀ {k : ℕ} {e : ExpansionM α}
    {f : ExpansionN α} {t : Chart α k} {c : Fin k → M} {d : Fin k → N},
    coversM e t c → coversN f t d →
      ∃ (e' : ExpansionM β) (f' : ExpansionN β) (t' : Chart β k), coversM e' t' c ∧ coversN f' t' d
  /-- **Forth**: for `α + 1 ≤ η`, two covers `c` and `d` of one chart at level `α + 1` and a point
  `x` of `M` give covers `c'` and `d'` of one chart at level `α` that extend `c` and `d` along a
  common map `j`, with `x` among the coordinates of `c'` (in the application, the one-block
  transfer, with a closed extension containing `x`). -/
  forth : ∀ {α : Ordinal.{0}}, α + 1 ≤ η → ∀ {k : ℕ} {e : ExpansionM (α + 1)}
    {f : ExpansionN (α + 1)} {t : Chart (α + 1) k} {c : Fin k → M} {d : Fin k → N},
    coversM e t c → coversN f t d → ∀ x : M,
      ∃ (e' : ExpansionM α) (f' : ExpansionN α) (k' : ℕ) (t' : Chart α k') (c' : Fin k' → M)
        (d' : Fin k' → N) (j : Fin k → Fin k') (i : Fin k'),
        coversM e' t' c' ∧ coversN f' t' d' ∧ c' ∘ j = c ∧ d' ∘ j = d ∧ c' i = x
  /-- **Back**: the forth law with the roles of `M` and `N` exchanged, for a point `y` of `N`. -/
  back : ∀ {α : Ordinal.{0}}, α + 1 ≤ η → ∀ {k : ℕ} {e : ExpansionM (α + 1)}
    {f : ExpansionN (α + 1)} {t : Chart (α + 1) k} {c : Fin k → M} {d : Fin k → N},
    coversM e t c → coversN f t d → ∀ y : N,
      ∃ (e' : ExpansionM α) (f' : ExpansionN α) (k' : ℕ) (t' : Chart α k') (c' : Fin k' → M)
        (d' : Fin k' → N) (j : Fin k → Fin k') (i : Fin k'),
        coversM e' t' c' ∧ coversN f' t' d' ∧ c' ∘ j = c ∧ d' ∘ j = d ∧ d' i = y

namespace ExpansionMatchData

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
  {η : Ordinal.{0}}

/-- **The match of condition 3** at height `η`: `D.Match α n a b` holds when `α ≤ η` and there
are expansions of `M` and `N` at `α`, a common chart `t` on `k` points with a cover `c` in the
first and `d` in the second, and a selector `s : Fin n → Fin k`, repetitions and the empty tuple
allowed, with `c ∘ s = a` and `d ∘ s = b`. -/
def Match (D : ExpansionMatchData.{u, v, w, w', rM, rN, rC} L M N η) (α : Ordinal.{0}) (n : ℕ)
    (a : Fin n → M) (b : Fin n → N) : Prop :=
  ∃ _ : α ≤ η, ∃ (e : D.ExpansionM α) (f : D.ExpansionN α) (k : ℕ) (t : D.Chart α k)
    (c : Fin k → M) (d : Fin k → N),
    D.coversM e t c ∧ D.coversN f t d ∧ ∃ s : Fin n → Fin k, c ∘ s = a ∧ d ∘ s = b

variable (D : ExpansionMatchData.{u, v, w, w', rM, rN, rC} L M N η)

/-- Every pair related by `D.Match` at a level `α ≤ η` is back-and-forth equivalent at `α`: the
relation `D.Match` satisfies the laws of InfinitaryLogic's `bfEquiv_of_gradedMatching` with
height `η`. -/
theorem bfEquiv_of_match {α : Ordinal.{0}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hR : D.Match α n a b) : BFEquiv (L := L) α n a b :=
  bfEquiv_of_gradedMatching D.Match (height := η)
    (fun ⟨_, _, _, _, _, _, _, hc, hd, s, hs, hs'⟩ ↦ hs ▸ hs' ▸ (D.atomic hc hd).relabel s)
    (fun hβα hαη ⟨_, _, _, _, _, _, _, hc, hd, hsel⟩ ↦
      have ⟨e', f', t', hc', hd'⟩ := D.lower hβα hαη hc hd
      ⟨hβα.trans hαη, e', f', _, t', _, _, hc', hd', hsel⟩)
    (fun hα ⟨_, _, _, _, _, _, _, hc, hd, s, hs, hs'⟩ x ↦
      have ⟨e', f', _, t', c', d', j, i, hc', hd', hj, hj', hi⟩ := D.forth hα hc hd x
      ⟨d' i, (le_self_add).trans hα, e', f', _, t', c', d', hc', hd', Fin.snoc (j ∘ s) i,
        by rw [Fin.comp_snoc, ← Function.comp_assoc, hj, hs, hi],
        by rw [Fin.comp_snoc, ← Function.comp_assoc, hj', hs']⟩)
    (fun hα ⟨_, _, _, _, _, _, _, hc, hd, s, hs, hs'⟩ y ↦
      have ⟨e', f', _, t', c', d', j, i, hc', hd', hj, hj', hi⟩ := D.back hα hc hd y
      ⟨c' i, (le_self_add).trans hα, e', f', _, t', c', d', hc', hd', Fin.snoc (j ∘ s) i,
        by rw [Fin.comp_snoc, ← Function.comp_assoc, hj, hs],
        by rw [Fin.comp_snoc, ← Function.comp_assoc, hj', hs', hi]⟩)
    hR.1 hR

/-- **Condition 3 in back-and-forth form, on abstract hypotheses.**  Given expansion-match data
at height `η`, the empty tuples of `M` and `N` are back-and-forth equivalent at `η`.  The initial
match, `D.Match η 0 ![] ![]` through the common empty chart, comes from two separate hypotheses:
`exists_empty_chart`, that each of some expansions of `M` and of `N` at `η` has an occurrence of a
chart on zero points (in the application, the empty set is closed in both expansions), and
`compat`, that the two empty charts so obtained are equal (in the application,
`StageType.eq_of_zero`).  The proof applies InfinitaryLogic's `bfEquiv_of_gradedMatching` with
height `η` to `D.Match`.  Nothing here constructs the expansions: their instantiation to the
expansion domains of the construction is the work of Layer 5 and is not elaborated. -/
theorem bfEquiv_of_expansionMatch
    (exists_empty_chart : (∃ (e : D.ExpansionM η) (t : D.Chart η 0), D.coversM e t ![]) ∧
      ∃ (f : D.ExpansionN η) (t : D.Chart η 0), D.coversN f t ![])
    (compat : ∀ {e : D.ExpansionM η} {f : D.ExpansionN η} {t t' : D.Chart η 0},
      D.coversM e t ![] → D.coversN f t' ![] → t = t') :
    BFEquiv (L := L) (M := M) (N := N) η 0 ![] ![] :=
  have ⟨⟨e, t, hc⟩, ⟨f, _, hd⟩⟩ := exists_empty_chart
  D.bfEquiv_of_match ⟨le_rfl, e, f, 0, t, ![], ![], hc, compat hc hd ▸ hd, id, rfl, rfl⟩

end ExpansionMatchData

/-! ### Regressions -/

section Examples

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- The identity match: through `bfEquiv_of_gradedMatching`, the relation `a = b` on one
structure recovers InfinitaryLogic's `BFEquiv.refl` at every level up to the height. -/
example {height α : Ordinal.{0}} (hα : α ≤ height) {n : ℕ} (a : Fin n → M) :
    BFEquiv (L := L) α n a a :=
  bfEquiv_of_gradedMatching (fun _ _ a b ↦ a = b) (height := height)
    (fun h ↦ h ▸ SameAtomicType.refl _) (fun _ _ ↦ id)
    (fun _ h x ↦ ⟨x, h ▸ rfl⟩) (fun _ h y ↦ ⟨y, h ▸ rfl⟩) hα rfl

/-- The identity match in the form of condition 3: on one structure, with the tuples themselves
as charts, a single expansion at each level, and `t = c` as the cover, the four laws hold, and
`bfEquiv_of_expansionMatch` gives `BFEquiv η 0 ![] ![]`. -/
example (η : Ordinal.{0}) : BFEquiv (L := L) (M := M) (N := M) η 0 ![] ![] :=
  ExpansionMatchData.bfEquiv_of_expansionMatch (L := L)
    { ExpansionM := fun _ ↦ PUnit.{1}
      ExpansionN := fun _ ↦ PUnit.{1}
      Chart := fun _ k ↦ Fin k → M
      coversM := fun _ t c ↦ t = c
      coversN := fun _ t d ↦ t = d
      atomic := by rintro _ _ _ _ _ _ rfl rfl; exact SameAtomicType.refl _
      lower := by rintro _ _ _ _ _ _ _ _ _ _ rfl rfl; exact ⟨⟨⟩, ⟨⟩, _, rfl, rfl⟩
      forth := by
        rintro _ _ k _ _ t _ _ rfl rfl x
        exact ⟨⟨⟩, ⟨⟩, k + 1, Fin.snoc t x, _, _, Fin.castSucc, Fin.last k, rfl, rfl,
          funext fun _ ↦ by simp, funext fun _ ↦ by simp, by simp⟩
      back := by
        rintro _ _ k _ _ t _ _ rfl rfl y
        exact ⟨⟨⟩, ⟨⟩, k + 1, Fin.snoc t y, _, _, Fin.castSucc, Fin.last k, rfl, rfl,
          funext fun _ ↦ by simp, funext fun _ ↦ by simp, by simp⟩ }
    ⟨⟨⟨⟩, _, rfl⟩, ⟨⟩, _, rfl⟩ (fun hc hd ↦ hc.trans hd.symm)

/-- The empty relation satisfies all four laws of `bfEquiv_of_gradedMatching`, so the laws give
no related pair: without an initial match nothing follows. -/
example (height : Ordinal.{0}) :
    let R : Ordinal.{0} → (n : ℕ) → (Fin n → M) → (Fin n → N) → Prop := fun _ _ _ _ ↦ False
    (∀ {n a b}, R 0 n a b → SameAtomicType (L := L) a b) ∧
      (∀ {α β n a b}, β ≤ α → α ≤ height → R α n a b → R β n a b) ∧
      (∀ {α n a b}, α + 1 ≤ height → R (α + 1) n a b →
        ∀ x : M, ∃ y : N, R α (n + 1) (Fin.snoc a x) (Fin.snoc b y)) ∧
      (∀ {α n a b}, α + 1 ≤ height → R (α + 1) n a b →
        ∀ y : N, ∃ x : M, R α (n + 1) (Fin.snoc a x) (Fin.snoc b y)) ∧
      ∀ {α n a b}, ¬ R α n a b :=
  ⟨False.elim, fun _ _ ↦ id, fun _ ↦ False.elim, fun _ ↦ False.elim, id⟩

/-- In the form of condition 3: with no expansions at any level, the four laws hold vacuously,
the data relate no pair, and the existence half of the initial match fails, so
`bfEquiv_of_expansionMatch` does not apply. -/
example (η : Ordinal.{0}) :
    ∃ D : ExpansionMatchData.{u, v, w, w', 0, 0, 0} L M N η,
      (∀ α n a b, ¬ D.Match α n a b) ∧
        ¬ ∃ (e : D.ExpansionM η) (t : D.Chart η 0), D.coversM e t ![] :=
  ⟨{ ExpansionM := fun _ ↦ Empty
     ExpansionN := fun _ ↦ Empty
     Chart := fun _ _ ↦ Unit
     coversM := fun _ _ _ ↦ True
     coversN := fun _ _ _ ↦ True
     atomic := fun {_ e} ↦ e.elim
     lower := by intro _ _ _ _ _ e; exact e.elim
     forth := by intro _ _ _ e; exact e.elim
     back := by intro _ _ _ e; exact e.elim },
    fun _ _ _ _ ⟨_, e, _⟩ ↦ e.elim, fun ⟨e, _⟩ ↦ e.elim⟩

/-- Height `0`: the forth and back laws are vacuous (`α + 1 ≤ 0` never holds), and approximate
comparison at `η = 0` needs no (AE): equal observations at `0` give `BFEquiv 0`. -/
example {O : FullPresentation.LevelObservations} (H : FullPresentation.ObservedPresentation O M)
    (H' : FullPresentation.ObservedPresentation O N) (hzero : FullPresentation.AtomicAtZero L H H')
    {n : ℕ} (a : Fin n → M) (b : Fin n → N) (ha : H.IsClosed a) (hb : H'.IsClosed b)
    (hobs : H.obs 0 zero_le a ha = H'.obs 0 zero_le b hb) :
    BFEquiv (L := L) (0 : Ordinal.{0}) n a b :=
  FullPresentation.bfEquiv_comp_of_obs_eq H H' hzero (fun _ h ↦ absurd h (by simp))
    zero_le zero_le a b ha hb hobs id

/-- Height `0` in the form of condition 3: no forth or back step is ever requested. -/
example (α : Ordinal.{0}) : ¬ α + 1 ≤ 0 := by simp

/-- A selector with repeated coordinates: the two-fold repetition of the first coordinate of a
pair of closed tuples with equal observations. -/
example {O : FullPresentation.LevelObservations} (H : FullPresentation.ObservedPresentation O M)
    (H' : FullPresentation.ObservedPresentation O N) (hzero : FullPresentation.AtomicAtZero L H H')
    {η : Ordinal.{0}}
    (hae : ∀ ζ, ζ < η → FullPresentation.ApproxExtension H H' ζ ∧
      FullPresentation.ApproxExtension H' H ζ)
    (hη : η ≤ H.level) (hη' : η ≤ H'.level) (a : Fin 1 → M) (b : Fin 1 → N)
    (ha : H.IsClosed a) (hb : H'.IsClosed b) (hobs : H.obs η hη a ha = H'.obs η hη' b hb) :
    BFEquiv (L := L) η 2 (fun _ ↦ a 0) (fun _ ↦ b 0) :=
  FullPresentation.bfEquiv_comp_of_obs_eq H H' hzero hae hη hη' a b ha hb hobs (fun _ ↦ 0)

end Examples

end VaughtConjecture.Comparison
