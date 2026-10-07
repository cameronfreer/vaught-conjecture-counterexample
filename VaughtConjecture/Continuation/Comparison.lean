/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ExactAge
import VaughtConjecture.Continuation.Terminal

/-!
# Comparison of expansions sharing a property

Roadmap, Layer 4 (the rigid-core, residual, and hollow comparisons, as instances of the exact-age
comparison of `VaughtConjecture.Continuation.ExactAge`); semantic contract, item 8.

Terminality is not a hypothesis here: each comparison holds for any two expansions sharing its
property.  Terminality enters only in showing that every terminal model has one of these
properties (the countable cover of the terminal classes, Layer 4).

**Rigid cores from finite-extension receiving.**  Let `R` be exactly consistent at a limit stage
with finite-extension receiving (`Realization.HasFiniteExtensionReceiving`).  Over a cover `c` of a
stage type `t`, let `D` be a legal donor restricting to `t` along `g`, in which the root is a rigid
core (`StageType.IsRigidCoreIn D g`).  Then some cover of `D` itself extends `c`
(`Realization.exists_covers_of_isRigidCoreIn`):

* since the stage is a limit, some ordinal `δ` below the stage lies above every label of `D` other
  than `⊤` (`StageType.exists_lt_forall_label_lt`), and `δ` is a permitted cutoff;
* receiving `D` at `δ` gives a cover `u` with `u ∘ g = c` whose type `q` agrees with `D` below `δ`:
  so `q` agrees with `D` at every cell not labelled `⊤` in `D`, and at the top cells of `D` it is
  `⊤` or an ordinal at least `δ`; hence `q` witnesses that its own top cells form an admissible
  top support of `D` (`StageType.IsAdmissibleTopSupport`);
* by exact consistency the face of `q` along `g` is the type `t` of the root, which is also the
  face of `D`: so `q` agrees with `D` at every cell visible through `g`, and the top cells of `D`
  supported on the root are top cells of `q`;
* rigidity of the root in `D` makes every top cell of `D` a top cell of `q`, so `q = D`
  (`StageType.eq_of_mem_receivingFamily_of_isRigidCoreIn`).

Only exact consistency, the limit stage, legality of the donor, and rigidity in the donor are
used: neither covering, nor any family clause of a model, nor any property of the root beyond
being a cover.  Without rigidity, receiving at a cutoff is not exact
(`VaughtConjecture.Continuation.ComparisonExamples`: a capped donor).

**The rigid-core comparison.**  For a stage type `p` on `k₀` points, the **pointed age of a rigid
core of type `p`** (`StageType.rigidCoreAge`) consists, at positions `ι : Fin k₀ ↪ Fin m`, of the
legal stage types with face `p` along `ι` in which the core along `ι` is rigid.  Exact receiving
within it at any core follows from the above, since a donor in which the core is rigid has the
root, which contains the core, rigid too (`StageType.IsRigidCoreIn.mono`).  In a model in which a
cover `x₀` of `p` is a globally rigid core (`Realization.IsGloballyRigidCore`), every actual type of
a cover containing `x₀` lies in this age.  So the exact-age comparison applies to two expansions
with finite-extension receiving and globally rigid cores of one type `p`
(`Realization.exists_equiv_comp_eq_of_isGloballyRigidCore`): their base structures are isomorphic,
by an isomorphism carrying one core to the other.  Finite-extension receiving of models is (R1) of
the table of Layer 3 (equivalently finite-cut receiving,
`Realization.hasFiniteExtensionReceiving_iff`), still to be proved for models in general; here it
is a hypothesis of each comparison.  No other receiving statement for donors with top cells is
used: rigidity is what makes cutoff receiving exact.

**The top-free comparison** is the instance on no points.  There is a single stage type on no
points (`StageType.eq_of_zero`), every model covers it by the empty tuple
(`Realization.IsModel.exists_covers_zero`), and at a limit stage the empty core is rigid in a legal
type exactly when the type is top-free (`StageType.isRigidCoreIn_empty_iff_isTopFree`), so the
pointed age on no points is the set of legal top-free types (`StageType.rigidCoreAge_zero`), and
the empty tuple is a globally rigid core of a model exactly when its top-grade supremum is `0`.  So
two expansions with finite-extension receiving and top-grade supremum `0` have isomorphic base
structures (`Realization.nonempty_equiv_of_topGradeSup_eq_zero`).

**The residual and hollow comparisons, under named hypotheses.**  (R2) and (R3) of the table of
Layer 3 are stated here as hypotheses, at the strength of the table and at limit stages:

* `Realization.ResidualReceiving` ((R2)): in a model with no cover that is a globally rigid core
  and with top-grade supremum `K`, over every cover, the empty one included, every one-point coface
  of top grade at most `K` is the type of the cover extended by one point;
* `Realization.HollowReceiving H` ((R3)): in a model satisfying `H` with unbounded top-grade
  growth, over every cover, the empty one included, every one-point coface is the type of the cover
  extended by one point.

Hollowness is not defined in this library yet: the predicate `H` is a parameter, to be fixed as
the hollowness predicate of the continuation criterion (output 3 of higher-stage reconstruction),
so that one predicate is used in both.  Both statements are still to be proved; by the table,
both use, among other inputs, the coatom extension construction ((R6)), that is, the coatom
extension property `StageType.HasCoatomExtensions`, which is not proved.  The families
`{D | D legal, topGrade D ≤ K}` and `{D | D legal}` are closed under the face maps
(`StageType.IsLegal.restrictFace`, `StageType.topGrade_le_of_restrictFace`), so the one-point
form gives exact receiving within them (`Realization.ExactReceivingWithin.of_one_point`); every
actual type of a model lies in them (top grade at most the top-grade supremum,
`Occurrence.topGrade_le_topGradeSup`), and the initial match is the pair of empty covers.  Hence
the residual comparison (`Realization.nonempty_equiv_of_residual`: two expansions with no cover
that is a globally rigid core and with the same top-grade supremum `K`, under
`ResidualReceiving`) and the hollow comparison (`Realization.nonempty_equiv_of_hollow`: two
expansions satisfying `H` with unbounded growth, under `HollowReceiving H`).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset FirstOrder Language Label

variable {α : Ordinal.{u}} {n m k₀ : ℕ}

/-! ### Exact receiving at a rigid root -/

namespace StageType

/-- **Receiving at a rigid root is exact.**  Let `q` agree with a legal `D` below a cutoff `δ`
above every label of `D` other than `⊤`, and let `q` and `D` have a common face along `g`.  If the
root along `g` is a rigid core in `D`, then `q = D`: the top cells of `q` form an admissible top
support of `D` containing the top cells supported on the root. -/
theorem eq_of_mem_receivingFamily_of_isRigidCoreIn {D q : StageType.{u} α m} (hD : D.IsLegal)
    {δ : Ordinal.{u}} (hδ : ∀ j, D.label j ≠ ⊤ → D.label j < (δ : Label.{u}))
    (hq : q ∈ receivingFamily D δ)
    {g : Fin n ↪ Fin m} {t : StageType.{u} α n} (hqg : restrictFace g q = some t)
    (hDg : restrictFace g D = some t) (hrig : D.IsRigidCoreIn g) : q = D := by
  obtain ⟨hs, hl⟩ := hq
  obtain ⟨S, ℓ, hw, hc, hlaw, hat⟩ := q
  obtain ⟨S', ℓ', hw', hc', hlaw', hat'⟩ := D
  obtain rfl : S = S' := hs
  have hl (j : Fin S.card) : min (ℓ j) δ = min (ℓ' j) δ := hl j j rfl
  -- the labels other than `⊤` are kept
  have hnt (j : Fin S.card) (hj : ℓ' j ≠ ⊤) : ℓ j = ℓ' j := by
    have h := hl j
    rw [min_eq_left (hδ j hj).le] at h
    rcases le_total (ℓ j) δ with h' | h'
    · rwa [min_eq_left h'] at h
    · rw [min_eq_right h'] at h
      exact absurd (h ▸ hδ j hj) (lt_irrefl _)
  -- the cells visible through `g` are kept
  have hvis (j : Fin S.card) (hj : j ∈ S.visibleCells g) : ℓ j = ℓ' j := by
    obtain ⟨hfq, hq⟩ := (restrictFace_eq_some_iff _ g).mp hqg
    obtain ⟨hfD, hD⟩ := (restrictFace_eq_some_iff _ g).mp hDg
    obtain ⟨k, rfl⟩ : j ∈ Set.range (S.cellMap g) := by
      rw [Scheme.range_cellMap]
      exact hj
    exact label_congr (hq.trans hD.symm) (i := k) (j := k) rfl
  -- the top cells of `q` form an admissible top support of `D`
  have hadm : IsAdmissibleTopSupport ⟨S, ℓ', hw', hc', hlaw', hat'⟩ {j | ℓ j = ⊤} := by
    -- legality concerns only the scheme, so `hD` is also the legality of `q`
    refine ⟨⟨S, ℓ, hw, hc, hlaw, hat⟩, hD, rfl, fun i j hij ↦ ?_⟩
    obtain rfl : i = j := Fin.ext hij
    refine ⟨hnt i, Iff.rfl, fun htop hi ↦ ?_⟩
    -- unfold the labels of the structure literals
    change ℓ i ≠ ⊤ at hi
    change (ℓ i).IsProper
    have h := hl i
    simp only at htop
    rw [htop, min_eq_right le_top] at h
    have hge : (δ : Label.{u}) ≤ ℓ i := by
      by_contra hlt
      rw [min_eq_left (le_of_not_ge hlt)] at h
      exact hlt h.ge
    revert hge hi
    induction ℓ i using Label.recBotCoeTop with
    | bot => exact fun _ hge ↦ absurd hge (by simp)
    | coe o => exact fun _ _ ↦ isProper_coe o
    | top => exact fun h _ ↦ absurd rfl h
  have htop := hrig _ hadm fun j hj htop ↦ (hvis j hj).trans htop
  refine ext rfl fun i j hij ↦ ?_
  obtain rfl : i = j := Fin.ext hij
  by_cases hi : ℓ' i = ⊤
  · exact (htop i hi).trans hi.symm
  · exact hnt i hi

/-- The **pointed age of a rigid core of type `p`**: at positions `ι`, the legal stage types whose
face along `ι` is `p` and in which the core along `ι` is rigid. -/
def rigidCoreAge (p : StageType.{u} α k₀) (m : ℕ) (ι : Fin k₀ ↪ Fin m) :
    Set (StageType.{u} α m) :=
  {D | D.IsLegal ∧ restrictFace ι D = some p ∧ D.IsRigidCoreIn ι}

/-- **Membership in the pointed age of a rigid core**: a legal stage type with face `p` along `ι`,
in which the core along `ι` is rigid. -/
@[simp] theorem mem_rigidCoreAge {p : StageType.{u} α k₀} {ι : Fin k₀ ↪ Fin m}
    {D : StageType.{u} α m} :
    D ∈ rigidCoreAge p m ι ↔ D.IsLegal ∧ restrictFace ι D = some p ∧ D.IsRigidCoreIn ι :=
  Iff.rfl

/-- **The pointed age on no points** is the set of legal top-free stage types, at a limit stage:
the stage type on no points is unique, and the empty core is rigid exactly in the top-free
types. -/
theorem rigidCoreAge_zero (hα : Order.IsSuccLimit α) (p : StageType.{u} α 0)
    (ι : Fin 0 ↪ Fin m) : rigidCoreAge p m ι = {D | D.IsLegal ∧ D.IsTopFree} := by
  ext D
  refine ⟨fun ⟨hD, _, hr⟩ ↦ ⟨hD, (isRigidCoreIn_empty_iff_isTopFree hα hD ι).mp hr⟩,
    fun ⟨hD, ht⟩ ↦ ⟨hD, ?_, isRigidCoreIn_of_isTopFree ht ι⟩⟩
  obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (D.isSome_restrictFace_of_zero ι)
  rw [hp', eq_of_zero p' p]

/-- Legality and a bound on the top grade pass to faces. -/
theorem isLegal_and_topGrade_le_of_restrictFace {K : ℕ} {D : StageType.{u} α m}
    (hD : D.IsLegal ∧ D.topGrade ≤ K) {f : Fin n ↪ Fin m} {p : StageType.{u} α n}
    (hf : StageType.restrictFace f D = some p) : p.IsLegal ∧ p.topGrade ≤ K :=
  ⟨hD.1.restrictFace f hf, (StageType.topGrade_le_of_restrictFace hf).trans hD.2⟩

end StageType

namespace Realization

section Receiving

variable {M : Type w} {R : Realization.{u, w} α M}

/-- **Exact receiving at a rigid root, from finite-extension receiving.**  In an exactly
consistent realization at a limit stage with finite-extension receiving, a legal donor over a
cover `c`, in which the root is a rigid core, is the type of a cover extending `c`.  The donor is
received at a cutoff above all its labels other than `⊤`. -/
theorem exists_covers_of_isRigidCoreIn (hR : R.IsConsistent) (hα : Order.IsSuccLimit α)
    (hrec : R.HasFiniteExtensionReceiving) {t : StageType.{u} α n} {c : Fin n → M}
    (hc : R.Covers t c) {D : StageType.{u} α m} {g : Fin n ↪ Fin m} (hD : D.IsLegal)
    (hg : StageType.restrictFace g D = some t) (hrig : D.IsRigidCoreIn g) :
    ∃ u : Fin m → M, R.Covers D u ∧ u ∘ g = c := by
  obtain ⟨δ, hδα, hδ⟩ := D.exists_lt_forall_label_lt hα
  obtain ⟨u, hu, q, hq, huq⟩ :=
    hrec ⟨c, hc.injective⟩ t hc.eval_eq D g hD hg δ (isPermittedCutoff_coe.mpr hδα)
  have hqg : StageType.restrictFace g q = some t := by
    rw [← hR u q g huq, hu]
    exact hc.eval_eq
  obtain rfl := StageType.eq_of_mem_receivingFamily_of_isRigidCoreIn hD hδ hq hqg hg hrig
  exact ⟨u, covers_of_eval u huq, funext fun i ↦ DFunLike.congr_fun hu i⟩

/-- **Exact receiving within the pointed age of a rigid core**, at any core, for an exactly
consistent realization at a limit stage with finite-extension receiving. -/
theorem exactReceivingWithinAt_rigidCoreAge (hR : R.IsConsistent) (hα : Order.IsSuccLimit α)
    (hrec : R.HasFiniteExtensionReceiving) (x₀ : Fin k₀ → M) (p : StageType.{u} α k₀) :
    R.ExactReceivingWithinAt x₀ (StageType.rigidCoreAge p) :=
  fun _ _ _ _ ι hc _ _ g hD hg ↦
    exists_covers_of_isRigidCoreIn hR hα hrec hc (StageType.mem_rigidCoreAge.mp hD).1 hg
      ((StageType.mem_rigidCoreAge.mp hD).2.2.mono (by rintro _ ⟨i, rfl⟩; exact ⟨ι i, rfl⟩))

/-- **The top-free case**: exact receiving of the legal top-free stage types, for an exactly
consistent realization at a limit stage with finite-extension receiving; every core is rigid in a
top-free type. -/
theorem exactReceivingWithin_isTopFree (hR : R.IsConsistent) (hα : Order.IsSuccLimit α)
    (hrec : R.HasFiniteExtensionReceiving) :
    R.ExactReceivingWithin fun _ ↦ {D | D.IsLegal ∧ D.IsTopFree} :=
  fun _ _ _ _ hc _ g hD hg ↦ exists_covers_of_isRigidCoreIn hR hα hrec hc hD.1 hg
    (StageType.isRigidCoreIn_of_isTopFree hD.2 g)

/-- **Age inclusion at a globally rigid core**: in a model in which a cover `x₀` of `p` is a
globally rigid core, every actual type of a cover containing `x₀` at positions `ι` lies in the
pointed age of a rigid core of type `p`. -/
theorem IsGloballyRigidCore.mem_rigidCoreAge {p : StageType.{u} α k₀} {x₀ : Fin k₀ → M}
    (hcore : R.IsGloballyRigidCore x₀) (hR : R.IsModel) (hc : R.Covers p x₀) {s : Fin m ↪ M}
    (ι : Fin k₀ ↪ Fin m) {D : StageType.{u} α m} (hs : R.eval s = some D) (hsι : ⇑s ∘ ι = x₀) :
    D ∈ StageType.rigidCoreAge p m ι := by
  refine StageType.mem_rigidCoreAge.mpr
    ⟨hR.isLegal s D hs, ?_, hcore D s ι (covers_of_eval s hs) hsι⟩
  rw [← hR.isConsistent s D ι hs, ← hc.eval_eq]
  congr 1
  ext i
  exact congrFun hsι i

/-- In a model, the actual types are legal with top grade at most the top-grade supremum. -/
theorem IsModel.isLegal_and_topGrade_le {K : ℕ} (hR : R.IsModel) (hK : R.topGradeSup = K)
    {s : Fin m ↪ M} {D : StageType.{u} α m} (hs : R.eval s = some D) :
    D.IsLegal ∧ D.topGrade ≤ K :=
  ⟨hR.isLegal s D hs, by exact_mod_cast hK ▸ (⟨m, s, D, hs⟩ : R.Occurrence).topGrade_le_topGradeSup⟩

end Receiving

/-! ### The named receiving hypotheses -/

/-- **Exact residual receiving**, (R2) of the table of Layer 3, still to be proved: in a model at a
limit stage with no cover that is a globally rigid core and with top-grade supremum `K`, over
every cover `c` of a stage type `t`, the empty cover included, every one-point coface of `t` of
top grade at most `K` is the type of `c` extended by one point. -/
structure ResidualReceiving : Prop where
  /-- Over every cover, every one-point coface of top grade at most `K` is received exactly. -/
  exists_covers ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄ ⦃K : ℕ⦄ :
    Order.IsSuccLimit α → R.IsModel →
      (¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
        R.IsGloballyRigidCore c) →
      R.topGradeSup = K → ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
        ∀ D ∈ t.cofaces, D.topGrade ≤ K → ∃ y : M, R.Covers D (Fin.snoc c y)

/-- **Exact hollow-growth receiving**, (R3) of the table of Layer 3, still to be proved: in a
model at a limit stage satisfying `H`, with unbounded top-grade growth, over every cover `c` of a
stage type `t`, the empty cover included, every one-point coface of `t` is the type of `c`
extended by one point.  The predicate `H` is to be fixed as the hollowness predicate of the
continuation criterion (output 3 of higher-stage reconstruction); it is a parameter here. -/
structure HollowReceiving (H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop) :
    Prop where
  /-- Over every cover, every one-point coface is received exactly. -/
  exists_covers ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄ :
    Order.IsSuccLimit α → R.IsModel → H R → R.topGradeSup = ⊤ →
      ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
        ∀ D ∈ t.cofaces, ∃ y : M, R.Covers D (Fin.snoc c y)

/-! ### The comparisons -/

section Comparison

variable {M N : Type w} [baseLanguage.{u}.Structure M] [baseLanguage.{u}.Structure N]
  [Countable M] [Countable N] {R : Realization.{u, w} α M} {R' : Realization.{u, w} α N}

/-- **The rigid-core comparison**: two expansions of countable base structures at a limit stage,
with finite-extension receiving, and with globally rigid cores `x₀` and `y₀` covering one stage
type `p`, have an isomorphism of their base structures carrying `x₀` to `y₀`. -/
theorem exists_equiv_comp_eq_of_isGloballyRigidCore {p : StageType.{u} α k₀} {x₀ : Fin k₀ → M}
    {y₀ : Fin k₀ → N} (hα : Order.IsSuccLimit α) (he : R.IsExpansionOf) (he' : R'.IsExpansionOf)
    (hrec : R.HasFiniteExtensionReceiving) (hrec' : R'.HasFiniteExtensionReceiving)
    (hc : R.Covers p x₀) (hc' : R'.Covers p y₀) (hcore : R.IsGloballyRigidCore x₀)
    (hcore' : R'.IsGloballyRigidCore y₀) : ∃ e : M ≃[baseLanguage.{u}] N, ⇑e ∘ x₀ = y₀ :=
  exists_equiv_comp_eq_of_exactReceivingWithinAt he he'
    (fun _ _ ι _ hs hsι ↦ hcore.mem_rigidCoreAge he.isModel hc ι hs hsι)
    (fun _ _ ι _ hs hsι ↦ hcore'.mem_rigidCoreAge he'.isModel hc' ι hs hsι)
    (exactReceivingWithinAt_rigidCoreAge he.isModel.isConsistent hα hrec x₀ p)
    (exactReceivingWithinAt_rigidCoreAge he'.isModel.isConsistent hα hrec' y₀ p) hc hc'

/-- **The rigid-core comparison**, unpointed. -/
theorem nonempty_equiv_of_isGloballyRigidCore {p : StageType.{u} α k₀} {x₀ : Fin k₀ → M}
    {y₀ : Fin k₀ → N} (hα : Order.IsSuccLimit α) (he : R.IsExpansionOf) (he' : R'.IsExpansionOf)
    (hrec : R.HasFiniteExtensionReceiving) (hrec' : R'.HasFiniteExtensionReceiving)
    (hc : R.Covers p x₀) (hc' : R'.Covers p y₀) (hcore : R.IsGloballyRigidCore x₀)
    (hcore' : R'.IsGloballyRigidCore y₀) : Nonempty (M ≃[baseLanguage.{u}] N) :=
  let ⟨e, _⟩ := exists_equiv_comp_eq_of_isGloballyRigidCore hα he he' hrec hrec' hc hc' hcore
    hcore'
  ⟨e⟩

omit [Countable M] [Countable N] in
/-- Two expansions have covers of one stage type on no points by the empty tuples. -/
private theorem exists_covers_zero₂ (he : R.IsExpansionOf) (he' : R'.IsExpansionOf) :
    ∃ p : StageType.{u} α 0, R.Covers p ![] ∧ R'.Covers p ![] := by
  obtain ⟨p, hp⟩ := he.isModel.exists_covers_zero
  obtain ⟨p', hp'⟩ := he'.isModel.exists_covers_zero
  exact ⟨p, hp, StageType.eq_of_zero p' p ▸ hp'⟩

/-- **The top-free comparison**, the rigid-core comparison on no points: two expansions of
countable base structures at a limit stage, with finite-extension receiving and top-grade
supremum `0`, have isomorphic base structures. -/
theorem nonempty_equiv_of_topGradeSup_eq_zero (hα : Order.IsSuccLimit α) (he : R.IsExpansionOf)
    (he' : R'.IsExpansionOf) (hrec : R.HasFiniteExtensionReceiving)
    (hrec' : R'.HasFiniteExtensionReceiving) (h : R.topGradeSup = 0) (h' : R'.topGradeSup = 0) :
    Nonempty (M ≃[baseLanguage.{u}] N) :=
  let ⟨_, hp, hp'⟩ := exists_covers_zero₂ he he'
  nonempty_equiv_of_isGloballyRigidCore hα he he' hrec hrec' hp hp'
    ((he.isModel.isGloballyRigidCore_empty_iff hα).mpr h)
    ((he'.isModel.isGloballyRigidCore_empty_iff hα).mpr h')

/-- The comparison over a face-closed family from one-point exact receiving, starting from the
empty covers. -/
private theorem nonempty_equiv_of_one_point {A : ∀ m, Set (StageType.{u} α m)}
    (hA : ∀ ⦃m k : ℕ⦄ (D : StageType.{u} α m) (f : Fin k ↪ Fin m) (p : StageType.{u} α k),
      D ∈ A m → StageType.restrictFace f D = some p → p ∈ A k)
    (he : R.IsExpansionOf) (he' : R'.IsExpansionOf)
    (hage : ∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (D : StageType.{u} α m), R.eval s = some D → D ∈ A m)
    (hage' : ∀ ⦃m : ℕ⦄ (s : Fin m ↪ N) (D : StageType.{u} α m), R'.eval s = some D → D ∈ A m)
    (h1 : ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
      ∀ D ∈ A (n + 1), StageType.restrictFace Fin.castSuccEmb D = some t →
        ∃ y : M, R.Covers D (Fin.snoc c y))
    (h1' : ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → N), R'.Covers t c →
      ∀ D ∈ A (n + 1), StageType.restrictFace Fin.castSuccEmb D = some t →
        ∃ y : N, R'.Covers D (Fin.snoc c y)) :
    Nonempty (M ≃[baseLanguage.{u}] N) :=
  let ⟨_, hp, hp'⟩ := exists_covers_zero₂ he he'
  nonempty_equiv_of_exactReceivingWithin he he' hage hage'
    (.of_one_point he.isModel.isConsistent hA fun _ t c hc D hD hDt ↦
      let ⟨y, hy⟩ := h1 t c hc D hD hDt
      ⟨Fin.snoc c y, hy, Fin.snoc_comp_castSucc⟩)
    (.of_one_point he'.isModel.isConsistent hA fun _ t c hc D hD hDt ↦
      let ⟨y, hy⟩ := h1' t c hc D hD hDt
      ⟨Fin.snoc c y, hy, Fin.snoc_comp_castSucc⟩) hp hp'

/-- **The residual comparison**, under (R2): two expansions of countable base structures at a
limit stage, with no cover that is a globally rigid core and with the same top-grade supremum
`K`, have isomorphic base structures.  The age is that of the legal types of top grade at most
`K`. -/
theorem nonempty_equiv_of_residual (hres : ResidualReceiving.{u, w}) (hα : Order.IsSuccLimit α)
    (he : R.IsExpansionOf) (he' : R'.IsExpansionOf)
    (hcore : ¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
      R.IsGloballyRigidCore c)
    (hcore' : ¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → N), R'.Covers p c ∧
      R'.IsGloballyRigidCore c)
    {K : ℕ} (hK : R.topGradeSup = K) (hK' : R'.topGradeSup = K) :
    Nonempty (M ≃[baseLanguage.{u}] N) :=
  nonempty_equiv_of_one_point (A := fun _ ↦ {D | D.IsLegal ∧ D.topGrade ≤ K})
    (fun _ _ _ _ _ hD hf ↦ StageType.isLegal_and_topGrade_le_of_restrictFace hD hf) he he'
    (fun _ _ _ hs ↦ he.isModel.isLegal_and_topGrade_le hK hs)
    (fun _ _ _ hs ↦ he'.isModel.isLegal_and_topGrade_le hK' hs)
    (fun _ t c hc D hD hDt ↦ hres.exists_covers hα he.isModel hcore hK t c hc D ⟨hD.1, hDt⟩ hD.2)
    (fun _ t c hc D hD hDt ↦ hres.exists_covers hα he'.isModel hcore' hK' t c hc D ⟨hD.1, hDt⟩
      hD.2)

/-- **The hollow comparison**, under (R3) for a predicate `H` (to be fixed as hollowness): two
expansions of countable base structures at a limit stage satisfying `H`, with unbounded
top-grade growth, have isomorphic base structures.  The age is that of all legal types. -/
theorem nonempty_equiv_of_hollow
    {H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop}
    (hhol : HollowReceiving.{u, w} H) (hα : Order.IsSuccLimit α) (he : R.IsExpansionOf)
    (he' : R'.IsExpansionOf) (hH : H R) (hH' : H R') (h : R.topGradeSup = ⊤)
    (h' : R'.topGradeSup = ⊤) : Nonempty (M ≃[baseLanguage.{u}] N) :=
  nonempty_equiv_of_one_point (A := fun _ ↦ {D | D.IsLegal})
    (fun _ _ _ f _ hD hf ↦ StageType.IsLegal.restrictFace f hD hf) he he'
    (fun _ s D hs ↦ he.isModel.isLegal s D hs) (fun _ s D hs ↦ he'.isModel.isLegal s D hs)
    (fun _ t c hc D hD hDt ↦ hhol.exists_covers hα he.isModel hH h t c hc D ⟨hD, hDt⟩)
    (fun _ t c hc D hD hDt ↦ hhol.exists_covers hα he'.isModel hH' h' t c hc D ⟨hD, hDt⟩)

end Comparison

end Realization

end VaughtConjecture
