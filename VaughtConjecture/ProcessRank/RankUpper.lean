/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.ScottAnalysis
import VaughtConjecture.Realization.Closure

/-!
# Process rank `ω₁` from exact receiving within the realized age

Companion programme over the density sentence, process rank `ω₁`.  Conventions as in
`VaughtConjecture.ProcessRank.RankConventions`: `r(a) = orbitRank a`,
`R(M) = sup_a (r(a))`.  Every statement here is a **given-model statement** about one receiving
model expansion `R` at stage `ω₁`.

**Lower bound, in every receiving model** (`lift_omegaOne_le_iSup_orbitRank`, proved).  For every
countable `ξ` some tuple has `r(a) > ξ` (`AlephOne.existsOrbitRankGtTarget`, the one-point pair
of `AlephOne.onePointPairOccursTarget`); top-freeness of the model is not used there.  So
`R(M)` is at least the lift of `ω₁` in every receiving model expansion at `ω₁`, top-bearing ones
included.

**Upper bound, from exact receiving within the realized age.**  The **realized age** of `R`
(`realizedAge`, with `mem_realizedAge_iff`) is the family of the stage types of its covers.  Two
steps.

1. Matching hulls (`ExistsCoverMatchOfBFEquivOmegaOneTarget`, proved; every receiving model): if
   tuples `a`, `b` of `M` are back-and-forth equivalent at `ω₁`, they are selections along one
   selector of covers of one stage type at `ω₁`.  Route: enumerate the finite hull of `a` by a
   cover of `p`; at each countable block stage the formula saying that a tuple is the selection of
   a cover of the reduction of `p` has countable rank, so `b` satisfies it; the matching covers
   enumerate the finite hull of `b`; one of finitely many enumerations serves for unboundedly many
   `η` (`exists_cofinal_eq_of_finite`), and its type is `p`, since stage types at `ω₁` are
   separated by their countable reductions (`stageType_eq_of_forall_reduce_eq`, through
   `blockStage_omegaOne`).
2. Exact-age comparison within `M` (`orbitRankLeOmegaOneOfExactReceivingTarget_of_coverMatch`,
   proved from step 1): matched tuples are equivalent at every level by the rooted back-and-forth
   family (`Realization.CoverMatch.bfEquiv`) for the realized age at the empty cores.

So, with exact receiving within the realized age, `r(a) ≤ ω₁` for every `a`
(`OrbitRankLeOmegaOneOfExactReceivingTarget`, proved) and `R(M)` is the lift of `ω₁`
(`iSup_orbitRank_eq_omegaOne_of_exactReceiving`, proved from the bound).

**Results.**

* `realizedAge`, `mem_realizedAge_iff` (proved).
* `lift_omegaOne_le_iSup_orbitRank` (proved).
* `blockStage_omegaOne`, `stageType_eq_of_forall_reduce_eq`, `exists_cofinal_eq_of_finite`
  (proved).
* `ExistsCoverMatchOfBFEquivOmegaOneTarget` (proved, `existsCoverMatchOfBFEquivOmegaOneTarget`).
* `OrbitRankLeOmegaOneOfExactReceivingTarget` (proved, `orbitRankLeOmegaOneOfExactReceivingTarget`),
  through `orbitRankLeOmegaOneOfExactReceivingTarget_of_coverMatch` (step 2).
* `iSup_orbitRank_eq_omegaOne_of_exactReceiving` (proved from
  `OrbitRankLeOmegaOneOfExactReceivingTarget`).
-/

universe u v w

namespace VaughtConjecture.ProcessRank

open Ordinal _root_.Order FirstOrder Language

/-- The **realized age** of a realization: at each number `m` of points, the stage types it
covers on `m` points. -/
def realizedAge {α : Ordinal.{u}} {M : Type v} (R : Realization.{u, v} α M) (m : ℕ) :
    Set (StageType.{u} α m) :=
  {D | ∃ x : Fin m → M, R.Covers D x}

/-- **Membership in the realized age** is being covered. -/
theorem mem_realizedAge_iff {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M} {m : ℕ}
    {p : StageType.{u} α m} : p ∈ realizedAge R m ↔ ∃ x : Fin m → M, R.Covers p x :=
  Iff.rfl

/-- **`R(M)` is at least `ω₁` in every receiving model expansion at `ω₁`**: every countable `ξ`
is exceeded by some `r(a)` (`AlephOne.existsOrbitRankGtTarget`). -/
theorem lift_omegaOne_le_iSup_orbitRank {M : Type w} [baseLanguage.{0}.Structure M]
    (R : ModelExpansion M ω₁) (hR : R.1.IsReceivingModel) :
    Ordinal.lift.{w} (ω₁ : Ordinal.{0}) ≤
      ⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := baseLanguage.{0}) x.2 := by
  refine le_of_forall_lt fun γ hγ ↦ ?_
  obtain ⟨ξ, hξ, rfl⟩ := Ordinal.lt_lift_iff.1 hγ
  obtain ⟨n, a, ha⟩ := AlephOne.existsOrbitRankGtTarget R hR hξ
  exact ha.trans_le (orbitRank_le_iSup_orbitRank a)

/-- **Target: tuples equivalent at `ω₁` are matched through one chart.**  In a receiving model
expansion `R` to `ω₁`, two tuples `a`, `b` of `M` back-and-forth equivalent at `ω₁` in the base
language are the selections `x ∘ s`, `y ∘ s` along one selector `s` of covers `x`, `y` of one
stage type at `ω₁`.  Given-model statement.  Proved (`existsCoverMatchOfBFEquivOmegaOneTarget`).
-/
def ExistsCoverMatchOfBFEquivOmegaOneTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁), R.1.IsReceivingModel →
    ∀ ⦃n : ℕ⦄ (a b : Fin n → M), BFEquiv (L := baseLanguage.{0}) (ω₁ : Ordinal.{0}) n a b →
      ∃ (k : ℕ) (p : StageType.{0} ω₁ k) (x y : Fin k → M) (s : Fin n → Fin k),
        R.1.Covers p x ∧ R.1.Covers p y ∧ x ∘ s = a ∧ y ∘ s = b

/-- **Target: orbit ranks at most `ω₁` under exact receiving within the realized age.**  In a
receiving model expansion `R` to `ω₁` with exact receiving within its realized age, every tuple
has `r(a)` at most the lift of `ω₁`.  Given-model statement.  Proved
(`orbitRankLeOmegaOneOfExactReceivingTarget`). -/
def OrbitRankLeOmegaOneOfExactReceivingTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁), R.1.IsReceivingModel →
    R.1.ExactReceivingWithin (realizedAge R.1) →
      ∀ ⦃n : ℕ⦄ (a : Fin n → M),
        orbitRank (L := baseLanguage.{0}) a ≤ Ordinal.lift.{w} (ω₁ : Ordinal.{0})

/-- **Step 2: the exact-age comparison within the model.**  Matched tuples
(`ExistsCoverMatchOfBFEquivOmegaOneTarget`) are pairs of the rooted back-and-forth family of `R`
with itself for the realized age at the empty cores, hence equivalent at every level
(`Realization.CoverMatch.bfEquiv`). -/
theorem orbitRankLeOmegaOneOfExactReceivingTarget_of_coverMatch
    (h : ExistsCoverMatchOfBFEquivOmegaOneTarget.{w}) :
    OrbitRankLeOmegaOneOfExactReceivingTarget.{w} := by
  intro M _ R hR hex n a
  refine orbitRank_le_of_mem fun b hb γ ↦ ?_
  obtain ⟨k, p, x, y, s, hx, hy, rfl, rfl⟩ := h R hR a b hb.toOrdinalLift
  obtain ⟨p₀, hp₀⟩ := hR.1.exists_covers_zero
  have hage : ∀ ⦃m : ℕ⦄ (t : Fin m ↪ M) (ι : Fin 0 ↪ Fin m) (D : StageType.{0} ω₁ m),
      R.1.eval t = some D → ⇑t ∘ ι = ![] → D ∈ realizedAge R.1 m :=
    fun _ t _ D hD _ ↦ ⟨t, Realization.covers_of_eval t hD⟩
  have hr := hex.exactReceivingWithinAt (![] : Fin 0 → M)
  exact Realization.CoverMatch.bfEquiv R.2 R.2 hage hage hr hr hp₀ hp₀
    ⟨k, p, x, y, Function.Embedding.ofIsEmpty, s, hx, hy, funext fun i ↦ i.elim0,
      funext fun i ↦ i.elim0, rfl, rfl⟩ γ

/-- **`R(M)` is `ω₁` under exact receiving within the realized age**, given the upper bound
`OrbitRankLeOmegaOneOfExactReceivingTarget`; the lower bound is
`lift_omegaOne_le_iSup_orbitRank`. -/
theorem iSup_orbitRank_eq_omegaOne_of_exactReceiving
    (h : OrbitRankLeOmegaOneOfExactReceivingTarget.{w}) {M : Type w}
    [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁) (hR : R.1.IsReceivingModel)
    (hex : R.1.ExactReceivingWithin (realizedAge R.1)) :
    (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := baseLanguage.{0}) x.2) =
      Ordinal.lift.{w} (ω₁ : Ordinal.{0}) :=
  le_antisymm (iSup_orbitRank_le_iff.2 fun _ a ↦ h R hR hex a)
    (lift_omegaOne_le_iSup_orbitRank R hR)

/-! ### The matching of hulls -/

/-- The block stage of index `ω₁` is `ω₁`: `ω` and `ω₁` are below `ω₁`, which is closed under
ordinal multiplication and addition. -/
theorem blockStage_omegaOne : blockStage (ω₁ : Ordinal.{u}) = ω₁ := by
  have hω : ω < (ω₁ : Ordinal.{u}) := omega0_lt_omega_one
  rw [blockStage, isPrincipal_mul_iff_mul_left_eq.1 (isPrincipal_mul_omega 1) ω omega0_pos hω,
    isPrincipal_add_iff_add_left_eq_self.1 (isPrincipal_add_omega 1) ω hω]

/-- **A stage type at `ω₁` is determined by its countable reductions**: two stage types at `ω₁`
with the same reduction to every countable block stage are equal
(`StageType.eq_of_forall_reduce_eq_of_isSuccLimit` at the index `ω₁`, with
`blockStage_omegaOne`). -/
theorem stageType_eq_of_forall_reduce_eq {k : ℕ} {t t' : StageType.{0} ω₁ k}
    (h : ∀ ξ < (ω₁ : Ordinal.{0}),
      t.reduce (isSuccPrelimit_blockStage ξ) = t'.reduce (isSuccPrelimit_blockStage ξ)) :
    t = t' := by
  have key : ∀ {α : Ordinal.{0}} (_ : blockStage (ω₁ : Ordinal.{0}) = α) (t t' : StageType.{0} α k),
      (∀ ξ < (ω₁ : Ordinal.{0}),
        t.reduce (isSuccPrelimit_blockStage ξ) = t'.reduce (isSuccPrelimit_blockStage ξ)) →
        t = t' := by
    rintro _ rfl t t' h
    exact StageType.eq_of_forall_reduce_eq_of_isSuccLimit (Cardinal.isSuccLimit_omega 1) h
  exact key blockStage_omegaOne t t' h

/-- **A value taken cofinally often below `ω₁`**: a map from the countable ordinals to a finite
type takes some value at indices above every countable ordinal.  Otherwise each value is bounded
below `ω₁`, and the largest of these finitely many bounds is a countable index at which no value
is taken. -/
theorem exists_cofinal_eq_of_finite {β : Type*} [Finite β]
    (g : ∀ η : Ordinal.{0}, η < ω₁ → β) :
    ∃ v : β, ∀ ζ < (ω₁ : Ordinal.{0}), ∃ η, ∃ hη : η < ω₁, ζ ≤ η ∧ g η hη = v := by
  by_contra hne
  push Not at hne
  choose ζ hζ hζg using hne
  have := Fintype.ofFinite β
  have hω : IsSuccLimit (ω₁ : Ordinal.{0}) := Cardinal.isSuccLimit_omega 1
  have hm : Finset.univ.sup ζ < (ω₁ : Ordinal.{0}) :=
    (Finset.sup_lt_iff hω.bot_lt).mpr fun v _ ↦ hζ v
  exact hζg (g _ hm) _ hm (Finset.le_sup (f := ζ) (Finset.mem_univ _)) rfl

/-- **Tuples equivalent at `ω₁` are matched through one chart**, the target form.

Let `x` enumerate the canonical hull of the points of `a`, with `x ∘ f = a`; in the plan of its
type `p`, the hull of the coordinates selected by `f` is everything.  At each countable block
index `η`, the formula saying that a tuple is the selection along `f` of a cover of the reduction
of `p` to `λ_η` has countable rank (`chartSelectionFormula`, read through
`realizeBlockFormulaOfIsReceivingModelTarget`), so `b` satisfies it: `b = y_η ∘ f` for a cover
`y_η` of that reduction.  Since the hull of the selected coordinates is everything, the points of
`y_η` are the canonical hull of the points of `b`, the same at every stage
(`Realization.finiteHull_eq`, `Realization.finiteHull_reduce`).  So `y_η` ranges over the
finitely many tuples of that hull, and one tuple `y` occurs above every countable ordinal
(`exists_cofinal_eq_of_finite`).  The type of `y` has the reduction of `p` at cofinally many,
hence at all, countable block stages, so it is `p` (`stageType_eq_of_forall_reduce_eq`). -/
theorem existsCoverMatchOfBFEquivOmegaOneTarget : ExistsCoverMatchOfBFEquivOmegaOneTarget.{w} := by
  intro M _ R hR n a b hab
  classical
  have hω : IsSuccLimit (ω₁ : Ordinal.{0}) := Cardinal.isSuccLimit_omega 1
  have hcon := hR.1.isConsistent
  have hcov := hR.1.isCovering
  -- the canonical hull of the points of `a`, enumerated by an occurrence `x`
  obtain ⟨x, hx⟩ := Realization.isSupport_finiteHull hcon hcov (Finset.univ.image a)
  have haF : Finset.univ.image a ⊆ x.support := hx ▸ Realization.subset_finiteHull _
  have hf : ∀ i, ∃ j, x.tuple j = a i := fun i ↦
    (x.mem_support).1 (haF (Finset.mem_image_of_mem a (Finset.mem_univ i)))
  choose f hf using hf
  have hxf : ⇑x.tuple ∘ f = a := funext hf
  subst hxf
  have hmap : ∀ y : Fin x.arity ↪ M,
      Finset.univ.image (⇑y ∘ f) = (Finset.univ.image f).map y := fun y ↦ by
    rw [Finset.map_eq_image, Finset.image_image]
  -- the hull of the selected coordinates is everything
  have hgen : Geometry.hull Finset.univ x.type.toCellScheme.faces (Finset.univ.image f) =
      Finset.univ := by
    have h1 : x.hull (Finset.univ.image (⇑x.tuple ∘ f)) = x.support :=
      (Realization.finiteHull_eq hcon hcov x haF).symm.trans hx.symm
    rw [hmap, Realization.Occurrence.hull, Realization.Occurrence.coords_map,
      Realization.Occurrence.support] at h1
    exact Finset.map_inj.1 h1
  -- at each countable stage, `b` is a selection of a cover of the reduction of the type of `x`
  have hsel : ∀ η (hη : η < (ω₁ : Ordinal.{0})), ∃ y : Fin x.arity → M,
      (R.1.reduce (isSuccPrelimit_blockStage η)).Covers
        (x.type.reduce (isSuccPrelimit_blockStage η)) y ∧ y ∘ f = b := by
    intro η hη
    have hφa : (chartSelectionFormula hη x.type f).Realize (⇑x.tuple ∘ f) := by
      rw [chartSelectionFormula, realize_extendFormula]
      exact ⟨x.tuple, rfl, (realizeBlockFormulaOfIsReceivingModelTarget R hR hη _ _).2
        ((Realization.covers_of_eval x.tuple x.eval_tuple).reduce _)⟩
    have hφb : (chartSelectionFormula hη x.type f).Realize b := (BFEquiv_implies_agreeQR _ _ b
      (BFEquiv.monotone (qrank_chartSelectionFormula_lt hη x.type f).le hab) _ le_rfl).1 hφa
    rw [chartSelectionFormula, realize_extendFormula] at hφb
    obtain ⟨y, hyf, hy⟩ := hφb
    exact ⟨y, (realizeBlockFormulaOfIsReceivingModelTarget R hR hη _ _).1 hy, hyf⟩
  choose y hy hyf using hsel
  -- every such cover enumerates the canonical hull of the points of `b`
  have hrange : ∀ η (hη : η < (ω₁ : Ordinal.{0})) (i : Fin x.arity),
      y η hη i ∈ R.1.finiteHull (Finset.univ.image b) := by
    intro η hη i
    have hβ := isSuccPrelimit_blockStage η
    let z : (R.1.reduce hβ).Occurrence :=
      ⟨x.arity, ⟨y η hη, (hy η hη).injective⟩, _, (hy η hη).eval_eq⟩
    have hbF : Finset.univ.image b = (Finset.univ.image f).map z.tuple := by
      rw [← hyf η hη]
      exact hmap z.tuple
    have hFz : Finset.univ.image b ⊆ z.support := by
      rw [hbF, Realization.Occurrence.support]
      exact Finset.map_subset_map.2 (Finset.subset_univ _)
    have h1 := Realization.finiteHull_eq (hcon.reduce hβ) (hcov.reduce hβ) z hFz
    rw [Realization.finiteHull_reduce hcon hcov hβ] at h1
    rw [h1, hbF, Realization.Occurrence.hull, Realization.Occurrence.coords_map]
    change y η hη i ∈ (Geometry.hull Finset.univ x.type.toCellScheme.faces
      (Finset.univ.image f)).map z.tuple
    rw [hgen]
    exact Finset.mem_map_of_mem z.tuple (Finset.mem_univ i)
  -- one tuple of the hull occurs cofinally often
  obtain ⟨v, hv⟩ := exists_cofinal_eq_of_finite
    fun η hη (i : Fin x.arity) ↦ (⟨y η hη i, hrange η hη i⟩ : R.1.finiteHull (Finset.univ.image b))
  let y₀ : Fin x.arity → M := fun i ↦ (v i : M)
  have hcof : ∀ ζ < (ω₁ : Ordinal.{0}), ∃ η, ∃ hη : η < ω₁, ζ ≤ η ∧ y η hη = y₀ := by
    intro ζ hζ
    obtain ⟨η, hη, hζη, hg⟩ := hv ζ hζ
    exact ⟨η, hη, hζη, funext fun i ↦ congrArg Subtype.val (congrFun hg i)⟩
  -- the type of `y₀`
  obtain ⟨η₀, hη₀, -, hy₀⟩ := hcof 0 hω.bot_lt
  have hc₀ := hy η₀ hη₀
  rw [hy₀] at hc₀
  have he₀ := hc₀.eval_eq
  rw [Realization.reduce_eval, Option.map_eq_some_iff] at he₀
  obtain ⟨p', hp', -⟩ := he₀
  have hall : ∀ ζ < (ω₁ : Ordinal.{0}), p'.reduce (isSuccPrelimit_blockStage ζ) =
      x.type.reduce (isSuccPrelimit_blockStage ζ) := by
    intro ζ hζ
    obtain ⟨η, hη, hζη, hyη⟩ := hcof ζ hζ
    have hcη := hy η hη
    rw [hyη] at hcη
    have he := hcη.eval_eq
    rw [Realization.reduce_eval, Option.map_eq_some_iff] at he
    obtain ⟨p'', hp'', hred⟩ := he
    obtain rfl : p' = p'' := Option.some_injective _ (hp'.symm.trans hp'')
    rw [← StageType.reduce_reduce p' (isSuccPrelimit_blockStage η) _ (blockStage_mono hζη), hred,
      StageType.reduce_reduce _ (isSuccPrelimit_blockStage η) _ (blockStage_mono hζη)]
  obtain rfl := stageType_eq_of_forall_reduce_eq hall
  refine ⟨x.arity, x.type, x.tuple, y₀, f, Realization.covers_of_eval x.tuple x.eval_tuple,
    ⟨hc₀.injective, hp'⟩, rfl, ?_⟩
  rw [← hy₀]
  exact hyf η₀ hη₀

/-- **Orbit ranks at most `ω₁` under exact receiving within the realized age**, the target form:
`orbitRankLeOmegaOneOfExactReceivingTarget_of_coverMatch` with
`existsCoverMatchOfBFEquivOmegaOneTarget`. -/
theorem orbitRankLeOmegaOneOfExactReceivingTarget :
    OrbitRankLeOmegaOneOfExactReceivingTarget.{w} :=
  orbitRankLeOmegaOneOfExactReceivingTarget_of_coverMatch existsCoverMatchOfBFEquivOmegaOneTarget

end VaughtConjecture.ProcessRank
