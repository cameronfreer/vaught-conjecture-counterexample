/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Comparison
import VaughtConjecture.Extension.Basic
import VaughtConjecture.Realization.Receiving

/-!
# Exact residual and hollow receiving: reformulations and reduction to determination

Roadmap, Layer 3 ((R2) and (R3) of the table of 3.4: exact residual receiving and exact
hollow-growth receiving) and Layer 4 (the residual and hollow comparisons); semantic contract,
items 4 and 8.

(R2) (`Realization.ResidualReceiving`) and (R3) (`Realization.HollowReceiving H`) are stated in
`VaughtConjecture.Continuation.Comparison` as one-point statements over every cover of a model at a
limit stage: in a model with no cover that is a globally rigid core and with top-grade supremum
`K`, every one-point coface of top grade at most `K` of the type of a cover is the type of the
cover extended by one point; in a model satisfying `H` with top-grade supremum `⊤`, every one-point
coface is.  This file proves what follows from these statements and reduces each to a statement
about stage types together with a statement about models, both named.

**Exact reformulations.**  For an exactly consistent realization, one-point exact receiving of a
family closed under the face maps is exact receiving of every member of the family over every
cover, on any number of new points (`Realization.ExactReceivingWithin.of_one_point`).  So (R2) is
exact receiving of the legal stage types of top grade at most `K` in every residual model
(`Realization.residualReceiving_iff`), and (R3) exact receiving of all legal stage types in every
model satisfying `H` with unbounded growth (`Realization.hollowReceiving_iff`).  These are
reformulations, not reductions.

**(R3) excludes non-rigid donors over a rigid core.**  (R3) has no hypothesis excluding a globally
rigid core, and the definitions do not exclude a cover-hollow model with unbounded growth and a
globally rigid core (`VaughtConjecture.Continuation.Classification`).  In such a model a received
donor is the type of a cover containing the core, so under (R3) the core is rigid in every legal
donor over its type (`Realization.HollowReceiving.isRigidCoreIn`).  So (R3) asserts that such
models have no legal donor over a rigid core in which the core is not rigid.  With (R3) for
cover-hollowness, the count uses (R3) at every cover-hollow model with unbounded growth, a globally
rigid core included: the cover of the terminal models (`Realization.exists_hasTerminalProperty`)
checks unbounded growth first and assigns the hollow property whatever the cores are, and the
hollow property (`Realization.HasTerminalProperty`) does not exclude a globally rigid core.

The restricted alternative (`VaughtConjecture.Continuation.RestrictedHollow`) excludes a globally
rigid core from the hollow property and from the predicate given to (R3)
(`Realization.HasRestrictedTerminalProperty`, `Realization.IsCoverHollowWithoutRigidCoreAtBlock`):
the cover of the terminal models survives (`Realization.exists_hasRestrictedTerminalProperty`),
models with a globally rigid core go through the rigid-core comparison, and the count needs (R3)
only for that stronger predicate, which (R3) for cover-hollowness implies
(`Realization.HollowReceiving.withoutRigidCore`, an instance of `Realization.HollowReceiving.mono`).
It is a separate hypothesis set, not shown equivalent to (R3) for cover-hollowness.

**The rigid part is (R1).**  Under finite-cut receiving ((R1), `Realization.HasFiniteCutReceiving`),
at a limit stage, a one-point coface in which the root is a rigid core is received exactly
(`Realization.exists_covers_snoc_of_isRigidCoreIn`, the one-point case of the rigid-core receiving
`Realization.exists_covers_of_isRigidCoreIn` of the rigid-core comparison): top-free cofaces in
particular.  So (R2) and (R3) follow from (R1) for every model at every limit stage, together
with their restriction to the cofaces in which the root is not a rigid core
(`Realization.ResidualReceiving.of_not_isRigidCoreIn`,
`Realization.HollowReceiving.of_not_isRigidCoreIn`).  That restriction is where literal-top
recovery is needed: receiving at a cutoff above the labels of the donor that are not `⊤` returns a
type agreeing with the donor except that a top cell may carry an ordinal at least the cutoff.

This receiving hypothesis ranges over every limit stage at fixed universe levels and is not
supplied by the countable-stage `Expansion.FiniteCutReceiving`, the library's (R1) for models
(limit stages below `ω₁`, universe `0`).  The mismatch comes from (R2) and (R3), which are
themselves stated at every limit stage.

**Determination.**  Let `t'` be a stage type on `k` points, `h : Fin n ↪ Fin k`, and `d` a stage
type on `n + 1` points.  For a set `U` of stage types on `k + 1` points, `d` is **determined over
`t'` along `h` within `U`** (`StageType.IsDeterminedWithin`) when every member of `U` whose face
along the initial segment is `t'` has face `d` along `h` followed by the new point
(`extendByLast h`).  If a cover `c'` of `t'` in an exactly consistent realization realizes a member
of `U` over it (`Realization.RealizesOver`), then `d` is the type of `c' ∘ h` extended by one point
(`Realization.exists_covers_snoc_of_isDeterminedWithin`).  Two families supply the realized
member:

* the stage types on the scheme of a coface `D'` of `t'` (`StageType.saturationFamily`), realized
  by generalized saturation, clause 4(a)i of modelhood
  (`Realization.IsModel.realizesOver_saturationFamily`); no receiving is used;
* the receiving family of a coface `D'` of `t'` at a permitted cutoff
  (`StageType.receivingFamily`), realized by finite-cut receiving
  (`Realization.HasFiniteCutReceiving.realizesOver_receivingFamily`), which is (R1).

The rigid-core case is the instance with `t'` the root, `h` the identity, `D' = d`, and a cutoff
above every label of `d` other than `⊤`
(`StageType.isDeterminedWithin_receivingFamily_of_isRigidCoreIn`, from
`StageType.eq_of_mem_receivingFamily_of_isRigidCoreIn`).

**The reductions.**  Each of (R2) and (R3) is reduced to two named statements, for a predicate
`P` on pairs `(t', h)`, the **acquired context**:

* an **acquisition** statement about models: every cover `c` of a model of the kind in question
  extends to a cover `c'` of some `t'` with `c' ∘ h = c` and `P t' h`
  (`Realization.ResidualAcquisition`, `Realization.HollowAcquisition`);
* a **determination** statement about stage types: over every legal `t'` with `P t' h`, every
  one-point coface `d` (of top grade at most `K` in the residual case) of the face of `t'` along
  `h` is determined over `t'` along `h`, at a permitted cutoff within the receiving family of some
  coface of `t'` in the residual case (`Realization.CutoffDetermination`), and within the stage
  types on the scheme of some coface of `t'` in the hollow case
  (`Realization.SchemeDetermination`).

Then (R2) follows from (R1) for every model at every limit stage (a receiving hypothesis that
ranges over every limit stage at fixed universe levels and is not supplied by the countable-stage
`Expansion.FiniteCutReceiving`, as above), residual acquisition, and cutoff
determination (`Realization.residualReceiving_of_cutoffDetermination`), and (R3) from hollow
acquisition and scheme determination, with no receiving
(`Realization.hollowReceiving_of_schemeDetermination`).  This is the form of the constructions of
3.3: in the residual case the acquired context is the private context with a private gap at grade
`K`, the coface `D'` is the display on the LOW scheme, and LOW recovery is cutoff determination;
in the hollow case the acquired context has the private cap and the marker labelled `⊤`, the
coface `D'` is on the constructed legal scheme of the growth construction, and the marker clause of
`Correct` gives scheme determination.  Neither predicate `P` is defined here, neither acquisition
nor determination is proved here for any `P`, and determination is proved only in the rigid-core
instance.

**Determination needs an acquired context.**  Over a top-free root `t` along the identity, a
one-point coface `d` of `t` that is not top-free is determined neither at a cutoff nor by a scheme
(`StageType.not_isDeterminedWithin_receivingFamily_of_isTopFree`,
`StageType.not_isDeterminedWithin_saturationFamily_of_isTopFree`): a determining coface would be
`d` itself, and the cap of `d` (`StageType.cap`) at an ordinal above the cutoff and the labels of
`t` is a top-free stage type on the scheme of `d`, in its receiving family, with face `t`.  So
cutoff determination and scheme determination for the predicate that is always true fail, already
at the empty root and the one-point stage type whose only cell is an apex labelled `⊤`
(`VaughtConjecture.Continuation.ExactReceivingExamples`).  So, along the identity (the only case
compiled), the acquired context must carry information that a top-free root lacks; in 3.3 it is
acquired from the absence of a rigid core (the private gap) or from hollowness (the private cap and
the marker labelled `⊤`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label

variable {α : Ordinal.{u}} {n k m : ℕ}

/-! ### Determination -/

namespace StageType

/-- A one-point type `d` is **determined over `t'` along `h` within `U`**: every member of `U`
whose face along the initial segment is `t'` has face `d` along `h` followed by the new point. -/
def IsDeterminedWithin (U : Set (StageType.{u} α (k + 1))) (t' : StageType.{u} α k)
    (h : Fin n ↪ Fin k) (d : StageType.{u} α (n + 1)) : Prop :=
  ∀ q ∈ U, restrictFace Fin.castSuccEmb q = some t' → restrictFace (extendByLast h) q = some d

/-- **The rigid-core instance of determination**: a legal one-point coface `d` of `t` in which the
root is a rigid core is determined over `t` along the identity within its receiving family at a
cutoff above every label of `d` other than `⊤`. -/
theorem isDeterminedWithin_receivingFamily_of_isRigidCoreIn {t : StageType.{u} α n}
    {d : StageType.{u} α (n + 1)}
    (hd : d.IsLegal) (hdt : restrictFace Fin.castSuccEmb d = some t)
    (hrig : d.IsRigidCoreIn Fin.castSuccEmb) {δ : Ordinal.{u}}
    (hδ : ∀ j, d.label j ≠ ⊤ → d.label j < (δ : Label.{u})) :
    IsDeterminedWithin (receivingFamily d δ) t (Function.Embedding.refl (Fin n)) d := by
  intro q hq hqt
  rw [extendByLast_refl, restrictFace_refl,
    eq_of_mem_receivingFamily_of_isRigidCoreIn hd hδ hq hqt hdt hrig]

/-- A one-point type determined over its root along the identity, within a family containing a
coface `D'` of the root, is `D'`. -/
private theorem eq_of_isDeterminedWithin_refl {U : Set (StageType.{u} α (n + 1))}
    {t : StageType.{u} α n} {d D' : StageType.{u} α (n + 1)}
    (hdet : IsDeterminedWithin U t (Function.Embedding.refl (Fin n)) d) (hD'U : D' ∈ U)
    (hD' : restrictFace Fin.castSuccEmb D' = some t) : D' = d := by
  have h := hdet D' hD'U hD'
  rwa [extendByLast_refl, restrictFace_refl, Option.some_inj] at h

/-- Over a top-free root, a cap of a one-point coface above a given ordinal keeps the root. -/
private theorem exists_cap_restrictFace (hα : Order.IsSuccLimit α) {t : StageType.{u} α n}
    (ht : t.IsTopFree) {d : StageType.{u} α (n + 1)}
    (hdt : restrictFace Fin.castSuccEmb d = some t) {o₀ : Ordinal.{u}} (ho₀ : o₀ < α) :
    ∃ (c : Ordinal.{u}) (hc : IsSelfVisible (n + 1) (c : Label.{u})) (hcα : c < α), o₀ ≤ c ∧
      restrictFace Fin.castSuccEmb (d.cap c hc hcα) = some t := by
  obtain ⟨o, ho, hto⟩ := ht.exists_label_le hα.bot_lt
  obtain ⟨c, hoc, hcα, hc⟩ := exists_lt_lt_isSelfVisible hα.isSuccPrelimit (max_lt ho ho₀) (n + 1)
  refine ⟨c, hc, hcα, (le_max_right _ _).trans hoc.le,
    restrictFace_cap hdt fun i ↦ (hto i).trans ?_⟩
  exact_mod_cast (le_max_left o o₀).trans hoc.le

/-- **No determination at a cutoff over a top-free root along the identity**: at a limit stage, if
`t` is top-free and its one-point coface `d` is not, then for every coface `D'` of `t` and every
permitted cutoff `δ`, `d` is not determined over `t` along the identity within the receiving family
of `D'` at `δ`.  Such a `D'` would be `d`, and the cap of `d` at an ordinal at least `δ` and above
the labels of `t` is a top-free member of that family with face `t`. -/
theorem not_isDeterminedWithin_receivingFamily_of_isTopFree (hα : Order.IsSuccLimit α)
    {t : StageType.{u} α n} (ht : t.IsTopFree) {d : StageType.{u} α (n + 1)}
    (hdt : restrictFace Fin.castSuccEmb d = some t) (hd : ¬ d.IsTopFree)
    {D' : StageType.{u} α (n + 1)} (hD' : restrictFace Fin.castSuccEmb D' = some t)
    {δ : Label.{u}} (hδ : IsPermittedCutoff α δ) :
    ¬ IsDeterminedWithin (receivingFamily D' δ) t (Function.Embedding.refl (Fin n)) d := by
  intro hdet
  obtain rfl := eq_of_isDeterminedWithin_refl hdet (self_mem_receivingFamily D' δ) hD'
  obtain ⟨o₀, ho₀, rfl⟩ := isPermittedCutoff_iff.mp hδ
  obtain ⟨c, hc, hcα, hoc, hcap⟩ := exists_cap_restrictFace hα ht hdt ho₀
  have hmem : D'.cap c hc hcα ∈ receivingFamily D' o₀ := by
    refine ⟨rfl, fun i j hij ↦ ?_⟩
    obtain rfl : i = j := Fin.ext hij
    -- the label of the cap at `i` is `min (D'.label i) c` by definition
    change min (min (D'.label i) c) _ = _
    have hoc' : ((o₀ : Ordinal.{u}) : Label.{u}) ≤ (c : Label.{u}) := by exact_mod_cast hoc
    rw [min_assoc, min_eq_right hoc']
  exact hd (eq_of_isDeterminedWithin_refl hdet hmem hcap ▸ isTopFree_cap)

/-- **No determination by a scheme over a top-free root along the identity**: at a limit stage, if
`t` is top-free and its one-point coface `d` is not, then for every coface `D'` of `t`, `d` is not
determined over `t` along the identity within the stage types on the scheme of `D'`.  Such a `D'`
would be `d`, and a cap of `d` above the labels of `t` is a top-free stage type on that scheme with
face `t`. -/
theorem not_isDeterminedWithin_saturationFamily_of_isTopFree (hα : Order.IsSuccLimit α)
    {t : StageType.{u} α n} (ht : t.IsTopFree) {d : StageType.{u} α (n + 1)}
    (hdt : restrictFace Fin.castSuccEmb d = some t) (hd : ¬ d.IsTopFree)
    {D' : StageType.{u} α (n + 1)} (hD' : restrictFace Fin.castSuccEmb D' = some t) :
    ¬ IsDeterminedWithin (saturationFamily D'.toScheme) t (Function.Embedding.refl (Fin n)) d := by
  intro hdet
  obtain rfl := eq_of_isDeterminedWithin_refl hdet rfl hD'
  obtain ⟨c, hc, hcα, -, hcap⟩ := exists_cap_restrictFace hα ht hdt (o₀ := 0) hα.bot_lt
  exact hd (eq_of_isDeterminedWithin_refl (D' := D'.cap c hc hcα) hdet rfl hcap ▸ isTopFree_cap)

end StageType

namespace Realization

variable {M : Type w} {R : Realization.{u, w} α M}

/-- The tuple `u ∘ extendByLast h` is the tuple `c' ∘ h` extended by the last point of `u`, when `u`
extends `c'`. -/
private theorem comp_extendByLast_eq {u : Fin (k + 1) ↪ M} {c' : Fin k → M}
    (hu : ∀ i, u (Fin.castSucc i) = c' i) (h : Fin n ↪ Fin k) :
    ⇑((extendByLast h).trans u) = Fin.snoc (c' ∘ h) (u (Fin.last k)) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp [hu]

/-- **Exact receiving from determination**: if a cover `c'` of `t'` in an exactly consistent
realization realizes a member of `U` over it, and `d` is determined over `t'` along `h` within
`U`, then `d` is the type of `c' ∘ h` extended by one point. -/
theorem exists_covers_snoc_of_isDeterminedWithin (hR : R.IsConsistent) {t' : StageType.{u} α k}
    {c' : Fin k → M} (hc' : R.Covers t' c') {U : Set (StageType.{u} α (k + 1))}
    (hU : R.RealizesOver ⟨c', hc'.injective⟩ U) {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} (hdet : StageType.IsDeterminedWithin U t' h d) :
    ∃ y : M, R.Covers d (Fin.snoc (c' ∘ h) y) := by
  obtain ⟨u, hu, q, hq, he⟩ := hU
  have hu' (i : Fin k) : u (Fin.castSucc i) = c' i := DFunLike.congr_fun hu i
  have hqt : StageType.restrictFace Fin.castSuccEmb q = some t' := by
    rw [← hR u q _ he, hu]
    exact hc'.eval_eq
  have hev := hR u q (extendByLast h) he
  rw [hdet q hq hqt] at hev
  refine ⟨u (Fin.last k), ?_⟩
  rw [← comp_extendByLast_eq hu' h]
  exact covers_of_eval _ hev

/-- **Generalized saturation realizes the scheme of a coface**: over a cover `c'` of `t'` in a
model, some coface of `t'` on the scheme of a given coface `D'` is realized. -/
theorem IsModel.realizesOver_saturationFamily (hR : R.IsModel) {t' : StageType.{u} α k}
    {c' : Fin k → M} (hc' : R.Covers t' c') {D' : StageType.{u} α (k + 1)} (hD' : D' ∈ t'.cofaces) :
    R.RealizesOver ⟨c', hc'.injective⟩ (StageType.saturationFamily D'.toScheme) :=
  hR.saturation ⟨k, ⟨c', hc'.injective⟩, t', hc'.eval_eq⟩ D'.toScheme ⟨D', hD', rfl⟩

/-- **Finite-cut receiving realizes the receiving family of a coface** over a cover. -/
theorem HasFiniteCutReceiving.realizesOver_receivingFamily (hrec : R.HasFiniteCutReceiving)
    {t' : StageType.{u} α k} {c' : Fin k → M} (hc' : R.Covers t' c')
    {D' : StageType.{u} α (k + 1)} (hD' : D' ∈ t'.cofaces) {δ : Label.{u}}
    (hδ : IsPermittedCutoff α δ) :
    R.RealizesOver ⟨c', hc'.injective⟩ (StageType.receivingFamily D' δ) :=
  hrec ⟨k, ⟨c', hc'.injective⟩, t', hc'.eval_eq⟩ D' hD' δ hδ

/-- One-point exact receiving of `D` over `c` from a cover of `D` extending `c`. -/
private theorem covers_snoc_of_covers {c : Fin n → M} {D : StageType.{u} α (n + 1)}
    {u : Fin (n + 1) → M} (hu : R.Covers D u) (huc : u ∘ Fin.castSucc = c) :
    R.Covers D (Fin.snoc c (u (Fin.last n))) := by
  subst huc
  have h : (Fin.snoc (u ∘ Fin.castSucc) (u (Fin.last n)) : Fin (n + 1) → M) = u :=
    Fin.snoc_init_self u
  rwa [h]

/-- **Exact receiving at a rigid root, one point at a time**: in an exactly consistent realization
at a limit stage with finite-cut receiving, a one-point coface of the type of a cover in which the
root is a rigid core is the type of the cover extended by one point.  The one-point case of
`Realization.exists_covers_of_isRigidCoreIn`, with finite-extension receiving from finite-cut
receiving (`Realization.HasFiniteCutReceiving.hasFiniteExtensionReceiving`). -/
theorem exists_covers_snoc_of_isRigidCoreIn (hR : R.IsConsistent) (hα : Order.IsSuccLimit α)
    (hrec : R.HasFiniteCutReceiving) {t : StageType.{u} α n} {c : Fin n → M} (hc : R.Covers t c)
    {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces) (hrig : d.IsRigidCoreIn Fin.castSuccEmb) :
    ∃ y : M, R.Covers d (Fin.snoc c y) := by
  obtain ⟨u, hu, huc⟩ := exists_covers_of_isRigidCoreIn hR hα
    (hrec.hasFiniteExtensionReceiving hR hα.isSuccPrelimit) hc hd.1 hd.2 hrig
  exact ⟨_, covers_snoc_of_covers hu huc⟩

/-! ### Exact reformulations -/

/-- One-point exact receiving of a face-closed family gives exact receiving within it. -/
private theorem exactReceivingWithin_of_snoc (hR : R.IsConsistent)
    {A : ∀ m, Set (StageType.{u} α m)}
    (hA : ∀ ⦃m k : ℕ⦄ (D : StageType.{u} α m) (f : Fin k ↪ Fin m) (p : StageType.{u} α k),
      D ∈ A m → StageType.restrictFace f D = some p → p ∈ A k)
    (h1 : ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
      ∀ D ∈ A (n + 1), StageType.restrictFace Fin.castSuccEmb D = some t →
        ∃ y : M, R.Covers D (Fin.snoc c y)) :
    R.ExactReceivingWithin A :=
  .of_one_point hR hA fun _ t c hc D hD hDt ↦
    let ⟨y, hy⟩ := h1 t c hc D hD hDt
    ⟨Fin.snoc c y, hy, Fin.snoc_comp_castSucc⟩

/-- **(R2) is exact receiving of the legal stage types of top grade at most `K`** in every model at
a limit stage with no cover that is a globally rigid core and with top-grade supremum `K`, on any
number of new points.  An exact reformulation. -/
theorem residualReceiving_iff : ResidualReceiving.{u, w} ↔
    ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄ ⦃K : ℕ⦄,
      Order.IsSuccLimit α → R.IsModel →
      (¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
        R.IsGloballyRigidCore c) →
      R.topGradeSup = K → R.ExactReceivingWithin fun _ ↦ {D | D.IsLegal ∧ D.topGrade ≤ K} := by
  refine ⟨fun h α M R K hα hR hcore hK ↦ exactReceivingWithin_of_snoc hR.isConsistent
    (fun _ _ _ _ _ hD hf ↦ StageType.isLegal_and_topGrade_le_of_restrictFace hD hf)
    fun _ t c hc D hD hDt ↦ h.exists_covers hα hR hcore hK t c hc D ⟨hD.1, hDt⟩ hD.2,
    fun h ↦ ⟨fun α M R K hα hR hcore hK n t c hc D hD hDK ↦ ?_⟩⟩
  obtain ⟨u, hu, huc⟩ := h hα hR hcore hK t c hc D Fin.castSuccEmb ⟨hD.1, hDK⟩ hD.2
  exact ⟨_, covers_snoc_of_covers hu huc⟩

/-- **(R3) is exact receiving of all legal stage types** in every model at a limit stage satisfying
`H` with top-grade supremum `⊤`, on any number of new points.  An exact reformulation. -/
theorem hollowReceiving_iff {H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop} :
    HollowReceiving.{u, w} H ↔
      ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄,
        Order.IsSuccLimit α → R.IsModel → H R → R.topGradeSup = ⊤ →
          R.ExactReceivingWithin fun _ ↦ {D | D.IsLegal} := by
  refine ⟨fun h α M R hα hR hH htop ↦ exactReceivingWithin_of_snoc hR.isConsistent
    (fun _ _ _ f _ hD hf ↦ StageType.IsLegal.restrictFace f hD hf)
    fun _ t c hc D hD hDt ↦ h.exists_covers hα hR hH htop t c hc D ⟨hD, hDt⟩,
    fun h ↦ ⟨fun α M R hα hR hH htop n t c hc D hD ↦ ?_⟩⟩
  obtain ⟨u, hu, huc⟩ := h hα hR hH htop t c hc D Fin.castSuccEmb hD.1 hD.2
  exact ⟨_, covers_snoc_of_covers hu huc⟩

/-! ### (R3) over a rigid core -/

/-- **Under (R3), a globally rigid core is rigid in every legal donor over its type**: in a model
at a limit stage satisfying `H` with top-grade supremum `⊤`, if a cover `c` of `t` is a globally
rigid core, then for every legal `D` restricting to `t` along `g`, the core along `g` is rigid in
`D`.  The donor is received exactly over `c`, and its type is that of a cover containing `c`. -/
theorem HollowReceiving.isRigidCoreIn
    {H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop}
    (hhol : HollowReceiving.{u, w} H) (hα : Order.IsSuccLimit α) (hR : R.IsModel) (hH : H R)
    (htop : R.topGradeSup = ⊤) {t : StageType.{u} α n} {c : Fin n → M} (hc : R.Covers t c)
    (hcore : R.IsGloballyRigidCore c) {D : StageType.{u} α m} {g : Fin n ↪ Fin m}
    (hD : D.IsLegal) (hg : StageType.restrictFace g D = some t) : D.IsRigidCoreIn g := by
  obtain ⟨u, hu, hug⟩ := hollowReceiving_iff.mp hhol hα hR hH htop t c hc D g hD hg
  exact hcore D u g hu hug

/-- **(R3) is antitone in the predicate**: (R3) for `H` gives (R3) for every stronger predicate,
for instance `H` together with the absence of a globally rigid core
(`Realization.HollowReceiving.withoutRigidCore`). -/
theorem HollowReceiving.mono
    {H H' : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop}
    (hhol : HollowReceiving.{u, w} H)
    (hH : ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄, H' R → H R) :
    HollowReceiving.{u, w} H' where
  exists_covers _ _ _ hα hR hH' htop := hhol.exists_covers hα hR (hH hH') htop

/-! ### The rigid part from (R1) -/

/-- **(R2) from (R1) and the non-rigid cofaces**: if every model at every limit stage has
finite-cut receiving, then (R2) follows from its restriction to the cofaces in which the root is
not a rigid core.  The receiving hypothesis ranges over every limit stage at fixed universe levels
and is not supplied by the countable-stage `Expansion.FiniteCutReceiving`. -/
theorem ResidualReceiving.of_not_isRigidCoreIn
    (hrec : ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄,
      Order.IsSuccLimit α → R.IsModel → R.HasFiniteCutReceiving)
    (h : ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄ ⦃K : ℕ⦄,
      Order.IsSuccLimit α → R.IsModel →
      (¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
        R.IsGloballyRigidCore c) →
      R.topGradeSup = K → ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
        ∀ D ∈ t.cofaces, D.topGrade ≤ K → ¬ D.IsRigidCoreIn Fin.castSuccEmb →
          ∃ y : M, R.Covers D (Fin.snoc c y)) :
    ResidualReceiving.{u, w} where
  exists_covers α M R K hα hR hcore hK n t c hc D hD hDK := by
    by_cases hrig : D.IsRigidCoreIn Fin.castSuccEmb
    · exact exists_covers_snoc_of_isRigidCoreIn hR.isConsistent hα (hrec hα hR) hc hD hrig
    · exact h hα hR hcore hK t c hc D hD hDK hrig

/-- **(R3) from (R1) and the non-rigid cofaces**: if every model at every limit stage has
finite-cut receiving, then (R3) follows from its restriction to the cofaces in which the root is
not a rigid core.  The receiving hypothesis ranges over every limit stage at fixed universe levels
and is not supplied by the countable-stage `Expansion.FiniteCutReceiving`. -/
theorem HollowReceiving.of_not_isRigidCoreIn
    {H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop}
    (hrec : ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄,
      Order.IsSuccLimit α → R.IsModel → R.HasFiniteCutReceiving)
    (h : ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄,
      Order.IsSuccLimit α → R.IsModel → H R → R.topGradeSup = ⊤ →
        ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
          ∀ D ∈ t.cofaces, ¬ D.IsRigidCoreIn Fin.castSuccEmb →
            ∃ y : M, R.Covers D (Fin.snoc c y)) :
    HollowReceiving.{u, w} H where
  exists_covers α M R hα hR hH htop n t c hc D hD := by
    by_cases hrig : D.IsRigidCoreIn Fin.castSuccEmb
    · exact exists_covers_snoc_of_isRigidCoreIn hR.isConsistent hα (hrec hα hR) hc hD hrig
    · exact h hα hR hH htop t c hc D hD hrig

/-! ### Acquisition and determination -/

/-- **Residual acquisition** for a predicate `P` on acquired contexts (depending on the eventual
top grade `K`): in every model at a limit stage with no cover that is a globally rigid core and
with top-grade supremum `K`, every cover `c` extends to a cover `c'` of some `t'` along some `h`
(`c' ∘ h = c`) with `P K t' h`.  A statement about models; not proved for any `P` here. -/
structure ResidualAcquisition
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop) :
    Prop where
  /-- Every cover extends to a cover of an acquired context. -/
  exists_context ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄ ⦃K : ℕ⦄ :
    Order.IsSuccLimit α → R.IsModel →
      (¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
        R.IsGloballyRigidCore c) →
      R.topGradeSup = K → ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
        ∃ (k : ℕ) (t' : StageType.{u} α k) (c' : Fin k → M) (h : Fin n ↪ Fin k),
          R.Covers t' c' ∧ c' ∘ h = c ∧ P K t' h

/-- **Cutoff determination** for `P`, a statement about stage types: at a limit stage, over every
legal `t'` with `P K t' h`, every one-point coface `d` of top grade at most `K` of the face of `t'`
along `h` is determined over `t'` along `h` within the receiving family, at a permitted cutoff, of
some coface of `t'`.  Not proved for any `P` here. -/
structure CutoffDetermination
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop) :
    Prop where
  /-- Every coface of the face is determined at a cutoff. -/
  exists_coface ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) :
    Order.IsSuccLimit α → t'.IsLegal → P K t' h → ∀ t : StageType.{u} α n,
      StageType.restrictFace h t' = some t → ∀ d ∈ t.cofaces, d.topGrade ≤ K →
        ∃ D' ∈ t'.cofaces, ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
          StageType.IsDeterminedWithin (StageType.receivingFamily D' δ) t' h d

/-- **Hollow acquisition** for a predicate `P` on acquired contexts: in every model at a limit
stage satisfying `H` with top-grade supremum `⊤`, every cover `c` extends to a cover `c'` of some
`t'` along some `h` (`c' ∘ h = c`) with `P t' h`.  A statement about models; not proved for any
`P` here. -/
structure HollowAcquisition (H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop)
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop) : Prop where
  /-- Every cover extends to a cover of an acquired context. -/
  exists_context ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄ :
    Order.IsSuccLimit α → R.IsModel → H R → R.topGradeSup = ⊤ →
      ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
        ∃ (k : ℕ) (t' : StageType.{u} α k) (c' : Fin k → M) (h : Fin n ↪ Fin k),
          R.Covers t' c' ∧ c' ∘ h = c ∧ P t' h

/-- **Scheme determination** for `P`, a statement about stage types: at a limit stage, over every
legal `t'` with `P t' h`, every one-point coface `d` of the face of `t'` along `h` is determined
over `t'` along `h` within the stage types on the scheme of some coface of `t'`.  Not proved for
any `P` here. -/
structure SchemeDetermination
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop) : Prop where
  /-- Every coface of the face is determined by a scheme. -/
  exists_coface ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) :
    Order.IsSuccLimit α → t'.IsLegal → P t' h → ∀ t : StageType.{u} α n,
      StageType.restrictFace h t' = some t → ∀ d ∈ t.cofaces,
        ∃ D' ∈ t'.cofaces,
          StageType.IsDeterminedWithin (StageType.saturationFamily D'.toScheme) t' h d

/-- The face of an acquired context along `h` is the type of the original cover. -/
private theorem restrictFace_of_covers (hR : R.IsConsistent) {t : StageType.{u} α n}
    {c : Fin n → M} (hc : R.Covers t c) {t' : StageType.{u} α k} {c' : Fin k → M}
    (hc' : R.Covers t' c') {h : Fin n ↪ Fin k} (hcc' : c' ∘ h = c) :
    StageType.restrictFace h t' = some t := by
  rw [← hR ⟨c', hc'.injective⟩ t' h hc'.eval_eq, ← hc.eval_eq]
  congr 1
  ext i
  exact congrFun hcc' i

/-- **(R2) from (R1), residual acquisition, and cutoff determination**, for any predicate `P` on
acquired contexts.  (R1) is assumed for every model at every limit stage: the receiving
hypothesis ranges over every limit stage at fixed universe levels and is not supplied by the
countable-stage `Expansion.FiniteCutReceiving`.  No `P` is defined in this file; this is a
template. -/
theorem residualReceiving_of_cutoffDetermination
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop}
    (hrec : ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄,
      Order.IsSuccLimit α → R.IsModel → R.HasFiniteCutReceiving)
    (hacq : ResidualAcquisition.{u, w} P) (hdet : CutoffDetermination.{u} P) :
    ResidualReceiving.{u, w} where
  exists_covers α M R K hα hR hcore hK n t c hc d hd hdK := by
    obtain ⟨k, t', c', h, hc', hcc', hP⟩ := hacq.exists_context hα hR hcore hK t c hc
    obtain ⟨D', hD', δ, hδ, hdet'⟩ := hdet.exists_coface t' h hα (hR.isLegal _ _ hc'.eval_eq) hP
      t (restrictFace_of_covers hR.isConsistent hc hc' hcc') d hd hdK
    rw [← hcc']
    exact exists_covers_snoc_of_isDeterminedWithin hR.isConsistent hc'
      ((hrec hα hR).realizesOver_receivingFamily hc' hD' hδ) hdet'

/-- **(R3) from hollow acquisition and scheme determination**, for any predicate `P` on acquired
contexts.  No receiving is used: the coface is realized by generalized saturation. -/
theorem hollowReceiving_of_schemeDetermination
    {H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop}
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop}
    (hacq : HollowAcquisition.{u, w} H P) (hdet : SchemeDetermination.{u} P) :
    HollowReceiving.{u, w} H where
  exists_covers α M R hα hR hH htop n t c hc d hd := by
    obtain ⟨k, t', c', h, hc', hcc', hP⟩ := hacq.exists_context hα hR hH htop t c hc
    obtain ⟨D', hD', hdet'⟩ := hdet.exists_coface t' h hα (hR.isLegal _ _ hc'.eval_eq) hP t
      (restrictFace_of_covers hR.isConsistent hc hc' hcc') d hd
    rw [← hcc']
    exact exists_covers_snoc_of_isDeterminedWithin hR.isConsistent hc'
      (hR.realizesOver_saturationFamily hc' hD') hdet'

end Realization

end VaughtConjecture
