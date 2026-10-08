/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Age

/-!
# Reconstruction of partial evaluation from a classical limit of the age of top-free charts

Roadmap, the section "The top-free witnesses: the finite age and its classical limit", step 4
(reconstruction of partial evaluation) and the parts of step 5 proved from the factorization of one
tuple (exact consistency, covering, top-freeness, a nonempty carrier); semantic contract, item 11
(literal recovery of chart relations, uniqueness and injectivity of labelled tuples, exact partial
restriction, covering, and the literal roundtrip in both directions, for the operations
`Realization.hullOp`).

**The reconstructed realization.**  Let `M` be a structure of the hull language `hullLanguage α`.
Its **reconstructed realization** `reconstruct α M` gives an injective tuple `t` of `M` a stage type
`p` at which the chart relation of `p` holds at `t`, if there is one, and no type otherwise.  The
relation symbols are the legal stage types, so the types read off are legal
(`hasLegalTypes_reconstruct`).  The definition makes a choice; the choice does not matter when at
most one chart relation holds at each tuple, which is the case below.

**One chart through which a tuple factors.**  The basic computation needs no hypothesis on `M`:
if `e` embeds the chart of a legal stage type `Q` in `M`, the reconstructed evaluation of the
image under `e` of a tuple `b` of points of `Q` is the evaluation of `b` in the face realization of
`Q` (`reconstruct_eval_trans_chart`): the type of the face `b` spans when it is closed, and no type
when it is not.  An embedding preserves and reflects the chart relations, and in the chart of `Q`
the relation of `p` holds at `b` exactly when the face map of `Q` along `b` returns `p`
(`StageType.relMap_chart`).  On the chart of a legal stage type, reconstruction therefore returns
its face realization (`reconstruct_chart`, `reconstruct_chart_eval`).

**Legal chart coverage.**  Under `hage : (hullLanguage α).age M ⊆ legalAge α`, every injective
tuple of `M` is the image of a tuple of points of a legal chart under an embedding of the chart
(`exists_eq_trans_legalChart`), and the reconstructed realization is exactly consistent and
covering, a typed tuple being the image of the points of its type under an embedding of its chart
(`isConsistent_reconstruct_of_legalAge`, `isCovering_reconstruct_of_legalAge`,
`exists_embedding_of_reconstruct_eval_of_legalAge`).  The age of top-free charts is contained in
the age of legal charts (`topFreeAge_subset_legalAge`), so the corresponding statements under
top-free chart coverage below are their case.

**Top-free chart coverage.**  The hypothesis of the statements in the section of that name is
`hage : (hullLanguage α).age M ⊆ topFreeAge α`: every finitely generated substructure of `M` is
isomorphic to a *top-free* chart.  This is stricter than the local chart coverage of
`HULL_ALGEBRA.md`, §5 (every finite tuple in a finitely generated substructure isomorphic to the
structure of a chart, top-free or not), so the roundtrip (b) is proved here for the age of top-free
charts only.  It is one inclusion of the equality of ages `(hullLanguage α).age M = topFreeAge α`;
a Fraïssé limit of the age (`IsFraisseLimit`) is ultrahomogeneous with that age.  The converse
inclusion is used here only for a nonempty carrier, and ultrahomogeneity is not used.
Under `hage`, every finite tuple of `M`, injective or not, factors literally through an embedding
of a top-free chart (`exists_eq_trans_topFreeChart`, `exists_comp_eq_topFreeChart`, from
`FirstOrder.Language.exists_factor_embedding_of_age_subset` and
`FirstOrder.Language.exists_factor_tuple_of_age_subset`), and each statement below is a statement
about one tuple, read in the face realization of the chart through which it factors:

* **every reconstructed type is in the age** (`mem_topFreeAge_of_reconstruct_eval`), roadmap,
  milestone 5, in its literal form;
* **literal recovery of chart relations** (`reconstruct_eval_eq_some_iff`,
  `relMap_rel_iff_reconstruct_eval`): the relation of `p` holds at a tuple exactly when the tuple is
  injective and its reconstructed evaluation is `p`;
* **uniqueness and injectivity of labelled tuples** (`eq_of_relMap_rel`, `injective_of_relMap_rel`):
  at most one chart relation holds at a tuple, and a tuple at which one holds is injective.  The
  uniqueness used is that of the face map of one stage type along one tuple of its points, an
  equation in `Option`; the two-charts theorem is not used for it;
* **exact partial restriction** (`isConsistent_reconstruct`), by the guarded composition law of
  face maps in the chart, with `none` at an invisible face;
* **covering** (`isCovering_reconstruct`), and for arbitrary tuples, the empty tuple and repeated
  coordinates included (`exists_comp_eq_reconstruct_eval`);
* **top-free types** (`isTopFree_of_reconstruct_eval`): a reconstructed type is a face of a
  top-free stage type;
* **typed tuples are charts** (`reconstruct_eval_eq_some_iff_exists_embedding`): a tuple has the
  type `p` exactly when `p` is legal and top-free and the tuple is the image of the points of `p`,
  in order, under an embedding of the chart of `p`; and a tuple is typed exactly when the set of
  its points is closed under the hull operations, so that it is the substructure it generates
  (`isSome_reconstruct_eval_iff`).  A tuple whose points do not form a substructure, such as a
  pair whose hull has more points, has no type.

**The roundtrip.**  (a) Reconstructing the structure of a realization with legal types in the
hull language (`Realization.toHullStructure`) returns the realization
(`reconstruct_toHullStructure`).  (b) Under `hage`, the hull operations of `M` are the hull
operations of its reconstructed realization (`funMap_op_eq_hullOp`), and the structure of `M` is
the structure of its reconstructed realization in the hull language
(`toHullStructure_reconstruct`), relations and functions both: this is `HULL_ALGEBRA.md`, §5, (b),
for structures with top-free chart coverage.  Where a chart witness exists the
value is its target point, by the two-charts theorem in the chart through which the witness
factors (`StageType.hullOp_eq_of_restrictFace`); the realization-level two-charts theorem for the
reconstructed realization follows (`eq_of_reconstruct_eval_eq_some`), from the chart-level one in
a chart through which both witnesses factor.  Where no chart witness exists in `M`, none exists in
the chart through which the two arguments factor either, since the image of a witness there is a
witness in `M`; so both operations take the default value, the first argument, as at repeated
inputs.

**Stage reduction.**  For a realization `R` with legal types and a stage `β` that is zero or a
limit, reconstructing at `β` the structure in the hull language of the stage reduction
`R.reduce hβ` returns `R.reduce hβ` (`reconstruct_reduce_toHullStructure`), on the same carrier
and with the same untyped tuples; for `R = reconstruct α M` no hypothesis on `M` is needed
(`reconstruct_reduce_toHullStructure_reconstruct`).  This is the roundtrip (a) at `β`, the types
of the reduction being legal by `StageType.IsLegal.reduce`.

The operations identified here are `Realization.hullOp`, defined by a choice of chart witness;
that they are the operations defined by a first-order formula of the stage chart language
(roadmap, Layer 2, item 2) is not used and not proved here.

**For a Fraïssé limit** (`reconstruct_of_isFraisseLimit`, from the equality of ages alone in
`reconstruct_of_age_eq`).  If `M` is a Fraïssé limit of the age of top-free charts, its carrier is
nonempty (`nonempty_of_topFreeAge_subset`, the one-point chart being in its age), its
reconstructed realization is exactly consistent and covering with legal top-free types, and the
structure of `M` is that of the reconstructed realization.  The limit is a
hypothesis, not constructed: its existence (`exists_isFraisseLimit_topFreeAge`) depends on the
coatom extension property `StageType.HasCoatomExtensions α`, which is not proved, and on the
hypotheses on the stage `α` stated there; none of these enters this file.

**What this file does not contain.**  Each item names the hypotheses it will need beyond those
used here.

* **Receiving** (step 6), `(reconstruct α M).HasFiniteCutReceiving`, is in
  `VaughtConjecture.ClassicalLimit.Receiving` (`hasFiniteCutReceiving_reconstruct`), for a
  structure whose age is the age of top-free charts and which is ultrahomogeneous, at a stage that
  is zero or a limit: the donor capped at an ordinal below the stage (`StageType.cap`) is a legal
  top-free coface of the root's type, realized over the occurrence by ultrahomogeneity
  (`FirstOrder.Language.IsUltrahomogeneous.extend_embedding`, applied to the embedding of the
  chart of the root's type given by `reconstruct_eval_eq_some_iff_exists_embedding`).
* **Modelhood** (step 7), `Realization.IsModel`: for a structure whose age is the age of top-free
  charts, its clauses of a nonempty carrier, legal types, exact consistency, and covering are
  proved here (`reconstruct_of_age_eq`); its four extension clauses (generalized saturation, the
  bottom pattern, uniformity, and high-arity dominance) are in
  `VaughtConjecture.ClassicalLimit.Modelhood` (`isModel_reconstruct`), at a nonzero limit stage,
  from receiving and the cap-to-model theorem (`Realization.isModel_of_hasFiniteCutReceiving`),
  given the nonemptiness of the uniformity and dominance instances.
* **Infinitude and terminality** (step 7) are in `VaughtConjecture.ClassicalLimit.Modelhood`:
  infinitude from receiving over a whole occurrence, with a one-point coface of its type
  (`infinite_of_age_eq_of_hasCoatomExtensions`, under the coatom extension property), and
  terminality from the top-freeness proved here and the uniformity clause of a model at a higher
  stage (`reduce_ne_reconstruct`).
* **The density sentence** (the sentence of the main theorem; for the base reduct, the
  base-reduct part of step 7) for the base-language structure (`Realization.toStructure`) of the
  reduction of the reconstructed realization to `ω` (`Realization.reduce`) is in
  `VaughtConjecture.ClassicalLimit.Receiving` (`realize_densitySentence_reconstruct_reduce`), for
  a structure whose age is the age of top-free charts and which is ultrahomogeneous, at a limit
  stage `α ≥ ω`: the clauses proved here, reduced to `ω`, and finite-cut receiving of the
  reduction, by receiving at `α` and its descent along stage reduction
  (`Realization.HasFiniteCutReceiving.reduce`), cutoff by cutoff, which is not exact projected
  receiving (semantic contract, item 12).
* **Exact extension within the age** (semantic contract, item 12): exact extension of top-free
  donors, by ultrahomogeneity, is in `VaughtConjecture.ClassicalLimit.Receiving`
  (`exists_reconstruct_eval_eq_of_isTopFree`), with the statements there about the reduction of
  the reconstructed realization to a lower stage and its cutoff observations.

**Universes.**  The limit is a structure in `Type` of a language in `Type (u + 1)`; the output of
reconstruction is the realization `reconstruct α M`, on the same carrier in `Type`.  With `u = 0`,
the base-language structure in `Type` that the spectrum statements take is that of its reduction to
`ω`; the structure of `M` in the hull language is not.

## Placement

This file belongs to the section on the top-free witnesses of `roadmap/README.md`.

## References

Realizations, exact consistency, covering, and models are [Kni26, Definition 3.2.1].
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Finset
open scoped Ordinal

/-! ### The reconstructed realization -/

section Reconstruct

variable (α : Ordinal.{u}) (M : Type v) [(hullLanguage.{u} α).Structure M]

open Classical in
/-- The **reconstructed realization** of a structure of the hull language (roadmap, the top-free
witnesses, step 4): an injective tuple has a stage type at which its chart relation holds, if there
is one, and no type otherwise. -/
noncomputable def reconstruct : Realization.{u, v} α M where
  eval {n} t := if h : ∃ (p : StageType.{u} α n) (hp : p.IsLegal),
      RelMap (hullLanguage.rel p hp) t then some h.choose else none

variable {α M} {n k : ℕ}

open Classical in
/-- The reconstructed evaluation, unfolded. -/
theorem reconstruct_eval (t : Fin n ↪ M) :
    (reconstruct α M).eval t = if h : ∃ (p : StageType.{u} α n) (hp : p.IsLegal),
      RelMap (hullLanguage.rel p hp) t then some h.choose else none :=
  rfl

/-- A reconstructed type is a stage type whose chart relation holds at the tuple. -/
theorem exists_relMap_of_reconstruct_eval_eq_some {t : Fin n ↪ M} {p : StageType.{u} α n}
    (h : (reconstruct α M).eval t = some p) :
    ∃ hp : p.IsLegal, RelMap (hullLanguage.rel p hp) t := by
  rw [reconstruct_eval] at h
  split_ifs at h with hex
  obtain rfl := Option.some_injective _ h
  exact hex.choose_spec

/-- **The reconstructed types are legal**: they index chart relations. -/
theorem hasLegalTypes_reconstruct : (reconstruct α M).HasLegalTypes := fun _ _ _ h ↦
  (exists_relMap_of_reconstruct_eval_eq_some h).1

/-- A tuple has no reconstructed type exactly when no chart relation holds at it. -/
theorem reconstruct_eval_eq_none_iff {t : Fin n ↪ M} :
    (reconstruct α M).eval t = none ↔
      ∀ (p : StageType.{u} α n) (hp : p.IsLegal), ¬ RelMap (hullLanguage.rel p hp) t := by
  rw [reconstruct_eval]
  split_ifs with hex
  · simp only [false_iff, not_forall, not_not]
    exact hex
  · simp only [true_iff]
    exact fun p hp h ↦ hex ⟨p, hp, h⟩

/-- If the chart relation of `p` holds at a tuple and no other chart relation does, the
reconstructed type of the tuple is `p`. -/
theorem reconstruct_eval_eq_some_of_relMap {t : Fin n ↪ M} {p : StageType.{u} α n}
    (hp : p.IsLegal) (h : RelMap (hullLanguage.rel p hp) t)
    (huniq : ∀ (q : StageType.{u} α n) (hq : q.IsLegal), RelMap (hullLanguage.rel q hq) t → q = p) :
    (reconstruct α M).eval t = some p := by
  have hex : ∃ (p : StageType.{u} α n) (hp : p.IsLegal), RelMap (hullLanguage.rel p hp) t :=
    ⟨p, hp, h⟩
  rw [reconstruct_eval, dite_eq_left hex]
  obtain ⟨hq, hr⟩ := hex.choose_spec
  exact congrArg some (huniq _ hq hr)

/-! ### Tuples through one chart -/

variable {Q : StageType.{u} α k}

/-- Along an embedding of the chart of `Q`, the chart relation of `p` holds at the image of a tuple
`b` of points of `Q` exactly when the face map of `Q` along `b` returns `p`. -/
theorem relMap_trans_chart_iff (e : Q.Chart ↪[hullLanguage.{u} α] M) (b : Fin n ↪ Fin k)
    {p : StageType.{u} α n} (hp : p.IsLegal) :
    RelMap (hullLanguage.rel p hp) (b.trans (Q.toChart.toEmbedding.trans e.toEmbedding)) ↔
      StageType.restrictFace b Q = some p :=
  (e.map_rel (hullLanguage.rel p hp) (Q.toChart ∘ b)).trans (StageType.relMap_chart Q p hp b)

/-- **Reconstruction through one chart**: along an embedding of the chart of a legal stage type
`Q`, the reconstructed evaluation of the image of a tuple `b` of points of `Q` is the evaluation of
`b` in the face realization of `Q`, the type of the face `b` spans, and no type when that face is
not closed.  No hypothesis on `M` is needed. -/
theorem reconstruct_eval_trans_chart (hQ : Q.IsLegal) (e : Q.Chart ↪[hullLanguage.{u} α] M)
    (b : Fin n ↪ Fin k) :
    (reconstruct α M).eval (b.trans (Q.toChart.toEmbedding.trans e.toEmbedding)) =
      Q.faceRealization.eval b := by
  rw [StageType.faceRealization_eval]
  cases hb : StageType.restrictFace b Q with
  | none =>
    refine reconstruct_eval_eq_none_iff.mpr fun p hp h ↦ ?_
    rw [relMap_trans_chart_iff e b hp, hb] at h
    exact Option.some_ne_none p h.symm
  | some q =>
    exact reconstruct_eval_eq_some_of_relMap (hQ.restrictFace b hb)
      ((relMap_trans_chart_iff e b _).mpr hb)
      fun p hp h ↦ Option.some_injective _ (((relMap_trans_chart_iff e b hp).mp h).symm.trans hb)

/-- Along an embedding of the chart of a legal stage type `Q`, the points of `Q`, in order, have
the type `Q`. -/
theorem reconstruct_eval_chart (hQ : Q.IsLegal) (e : Q.Chart ↪[hullLanguage.{u} α] M) :
    (reconstruct α M).eval (Q.toChart.toEmbedding.trans e.toEmbedding) = some Q := by
  have h := reconstruct_eval_trans_chart hQ e (Function.Embedding.refl _)
  rwa [Function.Embedding.refl_trans, StageType.faceRealization_eval,
    StageType.restrictFace_refl] at h

/-- The value of a hull operation of `M` at the images of two points of a chart under an embedding
is the image of its value in the chart. -/
theorem funMap_op_trans_chart (e : Q.Chart ↪[hullLanguage.{u} α] M) (ι : HullIndex.{u} α)
    (x y : Fin k) :
    funMap (hullLanguage.op ι) ![e (Q.toChart x), e (Q.toChart y)] =
      e (Q.toChart (Q.faceRealization.hullOp ι x y)) := by
  rw [← StageType.funMap_chart, Embedding.map_fun]
  exact congrArg _ (funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩))

end Reconstruct

/-! ### The roundtrip from a realization -/

/-- **The roundtrip from a realization** (`HULL_ALGEBRA.md`, §5, (a)): reconstructing the structure
of a realization with legal types in the hull language returns the realization. -/
theorem reconstruct_toHullStructure {α : Ordinal.{u}} {M : Type v} (R : Realization.{u, v} α M)
    (hR : R.HasLegalTypes) : @reconstruct α M R.toHullStructure = R := by
  let _ : (hullLanguage.{u} α).Structure M := R.toHullStructure
  refine Realization.ext fun {n} t ↦ ?_
  cases ht : R.eval t with
  | none =>
    refine reconstruct_eval_eq_none_iff.mpr fun p hp hr ↦ ?_
    obtain ⟨_, h⟩ := (R.relMap_toHullStructure p hp t).mp hr
    exact Option.some_ne_none p (h.symm.trans ht)
  | some p =>
    refine reconstruct_eval_eq_some_of_relMap (hR t p ht)
      ((R.relMap_toHullStructure p _ t).mpr ⟨t.injective, ht⟩) fun q hq hr ↦ ?_
    obtain ⟨_, h⟩ := (R.relMap_toHullStructure q hq t).mp hr
    exact Option.some_injective _ (h.symm.trans ht)

/-- **Reconstruction on a chart**: on the chart of a legal stage type, the reconstructed
realization is its face realization. -/
theorem reconstruct_chart {α : Ordinal.{u}} {k : ℕ} {P : StageType.{u} α k} (hP : P.IsLegal) :
    reconstruct α P.Chart = P.faceRealization :=
  reconstruct_toHullStructure P.faceRealization (StageType.hasLegalTypes_faceRealization hP)

/-- On the chart of a legal stage type, the reconstructed evaluation of a tuple of points is the
face map of the stage type along it. -/
theorem reconstruct_chart_eval {α : Ordinal.{u}} {k n : ℕ} {P : StageType.{u} α k}
    (hP : P.IsLegal) (t : Fin n ↪ Fin k) :
    (reconstruct α P.Chart).eval (t.trans P.toChart.toEmbedding) = StageType.restrictFace t P :=
  reconstruct_eval_trans_chart hP (Embedding.refl (hullLanguage.{u} α) P.Chart) t

/-! ### Stage reduction -/

/-- **Reconstruction commutes with stage reduction**: for a realization `R` with legal types at a
stage `α` and a stage `β` that is zero or a limit, reconstructing at `β` the structure in the hull
language of the stage reduction `R.reduce hβ` returns `R.reduce hβ`, on the same carrier and with
the same untyped tuples (`none` faces included).  The types of the reduction are legal
(`Realization.HasLegalTypes.reduce`, by `StageType.IsLegal.reduce`), so this is the roundtrip (a)
(`reconstruct_toHullStructure`) at `β`; no relation between `β` and `α` is needed.

This is the algebraic equality only.  Modelhood transfers separately, by
`Realization.IsModel.reduce` (which needs in addition that `α` is zero or a limit and that `β` is a
limit with `β ≤ α`); countability enters only when the sentence at the lower stage is formed. -/
theorem reconstruct_reduce_toHullStructure {α β : Ordinal.{u}} {M : Type v}
    (R : Realization.{u, v} α M) (hR : R.HasLegalTypes) (hβ : Order.IsSuccPrelimit β) :
    @reconstruct β M (R.reduce hβ).toHullStructure = R.reduce hβ :=
  reconstruct_toHullStructure _ (hR.reduce hβ)

/-- **Reconstruction commutes with stage reduction, for a reconstructed realization**: for a
structure `M` of the hull language at `α` and a stage `β` that is zero or a limit, reconstructing
at `β` the structure in the hull language of the stage reduction of `reconstruct α M` returns that
stage reduction.  No hypothesis on `M` is needed, since reconstructed types are legal
(`hasLegalTypes_reconstruct`). -/
theorem reconstruct_reduce_toHullStructure_reconstruct {α β : Ordinal.{u}} {M : Type v}
    [(hullLanguage.{u} α).Structure M] (hβ : Order.IsSuccPrelimit β) :
    @reconstruct β M ((reconstruct α M).reduce hβ).toHullStructure = (reconstruct α M).reduce hβ :=
  reconstruct_reduce_toHullStructure _ hasLegalTypes_reconstruct hβ

/-- After stage reduction and reconstruction, a tuple untyped in `R` is still untyped, and a typed
tuple carries the reduction of its type. -/
example {α β : Ordinal.{u}} {M : Type v} {n : ℕ} (R : Realization.{u, v} α M)
    (hR : R.HasLegalTypes) (hβ : Order.IsSuccPrelimit β) (t : Fin n ↪ M) :
    (@reconstruct β M (R.reduce hβ).toHullStructure).eval t =
      (R.eval t).map (StageType.reduce · hβ) := by
  rw [reconstruct_reduce_toHullStructure R hR hβ, Realization.reduce_eval]

/-! ### Legal chart coverage -/

section LegalAge

variable {α : Ordinal.{u}} {M : Type} [(hullLanguage.{u} α).Structure M] {n : ℕ}
  (hage : (hullLanguage.{u} α).age M ⊆ legalAge α)
include hage

/-- **Factorization of an injective tuple** through a legal chart, under legal chart coverage. -/
theorem exists_eq_trans_legalChart (t : Fin n ↪ M) :
    ∃ (i : LegalIndex.{u} α) (e : i.2.1.Chart ↪[hullLanguage.{u} α] M) (b : Fin n ↪ Fin i.1),
      b.trans (i.2.1.toChart.toEmbedding.trans e.toEmbedding) = t := by
  obtain ⟨i, e, b, hb⟩ := exists_factor_embedding_of_age_subset hage t
  exact ⟨i, e, b, hb⟩

/-- **Exact consistency** of the reconstructed realization, under legal chart coverage. -/
theorem isConsistent_reconstruct_of_legalAge : (reconstruct α M).IsConsistent := by
  intro m n t p f ht
  obtain ⟨i, e, b, rfl⟩ := exists_eq_trans_legalChart hage t
  rw [reconstruct_eval_trans_chart i.2.2 e b, StageType.faceRealization_eval] at ht
  rw [← Function.Embedding.trans_assoc, reconstruct_eval_trans_chart i.2.2 e (f.trans b),
    StageType.faceRealization_eval]
  exact (StageType.restrictFace_trans _ b f ht).symm

/-- **Covering** of the reconstructed realization, under legal chart coverage. -/
theorem isCovering_reconstruct_of_legalAge : (reconstruct α M).IsCovering := by
  intro n t
  obtain ⟨i, e, b, rfl⟩ := exists_eq_trans_legalChart hage t
  refine ⟨i.1, i.2.1.toChart.toEmbedding.trans e.toEmbedding, b, rfl, ?_⟩
  rw [reconstruct_eval_chart i.2.2 e]
  rfl

/-- **Typed tuples are images of charts**, under legal chart coverage: a tuple of reconstructed type
`p` is the image of the points of `p`, in order, under an embedding of the chart of `p`. -/
theorem exists_embedding_of_reconstruct_eval_of_legalAge {t : Fin n ↪ M} {p : StageType.{u} α n}
    (h : (reconstruct α M).eval t = some p) :
    ∃ φ : p.Chart ↪[hullLanguage.{u} α] M, ∀ j, φ (p.toChart j) = t j := by
  obtain ⟨i, e, b, rfl⟩ := exists_eq_trans_legalChart hage t
  rw [reconstruct_eval_trans_chart i.2.2 e b, StageType.faceRealization_eval] at h
  exact ⟨e.comp (StageType.chartEmbedding h), fun _ ↦ rfl⟩

end LegalAge

/-! ### Top-free chart coverage -/

section Age

variable {α : Ordinal.{u}} {M : Type} [(hullLanguage.{u} α).Structure M] {n : ℕ}
  (hage : (hullLanguage.{u} α).age M ⊆ topFreeAge α)
include hage

/-- **Factorization of an injective tuple** through a top-free chart: under top-free chart coverage,
every injective tuple of `M` is the image of a tuple of points of a top-free chart under an
embedding of the chart. -/
theorem exists_eq_trans_topFreeChart (t : Fin n ↪ M) :
    ∃ (i : TopFreeIndex.{u} α) (e : i.2.1.Chart ↪[hullLanguage.{u} α] M) (b : Fin n ↪ Fin i.1),
      b.trans (i.2.1.toChart.toEmbedding.trans e.toEmbedding) = t := by
  obtain ⟨i, e, b, hb⟩ := exists_factor_embedding_of_age_subset hage t
  exact ⟨i, e, b, hb⟩

/-- **Factorization of a tuple** through a top-free chart, repeated coordinates allowed: under
top-free chart coverage, every tuple of `M` is the image of a tuple of points of a top-free chart
under an embedding of the chart. -/
theorem exists_comp_eq_topFreeChart (a : Fin n → M) :
    ∃ (i : TopFreeIndex.{u} α) (e : i.2.1.Chart ↪[hullLanguage.{u} α] M) (b : Fin n → Fin i.1),
      (i.2.1.toChart.toEmbedding.trans e.toEmbedding) ∘ b = a := by
  obtain ⟨i, e, b, hb⟩ := exists_factor_tuple_of_age_subset hage a
  exact ⟨i, e, b, hb⟩

/-- **Literal recovery of chart relations** (semantic contract, item 11), for injective tuples:
under top-free chart coverage, an injective tuple has the reconstructed type `p` exactly when the
chart relation of `p` holds at it. -/
theorem reconstruct_eval_eq_some_iff (t : Fin n ↪ M) (p : StageType.{u} α n) :
    (reconstruct α M).eval t = some p ↔ ∃ hp : p.IsLegal, RelMap (hullLanguage.rel p hp) t := by
  refine ⟨exists_relMap_of_reconstruct_eval_eq_some, fun ⟨hp, h⟩ ↦ ?_⟩
  obtain ⟨i, e, b, rfl⟩ := exists_eq_trans_topFreeChart hage t
  rw [reconstruct_eval_trans_chart i.2.2.1 e b, StageType.faceRealization_eval]
  exact (relMap_trans_chart_iff e b hp).mp h

/-- **Literal recovery of chart relations and injectivity of labelled tuples** (semantic contract,
item 11): under top-free chart coverage, the chart relation of `p` holds at a tuple exactly when the
tuple is injective and its reconstructed type is `p`. -/
theorem relMap_rel_iff_reconstruct_eval (xs : Fin n → M) {p : StageType.{u} α n}
    (hp : p.IsLegal) :
    RelMap (hullLanguage.rel p hp) xs ↔
      ∃ h : Function.Injective xs, (reconstruct α M).eval ⟨xs, h⟩ = some p := by
  refine ⟨fun hr ↦ ?_, fun ⟨h, he⟩ ↦ (exists_relMap_of_reconstruct_eval_eq_some he).2⟩
  have hinj : Function.Injective xs := by
    obtain ⟨i, e, b, rfl⟩ := exists_comp_eq_topFreeChart hage xs
    obtain ⟨hb, -⟩ := (e.map_rel (hullLanguage.rel p hp) (i.2.1.toChart ∘ b)).mp hr
    exact e.injective.comp hb
  exact ⟨hinj, (reconstruct_eval_eq_some_iff hage ⟨xs, hinj⟩ p).mpr ⟨hp, hr⟩⟩

/-- **Injectivity of labelled tuples**: under top-free chart coverage, a tuple at which a chart
relation holds is injective. -/
theorem injective_of_relMap_rel {xs : Fin n → M} {p : StageType.{u} α n} {hp : p.IsLegal}
    (h : RelMap (hullLanguage.rel p hp) xs) : Function.Injective xs :=
  ((relMap_rel_iff_reconstruct_eval hage xs hp).mp h).1

/-- **Uniqueness of labelled tuples**: under top-free chart coverage, at most one chart relation
holds at a tuple. -/
theorem eq_of_relMap_rel {xs : Fin n → M} {p q : StageType.{u} α n} {hp : p.IsLegal}
    {hq : q.IsLegal} (h : RelMap (hullLanguage.rel p hp) xs)
    (h' : RelMap (hullLanguage.rel q hq) xs) : p = q := by
  obtain ⟨_, he⟩ := (relMap_rel_iff_reconstruct_eval hage xs hp).mp h
  obtain ⟨_, he'⟩ := (relMap_rel_iff_reconstruct_eval hage xs hq).mp h'
  exact Option.some_injective _ (he.symm.trans he')

/-- **Exact partial restriction** (semantic contract, item 11): under top-free chart coverage, the
reconstructed realization is exactly consistent: the case of legal chart coverage
(`isConsistent_reconstruct_of_legalAge`).  A typed tuple and its faces factor through one chart,
where face maps compose; an invisible face has no type. -/
theorem isConsistent_reconstruct : (reconstruct α M).IsConsistent :=
  isConsistent_reconstruct_of_legalAge (hage.trans topFreeAge_subset_legalAge)

/-- **Covering** (semantic contract, item 11): under top-free chart coverage, the reconstructed
realization is covering: the case of legal chart coverage (`isCovering_reconstruct_of_legalAge`).
An injective tuple is a face of the points of the chart through which it factors, and those points
have the type of the chart. -/
theorem isCovering_reconstruct : (reconstruct α M).IsCovering :=
  isCovering_reconstruct_of_legalAge (hage.trans topFreeAge_subset_legalAge)

/-- **Covering for arbitrary tuples** (semantic contract, item 11): under top-free chart coverage,
every tuple of `M`, the empty tuple and tuples with repeated coordinates included, lies in the
points of a typed tuple. -/
theorem exists_comp_eq_reconstruct_eval (a : Fin n → M) :
    ∃ (m : ℕ) (u : Fin m ↪ M) (b : Fin n → Fin m), u ∘ b = a ∧
      ((reconstruct α M).eval u).isSome := by
  obtain ⟨i, e, b, rfl⟩ := exists_comp_eq_topFreeChart hage a
  refine ⟨i.1, i.2.1.toChart.toEmbedding.trans e.toEmbedding, b, rfl, ?_⟩
  rw [reconstruct_eval_chart i.2.2.1 e]
  rfl

/-- **Top-free types**: under top-free chart coverage, every reconstructed type is top-free, being a
face of a top-free stage type. -/
theorem isTopFree_of_reconstruct_eval {t : Fin n ↪ M} {p : StageType.{u} α n}
    (h : (reconstruct α M).eval t = some p) : p.IsTopFree := by
  obtain ⟨i, e, b, rfl⟩ := exists_eq_trans_topFreeChart hage t
  rw [reconstruct_eval_trans_chart i.2.2.1 e b, StageType.faceRealization_eval] at h
  exact i.2.2.2.restrictFace h

/-- **Every reconstructed type is in the age** (`IMPLEMENTATION.md`, milestone 5): under top-free
chart coverage, the chart of every reconstructed type belongs to the age of top-free charts. -/
theorem mem_topFreeAge_of_reconstruct_eval {t : Fin n ↪ M} {p : StageType.{u} α n}
    (h : (reconstruct α M).eval t = some p) :
    (⟨p.Chart, inferInstance⟩ : CategoryTheory.Bundled.{0} (hullLanguage.{u} α).Structure) ∈
      topFreeAge α :=
  topFreeChart_mem_topFreeAge
    ⟨n, p, hasLegalTypes_reconstruct t p h, isTopFree_of_reconstruct_eval hage h⟩

/-- **Typed tuples are charts**: under top-free chart coverage, an injective tuple has the
reconstructed type `p` exactly when `p` is legal and top-free and the tuple is the image of the
points of `p`, in order, under an embedding of the chart of `p`.  The embedding is that of legal
chart coverage (`exists_embedding_of_reconstruct_eval_of_legalAge`); the direction from an
embedding to the type needs only that `p` is legal (`reconstruct_eval_chart`). -/
theorem reconstruct_eval_eq_some_iff_exists_embedding (t : Fin n ↪ M) (p : StageType.{u} α n) :
    (reconstruct α M).eval t = some p ↔ p.IsLegal ∧ p.IsTopFree ∧
      ∃ φ : p.Chart ↪[hullLanguage.{u} α] M, ∀ j, φ (p.toChart j) = t j := by
  refine ⟨fun h ↦ ⟨hasLegalTypes_reconstruct t p h, isTopFree_of_reconstruct_eval hage h,
    exists_embedding_of_reconstruct_eval_of_legalAge (hage.trans topFreeAge_subset_legalAge) h⟩,
    fun ⟨hp, _, φ, hφ⟩ ↦ ?_⟩
  · have ht : p.toChart.toEmbedding.trans φ.toEmbedding = t := Function.Embedding.ext hφ
    rw [← ht]
    exact reconstruct_eval_chart hp φ

/-- **Typed tuples are exactly the substructures**: under top-free chart coverage, an injective
tuple has a reconstructed type exactly when the set of its points is closed under the hull
operations, that is, is the substructure it generates.  A tuple whose points do not form a
substructure, such as a pair whose hull has more points, has no type. -/
theorem isSome_reconstruct_eval_iff (t : Fin n ↪ M) :
    ((reconstruct α M).eval t).isSome ↔
      (Substructure.closure (hullLanguage.{u} α) (Set.range t) : Set M) = Set.range t := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨-, -, φ, hφ⟩ := (reconstruct_eval_eq_some_iff_exists_embedding hage t p).mp hp
    refine Set.Subset.antisymm (fun x hx ↦ ?_) Substructure.subset_closure
    have hle : Substructure.closure (hullLanguage.{u} α) (Set.range t) ≤ φ.toHom.range := by
      refine Substructure.closure_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      exact Hom.mem_range.mpr ⟨p.toChart j, hφ j⟩
    obtain ⟨y, rfl⟩ := Hom.mem_range.mp (hle hx)
    obtain ⟨j, rfl⟩ := p.toChart.surjective y
    exact ⟨j, (hφ j).symm⟩
  · obtain ⟨i, e, b, rfl⟩ := exists_eq_trans_topFreeChart hage t
    rw [reconstruct_eval_trans_chart i.2.2.1 e b, StageType.faceRealization_eval,
      StageType.isSome_restrictFace_iff]
    -- the preimage of the generated substructure is a substructure of the chart, on `univ.map b`
    refine StageType.mem_faces_of_substructure i.2.2.1
      ((Substructure.closure (hullLanguage.{u} α)
        (Set.range (b.trans (i.2.1.toChart.toEmbedding.trans e.toEmbedding)))).comap e.toHom)
        fun x ↦ ?_
    rw [Substructure.mem_comap, ← SetLike.mem_coe, h, mem_map]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, mem_univ j, e.injective hj⟩
    · rintro ⟨j, -, rfl⟩
      exact ⟨j, rfl⟩

/-- **The realization-level two-charts theorem** for the reconstructed realization: under top-free
chart coverage, two tuples of the same type `q`, generated by the coordinates `i₀` and `i₁`, that
agree at `i₀` and `i₁` are equal.  Both factor through one top-free chart, where this is the
two-charts theorem for charts (`StageType.eq_of_restrictFace_eq_some`). -/
theorem eq_of_reconstruct_eval_eq_some {m : ℕ} {q : StageType.{u} α m} {g g' : Fin m ↪ M}
    {i₀ i₁ : Fin m} (hgen : Geometry.hull univ q.toCellScheme.faces {i₀, i₁} = univ)
    (hg : (reconstruct α M).eval g = some q) (hg' : (reconstruct α M).eval g' = some q)
    (h₀ : g i₀ = g' i₀) (h₁ : g i₁ = g' i₁) : g = g' := by
  obtain ⟨i, e, c, hc⟩ := exists_comp_eq_topFreeChart hage (Fin.append g g')
  set E := i.2.1.toChart.toEmbedding.trans e.toEmbedding
  have hb (j : Fin m) : E (c (Fin.castAdd m j)) = g j := by
    rw [← Function.comp_apply (f := E), hc, Fin.append_left]
  have hb' (j : Fin m) : E (c (Fin.natAdd m j)) = g' j := by
    rw [← Function.comp_apply (f := E), hc, Fin.append_right]
  let b : Fin m ↪ Fin i.1 :=
    ⟨c ∘ Fin.castAdd m, fun x y h ↦ g.injective (by rw [← hb, ← hb]; exact congrArg E h)⟩
  let b' : Fin m ↪ Fin i.1 :=
    ⟨c ∘ Fin.natAdd m, fun x y h ↦ g'.injective (by rw [← hb', ← hb']; exact congrArg E h)⟩
  have hgb : b.trans E = g := Function.Embedding.ext hb
  have hgb' : b'.trans E = g' := Function.Embedding.ext hb'
  rw [← hgb, reconstruct_eval_trans_chart i.2.2.1 e b, StageType.faceRealization_eval] at hg
  rw [← hgb', reconstruct_eval_trans_chart i.2.2.1 e b', StageType.faceRealization_eval] at hg'
  have hbb : b = b' := StageType.eq_of_restrictFace_eq_some hgen hg hg'
    (E.injective ((hb i₀).trans (h₀.trans (hb' i₀).symm)))
    (E.injective ((hb i₁).trans (h₁.trans (hb' i₁).symm)))
  rw [← hgb, ← hgb', hbb]

/-- **The value at a chart witness**: under top-free chart coverage, at the generators of a tuple of
type `ι.type`, the hull operation of `ι` in `M` is the point of the tuple at the target. -/
theorem funMap_op_of_reconstruct_eval {ι : HullIndex.{u} α} {w : Fin ι.arity ↪ M}
    (hw : (reconstruct α M).eval w = some ι.type) :
    funMap (hullLanguage.op ι) ![w ι.left, w ι.right] = w ι.target := by
  obtain ⟨i, e, b, rfl⟩ := exists_eq_trans_topFreeChart hage w
  rw [reconstruct_eval_trans_chart i.2.2.1 e b, StageType.faceRealization_eval] at hw
  have h := funMap_op_trans_chart e ι (b ι.left) (b ι.right)
  rw [StageType.hullOp_eq_of_restrictFace hw] at h
  exact h

/-- **The roundtrip of the hull operations** (`HULL_ALGEBRA.md`, §5, (b), for the functions, for
structures with top-free chart coverage): under top-free chart coverage, the hull operations of
`M` are the hull operations of its reconstructed realization, at a chart witness and at the default
value alike. -/
theorem funMap_op_eq_hullOp (ι : HullIndex.{u} α) (a b : M) :
    funMap (hullLanguage.op ι) ![a, b] = (reconstruct α M).hullOp ι a b := by
  by_cases hw : ∃ w : Fin ι.arity ↪ M,
      (reconstruct α M).eval w = some ι.type ∧ w ι.left = a ∧ w ι.right = b
  · obtain ⟨w, hw', rfl, rfl, hval⟩ := Realization.hullOp_spec hw
    rw [hval]
    exact funMap_op_of_reconstruct_eval hage hw'
  · rw [Realization.hullOp_of_not_exists hw]
    obtain ⟨i, e, c, hc⟩ := exists_comp_eq_topFreeChart hage ![a, b]
    have ha : e (i.2.1.toChart (c 0)) = a := congrFun hc 0
    have hb : e (i.2.1.toChart (c 1)) = b := congrFun hc 1
    rw [← ha, ← hb, funMap_op_trans_chart, Realization.hullOp_of_not_exists]
    -- a chart witness in the chart is carried to a chart witness in `M`
    rintro ⟨w, hwq, hl, hr⟩
    refine hw ⟨w.trans (i.2.1.toChart.toEmbedding.trans e.toEmbedding), ?_, ?_, ?_⟩
    · rw [reconstruct_eval_trans_chart i.2.2.1 e w]
      exact hwq
    · simp only [Function.Embedding.trans_apply, hl]
      exact ha
    · simp only [Function.Embedding.trans_apply, hr]
      exact hb

/-- **The roundtrip of the structure** (`HULL_ALGEBRA.md`, §5, (b), for structures with top-free
chart coverage; semantic contract, item 11): under top-free chart coverage, the structure of `M`
in the hull language is the structure of its reconstructed realization, relations and functions
both. -/
theorem toHullStructure_reconstruct :
    (reconstruct α M).toHullStructure = ‹(hullLanguage.{u} α).Structure M› := by
  refine Structure.ext (funext fun l ↦ funext fun f ↦ ?_)
    (funext fun l ↦ funext fun r ↦ funext fun xs ↦ propext ?_)
  · induction f using hullLanguage.functions_induction with
    | op ι =>
      funext xs
      rw [Realization.funMap_toHullStructure]
      have hxs : xs = ![xs 0, xs 1] := funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩)
      conv_rhs => rw [hxs]
      rw [funMap_op_eq_hullOp hage]
  · rcases r with ⟨p, hp⟩ | r
    · exact (relMap_rel_iff_reconstruct_eval hage xs hp).symm
    · exact (r : Empty).elim

end Age

/-! ### A Fraïssé limit of the age of top-free charts -/

section Limit

variable {α : Ordinal.{u}} {M : Type} [(hullLanguage.{u} α).Structure M]

/-- **A nonempty carrier**: a structure of the hull language whose age contains the age of
top-free charts is nonempty, since the one-point chart embeds in it. -/
theorem nonempty_of_topFreeAge_subset (h : topFreeAge α ⊆ (hullLanguage.{u} α).age M) :
    Nonempty M := by
  obtain ⟨-, ⟨e⟩⟩ := h (topFreeChart_mem_topFreeAge (TopFreeIndex.point α))
  exact ⟨e ((TopFreeIndex.point α).2.1.toChart ⟨0, Nat.one_pos⟩)⟩

/-- **Reconstruction from the equality of ages**: if the age of `M` is the age of top-free charts,
the carrier is nonempty, the reconstructed realization is exactly consistent and covering with legal
top-free types, and the structure of `M` in the hull language is the structure of its reconstructed
realization. -/
theorem reconstruct_of_age_eq (hM : (hullLanguage.{u} α).age M = topFreeAge α) :
    Nonempty M ∧ (reconstruct α M).IsConsistent ∧ (reconstruct α M).IsCovering ∧
      (reconstruct α M).HasLegalTypes ∧
      (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n),
        (reconstruct α M).eval t = some p → p.IsTopFree) ∧
      (reconstruct α M).toHullStructure = ‹(hullLanguage.{u} α).Structure M› :=
  ⟨nonempty_of_topFreeAge_subset hM.symm.subset, isConsistent_reconstruct hM.subset,
    isCovering_reconstruct hM.subset, hasLegalTypes_reconstruct,
    fun _ _ _ ↦ isTopFree_of_reconstruct_eval hM.subset, toHullStructure_reconstruct hM.subset⟩

/-- **Reconstruction from a Fraïssé limit of the age of top-free charts** (roadmap, the top-free
witnesses, steps 4 and 5; semantic contract, item 11, without receiving): the carrier is nonempty,
the reconstructed realization is exactly consistent and covering with legal top-free types, and the
structure of the limit in the hull language is the structure of its reconstructed realization.

The limit is a hypothesis.  Only its age is used, not its ultrahomogeneity; its existence
(`exists_isFraisseLimit_topFreeAge`) is conditional on the coatom extension property (compiled at
every stage that is zero or a limit, `StageType.hasCoatomExtensions`), and is not used here. -/
theorem reconstruct_of_isFraisseLimit [Countable (Σ l, (hullLanguage.{u} α).Functions l)]
    [Countable M] (hM : IsFraisseLimit (topFreeAge.{u} α) M) :
    Nonempty M ∧ (reconstruct α M).IsConsistent ∧ (reconstruct α M).IsCovering ∧
      (reconstruct α M).HasLegalTypes ∧
      (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n),
        (reconstruct α M).eval t = some p → p.IsTopFree) ∧
      (reconstruct α M).toHullStructure = ‹(hullLanguage.{u} α).Structure M› :=
  reconstruct_of_age_eq hM.age

end Limit

end VaughtConjecture
