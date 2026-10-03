/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Amalgamation
import VaughtConjecture.ClassicalLimit.Reconstruction
import VaughtConjecture.Language.Density
import VaughtConjecture.Realization.Receiving

/-!
# Receiving for the reconstructed realization of a classical limit

Roadmap, the section "The top-free witnesses: the finite age and its classical limit", step 6
(receiving) and, for the base reduct, step 7 (the density sentence); Layer 3, 3.4, the rows (R1)
and (R5) of the table; semantic contract, item 11 (receiving with all equations attached to one
occurrence) and item 12 (cutoff observations and exact extension within a specified age are
different notions).

Throughout, `M` is a structure of the hull language `hullLanguage α` whose age is the age of
top-free charts, `hage : (hullLanguage α).age M = topFreeAge α`, and which is ultrahomogeneous,
`hu : (hullLanguage α).IsUltrahomogeneous M`; a Fraïssé limit of the age of top-free charts is
both (`hasFiniteCutReceiving_reconstruct_of_isFraisseLimit`).

**Exact extension within the age** (`exists_reconstruct_eval_eq_of_isTopFree`).  Let `t` be a
typed tuple of the reconstructed realization `reconstruct α M`, of type `p`, and let `D` be a legal
top-free stage type on `m` points whose face along an embedding `g` of coordinates is `p`.  Some
tuple `u` of `M` extends `t` along `g` literally and has the type `D` exactly.  The tuple `t` is
the image of the points of `p` under an embedding `φ` of the chart of `p`
(`reconstruct_eval_eq_some_iff_exists_embedding`, which uses the inclusion of the age of `M` in the
age of top-free charts); the chart of `D` is in the age of `M` (the converse inclusion), and the
chart embedding of `p` into `D` along `g` (`StageType.chartEmbedding`) is an embedding of finite
structures, so ultrahomogeneity extends `φ` along it to an embedding `ψ` of the chart of `D`
(`FirstOrder.Language.IsUltrahomogeneous.extend_embedding`).  The points of `D` under `ψ` have the
type `D` (`reconstruct_eval_chart`).  This is exact extension, within the age of top-free charts,
of every top-free donor; it needs no hypothesis on the stage.

**Finite-cut receiving** (`hasFiniteCutReceiving_reconstruct`, step 6).  Over an occurrence of
type `p` on `n` points, a one-point coface `d` of `p` and a permitted cutoff `δ < α`: the labels of
the top-free type `p` are at most an ordinal `o < α` (`StageType.IsTopFree.exists_label_le`, which
needs `0 < α`, a consequence of `δ < α`); an ordinal `c'` with `max o δ < c' < α`, self-visible at
`n + 1`, exists because the stage is zero or a limit (`Label.exists_lt_lt_isSelfVisible`).  The
capped coface `d.cap c'` (`StageType.cap`) is legal (`StageType.isLegal_cap`), top-free
(`StageType.isTopFree_cap`), and restricts literally to `p` along the initial segment, since the
labels of `p` are at most `c'` (`StageType.restrictFace_cap`).  Exact extension within the age
receives it, and `min (min (d i) c') δ = min (d i) δ` cellwise, so the received type agrees with
`d` below `δ`.  The root, the new point, and the agreement with the donor are equations about the
one occurrence `ψ` gives; its new point is off the whole root.

* *A top-free donor* is received exactly: at a cutoff above its labels the cap changes nothing,
  and exact extension within the age applies to it directly.
* *A donor with top labels* is received at each permitted cutoff separately, by an occurrence that
  depends on the cutoff, through a cap above the cutoff: no top label is recovered, since every
  reconstructed type is top-free.

**What is used.**  The root is a whole occurrence, so the face of the chart of `p` to which the
donor is attached is the whole chart, and the one-point pinned extension of that chart by `d` is
`d` itself: the case of (R6) of the table of Layer 3, 3.4, where the face is onto, which needs no
coatom extension (`StageType.exists_pinned_extension_of_surjective`; here `d` is used directly, as
a coface of `p`).  Capped, it is (R5) in that case.  So step 6 uses only the equality of ages,
ultrahomogeneity, and capping: neither the coatom extension property
`StageType.HasCoatomExtensions` nor modelhood (`Realization.IsModel`) is a hypothesis of any
statement here.  Only the *existence* of a Fraïssé limit of the age of top-free charts
(`exists_isFraisseLimit_topFreeAge`) needs the coatom extension property, which is not proved.

**Finite-extension receiving** (`hasFiniteExtensionReceiving_reconstruct`): the reconstructed
realization is exactly consistent (`isConsistent_reconstruct`), so finite-cut receiving gives
receiving of donors on several new points
(`Realization.HasFiniteCutReceiving.hasFiniteExtensionReceiving`).

**The base reduct** (`realize_densitySentence_reconstruct_reduce`, the base-reduct part of
step 7).  For a limit stage `α ≥ ω`, the reduction of the reconstructed realization to `ω`
(`Realization.reduce`) has legal types (`hasLegalTypes_reconstruct_reduce`, by
`StageType.IsLegal.reduce`), is exactly consistent and covering (`isConsistent_reconstruct_reduce`,
`isCovering_reconstruct_reduce`), and has the finite-cut receiving property
(`hasFiniteCutReceiving_reconstruct_reduce`): receiving at `α` descends along stage reduction
(`Realization.HasFiniteCutReceiving.reduce`), one permitted cutoff at a time, which is not exact
projected receiving (semantic contract, item 12).  With a nonempty carrier, these are the clauses
of the density sentence for the base-language structure of the reduction
(`baseLanguage.realize_toStructure_densitySentence_iff`), so that structure satisfies it.

**What this file does not contain.**

* *Finite-cut receiving of models in general*, (R1) of the table of Layer 3, 3.4: every model, not
  only the reconstructed realization of a classical limit, has the finite-cut receiving property.
  It is still to be proved; the statements here do not give it.
* *Modelhood* (step 7): the four extension clauses of `Realization.IsModel` for the reconstructed
  realization are in `VaughtConjecture.ClassicalLimit.Modelhood` (`isModel_reconstruct`), from
  receiving and the cap-to-model theorem at a nonzero limit stage
  (`Realization.isModel_of_hasFiniteCutReceiving`), given the nonemptiness of the uniformity and
  dominance instances.
* *Infinitude and terminality* (step 7) are still to be proved.  Infinitude is to come from
  receiving over a whole occurrence, with a one-point coface of its type
  (`StageType.exists_extension`, under the coatom extension property
  `StageType.HasCoatomExtensions`): the received point is off the whole occurrence.

## Placement

This file belongs to the section on the top-free witnesses of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open FirstOrder Language Structure Label Realization
open scoped Ordinal

variable {α : Ordinal.{u}} {M : Type} [(hullLanguage.{u} α).Structure M]

section Receiving

variable (hage : (hullLanguage.{u} α).age M = topFreeAge α)
  (hu : (hullLanguage.{u} α).IsUltrahomogeneous M)
include hage hu

/-- **Exact extension within the age of top-free charts**: for a structure whose age is the age of
top-free charts and which is ultrahomogeneous, over a typed tuple `t` of type `p`, every legal
top-free stage type `D` whose face along `g` is `p` is the type of a tuple extending `t` along `g`
literally.  No hypothesis on the stage is needed. -/
theorem exists_reconstruct_eval_eq_of_isTopFree {n m : ℕ} {t : Fin n ↪ M}
    {p : StageType.{u} α n} (ht : (reconstruct α M).eval t = some p) {D : StageType.{u} α m}
    (hD : D.IsLegal) (hDt : D.IsTopFree) {g : Fin n ↪ Fin m}
    (hg : StageType.restrictFace g D = some p) :
    ∃ v : Fin m ↪ M, g.trans v = t ∧ (reconstruct α M).eval v = some D := by
  obtain ⟨-, -, φ, hφ⟩ :=
    (reconstruct_eval_eq_some_iff_exists_embedding hage.subset t p).mp ht
  have hmem : topFreeChart α ⟨m, D, hD, hDt⟩ ∈ (hullLanguage.{u} α).age M :=
    hage ▸ topFreeChart_mem_topFreeAge _
  have : Nonempty (D.Chart ↪[hullLanguage.{u} α] M) := hmem.2
  obtain ⟨ψ, hψ⟩ := hu.extend_embedding (S := p.Chart) (Structure.FG.of_finite) φ
    (StageType.chartEmbedding hg)
  refine ⟨D.toChart.toEmbedding.trans ψ.toEmbedding, Function.Embedding.ext fun j ↦ ?_,
    reconstruct_eval_chart hD ψ⟩
  rw [← hφ j, hψ]
  -- the chart embedding along `g` sends the point `j` of `p` to the point `g j` of `D`
  rfl

/-- **Receiving for the reconstructed realization of a classical limit** (roadmap, the top-free
witnesses, step 6): for a structure whose age is the age of top-free charts and which is
ultrahomogeneous, at a stage that is zero or a limit, the reconstructed realization has the
finite-cut receiving property.  The donor is capped at an ordinal below the stage, self-visible at
its arity, above the cutoff and the labels of the root's type, and the capped donor, a legal
top-free coface of the root's type, is received exactly
(`exists_reconstruct_eval_eq_of_isTopFree`).

Only the equality of ages, ultrahomogeneity, and capping are used: neither the coatom extension
property `StageType.HasCoatomExtensions` nor modelhood is a hypothesis.  The existence of such a
structure (`exists_isFraisseLimit_topFreeAge`) needs the coatom extension property, which is not
proved. -/
theorem hasFiniteCutReceiving_reconstruct (hα : Order.IsSuccPrelimit α) :
    (reconstruct α M).HasFiniteCutReceiving := by
  intro x d hd c hc
  obtain ⟨δ, hδ, rfl⟩ := isPermittedCutoff_iff.mp hc
  have h0 : 0 < α := pos_of_gt hδ
  obtain ⟨-, hpt, -⟩ :=
    (reconstruct_eval_eq_some_iff_exists_embedding hage.subset x.tuple x.type).mp x.eval_tuple
  obtain ⟨o, ho, hpo⟩ := hpt.exists_label_le h0
  obtain ⟨c', hoc', hc'α, hc'⟩ := exists_lt_lt_isSelfVisible hα (max_lt ho hδ) (x.arity + 1)
  have hle {y : Ordinal.{u}} (hy : y ≤ max o δ) : (y : Label.{u}) ≤ c' :=
    WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (hy.trans hoc'.le))
  have hQ : StageType.restrictFace Fin.castSuccEmb (d.cap c' hc' hc'α) = some x.type :=
    StageType.restrictFace_cap hd.2 fun i ↦ (hpo i).trans (hle (le_max_left _ _))
  obtain ⟨v, hv, hve⟩ := exists_reconstruct_eval_eq_of_isTopFree hage hu x.eval_tuple
    (StageType.isLegal_cap.mpr hd.1) StageType.isTopFree_cap hQ
  refine ⟨v, hv, d.cap c' hc' hc'α, ⟨rfl, fun i j hij ↦ ?_⟩, hve⟩
  obtain rfl : i = j := Fin.ext hij
  -- the labels of the capped coface are `min (d.label i) c'` (`StageType.cap_label`)
  change min (min (d.label i) (c' : Label.{u})) _ = _
  rw [min_assoc, min_eq_right (hle (le_max_right _ _))]

/-- **Finite-extension receiving for the reconstructed realization of a classical limit**: for a
structure whose age is the age of top-free charts and which is ultrahomogeneous, at a stage that is
zero or a limit, the reconstructed realization receives donors on several new points.  It is exactly
consistent (`isConsistent_reconstruct`), so this is finite-cut receiving
(`hasFiniteCutReceiving_reconstruct`) along the chain of
`Realization.HasFiniteCutReceiving.hasFiniteExtensionReceiving`. -/
theorem hasFiniteExtensionReceiving_reconstruct (hα : Order.IsSuccPrelimit α) :
    (reconstruct α M).HasFiniteExtensionReceiving :=
  (hasFiniteCutReceiving_reconstruct hage hu hα).hasFiniteExtensionReceiving
    (isConsistent_reconstruct hage.subset) hα

end Receiving

/-- **Receiving for the reconstructed realization of a Fraïssé limit** of the age of top-free
charts, at a stage that is zero or a limit (roadmap, the top-free witnesses, step 6).  The limit is
a hypothesis: its existence (`exists_isFraisseLimit_topFreeAge`) needs the coatom extension
property `StageType.HasCoatomExtensions`, which is not proved; receiving itself uses only its age
and its ultrahomogeneity. -/
theorem hasFiniteCutReceiving_reconstruct_of_isFraisseLimit
    [Countable (Σ l, (hullLanguage.{u} α).Functions l)] [Countable M]
    (hα : Order.IsSuccPrelimit α) (hM : IsFraisseLimit (topFreeAge.{u} α) M) :
    (reconstruct α M).HasFiniteCutReceiving :=
  hasFiniteCutReceiving_reconstruct hM.age hM.ultrahomogeneous hα

/-! ### The base reduct -/

section Reduce

variable {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β)

/-- **Legal types of a reduction**: the stage reduction of the reconstructed realization to a stage
that is zero or a limit has legal types, the reductions of legal types.  No hypothesis on `M` is
needed. -/
theorem hasLegalTypes_reconstruct_reduce : ((reconstruct α M).reduce hβ).HasLegalTypes :=
  fun _ t p hp ↦ by
    obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hp
    exact (hasLegalTypes_reconstruct t p' hp').reduce hβ

/-- **Exact consistency of a reduction**: under top-free chart coverage, the stage reduction of the
reconstructed realization to a stage that is zero or a limit is exactly consistent. -/
theorem isConsistent_reconstruct_reduce (hage : (hullLanguage.{u} α).age M ⊆ topFreeAge α) :
    ((reconstruct α M).reduce hβ).IsConsistent :=
  (isConsistent_reconstruct hage).reduce hβ

/-- **Covering of a reduction**: under top-free chart coverage, the stage reduction of the
reconstructed realization to a stage that is zero or a limit is covering. -/
theorem isCovering_reconstruct_reduce (hage : (hullLanguage.{u} α).age M ⊆ topFreeAge α) :
    ((reconstruct α M).reduce hβ).IsCovering :=
  (isCovering_reconstruct hage).reduce hβ

/-- **Receiving of a reduction**: for a structure whose age is the age of top-free charts and which
is ultrahomogeneous, at a stage `α` that is zero or a limit, the stage reduction of the
reconstructed realization to a stage `β ≤ α` that is zero or a limit has the finite-cut receiving
property: receiving at `α` (`hasFiniteCutReceiving_reconstruct`) descends along stage reduction
(`Realization.HasFiniteCutReceiving.reduce`), one permitted cutoff at a time.  This is not exact
projected receiving (semantic contract, item 12). -/
theorem hasFiniteCutReceiving_reconstruct_reduce
    (hage : (hullLanguage.{u} α).age M = topFreeAge α)
    (hu : (hullLanguage.{u} α).IsUltrahomogeneous M) (hα : Order.IsSuccPrelimit α) (hβα : β ≤ α) :
    ((reconstruct α M).reduce hβ).HasFiniteCutReceiving :=
  (hasFiniteCutReceiving_reconstruct hage hu hα).reduce hα hβ hβα

end Reduce

/-- **The base reduct satisfies the density sentence** (roadmap, the top-free witnesses, step 7,
for the base reduct): for a structure whose age is the age of top-free charts and which is
ultrahomogeneous, at a limit stage `α ≥ ω`, the base-language structure of the reduction of the
reconstructed realization to `ω` satisfies the density sentence.  Its clauses are a nonempty
carrier (`nonempty_of_topFreeAge_subset`), exact consistency and covering
(`isConsistent_reconstruct_reduce`, `isCovering_reconstruct_reduce`), and finite-cut receiving
(`hasFiniteCutReceiving_reconstruct_reduce`), for a realization with legal types
(`hasLegalTypes_reconstruct_reduce`), by `baseLanguage.realize_toStructure_densitySentence_iff`.

This is the base-reduct part of step 7.  Modelhood of the reconstructed realization at `α`, given
the nonemptiness of the uniformity and dominance instances, is `isModel_reconstruct`; infinitude
and terminality are still to be proved.  The existence
of a Fraïssé limit of the age of top-free charts (`exists_isFraisseLimit_topFreeAge`) needs the
coatom extension property `StageType.HasCoatomExtensions`, which is not proved. -/
theorem realize_densitySentence_reconstruct_reduce
    (hage : (hullLanguage.{u} α).age M = topFreeAge α)
    (hu : (hullLanguage.{u} α).IsUltrahomogeneous M) (hα : Order.IsSuccPrelimit α)
    (hωα : ω ≤ α) :
    @Sentenceω.Realize _ baseLanguage.densitySentence M
      ((reconstruct α M).reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).toStructure :=
  (baseLanguage.realize_toStructure_densitySentence_iff (hasLegalTypes_reconstruct_reduce _)).mpr
    ⟨nonempty_of_topFreeAge_subset hage.symm.subset, isConsistent_reconstruct_reduce _ hage.subset,
      isCovering_reconstruct_reduce _ hage.subset,
      hasFiniteCutReceiving_reconstruct_reduce _ hage hu hα hωα⟩

end VaughtConjecture
