/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Age
import VaughtConjecture.Stage.Cap

/-!
# Amalgamation and joint embedding of top-free charts, under the coatom extension property

Roadmap, the section "The top-free witnesses: the finite age and its classical limit", step 2
(amalgamation and joint embedding proved directly for finite charts), here conditional on the coatom
extension property, which is not proved, with the application of the classical existence theorem of
step 3; Layer 3, 3.1, (R6) (the plain form of the coatom extension property gives the amalgamation
of legal stage types over a common face, which capped is step 2).

**Capping.**  The capped stage type `t.cap c` (`StageType.cap`, in `VaughtConjecture.Stage.Cap`)
has the scheme of `t` and the labels `min (t.label d) c`; it is legal exactly when `t` is, it is
top-free, and along a closed face whose labels are at most `c` it restricts to the same stage type
as `t` (`StageType.isLegal_cap`, `StageType.isTopFree_cap`, `StageType.restrictFace_cap`).  At a
limit stage such a cap exists above the labels of any two top-free stage types, self-visible at
any arity (`StageType.exists_cap`).

**Amalgamation of top-free stage types, under the coatom extension property**
(`StageType.exists_isTopFree_amalgam`).  If the coatom extension property holds at a limit stage,
two legal top-free stage types with the same face `p` along `f` and `g` are the faces, along `i` and
`j` with `f.trans i = g.trans j`, of one legal top-free stage type: the amalgam of
`StageType.exists_amalgam` capped at a cap self-visible at its arity and above the labels of the two
stage types.  The labels of the amalgam that are not labels of the two stage types are arbitrary,
possibly `⊤`; capping is what makes it top-free, so nothing about the labels of `exists_amalgam`'s
output is used.

**Amalgamation and joint embedding of top-free charts, under the coatom extension property.**  Every
embedding of a top-free chart into another is the chart embedding of a face map along which the
restriction is literally the smaller stage type (`StageType.exists_eq_chartEmbedding`, both charts
being legal), so the amalgamation of top-free stage types gives the amalgamation of top-free charts
with a literally commuting square (`exists_amalgam_topFreeChart`, `StageType.chartEmbedding_comp`),
the hypothesis `hap` of `isFraisse_representativeClass`.  Joint embedding is amalgamation over the
empty chart, which is the face of every top-free chart on no points
(`TopFreeIndex.restrictFace_empty`, from `StageType.isSome_restrictFace_of_zero` and
`StageType.eq_of_zero`), and gives the hypothesis `hjep` (`exists_jointEmbedding_topFreeChart`).
Strong amalgamation (disjointness of the two images outside the common chart) is not claimed.  Under
the coatom extension property at a limit stage, the age of top-free charts has the amalgamation and
joint embedding properties (`amalgamation_topFreeAge`, `jointEmbedding_topFreeAge`) and, when there
are countably many ordinals below the stage, is a Fraïssé class (`isFraisse_topFreeAge`; at `ω`,
`isFraisse_topFreeAge_omega`).  None of these is proved outright: the coatom extension property is
not proved (Hypotheses, below).

**Classical existence** (step 3), under the coatom extension property.
`exists_isFraisseLimit_topFreeAge` is the classical existence theorem
`exists_isFraisseLimit_representativeClass` applied to the hypotheses of steps 1 and 2, with the
countability of the function symbols of the hull language derived from the countability of the
ordinals below the stage (`hullLanguage.countable_functions`); at `ω` it is
`exists_isFraisseLimit_topFreeAge_omega`.  It is not developed further here.

**Hypotheses.**  Each statement of amalgamation, joint embedding, the Fraïssé class, and the limit
takes three hypotheses on the stage `α`, explicitly:

* `hext : StageType.HasCoatomExtensions α`, the plain form of the coatom extension property at `α`.
  It is not proved: it is the open part of statement (R6) of roadmap, Layer 3, 3.1, whose proof by
  the completion of the coatom amalgam is checkpoints 2.1–2.7 there.  It gives the amalgam of two
  legal stage types over a common face (`StageType.exists_amalgam`).
* `hα : Order.IsSuccPrelimit α`, so that above every ordinal below `α` there is an ordinal below `α`
  self-visible at a given arity, the cap.
* `h0 : 0 < α`, so that the bound of the labels of a top-free stage type, and the cap, are ordinals
  below `α`.  It is a restriction of the ordinal-valued cap, not of amalgamation: at stage `0` every
  top-free label is `⊥`, and capping at `⊥` is lawful.  A cap valued in labels (a label `c ≠ ⊤` at
  the stage, self-visible at the arity) would remove it; that weakening is not made here.

Together `hα` and `h0` say that `α` is a **limit stage**, a limit ordinal.  Capping (`StageType.cap`
to `StageType.restrictFace_cap`) and the hereditary property assume none of them; the existence of
the cap (`StageType.exists_cap`) assumes `hα` and `h0`.

## Placement

This file belongs to the section on the top-free witnesses of `roadmap/README.md`.

## References

Capping a lawful section is [Kni26, Lemma 2.5.8]; the coatom extension property is
[Kni26, Corollary 4.3.22].
-/

universe u

namespace VaughtConjecture

open FirstOrder Language Structure Finset CategoryTheory Label
open scoped Ordinal

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-! ### Amalgamation of top-free stage types -/

/-- **Amalgamation of top-free stage types over a common face**, from the coatom extension property
at a limit stage: two legal top-free stage types `P` and `R` whose faces along `f` and `g` are the
same stage type are the faces, along embeddings `i` and `j` with `f.trans i = g.trans j`, of one
legal top-free stage type.  It is the amalgam of `exists_amalgam` capped at an ordinal self-visible
at its arity and above every label of `P` and `R` (`exists_cap`, `restrictFace_cap`).

The coatom extension property `HasCoatomExtensions α` is not proved here: it is the open part of
statement (R6) of roadmap, Layer 3, 3.1, checkpoints 2.1–2.7. -/
theorem exists_isTopFree_amalgam (hext : HasCoatomExtensions.{u} α)
    (hα : Order.IsSuccPrelimit α) (h0 : 0 < α) {P : StageType.{u} α n} {R : StageType.{u} α k}
    (hP : P.IsLegal) (hPt : P.IsTopFree) (hR : R.IsLegal) (hRt : R.IsTopFree) {f : Fin m ↪ Fin n}
    {g : Fin m ↪ Fin k} {p : StageType.{u} α m} (hPf : restrictFace f P = some p)
    (hRg : restrictFace g R = some p) :
    ∃ (N : ℕ) (Q : StageType.{u} α N) (i : Fin n ↪ Fin N) (j : Fin k ↪ Fin N), Q.IsLegal ∧
      Q.IsTopFree ∧ restrictFace i Q = some P ∧ restrictFace j Q = some R ∧
        f.trans i = g.trans j := by
  obtain ⟨N, Q, i, j, hQ, hQP, hQR, hij⟩ := exists_amalgam hext hP hR hPf hRg
  obtain ⟨c, hcα, hc, hPc, hRc⟩ := exists_cap hα h0 hPt hRt N
  exact ⟨N, Q.cap c hc hcα, i, j, hQ, isTopFree_cap, restrictFace_cap hQP hPc,
    restrictFace_cap hQR hRc, hij⟩

end StageType

/-! ### Amalgamation and joint embedding of top-free charts -/

variable {α : Ordinal.{u}}

/-- The empty chart is the face on no points of every top-free chart: every stage type has a face
on no points (`StageType.isSome_restrictFace_of_zero`), and there is only one stage type on no
points (`StageType.eq_of_zero`). -/
theorem TopFreeIndex.restrictFace_empty (i : TopFreeIndex.{u} α) (e : Fin 0 ↪ Fin i.1) :
    StageType.restrictFace e i.2.1 = some (TopFreeIndex.empty α).2.1 := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (i.2.1.isSome_restrictFace_of_zero e)
  exact hp.trans (congrArg some (StageType.eq_of_zero _ _))

/-- **Amalgamation of top-free charts**, from the coatom extension property at a limit stage: two
embeddings of a top-free chart into top-free charts are completed by embeddings into one top-free
chart to a literally commuting square.  This is the hypothesis `hap` of
`isFraisse_representativeClass` for the top-free charts.  The embeddings are chart embeddings of
face maps (`StageType.exists_eq_chartEmbedding`), and the amalgam is that of top-free stage types
over the common face (`StageType.exists_isTopFree_amalgam`).

The coatom extension property `StageType.HasCoatomExtensions α` is not proved here: it is the open
part of statement (R6) of roadmap, Layer 3, 3.1, checkpoints 2.1–2.7. -/
theorem exists_amalgam_topFreeChart (hext : StageType.HasCoatomExtensions.{u} α)
    (hα : Order.IsSuccPrelimit α) (h0 : 0 < α) (i j k : TopFreeIndex.{u} α)
    (f : topFreeChart α i ↪[hullLanguage.{u} α] topFreeChart α j)
    (g : topFreeChart α i ↪[hullLanguage.{u} α] topFreeChart α k) :
    ∃ (l : TopFreeIndex.{u} α) (a : topFreeChart α j ↪[hullLanguage.{u} α] topFreeChart α l)
      (b : topFreeChart α k ↪[hullLanguage.{u} α] topFreeChart α l), a.comp f = b.comp g := by
  obtain ⟨e, he, rfl⟩ := StageType.exists_eq_chartEmbedding (P := i.2.1) (Q := j.2.1)
    (.inl i.2.2.1) f
  obtain ⟨e', he', rfl⟩ := StageType.exists_eq_chartEmbedding (P := i.2.1) (Q := k.2.1)
    (.inl i.2.2.1) g
  obtain ⟨N, Q, a, b, hQ, hQt, hQa, hQb, hab⟩ := StageType.exists_isTopFree_amalgam hext hα h0
    j.2.2.1 j.2.2.2 k.2.2.1 k.2.2.2 he he'
  refine ⟨⟨N, Q, hQ, hQt⟩, StageType.chartEmbedding hQa, StageType.chartEmbedding hQb, ?_⟩
  refine Embedding.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := i.2.1.toChart.surjective x
  have hy := DFunLike.congr_fun hab y
  simp only [Function.Embedding.trans_apply] at hy
  simp only [Embedding.comp_apply, StageType.chartEmbedding_toChart, hy]

/-- **Joint embedding of top-free charts**, from the coatom extension property at a limit stage: any
two top-free charts embed into one top-free chart.  This is the hypothesis `hjep` of
`isFraisse_representativeClass` for the top-free charts: the amalgamation of the two charts over the
empty chart (`TopFreeIndex.restrictFace_empty`).

The coatom extension property `StageType.HasCoatomExtensions α` is not proved here: it is the open
part of statement (R6) of roadmap, Layer 3, 3.1, checkpoints 2.1–2.7. -/
theorem exists_jointEmbedding_topFreeChart (hext : StageType.HasCoatomExtensions.{u} α)
    (hα : Order.IsSuccPrelimit α) (h0 : 0 < α) (i j : TopFreeIndex.{u} α) :
    ∃ k, Nonempty (topFreeChart α i ↪[hullLanguage.{u} α] topFreeChart α k) ∧
      Nonempty (topFreeChart α j ↪[hullLanguage.{u} α] topFreeChart α k) := by
  obtain ⟨l, a, b, -⟩ := exists_amalgam_topFreeChart hext hα h0 (TopFreeIndex.empty α) i j
    (StageType.chartEmbedding (i.restrictFace_empty Function.Embedding.ofIsEmpty))
    (StageType.chartEmbedding (j.restrictFace_empty Function.Embedding.ofIsEmpty))
  exact ⟨l, ⟨a⟩, ⟨b⟩⟩

/-- **The age of top-free charts has the amalgamation property**, conditional on the coatom
extension property at a limit stage.

The coatom extension property `StageType.HasCoatomExtensions α` is not proved here: it is the open
part of statement (R6) of roadmap, Layer 3, 3.1, checkpoints 2.1–2.7. -/
theorem amalgamation_topFreeAge (hext : StageType.HasCoatomExtensions.{u} α)
    (hα : Order.IsSuccPrelimit α) (h0 : 0 < α) : Amalgamation (topFreeAge.{u} α) :=
  representativeClass_amalgamation _ (exists_amalgam_topFreeChart hext hα h0)

/-- **The age of top-free charts has the joint embedding property**, conditional on the coatom
extension property at a limit stage.

The coatom extension property `StageType.HasCoatomExtensions α` is not proved here: it is the open
part of statement (R6) of roadmap, Layer 3, 3.1, checkpoints 2.1–2.7. -/
theorem jointEmbedding_topFreeAge (hext : StageType.HasCoatomExtensions.{u} α)
    (hα : Order.IsSuccPrelimit α) (h0 : 0 < α) : JointEmbedding (topFreeAge.{u} α) :=
  representativeClass_jointEmbedding _ (exists_jointEmbedding_topFreeChart hext hα h0)

/-! ### The Fraïssé class -/

/-- **The age of top-free charts is a Fraïssé class**, from the coatom extension property at a limit
stage `α`, with countably many ordinals below `α`: it is hereditary (`exists_equiv_topFreeChart`),
has the joint embedding and amalgamation properties, and has countably many isomorphism types of
finitely generated members.

The coatom extension property `StageType.HasCoatomExtensions α` is not proved here: it is the open
part of statement (R6) of roadmap, Layer 3, 3.1, checkpoints 2.1–2.7. -/
theorem isFraisse_topFreeAge (hext : StageType.HasCoatomExtensions.{u} α)
    (hα : Order.IsSuccPrelimit α) (h0 : 0 < α) (hcount : (Set.Iio α).Countable) :
    IsFraisse (topFreeAge.{u} α) :=
  haveI := countable_topFreeIndex hcount
  isFraisse_representativeClass _ fg_topFreeChart exists_equiv_topFreeChart
    (exists_jointEmbedding_topFreeChart hext hα h0) (exists_amalgam_topFreeChart hext hα h0)

/-- **The age of top-free charts at `ω` is a Fraïssé class**, conditional on the coatom extension
property at `ω`.

The coatom extension property `StageType.HasCoatomExtensions ω` is not proved here: it is the open
part of statement (R6) of roadmap, Layer 3, 3.1, checkpoints 2.1–2.7. -/
theorem isFraisse_topFreeAge_omega (hext : StageType.HasCoatomExtensions.{u} ω) :
    IsFraisse (topFreeAge.{u} ω) :=
  isFraisse_topFreeAge hext Ordinal.isSuccLimit_omega0.isSuccPrelimit Ordinal.omega0_pos
    (Set.countable_coe_iff.mp countable_Iio_omega0_coe)

/-! ### Classical existence -/

/-- **A Fraïssé limit of the age of top-free charts** (step 3): the classical existence theorem
`exists_isFraisseLimit_representativeClass` applied to the hypotheses of steps 1 and 2, conditional
on the coatom extension property at a limit stage `α` with countably many ordinals below `α`.  The
countability of the function symbols of the hull language, needed to state `IsFraisseLimit`, is
derived from that of the ordinals below `α` (`hullLanguage.countable_functions`), not assumed.

The coatom extension property `StageType.HasCoatomExtensions α` is not proved here: it is the open
part of statement (R6) of roadmap, Layer 3, 3.1, checkpoints 2.1–2.7. -/
theorem exists_isFraisseLimit_topFreeAge (hext : StageType.HasCoatomExtensions.{u} α)
    (hα : Order.IsSuccPrelimit α) (h0 : 0 < α) (hcount : (Set.Iio α).Countable) :
    letI := hullLanguage.countable_functions hcount
    ∃ (M : Bundled.{0} (hullLanguage.{u} α).Structure) (_ : Countable M),
      IsFraisseLimit (topFreeAge.{u} α) M :=
  letI := hullLanguage.countable_functions hcount
  haveI := countable_topFreeIndex hcount
  exists_isFraisseLimit_representativeClass _ fg_topFreeChart exists_equiv_topFreeChart
    (exists_jointEmbedding_topFreeChart hext hα h0) (exists_amalgam_topFreeChart hext hα h0)

/-- **A Fraïssé limit of the age of top-free charts at `ω`**, conditional on the coatom extension
property at `ω`; the countability of the function symbols is the instance
`hullLanguage.countable_functions_omega`.

The coatom extension property `StageType.HasCoatomExtensions ω` is not proved here: it is the open
part of statement (R6) of roadmap, Layer 3, 3.1, checkpoints 2.1–2.7. -/
theorem exists_isFraisseLimit_topFreeAge_omega (hext : StageType.HasCoatomExtensions.{u} ω) :
    ∃ (M : Bundled.{0} (hullLanguage.{u} ω).Structure) (_ : Countable M),
      IsFraisseLimit (topFreeAge.{u} ω) M :=
  exists_isFraisseLimit_topFreeAge hext Ordinal.isSuccLimit_omega0.isSuccPrelimit
    Ordinal.omega0_pos (Set.countable_coe_iff.mp countable_Iio_omega0_coe)

end VaughtConjecture
