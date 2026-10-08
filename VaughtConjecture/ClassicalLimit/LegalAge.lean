/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Receiving
import VaughtConjecture.Continuation.ExactAge
import VaughtConjecture.Extension.FamilyCofaces
import VaughtConjecture.Realization.CapToModel

/-!
# The age of legal charts and the countable saturated realization

Roadmap, the section "The intended construction: the finite age and its classical limit" (the
uncapped age of all legal stage types, whose classical limit is the countable saturated model, in
the paragraph on the chain construction); semantic contract, item 11.

**The age of legal charts** (the uncapped age).  A **legal index** at `α` (`LegalIndex α`) is a
legal stage type at `α` on finitely many points, and its **legal chart** (`legalChart α i`) is the
chart of the stage type, a finite structure of the hull language `hullLanguage α`.  The **age of
legal charts** (`legalAge α`) is their representative class; these three, and the inclusion of the
age of top-free charts (`topFreeAge_subset_legalAge`), are in
`VaughtConjecture.ClassicalLimit.Age`.  The age of legal charts is hereditary
(`exists_equiv_legalChart`, from `StageType.exists_equiv_comap`, with no hypothesis); under the
plain coatom extension property it has amalgamation (`exists_amalgam_legalChart`, the amalgam of
`StageType.exists_amalgam` itself, not capped, so the stage need not be a limit) and joint
embedding over the empty chart (`exists_jointEmbedding_legalChart`); when there are countably
many ordinals below `α` it is a Fraïssé class (`isFraisse_legalAge`) with a countable Fraïssé
limit (`exists_isFraisseLimit_legalAge`).  Unlike the age of top-free charts
(`VaughtConjecture.ClassicalLimit.Age`), it contains charts with cells labelled the formal top.

**Reconstruction for legal chart coverage.**  For a structure `M` of the hull language whose age
is contained in the age of legal charts, the reconstructed realization (`reconstruct α M`) is
exactly consistent and covering, and a typed tuple is the image of the points of its type under an
embedding of its chart (`isConsistent_reconstruct_of_legalAge`,
`isCovering_reconstruct_of_legalAge`, `exists_embedding_of_reconstruct_eval_of_legalAge`, in
`VaughtConjecture.ClassicalLimit.Reconstruction`, where the statements under top-free chart
coverage are their case).  Conversely, when the age of legal charts is contained in the age of `M`,
every legal stage type is the reconstructed type of a cover
(`exists_covers_reconstruct_of_legalAge`), and the carrier is nonempty
(`nonempty_of_legalAge_subset`, the case of the age of top-free charts).

**Exact receiving** (`exactReceivingWithin_reconstruct_of_legalAge`).  When the age of `M` is the
age of legal charts and `M` is ultrahomogeneous, over a cover of `t` and for a legal `D` restricting
to `t` along `g`, the embedding of the chart of `t` extends along the chart embedding of `g` to an
embedding of the chart of `D`, whose points cover `D` and extend the root literally: exact
extension along a chart embedding (`exists_reconstruct_eval_eq_of_embedding`, in
`VaughtConjecture.ClassicalLimit.Receiving`, shared with exact extension of top-free donors).
Exact receiving of legal donors gives finite-cut receiving
(`Realization.ExactReceivingWithin.hasFiniteCutReceiving`, in
`VaughtConjecture.Continuation.ExactAge`).  The occurrence of every legal stage type comes from the
age equality alone (`exists_covers_reconstruct_of_legalAge`), not from receiving.

**Modelhood** (`isModel_reconstruct_of_legalAge`).  At a nonzero limit stage, the cap-to-model
theorem (`Realization.isModel_of_hasFiniteCutReceiving`) applies, the uniformity and dominance
instances being nonempty under the coatom extension property with apex.

**Not here.**  The capped amalgamation and the capped receiving of the age of top-free charts
(`VaughtConjecture.ClassicalLimit.Amalgamation`, `VaughtConjecture.ClassicalLimit.Receiving`)
are proved there: a top-free amalgam or donor is capped below the stage, which the age of legal
charts does not need.

## Placement

This file belongs to the section "The intended construction: the finite age and its classical
limit" of `roadmap/README.md`.

## References

Models are [Kni26, Definition 3.2.1]; the nonemptiness of the uniformity and dominance instances is
[Kni26, Lemmas 4.4.2 and 4.4.3]; the countable saturated model is [Kni26, Definition 4.1.1 and
Proposition 4.4.5].
-/

universe u

namespace VaughtConjecture

open FirstOrder Language Structure CategoryTheory Realization StageType

/-! ### The age of legal charts -/

namespace LegalIndex

variable (α : Ordinal.{u})

/-- The **empty chart**, as a legal index: the stage type on no points. -/
noncomputable def empty : LegalIndex.{u} α :=
  ⟨0, (TopFreeIndex.empty α).2.1, (TopFreeIndex.empty α).2.2.1⟩

/-- The legal one-point stage type with the bottom label, as a legal index. -/
noncomputable def point : LegalIndex.{u} α :=
  ⟨1, (TopFreeIndex.point α).2.1, (TopFreeIndex.point α).2.2.1⟩

instance : Nonempty (LegalIndex.{u} α) :=
  ⟨empty α⟩

variable {α}

/-- The empty chart is the face on no points of every legal chart. -/
theorem restrictFace_empty (i : LegalIndex.{u} α) (e : Fin 0 ↪ Fin i.1) :
    StageType.restrictFace e i.2.1 = some (empty α).2.1 := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (i.2.1.isSome_restrictFace_of_zero e)
  exact hp.trans (congrArg some (StageType.eq_of_zero _ _))

end LegalIndex

variable {α : Ordinal.{u}}

/-- **Countably many legal indices**, when there are countably many ordinals below the stage. -/
theorem countable_legalIndex (hα : (Set.Iio α).Countable) : Countable (LegalIndex.{u} α) := by
  have := StageType.countable hα
  infer_instance

/-- A legal chart is finite. -/
instance finite_legalChart (i : LegalIndex.{u} α) : Finite (legalChart α i) :=
  inferInstanceAs (Finite (Fin i.1))

/-- A legal chart is finitely generated. -/
theorem fg_legalChart (i : LegalIndex.{u} α) : Structure.FG (hullLanguage.{u} α) (legalChart α i) :=
  Structure.FG.of_finite

/-- **Substructures of legal charts are legal charts**: the chart of the restriction of the stage
type to the closed face of the points of the substructure (`StageType.exists_equiv_comap`). -/
theorem exists_equiv_legalChart (i : LegalIndex.{u} α)
    (S : (hullLanguage.{u} α).Substructure (legalChart α i)) (_ : S.FG) :
    ∃ j : LegalIndex.{u} α, Nonempty (S ≃[hullLanguage.{u} α] legalChart α j) := by
  obtain ⟨m, g, hg, -, hS⟩ := StageType.exists_equiv_comap i.2.2 S
  exact ⟨⟨m, i.2.1.comap g hg, i.2.2.comap g hg⟩, hS⟩

/-- **The age of legal charts is hereditary.** -/
theorem hereditary_legalAge : Hereditary (legalAge.{u} α) :=
  representativeClass_hereditary _ exists_equiv_legalChart

/-- **Amalgamation of legal charts**, from the coatom extension property: two embeddings of a legal
chart into legal charts are completed by embeddings into one legal chart to a literally commuting
square.  The amalgam is that of `StageType.exists_amalgam`, not capped; no hypothesis on the stage
is needed.

The coatom extension property `StageType.HasCoatomExtensions α` is a hypothesis here; it is compiled
at every stage that is zero or a limit (`StageType.hasApexCoatomExtensions`,
`StageType.hasCoatomExtensions`; statement (R6) of roadmap, Layer 3, 3.1, checkpoint 2.7). -/
theorem exists_amalgam_legalChart (hext : StageType.HasCoatomExtensions.{u} α)
    (i j k : LegalIndex.{u} α) (f : legalChart α i ↪[hullLanguage.{u} α] legalChart α j)
    (g : legalChart α i ↪[hullLanguage.{u} α] legalChart α k) :
    ∃ (l : LegalIndex.{u} α) (a : legalChart α j ↪[hullLanguage.{u} α] legalChart α l)
      (b : legalChart α k ↪[hullLanguage.{u} α] legalChart α l), a.comp f = b.comp g := by
  obtain ⟨e, he, rfl⟩ := StageType.exists_eq_chartEmbedding (P := i.2.1) (Q := j.2.1)
    (.inl i.2.2) f
  obtain ⟨e', he', rfl⟩ := StageType.exists_eq_chartEmbedding (P := i.2.1) (Q := k.2.1)
    (.inl i.2.2) g
  obtain ⟨N, Q, a, b, hQ, hQa, hQb, hab⟩ := StageType.exists_amalgam hext j.2.2 k.2.2 he he'
  refine ⟨⟨N, Q, hQ⟩, StageType.chartEmbedding hQa, StageType.chartEmbedding hQb, ?_⟩
  refine Embedding.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := i.2.1.toChart.surjective x
  have hy := DFunLike.congr_fun hab y
  simp only [Function.Embedding.trans_apply] at hy
  simp only [Embedding.comp_apply, StageType.chartEmbedding_toChart, hy]

/-- **Joint embedding of legal charts**, from the coatom extension property: the amalgamation of
two legal charts over the empty chart.

The coatom extension property `StageType.HasCoatomExtensions α` is a hypothesis here; it is compiled
at every stage that is zero or a limit (`StageType.hasApexCoatomExtensions`,
`StageType.hasCoatomExtensions`; statement (R6) of roadmap, Layer 3, 3.1, checkpoint 2.7). -/
theorem exists_jointEmbedding_legalChart (hext : StageType.HasCoatomExtensions.{u} α)
    (i j : LegalIndex.{u} α) :
    ∃ k, Nonempty (legalChart α i ↪[hullLanguage.{u} α] legalChart α k) ∧
      Nonempty (legalChart α j ↪[hullLanguage.{u} α] legalChart α k) := by
  obtain ⟨l, a, b, -⟩ := exists_amalgam_legalChart hext (LegalIndex.empty α) i j
    (StageType.chartEmbedding (i.restrictFace_empty Function.Embedding.ofIsEmpty))
    (StageType.chartEmbedding (j.restrictFace_empty Function.Embedding.ofIsEmpty))
  exact ⟨l, ⟨a⟩, ⟨b⟩⟩

/-- **The age of legal charts is a Fraïssé class**, conditional on the coatom extension property,
when there are countably many ordinals below the stage.

The coatom extension property `StageType.HasCoatomExtensions α` is a hypothesis here; it is compiled
at every stage that is zero or a limit (`StageType.hasApexCoatomExtensions`,
`StageType.hasCoatomExtensions`; statement (R6) of roadmap, Layer 3, 3.1, checkpoint 2.7). -/
theorem isFraisse_legalAge (hext : StageType.HasCoatomExtensions.{u} α)
    (hcount : (Set.Iio α).Countable) : IsFraisse (legalAge.{u} α) :=
  haveI := countable_legalIndex hcount
  isFraisse_representativeClass _ fg_legalChart exists_equiv_legalChart
    (exists_jointEmbedding_legalChart hext) (exists_amalgam_legalChart hext)

/-- **A Fraïssé limit of the age of legal charts**, conditional on the coatom extension property,
when there are countably many ordinals below the stage: the classical existence theorem
`exists_isFraisseLimit_representativeClass`.

The coatom extension property `StageType.HasCoatomExtensions α` is a hypothesis here; it is compiled
at every stage that is zero or a limit (`StageType.hasApexCoatomExtensions`,
`StageType.hasCoatomExtensions`; statement (R6) of roadmap, Layer 3, 3.1, checkpoint 2.7). -/
theorem exists_isFraisseLimit_legalAge (hext : StageType.HasCoatomExtensions.{u} α)
    (hcount : (Set.Iio α).Countable) :
    letI := hullLanguage.countable_functions hcount
    ∃ (M : Bundled.{0} (hullLanguage.{u} α).Structure) (_ : Countable M),
      IsFraisseLimit (legalAge.{u} α) M :=
  letI := hullLanguage.countable_functions hcount
  haveI := countable_legalIndex hcount
  exists_isFraisseLimit_representativeClass _ fg_legalChart exists_equiv_legalChart
    (exists_jointEmbedding_legalChart hext) (exists_amalgam_legalChart hext)

/-! ### Occurrence and exact receiving in a limit -/

section Limit

variable {M : Type} [(hullLanguage.{u} α).Structure M]

/-- **Every legal stage type occurs**: if the age of legal charts is contained in the age of `M`,
every legal stage type is the reconstructed type of a cover. -/
theorem exists_covers_reconstruct_of_legalAge (h : legalAge α ⊆ (hullLanguage.{u} α).age M)
    {n : ℕ} {p : StageType.{u} α n} (hp : p.IsLegal) :
    ∃ c : Fin n → M, (reconstruct α M).Covers p c := by
  obtain ⟨-, ⟨φ⟩⟩ := h (legalChart_mem_legalAge ⟨n, p, hp⟩)
  exact ⟨_, covers_of_eval _ (reconstruct_eval_chart hp φ)⟩

/-- **A nonempty carrier**: if the age of legal charts is contained in the age of `M`, the
one-point chart embeds in `M`. -/
theorem nonempty_of_legalAge_subset (h : legalAge α ⊆ (hullLanguage.{u} α).age M) :
    Nonempty M :=
  nonempty_of_topFreeAge_subset (topFreeAge_subset_legalAge.trans h)

/-- **Exact receiving of legal donors**: for a structure whose age is the age of legal charts and
which is ultrahomogeneous, over every cover of a stage type `t`, every legal stage type `D`
restricting to `t` along `g` is the type of a cover extending the root along `g` literally: exact
extension along the embedding of the chart of `t` (`exists_reconstruct_eval_eq_of_embedding`).  No
hypothesis on the stage is needed. -/
theorem exactReceivingWithin_reconstruct_of_legalAge
    (hage : (hullLanguage.{u} α).age M = legalAge α)
    (hu : (hullLanguage.{u} α).IsUltrahomogeneous M) :
    (reconstruct α M).ExactReceivingWithin fun m ↦ {D : StageType.{u} α m | D.IsLegal} := by
  intro n m t c hc D g hD hg
  obtain ⟨φ, hφ⟩ := exists_embedding_of_reconstruct_eval_of_legalAge hage.subset hc.eval_eq
  have hmem : legalChart α ⟨m, D, hD⟩ ∈ (hullLanguage.{u} α).age M :=
    hage ▸ legalChart_mem_legalAge _
  obtain ⟨v, hv, hvD⟩ := exists_reconstruct_eval_eq_of_embedding hu φ hφ hD hmem.2 hg
  exact ⟨v, covers_of_eval _ hvD, funext fun j ↦ DFunLike.congr_fun hv j⟩

end Limit

/-! ### Modelhood from exact receiving -/

/-- **Modelhood of the reconstruction of a limit of the age of legal charts**: for a structure whose
age is the age of legal charts and which is ultrahomogeneous, at a nonzero limit stage, the
reconstructed realization is a model, conditional on the coatom extension property with apex.
Finite-cut receiving comes from exact receiving, and the uniformity and dominance instances from
the coatom extension property with apex (`StageType.nonempty_cofaces_inter_uniformityFamily`,
`StageType.nonempty_cofaces_inter_dominanceFamily`).

The coatom extension property with apex `StageType.HasApexCoatomExtensions α` is a hypothesis here;
it is compiled at every stage that is zero or a limit (`StageType.hasApexCoatomExtensions`,
`StageType.hasCoatomExtensions`; statement (R6) of roadmap, Layer 3, 3.1, checkpoint 2.7). -/
theorem isModel_reconstruct_of_legalAge {M : Type} [(hullLanguage.{u} α).Structure M]
    (hext : StageType.HasApexCoatomExtensions.{u} α)
    (hage : (hullLanguage.{u} α).age M = legalAge α)
    (hu : (hullLanguage.{u} α).IsUltrahomogeneous M) (hα : Order.IsSuccLimit α) :
    (reconstruct α M).IsModel :=
  isModel_of_hasFiniteCutReceiving hα (nonempty_of_legalAge_subset hage.symm.subset)
    hasLegalTypes_reconstruct (isConsistent_reconstruct_of_legalAge hage.subset)
    (isCovering_reconstruct_of_legalAge hage.subset)
    (exactReceivingWithin_reconstruct_of_legalAge hage hu).hasFiniteCutReceiving
    (fun x _ _ hγα ↦ nonempty_cofaces_inter_uniformityFamily hext.hasCoatomExtensions
      hα.isSuccPrelimit (hasLegalTypes_reconstruct _ _ x.eval_tuple) hγα)
    (fun x _ hγα ↦ nonempty_cofaces_inter_dominanceFamily hext hα.isSuccPrelimit
      (hasLegalTypes_reconstruct _ _ x.eval_tuple) hγα)

end VaughtConjecture
