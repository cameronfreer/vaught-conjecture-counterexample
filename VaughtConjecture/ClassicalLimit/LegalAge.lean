/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Amalgamation
import VaughtConjecture.ClassicalLimit.Reconstruction
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
legal charts** (`legalAge α`) is their representative class.  It is hereditary
(`exists_equiv_legalChart`, from `StageType.exists_equiv_comap`, with no hypothesis); under the
plain coatom extension property it has amalgamation (`exists_amalgam_legalChart`, the amalgam of
`StageType.exists_amalgam` itself, not capped, so the stage need not be a limit) and joint
embedding over the empty chart (`exists_jointEmbedding_legalChart`); when there are countably
many ordinals below `α` it is a Fraïssé class (`isFraisse_legalAge`) with a countable Fraïssé
limit (`exists_isFraisseLimit_legalAge`).  Unlike the age of top-free charts
(`VaughtConjecture.ClassicalLimit.Age`), it contains charts with cells labelled the formal top.

**Reconstruction for legal chart coverage.**  For a structure `M` of the hull language whose age
is contained in the age of legal charts, every injective tuple factors through an embedding of a
legal chart (`exists_eq_trans_legalChart`), so the reconstructed realization
(`reconstruct α M`, `VaughtConjecture.ClassicalLimit.Reconstruction`) is exactly consistent and
covering (`isConsistent_reconstruct_of_legalAge`, `isCovering_reconstruct_of_legalAge`), and a
typed tuple is the image of the points of its type under an embedding of its chart
(`exists_embedding_of_reconstruct_eval_of_legalAge`).  The proofs are those of the top-free case,
read in a legal chart.  Conversely, when the age of legal charts is contained in the age of `M`,
every legal stage type is the reconstructed type of a cover
(`exists_covers_reconstruct_of_legalAge`).

**Exact receiving** (`exactReceivingWithin_reconstruct_of_legalAge`).  When the age of `M` is the
age of legal charts and `M` is ultrahomogeneous, over a cover of `t` and for a legal `D` restricting
to `t` along `g`, the embedding of the chart of `t` extends along the chart embedding of `g` to an
embedding of the chart of `D` (`FirstOrder.Language.IsUltrahomogeneous.extend_embedding`), whose
points cover `D` and extend the root literally.  Exact receiving of legal donors gives finite-cut
receiving (`Realization.ExactReceivingWithin.hasFiniteCutReceiving`: the donor is in each of its
receiving families).  The occurrence of every legal stage type comes from the age equality alone
(`exists_covers_reconstruct_of_legalAge`), not from receiving.

**Modelhood** (`isModel_reconstruct_of_legalAge`).  At a nonzero limit stage, the cap-to-model
theorem (`Realization.isModel_of_hasFiniteCutReceiving`) applies, the uniformity and dominance
instances being nonempty under the coatom extension property with apex.

**Not here.**  The top-free statements of `VaughtConjecture.ClassicalLimit` are not yet derived as
the case of the subfamily of top-free legal charts; the legal statements re-prove them.

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

/-- A **legal index** at stage `α`: a legal stage type at stage `α` on some finite number of
points. -/
abbrev LegalIndex (α : Ordinal.{u}) : Type (u + 1) :=
  Σ k : ℕ, {P : StageType.{u} α k // P.IsLegal}

/-- The **legal chart** of a legal index: the chart of its stage type, a finite structure of the
hull language, bundled in `Type`. -/
noncomputable abbrev legalChart (α : Ordinal.{u}) (i : LegalIndex.{u} α) :
    Bundled.{0} (hullLanguage.{u} α).Structure :=
  ⟨i.2.1.Chart, inferInstance⟩

/-- The **age of legal charts** at stage `α`: the structures of the hull language isomorphic to a
legal chart. -/
def legalAge (α : Ordinal.{u}) : Set (Bundled.{0} (hullLanguage.{u} α).Structure) :=
  representativeClass (legalChart α)

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

/-- A legal chart belongs to the age of legal charts. -/
theorem legalChart_mem_legalAge (i : LegalIndex.{u} α) : legalChart α i ∈ legalAge α :=
  mem_representativeClass _ i

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

The coatom extension property `StageType.HasCoatomExtensions α` is not proved here: it is the open
part of statement (R6) of roadmap, Layer 3, 3.1. -/
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

The coatom extension property `StageType.HasCoatomExtensions α` is not proved here: it is the open
part of statement (R6) of roadmap, Layer 3, 3.1. -/
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

The coatom extension property `StageType.HasCoatomExtensions α` is not proved here: it is the open
part of statement (R6) of roadmap, Layer 3, 3.1. -/
theorem isFraisse_legalAge (hext : StageType.HasCoatomExtensions.{u} α)
    (hcount : (Set.Iio α).Countable) : IsFraisse (legalAge.{u} α) :=
  haveI := countable_legalIndex hcount
  isFraisse_representativeClass _ fg_legalChart exists_equiv_legalChart
    (exists_jointEmbedding_legalChart hext) (exists_amalgam_legalChart hext)

/-- **A Fraïssé limit of the age of legal charts**, conditional on the coatom extension property,
when there are countably many ordinals below the stage: the classical existence theorem
`exists_isFraisseLimit_representativeClass`.

The coatom extension property `StageType.HasCoatomExtensions α` is not proved here: it is the open
part of statement (R6) of roadmap, Layer 3, 3.1. -/
theorem exists_isFraisseLimit_legalAge (hext : StageType.HasCoatomExtensions.{u} α)
    (hcount : (Set.Iio α).Countable) :
    letI := hullLanguage.countable_functions hcount
    ∃ (M : Bundled.{0} (hullLanguage.{u} α).Structure) (_ : Countable M),
      IsFraisseLimit (legalAge.{u} α) M :=
  letI := hullLanguage.countable_functions hcount
  haveI := countable_legalIndex hcount
  exists_isFraisseLimit_representativeClass _ fg_legalChart exists_equiv_legalChart
    (exists_jointEmbedding_legalChart hext) (exists_amalgam_legalChart hext)

/-! ### Reconstruction under legal chart coverage -/

section Coverage

variable {M : Type} [(hullLanguage.{u} α).Structure M] {n : ℕ}
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

end Coverage

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
    Nonempty M := by
  obtain ⟨c, -⟩ := exists_covers_reconstruct_of_legalAge h (LegalIndex.point α).2.2
  exact ⟨c ⟨0, Nat.one_pos⟩⟩

/-- **Exact receiving of legal donors**: for a structure whose age is the age of legal charts and
which is ultrahomogeneous, over every cover of a stage type `t`, every legal stage type `D`
restricting to `t` along `g` is the type of a cover extending the root along `g` literally.  The
embedding of the chart of `t` extends along the chart embedding of `g`
(`IsUltrahomogeneous.extend_embedding`).  No hypothesis on the stage is needed. -/
theorem exactReceivingWithin_reconstruct_of_legalAge
    (hage : (hullLanguage.{u} α).age M = legalAge α)
    (hu : (hullLanguage.{u} α).IsUltrahomogeneous M) :
    (reconstruct α M).ExactReceivingWithin fun m ↦ {D : StageType.{u} α m | D.IsLegal} := by
  intro n m t c hc D g hD hg
  obtain ⟨φ, hφ⟩ := exists_embedding_of_reconstruct_eval_of_legalAge hage.subset hc.eval_eq
  have hmem : legalChart α ⟨m, D, hD⟩ ∈ (hullLanguage.{u} α).age M :=
    hage ▸ legalChart_mem_legalAge _
  have : Nonempty (D.Chart ↪[hullLanguage.{u} α] M) := hmem.2
  obtain ⟨ψ, hψ⟩ := hu.extend_embedding (S := t.Chart) (Structure.FG.of_finite) φ
    (StageType.chartEmbedding hg)
  refine ⟨D.toChart.toEmbedding.trans ψ.toEmbedding,
    covers_of_eval _ (reconstruct_eval_chart hD ψ), funext fun j ↦ ?_⟩
  -- the chart embedding along `g` sends the point `j` of `t` to the point `g j` of `D`
  have hj := hφ j
  rw [hψ] at hj
  exact hj

end Limit

/-! ### Receiving and modelhood from exact receiving -/

namespace Realization

variable {M : Type*} {R : Realization.{u, _} α M}

/-- **Exact receiving of legal donors gives finite-cut receiving**: the donor itself is received,
and it lies in each of its receiving families. -/
theorem ExactReceivingWithin.hasFiniteCutReceiving
    (h : R.ExactReceivingWithin fun m ↦ {D : StageType.{u} α m | D.IsLegal}) :
    R.HasFiniteCutReceiving := by
  intro x d hd c _
  obtain ⟨u, hu, hug⟩ := h x.type x.tuple (covers_of_eval _ x.eval_tuple) d Fin.castSuccEmb hd.1
    hd.2
  exact ⟨⟨u, hu.injective⟩, Function.Embedding.ext (congrFun hug), d,
    self_mem_receivingFamily d c, hu.eval_eq⟩

end Realization

/-- **Modelhood of the reconstruction of a limit of the age of legal charts**: for a structure whose
age is the age of legal charts and which is ultrahomogeneous, at a nonzero limit stage, the
reconstructed realization is a model, conditional on the coatom extension property with apex.
Finite-cut receiving comes from exact receiving, and the uniformity and dominance instances from
the coatom extension property with apex (`StageType.nonempty_cofaces_inter_uniformityFamily`,
`StageType.nonempty_cofaces_inter_dominanceFamily`).

The coatom extension property with apex `StageType.HasApexCoatomExtensions α` is not proved here:
it is the open part of statement (R6) of roadmap, Layer 3, 3.1. -/
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
