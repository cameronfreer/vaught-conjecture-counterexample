/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Amalgamation
import VaughtConjecture.ClassicalLimit.Reconstruction
import VaughtConjecture.Continuation.ExactAge
import VaughtConjecture.Continuation.Hollow
import VaughtConjecture.Continuation.Terminal
import VaughtConjecture.Extension.FamilyCofaces
import VaughtConjecture.Realization.CapToModel

/-!
# Same-level maximal realization

Roadmap, the section "Reduction to full presentations" (acceptance lemma 1, the same-level
maximal realization) and the section "The intended construction: the finite age and its
classical limit" (the uncapped age of all legal stage types, whose classical limit is the
countable saturated model).

Throughout, `λ_β = blockStage β` is the block stage of a countable `β`, and `λ_{β+1}` is the next
one.  **Acceptance lemma 1** (`exists_sameLevelMaximal`): on every countably infinite carrier
`X` there is a realization `H` at `λ_β` that

* is a model (`Realization.IsModel`);
* realizes every legal stage type at `λ_β` (`Realization.Covers`);
* has exact receiving of every legal donor over every actual root
  (`Realization.ExactReceivingWithin` for the family of all legal stage types), the received type
  being the donor itself, with no cutoff;
* is cover-hollow (`Realization.IsCoverHollow`) and terminal at `β` (`Realization.IsTerminalAt`):
  no model at `λ_{β+1}` on `X` reduces to it.

The strengthening on a prescribed tuple (`exists_sameLevelMaximal_covers`): for a legal stage
type `p` on `n` points and an injective tuple `a` of `X`, `H` can be chosen with `a` a cover of
`p`.

Without terminality, the countable saturated realization (`exists_saturated_reconstruct`: a model
realizing every legal stage type, with exact receiving of legal donors) needs only the first of
the two hypotheses below.  Acceptance lemma 1 is conditional on two named hypotheses, each still
to be proved:

* `StageType.HasApexCoatomExtensions (blockStage β)`, the coatom extension property with apex at
  `λ_β` (Layer 3, 3.1, the open part of (R6)).  Its plain form gives the amalgamation of legal
  stage types, hence the classical limit of the age of all legal charts; the apex gives the
  dominance instances of modelhood ([Kni26, Lemma 4.4.3]).
* `ForcingDonors β` (`VaughtConjecture.Continuation.Normalization`; Layer 4, output 2).  It is
  used only at legal stage types at `λ_{β+1}` that are stage types at `λ_β` read at `λ_{β+1}`
  (`StageType.castLE`): at a cell labelled the formal top, every threshold is forced by some legal
  extension (`StageType.exists_forcesThreshold_of_label_eq_top`).

Neither the continuation criterion (`ContinuationCriterion`), nor finite-cut receiving of models
((R1), `Expansion.FiniteCutReceiving`), nor uniqueness of expansions, nor global termination is
used.  The continuation criterion concerns realizations that are *not* cover-hollow, and makes
them continue; terminality of a cover-hollow realization is proved here directly, with no
hypothesis.

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
read in a legal chart.

**Exact receiving** (`exactReceivingWithin_reconstruct_of_legalAge`).  When the age of `M` is the
age of legal charts and `M` is ultrahomogeneous, over a cover of `t` and for a legal `D` restricting
to `t` along `g`, the embedding of the chart of `t` extends along the chart embedding of `g` to an
embedding of the chart of `D` (`FirstOrder.Language.IsUltrahomogeneous.extend_embedding`), whose
points cover `D` and extend the root literally.  Exact receiving of legal donors gives finite-cut
receiving (`Realization.ExactReceivingWithin.hasFiniteCutReceiving`: the donor is in each of its
receiving families) and the occurrence of every legal stage type
(`exists_covers_reconstruct_of_legalAge`).

**Modelhood** (`isModel_reconstruct_of_legalAge`).  At a nonzero limit stage, the cap-to-model
theorem (`Realization.isModel_of_hasFiniteCutReceiving`) applies, the uniformity and dominance
instances being nonempty under the coatom extension property with apex.

**Cover-hollowness** (`Realization.isCoverHollow_of_exactReceivingWithin`).  A realization at
`λ_β` with legal types and exact receiving of legal donors is cover-hollow under `ForcingDonors β`:
for a cell `a` labelled the formal top in an occurrence `x` and a bound `N`, the extension of the
type of `x` forcing `N` at `a` is received over `x`, so `(x, a, N)` is not an anchor at the top.

**Terminality of cover-hollow realizations** (`Realization.IsCoverHollow.isTerminalAt`), with no
hypothesis.  Let `R'` be a model at `λ_{β+1}` reducing to a cover-hollow `R`.  Uniformity of `R'`
at `γ = λ_β` gives a cover `u` of a type `q` with a label `λ_β + m` at some cell `d`, which is the
formal top in the reduction.  Since `R` has no anchor at the top, some rooted cover of `u` in `R`
forces the threshold `m + 1` at `d`, and soundness
(`Realization.Covers.le_label_of_forcesThreshold`, from exact consistency of `R'` alone) gives
`λ_β + (m + 1) ≤ λ_β + m`.  So every label of a cover-hollow realization that is the formal top
stays the formal top in any model reducing to it, and uniformity at `λ_β` fails.

**Countability and the carrier.**  The limit is countable (classical existence) and infinite
(`Realization.IsModel.infinite`), so it is in bijection with any countably infinite `X`, and
every property above is invariant under transport along a bijection of carriers
(`Realization.isModel_map_iff`, `Realization.exactReceivingWithin_map_iff`,
`Realization.covers_map_iff`; for cover-hollowness and terminality, the theorems of this file
apply to the transport directly).  For the prescribed tuple, the bijection is chosen to carry a
cover of `p` in the limit to `a`: the complements of two finite sets in countably infinite types
are countably infinite.

**Not here.**  Unbounded top-grade growth (`Realization.topGradeSup = ⊤`) of the realization is
not proved and not used: it needs legal stage types of arbitrarily large top grade.  Nothing here
identifies the base reduct of `H` or places it in a successor loss of the expansion domains;
that needs uniqueness of model expansions at `λ_β` (Layer 5).

## Placement

This file belongs to the section "Reduction to full presentations" of `roadmap/README.md`.

## References

Models are [Kni26, Definition 3.2.1]; the nonemptiness of the uniformity and dominance instances is
[Kni26, Lemmas 4.4.2 and 4.4.3]; the countable saturated model is [Kni26, Definition 4.1.1 and
Proposition 4.4.5].
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Finset CategoryTheory Realization StageType
open scoped Ordinal

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

/-! ### Forcing every threshold at a top cell -/

namespace StageType

/-- **Forcing along an equality of roots**: a threshold forced at a cell of `p` is forced at the
cell of the same position of a stage type equal to `p`. -/
theorem ForcesThreshold.congr_root {α β : Ordinal.{u}} {hβ : Order.IsSuccPrelimit β} {m k : ℕ}
    {q : StageType.{u} β m} {f : Fin k ↪ Fin m} {p p' : StageType.{u} β k} {d : Fin p.card}
    {n : ℕ} (h : ForcesThreshold α hβ q f p d n) (hp : p = p') (d' : Fin p'.card)
    (hd : (d : ℕ) = d') : ForcesThreshold α hβ q f p' d' n := by
  subst hp
  obtain rfl : d = d' := Fin.ext hd
  exact h

/-- **Every threshold at a top cell is forced by a legal extension**, conditional on forcing donors
at `η`: for a legal stage type `p` at `λ_η` with a cell `d` labelled the formal top and every `n`,
some legal stage type `D` at `λ_η` restricts to `p` along some `g`, and `(D, g)` forces the
threshold `n` at `d`.  Forcing donors is applied to `p` read at `λ_{η+1}` (`StageType.castLE`),
where the label of `d` is still the formal top, so every threshold is below it.

Forcing donors `ForcingDonors η` is not proved here: it is a finite statement of Layer 4,
output 2, still to be proved. -/
theorem exists_forcesThreshold_of_label_eq_top {η : Ordinal.{u}} (hF : ForcingDonors.{u} η)
    {k : ℕ} {p : StageType.{u} (blockStage η) k} (hp : p.IsLegal) {d : Fin p.card}
    (hd : p.label d = ⊤) (n : ℕ) :
    ∃ (m : ℕ) (D : StageType.{u} (blockStage η) m) (g : Fin k ↪ Fin m), D.IsLegal ∧
      restrictFace g D = some p ∧
        ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η) D g p d n := by
  have hle := (blockStage_lt_blockStage_add_one η).le
  have hβ := isSuccPrelimit_blockStage η
  have hp' : (p.castLE hle).reduce hβ = p := reduce_eq_castLE p hβ le_rfl
  have htop : ((p.castLE hle).reduce hβ).label d = ⊤ :=
    Label.reduce_of_le (by rw [castLE_label, hd]; exact le_top)
  obtain ⟨m, D, g, hD, hDg, hforce⟩ := hF (p.castLE hle) ((isLegal_castLE_iff p hle).mpr hp) d
    htop n (by rw [castLE_label, hd]; exact le_top)
  refine ⟨m, D.reduce hβ, g, hD.reduce hβ, ?_, hforce.congr_root hp' d rfl⟩
  rw [restrictFace_reduce, hDg, Option.map_some, hp']

end StageType

/-! ### Cover-hollowness and terminality -/

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type*} {R : Realization.{u, _} (blockStage ξ) M}

/-- **Exact receiving of legal donors makes a realization cover-hollow**, conditional on forcing
donors at `ξ`: at a cell `a` labelled the formal top in an occurrence `x`, every bound `N` is
forced by a legal extension of the type of `x`
(`StageType.exists_forcesThreshold_of_label_eq_top`), which is received over `x`, so `(x, a, N)`
is not an anchor at the top.

Forcing donors `ForcingDonors ξ` is not proved here: it is a finite statement of Layer 4,
output 2, still to be proved. -/
theorem isCoverHollow_of_exactReceivingWithin (hF : ForcingDonors.{u} ξ) (hl : R.HasLegalTypes)
    (h : R.ExactReceivingWithin fun m ↦ {D : StageType.{u} (blockStage ξ) m | D.IsLegal}) :
    R.IsCoverHollow := by
  rintro ⟨x, a, N, ha, hno⟩
  obtain ⟨m, D, g, hD, hDg, hforce⟩ :=
    StageType.exists_forcesThreshold_of_label_eq_top hF (hl _ _ x.eval_tuple) ha N
  obtain ⟨v, hv, hvg⟩ := h x.type x.tuple (covers_of_eval _ x.eval_tuple) D g hD hDg
  exact hno ⟨m, D, g⟩ ⟨v, hvg, hv⟩ hforce

/-- A label in the block `[β, β + ω)` is below `β + n` for some `n`. -/
private theorem exists_lt_coe_add_of_lt_coe_add_omega0 {β : Ordinal.{u}} {L : Label.{u}}
    (h₁ : (β : Label.{u}) ≤ L) (h₂ : L < ((β + ω : Ordinal.{u}) : Label.{u})) :
    ∃ n : ℕ, L < ((β + n : Ordinal.{u}) : Label.{u}) := by
  induction L using WithBot.recBotCoe with
  | bot => exact absurd h₁ (not_le.mpr (WithBot.bot_lt_coe _))
  | coe L =>
    induction L using WithTop.recTopCoe with
    | top => exact absurd h₂ (not_lt.mpr (WithBot.coe_le_coe.mpr le_top))
    | coe o =>
      have ho : o < β + ω := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h₂)
      obtain ⟨c, hc, hoc⟩ := (Ordinal.lt_add_iff Ordinal.omega0_ne_zero).mp ho
      obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hc
      refine ⟨n + 1, WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (hoc.trans_lt ?_))⟩
      exact add_lt_add_right (by exact_mod_cast Nat.lt_succ_self n) β

/-- **Cover-hollow realizations are terminal**, with no hypothesis: no model at `λ_{ξ+1}` reduces
to a cover-hollow realization at `λ_ξ`.  Uniformity of such a model `R'` at `γ = λ_ξ` gives a cover
of a type with a label `L` in `[λ_ξ, λ_ξ + ω)` at a cell that is the formal top in the reduction;
cover-hollowness gives, for every `N`, a rooted cover forcing `N` there, and soundness
(`Realization.Covers.le_label_of_forcesThreshold`, from exact consistency of `R'`) gives
`λ_ξ + N ≤ L` for every `N`, which is impossible. -/
theorem IsCoverHollow.isTerminalAt (h : R.IsCoverHollow) : R.IsTerminalAt ξ := by
  intro R' hR' hred
  have hβ := isSuccPrelimit_blockStage ξ
  obtain ⟨x⟩ := hR'.nonempty_occurrence
  obtain ⟨u, -, q, ⟨d, h₁, h₂⟩, hq⟩ :=
    hR'.uniformity x _ hβ (blockStage_lt_blockStage_add_one ξ)
  let y : R.Occurrence := ⟨_, u, q.reduce hβ, by rw [← hred, reduce_eval, hq, Option.map_some]⟩
  obtain ⟨N, hN⟩ := exists_lt_coe_add_of_lt_coe_add_omega0 h₁ h₂
  have hnot : ¬ R.IsTopAnchor y d N := fun hy ↦ h ⟨y, d, N, hy⟩
  simp only [IsTopAnchor, not_and, not_forall, not_not] at hnot
  obtain ⟨z, hz, hforce⟩ := hnot (Label.reduce_of_le h₁)
  have hle := Covers.le_label_of_forcesThreshold hR'.isConsistent hβ (covers_of_eval u hq) hforce
    (hred ▸ hz)
  exact hle.not_gt hN

/-- **Terminality is invariant under transport** along a bijection of carriers. -/
theorem IsTerminalAt.map {N : Type*} (h : R.IsTerminalAt ξ) (e : M ≃ N) :
    (R.map e).IsTerminalAt ξ := by
  intro R' hR' hred
  refine h (R'.map e.symm) ((isModel_map_iff e.symm).mpr hR') ?_
  rw [reduce_map, hred, map_symm_map]

end Realization

/-! ### Acceptance lemma 1 -/

/-- **The countable saturated realization at a block stage**, conditional on the coatom extension
property with apex at `λ_β`: for a countable `β`, some countable structure `M` of the hull language
at `λ_β` has a reconstructed realization that is a model, realizes every legal stage type at
`λ_β`, and has exact receiving of every legal donor.  `M` is a Fraïssé limit of the age of legal
charts.

The coatom extension property with apex `StageType.HasApexCoatomExtensions (blockStage β)` is
still to be proved: it is the open part of statement (R6) of roadmap, Layer 3, 3.1. -/
theorem exists_saturated_reconstruct {β : Ordinal.{0}} (hβ : β < ω₁)
    (hext : StageType.HasApexCoatomExtensions.{0} (blockStage β)) :
    ∃ (M : Type) (_ : (hullLanguage.{0} (blockStage β)).Structure M), Countable M ∧
      (reconstruct (blockStage β) M).IsModel ∧
      (∀ ⦃n : ℕ⦄ (p : StageType.{0} (blockStage β) n), p.IsLegal →
        ∃ c : Fin n → M, (reconstruct (blockStage β) M).Covers p c) ∧
      (reconstruct (blockStage β) M).ExactReceivingWithin
        (fun m ↦ {D : StageType.{0} (blockStage β) m | D.IsLegal}) := by
  have hcount := Cardinal.countable_Iio_of_lt_omega_one (blockStage_lt_omega_one hβ)
  let := hullLanguage.countable_functions hcount
  obtain ⟨M, hMc, hM⟩ := exists_isFraisseLimit_legalAge hext.hasCoatomExtensions hcount
  exact ⟨M, inferInstance, hMc,
    isModel_reconstruct_of_legalAge hext hM.age hM.ultrahomogeneous (isSuccLimit_blockStage β),
    fun _ _ hp ↦ exists_covers_reconstruct_of_legalAge hM.age.symm.subset hp,
    exactReceivingWithin_reconstruct_of_legalAge hM.age hM.ultrahomogeneous⟩

/-- **The same-level maximal realization on the carrier of a classical limit**, conditional on the
coatom extension property with apex at `λ_β` and on forcing donors at `β`: the countable saturated
realization of `exists_saturated_reconstruct` is moreover cover-hollow
(`Realization.isCoverHollow_of_exactReceivingWithin`) and terminal at `β`
(`Realization.IsCoverHollow.isTerminalAt`).

Both hypotheses are still to be proved: `StageType.HasApexCoatomExtensions (blockStage β)` is the
open part of statement (R6) of roadmap, Layer 3, 3.1; `ForcingDonors β` is a finite statement of
Layer 4, output 2. -/
theorem exists_sameLevelMaximal_reconstruct {β : Ordinal.{0}} (hβ : β < ω₁)
    (hext : StageType.HasApexCoatomExtensions.{0} (blockStage β)) (hF : ForcingDonors.{0} β) :
    ∃ (M : Type) (_ : (hullLanguage.{0} (blockStage β)).Structure M), Countable M ∧
      (reconstruct (blockStage β) M).IsModel ∧
      (∀ ⦃n : ℕ⦄ (p : StageType.{0} (blockStage β) n), p.IsLegal →
        ∃ c : Fin n → M, (reconstruct (blockStage β) M).Covers p c) ∧
      (reconstruct (blockStage β) M).ExactReceivingWithin
        (fun m ↦ {D : StageType.{0} (blockStage β) m | D.IsLegal}) ∧
      (reconstruct (blockStage β) M).IsCoverHollow ∧
      (reconstruct (blockStage β) M).IsTerminalAt β := by
  obtain ⟨M, _, hMc, hmod, hocc, hrec⟩ := exists_saturated_reconstruct hβ hext
  have hhol := isCoverHollow_of_exactReceivingWithin hF hasLegalTypes_reconstruct hrec
  exact ⟨M, inferInstance, hMc, hmod, hocc, hrec, hhol, hhol.isTerminalAt⟩

/-- **A bijection of countably infinite types extending a finite injection**: two injective tuples
of the same length in countably infinite types are matched by a bijection.  The complements of
their ranges are countably infinite. -/
theorem exists_equiv_extend_tuple {M X : Type v} [Countable M] [Infinite M] [Countable X]
    [Infinite X] {n : ℕ} (c : Fin n ↪ M) (a : Fin n ↪ X) : ∃ e : M ≃ X, ∀ i, e (c i) = a i := by
  classical
  let e₁ : {x // x ∈ Set.range c} ≃ {x // x ∈ Set.range a} :=
    (Equiv.ofInjective c c.injective).symm.trans (Equiv.ofInjective a a.injective)
  have : Infinite {x // x ∉ Set.range c} := (Set.finite_range c).infinite_compl.to_subtype
  have : Infinite {x // x ∉ Set.range a} := (Set.finite_range a).infinite_compl.to_subtype
  obtain ⟨e₂⟩ : Nonempty ({x // x ∉ Set.range c} ≃ {x // x ∉ Set.range a}) :=
    Cardinal.eq.mp ((Cardinal.mk_eq_aleph0 _).trans (Cardinal.mk_eq_aleph0 _).symm)
  refine ⟨(Equiv.sumCompl _).symm.trans ((Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl _)),
    fun i ↦ ?_⟩
  simp [Equiv.sumCompl_symm_apply_of_pos (p := (· ∈ Set.range c)) ⟨i, rfl⟩, e₁,
    Equiv.ofInjective_symm_apply]

/-- **Acceptance lemma 1, the same-level maximal realization**, conditional on the coatom
extension property with apex at `λ_β` and on forcing donors at `β`: for a countable `β` and every
countably infinite carrier `X`, some realization `H` at `λ_β = blockStage β` on `X`

* is a model;
* realizes every legal stage type at `λ_β`;
* has exact receiving of every legal donor over every actual root (the received type is the donor
  itself, with no cutoff);
* is cover-hollow and terminal at `β`: no model at `λ_{β+1}` on `X` reduces to it.

It is the transport to `X` of the reconstruction of a Fraïssé limit of the age of legal charts
(`exists_sameLevelMaximal_reconstruct`).

Both hypotheses are still to be proved: `StageType.HasApexCoatomExtensions (blockStage β)` is the
open part of statement (R6) of roadmap, Layer 3, 3.1; `ForcingDonors β` is a finite statement of
Layer 4, output 2. -/
theorem exists_sameLevelMaximal_covers {β : Ordinal.{0}} (hβ : β < ω₁)
    (hext : StageType.HasApexCoatomExtensions.{0} (blockStage β)) (hF : ForcingDonors.{0} β)
    (X : Type) [Countable X] [Infinite X] {n : ℕ} {p : StageType.{0} (blockStage β) n}
    (hp : p.IsLegal) (a : Fin n ↪ X) :
    ∃ H : Realization.{0, 0} (blockStage β) X, H.IsModel ∧ H.Covers p a ∧
      (∀ ⦃n : ℕ⦄ (p : StageType.{0} (blockStage β) n), p.IsLegal → ∃ c : Fin n → X, H.Covers p c) ∧
      H.ExactReceivingWithin (fun m ↦ {D : StageType.{0} (blockStage β) m | D.IsLegal}) ∧
      H.IsCoverHollow ∧ H.IsTerminalAt β := by
  obtain ⟨M, _, hMc, hmod, hocc, hrec, -, -⟩ := exists_sameLevelMaximal_reconstruct hβ hext hF
  have := hMc
  have := hmod.infinite (Ordinal.omega0_pos.trans_le (omega0_le_blockStage β))
  obtain ⟨c, hc⟩ := hocc p hp
  obtain ⟨e, he⟩ := exists_equiv_extend_tuple ⟨c, hc.injective⟩ a
  have hmod' := (isModel_map_iff e).mpr hmod
  have hrec' := (exactReceivingWithin_map_iff e).mpr hrec
  have hhol := isCoverHollow_of_exactReceivingWithin hF hmod'.hasLegalTypes hrec'
  have hcov (n : ℕ) (q : StageType.{0} (blockStage β) n) (c' : Fin n → M)
      (hq : (reconstruct (blockStage β) M).Covers q c') :
      ((reconstruct (blockStage β) M).map e).Covers q (e ∘ c') :=
    (covers_map_iff e).mpr (by simpa [Function.comp_def] using hq)
  refine ⟨_, hmod', ?_, fun n q hq ↦ ?_, hrec', hhol, hhol.isTerminalAt⟩
  · have ha : e ∘ c = a := funext he
    exact ha ▸ hcov n p c hc
  · obtain ⟨c', hc'⟩ := hocc q hq
    exact ⟨_, hcov n q c' hc'⟩

/-- **Acceptance lemma 1, the same-level maximal realization** (`exists_sameLevelMaximal_covers`
without the prescribed tuple), conditional on the coatom extension property with apex at `λ_β`
and on forcing donors at `β`, both still to be proved: for a countable `β`, every countably
infinite carrier `X` carries a model at `λ_β` that realizes every legal stage type at `λ_β`,
receives every legal donor exactly over every actual root, and is cover-hollow and terminal at
`β`. -/
theorem exists_sameLevelMaximal {β : Ordinal.{0}} (hβ : β < ω₁)
    (hext : StageType.HasApexCoatomExtensions.{0} (blockStage β)) (hF : ForcingDonors.{0} β)
    (X : Type) [Countable X] [Infinite X] :
    ∃ H : Realization.{0, 0} (blockStage β) X, H.IsModel ∧
      (∀ ⦃n : ℕ⦄ (p : StageType.{0} (blockStage β) n), p.IsLegal → ∃ c : Fin n → X, H.Covers p c) ∧
      H.ExactReceivingWithin (fun m ↦ {D : StageType.{0} (blockStage β) m | D.IsLegal}) ∧
      H.IsCoverHollow ∧ H.IsTerminalAt β := by
  obtain ⟨H, hH, -, h⟩ := exists_sameLevelMaximal_covers hβ hext hF X
    (TopFreeIndex.empty (blockStage β)).2.2.1 (Function.Embedding.ofIsEmpty : Fin 0 ↪ X)
  exact ⟨H, hH, h⟩

end VaughtConjecture
