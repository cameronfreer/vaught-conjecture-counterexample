/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapDetermination
import VaughtConjecture.Expansion.Losses

/-!
# (R2) at the countable block stages, and the losses under it

Roadmap, Layer 3 ((R2) of the table of 3.4) and Layer 5 (the countable losses); semantic contract,
item 8.

(R2) (`Realization.ResidualReceiving`) is stated at every limit stage and at every universe level,
and its reduction to cutoff determination
(`Realization.residualReceiving_of_cutoffDetermination`) assumes (R1) for every model at every
limit stage, which the library's (R1) for models, `Expansion.FiniteCutReceiving` (limit stages
below `ω₁`, universe `0`), does not give.  The count uses (R2) only through the residual
comparison of two model expansions to a block stage `λ_ξ`, `ξ < ω₁`
(`ModelExpansion.nonempty_equiv_of_hasTerminalProperty`).  This file states the form it uses and
derives it with (R1) in the library's form.

* **(R2) at the countable block stages** (`Realization.BlockResidualReceiving`): (R2) restricted to
  models at the stages `blockStage ξ`, `ξ < ω₁`, universe `0`.  It follows from (R2)
  (`Realization.ResidualReceiving.blockResidualReceiving`), and from (R1) in the library's form
  together with the separated pinned extension property at those stages
  (`Realization.blockResidualReceiving_of_hasSeparatedPinnedExtensions`, compiled in this
  repository): (R1) is used for one model at a time
  (`Realization.exists_covers_snoc_of_hasSeparatedPinnedExtensions`).
* **The residual comparison under it** (`Realization.nonempty_equiv_of_blockResidual`), and **the
  countable losses** with it in place of (R2)
  (`Expansion.expansionDomain_loss_countable_of_blockResidual`, through
  `ModelExpansion.nonempty_equiv_of_hasTerminalProperty_of_blockResidual` and
  `Expansion.subsingleton_classes_of_property_of_blockResidual`), conditional on (R1), the
  continuation criterion, (R2) at the countable block stages and (R3), each still to be proved.
  Since (R2) gives its block form, these hypotheses are weaker than or equal to those of
  `Expansion.expansionDomain_loss_countable`; the statements with (R2) are kept.

So for the count, (R2) reduces to the separated pinned extension property at the countable block
stages, with (R1) in the library's form
(`Expansion.expansionDomain_loss_countable_of_hasSeparatedPinnedExtensions`); the separated pinned
extension property is open.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture

open Ordinal FirstOrder Language Structure baseLanguage

namespace Realization

/-- **(R2) at the countable block stages**: in a model at a block stage `λ_ξ`, `ξ < ω₁`, with no
cover that is a globally rigid core and with top-grade supremum `K`, over every cover `c` of a
stage type `t`, every one-point coface of `t` of top grade at most `K` is the type of `c` extended
by one point.  Still to be proved. -/
structure BlockResidualReceiving : Prop where
  /-- Over every cover, every one-point coface of top grade at most `K` is received exactly. -/
  exists_covers ⦃ξ : Ordinal.{0}⦄ ⦃M : Type w⦄ ⦃R : Realization.{0, w} (blockStage ξ) M⦄ ⦃K : ℕ⦄ :
    ξ < ω₁ → R.IsModel →
      (¬ ∃ (k : ℕ) (p : StageType.{0} (blockStage ξ) k) (c : Fin k → M), R.Covers p c ∧
        R.IsGloballyRigidCore c) →
      R.topGradeSup = K → ∀ ⦃n : ℕ⦄ (t : StageType.{0} (blockStage ξ) n) (c : Fin n → M),
        R.Covers t c → ∀ D ∈ t.cofaces, D.topGrade ≤ K → ∃ y : M, R.Covers D (Fin.snoc c y)

/-- **(R2) gives (R2) at the countable block stages.** -/
theorem ResidualReceiving.blockResidualReceiving (h : ResidualReceiving.{0, w}) :
    BlockResidualReceiving.{w} where
  exists_covers ξ _ _ _ _ hR hcore hK _ t c hc D hD hDK :=
    h.exists_covers (isSuccLimit_blockStage ξ) hR hcore hK t c hc D hD hDK

/-- **(R2) at the countable block stages from (R1) and separated pinned extensions**: (R1) in the
library's form (every model at a countable limit stage, universe `0`) and the separated pinned
extension property at every countable block stage.  Both hypotheses are open. -/
theorem blockResidualReceiving_of_hasSeparatedPinnedExtensions
    (hrec : Expansion.FiniteCutReceiving.{w})
    (hsep : ∀ ξ : Ordinal.{0}, ξ < ω₁ → StageType.HasSeparatedPinnedExtensions (blockStage ξ)) :
    BlockResidualReceiving.{w} where
  exists_covers ξ _ R _ hξ hR hcore hK _ _ _ hc _ hD hDK :=
    exists_covers_snoc_of_hasSeparatedPinnedExtensions (isSuccLimit_blockStage ξ) hR
      (hrec.receive (isSuccLimit_blockStage ξ) (blockStage_lt_omega_one hξ) R hR) (hsep ξ hξ)
      hcore hK hc hD hDK

section Comparison

variable {M N : Type w} [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
  [Countable M] [Countable N] {ξ : Ordinal.{0}}

omit [baseLanguage.{0}.Structure M] [Countable M] in
/-- Under (R2) at the countable block stages, a residual model at a countable block stage has exact
receiving of the legal stage types of top grade at most `K`. -/
private theorem exactReceivingWithin_of_blockResidual (hres : BlockResidualReceiving.{w})
    (hξ : ξ < ω₁) {R : Realization.{0, w} (blockStage ξ) M} (hR : R.IsModel)
    (hcore : ¬ ∃ (k : ℕ) (p : StageType.{0} (blockStage ξ) k) (c : Fin k → M), R.Covers p c ∧
      R.IsGloballyRigidCore c)
    {K : ℕ} (hK : R.topGradeSup = K) :
    R.ExactReceivingWithin fun _ ↦ {D | D.IsLegal ∧ D.topGrade ≤ K} :=
  .of_one_point hR.isConsistent
    (fun _ _ _ _ _ hD hf ↦ StageType.isLegal_and_topGrade_le_of_restrictFace hD hf)
    fun _ t c hc D hD hDt ↦
      let ⟨y, hy⟩ := hres.exists_covers hξ hR hcore hK t c hc D ⟨hD.1, hDt⟩ hD.2
      ⟨Fin.snoc c y, hy, Fin.snoc_comp_castSucc⟩

/-- **The residual comparison at a countable block stage**, under (R2) at the countable block
stages: two expansions of countable base structures at `λ_ξ`, `ξ < ω₁`, with no cover that is a
globally rigid core and with the same top-grade supremum `K`, have isomorphic base structures. -/
theorem nonempty_equiv_of_blockResidual (hres : BlockResidualReceiving.{w}) (hξ : ξ < ω₁)
    {R : Realization.{0, w} (blockStage ξ) M} {R' : Realization.{0, w} (blockStage ξ) N}
    (he : R.IsExpansionOf) (he' : R'.IsExpansionOf)
    (hcore : ¬ ∃ (k : ℕ) (p : StageType.{0} (blockStage ξ) k) (c : Fin k → M), R.Covers p c ∧
      R.IsGloballyRigidCore c)
    (hcore' : ¬ ∃ (k : ℕ) (p : StageType.{0} (blockStage ξ) k) (c : Fin k → N), R'.Covers p c ∧
      R'.IsGloballyRigidCore c)
    {K : ℕ} (hK : R.topGradeSup = K) (hK' : R'.topGradeSup = K) :
    Nonempty (M ≃[baseLanguage.{0}] N) := by
  obtain ⟨p, hp⟩ := he.isModel.exists_covers_zero
  obtain ⟨p', hp'⟩ := he'.isModel.exists_covers_zero
  exact nonempty_equiv_of_exactReceivingWithin (A := fun _ ↦ {D | D.IsLegal ∧ D.topGrade ≤ K})
    he he' (fun _ _ _ hs ↦ he.isModel.isLegal_and_topGrade_le hK hs)
    (fun _ _ _ hs ↦ he'.isModel.isLegal_and_topGrade_le hK' hs)
    (exactReceivingWithin_of_blockResidual hres hξ he.isModel hcore hK)
    (exactReceivingWithin_of_blockResidual hres hξ he'.isModel hcore' hK') hp
    (StageType.eq_of_zero p' p ▸ hp')

end Comparison

end Realization

/-- **Two model expansions sharing a terminal property have isomorphic base structures**, for
countable carriers at `λ_ξ` with `ξ < ω₁`, conditional on (R1) (`hrec`), (R2) at the countable
block stages (`hres`) and (R3) (`hhol`), each still to be proved. -/
theorem ModelExpansion.nonempty_equiv_of_hasTerminalProperty_of_blockResidual {M N : Type w}
    [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N] [Countable M] [Countable N]
    (hrec : Expansion.FiniteCutReceiving.{w}) (hres : Realization.BlockResidualReceiving.{w})
    (hhol : Realization.HollowReceiving.{0, w} Realization.IsCoverHollowAtBlock)
    {ξ : Ordinal.{0}} (hξ : ξ < ω₁)
    {P : TerminalProperty ξ} (e : ModelExpansion M (blockStage ξ))
    (e' : ModelExpansion N (blockStage ξ)) (h : e.1.HasTerminalProperty P)
    (h' : e'.1.HasTerminalProperty P) : Nonempty (M ≃[baseLanguage.{0}] N) := by
  have hα := isSuccLimit_blockStage ξ
  have hr {K : Type w} (R : Realization.{0, w} (blockStage ξ) K) :=
    hrec.finiteExtensionReceiving.receive hα (blockStage_lt_omega_one hξ) R
  rcases P with ⟨_, p⟩ | K | ⟨⟩
  · obtain ⟨x, hx, hcx⟩ := h
    obtain ⟨y, hy, hcy⟩ := h'
    exact Realization.nonempty_equiv_of_isGloballyRigidCore hα e.2 e'.2 (hr _ e.2.isModel)
      (hr _ e'.2.isModel) hx hy hcx hcy
  · exact Realization.nonempty_equiv_of_blockResidual hres hξ e.2 e'.2 h.1 h'.1 h.2 h'.2
  · exact Realization.nonempty_equiv_of_hollow hhol hα e.2 e'.2 ⟨ξ, rfl, h.1⟩ ⟨ξ, rfl, h'.1⟩ h.2
      h'.2

namespace Expansion

open Realization

/-- **At most one class per terminal property**, conditional on (R1) (`hrec`), (R2) at the
countable block stages (`hres`) and (R3) (`hhol`), each still to be proved. -/
theorem subsingleton_classes_of_property_of_blockResidual (hrec : FiniteCutReceiving.{0})
    (hres : BlockResidualReceiving.{0}) (hhol : HollowReceiving.{0, 0} IsCoverHollowAtBlock)
    {ξ : Ordinal.{0}} (hξ : ξ < ω₁) (P : TerminalProperty ξ) :
    {q : Quotient (isoSetoid densitySentence.{0}) | ∃ (c : ModelsOf densitySentence.{0})
      (e : @ModelExpansion ℕ c.1.toStructure (blockStage ξ)),
        Quotient.mk _ c = q ∧ e.1.HasTerminalProperty P}.Subsingleton := by
  rintro _ ⟨c, e, rfl, h⟩ _ ⟨c', e', rfl, h'⟩
  obtain ⟨i⟩ := @ModelExpansion.nonempty_equiv_of_hasTerminalProperty_of_blockResidual ℕ ℕ
    c.1.toStructure c'.1.toStructure _ _ hrec hres hhol ξ hξ P e e' h h'
  exact Quotient.sound (isoSetoid_r_iff.mpr ⟨i⟩)

/-- **The successor losses of the expansion domains are countable**, conditional on (R1)
(`hrec`), the continuation criterion (`hcont`), (R2) at the countable block stages (`hres`) and
(R3) (`hhol`), each still to be proved. -/
theorem expansionDomain_loss_countable_of_blockResidual (hrec : FiniteCutReceiving.{0})
    (hcont : ContinuationCriterion.{0}) (hres : BlockResidualReceiving.{0})
    (hhol : HollowReceiving.{0, 0} IsCoverHollowAtBlock) :
    ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable := by
  intro ξ hξ
  have := countable_terminalProperty hξ
  refine Counting.countable_of_subsingleton_cover _
    (subsingleton_classes_of_property_of_blockResidual hrec hres hhol hξ) fun q hq ↦ ?_
  obtain ⟨c, rfl⟩ := Quotient.mk_surjective q
  let := c.1.toStructure
  obtain ⟨e⟩ := (mem_expansionDomain_iff c).mp hq.1
  obtain ⟨P, hP⟩ :=
    e.1.exists_hasTerminalProperty hcont hξ e.2.isModel (e.isTerminalAt_of_mem_loss hq)
  exact Set.mem_iUnion.mpr ⟨P, c, e, rfl, hP⟩

/-- **The successor losses are countable, with (R2) replaced by separated pinned extensions**:
conditional on (R1) (`hrec`), the continuation criterion (`hcont`), the separated pinned extension
property at every countable block stage (`hsep`) and (R3) (`hhol`), each still to be proved. -/
theorem expansionDomain_loss_countable_of_hasSeparatedPinnedExtensions
    (hrec : FiniteCutReceiving.{0}) (hcont : ContinuationCriterion.{0})
    (hsep : ∀ ξ : Ordinal.{0}, ξ < ω₁ → StageType.HasSeparatedPinnedExtensions (blockStage ξ))
    (hhol : HollowReceiving.{0, 0} IsCoverHollowAtBlock) :
    ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable :=
  expansionDomain_loss_countable_of_blockResidual hrec hcont
    (blockResidualReceiving_of_hasSeparatedPinnedExtensions hrec hsep) hhol

end Expansion

end VaughtConjecture
