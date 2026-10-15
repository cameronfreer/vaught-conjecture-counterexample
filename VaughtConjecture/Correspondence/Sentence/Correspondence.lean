/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Sentence.Lift
import VaughtConjecture.Correspondence.Sentence.Reduct
import VaughtConjecture.Correspondence.Sentence.Targets

/-!
# B.T12: the models of `σ[L]` are the base reducts of `K₀[L]`

Numbering as in the current draft of [AFK26].  On a nonempty carrier, a structure `B` of
`L_c[L]` satisfies `σ[L]` exactly when `B = G↾L_c[L]` for some `G ∈ K₀[L]` on the same carrier
(`realize_templateSentence_iff_exists_lift`), the identification of [AFK26, Theorem 4.23] at
level zero, the label stage `blockStage 0 = ω`.  The target B.T12 (`SentenceCorrespondenceTarget`)
follows (`sentenceCorrespondenceTarget`); its premise `Countable M` is not used.

* From `σ[L]` to a lift: `liftStructure B` (`VaughtConjecture.Correspondence.Sentence.Lift`), with
  `Q_t` read as `R_t` for `t` of rank zero; clause (d) gives `D[k]` for donors of every rank
  through donor reduction and witness passage (`satisfiesDensityAt_of_rankZero`).
* From a lift to `σ[L]`: `isTemplateSentenceModel_baseReduct`
  (`VaughtConjecture.Correspondence.Sentence.Reduct`); clause (d) is the specialization of `D[k]`
  to rank-zero donors (`SatisfiesDensityAt.rankZero`), and the plan clauses come from the plans of
  the templates.

Correspondence with the printed definitions.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

/-- **The models of `σ[L]` are the base reducts of `K₀[L]`**, on a nonempty carrier: a structure
`B` of `L_c[L]` satisfies `σ[L]` exactly when some `G ∈ K₀[L]` on the same carrier has
`G↾L_c[L] = B`.  No countability is assumed.  Correspondence with the printed definitions. -/
theorem realize_templateSentence_iff_exists_lift {M : Type v} [Nonempty M]
    (B : baseTemplateLanguage.{u}.Structure M) :
    @Sentenceω.Realize _ templateSentence.{u} M B ↔
      ∃ G ∈ templateStageClass M (0 : Ordinal.{u}), baseReduct G = B := by
  rw [@realize_templateSentence_iff M B]
  constructor
  · intro h
    exact ⟨liftStructure B, liftStructure_mem_templateStageClass h, baseReduct_liftStructure B⟩
  · rintro ⟨G, ⟨-, hG, hfix, hden⟩, rfl⟩
    refine isTemplateSentenceModel_baseReduct hG hfix fun k ↦ hden k ?_
    rw [blockStage_zero]
    exact Ordinal.natCast_lt_omega0 k

/-- **Target B.T12, proved.**  The premise `Countable M` of the target is not used.
Correspondence with the printed definitions. -/
theorem sentenceCorrespondenceTarget (M : Type v) : SentenceCorrespondenceTarget.{u, v} M :=
  fun _ hne B ↦ haveI := hne; realize_templateSentence_iff_exists_lift B

end VaughtConjecture
