/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Limits.ClassGluing

/-!
# Limits: a lift at a limit level from lower lifts over one base

Numbering as in the current draft of [AFK26].  Write `λ_ξ = blockStage ξ = ω + ω · ξ`; the
manuscript level `ξ` is the label stage `λ_ξ`.  `τ_ξ` is `projectStructure ξ`, and `K_ξ[L]` is
`templateStageClass M ξ`.

**Target B.T11, Limits** [AFK26, Proposition 4.34] (`LimitsTarget δ M`, proved as
`limitsTarget`): for a nonzero limit `δ < ω₁` on a countable carrier `M` and a structure `B` of
the base language, if for every `ξ < δ` some structure of `K_ξ[L]` has base reduct `B`, then
some structure of `K_δ[L]` has base reduct `B`.  The hypothesis is mere existence at each lower
level, one level at a time; no relation between the lower lifts is assumed.  Coherence of the
lower lifts is derived, and it is not a premise of the statement.

## The steps

1. **Choice.**  For each `ξ < δ` choose a lift `G_ξ ∈ K_ξ[L]` with `G_ξ↾L_c[L] = B`.
2. **Coherence of lower lifts** (`LowerLiftCoherenceTarget ζ ξ M`, proved as
   `lowerLiftCoherenceTarget`): for `ξ ≤ ζ < ω₁` on a countable carrier, a structure `G` of
   `K_ζ[L]` and a structure `H` of `K_ξ[L]` with the same base reduct have `τ_ξ(G) = H`.  By
   projection (`projectionTarget`, B.T9) `τ_ξ(G) ∈ K_ξ[L]`; `τ_ξ` keeps the base reduct
   (`baseReduct_projectStructure`); Reconstruction at level `ξ` (`reconstructionTarget`, B.T10)
   gives literal equality.  Its class form (`DecodedCoherenceTarget ζ ξ M`, proved as
   `decodedCoherenceTarget`): the decoded class realization of `G` reduces to `λ_ξ` as the
   decoded class realization of `H`, since `τ_ξ(G)` is the structure of that reduction
   (`projectStructure_eq_toStructure_decode_reduce`) and decoding the structure of a well-formed
   class realization gives it back (`decode_toStructure`).
3. **The coherent family** (`CoherentClassFamily.ofLowerLifts`): the decoded class realizations
   `decode ξ G_ξ` at the stages `λ_ξ`, `ξ < δ`, with coherence from step 2, well-formedness from
   compatibility (`IsTemplateCompatible.isWellFormed_decode`), and donor density from
   `mem_templateStageClass_iff`.
4. **Gluing** (`classGluingTarget`): a class realization `T` at `λ_δ` reducing to every member,
   well-formed, with donor density at every permitted cutoff at `λ_δ`, which is donor density
   (`ClassRealization.hasDonorDensity_iff_forall_hasDonorDensityAt`).
5. **Decoding at the limit level** (`LimitDecodingTarget δ M`, proved as
   `limitDecodingTarget`): for `δ < ω₁` on a nonempty carrier, the structure of a well-formed
   class realization at `λ_δ` with donor density is in `K_δ[L]`
   (`mem_templateStageClass_iff`, `ClassRealization.projectStructure_toStructure`,
   `decode_toStructure`), and its base reduct is read from the reduction to `λ_0 = ω`
   (`ClassRealization.baseReduct_toStructure_reduce`).  For `T` from step 4 the reduction to
   `λ_0` is `decode 0 G_0`, whose structure is `G_0` (`toStructure_decode`), of base reduct `B`.

**Premises.**  `Countable M` is used by projection and Reconstruction at the lower levels;
`δ < ω₁` bounds every lower level below `ω₁` and is used by the decoder at `λ_δ`; that `δ` is a
limit is used by the gluing, and `0 < δ` (from it) gives the member at level zero, whose carrier
is nonempty and whose base reduct is `B`.  Level zero itself (the label stage `ω`) is not a limit
level here; it is the content of the sentence correspondence, not of this file.

## Placement

Limits clause of [AFK26, Proposition 4.34] (roadmap, Layer 4).
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

/-! ### The targets -/

/-- **Target: coherence of lower lifts** (step 2): for `ξ ≤ ζ < ω₁` on a countable carrier, a
structure `G` of `K_ζ[L]` and a structure `H` of `K_ξ[L]` with equal base reducts have
`τ_ξ(G) = H`, literally.  Correspondence with the printed definitions. -/
def LowerLiftCoherenceTarget (ζ ξ : Ordinal.{u}) (M : Type v) : Prop :=
  Countable M → ζ < ω₁ → ξ ≤ ζ →
    ∀ G ∈ templateStageClass M ζ, ∀ H ∈ templateStageClass M ξ,
      baseReduct G = baseReduct H → projectStructure ξ G = H

/-- **Target: coherence of lower lifts, on decoded class realizations** (step 2, class form): for
`ξ ≤ ζ < ω₁` on a countable carrier, a structure `G` of `K_ζ[L]` and a structure `H` of
`K_ξ[L]` with equal base reducts have `(decode ζ G).reduce λ_ξ = decode ξ H`, an equality of
class realizations.  Correspondence with the printed definitions. -/
def DecodedCoherenceTarget (ζ ξ : Ordinal.{u}) (M : Type v) : Prop :=
  Countable M → ζ < ω₁ → ξ ≤ ζ →
    ∀ G ∈ templateStageClass M ζ, ∀ H ∈ templateStageClass M ξ,
      baseReduct G = baseReduct H →
        (decode ζ G).reduce (isSuccPrelimit_blockStage ξ) = decode ξ H

/-- **Target: decoding at a level** (step 5): for `δ < ω₁` on a nonempty carrier, the structure of
a well-formed class realization `T` at `λ_δ` with donor density is in `K_δ[L]`, and its base
reduct is that of the structure of the reduction of `T` to `λ_0 = ω`.  Correspondence with the
printed definitions. -/
def LimitDecodingTarget (δ : Ordinal.{u}) (M : Type v) : Prop :=
  δ < ω₁ → Nonempty M → ∀ T : ClassRealization.{u, v} (blockStage δ) M,
    T.IsWellFormed → T.HasDonorDensity →
      T.toStructure ∈ templateStageClass M δ ∧
        baseReduct T.toStructure =
          baseReduct (T.reduce (isSuccPrelimit_blockStage 0)).toStructure

/-- **Target B.T11, Limits** [AFK26, Proposition 4.34]: for a nonzero limit `δ < ω₁` on a
countable carrier `M` and a structure `B` of the base language `L_c[L]`, if every level `ξ < δ`
has some structure of `K_ξ[L]` with base reduct `B`, then some structure of `K_δ[L]` has base
reduct `B`.  The lower lifts are assumed to exist level by level, with no relation between them;
coherence is not a premise.  Correspondence with the printed definitions. -/
def LimitsTarget (δ : Ordinal.{u}) (M : Type v) : Prop :=
  Countable M → Order.IsSuccLimit δ → δ < ω₁ → ∀ B : baseTemplateLanguage.{u}.Structure M,
    (∀ ξ < δ, ∃ G ∈ templateStageClass M ξ, baseReduct G = B) →
      ∃ G ∈ templateStageClass M δ, baseReduct G = B

/-! ### Coherence of lower lifts -/

/-- **Coherence of lower lifts holds** (`LowerLiftCoherenceTarget ζ ξ M` for every `ζ`, `ξ` and
`M`): `τ_ξ(G) ∈ K_ξ[L]` by projection (`projectionTarget`), with the base reduct of `G`
(`baseReduct_projectStructure`), so `τ_ξ(G) = H` by Reconstruction at level `ξ`
(`reconstructionTarget`).  Used: `Countable M`, `ζ < ω₁`, `ξ ≤ ζ`.  Correspondence with the
printed definitions. -/
theorem lowerLiftCoherenceTarget (ζ ξ : Ordinal.{u}) (M : Type v) :
    LowerLiftCoherenceTarget ζ ξ M := by
  intro hc hζ hξζ G hG H hH h
  exact reconstructionTarget ξ M hc (hξζ.trans_lt hζ) _ (projectionTarget ζ ξ M hc hζ hξζ G hG)
    H hH (by rw [baseReduct_projectStructure, h])

/-- **Coherence of lower lifts holds on decoded class realizations** (`DecodedCoherenceTarget ζ ξ M`
for every `ζ`, `ξ` and `M`): `τ_ξ(G) = H` (`lowerLiftCoherenceTarget`), `τ_ξ(G)` is the structure
of `(decode ζ G).reduce λ_ξ` (`projectStructure_eq_toStructure_decode_reduce`), and decoding that
structure gives the reduction back (`decode_toStructure`).  Correspondence with the printed
definitions. -/
theorem decodedCoherenceTarget (ζ ξ : Ordinal.{u}) (M : Type v) :
    DecodedCoherenceTarget ζ ξ M := by
  intro hc hζ hξζ G hG H hH h
  obtain rfl := lowerLiftCoherenceTarget ζ ξ M hc hζ hξζ G hG H hH h
  rw [projectStructure_eq_toStructure_decode_reduce hζ hξζ hG,
    decode_toStructure (hξζ.trans_lt hζ) (hG.2.1.isWellFormed_decode.reduce _)]

/-! ### The coherent family of decoded lower lifts -/

namespace CoherentClassFamily

variable {δ : Ordinal.{u}} {M : Type v}

/-- **The coherent family of decoded lower lifts** (step 3): for lifts `G ξ ∈ K_ξ[L]`, `ξ < δ`,
all with base reduct `B`, on a countable carrier, with `δ < ω₁`, the decoded class realizations
`decode ξ (G ξ)` form a `CoherentClassFamily δ M`.  Coherence is derived
(`decodedCoherenceTarget`), not assumed; well-formedness is from compatibility, donor density
from `mem_templateStageClass_iff`.  Correspondence with the printed definitions. -/
def ofLowerLifts (hc : Countable M) (hδω : δ < ω₁) {B : baseTemplateLanguage.{u}.Structure M}
    (G : ∀ ξ < δ, templateLanguage.{u}.Structure M)
    (hG : ∀ ξ (hξ : ξ < δ), G ξ hξ ∈ templateStageClass M ξ)
    (hB : ∀ ξ (hξ : ξ < δ), baseReduct (G ξ hξ) = B) : CoherentClassFamily.{u, v} δ M where
  family ξ hξ := decode ξ (G ξ hξ)
  coherent ξ hξ ζ hζ h := decodedCoherenceTarget ζ ξ M hc (hζ.trans hδω) h.le _ (hG ζ hζ) _
    (hG ξ hξ) ((hB ζ hζ).trans (hB ξ hξ).symm)
  isWellFormed ξ hξ := (hG ξ hξ).2.1.isWellFormed_decode
  hasDonorDensity ξ hξ := ((mem_templateStageClass_iff (hξ.trans hδω) _).mp (hG ξ hξ)).2.2.2

end CoherentClassFamily

/-! ### Decoding at the limit level -/

/-- **Decoding at a level holds** (`LimitDecodingTarget δ M` for every `δ` and `M`): the structure
of `T` is compatible (`ClassRealization.IsWellFormed.isTemplateCompatible`), fixed by `τ_δ`
(`ClassRealization.projectStructure_toStructure`), and decodes to `T` (`decode_toStructure`), so
it is in `K_δ[L]` by `mem_templateStageClass_iff`; its base reduct is read from the reduction to
`λ_0` (`ClassRealization.baseReduct_toStructure_reduce`).  Used: `δ < ω₁`, `Nonempty M`.
Correspondence with the printed definitions. -/
theorem limitDecodingTarget (δ : Ordinal.{u}) (M : Type v) : LimitDecodingTarget δ M := by
  intro hδω hM T hT hd
  refine ⟨(mem_templateStageClass_iff hδω _).mpr ⟨hM, hT.isTemplateCompatible,
    ClassRealization.projectStructure_toStructure hδω T, ?_⟩,
    T.baseReduct_toStructure_reduce.symm⟩
  rw [decode_toStructure hδω hT]
  exact hd

/-! ### Limits -/

/-- **Target B.T11, Limits, holds** (`LimitsTarget δ M` for every `δ` and `M`)
[AFK26, Proposition 4.34]: choose a lift `G_ξ` at each level `ξ < δ`; the decoded lifts form a
coherent family (`CoherentClassFamily.ofLowerLifts`, coherence derived from projection,
preservation of the base reduct, and Reconstruction); glue it at `λ_δ` (`classGluingTarget`);
the structure of the glued class realization is in `K_δ[L]` (`limitDecodingTarget`), and its
base reduct is that of `G_0`, which is `B`.  No coherence premise.  Used: `Countable M`, that
`δ` is a limit, `δ < ω₁`.  Correspondence with the printed definitions. -/
theorem limitsTarget (δ : Ordinal.{u}) (M : Type v) : LimitsTarget δ M := by
  intro hc hδ hδω B h
  choose G hG hB using h
  obtain ⟨T, hTred, hT, hTd⟩ := classGluingTarget δ M hδ hδω
    (CoherentClassFamily.ofLowerLifts hc hδω G hG hB)
  obtain ⟨hmem, hbase⟩ := limitDecodingTarget δ M hδω (hG 0 hδ.pos).1 T hT
    ((ClassRealization.hasDonorDensity_iff_forall_hasDonorDensityAt T).mpr hTd)
  refine ⟨T.toStructure, hmem, ?_⟩
  rw [hbase, hTred 0 hδ.pos]
  change baseReduct (decode 0 (G 0 hδ.pos)).toStructure = B
  rw [(hG 0 hδ.pos).2.1.toStructure_decode (hG 0 hδ.pos).2.2.1, hB]

end

end VaughtConjecture
