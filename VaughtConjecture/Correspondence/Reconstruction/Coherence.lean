/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Reconstruction.Reconstruction

/-!
# Reconstruction: lifts of one base structure at two levels

Write `λ_ξ = blockStage ξ`.  `τ_ξ` is `projectStructure ξ`, `K_ξ[L]` is `templateStageClass M ξ`,
and `N↾L_c[L]` is `baseReduct N`.

For `ξ ≤ ζ < ω₁` on a countable carrier, let `G ∈ K_ζ[L]` and `H ∈ K_ξ[L]` have the same base
reduct.

* `projectStructure_eq_of_baseReduct_eq`: `τ_ξ(G) = H`, literally.  By projection
  (`projectionTarget`, B.T9) `τ_ξ(G) ∈ K_ξ[L]`; `τ_ξ` keeps the base reduct
  (`baseReduct_projectStructure`); Reconstruction at level `ξ` (`reconstructionTarget`, B.T10)
  gives the equality.
* `decode_reduce_eq_decode_of_baseReduct_eq`: the decoded class realization of `G` reduces at
  `λ_ξ` to that of `H`.  `τ_ξ(G)` is the structure of the reduction
  (`projectStructure_eq_toStructure_decode_reduce`), and decoding the structure of a well-formed
  class realization gives it back (`decode_toStructure`).

Both are correspondence with the printed definitions.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

variable {M : Type v}

/-- **A lift at a higher level projects to a lift at a lower level with the same base reduct**:
for `ξ ≤ ζ < ω₁` on a countable carrier, if `G ∈ K_ζ[L]` and `H ∈ K_ξ[L]` have the same base
reduct, then `τ_ξ(G) = H`.  By projection (`projectionTarget`, B.T9), the base reduct of a
projection (`baseReduct_projectStructure`) and Reconstruction at level `ξ`
(`reconstructionTarget`, B.T10).  Correspondence with the printed definitions. -/
theorem projectStructure_eq_of_baseReduct_eq (hc : Countable M) {ζ ξ : Ordinal.{u}}
    (hζ : ζ < ω₁) (hξζ : ξ ≤ ζ) {G H : templateLanguage.{u}.Structure M}
    (hG : G ∈ templateStageClass M ζ) (hH : H ∈ templateStageClass M ξ)
    (h : baseReduct G = baseReduct H) :
    projectStructure ξ G = H :=
  reconstructionTarget ξ M hc (hξζ.trans_lt hζ) _ (projectionTarget ζ ξ M hc hζ hξζ G hG) H hH
    (by rw [baseReduct_projectStructure, h])

/-- **A lift at a higher level reduces to a lift at a lower level with the same base reduct**, on
decoded class realizations: for `ξ ≤ ζ < ω₁` on a countable carrier, if `G ∈ K_ζ[L]` and
`H ∈ K_ξ[L]` have the same base reduct, the decoded class realization of `G` reduces at `λ_ξ` to
that of `H`.  `τ_ξ(G) = H` (`projectStructure_eq_of_baseReduct_eq`), `τ_ξ(G)` is the structure of
the reduction (`projectStructure_eq_toStructure_decode_reduce`), and decoding that structure
gives the reduction back (`decode_toStructure`).  Correspondence with the printed definitions. -/
theorem decode_reduce_eq_decode_of_baseReduct_eq (hc : Countable M) {ζ ξ : Ordinal.{u}}
    (hζ : ζ < ω₁) (hξζ : ξ ≤ ζ) {G H : templateLanguage.{u}.Structure M}
    (hG : G ∈ templateStageClass M ζ) (hH : H ∈ templateStageClass M ξ)
    (h : baseReduct G = baseReduct H) :
    (decode ζ G).reduce (isSuccPrelimit_blockStage ξ) = decode ξ H := by
  rw [← projectStructure_eq_of_baseReduct_eq hc hζ hξζ hG hH h,
    projectStructure_eq_toStructure_decode_reduce hζ hξζ hG,
    decode_toStructure (hξζ.trans_lt hζ) (hG.2.1.isWellFormed_decode.reduce _)]

end

end VaughtConjecture
