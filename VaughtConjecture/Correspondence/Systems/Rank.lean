/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.Projection

/-!
# Fixed structures and rank

Numbering as in the current draft of [AFK26] (the published v1 reads identically).

* `InvariantSystem.IsFixedAt.mono`: a structure fixed at `β` is fixed at every `γ ≥ β`
  (`τ_γ ∘ τ_β = τ_β`, `InvariantSystem.projection_projection_of_ge`);
* `InvariantSystem.fixedAtIffRankLeTarget`: for a structure fixed at some countable level, being
  fixed at `β` is having rank at most `β` ([AFK26, Definition 2.7]).  The premise that some
  fixing level exists is kept: without it the rank is `sInf ∅ = 0` by convention, while the
  structure is fixed at no level.
-/

universe w w' v

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal

variable {L : Language.{w, w'}} {σ : GeometrySignature L}

namespace InvariantSystem

variable {S : InvariantSystem.{0} σ}

/-- **Fixation is monotone**: a structure fixed at `β` is fixed at every `γ ≥ β`, since
`τ_γ(τ_β(G)) = τ_β(G)`.  Correspondence with the printed definitions. -/
theorem IsFixedAt.mono {β γ : SystemLevel} {M : Type v} {G : L.Structure M}
    (h : S.IsFixedAt β G) (hβγ : β ≤ γ) : S.IsFixedAt γ G := by
  unfold IsFixedAt at h ⊢
  rw [← h, S.projection_projection_of_ge hβγ]

variable (S) in
/-- **Fixed at `β` exactly when the rank is at most `β`** (`FixedAtIffRankLeTarget`,
[AFK26, Definition 2.7]), for a structure fixed at some countable level: the rank is the least
fixing level (`csInf_mem`, the ordinals being well ordered), and fixation is monotone
(`IsFixedAt.mono`).  Correspondence with the printed definitions. -/
theorem fixedAtIffRankLeTarget : S.FixedAtIffRankLeTarget.{w, w', v} := by
  rintro M G ⟨γ, hγ⟩ β
  have hne : {β' : Ordinal.{0} | ∃ h : β' < ω₁, S.IsFixedAt ⟨β', h⟩ G}.Nonempty :=
    ⟨γ.1, γ.2, hγ⟩
  constructor
  · intro hβ
    exact csInf_le' ⟨β.2, hβ⟩
  · intro hle
    obtain ⟨h, hfix⟩ := csInf_mem hne
    exact hfix.mono (show (⟨S.structureRank G, h⟩ : SystemLevel) ≤ β from hle)

end InvariantSystem

end VaughtConjecture.Correspondence
