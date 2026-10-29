/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Density.Density

/-!
# Lift stages and lift ranks over a base structure

Numbering as in the current draft of [AFK26].  `τ_β` is `projectStructure β`, `K_β[L]` is
`templateStageClass M β`, and `N↾L_c[L]` is `baseReduct N`.

**The rank.**  [AFK26, Definitions 2.6 and 2.7]: `rank_τ(N)` is the least `β < ω₁` with
`τ_β(N) = N`, when there is one.  The fixing stages are `fixingStages N` (unchanged here), and
"`ρ` is the rank of `N`" is `IsLeast (fixingStages N) ρ`.  This is the projection-fixing rank of
the printed definitions, not a Scott rank.  Correspondence with the printed definitions.

**Over a base structure `B`** of `L_c[L]` on `M` (correspondence with the printed definitions):

* `liftStages M B`: the stages `β < ω₁` at which `B` has a lift, a structure `G ∈ K_β[L]` with
  `G↾L_c[L] = B`;
* `liftRanks M B`: the ranks of those lifts, the set `{rank_τ(N) : N ∈ K, N↾L_c[L] = B}` of
  [AFK26, Proposition 4.34] (Boundedness), with `K = ⋃_{β < ω₁} K_β[L]`.

**Proved here.**

* `leastFixingRank_of_mem_templateStageClass`: for `β < ω₁`, every `G ∈ K_β[L]` has a rank, by
  well-foundedness of the ordinals, since `β` is a fixing stage
  (`mem_fixingStages_of_mem_templateStageClass`);
* `rank_le_stage_of_mem_templateStageClass`: the rank of `G ∈ K_β[L]` is at most `β`, for every
  `β`: for `β < ω₁` since `β` is a fixing stage, and otherwise since fixing stages are below `ω₁`;
* `exists_mem_liftStages_le_of_mem_liftRanks`: a rank in `liftRanks M B` is at most some stage in
  `liftStages M B`;
* `liftRanks_countable_and_bounded_of_liftStages_bounded`: a bound `A < ω₁` on the lift stages
  bounds the lift ranks, which then form a countable set.

Nothing here says that the rank of `G ∈ K_β[L]` equals `β`.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

variable {M : Type v}

/-! ### The rank -/

/-- **Every structure of `K_β[L]`, `β < ω₁`, has a rank**: the fixing stages contain `β`, so the
least fixing stage exists by well-foundedness of the ordinals.  Correspondence with the printed
definitions. -/
theorem leastFixingRank_of_mem_templateStageClass {β : Ordinal.{u}}
    {G : templateLanguage.{u}.Structure M} (hG : G ∈ templateStageClass M β) (hβ : β < ω₁) :
    ∃ ρ, IsLeast (fixingStages G) ρ :=
  ⟨sInf (fixingStages G), csInf_mem ⟨β, mem_fixingStages_of_mem_templateStageClass hG hβ⟩,
    fun _ h ↦ csInf_le' h⟩

/-- **The rank is at most the stage**: if `G ∈ K_β[L]` and `ρ` is the least fixing stage of `G`,
then `ρ ≤ β`.  For `β < ω₁`, `β` is a fixing stage; otherwise `ρ < ω₁ ≤ β`.  No hypothesis on
`β`.  Correspondence with the printed definitions. -/
theorem rank_le_stage_of_mem_templateStageClass {β ρ : Ordinal.{u}}
    {G : templateLanguage.{u}.Structure M} (hG : G ∈ templateStageClass M β)
    (hρ : IsLeast (fixingStages G) ρ) : ρ ≤ β := by
  rcases lt_or_ge β ω₁ with hβ | hβ
  · exact hρ.2 (mem_fixingStages_of_mem_templateStageClass hG hβ)
  · exact hρ.1.1.le.trans hβ

/-! ### Lift stages and lift ranks -/

variable (M) in
/-- **The lift stages** of a base structure `B` of `L_c[L]` on `M`: the `β < ω₁` such that some
`G ∈ K_β[L]` has `G↾L_c[L] = B`.  Correspondence with the printed definitions. -/
def liftStages (B : baseTemplateLanguage.{u}.Structure M) : Set Ordinal.{u} :=
  {β | β < ω₁ ∧ ∃ G ∈ templateStageClass M β, baseReduct G = B}

variable (M) in
/-- **The lift ranks** of a base structure `B` of `L_c[L]` on `M` ([AFK26, Proposition 4.34],
Boundedness): the ranks `ρ` (`IsLeast (fixingStages G) ρ`) of the structures `G ∈ K_β[L]`,
`β < ω₁`, with `G↾L_c[L] = B`.  Correspondence with the printed definitions. -/
def liftRanks (B : baseTemplateLanguage.{u}.Structure M) : Set Ordinal.{u} :=
  {ρ | ∃ β < ω₁, ∃ G ∈ templateStageClass M β, baseReduct G = B ∧ IsLeast (fixingStages G) ρ}

/-- **A lift rank is at most a lift stage**: every `ρ ∈ liftRanks M B` is at most some
`β ∈ liftStages M B` (`rank_le_stage_of_mem_templateStageClass`).  Correspondence with the
printed definitions. -/
theorem exists_mem_liftStages_le_of_mem_liftRanks {B : baseTemplateLanguage.{u}.Structure M}
    {ρ : Ordinal.{u}} (hρ : ρ ∈ liftRanks M B) : ∃ β ∈ liftStages M B, ρ ≤ β := by
  obtain ⟨β, hβ, G, hG, hGB, hρG⟩ := hρ
  exact ⟨β, ⟨hβ, G, hG, hGB⟩, rank_le_stage_of_mem_templateStageClass hG hρG⟩

/-- **A bound on the lift stages bounds the lift ranks, and makes them countable**: if every lift
stage of `B` is below `A < ω₁`, then so is every lift rank, and the lift ranks form a countable
set.  Correspondence with the printed definitions. -/
theorem liftRanks_countable_and_bounded_of_liftStages_bounded
    {B : baseTemplateLanguage.{u}.Structure M} {A : Ordinal.{u}} (hA : A < ω₁)
    (hS : ∀ β ∈ liftStages M B, β < A) :
    (liftRanks M B).Countable ∧ ∀ ρ ∈ liftRanks M B, ρ < A := by
  have hR : ∀ ρ ∈ liftRanks M B, ρ < A := fun ρ hρ ↦ by
    obtain ⟨β, hβ, hρβ⟩ := exists_mem_liftStages_le_of_mem_liftRanks hρ
    exact hρβ.trans_lt (hS β hβ)
  exact ⟨(Cardinal.countable_Iio_of_lt_omega_one hA).mono (s₂ := Set.Iio A) hR, hR⟩

end

end VaughtConjecture
