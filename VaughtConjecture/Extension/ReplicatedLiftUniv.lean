/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedLift

/-!
# The lift from a mixed face into the full face

Roadmap, Layer 3 ((R3) and (R4), the mixed-coatom lift of the replicated carrier).

**The bottom pattern of a decoded controller row** (`Seed.decode_controller_dichotomy`).  Let `P`
be lawful below `(U, j)`, `U` mixed, and `θ` a capped decoder of `P` at the copy at `U` of a
controller `u` at a grade `K ≥ 2` with state `R`.  The controller reads every cell of the attachment
of grade at most `K` as `R`, and `R e` is the positive table of `R` at the rank of `e`, the reading
of a rung of the rank member of `R`.  The copied ladder at `U` has the shape of the table of one
member (`Seed.copyLadder_exists_shape`): the copied rungs of the rank member of `R` are all positive
or all `⊥`.  So `θ` either sends every reading of a cell of the attachment to `⊥`, or sends exactly
the readings `⊥` to `⊥`.

**The proofs.**  The replicated scheme is the ladder tower over the attachment mirrored at the
mixed faces, so each statement here is the statement for a mirrored scheme
(`VaughtConjecture.MainTheorem.MirrorMixedDecode`,
`VaughtConjecture.MainTheorem.MirrorMixedLift`) specialized to the tower, whose hypotheses it meets
(`VaughtConjecture.Extension.ReplicatedMixedLiftFromMirror`).

**Scope.**  Part of the earlier route (the replicated scheme over the height-set tower, or the
ladder tower of the amalgam), whose open inputs the levels re-rendered per grade replace; not used
by the main theorem through the levels (`VaughtConjecture.MainTheorem.GrowthLevelRoute`), and kept
as reusable constructions.

## References

Bountifulness is [Kni26, Definition 2.5.14]; witnesses are [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}
  {U : Finset (Fin (m + 2))}

/-- The replicated scheme. -/
local notation "𝔼" => Seed.replicated I g H Γ A B'

/-- The ladder tower over the attachment. -/
local notation "𝕋" => Seed.attachTower I g H Γ A B'

/-- **The bottom pattern of a decoded controller row**: a capped decoder at the copy of a
controller of grade `K ≥ 2` sends all its readings of the cells of the attachment of grade at most
`K` to `⊥`, or exactly the readings `⊥`. -/
theorem decode_controller_dichotomy (hU : U ∈ I.mixedFaces g) (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) {j : ℕ} {P : Fin (𝔼).card → Label.{u}}
    (hP : (𝔼).rows.IsLawfulBelow (U, j) fun d ↦ P d) (hj1 : 1 ≤ j) {K : ℕ} (hK2 : 2 ≤ K)
    (hKm : K ≤ m + 1) (hKU : K ≤ #U) {u : Fin (𝕋).card}
    (hu : (𝕋).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), K))
    {θ : Label.{u} → Label.{u}} (hθ_bot : θ ⊥ = ⊥)
    (hθ : ∀ d ∈ (𝔼).toCellScheme.below
        ((𝔼).toCellScheme.gradedIndex (copyFull H Γ A B' hU u hu hKU)),
      θ ((𝔼).rowAt (copyFull H Γ A B' hU u hu hKU) d) =
        min (P d) (P (copyFull H Γ A B' hU u hu hKU))) :
    (∀ e : Fin (I.attachment g).card, (I.attachment g).toCellScheme.grade e ≤ K →
        θ ((𝕋).rowAt u ((I.attachmentBase g).baseCellEmb m e)) = ⊥) ∨
      ∀ e : Fin (I.attachment g).card, (I.attachment g).toCellScheme.grade e ≤ K →
        (θ ((𝕋).rowAt u ((I.attachmentBase g).baseCellEmb m e)) = ⊥ ↔
          (𝕋).rowAt u ((I.attachmentBase g).baseCellEmb m e) = ⊥) := by
  have _ := hKm
  exact decode_controller_dichotomy_m (hmix := I.not_subset_scope_tower g H Γ A B') hU hH
    gradedIndex_ladCell attachTower_rowAt_lad_lad (attachTower_reads_ladder hcard) hP hj1 hK2 hKU
    hu hθ_bot hθ

/-- **The cells of the replicated scheme**: a cell has an original of full scope at its grade (a
cell of full scope of the tower or a copy), or is a cell of the attachment. -/
theorem cell_cases (z : Fin (𝔼).card) :
    (∃ v, (𝕋).mirrorOrig (I.mixedFaces g) z = v ∧
        (𝕋).toCellScheme.gradedIndex v =
          ((univ : Finset (Fin (m + 2))), (𝔼).toCellScheme.grade z)) ∨
      ∃ e, z = I.attachEmb g H Γ A B' e :=
  mirror_cell_cases_att (hmix := I.not_subset_scope_tower g H Γ A B') attachTower_cells z

/-- **The bottom pattern of the decoded top rung**: a capped decoder at the copy of the top rung
of a member `a` whose copy dominates the copied ladder sends all readings of the cells of the
attachment of grade one by the original top rung to `⊥`, or exactly the readings `⊥`. -/
theorem decode_one_dichotomy (hU : U ∈ I.mixedFaces g) (hH : 0 < H) {j : ℕ}
    {P : Fin (𝔼).card → Label.{u}} (hP : (𝔼).rows.IsLawfulBelow (U, j) fun d ↦ P d)
    (hj1 : 1 ≤ j) (hU1 : 1 ≤ #U) (a : Scheme.RankMember (I.attachmentBase g).S H)
    (hmax : ∀ v, P (copyLadder H Γ A B' hU v) ≤
      P (copyLadder H Γ A B' hU (a, Sum.inl ⟨H - 1, by omega⟩)))
    {θ : Label.{u} → Label.{u}}
    (hθ : ∀ d ∈ (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex
        (copyFull H Γ A B' hU (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
          (gradedIndex_ladCell _) hU1)),
      θ ((𝔼).rowAt (copyFull H Γ A B' hU (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
          (gradedIndex_ladCell _) hU1) d) =
        min (P d) (P (copyFull H Γ A B' hU (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
          (gradedIndex_ladCell _) hU1))) :
    (∀ e : Fin (I.attachment g).card, (I.attachment g).toCellScheme.grade e = 1 →
        θ ((𝕋).rowAt (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
          ((I.attachmentBase g).baseCellEmb m e)) = ⊥) ∨
      ∀ e : Fin (I.attachment g).card, (I.attachment g).toCellScheme.grade e = 1 →
        (θ ((𝕋).rowAt (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
          ((I.attachmentBase g).baseCellEmb m e)) = ⊥ ↔
        (𝕋).rowAt (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
          ((I.attachmentBase g).baseCellEmb m e) = ⊥) :=
  decode_one_dichotomy_m (hmix := I.not_subset_scope_tower g H Γ A B') hU hH gradedIndex_ladCell
    attachTower_rowAt_lad_lad (fun p _ he ↦ rowAt_ladCell_baseCellEmb p he) hP hj1 a hmax hθ

end Seed

end VaughtConjecture
