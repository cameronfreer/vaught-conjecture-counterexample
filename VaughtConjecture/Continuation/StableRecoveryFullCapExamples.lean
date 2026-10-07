/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryFullCap
import VaughtConjecture.Continuation.StableRecoveryInterior
import VaughtConjecture.Continuation.StableRecoveryTwin

/-!
# Stable recovery schemes with a full-scope cap: two tests

Tests of `VaughtConjecture.Continuation.StableRecoveryFullCap` at two inputs of the graded cap
calibration (`StageType.GradedCapCalibration`) at which a stable recovery scheme is known.  Each
item is compiled in this repository (theorem named).

**The twin donors through the full-scope graded face**
(`StableRecoveryTwin.isStableRecoveryScheme_twinScheme_of_readsThroughUnivCap`).  At the context of
three points of `VaughtConjecture.Continuation.StableRecoveryTwin`, whose cap is the cell
`({0, 1, 2}, 3)` (full scope, labelled the formal top), the twin scheme of each order of the twins
is a stable recovery scheme by `StageType.IsStableRecoveryScheme.of_readsThroughUnivCap`, with the
coface of `T⁺↓λ_ξ` given by legality of the twin scheme
(`StageType.exists_mem_cofaces_reduce_of_isLegal`).  The only cell at `(univ, 3)` is the reading
cell; the hypotheses "the cap and the new cells lie below the reading cell" of
`StageType.IsStableRecoveryScheme.of_readsThroughCap` are discharged by the general theorem.
`StableRecoveryTwin.exists_isStableRecoveryScheme_twinDonors_of_readsThroughUnivCap` restates
`StableRecoveryTwin.exists_isStableRecoveryScheme_twinDonors` through this route.

**A full-scope cap at the interior context**
(`StableRecoveryInterior.exists_univ_cap_contextType`).  At the context of four points of
`VaughtConjecture.Continuation.StableRecoveryInterior`, whose cap `({1, 2}, 2)` avoids both extreme
points of the context, `StageType.GradedCapCalibration.exists_univ_cap` gives a graded cap of full
scope `{0, 1, 2, 3}`, of the same grade `2`.  For that cap the interior case disappears: the only
graded face of grade `2` containing it and a new cell is the ground set
(`Scheme.setOf_gradedFaces_univCap_eq_singleton`).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Continuation

open Finset Label StageType CandidateCounterexamples StableRecoveryCounterexample
open Ordinal hiding univ

/-! ### The twin donors -/

namespace StableRecoveryTwin

variable (ξ : Ordinal.{u})

/-- The labels of the donors: `λ_ξ + 2` at the root, `⊥` at the dead cells, and `λ_ξ + 2`,
`λ_ξ + 1` at the twins. -/
private theorem twinDonor_label_eq (o : Bool) (j : Fin 5) :
    (twinDonor ξ o).label (Fin.cast (by cases o <;> rfl) j) =
      ![labelAdd (blockStage ξ) 2, ⊥, twinHi o (labelAdd (blockStage ξ) 2)
        (labelAdd (blockStage ξ) 1), twinLo o (labelAdd (blockStage ξ) 2)
        (labelAdd (blockStage ξ) 1), ⊥] j := by
  cases o <;> fin_cases j <;> rfl

/-- **The twin scheme is a stable recovery scheme, read at the full-scope graded face**: for each
order `o` of the twins, the twin scheme is a stable recovery scheme for the context, the root
embedding, the donor of the order `o` and `γ = λ_ξ`, by
`StageType.IsStableRecoveryScheme.of_readsThroughUnivCap`.  The cap `({0, 1, 2}, 3)` has grade
`3 > 1`; the coface of `T⁺↓λ_ξ` comes from legality of the twin scheme; the reading cell `21` is
the only cell at `(univ, 3)`, and reads the dead new cells as `⊥` and the twins through the root
(`StableRecoveryTwin.readsThroughCap_twin`). -/
theorem isStableRecoveryScheme_twinScheme_of_readsThroughUnivCap (o : Bool) :
    (contextType ξ).IsStableRecoveryScheme rootEmb (twinDonor ξ o) (blockStage ξ)
      (twinScheme.{u} o) := by
  have hc10 := card_comap_castSuccEmb.{u} o
  let b : Fin ((twinScheme.{u} o).comap Fin.castSuccEmb).card := ⟨9, by omega⟩
  have hb : (twinScheme.{u} o).cellMap Fin.castSuccEmb b = 19 :=
    cellMap_castSuccEmb o (i := 9) rfl
  have hg : (twinScheme.{u} o).toCellScheme.grade 19 = 3 := rfl
  have huniq : ∀ u : Fin 23, twinCells.gradedIndex u = ((univ : Finset (Fin 4)), 3) → u = 21 := by
    decide
  refine IsStableRecoveryScheme.of_readsThroughUnivCap (restrictFace_rootEmb_contextType ξ)
    (twinDonor_mem_cofaces ξ o)
    (exists_mem_cofaces_reduce_of_isLegal (isLegal_twinScheme o) map_castSuccEmb_mem_faces ?_)
    map_extendByLast_mem_faces (by cases o <;> exact comap_twinScheme_extendByLast _)
    (b := b) (b₀ := contextCap ξ) rfl ?_ ?_ ?_ ?_
  · cases o
    · exact comap_twinScheme_castSuccEmb
    · rfl
  · rw [hb, label_contextCap]
    exact le_top
  · rw [hb, hg]
    omega
  · rw [hb, hg]
    exact lt_add_of_pos_right _ (by simp)
  intro u hu i j hij hj
  rw [hb, hg] at hu
  obtain rfl := huniq u hu
  have hj5 : (j : ℕ) < 5 := by cases o <;> exact j.2
  rw [cellMap_extendByLast o (i := ⟨j, hj5⟩) (j := i) hij.symm]
  have hl := twinDonor_label_eq ξ o ⟨j, hj5⟩
  rw [show (Fin.cast (by cases o <;> rfl) ⟨j, hj5⟩ : Fin (twinDonor ξ o).card) = j from rfl] at hl
  rw [hl]
  have hj0 : (⟨j, hj5⟩ : Fin 5) ≠ 0 := by
    have hs : Fin.last 1 ∈ fiveCells.scope ⟨j, hj5⟩ := by cases o <;> exact hj
    have key : ∀ k : Fin 5, Fin.last 1 ∈ fiveCells.scope k → k ≠ 0 := by decide
    exact key _ hs
  generalize (⟨j, hj5⟩ : Fin 5) = k at hj0 ⊢
  -- a dead new cell is read as `⊥` by the reading cell
  have hbot (e : Fin 23) (he0 : cellKind e = 0) :
      (contextType ξ).ReadsThroughCap (twinScheme.{u} o) b 21 e ⊥ := by
    intro he _
    refine ⟨fun _ ↦ ?_, fun h ↦ absurd h bot_ne_top, fun μ n _ h ↦ absurd h WithBot.bot_ne_coe⟩
    -- the row of the reading cell, by kinds
    change kindRow o 5 (cellKind e) = ⊥
    rw [he0]
    rfl
  fin_cases k
  · exact absurd rfl hj0
  · exact hbot 3 rfl
  · cases o
    · exact readsThroughCap_twin ξ false b hb (.inl rfl) (e := 6) rfl
    · exact readsThroughCap_twin ξ true b hb (.inr rfl) (e := 6) rfl
  · cases o
    · exact readsThroughCap_twin ξ false b hb (.inr rfl) (e := 7) rfl
    · exact readsThroughCap_twin ξ true b hb (.inl rfl) (e := 7) rfl
  · exact hbot 15 rfl

/-- **The twin donors through the full-scope graded face**: the statement of
`StableRecoveryTwin.exists_isStableRecoveryScheme_twinDonors`, with the two stable recovery
schemes obtained by `StageType.IsStableRecoveryScheme.of_readsThroughUnivCap`. -/
theorem exists_isStableRecoveryScheme_twinDonors_of_readsThroughUnivCap :
    ∃ (Tp : StageType.{u} (blockStage (ξ + 1)) 3) (f : Fin 1 ↪ Fin 3) (γ : Ordinal.{u}),
      Tp.IsLegal ∧ restrictFace f Tp = some (twinRoot ξ) ∧ γ < blockStage (ξ + 1) ∧
      GradedCapCalibration ξ Tp f (twinDonor₁ ξ) γ ∧ GradedCapCalibration ξ Tp f (twinDonor₂ ξ) γ ∧
      (∃ E, Tp.IsStableRecoveryScheme f (twinDonor₁ ξ) γ E) ∧
      ∃ E, Tp.IsStableRecoveryScheme f (twinDonor₂ ξ) γ E :=
  ⟨contextType ξ, rootEmb, blockStage ξ, isLegal_contextType ξ,
    restrictFace_rootEmb_contextType ξ, blockStage_lt_blockStage_add_one ξ,
    gradedCapCalibration_contextType ξ true, gradedCapCalibration_contextType ξ false,
    ⟨_, isStableRecoveryScheme_twinScheme_of_readsThroughUnivCap ξ true⟩,
    ⟨_, isStableRecoveryScheme_twinScheme_of_readsThroughUnivCap ξ false⟩⟩

end StableRecoveryTwin

/-! ### The interior context -/

namespace StableRecoveryInterior

variable (ξ : Ordinal.{u}) {B : Label.{u}} (hB : IsSelfVisible 2 B ∧ AtStage (blockStage (ξ + 1)) B)

/-- **The interior context has a graded cap of full scope**: for a cap value `B ≥ λ_ξ + 2` and
`γ < λ_ξ + 2`, the context of four points, whose given cap `({1, 2}, 2)` avoids both extreme points
(`StableRecoveryInterior.scope_contextCap`), has a graded cap for the donor and `γ` whose scope is
all four points, by `StageType.GradedCapCalibration.exists_univ_cap`. -/
theorem exists_univ_cap_contextType
    (hBcap : ((blockStage ξ + ((2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) ≤ B)
    {γ : Ordinal.{u}} (hγ : γ < blockStage ξ + ((2 : ℕ) : Ordinal.{u})) :
    ∃ b, (contextType ξ hB).toCellScheme.scope b = univ ∧
      IsGradedCap ξ (contextType ξ hB) (donorType ξ hB) γ b :=
  (gradedCapCalibration_contextType ξ hB hBcap hγ).exists_univ_cap (isLegal_contextType ξ hB)

/-- The given cap of the interior context is not of full scope. -/
example : (contextType ξ hB).toCellScheme.scope (contextCap ξ hB) ≠ univ := by
  rw [scope_contextCap]
  decide

end StableRecoveryInterior

end VaughtConjecture.Continuation
