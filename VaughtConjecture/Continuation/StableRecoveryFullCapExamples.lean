/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryFullCap
import VaughtConjecture.Continuation.StableRecoveryInterior
import VaughtConjecture.Continuation.StableRecoveryTwin

/-!
# Stable recovery schemes with a full-scope cap: tests

Tests of `VaughtConjecture.Continuation.StableRecoveryFullCap` at two inputs of the graded cap
calibration (`StageType.GradedCapCalibration`) at which a stable recovery scheme is known.  Each
item is compiled in this repository (theorem named).

**The twin donors through the full-scope graded face**
(`StableRecoveryTwin.isStableRecoveryScheme_twinScheme_of_readsThroughCap_univ`).  At the context of
three points of `VaughtConjecture.Continuation.StableRecoveryTwin`, whose cap is the cell
`({0, 1, 2}, 3)` (full scope, labelled the formal top), the twin scheme of each order of the twins
is a stable recovery scheme by `StageType.IsStableRecoveryScheme.of_readsThroughCap_univ`, with the
coface of `T⁺↓λ_ξ` given by legality of the twin scheme
(`StageType.exists_mem_cofaces_reduce_of_isLegal`).  The only cell at `(univ, 3)` is the reading
cell; the hypotheses "the cap and the new cells lie below the reading cell" of
`StageType.IsStableRecoveryScheme.of_readsThroughCap` hold by the general theorem.
`StableRecoveryTwin.exists_isStableRecoveryScheme_twinDonors_of_readsThroughCap_univ` restates
`StableRecoveryTwin.exists_isStableRecoveryScheme_twinDonors` through this route.

**A full-scope cap at the interior context**
(`StableRecoveryInterior.exists_univ_cap_contextType`).  At the context of four points of
`VaughtConjecture.Continuation.StableRecoveryInterior`, whose cap `({1, 2}, 2)` avoids both extreme
points of the context, `StageType.GradedCapCalibration.exists_univ_cap` gives a graded cap of full
scope `{0, 1, 2, 3}`.  For such a cap the graded faces of grade `N` containing it and a new cell
reduce to the ground set (`Scheme.setOf_gradedFaces_univCap_eq_singleton`; argued, not formalized
at this input: that theorem is not applied in this file).  This concerns the faces of the new cap
only; the given interior cap and its two faces are unchanged.

**The interior scheme is a cap-reading extension**
(`StableRecoveryInterior.isCapReadingExtension_interiorScheme`).  For every full-scope graded cap of
the interior context (necessarily the cell `({0, 1, 2, 3}, 2)`, of grade `2`), the interior scheme
is a cap-reading extension (`StageType.IsCapReadingExtension`): its only cell at `(univ, 2)` reads
the new cells through the given cap, hence through the full-scope cap of the same grade
(`StageType.ReadsThroughCap.of_grade_eq`).  So the interior input satisfies the clause of
`StageType.HasCapReadingExtensions`, and its stable recovery scheme is recovered through
`StageType.IsCapReadingExtension.isStableRecoveryScheme`.

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
`StageType.IsStableRecoveryScheme.of_readsThroughCap_univ`.  The cap `({0, 1, 2}, 3)` has grade
`3 > 1`; the coface of `T⁺↓λ_ξ` comes from legality of the twin scheme; the reading cell `21` is
the only cell at `(univ, 3)`, and reads the dead new cells as `⊥` and the twins through the root
(`StableRecoveryTwin.readsThroughCap_twin`). -/
theorem isStableRecoveryScheme_twinScheme_of_readsThroughCap_univ (o : Bool) :
    (contextType ξ).IsStableRecoveryScheme rootEmb (twinDonor ξ o) (blockStage ξ)
      (twinScheme.{u} o) := by
  have hc10 := card_comap_castSuccEmb.{u} o
  let b : Fin ((twinScheme.{u} o).comap Fin.castSuccEmb).card := ⟨9, by omega⟩
  have hb : (twinScheme.{u} o).cellMap Fin.castSuccEmb b = 19 :=
    cellMap_castSuccEmb o (i := 9) rfl
  have hg : (twinScheme.{u} o).toCellScheme.grade 19 = 3 := rfl
  have huniq : ∀ u : Fin 23, twinCells.gradedIndex u = ((univ : Finset (Fin 4)), 3) → u = 21 := by
    decide
  refine IsStableRecoveryScheme.of_readsThroughCap_univ (restrictFace_rootEmb_contextType ξ)
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
schemes obtained by `StageType.IsStableRecoveryScheme.of_readsThroughCap_univ`. -/
theorem exists_isStableRecoveryScheme_twinDonors_of_readsThroughCap_univ :
    ∃ (Tp : StageType.{u} (blockStage (ξ + 1)) 3) (f : Fin 1 ↪ Fin 3) (γ : Ordinal.{u}),
      Tp.IsLegal ∧ restrictFace f Tp = some (twinRoot ξ) ∧ γ < blockStage (ξ + 1) ∧
      GradedCapCalibration ξ Tp f (twinDonor₁ ξ) γ ∧ GradedCapCalibration ξ Tp f (twinDonor₂ ξ) γ ∧
      (∃ E, Tp.IsStableRecoveryScheme f (twinDonor₁ ξ) γ E) ∧
      ∃ E, Tp.IsStableRecoveryScheme f (twinDonor₂ ξ) γ E :=
  ⟨contextType ξ, rootEmb, blockStage ξ, isLegal_contextType ξ,
    restrictFace_rootEmb_contextType ξ, blockStage_lt_blockStage_add_one ξ,
    gradedCapCalibration_contextType ξ true, gradedCapCalibration_contextType ξ false,
    ⟨_, isStableRecoveryScheme_twinScheme_of_readsThroughCap_univ ξ true⟩,
    ⟨_, isStableRecoveryScheme_twinScheme_of_readsThroughCap_univ ξ false⟩⟩

end StableRecoveryTwin

/-! ### The interior context -/

namespace StableRecoveryInterior

open StableRecoveryReading (markerLabel)

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

/-- **The interior scheme is a cap-reading extension for every full-scope graded cap** of the
interior context.  The only full-scope cell of the context of grade above `1` that is not dead is
the cell `({0, 1, 2, 3}, 2)` (the cell `22` of the interior scheme, of the cap kind), so a
full-scope graded cap has grade `2`; the only cell of the interior scheme at `(univ, 2)` is the
reading cell `24`, which reads the new cells of the donor through the given cap
`({1, 2}, 2)` (`StableRecoveryInterior.readsThroughCap_of_cellKind_eq_five`), hence through the
full-scope cap, of the same grade (`StageType.ReadsThroughCap.of_grade_eq`; no label of the donor
is the formal top). -/
theorem isCapReadingExtension_interiorScheme (b : Fin (contextType ξ hB).card)
    (hbu : (contextType ξ hB).toCellScheme.scope b = univ) {γ : Ordinal.{u}}
    (hcap : IsGradedCap ξ (contextType ξ hB) (donorType ξ hB) γ b) :
    IsCapReadingExtension (contextType ξ hB) rootEmb (donorType ξ hB) b interiorScheme := by
  have hb20 : (b : ℕ) < 20 := lt_of_lt_of_eq b.2 (card_contextType ξ hB)
  have hmap : interiorScheme.{u}.cellMap Fin.castSuccEmb b = contextCells ⟨b, hb20⟩ :=
    cellMap_castSuccEmb (i := ⟨b, hb20⟩) rfl
  -- the scope of the cap in the interior scheme is the first four points
  have hsc : interiorCells.scope (contextCells ⟨b, hb20⟩) =
      univ.map (Fin.castSuccEmb : Fin 4 ↪ Fin 5) := by
    have h1 := interiorScheme.{u}.map_comap_scope (Fin.castSuccEmb : Fin 4 ↪ Fin 5) b
    rw [hmap, show (interiorScheme.{u}.comap Fin.castSuccEmb).toCellScheme.scope b = univ from hbu]
      at h1
    exact h1.symm
  have hgr : (contextType ξ hB).toCellScheme.grade b =
      interiorCells.grade (contextCells ⟨b, hb20⟩) := by
    -- the grade of a cell of the context is the grade of its cell
    change interiorCells.grade (interiorScheme.{u}.cellMap Fin.castSuccEmb b) = _
    rw [hmap]
  have hlab : (contextType ξ hB).label b =
      kindValue (markerLabel ξ) (markerLabel ξ) B (cellKind (contextCells ⟨b, hb20⟩)) := by
    -- the label of a cell of the context is the label of its cell
    change interiorLabel _ _ B (interiorScheme.{u}.cellMap Fin.castSuccEmb b) = _
    rw [hmap]
    rfl
  obtain ⟨hcb, hkb, -, -⟩ := hcap
  have key : ∀ k : Fin 20, interiorCells.scope (contextCells k) =
      univ.map (Fin.castSuccEmb : Fin 4 ↪ Fin 5) → 1 < interiorCells.grade (contextCells k) →
      contextCells k = 22 ∨ cellKind (contextCells k) = 0 := by
    decide
  have h22 : contextCells ⟨b, hb20⟩ = 22 := by
    rcases key _ hsc (hgr ▸ hkb) with h | h
    · exact h
    · rw [hlab, h] at hcb
      exact absurd hcb (by simp [kindValue])
  have hg2 : (contextType ξ hB).toCellScheme.grade b = 2 := by
    rw [hgr, h22]
    rfl
  refine ⟨isLegal_interiorScheme, map_castSuccEmb_mem_faces, rfl, map_extendByLast_mem_faces, rfl,
    b, rfl, fun u hu i j hij hj ↦ ?_⟩
  rw [hg2] at hu
  obtain rfl : u = 24 := by
    have huniq : ∀ u : Fin 35, interiorCells.gradedIndex u = ((univ : Finset (Fin 5)), 2) →
        u = 24 := by
      decide
    exact huniq u hu
  have hread := ((readsThroughCap_of_cellKind_eq_five ξ hB (s := 24) rfl) i j hij hj).2 24 rfl
  -- no label of the donor is the formal top
  have hne : (donorType ξ hB).label j ≠ ⊤ := by
    have hj4 : (j : ℕ) < 4 := lt_of_lt_of_eq j.2 (card_donorType ξ hB)
    rw [donorType_label ξ hB j ⟨j, hj4⟩ rfl]
    generalize (⟨j, hj4⟩ : Fin 4) = k
    fin_cases k
    · exact bot_ne_top
    · exact bot_ne_top
    · exact fun h ↦ absurd (WithBot.coe_injective (h : markerLabel ξ = ⊤)) WithTop.coe_ne_top
    · exact bot_ne_top
  refine hread.of_grade_eq hne ?_ ?_
  · -- both caps have grade `2`
    rw [interiorScheme_toCellScheme.{u}, cellMap_contextCap, hmap, h22]
    rfl
  · rw [cellMap_contextCap]
    -- membership below a pair is the order of graded indices
    change interiorCells.gradedIndex 16 ≤ interiorCells.gradedIndex 24
    decide

/-- **The interior input satisfies the clause of `StageType.HasCapReadingExtensions`**: every
full-scope graded cap of the interior context has a cap-reading extension, and with the
full-scope cap of `exists_univ_cap_contextType` it is a stable recovery scheme
(`StageType.IsCapReadingExtension.isStableRecoveryScheme`). -/
example (hBcap : ((blockStage ξ + ((2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) ≤ B)
    {γ : Ordinal.{u}} (hγ : γ < blockStage ξ + ((2 : ℕ) : Ordinal.{u})) :
    (∀ b, (contextType ξ hB).toCellScheme.scope b = univ →
      IsGradedCap ξ (contextType ξ hB) (donorType ξ hB) γ b →
        ∃ E, IsCapReadingExtension (contextType ξ hB) rootEmb (donorType ξ hB) b E) ∧
      ∃ E, (contextType ξ hB).IsStableRecoveryScheme rootEmb (donorType ξ hB) γ E := by
  refine ⟨fun b hbu hcap ↦ ⟨_, isCapReadingExtension_interiorScheme ξ hB b hbu hcap⟩, ?_⟩
  obtain ⟨b, hbu, hcap⟩ := exists_univ_cap_contextType ξ hB hBcap hγ
  exact ⟨_, (isCapReadingExtension_interiorScheme ξ hB b hbu hcap).isStableRecoveryScheme
    (restrictFace_rootType ξ hB) (donorType_mem_cofaces ξ hB) hcap⟩

end StableRecoveryInterior

end VaughtConjecture.Continuation
