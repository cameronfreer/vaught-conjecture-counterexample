/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryCoatom
import VaughtConjecture.Continuation.StableRecoveryReading

/-!
# A reading coatom completion at one closed coatom

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the private cap and the decoder of (R4)); semantic contract, item 8.

A test of `StageType.HasReadingCoatomCompletions` (`VaughtConjecture.Continuation.
StableRecoveryCoatom`) at the input of `VaughtConjecture.Continuation.StableRecoveryReading`, where
the root is itself a closed coatom of the context (one coatom step, `r = 1`).  The item below is
compiled in this repository (theorem named).

**The reading type is a reading coatom completion**
(`Continuation.StableRecoveryReading.isReadingCoatomCompletion_readingType`).  At the context type
`T⁺` on two points, its coatom the root `{1}` with face the root type, the donor as intermediate
coface (the root is the whole coatom, so the intermediate coface is the donor itself, along the
identity of the root), and every graded cap of `T⁺` for the donor (necessarily of grade `2`; its
scope is not used, so in particular every full-scope one), the reading type on three points is a
reading coatom completion (`StageType.IsReadingCoatomCompletion`): its faces along the first two
points and along the root followed by the new point are `T⁺` and the donor, labels included, and
its only cell at `(univ, 2)` reads the new cells of the donor through the cap: the dead new cells
as `⊥`, and the new cell labelled `λ_ξ + 1` at `1`, where it reads the marker.  The clause of
`StageType.HasReadingCoatomCompletions` therefore holds at this input
(`Continuation.StableRecoveryReading.exists_isReadingCoatomCompletion`), at every `ξ`, with the
calibration satisfiable there.

**What this does not show.**  The intermediate coface here is the donor itself, so the case of an
uncontrolled intermediate coface (two or more coatom steps) is not tested; the input is the
degenerate one of `VaughtConjecture.Continuation.StableRecoveryReading` (recovery copies the
marker, `N = k + 1`); and the general statement is open.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Continuation.StableRecoveryReading

open Finset Label StageType
open Ordinal hiding univ

variable (ξ : Ordinal.{u})

/-- The root followed by the new point spans a closed face of the reading scheme. -/
private theorem map_extendByLast_rootEmb_mem_faces :
    univ.map (extendByLast rootEmb) ∈ readingCells.faces := by
  decide

/-- The donor is the face of the reading type along the root followed by the new point. -/
theorem restrictFace_donorType :
    restrictFace (extendByLast rootEmb) (readingType ξ) = some (donorType ξ) :=
  restrictFace_of_mem _ _ map_extendByLast_rootEmb_mem_faces

/-- **The reading type is a reading coatom completion**: for every graded cap `b` of the context
type for the donor (of grade `2`; its scope is not used), the reading type is a reading coatom
completion of the context type and the donor along the closed coatom `rootEmb`, for the donor
along the identity of the root and the cap `b` (`StageType.IsReadingCoatomCompletion`). -/
theorem isReadingCoatomCompletion_readingType {b : Fin (contextType ξ).card} {γ : Ordinal.{u}}
    (hcap : IsGradedCap ξ (contextType ξ) (donorType ξ) γ b) :
    IsReadingCoatomCompletion (contextType ξ) rootEmb (donorType ξ)
      (Function.Embedding.refl (Fin 1)) (donorType ξ) b (readingType ξ) := by
  have htrans : (Function.Embedding.refl (Fin 1)).trans rootEmb = rootEmb :=
    Function.Embedding.ext fun _ ↦ rfl
  refine ⟨restrictFace_contextType ξ, restrictFace_donorType ξ, ?_⟩
  rw [htrans]
  -- the grade of the cap is `2`: above `1` and at most the number of points
  have hgb : (contextType ξ).toCellScheme.grade b = 2 := by
    have h1 := hcap.2.1
    have h2 := (contextType ξ).grade_le b
    omega
  obtain ⟨a, ha, -, hal⟩ := exists_marker ξ
  refine ⟨isLegal_readingScheme, (restrictFace_eq_some_iff _ _).mp (restrictFace_contextType ξ)
    |>.1, rfl, map_extendByLast_rootEmb_mem_faces, rfl, b, rfl, fun u hu i j hij hj ↦ ?_⟩
  rw [hgb] at hu
  -- the only cell at `(univ, 2)` is the reading cell `8`
  have huniq : ∀ u : Fin 10, readingCells.gradedIndex u = ((univ : Finset (Fin 3)), 2) → u = 8 := by
    decide
  obtain rfl := huniq u hu
  obtain rfl : i = j := Fin.ext hij
  have h2 : (2 : Fin 3) ∈
      readingCells.scope (readingScheme.{u}.cellMap (extendByLast rootEmb) i) := by
    have : Fin.last 1 ∈ (readingCells.scope
        (readingScheme.{u}.cellMap (extendByLast rootEmb) i)).preimage (extendByLast rootEmb)
        (extendByLast rootEmb).injective.injOn := hj
    rw [Finset.mem_preimage, extendByLast_last] at this
    exact this
  -- the label of the new cell `i` of the donor is the label of its image in the reading type
  change (contextType ξ).ReadsThroughCap readingScheme b 8
    (readingScheme.{u}.cellMap (extendByLast rootEmb) i)
    (readingLabel (markerLabel ξ) (markerLabel ξ) ⊤
      (readingScheme.{u}.cellMap (extendByLast rootEmb) i))
  have hvis := readingScheme.{u}.cellMap_mem (extendByLast rootEmb) i
  generalize readingScheme.{u}.cellMap (extendByLast rootEmb) i = d at h2 hvis ⊢
  -- the grade of the cap in the reading scheme is its grade in the context type
  have hgb' : readingCells.grade (readingScheme.{u}.cellMap Fin.castSuccEmb b) = 2 := hgb
  rcases eq_of_mem_newCells hvis h2 with rfl | rfl | rfl
  · -- the new cell `2`, labelled `⊥`, read as `⊥`
    exact fun _ _ ↦ ⟨fun _ ↦ rfl, fun h ↦ absurd h bot_ne_top,
      fun μ n _ h ↦ absurd h WithBot.bot_ne_coe⟩
  · -- the new cell `4`, labelled `λ_ξ + 1`, read at `1` with the marker
    refine fun _ _ ↦ ⟨fun h ↦ absurd h WithBot.coe_ne_bot,
      fun h ↦ absurd (WithBot.coe_injective (h : markerLabel ξ = ⊤)) WithTop.coe_ne_top,
      fun μ n hμ h ↦ ?_⟩
    obtain rfl := eq_one_of_markerLabel_eq ξ hμ h
    have ha8 : readingScheme.{u}.cellMap Fin.castSuccEmb a ∈
        readingCells.below (readingCells.gradedIndex 8) := by
      rw [ha]
      exact show readingCells.gradedIndex 3 ≤ readingCells.gradedIndex 8 by decide
    refine ⟨by rw [hgb']; decide, a, a, 1, ((0 : ℕ) : Ordinal.{u}), rfl, hal.trans h,
      by rw [hgb']; decide, ha8, ?_, rfl⟩
    -- the row of the reading cell at the marker, the cell `3`
    change readingScheme.{u}.rows.row 8 ⟨_, ha8⟩ = _
    have h3 : (⟨readingScheme.{u}.cellMap Fin.castSuccEmb a, ha8⟩ :
        readingCells.below (readingCells.gradedIndex 8)) = ⟨3, ha ▸ ha8⟩ := Subtype.ext ha
    rw [h3]
    rfl
  · -- the new cell `6`, labelled `⊥`, read as `⊥`
    exact fun _ _ ↦ ⟨fun _ ↦ rfl, fun h ↦ absurd h bot_ne_top,
      fun μ n _ h ↦ absurd h WithBot.bot_ne_coe⟩

/-- **The clause of reading coatom completions holds at the reading input**: the context type is
legal, the root is a closed coatom of it with face the root type, the donor is a coface of the
root type and its own face along the identity of the root followed by the new point, the
calibration holds with a full-scope cap, and for every graded cap there is a reading coatom
completion (`Continuation.StableRecoveryReading.isReadingCoatomCompletion_readingType`). -/
theorem exists_isReadingCoatomCompletion :
    (contextType ξ).IsLegal ∧ restrictFace rootEmb (contextType ξ) = some (rootType ξ) ∧
      donorType ξ ∈ (rootType ξ).cofaces ∧
      restrictFace (Function.Embedding.refl (Fin 1)) (rootType ξ) = some (rootType ξ) ∧
      restrictFace (extendByLast (Function.Embedding.refl (Fin 1))) (donorType ξ) =
        some (donorType ξ) ∧
      (∃ b : Fin (contextType ξ).card, (contextType ξ).toCellScheme.scope b = univ ∧
        IsGradedCap ξ (contextType ξ) (donorType ξ) (blockStage ξ) b) ∧
      ∀ (b : Fin (contextType ξ).card) (γ : Ordinal.{u}),
        IsGradedCap ξ (contextType ξ) (donorType ξ) γ b →
          ∃ Q : StageType.{u} (blockStage (ξ + 1)) 3,
            IsReadingCoatomCompletion (contextType ξ) rootEmb (donorType ξ)
              (Function.Embedding.refl (Fin 1)) (donorType ξ) b Q :=
  ⟨isLegal_contextType ξ, restrictFace_rootType ξ, donorType_mem_cofaces ξ, restrictFace_refl _,
    by rw [extendByLast_refl, restrictFace_refl],
    GradedCapCalibration.exists_univ_cap (isLegal_contextType ξ)
      (gradedCapCalibration_contextType ξ),
    fun _ _ hcap ↦ ⟨readingType ξ, isReadingCoatomCompletion_readingType ξ hcap⟩⟩

end VaughtConjecture.Continuation.StableRecoveryReading
