/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryCoatom
import VaughtConjecture.Continuation.StableRecoveryReading
import VaughtConjecture.Continuation.StableRecoveryTwin

/-!
# Reading coatom completions at one and at two coatom steps

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the private cap and the decoder of (R4)); semantic contract, item 8.

Tests of `StageType.HasReadingCoatomCompletions`
(`VaughtConjecture.Continuation.StableRecoveryCoatom`): at the input of
`VaughtConjecture.Continuation.StableRecoveryReading`, where the root is itself a closed coatom of
the context (one coatom step, `r = 1`), and at the twin donors of
`VaughtConjecture.Continuation.StableRecoveryTwin`, where the root `{2}` lies in the closed coatom
`{1, 2}` of the context `{0, 1, 2}` (two coatom steps, `r = 2`).  Each item below is compiled in
this repository (theorem named).

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

**The labelled twin scheme is a reading coatom completion**
(`Continuation.StableRecoveryTwin.isReadingCoatomCompletion_twinType`,
`Continuation.StableRecoveryTwin.exists_isReadingCoatomCompletion_twin`).  At the context of the
twin donors, the closed coatom `{1, 2}` through the root, the intermediate coface `twinCoface`
(the face of the labelled twin scheme along `{1, 2, 3}`, a coface of the face of the context along
the coatom, whose face along the root and the new point is the donor), and every graded cap of the
context for the donor (the cell of grade `3`), the labelled twin scheme of either order is a
reading coatom completion: its faces are the context and the intermediate coface, labels
included, and its only cell at `(univ, 3)` reads the new cells of the donor through the cap.

**What this does not show.**  In both tests the intermediate coface is the face of the very scheme
that completes it, so the case of an intermediate coface given from outside (by the coatom
extension property) is not tested; on the cells of the coatoms that case is settled by
`StageType.exists_codedReadingLabelling`, and the completion at the cells of full scope stays open.
The inputs are the degenerate ones of the earlier tests (recovery copies the marker or the root,
`N = k + 1` or `N = k + 2`), and the general statement is open.

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

/-! ### Two coatom steps: the twin donors -/

namespace VaughtConjecture.Continuation.StableRecoveryTwin

open Finset Label StageType CandidateCounterexamples StableRecoveryCounterexample
open Ordinal hiding univ

variable (ξ : Ordinal.{u})

/-- The closed coatom `{1, 2}` of the context, through the root `2`. -/
def coatomEmb : Fin 2 ↪ Fin 3 := ⟨![1, 2], by decide⟩

/-- The root inside the coatom: its point `1`. -/
def rootInCoatom : Fin 1 ↪ Fin 2 := ⟨fun _ ↦ 1, fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- The root factors through the coatom. -/
theorem rootInCoatom_trans_coatomEmb : rootInCoatom.trans coatomEmb = rootEmb :=
  Function.Embedding.ext fun i ↦ by fin_cases i; rfl

/-- The coatom followed by the new point spans the closed face `{1, 2, 3}` of the twin scheme. -/
theorem map_extendByLast_coatomEmb_mem_faces :
    univ.map (extendByLast coatomEmb) ∈ twinCells.faces := by
  decide

/-- The coatom spans a closed face of the context. -/
theorem map_coatomEmb_mem_faces : univ.map coatomEmb ∈ (contextType ξ).toCellScheme.faces := by
  -- a face of the context is a face of the twin scheme along the first three points
  change univ.map coatomEmb ∈ ((twinScheme.{u} true).comap Fin.castSuccEmb).toCellScheme.faces
  rw [Scheme.mem_comap_faces]
  decide

/-- The **intermediate coface** for the order `o`: the face of the labelled twin scheme along the
coatom followed by the new point, on the points `{1, 2, 3}`. -/
noncomputable def twinCoface (o : Bool) : StageType.{u} (blockStage (ξ + 1)) 3 :=
  (twinType ξ o).comap (extendByLast coatomEmb) map_extendByLast_coatomEmb_mem_faces

/-- The face of the context along the coatom. -/
noncomputable def coatomType : StageType.{u} (blockStage (ξ + 1)) 2 :=
  (contextType ξ).comap coatomEmb (map_coatomEmb_mem_faces ξ)

/-- The intermediate coface is a coface of the face of the context along the coatom. -/
theorem twinCoface_mem_cofaces (o : Bool) : twinCoface ξ o ∈ (coatomType ξ).cofaces := by
  refine ⟨(isLegal_twinScheme o).comap _ map_extendByLast_coatomEmb_mem_faces, ?_⟩
  unfold twinCoface
  rw [restrictFace_trans _ _ _
      (restrictFace_of_mem (twinType ξ o) _ map_extendByLast_coatomEmb_mem_faces),
    castSuccEmb_trans_extendByLast,
    ← restrictFace_trans _ _ _ (restrictFace_twinType_castSuccEmb ξ o)]
  exact restrictFace_of_mem _ _ _

/-- The face of the coatom type along the root is the twin root. -/
theorem restrictFace_rootInCoatom :
    restrictFace rootInCoatom (coatomType ξ) = some (twinRoot ξ) := by
  have hcoat : restrictFace coatomEmb (contextType ξ) = some (coatomType ξ) :=
    restrictFace_of_mem _ _ _
  rw [restrictFace_trans _ _ _ hcoat, rootInCoatom_trans_coatomEmb,
    restrictFace_rootEmb_contextType]

/-- The face of the intermediate coface along the root followed by the new point is the donor. -/
theorem restrictFace_twinCoface (o : Bool) :
    restrictFace (extendByLast rootInCoatom) (twinCoface ξ o) = some (twinDonor ξ o) := by
  unfold twinCoface
  rw [restrictFace_trans _ _ _
      (restrictFace_of_mem (twinType ξ o) _ map_extendByLast_coatomEmb_mem_faces),
    extendByLast_trans, rootInCoatom_trans_coatomEmb, restrictFace_twinType_extendByLast]

/-- The labels of the donors: `λ_ξ + 2` at the root, `⊥` at the dead cells, and the twins. -/
private theorem twinDonor_label_table (o : Bool) (k : Fin 5) :
    (twinDonor ξ o).label (Fin.cast (by cases o <;> rfl) k) =
      ![labelAdd (blockStage ξ) 2, ⊥, twinHi o (labelAdd (blockStage ξ) 2)
        (labelAdd (blockStage ξ) 1), twinLo o (labelAdd (blockStage ξ) 2)
        (labelAdd (blockStage ξ) 1), ⊥] k := by
  cases o <;> fin_cases k <;> rfl

/-- The only cell of grade `3` of the context is its cell `9` (the cell `19` of the twin scheme). -/
private theorem eq_nine_of_grade : ∀ i : Fin 10, twinCells.grade (contextCells i) = 3 → i = 9 := by
  decide

/-- The only cell of the twin scheme at `(univ, 3)` is the cell `21`. -/
private theorem eq_twentyOne : ∀ u : Fin 23,
    twinCells.gradedIndex u = ((univ : Finset (Fin 4)), 3) → u = 21 := by
  decide

/-- **The labelled twin scheme is a reading coatom completion** (two coatom steps, `r = 2`): for
every graded cap `b` of the context for the donor of the order `o` (necessarily the cap of grade
`3` at `({0, 1, 2}, 3)`), the labelled twin scheme is a reading coatom completion of the context
and the intermediate coface `twinCoface` along the closed coatom `{1, 2}`, for the donor along the
root inside the coatom (`StageType.IsReadingCoatomCompletion`): its faces are the context and the
intermediate coface, labels included, and its only cell at `(univ, 3)` reads the new cells of the
donor through the cap (`Continuation.StableRecoveryTwin.readsThroughCap_twin`). -/
theorem isReadingCoatomCompletion_twinType (o : Bool) {b : Fin (contextType ξ).card}
    {γ : Ordinal.{u}} (hcap : IsGradedCap ξ (contextType ξ) (twinDonor ξ o) γ b) :
    IsReadingCoatomCompletion (contextType ξ) coatomEmb (twinCoface ξ o) rootInCoatom
      (twinDonor ξ o) b (twinType ξ o) := by
  refine ⟨restrictFace_twinType_castSuccEmb ξ o,
    restrictFace_of_mem _ _ map_extendByLast_coatomEmb_mem_faces, ?_⟩
  rw [rootInCoatom_trans_coatomEmb]
  have hc10 := card_comap_castSuccEmb.{u} o
  obtain ⟨_, hctx'⟩ := (restrictFace_eq_some_iff _ _).mp (restrictFace_twinType_castSuccEmb ξ o)
  have hctx := congrArg StageType.toScheme hctx'
  obtain ⟨-, -, -, href⟩ := hcap
  obtain ⟨μ, n, -, -, hμ, ho, hn, -⟩ :=
    href (Fin.cast (by cases o <;> rfl) 0) (blockStage ξ + ((2 : ℕ) : Ordinal.{u}))
      (twinDonor_label_table ξ o 0)
  obtain ⟨-, rfl⟩ := (add_natCast_eq_add_natCast_iff (isSuccPrelimit_blockStage ξ) hμ).mp ho
  have hgb : (contextType ξ).toCellScheme.grade b = 3 := by
    have := (contextType ξ).grade_le b
    omega
  -- the cap is the cell `9` of the context, the cell `19` of the twin scheme
  have hb10 : (b : ℕ) < 10 := (card_contextType ξ) ▸ b.2
  have hb9 : (b : ℕ) = 9 := by
    have hg := Scheme.comap_grade (twinScheme.{u} true) Fin.castSuccEmb b
    rw [cellMap_castSuccEmb true (i := ⟨b, hb10⟩) (j := b) rfl] at hg
    exact congrArg Fin.val (eq_nine_of_grade ⟨b, hb10⟩ (hg.symm.trans hgb))
  let b' : Fin ((twinScheme.{u} o).comap Fin.castSuccEmb).card := ⟨9, by omega⟩
  have hb'19 : (twinScheme.{u} o).cellMap Fin.castSuccEmb b' = 19 :=
    cellMap_castSuccEmb o (i := 9) rfl
  refine ⟨isLegal_twinScheme o, map_castSuccEmb_mem_faces, hctx, map_extendByLast_mem_faces,
    by cases o <;> exact comap_twinScheme_extendByLast _, b', hb9.symm, fun u hu i j hij hj ↦ ?_⟩
  rw [hgb] at hu
  obtain rfl := eq_twentyOne u hu
  have hj5 : (j : ℕ) < 5 := by cases o <;> exact j.2
  -- the scheme of the labelled twin scheme is the twin scheme
  change (contextType ξ).ReadsThroughCap (twinScheme.{u} o) b' 21
    ((twinScheme.{u} o).cellMap (extendByLast rootEmb) i) ((twinDonor ξ o).label j)
  rw [cellMap_extendByLast o (i := ⟨j, hj5⟩) (j := i) hij.symm]
  have hl := twinDonor_label_table ξ o ⟨j, hj5⟩
  rw [show (Fin.cast (by cases o <;> rfl) ⟨j, hj5⟩ : Fin (twinDonor ξ o).card) = j from rfl] at hl
  rw [hl]
  have hj0 : (⟨j, hj5⟩ : Fin 5) ≠ 0 := by
    have hs : Fin.last 1 ∈ fiveCells.scope ⟨j, hj5⟩ := by cases o <;> exact hj
    have key : ∀ k : Fin 5, Fin.last 1 ∈ fiveCells.scope k → k ≠ 0 := by decide
    exact key _ hs
  generalize (⟨j, hj5⟩ : Fin 5) = k at hj0 ⊢
  -- a dead new cell is read as `⊥` by the reading cell
  have hbot (e : Fin 23) (he0 : cellKind e = 0) :
      (contextType ξ).ReadsThroughCap (twinScheme.{u} o) b' 21 e ⊥ := by
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
    · exact readsThroughCap_twin ξ false b' hb'19 (.inl rfl) rfl
    · exact readsThroughCap_twin ξ true b' hb'19 (.inr rfl) rfl
  · cases o
    · exact readsThroughCap_twin ξ false b' hb'19 (.inr rfl) rfl
    · exact readsThroughCap_twin ξ true b' hb'19 (.inl rfl) rfl
  · exact hbot 15 rfl

/-- **The clause of reading coatom completions holds at the twin donors, with two coatom steps**:
the context is legal, `{1, 2}` is a closed coatom of it containing the root, the intermediate
coface is a coface of the face along the coatom with the donor as its face along the root followed
by the new point, the twin root is the face of the coatom type along the root, the calibration
holds with a full-scope cap, and for every graded cap there is a reading coatom completion
(`Continuation.StableRecoveryTwin.isReadingCoatomCompletion_twinType`). -/
theorem exists_isReadingCoatomCompletion_twin (o : Bool) :
    (contextType ξ).IsLegal ∧
      restrictFace coatomEmb (contextType ξ) = some (coatomType ξ) ∧
      twinCoface ξ o ∈ (coatomType ξ).cofaces ∧
      restrictFace rootInCoatom (coatomType ξ) = some (twinRoot ξ) ∧
      twinDonor ξ o ∈ (twinRoot ξ).cofaces ∧
      restrictFace (extendByLast rootInCoatom) (twinCoface ξ o) = some (twinDonor ξ o) ∧
      (∃ b : Fin (contextType ξ).card, (contextType ξ).toCellScheme.scope b = univ ∧
        IsGradedCap ξ (contextType ξ) (twinDonor ξ o) (blockStage ξ) b) ∧
      ∀ (b : Fin (contextType ξ).card) (γ : Ordinal.{u}),
        IsGradedCap ξ (contextType ξ) (twinDonor ξ o) γ b →
          ∃ Q : StageType.{u} (blockStage (ξ + 1)) 4,
            IsReadingCoatomCompletion (contextType ξ) coatomEmb (twinCoface ξ o) rootInCoatom
              (twinDonor ξ o) b Q :=
  ⟨isLegal_contextType ξ, restrictFace_of_mem _ _ _, twinCoface_mem_cofaces ξ o,
    restrictFace_rootInCoatom ξ, twinDonor_mem_cofaces ξ o, restrictFace_twinCoface ξ o,
    GradedCapCalibration.exists_univ_cap (isLegal_contextType ξ)
      (gradedCapCalibration_contextType ξ o),
    fun _ _ hcap ↦ ⟨twinType ξ o, isReadingCoatomCompletion_twinType ξ o hcap⟩⟩

end VaughtConjecture.Continuation.StableRecoveryTwin
