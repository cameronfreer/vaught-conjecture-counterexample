/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.SeedLevelTopFacts
import VaughtConjecture.MainTheorem.CodedLevelBountifulTop

/-!
# Legality below the full grade of the replicated coded level

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier) and Correspondence, item 1
(the strongly coded legal stage types). All results here are native constructions of this
repository.

The statements of `VaughtConjecture.MainTheorem.SeedLevelTopFacts` about the levels over the padded
grade-one base, for the coded levels (`Seed.codedLvLevel`) over the coded ladder base
(`Seed.codedLvBase`). The proofs are those of `VaughtConjecture.MainTheorem.SeedLevelTopFacts`, with
the facts of the padded base replaced by those of the coded base
(`VaughtConjecture.Extension.CodedLadderBase`, `VaughtConjecture.Extension.CodedLadderLift`) and the
coded mirror lifts (`VaughtConjecture.MainTheorem.CodedMirrorLift`); the statements there that do
not mention the levels or the base are used unchanged.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}
  {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

/-! ### Coding -/

/-- **Every level up to the number of points is coded.** -/
theorem codedLvLevel_isCoded (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card ≤ B) :
    ∀ j, j + 1 ≤ m + 2 → (I.codedLvLevel g H B hd Q j).S.IsCoded
  | 0, _ => (I.attachmentBase g).isCoded_codedLadderBase H
  | j + 1, hj => by
    have hN := codedLvLevel_good (B := B) (hd := hd) hH hcard hQ hB j (by omega)
    -- the next level appends the cells of the catalogue
    change ((I.codedLvLevel g H B hd Q j).nS B (I.lvCat g B hd Q (j + 2))).IsCoded
    refine Scheme.isCoded_appendFullCells (codedLvLevel_isCoded hH hcard hQ hB j (by omega))
      fun i z ↦ ?_
    obtain ⟨hRB, hRl, -, -, -⟩ := mem_lvCat.mp ((I.lvCat g B hd Q (j + 2)).equivFin.symm i).2
    exact lt_omega0_sq_of_mem_codeGrid (hN.Φ_mem_codeGrid _ hRB
      (hRl.mono (X := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_rfl, by omega⟩) z)

/-- **The replicated level is coded**: the copies read the rows of their originals. -/
theorem codedLvRep_isCoded (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card ≤ B) {J : ℕ}
    (hJ : J + 1 ≤ m + 2) (hN : (I.codedLvLevel g H B hd Q J).Good B (lvAdm hd Q)) :
    hN.rep.IsCoded :=
  Scheme.isCoded_mirror (codedLvLevel_isCoded hH hcard hQ hB J hJ)

/-! ### The cells of full scope of the levels -/

/-- **The first level has a cell at `(univ, 1)`**: a ladder point of the ladder base. -/
theorem codedLvLevel1_exists_gradedIndex_one (hH : 0 < H) :
    ∃ z, (I.codedLvLevel1 g H).S.toCellScheme.gradedIndex z = ((univ : Finset (Fin (m + 2))),
        1) := by
  obtain ⟨a⟩ := (inferInstance : Nonempty (Scheme.RankMember (I.attachmentBase g).S H))
  refine ⟨Fin.natAdd _ (Scheme.ladderEquiv _ _ H (a, Sum.inl ⟨0, hH⟩)), ?_⟩
  -- the first level appends the ladder points to the attachment
  change ((I.attachmentBase g).S.appendFullCellsScheme 1 _).gradedIndex (Fin.natAdd _ _) = _
  rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd]

/-- **The cell of the bottom state of the level at the grade `j + 2`** has graded index
`(univ, j + 2)`. -/
theorem codedLvLevel_gradedIndex_bot (j : ℕ) :
    (I.codedLvLevel g H B hd Q (j + 1)).S.toCellScheme.gradedIndex
      (Fin.natAdd _ ((I.lvCat g B hd Q (j + 2)).equivFin ⟨_, bot_mem_lvCat (j + 2)⟩)) =
      ((univ : Finset (Fin (m + 2))), j + 2) :=
  Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _

/-- **A graded index of a level is one of every higher level**: the next levels append cells. -/
theorem codedLvLevel_exists_gradedIndex_of_le {i : ℕ} {X : Finset (Fin (m + 2)) × ℕ}
    (h : ∃ z, (I.codedLvLevel g H B hd Q i).S.toCellScheme.gradedIndex z = X) :
    ∀ J, i ≤ J → ∃ z, (I.codedLvLevel g H B hd Q J).S.toCellScheme.gradedIndex z = X := by
  intro J hJ
  induction J, hJ using Nat.le_induction with
  | base => exact h
  | succ J _ ih =>
    obtain ⟨z, hz⟩ := ih
    exact ⟨Fin.castAdd _ z, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ z).trans hz⟩

/-- **The level at the grade `J + 1` has a cell at `(univ, k)` for every `1 ≤ k ≤ J + 1`**: a
ladder point at `k = 1`, the cell of the bottom state otherwise. -/
theorem codedLvLevel_exists_gradedIndex_univ (hH : 0 < H) (J : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (hkJ : k ≤ J + 1) :
    ∃ z, (I.codedLvLevel g H B hd Q J).S.toCellScheme.gradedIndex z =
      ((univ : Finset (Fin (m + 2))), k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases j with _ | j
  · exact codedLvLevel_exists_gradedIndex_of_le (i := 0) (codedLvLevel1_exists_gradedIndex_one hH) J
      (Nat.zero_le _)
  · exact codedLvLevel_exists_gradedIndex_of_le (i := j + 1) ⟨_, codedLvLevel_gradedIndex_bot j⟩ J
      (by omega)

/-! ### Completeness of the replicated level -/

/-- **The cells of full scope of the replicated top level**: at `(univ, k)`, `1 ≤ k ≤ m + 1`. -/
theorem codedLvRep_exists_gradedIndex_univ (hH : 0 < H)
    (hN : (I.codedLvLevel g H B hd Q m).Good B (lvAdm hd Q)) {k : ℕ} (hk : 1 ≤ k)
        (hkm : k ≤ m + 1) :
    ∃ z, hN.rep.toCellScheme.gradedIndex z = ((univ : Finset (Fin (m + 2))), k) := by
  obtain ⟨z, hz⟩ := codedLvLevel_exists_gradedIndex_univ (B := B) (hd := hd) (Q := Q) hH m hk hkm
  exact ⟨Fin.castAdd _ z, (Scheme.gradedIndex_mirror_castAdd z).trans hz⟩

/-- **The cells inside the context face or the donor face of a replicated level**: every graded
face of the amalgam of proper scope inside the context face or the donor face is the graded index
of a cell of the attachment, literal in the level and in its copies. -/
theorem codedLvRep_exists_gradedIndex_attached {J : ℕ}
    (hN : (I.codedLvLevel g H B hd Q J).Good B (lvAdm hd Q)) {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ I.amalgam.toCellScheme.gradedFaces) (hXu : X.1 ≠ univ)
    (hXc : X.1 ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      X.1 ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))) :
    ∃ z, hN.rep.toCellScheme.gradedIndex z = X := by
  obtain ⟨c, hc⟩ := I.exists_gradedIndex_eq X hX hXu
  have hcL : c ∈ I.attachmentCells g := (I.mem_attachmentCells g).mpr (by
    rw [show I.amalgam.toCellScheme.scope c = X.1 from congrArg Prod.fst hc]
    exact hXc)
  obtain ⟨e, he⟩ : c ∈ Set.range (I.amalgam.toScheme.lowerEmb (I.attachmentCells g)) := by
    have h := ((I.attachmentCells g).range_orderEmbOfFin rfl).symm ▸ (mem_coe.mpr hcL)
    exact h
  refine ⟨Fin.castAdd _ ((I.codedLvLevel g H B hd Q J).attEmb e),
    (Scheme.gradedIndex_mirror_castAdd _).trans ((hN.gradedIndex_attEmb e).trans ?_)⟩
  -- the cell of the attachment is the lower embedding of the cell of the amalgam
  change I.amalgam.toCellScheme.gradedIndex (I.amalgam.toScheme.lowerEmb _ e) = X
  rw [he, hc]

/-- **The copies at the mixed faces of the replicated top level**: at a mixed face `U` and a grade
`1 ≤ k ≤ #U`, a copy of the cell of full scope at `(univ, k)`. -/
theorem codedLvRep_exists_gradedIndex_mixed (hH : 0 < H)
    (hN : (I.codedLvLevel g H B hd Q m).Good B (lvAdm hd Q)) {U : Finset (Fin (m + 2))}
    (hU : U ∈ I.mixedFaces g) {k : ℕ} (hk : 1 ≤ k) (hkU : k ≤ #U) :
    ∃ z, hN.rep.toCellScheme.gradedIndex z = (U, k) := by
  have hlt : #U < m + 2 := by
    simpa using card_lt_card (ssubset_univ_iff.mpr ((I.mem_mixedFaces g).mp hU).2.1)
  obtain ⟨f, hf⟩ := codedLvLevel_exists_gradedIndex_univ (B := B) (hd := hd) (Q := Q) hH m hk
    (by omega)
  exact Scheme.exists_gradedIndex_mirror hU hkU hf

/-- **Completeness of the replicated top level below the full grade.** -/
theorem codedLvRep_exists_gradedIndex (hH : 0 < H)
    (hN : (I.codedLvLevel g H B hd Q m).Good B (lvAdm hd Q)) {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ hN.rep.toCellScheme.gradedFaces) (hX2 : X.2 < m + 2) :
    ∃ z, hN.rep.toCellScheme.gradedIndex z = X := by
  have hXF : X.1 ∈ I.amalgam.toCellScheme.faces := by
    have h : X.1 ∈ (I.codedLvLevel g H B hd Q m).S.toCellScheme.faces := hX.1
    rwa [faces_codedLvLevel] at h
  by_cases hXu : X.1 = univ
  · obtain ⟨z, hz⟩ := codedLvRep_exists_gradedIndex_univ hH hN hX.2.1 (k := X.2) (by omega)
    exact ⟨z, hz.trans (Prod.ext hXu.symm rfl)⟩
  by_cases hXc : X.1 ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      X.1 ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))
  · exact codedLvRep_exists_gradedIndex_attached hN ⟨hXF, hX.2⟩ hXu hXc
  · push Not at hXc
    have hU : X.1 ∈ I.mixedFaces g := (I.mem_mixedFaces g).mpr ⟨hXF, hXu, hXc.1, hXc.2⟩
    exact codedLvRep_exists_gradedIndex_mixed hH hN hU hX.2.1 hX.2.2

/-- **Every cell of the replicated top level has grade below `m + 2`**
(`Seed.ALvl.Good.rep_grade_lt` at the level `m`). -/
theorem codedLvRep_grade_lt (hN : (I.codedLvLevel g H B hd Q m).Good B (lvAdm hd Q))
    (z : Fin hN.rep.card) : hN.rep.toCellScheme.grade z < m + 2 :=
  hN.rep_grade_lt z

/-! ### At the seed choice -/

/-- **The replicated top level at the seed choice is coded**, at the strict block bound. -/
theorem codedLvRep_isCoded_seedChoice' {p : StageType.{u} α n}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) :
    (codedLvLevel_good (seedHeightLevel_pos I g) (card_attachmentBase_le_seedHeightLevel I g) hQ
      (two_mul_card_le_seedBlockBound' I g) (hd := hdA) m (by omega)).rep.IsCoded :=
  codedLvRep_isCoded (seedHeightLevel_pos I g) (card_attachmentBase_le_seedHeightLevel I g) hQ
    (two_mul_card_le_seedBlockBound' I g) (by omega) _

/-- **The replicated top level at the seed choice is complete below the full grade**, at the
strict block bound. -/
theorem codedLvRep_exists_gradedIndex_seedChoice'
    (hN : (I.codedLvLevel g (I.seedHeightLevel g) (I.seedBlockBound' g) hd Q m).Good
      (I.seedBlockBound' g) (lvAdm hd Q)) {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ hN.rep.toCellScheme.gradedFaces) (hX2 : X.2 < m + 2) :
    ∃ z, hN.rep.toCellScheme.gradedIndex z = X :=
  codedLvRep_exists_gradedIndex (seedHeightLevel_pos I g) hN hX hX2

/-- **The replicated top level at the seed choice is legal below the full grade**, at the strict
block bound: well formed (`Seed.ALvl.Good.isWellFormed_rep`), coded, consistent
(`Seed.ALvl.Good.isConsistent_rep`), bountiful (`Seed.codedLvRep_isBountiful_seedChoice'`), of
grades
below `m + 2` and complete below the full grade. -/
theorem codedLvRep_isLegalBelowFullGrade_seedChoice' {p : StageType.{u} α n}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (hd' : d ∈ p.cofaces)
    (hn : 0 < n)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hpair : ∀ j, Q.CorrectAt I.left.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hd'.2) :
    (codedLvLevel_good (seedHeightLevel_pos I g) (card_attachmentBase_le_seedHeightLevel I g) hQ
      (two_mul_card_le_seedBlockBound' I g) (hd := hdA) m
        (by omega)).rep.IsLegalBelowFullGrade where
  isWellFormed := ALvl.Good.isWellFormed_rep _ (faces_codedLvLevel m)
  isCoded := codedLvRep_isCoded_seedChoice' hte hdA hQ
  isConsistent := ALvl.Good.isConsistent_rep _
  isBountiful := codedLvRep_isBountiful_seedChoice' hte hd' hn hdA hpair hQ hrel
  grade_lt := codedLvRep_grade_lt _
  exists_gradedIndex_eq _ hX hX2 := codedLvRep_exists_gradedIndex_seedChoice' _ hX hX2

end Seed

end VaughtConjecture
