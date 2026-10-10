/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelBountifulTop

/-!
# Coding and completeness of the replicated top level

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier re-rendered per grade).

**Coding** (`Seed.lvLevel_isCoded`, `Seed.lvRep_isCoded`): the first level is the ladder base,
coded (`Scheme.LadderBaseData.isCoded_ladderBase`); the next level appends cells whose rows are row
labellings of states of the catalogue, with values in the code grid
(`Seed.ALvl.Good.Φ_mem_codeGrid`), below `ω ^ 2` (`Label.lt_omega0_sq_of_mem_codeGrid`); the copies
read the rows of their originals (`Scheme.isCoded_mirror`).

**Completeness below the full grade** (`Seed.lvRep_exists_gradedIndex`): every graded face `X` of
the replicated top level with `X.2 < m + 2` is the graded index of a cell:
* `X.1 = univ`: a cell of the level (`Seed.lvRep_exists_gradedIndex_univ`): at the grade `1` a
  ladder point of the ladder base (`Seed.lvLevel1_exists_gradedIndex_one`), at the grade `k + 2`
  the cell of the bottom state of the catalogue (`Seed.bot_mem_lvCat`,
  `Seed.lvLevel_gradedIndex_bot`), carried to the higher levels
  (`Seed.lvLevel_exists_gradedIndex_of_le`);
* `X.1` inside the context face or the donor face: a cell of the attachment, a cell of the amalgam
  (`Seed.lvRep_exists_gradedIndex_attached`);
* `X.1` mixed: a copy of a cell of full scope (`Seed.lvRep_exists_gradedIndex_mixed`,
  `Scheme.exists_gradedIndex_mirror`).

With the grades below `m + 2` (`Seed.lvRep_grade_lt`) and the bountifulness of the top level
(`Seed.lvRep_isBountiful`), the replicated top level at the seed choice `Seed.seedHeightLevel`,
`Seed.seedBlockBound'` is legal below the full grade
(`Seed.lvRep_isLegalBelowFullGrade_seedChoice'`).
No bound of the height by the number of cells of the amalgam is used.

## References

Completeness is [Kni26, Definition 2.5.15]; the growth construction is that of [Kni26, §4].
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
theorem lvLevel_isCoded (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card ≤ B) :
    ∀ j, j + 1 ≤ m + 2 → (I.lvLevel g H B hd Q j).S.IsCoded
  | 0, _ => (I.attachmentBase g).isCoded_ladderBase H
  | j + 1, hj => by
    have hN := lvLevel_good (B := B) (hd := hd) hH hcard hQ hB j (by omega)
    -- the next level appends the cells of the catalogue
    change ((I.lvLevel g H B hd Q j).nS B (I.lvCat g B hd Q (j + 2))).IsCoded
    refine Scheme.isCoded_appendFullCells (lvLevel_isCoded hH hcard hQ hB j (by omega))
      fun i z ↦ ?_
    obtain ⟨hRB, hRl, -, -, -⟩ := mem_lvCat.mp ((I.lvCat g B hd Q (j + 2)).equivFin.symm i).2
    exact lt_omega0_sq_of_mem_codeGrid (hN.Φ_mem_codeGrid _ hRB
      (hRl.mono (X := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_rfl, by omega⟩) z)

/-- **The replicated level is coded**: the copies read the rows of their originals. -/
theorem lvRep_isCoded (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card ≤ B) {J : ℕ}
    (hJ : J + 1 ≤ m + 2) (hN : (I.lvLevel g H B hd Q J).Good B (lvAdm hd Q)) :
    hN.rep.IsCoded :=
  Scheme.isCoded_mirror (lvLevel_isCoded hH hcard hQ hB J hJ)

/-! ### The cells of full scope of the levels -/

/-- **The bottom state is in the catalogue** at every grade. -/
theorem bot_mem_lvCat (k : ℕ) :
    (fun _ ↦ ⊥ : Fin (I.attachment g).card → Label.{u}) ∈ I.lvCat g B hd Q k :=
  mem_lvCat.mpr ⟨fun _ ↦ mem_insert_self _ _, Rows.isLawfulBelow_const_bot _,
    fun _ ↦ isSelfVisible_bot 1, funext fun _ ↦ orbitCode_eq_bot_iff.mpr rfl,
    I.attachAdmits_bot g hd Q _⟩

/-- **The first level has a cell at `(univ, 1)`**: a ladder point of the ladder base. -/
theorem lvLevel1_exists_gradedIndex_one (hH : 0 < H) :
    ∃ z, (I.lvLevel1 g H).S.toCellScheme.gradedIndex z = ((univ : Finset (Fin (m + 2))), 1) := by
  obtain ⟨a⟩ := (inferInstance : Nonempty (Scheme.RankMember (I.attachmentBase g).S H))
  refine ⟨Fin.natAdd _ (Scheme.ladderEquiv _ _ H (a, Sum.inl ⟨0, hH⟩)), ?_⟩
  -- the first level appends the ladder points to the attachment
  change ((I.attachmentBase g).S.appendFullCellsScheme 1 _).gradedIndex (Fin.natAdd _ _) = _
  rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd]

/-- **The cell of the bottom state of the level at the grade `j + 2`** has graded index
`(univ, j + 2)`. -/
theorem lvLevel_gradedIndex_bot (j : ℕ) :
    (I.lvLevel g H B hd Q (j + 1)).S.toCellScheme.gradedIndex
      (Fin.natAdd _ ((I.lvCat g B hd Q (j + 2)).equivFin ⟨_, bot_mem_lvCat (j + 2)⟩)) =
      ((univ : Finset (Fin (m + 2))), j + 2) :=
  Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _

/-- **A graded index of a level is one of every higher level**: the next levels append cells. -/
theorem lvLevel_exists_gradedIndex_of_le {i : ℕ} {X : Finset (Fin (m + 2)) × ℕ}
    (h : ∃ z, (I.lvLevel g H B hd Q i).S.toCellScheme.gradedIndex z = X) :
    ∀ J, i ≤ J → ∃ z, (I.lvLevel g H B hd Q J).S.toCellScheme.gradedIndex z = X := by
  intro J hJ
  induction J, hJ using Nat.le_induction with
  | base => exact h
  | succ J _ ih =>
    obtain ⟨z, hz⟩ := ih
    exact ⟨Fin.castAdd _ z, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ z).trans hz⟩

/-- **The level at the grade `J + 1` has a cell at `(univ, k)` for every `1 ≤ k ≤ J + 1`**: a
ladder point at `k = 1`, the cell of the bottom state otherwise. -/
theorem lvLevel_exists_gradedIndex_univ (hH : 0 < H) (J : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (hkJ : k ≤ J + 1) :
    ∃ z, (I.lvLevel g H B hd Q J).S.toCellScheme.gradedIndex z =
      ((univ : Finset (Fin (m + 2))), k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases j with _ | j
  · exact lvLevel_exists_gradedIndex_of_le (i := 0) (lvLevel1_exists_gradedIndex_one hH) J
      (Nat.zero_le _)
  · exact lvLevel_exists_gradedIndex_of_le (i := j + 1) ⟨_, lvLevel_gradedIndex_bot j⟩ J
      (by omega)

/-! ### Completeness of the replicated level -/

/-- **The cells of full scope of the replicated top level**: at `(univ, k)`, `1 ≤ k ≤ m + 1`. -/
theorem lvRep_exists_gradedIndex_univ (hH : 0 < H)
    (hN : (I.lvLevel g H B hd Q m).Good B (lvAdm hd Q)) {k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m + 1) :
    ∃ z, hN.rep.toCellScheme.gradedIndex z = ((univ : Finset (Fin (m + 2))), k) := by
  obtain ⟨z, hz⟩ := lvLevel_exists_gradedIndex_univ (B := B) (hd := hd) (Q := Q) hH m hk hkm
  exact ⟨Fin.castAdd _ z, (Scheme.gradedIndex_mirror_castAdd z).trans hz⟩

/-- **The cells inside the context face or the donor face of a replicated level**: every graded
face of the amalgam of proper scope inside the context face or the donor face is the graded index
of a cell of the attachment, literal in the level and in its copies. -/
theorem lvRep_exists_gradedIndex_attached {J : ℕ}
    (hN : (I.lvLevel g H B hd Q J).Good B (lvAdm hd Q)) {X : Finset (Fin (m + 2)) × ℕ}
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
  refine ⟨Fin.castAdd _ ((I.lvLevel g H B hd Q J).attEmb e),
    (Scheme.gradedIndex_mirror_castAdd _).trans ((hN.gradedIndex_attEmb e).trans ?_)⟩
  -- the cell of the attachment is the lower embedding of the cell of the amalgam
  change I.amalgam.toCellScheme.gradedIndex (I.amalgam.toScheme.lowerEmb _ e) = X
  rw [he, hc]

/-- **The copies at the mixed faces of the replicated top level**: at a mixed face `U` and a grade
`1 ≤ k ≤ #U`, a copy of the cell of full scope at `(univ, k)`. -/
theorem lvRep_exists_gradedIndex_mixed (hH : 0 < H)
    (hN : (I.lvLevel g H B hd Q m).Good B (lvAdm hd Q)) {U : Finset (Fin (m + 2))}
    (hU : U ∈ I.mixedFaces g) {k : ℕ} (hk : 1 ≤ k) (hkU : k ≤ #U) :
    ∃ z, hN.rep.toCellScheme.gradedIndex z = (U, k) := by
  have hlt : #U < m + 2 := by
    simpa using card_lt_card (ssubset_univ_iff.mpr ((I.mem_mixedFaces g).mp hU).2.1)
  obtain ⟨f, hf⟩ := lvLevel_exists_gradedIndex_univ (B := B) (hd := hd) (Q := Q) hH m hk
    (by omega)
  exact Scheme.exists_gradedIndex_mirror hU hkU hf

/-- **Completeness of the replicated top level below the full grade.** -/
theorem lvRep_exists_gradedIndex (hH : 0 < H)
    (hN : (I.lvLevel g H B hd Q m).Good B (lvAdm hd Q)) {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ hN.rep.toCellScheme.gradedFaces) (hX2 : X.2 < m + 2) :
    ∃ z, hN.rep.toCellScheme.gradedIndex z = X := by
  have hXF : X.1 ∈ I.amalgam.toCellScheme.faces := by
    have h : X.1 ∈ (I.lvLevel g H B hd Q m).S.toCellScheme.faces := hX.1
    rwa [faces_lvLevel] at h
  by_cases hXu : X.1 = univ
  · obtain ⟨z, hz⟩ := lvRep_exists_gradedIndex_univ hH hN hX.2.1 (k := X.2) (by omega)
    exact ⟨z, hz.trans (Prod.ext hXu.symm rfl)⟩
  by_cases hXc : X.1 ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      X.1 ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))
  · exact lvRep_exists_gradedIndex_attached hN ⟨hXF, hX.2⟩ hXu hXc
  · push Not at hXc
    have hU : X.1 ∈ I.mixedFaces g := (I.mem_mixedFaces g).mpr ⟨hXF, hXu, hXc.1, hXc.2⟩
    exact lvRep_exists_gradedIndex_mixed hH hN hU hX.2.1 hX.2.2

/-- **Every cell of the replicated level at the grade `m + 1` has grade below `m + 2`**: a cell of
full scope has grade at most `m + 1`, a cell of proper scope at most the size of its scope, and a
copy has the grade of its original. -/
theorem ALvl.Good.rep_grade_lt {N : I.ALvl g H (m + 1)} (hN : N.Good B (lvAdm hd Q))
    (z : Fin hN.rep.card) : hN.rep.toCellScheme.grade z < m + 2 := by
  -- a cell of the replicated level has the grade of its original
  change N.S.toCellScheme.grade (N.S.mirrorOrig (I.mixedFaces g) z) < m + 2
  rcases N.inv (N.S.mirrorOrig (I.mixedFaces g) z) with h | h
  · omega
  · have hlt : #(N.S.toCellScheme.scope (N.S.mirrorOrig (I.mixedFaces g) z)) < m + 2 := by
      simpa using card_lt_card (ssubset_univ_iff.mpr h)
    exact (hN.wf.isWellFormed.grade_le_card _).trans_lt hlt

/-- **Every cell of the replicated top level has grade below `m + 2`**
(`Seed.ALvl.Good.rep_grade_lt` at the level `m`). -/
theorem lvRep_grade_lt (hN : (I.lvLevel g H B hd Q m).Good B (lvAdm hd Q))
    (z : Fin hN.rep.card) : hN.rep.toCellScheme.grade z < m + 2 :=
  hN.rep_grade_lt z

/-! ### At the seed choice -/

/-- **The replicated top level at the seed choice is coded**, at the strict block bound. -/
theorem lvRep_isCoded_seedChoice' {p : StageType.{u} α n}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) :
    (lvLevel_good (seedHeightLevel_pos I g) (card_attachmentBase_le_seedHeightLevel I g) hQ
      (two_mul_card_le_seedBlockBound' I g) (hd := hdA) m (by omega)).rep.IsCoded :=
  lvRep_isCoded (seedHeightLevel_pos I g) (card_attachmentBase_le_seedHeightLevel I g) hQ
    (two_mul_card_le_seedBlockBound' I g) (by omega) _

/-- **The replicated top level at the seed choice is complete below the full grade**, at the
strict block bound. -/
theorem lvRep_exists_gradedIndex_seedChoice'
    (hN : (I.lvLevel g (I.seedHeightLevel g) (I.seedBlockBound' g) hd Q m).Good
      (I.seedBlockBound' g) (lvAdm hd Q)) {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ hN.rep.toCellScheme.gradedFaces) (hX2 : X.2 < m + 2) :
    ∃ z, hN.rep.toCellScheme.gradedIndex z = X :=
  lvRep_exists_gradedIndex (seedHeightLevel_pos I g) hN hX hX2

/-- **The replicated top level at the seed choice is legal below the full grade**, at the strict
block bound: well formed (`Seed.ALvl.Good.isWellFormed_rep`), coded, consistent
(`Seed.ALvl.Good.isConsistent_rep`), bountiful (`Seed.lvRep_isBountiful_seedChoice'`), of grades
below `m + 2` and complete below the full grade. -/
theorem lvRep_isLegalBelowFullGrade_seedChoice' {p : StageType.{u} α n}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (hd' : d ∈ p.cofaces)
    (hn : 0 < n)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hpair : ∀ j, Q.CorrectAt I.left.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hd'.2) :
    (lvLevel_good (seedHeightLevel_pos I g) (card_attachmentBase_le_seedHeightLevel I g) hQ
      (two_mul_card_le_seedBlockBound' I g) (hd := hdA) m
        (by omega)).rep.IsLegalBelowFullGrade where
  isWellFormed := ALvl.Good.isWellFormed_rep _ (faces_lvLevel m)
  isCoded := lvRep_isCoded_seedChoice' hte hdA hQ
  isConsistent := ALvl.Good.isConsistent_rep _
  isBountiful := lvRep_isBountiful_seedChoice' hte hd' hn hdA hpair hQ hrel
  grade_lt := lvRep_grade_lt _
  exists_gradedIndex_eq _ hX hX2 := lvRep_exists_gradedIndex_seedChoice' _ hX hX2

end Seed

end VaughtConjecture
