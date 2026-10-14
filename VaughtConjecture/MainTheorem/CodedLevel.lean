/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.CodedLadderContract
import VaughtConjecture.MainTheorem.LevelCodedBase
import VaughtConjecture.MainTheorem.ReplicatedLevelGrades

/-!
# The coded levels over the attachment

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier) and Correspondence, item 1
(the strongly coded legal stage types).  All results here are native constructions of this
repository.

The levels over the attachment (`Seed.ALvl`, their next level `Seed.ALvl.next` and good levels
`Seed.ALvl.Good`) depend on the ladder base only through the first level (`Seed.lvLevel1`, over the
padded grade-one base).  The **coded levels** start instead from the coded ladder base over the
attachment (`Seed.codedLvBase`) and continue by the same next level.

* `Seed.codedLvLevel1`, `Seed.codedLvLevel1_good`: the coded initial level, with the section of
  `Seed.lvLevel1` (`Seed.lvBaseSec`), is good, through the lawfulness of the extension of a state
  in the coded ladder base (`Scheme.LadderBaseData.isLawfulBelow_stateExtOf_coded`).
* `Seed.ALvl.CodedGood`: **the coded invariant**: a good level, strongly coded, in which the coded
  ladder base embeds (`Seed.ALvl.embed`) as a lower embedding keeping scopes and rows.  It gives the
  coded rungs at every level (`Seed.ALvl.CodedGood.codedLadderRungs`).
* `Seed.codedLvLevel1_codedGood`: the coded initial level satisfies it when the attachment is
  strongly coded (in particular when both coatom types are,
  `Seed.codedLvLevel1_codedGood_of_coatoms`).
* `Seed.ALvl.CodedGood.next`: **the successor step**.  The fields of a good level are kept
  (`Seed.ALvl.Good.next`); the old rows and the embedding of the coded base are kept by appending
  cells; the row of each new cell, of grade `j + 1`, is the row labelling `Seed.ALvl.Φ` of a state
  `R` of the catalogue at `j + 1`, whose values lie in the code grid at `j + 1`
  (`Seed.ALvl.Good.Φ_mem_codeGrid`: the section values from the catalogue values, `R e ∈ codeGrid
  (j + 1) B`, through the field `Seed.ALvl.Good.mem`; the agreement-height entries in the grid
  `grid (j + 1) B ⊆ codeGrid (j + 1) B`), hence are strongly coded at the owner grade `j + 1`
  (`Label.isStronglyCoded_of_mem_codeGrid`: finite part at most `j + 1`).
* `Seed.codedLvLevel`, `Seed.codedLvLevel_codedGood`: the coded levels at every grade up to the
  number of points.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Scheme.LadderBaseData

variable {n : ℕ} {B : LadderBaseData.{u} n} {H : ℕ}

/-- **The extension with the rank member from the grade one is lawful below the grade `k` in the
coded ladder base** (native construction),
for a state lawful below `(univ, k)` (`k ≥ 1`) whose values are self-visible at `1`: it agrees below
`(univ, k)` with the extension of the truncation of the state to the grades at most `k`, a lawful
state, along the same rank member (`Scheme.isLawful_codedLadderExtend`). -/
theorem isLawfulBelow_stateExtOf_coded (hH : 0 < H) (hcard : B.S.card ≤ H) {k : ℕ} (hk : 1 ≤ k)
    {R : Fin B.S.card → Label.{u}}
    (hR : B.S.rows.IsLawfulBelow ((univ : Finset (Fin n)), k) fun d ↦ R d)
    (hv1 : ∀ e, IsSelfVisible 1 (R e)) :
    (B.codedLadderBase H).rows.IsLawfulBelow ((univ : Finset (Fin n)), k) fun t ↦
      B.stateExtOf R (RankMember.ofLawfulBelowOne B.wf hcard
        (hR.mono (show ((univ : Finset (Fin n)), 1) ≤ ((univ : Finset (Fin n)), k) from
          ⟨subset_rfl, hk⟩))) t := by
  classical
  set a := RankMember.ofLawfulBelowOne B.wf hcard
    (hR.mono (show ((univ : Finset (Fin n)), 1) ≤ ((univ : Finset (Fin n)), k) from
      ⟨subset_rfl, hk⟩)) with ha
  set T : Fin B.S.card → Label.{u} := fun d ↦ if B.S.toCellScheme.grade d ≤ k then R d else ⊥
    with hT
  set v : Fin (B.ladderBase H).card → Label.{u} :=
    Fin.append T fun j ↦ posTable R (baseIndex H (rankProf B.S H) a (Fin.natAdd _ j)) with hv
  have hlaw : (B.codedLadderBase H).rows.IsLawful v := by
    refine isLawful_codedLadderExtend B.wf hH (rankProf_le _ H) a (monotone_posTable)
      posTable_zero (isSelfVisible_posTable hv1) (fun _ hi _ ↦ posTable_ne_bot (by omega))
      ?_ fun t ht ↦ ?_
    · have e : (fun d ↦ v (Fin.castAdd _ d)) = T := funext fun d ↦ Fin.append_left _ _ d
      rw [e]
      exact isLawful_truncate hR
    · induction t using Fin.addCases with
      | left d =>
        rw [appendFullCellsScheme_grade_castAdd] at ht
        change Fin.append T _ (Fin.castAdd _ d) = _
        rw [Fin.append_left, baseIndex_castAdd]
        change (if B.S.toCellScheme.grade d ≤ k then R d else ⊥) = _
        rw [ite_eq_left (ht.trans_le hk)]
        exact (posTable_rankVector hv1 d).symm
      | right j => exact Fin.append_right _ _ j
  have e : (fun t : (B.codedLadderBase H).toCellScheme.below ((univ : Finset (Fin n)), k) ↦
      B.stateExtOf R a t) =
      fun t : (B.codedLadderBase H).toCellScheme.below ((univ : Finset (Fin n)), k) ↦ v t := by
    funext t
    obtain ⟨t, htk⟩ := t
    induction t using Fin.addCases with
    | left d =>
      have hd : B.S.toCellScheme.grade d ≤ k := by
        have := htk.2
        change (B.S.appendFullCellsScheme 1 _).grade (Fin.castAdd _ d) ≤ k at this
        rwa [appendFullCellsScheme_grade_castAdd] at this
      change Fin.append R _ (Fin.castAdd _ d) = Fin.append T _ (Fin.castAdd _ d)
      rw [Fin.append_left, Fin.append_left, hT]
      beta_reduce
      rw [ite_eq_left hd]
    | right j =>
      change Fin.append R _ (Fin.natAdd _ j) = Fin.append T _ (Fin.natAdd _ j)
      rw [Fin.append_right, Fin.append_right]
  rw [e]
  exact hlaw.isLawfulBelow _

end Scheme.LadderBaseData

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ}

section Defs

variable (I : Seed.{u} α m) (g : Fin n ↪ Fin m) (H : ℕ)

/-- **The coded ladder base of the levels** (native construction): the attachment with its ladder
points, with the coded rows. -/
noncomputable abbrev codedLvBase : Scheme.{u} (m + 2) := (I.attachmentBase g).codedLadderBase H

/-- **The coded initial level** (native construction): the coded ladder base, the section of the
first level (`Seed.lvBaseSec`), the identity embedding of the ladder base. -/
noncomputable def codedLvLevel1 : I.ALvl g H 1 where
  S := I.codedLvBase g H
  σ := I.lvBaseSec g H
  embed t := t
  inv z := by
    induction z using Fin.addCases with
    | left d =>
      refine .inr ?_
      rw [Scheme.appendFullCellsScheme_scope_castAdd]
      exact (I.attachmentBase g).scope_ne_univ d
    | right i => exact .inl (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le

end Defs

variable {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}

/-- **The coded initial level is good**, for `0 < H` and the attachment with at most `H` cells, at
every predicate: as for `Seed.lvLevel1_good`, with the consistency of the coded ladder base and the
lawfulness of the extension of a state in it. -/
theorem codedLvLevel1_good (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop) :
    (I.codedLvLevel1 g H).Good B A := by
  have hemb := Scheme.isLowerEmbedding_castAdd (S := (I.attachmentBase g).S) 1
    (Scheme.ladderCard (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H)
    (Scheme.codedBaseRow H (Scheme.rankProf (I.attachmentBase g).S H)) (I.attachmentBase g).noFull
  refine
    { wf := (I.attachmentBase g).isWellFormed_codedLadderBase H (by omega)
      consistent := (I.attachmentBase g).isConsistent_codedLadderBase H hH
      lowerEmb := hemb
      scope_attEmb := fun d ↦ Scheme.appendFullCellsScheme_scope_castAdd _ _ _ d
      comap_rows := Scheme.comap_rows_castAdd (h := (I.attachmentBase g).noFull)
      mem_range := fun z hz ↦ ?_
      lawful := fun P hP hv _ ↦ ?_
      mem := fun P hP hP1 z ↦ ?_
      literal := fun P hP d ↦ ?_
      capAgree := fun P P' hP hP' _ h hh _ hag z ↦ ?_
      readable := fun Q hQ _ hQ1 z ↦ ?_ }
  · induction z using Fin.addCases with
    | left d => exact ⟨d, rfl⟩
    | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
  · change (I.codedLvBase g H).rows.IsLawfulBelow _ fun z ↦ I.lvBaseSec g H P z
    rw [lvBaseSec_of_isLawfulBelow hcard hP]
    exact (I.attachmentBase g).isLawfulBelow_stateExtOf_coded hH hcard le_rfl hP hv
  · change I.lvBaseSec g H P z ∈ _
    rw [lvBaseSec_of_isLawfulBelow hcard hP1]
    rcases Scheme.LadderBaseData.stateExtOf_cases P _ z with h | h | ⟨e, h⟩ <;> rw [h]
    · exact mem_insert_self _ _
    · exact one_mem_codeGrid (by omega)
    · exact hP e
  · change I.lvBaseSec g H P (Fin.castAdd _ d) = P d
    rw [lvBaseSec_of_isLawfulBelow hcard hP]
    exact Scheme.LadderBaseData.stateExtOf_castAdd' (B' := I.attachmentBase g) P _ d
  · change min (I.lvBaseSec g H P z) h = min (I.lvBaseSec g H P' z) h
    rw [lvBaseSec_of_isLawfulBelow hcard hP, lvBaseSec_of_isLawfulBelow hcard hP']
    by_cases h0 : h = ⊥
    · rw [h0, min_bot_right, min_bot_right]
    exact ((I.attachmentBase g).min_stateExtOf_eq hcard h0 (hh.mono (by omega)) hP hP'
      (fun d ↦ (hag d).symm) z).symm
  · change IsReadableAt 2 Q (I.lvBaseSec g H Q z)
    rw [lvBaseSec_of_isLawfulBelow hcard hQ1]
    rcases Scheme.LadderBaseData.stateExtOf_cases Q _ z with h | h | ⟨e, h⟩ <;> rw [h]
    · exact .inl rfl
    · refine .inr (.inr (by_cases (fun hkey ↦ .inl ?_) fun hkey ↦ .inr hkey))
      obtain ⟨e, he0, hek⟩ := hkey
      have h1 : visibilityReplace 2 2 (1 : Label.{u}) = gridPoint 2 0 :=
        visibilityReplace_one_eq_gridPoint le_rfl
      exact (isOrbitKey_congr hek).mp (isOrbitKey_of_natural hQ he0 (hek.trans h1))
    · exact isReadableAt_apply Q e

/-! ### The coded invariant -/

variable (B) in
/-- **A coded good level** (native construction), for a predicate `A` on states: a good level
(`Seed.ALvl.Good`), strongly coded, in which the coded ladder base embeds along `Seed.ALvl.embed`
as a lower embedding keeping scopes and rows. -/
structure ALvl.CodedGood {j : ℕ} (N : I.ALvl g H j)
    (A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop) : Prop
    extends ALvl.Good B N A where
  /-- The rows of the level are strongly coded, each at the grade of its cell. -/
  stronglyCoded : N.S.rows.IsStronglyCoded
  /-- The coded ladder base embeds as a lower embedding. -/
  baseEmb : (I.codedLvBase g H).toCellScheme.IsLowerEmbedding N.S.toCellScheme N.embed
  /-- The embedding of the coded ladder base keeps scopes. -/
  scope_embed : ∀ t, N.S.toCellScheme.scope (N.embed t) = (I.codedLvBase g H).toCellScheme.scope t
  /-- The embedding of the coded ladder base keeps rows: the rows of the level pull back to the
  rows of the coded ladder base. -/
  comap_base : N.S.rows.comap baseEmb = (I.codedLvBase g H).rows

namespace ALvl.CodedGood

variable {j : ℕ} {N : I.ALvl g H j} {A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop}

theorem gradedIndex_embed (hN : N.CodedGood B A) (t : Fin (I.lvBase g H).card) :
    N.S.toCellScheme.gradedIndex (N.embed t) = (I.codedLvBase g H).toCellScheme.gradedIndex t :=
  Prod.ext (hN.scope_embed t) (hN.baseEmb.grade_eq t)

/-- **A coded good level reads the coded ladder base as the base does.** -/
theorem rowAt_embed (hN : N.CodedGood B A) (s t : Fin (I.lvBase g H).card) :
    N.S.rowAt (N.embed s) (N.embed t) = (I.codedLvBase g H).rowAt s t := by
  have hiff : N.embed t ∈ N.S.toCellScheme.below (N.S.toCellScheme.gradedIndex (N.embed s)) ↔
      t ∈ (I.codedLvBase g H).toCellScheme.below
        ((I.codedLvBase g H).toCellScheme.gradedIndex s) := by
    rw [CellScheme.mem_below, CellScheme.mem_below, hN.gradedIndex_embed, hN.gradedIndex_embed]
  by_cases ht : t ∈ (I.codedLvBase g H).toCellScheme.below
      ((I.codedLvBase g H).toCellScheme.gradedIndex s)
  · rw [Scheme.rowAt_of_mem (hiff.mpr ht), Scheme.rowAt_of_mem ht]
    have h := congrArg (fun R : (I.codedLvBase g H).toCellScheme.Rows ↦ R.row s ⟨t, ht⟩)
      hN.comap_base
    simp only [CellScheme.Rows.comap_row] at h
    exact h
  · rw [Scheme.rowAt_of_notMem (mt hiff.mp ht), Scheme.rowAt_of_notMem ht]

/-- The rung `i` (clamped below `H`) of the member `a`, as a cell of a level. -/
noncomputable def rung (N : I.ALvl g H j) (hH : 0 < H)
    (a : Scheme.RankMember (I.attachmentBase g).S H) (i : ℕ) : Fin N.S.card :=
  N.embed (Fin.natAdd _ (Scheme.ladderEquiv (I.attachmentBase g).S
    (Scheme.RankMember (I.attachmentBase g).S H) H (a, Sum.inl ⟨min i (H - 1), by omega⟩)))

/-- **The coded rungs at a coded good level**: the rungs of the rank members, embedded from the
coded ladder base, satisfy the coded rung contract (`Scheme.CodedLadderRungs`). -/
theorem codedLadderRungs (hN : N.CodedGood B A) (hH : 0 < H) :
    N.S.CodedLadderRungs H (rung N hH) := by
  have hwf := (I.attachmentBase g).wf
  have hprof := Scheme.rankProf_le (I.attachmentBase g).S H
  refine ⟨hH, fun a i hi ↦ ?_, fun a i hi ↦ ?_, fun a i hi hi0 ↦ ?_⟩
  · rw [rung, hN.gradedIndex_embed]
    exact Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _
  · rw [rung, hN.rowAt_embed,
      Scheme.rowAt_codedLadderBase_rung (hS := (I.attachmentBase g).noFull) hwf hprof]
    simp only [min_eq_left (show i ≤ H - 1 by omega)]
  · have h := Scheme.rowAt_codedLadderBase_rung_pred (hS := (I.attachmentBase g).noFull) hwf
      hprof a i hi hi0
    rw [rung, rung, hN.rowAt_embed]
    simp only [min_eq_left (show i ≤ H - 1 by omega), min_eq_left (show i - 1 ≤ H - 1 by omega)]
    exact h

end ALvl.CodedGood

/-- **The coded initial level is a coded good level** (native construction), for `0 < H`, the
attachment with at most `H` cells and strongly coded, at every predicate. -/
theorem codedLvLevel1_codedGood (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hsc : (I.attachment g).rows.IsStronglyCoded)
    (A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop) :
    (I.codedLvLevel1 g H).CodedGood B A where
  toGood := codedLvLevel1_good hH hcard A
  stronglyCoded := (I.attachmentBase g).isStronglyCoded_codedLadderBase H hsc
  baseEmb := IsLowerEmbedding.id _
  scope_embed _ := rfl
  comap_base := rfl

/-- **The coded initial level of a seed with strongly coded coatom types is a coded good level**
(`Seed.isStronglyCoded_attachment`). -/
theorem codedLvLevel1_codedGood_of_coatoms (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hl : I.left.rows.IsStronglyCoded) (hr : I.right.rows.IsStronglyCoded)
    (A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop) :
    (I.codedLvLevel1 g H).CodedGood B A :=
  codedLvLevel1_codedGood hH hcard (I.isStronglyCoded_attachment g hl hr) A

/-! ### The successor step -/

namespace ALvl.CodedGood

variable {j : ℕ} {N : I.ALvl g H j} {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

/-- **The new rows are strongly coded at their grade** (native construction): the row of the cell
of a state `R` of the catalogue at `j + 1` in the next level is the row labelling `N.Φ B C R`,
whose values lie in the code grid at `j + 1` (`Seed.ALvl.Good.Φ_mem_codeGrid`): the section values
`N.σ R` by the field `Seed.ALvl.Good.mem` at the catalogue values `R e ∈ codeGrid (j + 1) B`, and
the agreement heights in `grid (j + 1) B`.  So they are strongly coded at `j + 1`
(`Label.isStronglyCoded_of_mem_codeGrid`). -/
theorem isStronglyCoded_Φ (hN : N.CodedGood B (lvAdm hd Q))
    {R : Fin (I.attachment g).card → Label.{u}} (hR : R ∈ I.lvCat g B hd Q (j + 1))
    (z : Fin (N.S.card + (I.lvCat g B hd Q (j + 1)).card)) :
    IsStronglyCoded (j + 1) (N.Φ B (I.lvCat g B hd Q (j + 1)) R z) := by
  obtain ⟨hRB, hRl, -, -, -⟩ := mem_lvCat.mp hR
  exact isStronglyCoded_of_mem_codeGrid (hN.toGood.Φ_mem_codeGrid _ hRB
    (hRl.mono (X := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_rfl, by omega⟩) z)

/-- **The successor step of the coded levels** (native construction): the next level of a coded
good level on the catalogue at `j + 1` is a coded good level.  The fields of a good level are those
of `Seed.ALvl.Good.next`; strong coding keeps the old rows and gives the new rows from the code
grid at the owner grade `j + 1` (`Seed.ALvl.CodedGood.isStronglyCoded_Φ`); the coded ladder base
stays embedded with its rows, the new cells being appended last. -/
theorem next {p₀ : StageType.{u} α n}
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hN : N.CodedGood B (lvAdm hd Q))
    (hQ : Q.ClassCalibrated hte) (hj : j + 1 ≤ m + 2) (hB : 2 * (I.attachment g).card ≤ B) :
    (N.next B (I.lvCat g B hd Q (j + 1))).CodedGood B (lvAdm hd Q) := by
  set C := I.lvCat g B hd Q (j + 1) with hC
  have hemb := Scheme.isLowerEmbedding_castAdd (S := N.S) (j + 1) C.card
    (fun i ↦ N.Φ B C (C.equivFin.symm i).1) N.not_le
  refine
    { toGood := hN.toGood.next hQ hj hB
      stronglyCoded := Scheme.isStronglyCoded_appendFullCells (h := N.not_le) hN.stronglyCoded
        fun i z ↦ hN.isStronglyCoded_Φ (C.equivFin.symm i).2 z
      baseEmb := hemb.comp hN.baseEmb
      scope_embed := fun t ↦ (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
        (hN.scope_embed t)
      comap_base := ?_ }
  have h := Rows.comap_comap (N.nS B C).rows hemb hN.baseEmb
  rw [Scheme.comap_rows_castAdd, hN.comap_base] at h
  exact h.symm

end ALvl.CodedGood

/-! ### The coded levels -/

variable (I g H B) {d : StageType.{u} α (n + 1)}
  (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
  (Q : GrowthRequests I.left d.toScheme) in
/-- **The coded level at the grade `j + 1`** (native construction): the coded initial level, then
the next level on the catalogue of each grade. -/
noncomputable def codedLvLevel : (j : ℕ) → I.ALvl g H (j + 1)
  | 0 => I.codedLvLevel1 g H
  | j + 1 => (codedLvLevel j).next B (I.lvCat g B hd Q (j + 2))

/-- **Every coded level up to the number of points is a coded good level** (native construction),
for a strongly coded attachment. -/
theorem codedLvLevel_codedGood {d : StageType.{u} α (n + 1)}
    {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
    {Q : GrowthRequests I.left d.toScheme} (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hsc : (I.attachment g).rows.IsStronglyCoded)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card ≤ B) :
    ∀ j, j + 1 ≤ m + 2 → (I.codedLvLevel g H B hd Q j).CodedGood B (lvAdm hd Q)
  | 0, _ => codedLvLevel1_codedGood hH hcard hsc _
  | j + 1, hj => (codedLvLevel_codedGood hH hcard hsc hQ hB j (by omega)).next hQ hj hB

end Seed

end VaughtConjecture
