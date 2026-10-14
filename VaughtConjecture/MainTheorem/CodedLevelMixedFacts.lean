/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelMixedFacts
import VaughtConjecture.MainTheorem.CodedLevelControl
import VaughtConjecture.MainTheorem.CodedMirrorDecode

/-!
# The mixed-face readings of the coded levels

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier) and Correspondence, item 1
(the strongly coded legal stage types). All results here are native constructions of this
repository.

The statements of `VaughtConjecture.MainTheorem.ReplicatedLevelMixedFacts` about the levels over the
padded grade-one base, for the coded levels (`Seed.codedLvLevel`) over the coded ladder base
(`Seed.codedLvBase`). The proofs are those of
`VaughtConjecture.MainTheorem.ReplicatedLevelMixedFacts`, with the facts of the padded base replaced
by those of the coded base (`VaughtConjecture.Extension.CodedLadderBase`,
`VaughtConjecture.Extension.CodedLadderLift`) and the coded mirror lifts
(`VaughtConjecture.MainTheorem.CodedMirrorLift`); the statements there that do not mention the
levels or the base are used unchanged.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ}

variable (I : Seed.{u} α m) (g : Fin n ↪ Fin m) (H B : ℕ) {d : StageType.{u} α (n + 1)}
  (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
  (Q : GrowthRequests I.left d.toScheme)

/-- The ladder point `v` in the level at the grade `j + 1`. -/
noncomputable abbrev codedLvLad (j : ℕ)
    (v : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    Fin (I.codedLvLevel g H B hd Q j).S.card :=
  (I.codedLvLevel g H B hd Q j).embed (Fin.natAdd _ (Scheme.ladderEquiv _ _ H v))

variable {I g H B hd Q}

set_option quotPrecheck false in
/-- The index of a ladder point for a member. -/
local notation "idx" => ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
  (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H))

/-- **The cells of the ladder base are read in every level as in the ladder base.** -/
theorem codedLvLevel_rowAt_embed : ∀ (j : ℕ) (t t' : Fin (I.codedLvBase g H).card),
    (I.codedLvLevel g H B hd Q j).S.rowAt ((I.codedLvLevel g H B hd Q j).embed t)
      ((I.codedLvLevel g H B hd Q j).embed t') = (I.codedLvBase g H).rowAt t t'
  | 0, _, _ => rfl
  | j + 1, t, t' => by
    change ((I.codedLvLevel g H B hd Q j).nS B (I.lvCat g B hd Q (j + 2))).rowAt
      (Fin.castAdd _ ((I.codedLvLevel g H B hd Q j).embed t))
      (Fin.castAdd _ ((I.codedLvLevel g H B hd Q j).embed t')) = _
    rw [Scheme.rowAt_appendFullCells_castAdd]
    exact codedLvLevel_rowAt_embed j t t'

theorem codedLvLevel_gradedIndex_lad (j : ℕ)
    (v : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.codedLvLevel g H B hd Q j).S.toCellScheme.gradedIndex (I.codedLvLad g H B hd Q j v) =
      ((univ : Finset (Fin (m + 2))), 1) :=
  (codedLvLevel_gradedIndex_embed j _).trans
      (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _)

/-- **The ladder points read one another with the rows of the ladder.** -/
theorem codedLvLevel_rowAt_lad_lad (j : ℕ)
    (p v : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.codedLvLevel g H B hd Q j).S.rowAt (I.codedLvLad g H B hd Q j p)
      (I.codedLvLad g H B hd Q j v) =
      codedLadderSource (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H) p)
        (idx p.1 v) := by
  refine (codedLvLevel_rowAt_embed j _ _).trans
    ((Scheme.rowAt_codedLadderBase_ladder (hS := (I.attachmentBase g).noFull)
      (I.attachmentBase g).wf p v).trans ?_)
  rw [Scheme.baseIndex_natAdd, Equiv.symm_apply_apply]

/-- **A ladder point reads a cell of the attachment of grade one as the ladder point of its member
and that cell.** -/
theorem codedLvLevel_rowAt_lad_att (j : ℕ)
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H)
    (e : Fin (I.attachment g).card) (he : (I.attachment g).toCellScheme.grade e = 1) :
    (I.codedLvLevel g H B hd Q j).S.rowAt (I.codedLvLad g H B hd Q j p)
      ((I.codedLvLevel g H B hd Q j).attEmb e) =
      (I.codedLvLevel g H B hd Q j).S.rowAt (I.codedLvLad g H B hd Q j p)
        (I.codedLvLad g H B hd Q j (p.1, Sum.inr e)) := by
  rw [codedLvLevel_rowAt_lad_lad]
  refine (codedLvLevel_rowAt_embed j _ _).trans
    ((Scheme.rowAt_codedLadderBase_old (hS := (I.attachmentBase g).noFull)
      (I.attachmentBase g).wf p he).trans ?_)
  congr 1
  exact (ladderIndex_parent (Scheme.ladderCeil_le (Scheme.rankProf_le _ H)) (p.1, Sum.inr e)).symm

/-- **The cells of full scope at the grade one are the ladder points**, in every level. -/
theorem codedLvLevel_hone : ∀ (j : ℕ) (x : Fin (I.codedLvLevel g H B hd Q j).S.card),
    (I.codedLvLevel g H B hd Q j).S.toCellScheme.gradedIndex x = ((univ : Finset (Fin
        (m + 2))), 1) →
    ∃ v, x = I.codedLvLad g H B hd Q j v
  | 0, x, hx => by
    change Fin ((I.attachmentBase g).S.card + _) at x
    induction x using Fin.addCases with
    | left e =>
      exfalso
      have hs := congrArg Prod.fst hx
      change (I.codedLvBase g H).toCellScheme.scope (Fin.castAdd _ e) = univ at hs
      rw [Scheme.appendFullCellsScheme_scope_castAdd] at hs
      exact (I.attachmentBase g).scope_ne_univ e hs
    | right i =>
      refine ⟨(Scheme.ladderEquiv _ _ H).symm i, ?_⟩
      change Fin.natAdd _ i = Fin.natAdd _ (Scheme.ladderEquiv _ _ H _)
      rw [Equiv.apply_symm_apply]
  | j + 1, x, hx => by
    change Fin ((I.codedLvLevel g H B hd Q j).S.card + _) at x
    induction x using Fin.addCases with
    | left x' =>
      obtain ⟨v, rfl⟩ := codedLvLevel_hone j x'
        ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).symm.trans hx)
      exact ⟨v, rfl⟩
    | right i =>
      exfalso
      have := congrArg Prod.snd
        ((Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i).symm.trans hx)
      simp only at this
      omega

/-- **The ladder reading of a section** (see the module docstring). -/
theorem codedLvLevel_ladderReading (hcard : (I.attachmentBase g).S.card ≤ H) :
    ∀ (k : ℕ) (P : Fin (I.attachment g).card → Label.{u})
      (hP1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
        (fun e ↦ P e)), (∀ e, IsSelfVisible 1 (P e)) →
      ∃ Φ : ℕ → Label.{u}, Monotone Φ ∧ Φ 0 = ⊥ ∧
        (∀ v, (I.codedLvLevel g H B hd Q k).σ P (I.codedLvLad g H B hd Q k v) =
          Φ (idx (Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase g).wf hcard hP1) v)) ∧
        ∀ e, P e = Φ (Scheme.rankProf (I.attachmentBase g).S H
          (Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase g).wf hcard hP1) e)
  | 0, P, hP1, hv => by
    refine ⟨posTable P, monotone_posTable, posTable_zero, fun v ↦ ?_, fun e ↦
      (posTable_rankVector hv e).symm⟩
    change I.lvBaseSec g H P (Fin.natAdd _ (Scheme.ladderEquiv _ _ H v)) = _
    rw [lvBaseSec_of_isLawfulBelow hcard hP1]
    refine (Scheme.LadderBaseData.stateExtOf_natAdd' (B' := I.attachmentBase g) P _ _).trans ?_
    rw [Scheme.baseIndex_natAdd, Equiv.symm_apply_apply]
    rfl
  | k + 1, P, hP1, hv => by
    have hC1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
        (fun e ↦ orbitCode (k + 2) P e) := hP1.orbitCode fun e ↦ e.2.2.trans (by omega)
    have hCv (e : Fin (I.attachment g).card) : IsSelfVisible 1 (orbitCode (k + 2) P e) :=
      isSelfVisible_one_orbitCode (by omega) (hv e)
    obtain ⟨Φ', hΦ', hΦ'0, hl, ha⟩ := codedLvLevel_ladderReading hcard k _ hC1 hCv
    have hmem := Scheme.LadderBaseData.ofLawfulBelowOne_orbitCode (B := I.attachmentBase g) hcard
      hP1 hC1
    have hW := isWitness_upperDecoderAt (ι := Fin (I.attachment g).card) (w := P) (B := B)
      (k := k + 2) (K := k + 3) (by omega)
    refine ⟨fun i ↦ upperDecoderAt (k + 2) (k + 3) B P (Φ' i), hW.monotone.comp hΦ',
      by simp only [hΦ'0, upperDecoderAt_bot], fun v ↦ ?_, fun e ↦ ?_⟩
    · change upperDecoderAt (k + 2) (k + 3) B P
        ((I.codedLvLevel g H B hd Q k).Φ B (I.lvCat g B hd Q (k + 2)) (orbitCode (k + 2) P)
          (Fin.castAdd _ (I.codedLvLad g H B hd Q k v))) = _
      rw [ALvl.Φ_castAdd, hl]
      exact congrArg (fun a ↦ upperDecoderAt (k + 2) (k + 3) B P (Φ' (idx a v))) hmem
    · calc P e = upperDecoderAt (k + 2) (k + 3) B P (orbitCode (k + 2) P e) :=
            (upperDecoderAt_orbitCode e).symm
        _ = upperDecoderAt (k + 2) (k + 3) B P (Φ' (Scheme.rankProf (I.attachmentBase g).S H
            (Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase g).wf hcard hC1) e)) := by
            rw [← ha e]
        _ = _ := congrArg (fun a ↦ upperDecoderAt (k + 2) (k + 3) B P
            (Φ' (Scheme.rankProf (I.attachmentBase g).S H a e))) hmem

/-- **Every level reads the cells of the attachment literally** at a state lawful below
`(univ, 1)`. -/
theorem codedLvLevel_σ_attEmb (hcard : (I.attachmentBase g).S.card ≤ H) :
    ∀ (k : ℕ) (P : Fin (I.attachment g).card → Label.{u}),
      (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1) (fun e ↦ P e) →
      ∀ e, (I.codedLvLevel g H B hd Q k).σ P ((I.codedLvLevel g H B hd Q k).attEmb e) = P e
  | 0, P, hP1, e => by
    change I.lvBaseSec g H P (Fin.castAdd _ e) = P e
    rw [lvBaseSec_of_isLawfulBelow hcard hP1]
    exact Scheme.LadderBaseData.stateExtOf_castAdd' (B' := I.attachmentBase g) P _ e
  | k + 1, P, hP1, e => by
    have hC1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
        (fun e ↦ orbitCode (k + 2) P e) := hP1.orbitCode fun e ↦ e.2.2.trans (by omega)
    change upperDecoderAt (k + 2) (k + 3) B P
      ((I.codedLvLevel g H B hd Q k).Φ B (I.lvCat g B hd Q (k + 2)) (orbitCode (k + 2) P)
        (Fin.castAdd _ ((I.codedLvLevel g H B hd Q k).attEmb e))) = P e
    rw [ALvl.Φ_castAdd, codedLvLevel_σ_attEmb hcard k _ hC1 e]
    exact upperDecoderAt_orbitCode e

/-- **A new cell reads an old cell below it through the section at its state.** -/
theorem codedLvLevel_rowAt_new_old (k : ℕ) (i : Fin (I.lvCat g B hd Q (k + 2)).card)
    (z : Fin (I.codedLvLevel g H B hd Q k).S.card)
    (hz : (I.codedLvLevel g H B hd Q k).S.toCellScheme.grade z ≤ k + 2) :
    ((I.codedLvLevel g H B hd Q k).nS B (I.lvCat g B hd Q (k + 2))).rowAt (Fin.natAdd _ i)
        (Fin.castAdd _ z) =
      (I.codedLvLevel g H B hd Q k).σ ((I.lvCat g B hd Q (k + 2)).equivFin.symm i).1 z := by
  have hmem : (Fin.castAdd _ z : Fin ((I.codedLvLevel g H B hd Q k).S.card +
      (I.lvCat g B hd Q (k + 2)).card)) ∈
      ((I.codedLvLevel g H B hd Q k).nS B (I.lvCat g B hd Q (k + 2))).toCellScheme.below
        (((I.codedLvLevel g H B hd Q k).nS B (I.lvCat g B hd Q (k + 2))).toCellScheme.gradedIndex
          (Fin.natAdd _ i)) := by
    rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_natAdd,
      Scheme.appendFullCellsScheme_gradedIndex_castAdd]
    exact ⟨subset_univ _, hz⟩
  rw [Scheme.rowAt_of_mem hmem, Scheme.appendFullCells_row_natAdd]
  exact ALvl.Φ_castAdd _ _ _

/-- **Two new cells read one another through their agreement height.** -/
theorem codedLvLevel_rowAt_new_new (k : ℕ) (i i' : Fin (I.lvCat g B hd Q (k + 2)).card) :
    ((I.codedLvLevel g H B hd Q k).nS B (I.lvCat g B hd Q (k + 2))).rowAt (Fin.natAdd _ i)
        (Fin.natAdd _ i') =
      agreementHeight (grid (k + 2) B) ((I.lvCat g B hd Q (k + 2)).equivFin.symm i).1
        ((I.lvCat g B hd Q (k + 2)).equivFin.symm i').1 := by
  have hmem : (Fin.natAdd _ i' : Fin ((I.codedLvLevel g H B hd Q k).S.card +
      (I.lvCat g B hd Q (k + 2)).card)) ∈
      ((I.codedLvLevel g H B hd Q k).nS B (I.lvCat g B hd Q (k + 2))).toCellScheme.below
        (((I.codedLvLevel g H B hd Q k).nS B (I.lvCat g B hd Q (k + 2))).toCellScheme.gradedIndex
          (Fin.natAdd _ i)) := by
    rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_natAdd,
      Scheme.appendFullCellsScheme_gradedIndex_natAdd]
  rw [Scheme.rowAt_of_mem hmem, Scheme.appendFullCells_row_natAdd]
  exact ALvl.Φ_natAdd _ _ _

/-- **The agreement at a shadow, for the sections of a level**: at a state `P` lawful below
`(univ, 1)` with values self-visible at `1`, for a cell `u` of full scope at a grade `≥ 2` and a
cell `e` of the attachment of grade at most that of `u`, some ladder point `v` is read by `u` as
`e`, and the section at `P` agrees at `v` and at `e` capped at its value at `u`. -/
theorem codedLvLevel_shadowAgree (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card ≤ B) :
    ∀ (k : ℕ), k + 1 ≤ m + 2 → ∀ (P : Fin (I.attachment g).card → Label.{u}),
      (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1) (fun e ↦ P e) →
      (∀ e, IsSelfVisible 1 (P e)) →
      ∀ (u : Fin (I.codedLvLevel g H B hd Q k).S.card) (gu : ℕ),
        (I.codedLvLevel g H B hd Q k).S.toCellScheme.gradedIndex u =
          ((univ : Finset (Fin (m + 2))), gu) → 2 ≤ gu →
      ∀ e, (I.attachment g).toCellScheme.grade e ≤ gu → ∃ v,
        (I.codedLvLevel g H B hd Q k).S.rowAt u (I.codedLvLad g H B hd Q k v) =
          (I.codedLvLevel g H B hd Q k).S.rowAt u ((I.codedLvLevel g H B hd Q k).attEmb e) ∧
        min ((I.codedLvLevel g H B hd Q k).σ P (I.codedLvLad g H B hd Q k v))
            ((I.codedLvLevel g H B hd Q k).σ P u) =
          min (P e) ((I.codedLvLevel g H B hd Q k).σ P u)
  | 0, _, P, _, _, u, gu, hu, h2, e, he => by
    exfalso
    rcases (I.codedLvLevel g H B hd Q 0).inv u with h | h
    · have := congrArg Prod.snd hu
      change (I.codedLvLevel g H B hd Q 0).S.toCellScheme.grade u = gu at this
      omega
    · exact h (congrArg Prod.fst hu)
  | k + 1, hk, P, hP1, hv, u, gu, hu, h2, e, he => by
    classical
    have hC1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
        (fun e ↦ orbitCode (k + 2) P e) := hP1.orbitCode fun e ↦ e.2.2.trans (by omega)
    have hCv (e : Fin (I.attachment g).card) : IsSelfVisible 1 (orbitCode (k + 2) P e) :=
      isSelfVisible_one_orbitCode (by omega) (hv e)
    have hW := isWitness_upperDecoderAt (ι := Fin (I.attachment g).card) (w := P) (B := B)
      (k := k + 2) (K := k + 3) (by omega)
    -- the section of the next level at an old cell
    have hσold (z : Fin (I.codedLvLevel g H B hd Q k).S.card) :
        (I.codedLvLevel g H B hd Q (k + 1)).σ P (Fin.castAdd _ z) =
          upperDecoderAt (k + 2) (k + 3) B P
            ((I.codedLvLevel g H B hd Q k).σ (orbitCode (k + 2) P) z) := by
      change upperDecoderAt (k + 2) (k + 3) B P
        ((I.codedLvLevel g H B hd Q k).Φ B (I.lvCat g B hd Q (k + 2)) (orbitCode (k + 2) P)
          (Fin.castAdd _ z)) = _
      rw [ALvl.Φ_castAdd]
    change Fin ((I.codedLvLevel g H B hd Q k).S.card + (I.lvCat g B hd Q (k + 2)).card) at u
    induction u using Fin.addCases with
    | left u' =>
      have hu' : (I.codedLvLevel g H B hd Q k).S.toCellScheme.gradedIndex u' =
          ((univ : Finset (Fin (m + 2))), gu) :=
        (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).symm.trans hu
      obtain ⟨v, hrv, hmin⟩ := codedLvLevel_shadowAgree hH hcard hQ hB k (by omega) _ hC1 hCv u' gu
        hu' h2 e he
      refine ⟨v, ?_, ?_⟩
      · change ((I.codedLvLevel g H B hd Q k).nS B (I.lvCat g B hd Q (k + 2))).rowAt
          (Fin.castAdd _ u') (Fin.castAdd _ (I.codedLvLad g H B hd Q k v)) =
          ((I.codedLvLevel g H B hd Q k).nS B (I.lvCat g B hd Q (k + 2))).rowAt
          (Fin.castAdd _ u') (Fin.castAdd _ ((I.codedLvLevel g H B hd Q k).attEmb e))
        rw [Scheme.rowAt_appendFullCells_castAdd, Scheme.rowAt_appendFullCells_castAdd]
        exact hrv
      · change min ((I.codedLvLevel g H B hd Q (k + 1)).σ P (Fin.castAdd _
          (I.codedLvLad g H B hd Q k v)))
          ((I.codedLvLevel g H B hd Q (k + 1)).σ P (Fin.castAdd _ u')) = min (P e)
            ((I.codedLvLevel g H B hd Q (k + 1)).σ P (Fin.castAdd _ u'))
        rw [hσold, hσold, ← hW.monotone.map_min, hmin, hW.monotone.map_min,
          upperDecoderAt_orbitCode]
    | right i =>
      have hgu : gu = k + 2 := by
        have := congrArg Prod.snd
          ((Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i).symm.trans hu)
        simp only at this
        omega
      subst hgu
      set R := ((I.lvCat g B hd Q (k + 2)).equivFin.symm i).1 with hRdef
      obtain ⟨hRB, hRl, hRv, -, -⟩ := mem_lvCat.mp ((I.lvCat g B hd Q (k + 2)).equivFin.symm i).2
      have hR1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
          (fun e ↦ R e) := hRl.mono (X := ((univ : Finset (Fin (m + 2))), 1))
            ⟨subset_rfl, by omega⟩
      obtain ⟨Φ, -, -, hlR, haR⟩ := codedLvLevel_ladderReading (hd := hd) (Q := Q)
        (B := B) hcard k R
        hR1 hRv
      set a := Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase g).wf hcard hR1 with ha
      have hshadow :
          (I.codedLvLevel g H B hd Q k).σ R (I.codedLvLad g H B hd Q k (a, Sum.inr e)) = R e := by
        rw [hlR, haR e]
        congr 1
        exact ladderIndex_parent (Scheme.ladderCeil_le (Scheme.rankProf_le _ H)) (a, Sum.inr e)
      have hlg : (I.codedLvLevel g H B hd Q k).S.toCellScheme.grade (I.codedLvLad g H B hd Q k
          (a, Sum.inr e)) ≤ k + 2 := by
        rw [show (I.codedLvLevel g H B hd Q k).S.toCellScheme.grade (I.codedLvLad g H B hd Q k
          (a, Sum.inr e)) = 1 from congrArg Prod.snd (codedLvLevel_gradedIndex_lad k _)]
        omega
      have hag : (I.codedLvLevel g H B hd Q k).S.toCellScheme.grade
          ((I.codedLvLevel g H B hd Q k).attEmb e) ≤ k + 2 := by
        rw [show (I.codedLvLevel g H B hd Q k).S.toCellScheme.grade
          ((I.codedLvLevel g H B hd Q k).attEmb e)
          = (I.attachment g).toCellScheme.grade e from
          (codedLvLevel_gradedIndex_embed k (Fin.castAdd _ e)).trans
            (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e) |> congrArg Prod.snd]
        exact he
      refine ⟨(a, Sum.inr e), ?_, ?_⟩
      · change ((I.codedLvLevel g H B hd Q k).nS B (I.lvCat g B hd Q (k + 2))).rowAt
          (Fin.natAdd _ i) (Fin.castAdd _ (I.codedLvLad g H B hd Q k (a, Sum.inr e))) =
          ((I.codedLvLevel g H B hd Q k).nS B (I.lvCat g B hd Q (k + 2))).rowAt
          (Fin.natAdd _ i) (Fin.castAdd _ ((I.codedLvLevel g H B hd Q k).attEmb e))
        rw [codedLvLevel_rowAt_new_old k i _ hlg, codedLvLevel_rowAt_new_old k i _ hag, ← hRdef,
          hshadow,
          codedLvLevel_σ_attEmb hcard k R hR1 e]
      · -- the capped agreement of the sections at the code and at `R`
        have hgood := codedLvLevel_good (B := B) (hd := hd) hH hcard hQ hB k (by omega)
        set P' := orbitCode (k + 2) P with hP'
        have hcB : 2 * Fintype.card (Fin (I.attachment g).card) ≤ B := by simpa using hB
        have hP'B (e : Fin (I.attachment g).card) : P' e ∈ codeGrid (k + 2) B :=
          orbitMap_mem_codeGrid hcB _
        set h := agreementHeight (grid (k + 2) B) P' R with hh
        have hspec := agreementHeight_spec (bot_mem_grid (k + 2) B) P' R
        have hhv : IsSelfVisible (k + 2) h := isSelfVisible_of_mem_grid hspec.1
        have hhs : IsShort (k + 2) h := isShort_of_mem_grid hspec.1
        have hcap := hgood.capAgree P' R hC1 hR1 hP'B h hhv hhs hspec.2
          (I.codedLvLad g H B hd Q k (a, Sum.inr e))
        have hσu : (I.codedLvLevel g H B hd Q (k + 1)).σ P (Fin.natAdd _ i) =
            upperDecoderAt (k + 2) (k + 3) B P h := by
          change upperDecoderAt (k + 2) (k + 3) B P
            ((I.codedLvLevel g H B hd Q k).Φ B (I.lvCat g B hd Q (k + 2)) (orbitCode (k + 2) P)
              (Fin.natAdd _ i)) = _
          rw [ALvl.Φ_natAdd]
        change min ((I.codedLvLevel g H B hd Q (k + 1)).σ P
            (Fin.castAdd _ (I.codedLvLad g H B hd Q k (a, Sum.inr e))))
          ((I.codedLvLevel g H B hd Q (k + 1)).σ P (Fin.natAdd _ i)) =
          min (P e) ((I.codedLvLevel g H B hd Q (k + 1)).σ P (Fin.natAdd _ i))
        rw [hσold, hσu, ← hW.monotone.map_min, hcap, hshadow, ← hspec.2 e, hW.monotone.map_min,
          upperDecoderAt_orbitCode]

/-- **Twins of a section at every grade** (with `2 · #cells < B`): at a state `P` lawful below
`(univ, k + 1)`, admitted at `k + 1`, with values self-visible at `1`, at every grade
`2 ≤ g ≤ k + 1` some cell of full scope of the level at the grade `k + 1` carries a value of the
section at `P` at least every value of `P`: the cell of the orbit code of `P` at the top grade
(read at the top of the grid, decoded above every value, `Label.le_upperDecoderAt_gridPoint`), and
below, the twin of the orbit code, decoded. -/
theorem codedLvLevel_twinGen (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB' : 2 * (I.attachment g).card < B) :
    ∀ (k : ℕ) (P : Fin (I.attachment g).card → Label.{u}),
      (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k + 1) (fun e ↦ P e) →
      (∀ e, IsSelfVisible 1 (P e)) → I.attachAdmits g hd Q (k + 1) P →
      ∀ gu, 2 ≤ gu → gu ≤ k + 1 → ∃ et : Fin (I.codedLvLevel g H B hd Q k).S.card,
        (I.codedLvLevel g H B hd Q k).S.toCellScheme.gradedIndex et =
          ((univ : Finset (Fin (m + 2))), gu) ∧
        ∀ e, P e ≤ (I.codedLvLevel g H B hd Q k).σ P et
  | 0, _, _, _, _, gu, h2, h1 => absurd (h2.trans h1) (by omega)
  | k + 1, P, hP, hv, hA, gu, h2, hgk => by
    classical
    have hcB : 2 * Fintype.card (Fin (I.attachment g).card) ≤ B := by
      simp only [Fintype.card_fin]; omega
    have hW := isWitness_upperDecoderAt (ι := Fin (I.attachment g).card) (w := P) (B := B)
      (k := k + 2) (K := k + 3) (by omega)
    have hC2 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k + 2)
        (fun e ↦ orbitCode (k + 2) P e) := hP.orbitCode fun e ↦ e.2.2
    have hCv (e : Fin (I.attachment g).card) : IsSelfVisible 1 (orbitCode (k + 2) P e) :=
      isSelfVisible_one_orbitCode (by omega) (hv e)
    have hCA : I.attachAdmits g hd Q (k + 2) (orbitCode (k + 2) P) := attachAdmits_orbitCode hQ hA
    have hσold (z : Fin (I.codedLvLevel g H B hd Q k).S.card) :
        (I.codedLvLevel g H B hd Q (k + 1)).σ P (Fin.castAdd _ z) =
          upperDecoderAt (k + 2) (k + 3) B P
            ((I.codedLvLevel g H B hd Q k).σ (orbitCode (k + 2) P) z) := by
      change upperDecoderAt (k + 2) (k + 3) B P
        ((I.codedLvLevel g H B hd Q k).Φ B (I.lvCat g B hd Q (k + 2)) (orbitCode (k + 2) P)
          (Fin.castAdd _ z)) = _
      rw [ALvl.Φ_castAdd]
    rcases Nat.lt_or_ge gu (k + 2) with hlt | hge
    · -- below the top grade: the twin of the orbit code, decoded
      obtain ⟨et, het, hle⟩ := codedLvLevel_twinGen hcard hQ hB' k (orbitCode (k + 2) P)
        (hC2.mono (X := ((univ : Finset (Fin (m + 2))), k + 1)) ⟨subset_rfl, by omega⟩) hCv
        (attachAdmits_pred hCA) gu h2 (by omega)
      refine ⟨Fin.castAdd _ et, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
        het, fun e ↦ ?_⟩
      rw [hσold, ← upperDecoderAt_orbitCode (k := k + 2) (K := k + 3) (B := B) (w := P) e]
      exact hW.monotone (hle e)
    · -- at the top grade: the cell of the orbit code
      obtain rfl : gu = k + 2 := by omega
      have hmem : orbitCode (k + 2) P ∈ I.lvCat g B hd Q (k + 2) :=
        mem_lvCat.mpr ⟨fun e ↦ orbitMap_mem_codeGrid hcB _, hC2, hCv, orbitCode_orbitCode, hCA⟩
      set iP := (I.lvCat g B hd Q (k + 2)).equivFin ⟨_, hmem⟩ with hiP
      refine ⟨Fin.natAdd _ iP, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _,
        fun e ↦ ?_⟩
      change P e ≤ upperDecoderAt (k + 2) (k + 3) B P
        ((I.codedLvLevel g H B hd Q k).Φ B (I.lvCat g B hd Q (k + 2)) (orbitCode (k + 2) P)
          (Fin.natAdd _ iP))
      rw [ALvl.Φ_natAdd, hiP, Equiv.symm_apply_apply]
      dsimp only
      rw [agreementHeight_self (gridPoint_mem_grid le_rfl) (fun _ hx ↦ le_gridPoint_of_mem_grid hx)]
      exact le_upperDecoderAt_gridPoint (by simpa using hB') P e

end Seed

end VaughtConjecture
