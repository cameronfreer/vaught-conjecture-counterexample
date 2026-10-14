/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelMixedLift
import VaughtConjecture.MainTheorem.CodedLevelMixedFacts
import VaughtConjecture.MainTheorem.CodedMirrorLift
import VaughtConjecture.MainTheorem.CodedLevelFaces

/-!
# The lifts from the mixed faces of the replicated coded levels

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier) and Correspondence, item 1
(the strongly coded legal stage types). All results here are native constructions of this
repository.

The statements of `VaughtConjecture.MainTheorem.ReplicatedLevelMixedLift` about the levels over the
padded grade-one base, for the coded levels (`Seed.codedLvLevel`) over the coded ladder base
(`Seed.codedLvBase`). The proofs are those of
`VaughtConjecture.MainTheorem.ReplicatedLevelMixedLift`, with the facts of the padded base replaced
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

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}
  {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

set_option quotPrecheck false in
/-- The index of a ladder point for a member. -/
local notation "idx" => ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
  (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H))

/-- The cells of full scope of a level have grade at most the grade of the level. -/
theorem codedLvLevel_grade_le_of_scope (J : ℕ) (x : Fin (I.codedLvLevel g H B hd Q J).S.card)
    (hx : (I.codedLvLevel g H B hd Q J).S.toCellScheme.scope x = univ) :
    (I.codedLvLevel g H B hd Q J).S.toCellScheme.grade x ≤ J + 1 :=
  ((I.codedLvLevel g H B hd Q J).inv x).resolve_right fun h ↦ h hx

/-- **A cell of full scope reads the ladder through one member** (in the level at the grade
`J + 1`). -/
theorem codedLvLevel_hread (hcard : (I.attachmentBase g).S.card ≤ H) :
    ∀ (J : ℕ) (f : Fin (I.codedLvLevel g H B hd Q J).S.card) (K : ℕ),
      (I.codedLvLevel g H B hd Q J).S.toCellScheme.gradedIndex f =
        ((univ : Finset (Fin (m + 2))), K) → 2 ≤ K →
      ∃ (b : Scheme.RankMember (I.attachmentBase g).S H) (Φ : ℕ → Label.{u}), Monotone Φ ∧
        Φ 0 = ⊥ ∧ (∀ v, (I.codedLvLevel g H B hd Q J).S.rowAt f (I.codedLvLad g H B hd Q J v) =
          Φ (idx b v)) ∧
        ∀ e, (I.attachment g).toCellScheme.grade e ≤ K →
          (I.codedLvLevel g H B hd Q J).S.rowAt f ((I.codedLvLevel g H B hd Q J).attEmb e) =
            Φ (Scheme.rankProf (I.attachmentBase g).S H b e)
  | 0, f, K, hf, hK => by
    exfalso
    have := codedLvLevel_grade_le_of_scope (hd := hd) (Q := Q) (B := B) 0 f (congrArg Prod.fst hf)
    rw [show (I.codedLvLevel g H B hd Q 0).S.toCellScheme.grade f = K from congrArg Prod.snd hf]
        at this
    omega
  | J + 1, f, K, hf, hK => by
    change Fin ((I.codedLvLevel g H B hd Q J).S.card + (I.lvCat g B hd Q (J + 2)).card) at f
    induction f using Fin.addCases with
    | left f' =>
      obtain ⟨b, Φ, hΦ, hΦ0, hl, ha⟩ := codedLvLevel_hread hcard J f' K
        ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).symm.trans hf) hK
      refine ⟨b, Φ, hΦ, hΦ0, fun v ↦ ?_, fun e he ↦ ?_⟩
      · change ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.castAdd _ f') (Fin.castAdd _ (I.codedLvLad g H B hd Q J v)) = _
        rw [Scheme.rowAt_appendFullCells_castAdd]
        exact hl v
      · change ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.castAdd _ f') (Fin.castAdd _ ((I.codedLvLevel g H B hd Q J).attEmb e)) = _
        rw [Scheme.rowAt_appendFullCells_castAdd]
        exact ha e he
    | right i =>
      have hKJ : K = J + 2 := by
        have := congrArg Prod.snd
          ((Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i).symm.trans hf)
        simp only at this
        omega
      subst hKJ
      set R := ((I.lvCat g B hd Q (J + 2)).equivFin.symm i).1 with hRdef
      obtain ⟨-, hRl, hRv, -, -⟩ := mem_lvCat.mp ((I.lvCat g B hd Q (J + 2)).equivFin.symm i).2
      have hR1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
          (fun e ↦ R e) := hRl.mono (X := ((univ : Finset (Fin (m + 2))), 1))
            ⟨subset_rfl, by omega⟩
      obtain ⟨Φ, hΦ, hΦ0, hl, ha⟩ := codedLvLevel_ladderReading (hd := hd) (Q := Q)
        (B := B) hcard J R
        hR1 hRv
      refine ⟨Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase g).wf hcard hR1, Φ, hΦ, hΦ0,
        fun v ↦ ?_, fun e he ↦ ?_⟩
      · change ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.natAdd _ i) (Fin.castAdd _ (I.codedLvLad g H B hd Q J v)) = _
        rw [codedLvLevel_rowAt_new_old J i _ (by
          rw [show (I.codedLvLevel g H B hd Q J).S.toCellScheme.grade
            (I.codedLvLad g H B hd Q J v) = 1
            from congrArg Prod.snd (codedLvLevel_gradedIndex_lad J v)]; omega)]
        exact hl v
      · change ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.natAdd _ i) (Fin.castAdd _ ((I.codedLvLevel g H B hd Q J).attEmb e)) = _
        rw [codedLvLevel_rowAt_new_old J i _ (by
          rw [show (I.codedLvLevel g H B hd Q J).S.toCellScheme.grade
              ((I.codedLvLevel g H B hd Q J).attEmb e) = (I.attachment g).toCellScheme.grade e
            from (codedLvLevel_gradedIndex_embed J (Fin.castAdd _ e)).trans
              (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e) |> congrArg Prod.snd]
          exact he), ← hRdef, codedLvLevel_σ_attEmb hcard J R hR1 e]
        exact ha e

/-- **A cell of full scope at every grade from `2` to the grade of the level**: the cells of the
bottom state. -/
theorem codedLvLevel_hexist : ∀ (J k : ℕ), 2 ≤ k → k ≤ J + 1 →
    ∃ f : Fin (I.codedLvLevel g H B hd Q J).S.card,
      (I.codedLvLevel g H B hd Q J).S.toCellScheme.gradedIndex f = ((univ : Finset (Fin
          (m + 2))), k)
  | 0, k, h2, hk => absurd (h2.trans hk) (by omega)
  | J + 1, k, h2, hk => by
    classical
    rcases Nat.lt_or_ge k (J + 2) with hlt | hge
    · obtain ⟨f, hf⟩ := codedLvLevel_hexist J k h2 (by omega)
      exact ⟨Fin.castAdd _ f, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans hf⟩
    · obtain rfl : k = J + 2 := by omega
      have hbot : (fun _ ↦ ⊥ : Fin (I.attachment g).card → Label.{u}) ∈
          I.lvCat g B hd Q (J + 2) :=
        mem_lvCat.mpr ⟨fun _ ↦ mem_insert_self _ _, Rows.isLawfulBelow_const_bot _,
          fun _ ↦ isSelfVisible_bot 1, funext fun _ ↦ orbitCode_eq_bot_iff.mpr rfl,
          I.attachAdmits_bot g hd Q _⟩
      exact ⟨Fin.natAdd _ ((I.lvCat g B hd Q (J + 2)).equivFin ⟨_, hbot⟩),
        Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _⟩

/-- The grade of a cell of the attachment in a level. -/
theorem codedLvLevel_grade_attEmb (J : ℕ) (e : Fin (I.attachment g).card) :
    (I.codedLvLevel g H B hd Q J).S.toCellScheme.grade ((I.codedLvLevel g H B hd Q J).attEmb e) =
      (I.attachment g).toCellScheme.grade e :=
  (codedLvLevel_gradedIndex_embed J (Fin.castAdd _ e)).trans
    (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e) |> congrArg Prod.snd

theorem codedLvLevel_grade_lad (J : ℕ)
    (v : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.codedLvLevel g H B hd Q J).S.toCellScheme.grade (I.codedLvLad g H B hd Q J v) = 1 :=
  congrArg Prod.snd (codedLvLevel_gradedIndex_lad J v)

/-- **The agreement at a shadow** (in the level at the grade `J + 1`). -/
theorem codedLvLevel_hagree (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card ≤ B) :
    ∀ (J : ℕ), J + 1 ≤ m + 2 → ∀ (f u : Fin (I.codedLvLevel g H B hd Q J).S.card) (K k : ℕ),
      (I.codedLvLevel g H B hd Q J).S.toCellScheme.gradedIndex f =
        ((univ : Finset (Fin (m + 2))), K) →
      (I.codedLvLevel g H B hd Q J).S.toCellScheme.gradedIndex u =
        ((univ : Finset (Fin (m + 2))), k) → 2 ≤ k → k ≤ K →
      ∀ e, (I.attachment g).toCellScheme.grade e = k → ∃ v,
        (I.codedLvLevel g H B hd Q J).S.rowAt u (I.codedLvLad g H B hd Q J v) =
          (I.codedLvLevel g H B hd Q J).S.rowAt u ((I.codedLvLevel g H B hd Q J).attEmb e) ∧
        min ((I.codedLvLevel g H B hd Q J).S.rowAt f (I.codedLvLad g H B hd Q J v))
            ((I.codedLvLevel g H B hd Q J).S.rowAt f u) =
          min ((I.codedLvLevel g H B hd Q J).S.rowAt f ((I.codedLvLevel g H B hd Q J).attEmb e))
            ((I.codedLvLevel g H B hd Q J).S.rowAt f u)
  | 0, _, f, u, K, k, hf, hu, h2, hkK, e, he => by
    exfalso
    have := codedLvLevel_grade_le_of_scope (hd := hd) (Q := Q) (B := B) 0 f (congrArg Prod.fst hf)
    rw [show (I.codedLvLevel g H B hd Q 0).S.toCellScheme.grade f = K from congrArg Prod.snd hf]
        at this
    omega
  | J + 1, hJ, f, u, K, k, hf, hu, h2, hkK, e, he => by
    classical
    change Fin ((I.codedLvLevel g H B hd Q J).S.card + (I.lvCat g B hd Q (J + 2)).card) at f u
    induction f using Fin.addCases with
    | left f' =>
      have hf' : (I.codedLvLevel g H B hd Q J).S.toCellScheme.gradedIndex f' =
          ((univ : Finset (Fin (m + 2))), K) :=
        (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).symm.trans hf
      have hKJ := codedLvLevel_grade_le_of_scope (hd := hd) (Q := Q) (B := B) J f'
        (congrArg Prod.fst hf')
      rw [show (I.codedLvLevel g H B hd Q J).S.toCellScheme.grade f' = K
        from congrArg Prod.snd hf'] at hKJ
      induction u using Fin.addCases with
      | left u' =>
        obtain ⟨v, hrv, hmin⟩ := codedLvLevel_hagree hH hcard hQ hB J (by omega) f' u' K k hf'
          ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).symm.trans hu) h2 hkK e he
        refine ⟨v, ?_, ?_⟩
        · change ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.castAdd _ u') (Fin.castAdd _ (I.codedLvLad g H B hd Q J v)) =
            ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.castAdd _ u') (Fin.castAdd _ ((I.codedLvLevel g H B hd Q J).attEmb e))
          rw [Scheme.rowAt_appendFullCells_castAdd, Scheme.rowAt_appendFullCells_castAdd]
          exact hrv
        · change min (((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.castAdd _ f') (Fin.castAdd _ (I.codedLvLad g H B hd Q J v)))
            (((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.castAdd _ f') (Fin.castAdd _ u')) =
            min (((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.castAdd _ f') (Fin.castAdd _ ((I.codedLvLevel g H B hd Q J).attEmb e)))
            (((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.castAdd _ f') (Fin.castAdd _ u'))
          rw [Scheme.rowAt_appendFullCells_castAdd, Scheme.rowAt_appendFullCells_castAdd,
            Scheme.rowAt_appendFullCells_castAdd]
          exact hmin
      | right i' =>
        exfalso
        have := congrArg Prod.snd
          ((Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i').symm.trans hu)
        simp only at this
        omega
    | right i =>
      have hKJ : K = J + 2 := by
        have := congrArg Prod.snd
          ((Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i).symm.trans hf)
        simp only at this
        omega
      subst hKJ
      set Rf := ((I.lvCat g B hd Q (J + 2)).equivFin.symm i).1 with hRf
      obtain ⟨hRfB, hRfl, hRfv, -, -⟩ :=
        mem_lvCat.mp ((I.lvCat g B hd Q (J + 2)).equivFin.symm i).2
      have hRf1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
          (fun e ↦ Rf e) := hRfl.mono (X := ((univ : Finset (Fin (m + 2))), 1))
            ⟨subset_rfl, by omega⟩
      have hσe : (I.codedLvLevel g H B hd Q J).σ Rf
        ((I.codedLvLevel g H B hd Q J).attEmb e) = Rf e :=
        codedLvLevel_σ_attEmb hcard J Rf hRf1 e
      have hge : (I.codedLvLevel g H B hd Q J).S.toCellScheme.grade
          ((I.codedLvLevel g H B hd Q J).attEmb e) ≤ J + 2 := by
        rw [codedLvLevel_grade_attEmb]; omega
      have hgl (v : Scheme.LadderPt (I.attachmentBase g).S
          (Scheme.RankMember (I.attachmentBase g).S H) H) :
          (I.codedLvLevel g H B hd Q J).S.toCellScheme.grade
              (I.codedLvLad g H B hd Q J v) ≤ J + 2 := by
        rw [codedLvLevel_grade_lad]; omega
      induction u using Fin.addCases with
      | left u' =>
        have hu' : (I.codedLvLevel g H B hd Q J).S.toCellScheme.gradedIndex u' =
            ((univ : Finset (Fin (m + 2))), k) :=
          (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).symm.trans hu
        have hgu : (I.codedLvLevel g H B hd Q J).S.toCellScheme.grade u' ≤ J + 2 := by
          rw [show (I.codedLvLevel g H B hd Q J).S.toCellScheme.grade u' = k
            from congrArg Prod.snd hu']; omega
        obtain ⟨v, hrv, hmin⟩ := codedLvLevel_shadowAgree hH hcard hQ hB J
          (by omega) Rf hRf1 hRfv u'
          k hu' h2 e he.le
        refine ⟨v, ?_, ?_⟩
        · change ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.castAdd _ u') (Fin.castAdd _ (I.codedLvLad g H B hd Q J v)) =
            ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.castAdd _ u') (Fin.castAdd _ ((I.codedLvLevel g H B hd Q J).attEmb e))
          rw [Scheme.rowAt_appendFullCells_castAdd, Scheme.rowAt_appendFullCells_castAdd]
          exact hrv
        · change min (((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i) (Fin.castAdd _ (I.codedLvLad g H B hd Q J v)))
            (((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i) (Fin.castAdd _ u')) =
            min (((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i) (Fin.castAdd _ ((I.codedLvLevel g H B hd Q J).attEmb e)))
            (((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i) (Fin.castAdd _ u'))
          rw [codedLvLevel_rowAt_new_old J i _ (hgl v), codedLvLevel_rowAt_new_old J i _ hgu,
            codedLvLevel_rowAt_new_old J i _ hge, ← hRf, hσe]
          exact hmin
      | right i' =>
        set Ru := ((I.lvCat g B hd Q (J + 2)).equivFin.symm i').1 with hRu
        obtain ⟨-, hRul, hRuv, -, -⟩ :=
          mem_lvCat.mp ((I.lvCat g B hd Q (J + 2)).equivFin.symm i').2
        have hRu1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
            (fun e ↦ Ru e) := hRul.mono (X := ((univ : Finset (Fin (m + 2))), 1))
              ⟨subset_rfl, by omega⟩
        obtain ⟨Φ, -, -, hlR, haR⟩ := codedLvLevel_ladderReading (hd := hd) (Q := Q)
          (B := B) hcard J
          Ru hRu1 hRuv
        set a := Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase g).wf hcard hRu1 with ha
        have hshadow : (I.codedLvLevel g H B hd Q J).σ Ru (I.codedLvLad g H B hd Q J (a,
            Sum.inr e)) =
            Ru e := by
          rw [hlR, haR e]
          congr 1
          exact ladderIndex_parent (Scheme.ladderCeil_le (Scheme.rankProf_le _ H)) (a, Sum.inr e)
        refine ⟨(a, Sum.inr e), ?_, ?_⟩
        · change ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i') (Fin.castAdd _ (I.codedLvLad g H B hd Q J (a, Sum.inr e))) =
            ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i') (Fin.castAdd _ ((I.codedLvLevel g H B hd Q J).attEmb e))
          rw [codedLvLevel_rowAt_new_old J i' _ (hgl _),
            codedLvLevel_rowAt_new_old J i' _ hge, ← hRu,
            hshadow, codedLvLevel_σ_attEmb hcard J Ru hRu1 e]
        · have hgood := codedLvLevel_good (B := B) (hd := hd) hH hcard hQ hB J (by omega)
          set h := agreementHeight (grid (J + 2) B) Rf Ru with hh
          have hspec := agreementHeight_spec (bot_mem_grid (J + 2) B) Rf Ru
          have hcap := hgood.capAgree Rf Ru hRf1 hRu1 hRfB h (isSelfVisible_of_mem_grid hspec.1)
            (isShort_of_mem_grid hspec.1) hspec.2 (I.codedLvLad g H B hd Q J (a, Sum.inr e))
          change min (((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i) (Fin.castAdd _ (I.codedLvLad g H B hd Q J (a, Sum.inr e))))
            (((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i) (Fin.natAdd _ i')) =
            min (((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i) (Fin.castAdd _ ((I.codedLvLevel g H B hd Q J).attEmb e)))
            (((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i) (Fin.natAdd _ i'))
          rw [codedLvLevel_rowAt_new_old J i _ (hgl _), codedLvLevel_rowAt_new_new J i i',
            codedLvLevel_rowAt_new_old J i _ hge, ← hRf, ← hRu, ← hh, hσe, hcap, hshadow, hspec.2 e]

/-- **The twins** (in the level at the grade `J + 1`, with `2 · #cells < B`). -/
theorem codedLvLevel_htwin (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB' : 2 * (I.attachment g).card < B) :
    ∀ (J : ℕ) (f : Fin (I.codedLvLevel g H B hd Q J).S.card) (K k : ℕ),
      (I.codedLvLevel g H B hd Q J).S.toCellScheme.gradedIndex f =
        ((univ : Finset (Fin (m + 2))), K) → 2 ≤ k → k ≤ K →
      ∀ e, (I.attachment g).toCellScheme.grade e = k →
      ∃ et, (I.codedLvLevel g H B hd Q J).S.toCellScheme.gradedIndex et =
          ((univ : Finset (Fin (m + 2))), k) ∧
        (I.codedLvLevel g H B hd Q J).S.rowAt f ((I.codedLvLevel g H B hd Q J).attEmb e) ≤
          (I.codedLvLevel g H B hd Q J).S.rowAt f et
  | 0, f, K, k, hf, h2, hkK, e, he => by
    exfalso
    have := codedLvLevel_grade_le_of_scope (hd := hd) (Q := Q) (B := B) 0 f (congrArg Prod.fst hf)
    rw [show (I.codedLvLevel g H B hd Q 0).S.toCellScheme.grade f = K from congrArg Prod.snd hf]
        at this
    omega
  | J + 1, f, K, k, hf, h2, hkK, e, he => by
    classical
    change Fin ((I.codedLvLevel g H B hd Q J).S.card + (I.lvCat g B hd Q (J + 2)).card) at f
    induction f using Fin.addCases with
    | left f' =>
      obtain ⟨et, het, hle⟩ := codedLvLevel_htwin hcard hQ hB' J f' K k
        ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).symm.trans hf) h2 hkK e he
      refine ⟨Fin.castAdd _ et,
        (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans het, ?_⟩
      change ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
        (Fin.castAdd _ f') (Fin.castAdd _ ((I.codedLvLevel g H B hd Q J).attEmb e)) ≤
        ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
        (Fin.castAdd _ f') (Fin.castAdd _ et)
      rw [Scheme.rowAt_appendFullCells_castAdd, Scheme.rowAt_appendFullCells_castAdd]
      exact hle
    | right i =>
      have hKJ : K = J + 2 := by
        have := congrArg Prod.snd
          ((Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i).symm.trans hf)
        simp only at this
        omega
      subst hKJ
      set R := ((I.lvCat g B hd Q (J + 2)).equivFin.symm i).1 with hRdef
      obtain ⟨hRB, hRl, hRv, -, hRA⟩ :=
        mem_lvCat.mp ((I.lvCat g B hd Q (J + 2)).equivFin.symm i).2
      have hR1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
          (fun e ↦ R e) := hRl.mono (X := ((univ : Finset (Fin (m + 2))), 1))
            ⟨subset_rfl, by omega⟩
      have hge : (I.codedLvLevel g H B hd Q J).S.toCellScheme.grade
          ((I.codedLvLevel g H B hd Q J).attEmb e) ≤ J + 2 := by
        rw [codedLvLevel_grade_attEmb]; omega
      have hre : ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.natAdd _ i) (Fin.castAdd _ ((I.codedLvLevel g H B hd Q J).attEmb e)) = R e := by
        rw [codedLvLevel_rowAt_new_old J i _ hge, ← hRdef, codedLvLevel_σ_attEmb hcard J R hR1 e]
      rcases Nat.lt_or_ge k (J + 2) with hlt | hge2
      · obtain ⟨et, het, hle⟩ := codedLvLevel_twinGen (hd := hd) (B := B) hcard hQ hB' J R
          (hRl.mono (X := ((univ : Finset (Fin (m + 2))), J + 1)) ⟨subset_rfl, by omega⟩) hRv
          (attachAdmits_pred hRA) k h2 (by omega)
        have hget : (I.codedLvLevel g H B hd Q J).S.toCellScheme.grade et ≤ J + 2 := by
          rw [show (I.codedLvLevel g H B hd Q J).S.toCellScheme.grade et = k
            from congrArg Prod.snd het]; omega
        refine ⟨Fin.castAdd _ et,
          (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans het, ?_⟩
        change ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.natAdd _ i) (Fin.castAdd _ ((I.codedLvLevel g H B hd Q J).attEmb e)) ≤
          ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.natAdd _ i) (Fin.castAdd _ et)
        rw [hre, codedLvLevel_rowAt_new_old J i _ hget]
        exact hle e
      · obtain rfl : k = J + 2 := by omega
        refine ⟨Fin.natAdd _ i, hf, ?_⟩
        change ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.natAdd _ i) (Fin.castAdd _ ((I.codedLvLevel g H B hd Q J).attEmb e)) ≤
          ((I.codedLvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.natAdd _ i) (Fin.natAdd _ i)
        rw [hre, codedLvLevel_rowAt_new_new J i i, ← hRdef,
          agreementHeight_self (gridPoint_mem_grid le_rfl) (fun _ hx ↦ le_gridPoint_of_mem_grid hx)]
        exact le_gridPoint_of_mem_codeGrid (hRB e)

/-- **The lift from a mixed face into the full face of a replicated level** (with
`2 · #cells < B`): for a good level at the grade `J + 1`, a mixed face `U` and
`1 ≤ j ≤ min (|U|) (J + 1)`, the replicated level lifts capped from `(U, j)` into `(univ, j)`. -/
theorem codedLvRep_cappedLift_mixed_univ (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB' : 2 * (I.attachment g).card < B) {J : ℕ} (hJ : J + 1 ≤ m + 2)
    (hN : (I.codedLvLevel g H B hd Q J).Good B (lvAdm hd Q)) {U : Finset (Fin (m + 2))}
    (hU : U ∈ I.mixedFaces g) {j : ℕ} (hj1 : 1 ≤ j) (hjU : j ≤ #U) (hjJ : j ≤ J + 1) :
    hN.rep.rows.CappedLift (X := (U, j)) (Y := ((univ : Finset (Fin (m + 2))), j))
      ⟨subset_univ _, le_rfl⟩ :=
  cappedLift_mirror_mixed_univ_coded (hmix := hN.not_subset_scope) hH hN.consistent
    (fun x ↦ hN.wf.isWellFormed.grade_pos x) hN.gradedIndex_attEmb
    (fun x hx ↦ (hN.mem_range x hx).elim fun e he ↦ ⟨e, he.symm⟩)
    (codedLvLevel_gradedIndex_lad J) (codedLvLevel_rowAt_lad_lad J) (codedLvLevel_rowAt_lad_att J)
    (codedLvLevel_hone J) (codedLvLevel_hread hcard J) (codedLvLevel_hagree hH hcard hQ hB'.le J hJ)
    (codedLvLevel_htwin hcard hQ hB' J) hU (fun k h2 hk ↦ codedLvLevel_hexist J k h2
        (hk.trans hjJ)) hj1 hjU

/-- **The lift between mixed faces of a replicated level** (with `2 · #cells < B`): for a good
level at the grade `J + 1`, mixed faces `U ⊆ V` and `1 ≤ j ≤ min (|U|) (J + 1)`, the replicated
level lifts capped from `(U, j)` into `(V, j)`. -/
theorem codedLvRep_cappedLift_mixed_mixed (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB' : 2 * (I.attachment g).card < B) {J : ℕ} (hJ : J + 1 ≤ m + 2)
    (hN : (I.codedLvLevel g H B hd Q J).Good B (lvAdm hd Q)) {U V : Finset (Fin (m + 2))}
    (hU : U ∈ I.mixedFaces g) (hV : V ∈ I.mixedFaces g) (hUV : U ⊆ V) {j : ℕ} (hj1 : 1 ≤ j)
    (hjU : j ≤ #U) (hjJ : j ≤ J + 1) :
    hN.rep.rows.CappedLift (X := (U, j)) (Y := (V, j)) ⟨hUV, le_rfl⟩ :=
  cappedLift_mirror_mixed_mixed_coded (hmix := hN.not_subset_scope) hH hN.consistent
    (fun x ↦ hN.wf.isWellFormed.grade_pos x) hN.gradedIndex_attEmb
    (fun x hx ↦ (hN.mem_range x hx).elim fun e he ↦ ⟨e, he.symm⟩)
    (codedLvLevel_gradedIndex_lad J) (codedLvLevel_rowAt_lad_lad J) (codedLvLevel_rowAt_lad_att J)
    (codedLvLevel_hone J) (codedLvLevel_hread hcard J) (codedLvLevel_hagree hH hcard hQ hB'.le J hJ)
    (codedLvLevel_htwin hcard hQ hB' J) hU hV hUV (fun k h2 hk ↦ codedLvLevel_hexist J k h2
        (hk.trans hjJ))
    hj1 hjU

end Seed

end VaughtConjecture
