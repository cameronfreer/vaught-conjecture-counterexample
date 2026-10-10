/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelMixedFacts

/-!
# The lifts from the mixed faces of a replicated level

Roadmap, Layer 3 ((R3) and (R4), the lifts into the mixed faces of the levels re-rendered per
grade).

The scheme of the level at the grade `J + 1` (`Seed.lvLevel`) meets the hypotheses of the lift from
a mixed face of a mirrored scheme (`Seed.cappedLift_mirror_mixed_face`), with the cells of the
attachment `attEmb` and the ladder points `Seed.lvLad`:

* `Seed.lvLevel_hread`: a cell of full scope at a grade `K ≥ 2` (the cell of a state `R`) reads the
  ladder through the rank member of `R` (`Seed.lvLevel_ladderReading`), and the cells of the
  attachment of grade at most `K` literally;
* `Seed.lvLevel_hagree`: the agreement at a shadow, for a lower cell through the sections
  (`Seed.lvLevel_shadowAgree`), for a cell of the same grade through the agreement height and the
  capped agreement of the sections (`Seed.ALvl.Good.capAgree`);
* `Seed.lvLevel_htwin` (with `2 · #cells < B`): the twin at the grade of the cell itself (the cell,
  read at the top of the grid) and below (`Seed.lvLevel_twinGen`);
* `Seed.lvLevel_hexist`: a cell of full scope at every grade `2 ≤ k ≤ J + 1` (the bottom state).

**The lifts** (`Seed.lvRep_cappedLift_mixed_univ`, `Seed.lvRep_cappedLift_mixed_mixed`): for a
good level at the grade `J + 1`, a mixed face `U` and `1 ≤ j ≤ min (|U|) (J + 1)`, the replicated
level lifts capped from `(U, j)` into `(univ, j)`, and into `(V, j)` for every mixed face `V ⊇ U`.
The block bound is asked strictly, `2 · #cells < B` (for the twins); the premises are those of the
requests calibrated on the class (`hQ`) and the height (`hH`, `hcard`).  Neither the labels pair
(`hpair`) nor the relative lift (`hrel`) is used here.

## References

Bountifulness is [Kni26, Definition 2.5.14]; the growth construction is that of [Kni26, §4].
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
theorem lvLevel_grade_le_of_scope (J : ℕ) (x : Fin (I.lvLevel g H B hd Q J).S.card)
    (hx : (I.lvLevel g H B hd Q J).S.toCellScheme.scope x = univ) :
    (I.lvLevel g H B hd Q J).S.toCellScheme.grade x ≤ J + 1 :=
  ((I.lvLevel g H B hd Q J).inv x).resolve_right fun h ↦ h hx

/-- **A cell of full scope reads the ladder through one member** (in the level at the grade
`J + 1`). -/
theorem lvLevel_hread (hcard : (I.attachmentBase g).S.card ≤ H) :
    ∀ (J : ℕ) (f : Fin (I.lvLevel g H B hd Q J).S.card) (K : ℕ),
      (I.lvLevel g H B hd Q J).S.toCellScheme.gradedIndex f =
        ((univ : Finset (Fin (m + 2))), K) → 2 ≤ K →
      ∃ (b : Scheme.RankMember (I.attachmentBase g).S H) (Φ : ℕ → Label.{u}), Monotone Φ ∧
        Φ 0 = ⊥ ∧ (∀ v, (I.lvLevel g H B hd Q J).S.rowAt f (I.lvLad g H B hd Q J v) =
          Φ (idx b v)) ∧
        ∀ e, (I.attachment g).toCellScheme.grade e ≤ K →
          (I.lvLevel g H B hd Q J).S.rowAt f ((I.lvLevel g H B hd Q J).attEmb e) =
            Φ (Scheme.rankProf (I.attachmentBase g).S H b e)
  | 0, f, K, hf, hK => by
    exfalso
    have := lvLevel_grade_le_of_scope (hd := hd) (Q := Q) (B := B) 0 f (congrArg Prod.fst hf)
    rw [show (I.lvLevel g H B hd Q 0).S.toCellScheme.grade f = K from congrArg Prod.snd hf] at this
    omega
  | J + 1, f, K, hf, hK => by
    change Fin ((I.lvLevel g H B hd Q J).S.card + (I.lvCat g B hd Q (J + 2)).card) at f
    induction f using Fin.addCases with
    | left f' =>
      obtain ⟨b, Φ, hΦ, hΦ0, hl, ha⟩ := lvLevel_hread hcard J f' K
        ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).symm.trans hf) hK
      refine ⟨b, Φ, hΦ, hΦ0, fun v ↦ ?_, fun e he ↦ ?_⟩
      · change ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.castAdd _ f') (Fin.castAdd _ (I.lvLad g H B hd Q J v)) = _
        rw [Scheme.rowAt_appendFullCells_castAdd]
        exact hl v
      · change ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.castAdd _ f') (Fin.castAdd _ ((I.lvLevel g H B hd Q J).attEmb e)) = _
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
      obtain ⟨Φ, hΦ, hΦ0, hl, ha⟩ := lvLevel_ladderReading (hd := hd) (Q := Q) (B := B) hcard J R
        hR1 hRv
      refine ⟨Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase g).wf hcard hR1, Φ, hΦ, hΦ0,
        fun v ↦ ?_, fun e he ↦ ?_⟩
      · change ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.natAdd _ i) (Fin.castAdd _ (I.lvLad g H B hd Q J v)) = _
        rw [lvLevel_rowAt_new_old J i _ (by
          rw [show (I.lvLevel g H B hd Q J).S.toCellScheme.grade (I.lvLad g H B hd Q J v) = 1
            from congrArg Prod.snd (lvLevel_gradedIndex_lad J v)]; omega)]
        exact hl v
      · change ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.natAdd _ i) (Fin.castAdd _ ((I.lvLevel g H B hd Q J).attEmb e)) = _
        rw [lvLevel_rowAt_new_old J i _ (by
          rw [show (I.lvLevel g H B hd Q J).S.toCellScheme.grade
              ((I.lvLevel g H B hd Q J).attEmb e) = (I.attachment g).toCellScheme.grade e
            from (lvLevel_gradedIndex_embed J (Fin.castAdd _ e)).trans
              (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e) |> congrArg Prod.snd]
          exact he), ← hRdef, lvLevel_σ_attEmb hcard J R hR1 e]
        exact ha e

/-- **A cell of full scope at every grade from `2` to the grade of the level**: the cells of the
bottom state. -/
theorem lvLevel_hexist : ∀ (J k : ℕ), 2 ≤ k → k ≤ J + 1 →
    ∃ f : Fin (I.lvLevel g H B hd Q J).S.card,
      (I.lvLevel g H B hd Q J).S.toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), k)
  | 0, k, h2, hk => absurd (h2.trans hk) (by omega)
  | J + 1, k, h2, hk => by
    classical
    rcases Nat.lt_or_ge k (J + 2) with hlt | hge
    · obtain ⟨f, hf⟩ := lvLevel_hexist J k h2 (by omega)
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
theorem lvLevel_grade_attEmb (J : ℕ) (e : Fin (I.attachment g).card) :
    (I.lvLevel g H B hd Q J).S.toCellScheme.grade ((I.lvLevel g H B hd Q J).attEmb e) =
      (I.attachment g).toCellScheme.grade e :=
  (lvLevel_gradedIndex_embed J (Fin.castAdd _ e)).trans
    (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e) |> congrArg Prod.snd

theorem lvLevel_grade_lad (J : ℕ)
    (v : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.lvLevel g H B hd Q J).S.toCellScheme.grade (I.lvLad g H B hd Q J v) = 1 :=
  congrArg Prod.snd (lvLevel_gradedIndex_lad J v)

/-- **The agreement at a shadow** (in the level at the grade `J + 1`). -/
theorem lvLevel_hagree (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card ≤ B) :
    ∀ (J : ℕ), J + 1 ≤ m + 2 → ∀ (f u : Fin (I.lvLevel g H B hd Q J).S.card) (K k : ℕ),
      (I.lvLevel g H B hd Q J).S.toCellScheme.gradedIndex f =
        ((univ : Finset (Fin (m + 2))), K) →
      (I.lvLevel g H B hd Q J).S.toCellScheme.gradedIndex u =
        ((univ : Finset (Fin (m + 2))), k) → 2 ≤ k → k ≤ K →
      ∀ e, (I.attachment g).toCellScheme.grade e = k → ∃ v,
        (I.lvLevel g H B hd Q J).S.rowAt u (I.lvLad g H B hd Q J v) =
          (I.lvLevel g H B hd Q J).S.rowAt u ((I.lvLevel g H B hd Q J).attEmb e) ∧
        min ((I.lvLevel g H B hd Q J).S.rowAt f (I.lvLad g H B hd Q J v))
            ((I.lvLevel g H B hd Q J).S.rowAt f u) =
          min ((I.lvLevel g H B hd Q J).S.rowAt f ((I.lvLevel g H B hd Q J).attEmb e))
            ((I.lvLevel g H B hd Q J).S.rowAt f u)
  | 0, _, f, u, K, k, hf, hu, h2, hkK, e, he => by
    exfalso
    have := lvLevel_grade_le_of_scope (hd := hd) (Q := Q) (B := B) 0 f (congrArg Prod.fst hf)
    rw [show (I.lvLevel g H B hd Q 0).S.toCellScheme.grade f = K from congrArg Prod.snd hf] at this
    omega
  | J + 1, hJ, f, u, K, k, hf, hu, h2, hkK, e, he => by
    classical
    change Fin ((I.lvLevel g H B hd Q J).S.card + (I.lvCat g B hd Q (J + 2)).card) at f u
    induction f using Fin.addCases with
    | left f' =>
      have hf' : (I.lvLevel g H B hd Q J).S.toCellScheme.gradedIndex f' =
          ((univ : Finset (Fin (m + 2))), K) :=
        (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).symm.trans hf
      have hKJ := lvLevel_grade_le_of_scope (hd := hd) (Q := Q) (B := B) J f'
        (congrArg Prod.fst hf')
      rw [show (I.lvLevel g H B hd Q J).S.toCellScheme.grade f' = K
        from congrArg Prod.snd hf'] at hKJ
      induction u using Fin.addCases with
      | left u' =>
        obtain ⟨v, hrv, hmin⟩ := lvLevel_hagree hH hcard hQ hB J (by omega) f' u' K k hf'
          ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).symm.trans hu) h2 hkK e he
        refine ⟨v, ?_, ?_⟩
        · change ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.castAdd _ u') (Fin.castAdd _ (I.lvLad g H B hd Q J v)) =
            ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.castAdd _ u') (Fin.castAdd _ ((I.lvLevel g H B hd Q J).attEmb e))
          rw [Scheme.rowAt_appendFullCells_castAdd, Scheme.rowAt_appendFullCells_castAdd]
          exact hrv
        · change min (((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.castAdd _ f') (Fin.castAdd _ (I.lvLad g H B hd Q J v)))
            (((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.castAdd _ f') (Fin.castAdd _ u')) =
            min (((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.castAdd _ f') (Fin.castAdd _ ((I.lvLevel g H B hd Q J).attEmb e)))
            (((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
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
      have hσe : (I.lvLevel g H B hd Q J).σ Rf ((I.lvLevel g H B hd Q J).attEmb e) = Rf e :=
        lvLevel_σ_attEmb hcard J Rf hRf1 e
      have hge : (I.lvLevel g H B hd Q J).S.toCellScheme.grade
          ((I.lvLevel g H B hd Q J).attEmb e) ≤ J + 2 := by
        rw [lvLevel_grade_attEmb]; omega
      have hgl (v : Scheme.LadderPt (I.attachmentBase g).S
          (Scheme.RankMember (I.attachmentBase g).S H) H) :
          (I.lvLevel g H B hd Q J).S.toCellScheme.grade (I.lvLad g H B hd Q J v) ≤ J + 2 := by
        rw [lvLevel_grade_lad]; omega
      induction u using Fin.addCases with
      | left u' =>
        have hu' : (I.lvLevel g H B hd Q J).S.toCellScheme.gradedIndex u' =
            ((univ : Finset (Fin (m + 2))), k) :=
          (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).symm.trans hu
        have hgu : (I.lvLevel g H B hd Q J).S.toCellScheme.grade u' ≤ J + 2 := by
          rw [show (I.lvLevel g H B hd Q J).S.toCellScheme.grade u' = k
            from congrArg Prod.snd hu']; omega
        obtain ⟨v, hrv, hmin⟩ := lvLevel_shadowAgree hH hcard hQ hB J (by omega) Rf hRf1 hRfv u'
          k hu' h2 e he.le
        refine ⟨v, ?_, ?_⟩
        · change ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.castAdd _ u') (Fin.castAdd _ (I.lvLad g H B hd Q J v)) =
            ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.castAdd _ u') (Fin.castAdd _ ((I.lvLevel g H B hd Q J).attEmb e))
          rw [Scheme.rowAt_appendFullCells_castAdd, Scheme.rowAt_appendFullCells_castAdd]
          exact hrv
        · change min (((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i) (Fin.castAdd _ (I.lvLad g H B hd Q J v)))
            (((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i) (Fin.castAdd _ u')) =
            min (((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i) (Fin.castAdd _ ((I.lvLevel g H B hd Q J).attEmb e)))
            (((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i) (Fin.castAdd _ u'))
          rw [lvLevel_rowAt_new_old J i _ (hgl v), lvLevel_rowAt_new_old J i _ hgu,
            lvLevel_rowAt_new_old J i _ hge, ← hRf, hσe]
          exact hmin
      | right i' =>
        set Ru := ((I.lvCat g B hd Q (J + 2)).equivFin.symm i').1 with hRu
        obtain ⟨-, hRul, hRuv, -, -⟩ :=
          mem_lvCat.mp ((I.lvCat g B hd Q (J + 2)).equivFin.symm i').2
        have hRu1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
            (fun e ↦ Ru e) := hRul.mono (X := ((univ : Finset (Fin (m + 2))), 1))
              ⟨subset_rfl, by omega⟩
        obtain ⟨Φ, -, -, hlR, haR⟩ := lvLevel_ladderReading (hd := hd) (Q := Q) (B := B) hcard J
          Ru hRu1 hRuv
        set a := Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase g).wf hcard hRu1 with ha
        have hshadow : (I.lvLevel g H B hd Q J).σ Ru (I.lvLad g H B hd Q J (a, Sum.inr e)) =
            Ru e := by
          rw [hlR, haR e]
          congr 1
          exact ladderIndex_parent (Scheme.ladderCeil_le (Scheme.rankProf_le _ H)) (a, Sum.inr e)
        refine ⟨(a, Sum.inr e), ?_, ?_⟩
        · change ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i') (Fin.castAdd _ (I.lvLad g H B hd Q J (a, Sum.inr e))) =
            ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i') (Fin.castAdd _ ((I.lvLevel g H B hd Q J).attEmb e))
          rw [lvLevel_rowAt_new_old J i' _ (hgl _), lvLevel_rowAt_new_old J i' _ hge, ← hRu,
            hshadow, lvLevel_σ_attEmb hcard J Ru hRu1 e]
        · have hgood := lvLevel_good (B := B) (hd := hd) hH hcard hQ hB J (by omega)
          set h := agreementHeight (grid (J + 2) B) Rf Ru with hh
          have hspec := agreementHeight_spec (bot_mem_grid (J + 2) B) Rf Ru
          have hcap := hgood.capAgree Rf Ru hRf1 hRu1 hRfB h (isSelfVisible_of_mem_grid hspec.1)
            (isShort_of_mem_grid hspec.1) hspec.2 (I.lvLad g H B hd Q J (a, Sum.inr e))
          change min (((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i) (Fin.castAdd _ (I.lvLad g H B hd Q J (a, Sum.inr e))))
            (((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i) (Fin.natAdd _ i')) =
            min (((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i) (Fin.castAdd _ ((I.lvLevel g H B hd Q J).attEmb e)))
            (((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
            (Fin.natAdd _ i) (Fin.natAdd _ i'))
          rw [lvLevel_rowAt_new_old J i _ (hgl _), lvLevel_rowAt_new_new J i i',
            lvLevel_rowAt_new_old J i _ hge, ← hRf, ← hRu, ← hh, hσe, hcap, hshadow, hspec.2 e]

/-- **The twins** (in the level at the grade `J + 1`, with `2 · #cells < B`). -/
theorem lvLevel_htwin (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB' : 2 * (I.attachment g).card < B) :
    ∀ (J : ℕ) (f : Fin (I.lvLevel g H B hd Q J).S.card) (K k : ℕ),
      (I.lvLevel g H B hd Q J).S.toCellScheme.gradedIndex f =
        ((univ : Finset (Fin (m + 2))), K) → 2 ≤ k → k ≤ K →
      ∀ e, (I.attachment g).toCellScheme.grade e = k →
      ∃ et, (I.lvLevel g H B hd Q J).S.toCellScheme.gradedIndex et =
          ((univ : Finset (Fin (m + 2))), k) ∧
        (I.lvLevel g H B hd Q J).S.rowAt f ((I.lvLevel g H B hd Q J).attEmb e) ≤
          (I.lvLevel g H B hd Q J).S.rowAt f et
  | 0, f, K, k, hf, h2, hkK, e, he => by
    exfalso
    have := lvLevel_grade_le_of_scope (hd := hd) (Q := Q) (B := B) 0 f (congrArg Prod.fst hf)
    rw [show (I.lvLevel g H B hd Q 0).S.toCellScheme.grade f = K from congrArg Prod.snd hf] at this
    omega
  | J + 1, f, K, k, hf, h2, hkK, e, he => by
    classical
    change Fin ((I.lvLevel g H B hd Q J).S.card + (I.lvCat g B hd Q (J + 2)).card) at f
    induction f using Fin.addCases with
    | left f' =>
      obtain ⟨et, het, hle⟩ := lvLevel_htwin hcard hQ hB' J f' K k
        ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).symm.trans hf) h2 hkK e he
      refine ⟨Fin.castAdd _ et,
        (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans het, ?_⟩
      change ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
        (Fin.castAdd _ f') (Fin.castAdd _ ((I.lvLevel g H B hd Q J).attEmb e)) ≤
        ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
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
      have hge : (I.lvLevel g H B hd Q J).S.toCellScheme.grade
          ((I.lvLevel g H B hd Q J).attEmb e) ≤ J + 2 := by
        rw [lvLevel_grade_attEmb]; omega
      have hre : ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.natAdd _ i) (Fin.castAdd _ ((I.lvLevel g H B hd Q J).attEmb e)) = R e := by
        rw [lvLevel_rowAt_new_old J i _ hge, ← hRdef, lvLevel_σ_attEmb hcard J R hR1 e]
      rcases Nat.lt_or_ge k (J + 2) with hlt | hge2
      · obtain ⟨et, het, hle⟩ := lvLevel_twinGen (hd := hd) (B := B) hcard hQ hB' J R
          (hRl.mono (X := ((univ : Finset (Fin (m + 2))), J + 1)) ⟨subset_rfl, by omega⟩) hRv
          (attachAdmits_pred hRA) k h2 (by omega)
        have hget : (I.lvLevel g H B hd Q J).S.toCellScheme.grade et ≤ J + 2 := by
          rw [show (I.lvLevel g H B hd Q J).S.toCellScheme.grade et = k
            from congrArg Prod.snd het]; omega
        refine ⟨Fin.castAdd _ et,
          (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans het, ?_⟩
        change ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.natAdd _ i) (Fin.castAdd _ ((I.lvLevel g H B hd Q J).attEmb e)) ≤
          ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.natAdd _ i) (Fin.castAdd _ et)
        rw [hre, lvLevel_rowAt_new_old J i _ hget]
        exact hle e
      · obtain rfl : k = J + 2 := by omega
        refine ⟨Fin.natAdd _ i, hf, ?_⟩
        change ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.natAdd _ i) (Fin.castAdd _ ((I.lvLevel g H B hd Q J).attEmb e)) ≤
          ((I.lvLevel g H B hd Q J).nS B (I.lvCat g B hd Q (J + 2))).rowAt
          (Fin.natAdd _ i) (Fin.natAdd _ i)
        rw [hre, lvLevel_rowAt_new_new J i i, ← hRdef,
          agreementHeight_self (gridPoint_mem_grid le_rfl) (fun _ hx ↦ le_gridPoint_of_mem_grid hx)]
        exact le_gridPoint_of_mem_codeGrid (hRB e)

/-- **The lift from a mixed face into the full face of a replicated level** (with
`2 · #cells < B`): for a good level at the grade `J + 1`, a mixed face `U` and
`1 ≤ j ≤ min (|U|) (J + 1)`, the replicated level lifts capped from `(U, j)` into `(univ, j)`. -/
theorem lvRep_cappedLift_mixed_univ (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB' : 2 * (I.attachment g).card < B) {J : ℕ} (hJ : J + 1 ≤ m + 2)
    (hN : (I.lvLevel g H B hd Q J).Good B (lvAdm hd Q)) {U : Finset (Fin (m + 2))}
    (hU : U ∈ I.mixedFaces g) {j : ℕ} (hj1 : 1 ≤ j) (hjU : j ≤ #U) (hjJ : j ≤ J + 1) :
    hN.rep.rows.CappedLift (X := (U, j)) (Y := ((univ : Finset (Fin (m + 2))), j))
      ⟨subset_univ _, le_rfl⟩ :=
  cappedLift_mirror_mixed_univ (hmix := hN.not_subset_scope) hH hN.consistent
    (fun x ↦ hN.wf.isWellFormed.grade_pos x) hN.gradedIndex_attEmb
    (fun x hx ↦ (hN.mem_range x hx).elim fun e he ↦ ⟨e, he.symm⟩)
    (lvLevel_gradedIndex_lad J) (lvLevel_rowAt_lad_lad J) (lvLevel_rowAt_lad_att J)
    (lvLevel_hone J) (lvLevel_hread hcard J) (lvLevel_hagree hH hcard hQ hB'.le J hJ)
    (lvLevel_htwin hcard hQ hB' J) hU (fun k h2 hk ↦ lvLevel_hexist J k h2 (hk.trans hjJ)) hj1 hjU

/-- **The lift between mixed faces of a replicated level** (with `2 · #cells < B`): for a good
level at the grade `J + 1`, mixed faces `U ⊆ V` and `1 ≤ j ≤ min (|U|) (J + 1)`, the replicated
level lifts capped from `(U, j)` into `(V, j)`. -/
theorem lvRep_cappedLift_mixed_mixed (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB' : 2 * (I.attachment g).card < B) {J : ℕ} (hJ : J + 1 ≤ m + 2)
    (hN : (I.lvLevel g H B hd Q J).Good B (lvAdm hd Q)) {U V : Finset (Fin (m + 2))}
    (hU : U ∈ I.mixedFaces g) (hV : V ∈ I.mixedFaces g) (hUV : U ⊆ V) {j : ℕ} (hj1 : 1 ≤ j)
    (hjU : j ≤ #U) (hjJ : j ≤ J + 1) :
    hN.rep.rows.CappedLift (X := (U, j)) (Y := (V, j)) ⟨hUV, le_rfl⟩ :=
  cappedLift_mirror_mixed_mixed (hmix := hN.not_subset_scope) hH hN.consistent
    (fun x ↦ hN.wf.isWellFormed.grade_pos x) hN.gradedIndex_attEmb
    (fun x hx ↦ (hN.mem_range x hx).elim fun e he ↦ ⟨e, he.symm⟩)
    (lvLevel_gradedIndex_lad J) (lvLevel_rowAt_lad_lad J) (lvLevel_rowAt_lad_att J)
    (lvLevel_hone J) (lvLevel_hread hcard J) (lvLevel_hagree hH hcard hQ hB'.le J hJ)
    (lvLevel_htwin hcard hQ hB' J) hU hV hUV (fun k h2 hk ↦ lvLevel_hexist J k h2 (hk.trans hjJ))
    hj1 hjU

end Seed

end VaughtConjecture
