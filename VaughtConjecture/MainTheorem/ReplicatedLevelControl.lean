/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelGrades

/-!
# The controllers of a re-rendered level

Roadmap, Layer 3 ((R3) and (R4), recognition on the rows of the levels re-rendered per grade).

**The controllers** (`Seed.lvLevel_controller`): a cell of full scope at the grade `k + 2` of the
level at the grade `j + 1` is the cell of a state `R` of the catalogue `lvCat (k + 2)`; it reads a
cell `t` of the ladder base as the section of the level at the grade `k + 1` at `R`, below its
grade, and `⊥` above.  On the attachment this is the truncation of `R` at `k + 2`
(`Seed.lvLevel_controller_attach`, the section being literal on the attachment).

**The ladder-controller clauses** (`Seed.lvLevel_ladderController`), at the threshold `N ≥ 2` of
the requests: a cell of full scope at `(univ, N)` stores, on the context and donor cells, a state
admitted on the exact class; its reading of the top rung of a member is at least its reading of the
cap; and every positive value it stores below the cap is the reading of a rung.  These are the
clauses of `GrowthCarrier.IsLadderController` read on the level, with the rungs the ladder points
of the ladder base (`Seed.lvRung`).

**The bottom-state exception.**  For a state with a value other than `⊥` the rungs read the
positive table of the state (`Seed.lvLevel_σ_embed`), and the clauses are those of the ladder
recovery.  For the bottom state the rungs read the gap values (`Seed.lvLevel_σ_embed_bot`), not the
positive table; the clauses still hold there, the stored state being `⊥` (its cap value is `⊥`, and
no positive value is stored).  The table `F` of the controller is the reading of the rungs, so
recognition handles `⊥` without the ladder recovery.

## References

The controllers of the growth step are those of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

/-- The extension of a state with a rank member reads the positive table on the ladder. -/
theorem Scheme.LadderBaseData.stateExtOf_natAdd' {n' : ℕ} {B' : Scheme.LadderBaseData.{u} n'}
    {H' : ℕ} (R : Fin B'.S.card → Label.{u}) (a : Scheme.RankMember B'.S H')
    (j : Fin (Scheme.ladderCard B'.S (Scheme.RankMember B'.S H') H')) :
    B'.stateExtOf R a (Fin.natAdd _ j) =
      posTable R (Scheme.baseIndex H' (Scheme.rankProf B'.S H') a (Fin.natAdd _ j)) :=
  Fin.append_right _ _ j

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}
  {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

/-- The cells of the ladder base keep their graded indices in every level. -/
theorem lvLevel_gradedIndex_embed : ∀ (j : ℕ) (t : Fin (I.lvBase g H).card),
    (I.lvLevel g H B hd Q j).S.toCellScheme.gradedIndex ((I.lvLevel g H B hd Q j).embed t) =
      (I.lvBase g H).toCellScheme.gradedIndex t
  | 0, _ => rfl
  | j + 1, t => (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
      (lvLevel_gradedIndex_embed j t)

/-- **The controllers of the levels**: a cell of full scope at the grade `k + 2` of a level is the
cell of a state `R` of the catalogue at `k + 2`, reading a cell of the ladder base as the section
of the level at the grade `k + 1` at `R` below its grade, and `⊥` above. -/
theorem lvLevel_controller : ∀ (j : ℕ) (u : Fin (I.lvLevel g H B hd Q j).S.card) (k : ℕ),
    (I.lvLevel g H B hd Q j).S.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k + 2) →
    ∃ R ∈ I.lvCat g B hd Q (k + 2), ∀ t : Fin (I.lvBase g H).card,
      (I.lvLevel g H B hd Q j).S.rowAt u ((I.lvLevel g H B hd Q j).embed t) =
        if (I.lvBase g H).toCellScheme.grade t ≤ k + 2 then
          (I.lvLevel g H B hd Q k).σ R ((I.lvLevel g H B hd Q k).embed t) else ⊥
  | 0, u, k, hu => by
    exfalso
    rcases (I.lvLevel g H B hd Q 0).inv u with h | h
    · have := congrArg Prod.snd hu
      change (I.lvLevel g H B hd Q 0).S.toCellScheme.grade u = k + 2 at this
      omega
    · exact h (congrArg Prod.fst hu)
  | j + 1, u, k, hu => by
    classical
    set N := I.lvLevel g H B hd Q j with hN
    set C := I.lvCat g B hd Q (j + 2) with hC
    change Fin (N.S.card + C.card) at u
    induction u using Fin.addCases with
    | left u' =>
      have hu' : N.S.toCellScheme.gradedIndex u' = ((univ : Finset (Fin (m + 2))), k + 2) :=
        (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).symm.trans hu
      obtain ⟨R, hR, hrow⟩ := lvLevel_controller j u' k hu'
      refine ⟨R, hR, fun t ↦ ?_⟩
      change (N.nS B C).rowAt (Fin.castAdd _ u') (Fin.castAdd _ (N.embed t)) = _
      rw [Scheme.rowAt_appendFullCells_castAdd]
      exact hrow t
    | right i =>
      have hk : k = j := by
        have := congrArg Prod.snd
          ((Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i).symm.trans hu)
        simp only at this
        omega
      subst hk
      refine ⟨(C.equivFin.symm i).1, (C.equivFin.symm i).2, fun t ↦ ?_⟩
      change (N.nS B C).rowAt (Fin.natAdd _ i) (Fin.castAdd _ (N.embed t)) = _
      have hiff : (Fin.castAdd C.card (N.embed t) : Fin (N.S.card + C.card)) ∈
          (N.nS B C).toCellScheme.below
            ((N.nS B C).toCellScheme.gradedIndex (Fin.natAdd _ i)) ↔
          (I.lvBase g H).toCellScheme.grade t ≤ k + 2 := by
        rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_natAdd,
          Scheme.appendFullCellsScheme_gradedIndex_castAdd, lvLevel_gradedIndex_embed]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨subset_univ _, h⟩⟩
      split_ifs with ht
      · rw [Scheme.rowAt_of_mem (hiff.mpr ht), Scheme.appendFullCells_row_natAdd]
        exact ALvl.Φ_castAdd _ _ _
      · exact Scheme.rowAt_of_notMem (mt hiff.mp ht)

/-- The rung `i` of a member: the ladder point of the member at the place `min i (H - 1)`. -/
noncomputable def lvRung (hH : 0 < H) (a : Scheme.RankMember (I.attachmentBase g).S H) (i : ℕ) :
    Fin (I.lvBase g H).card :=
  Fin.natAdd _ (Scheme.ladderEquiv _ _ H (a, Sum.inl ⟨min i (H - 1), by omega⟩))

theorem grade_lvRung (hH : 0 < H) (a : Scheme.RankMember (I.attachmentBase g).S H) (i : ℕ) :
    (I.lvBase g H).toCellScheme.grade (lvRung hH a i) = 1 :=
  Scheme.appendFullCellsScheme_grade_natAdd _ _ _ _

/-- **A controller reads the attachment as the truncation of its state**: for a good level at the
grade `k + 1` and a state `R` lawful below `(univ, 1)`, the reading of a cell of the attachment is
`R` truncated at `k + 2`. -/
theorem lvLevel_controller_attach {k : ℕ} {A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop}
    (hN : (I.lvLevel g H B hd Q k).Good B A) {R : Fin (I.attachment g).card → Label.{u}}
    (hR1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1) fun e ↦ R e)
    (c : Fin (I.attachment g).card) :
    (if (I.lvBase g H).toCellScheme.grade (Fin.castAdd _ c) ≤ k + 2 then
      (I.lvLevel g H B hd Q k).σ R ((I.lvLevel g H B hd Q k).embed (Fin.castAdd _ c)) else ⊥) =
      I.attachHatAt g (k + 2) R c := by
  unfold attachHatAt
  have hg : (I.lvBase g H).toCellScheme.grade (Fin.castAdd _ c) =
      (I.attachment g).toCellScheme.grade c :=
    Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _
  rw [hg]
  split_ifs
  · exact hN.literal R hR1 c
  · rfl

/-- **The ladder-controller clauses on a level**, at the threshold `N ≥ 2` of the requests: a
cell of full scope at `(univ, N)` stores on the context and donor cells a state admitted on the
exact class; for some member `a` and the table `F` of its readings of the rungs, its reading of
the top rung is at least its reading of the cap, and every positive value it stores below the cap
is the reading of a rung.  The bottom state is covered: it stores `⊥` (cap value `⊥`, no positive
value), while its rungs read the gap values (`Seed.lvLevel_σ_embed_bot`). -/
theorem lvLevel_ladderController (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card ≤ B) (hN2 : 2 ≤ Q.threshold)
    {j : ℕ} (u : Fin (I.lvLevel g H B hd Q j).S.card)
    (hu : (I.lvLevel g H B hd Q j).S.toCellScheme.gradedIndex u =
      ((univ : Finset (Fin (m + 2))), Q.threshold)) :
    ∃ (a : Scheme.RankMember (I.attachmentBase g).S H) (F : ℕ → Label.{u}),
      Q.AdmitsOnClass
          (fun x ↦ (I.lvLevel g H B hd Q j).S.rowAt u
            ((I.lvLevel g H B hd Q j).attEmb (I.attachCtxCell g x)))
          (fun y ↦ (I.lvLevel g H B hd Q j).S.rowAt u
            ((I.lvLevel g H B hd Q j).attEmb (I.attachDonCell g hd y))) ∧
        (I.lvLevel g H B hd Q j).S.rowAt u
            ((I.lvLevel g H B hd Q j).attEmb (I.attachCtxCell g Q.cap)) ≤
          (I.lvLevel g H B hd Q j).S.rowAt u
            ((I.lvLevel g H B hd Q j).embed (lvRung hH a (H - 1))) ∧
        (∀ i < H, (I.lvLevel g H B hd Q j).S.rowAt u
            ((I.lvLevel g H B hd Q j).embed (lvRung hH a i)) = F (i + 1)) ∧
        ∀ x ∈ I.left.toCellScheme.below (I.left.toCellScheme.gradedIndex Q.cap),
          (I.lvLevel g H B hd Q j).S.rowAt u
              ((I.lvLevel g H B hd Q j).attEmb (I.attachCtxCell g x)) ≠ ⊥ →
            ∃ i < H, (I.lvLevel g H B hd Q j).S.rowAt u
              ((I.lvLevel g H B hd Q j).attEmb (I.attachCtxCell g x)) = F (i + 1) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, Q.threshold = k + 2 := ⟨Q.threshold - 2, by omega⟩
  have hkm : k + 2 ≤ m + 1 := by
    have h1 := I.left.isWellFormed.isWellFormed.grade_le_card Q.cap
    have h2 : #(I.left.toCellScheme.scope Q.cap) ≤ m + 1 :=
      (card_le_univ _).trans (by simp)
    have h3 : Q.threshold ≤ m + 1 := h1.trans h2
    omega
  rw [hk] at hu
  obtain ⟨R, hR, hrow⟩ := lvLevel_controller j u k hu
  obtain ⟨-, hRl, hRv, -, hRA⟩ := mem_lvCat.mp hR
  have hR1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
      fun e ↦ R e := hRl.mono (X := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_rfl, by omega⟩
  have hgood := lvLevel_good (B := B) (hd := hd) hH hcard hQ hB k (by omega)
  have hatt (c : Fin (I.attachment g).card) :
      (I.lvLevel g H B hd Q j).S.rowAt u ((I.lvLevel g H B hd Q j).attEmb c) =
        I.attachHatAt g (k + 2) R c :=
    (hrow (Fin.castAdd _ c)).trans (lvLevel_controller_attach hgood hR1 c)
  set a := Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase g).wf hcard hR1 with ha
  set F : ℕ → Label.{u} := fun i ↦ (I.lvLevel g H B hd Q j).S.rowAt u
    ((I.lvLevel g H B hd Q j).embed (lvRung hH a (i - 1))) with hF
  -- the rungs read the positive table of a positive state
  have hrung (hpos : ∃ e, R e ≠ ⊥) (i : ℕ) (hi : i < H) :
      (I.lvLevel g H B hd Q j).S.rowAt u ((I.lvLevel g H B hd Q j).embed (lvRung hH a i)) =
        posTable R (i + 1) := by
    rw [hrow, grade_lvRung, ite_eq_left (by omega),
      lvLevel_σ_embed hcard k R hR1 hRv hpos, lvBaseSec_of_isLawfulBelow hcard hR1, ← ha]
    have h := Scheme.baseIndex_self (Scheme.rankProf_le _ H)
      ((a, Sum.inl ⟨min i (H - 1), by omega⟩) :
        Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H)
    simp only [Scheme.ladderCeil, Sum.elim_inl] at h
    refine (Scheme.LadderBaseData.stateExtOf_natAdd' (B' := I.attachmentBase g) R a _).trans ?_
    rw [h]
    congr 1
    omega
  have hrk (e : Fin (I.attachment g).card) : rankVector R e ≤ H :=
    (rankVector_le e).trans (le_of_eq_of_le (Fintype.card_fin _) hcard)
  refine ⟨a, F, ?_, ?_, fun i hi ↦ ?_, fun x _ hx ↦ ?_⟩
  · -- the stored state is admitted
    have hadm := hRA (by omega)
    have e1 : (fun x ↦ (I.lvLevel g H B hd Q j).S.rowAt u
        ((I.lvLevel g H B hd Q j).attEmb (I.attachCtxCell g x))) =
        fun x ↦ I.attachHatAt g Q.threshold R (I.attachCtxCell g x) :=
      funext fun x ↦ by rw [hatt, hk]
    have e2 : (fun y ↦ (I.lvLevel g H B hd Q j).S.rowAt u
        ((I.lvLevel g H B hd Q j).attEmb (I.attachDonCell g hd y))) =
        fun y ↦ I.attachHatAt g Q.threshold R (I.attachDonCell g hd y) :=
      funext fun y ↦ by rw [hatt, hk]
    rw [e1, e2]
    exact hadm
  · -- the top rung
    rw [hatt]
    by_cases hpos : ∃ e, R e ≠ ⊥
    · rw [hrung hpos (H - 1) (by omega), show H - 1 + 1 = H by omega]
      unfold attachHatAt
      split_ifs
      · exact le_posTable hRv (hrk _)
      · exact bot_le
    · push Not at hpos
      unfold attachHatAt
      split_ifs
      · rw [hpos]; exact bot_le
      · exact bot_le
  · simp only [hF, Nat.add_sub_cancel]
  · -- a positive stored value is the reading of a rung
    rw [hatt] at hx ⊢
    have hRx : R (I.attachCtxCell g x) ≠ ⊥ := by
      intro h0
      apply hx
      unfold attachHatAt
      split_ifs
      exacts [h0, rfl]
    have hpos : ∃ e, R e ≠ ⊥ := ⟨_, hRx⟩
    have h0 : rankVector R (I.attachCtxCell g x) ≠ 0 :=
      fun h ↦ hRx ((rankVector_eq_zero_iff _).mp h)
    refine ⟨rankVector R (I.attachCtxCell g x) - 1, by have := hrk (I.attachCtxCell g x); omega,
      ?_⟩
    have hF1 : F (rankVector R (I.attachCtxCell g x) - 1 + 1) =
        posTable R (rankVector R (I.attachCtxCell g x)) := by
      simp only [hF, Nat.add_sub_cancel]
      rw [hrung hpos _ (by have := hrk (I.attachCtxCell g x); omega)]
      congr 1
      omega
    rw [hF1, posTable_rankVector hRv]
    unfold attachHatAt at hx ⊢
    by_cases hc : (I.attachment g).toCellScheme.grade (I.attachCtxCell g x) ≤ k + 2
    · rw [ite_eq_left hc]
    · rw [ite_eq_right hc] at hx
      exact absurd rfl hx

end Seed

end VaughtConjecture
