/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanK2GradeTwoLabels
import VaughtConjecture.ProcessRank.SpanMirrorLift

/-!
# The row conditions of the mirror theorem on the grade-two scheme of the test with `K = 2`

Process rank `ω₁`, the finite span of mutual rigidity: the one-member reading, the common shadow
and the twin hypotheses of the lift theorem over a mirrored attachment
(`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed`: `hreadMember`, `hshadow`, `htwinAbove`),
stated literally for the grade-two scheme `ProcessRank.k2Grade2`.  The parameters are
instantiated as follows: the scheme `T` is `k2Grade2`, the attachment `Att` is the attachment of
the test with `K = 2`, the profiles `Pf` are the rank members at the height `8` with their rank
profiles `prof`, the attachment cells `att e` are the old cells `Fin.castAdd _ (Fin.castAdd _ e)`
and the ladder points `lad v` are the cells `Fin.castAdd _ (ProcessRank.k2LadPt v)`.

The cells of full scope of `k2Grade2` at a grade at least two are its controllers, all at the grade
two (`ProcessRank.exists_natAdd_of_gradedIndex`), so each hypothesis is exactly its grade-two case.
Compiled here (theorem named):
* **one-member reading** (`ProcessRank.k2Grade2_hreadMember`), from
  `ProcessRank.k2Grade2_readMember`;
* **common shadow** (`ProcessRank.k2Grade2_hshadow`): for the controllers `f`, `u` of the states
  `R`, `Q` and an attachment cell `e`, the ladder point `(b, Sum.inr e)` of the rank member `b` of
  `Q` is read by `u` as `e` (`ProcessRank.k2ControllerRow_ladPt_parent`, by `ladderIndex_parent`),
  and at the cap `agreementHeight (grid 2 16) R Q` the controller `f` reads it as `e`
  (`Scheme.LadderBaseData.min_stateExtOf_eq`);
* **twin** (`ProcessRank.k2Grade2_htwinAbove`): each controller is its own twin; it reads itself
  as `gridPoint 2 16`, the top of the grid, which bounds every value of its row.

Open: the shadows and twins across grades, the grades three and four, legality of the completed
scheme, the four-point span of mutual rigidity of the test pair, and the countable upper bound on
the Scott classes.  None of these is claimed here.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label
open scoped Ordinal

set_option quotPrecheck false in
/-- The index of a ladder point for a member. -/
local notation "idx" => ladderIndex 8 (Scheme.rankProf k2AttachmentBase.S 8) Prod.fst
  (Scheme.ladderCeil (Scheme.rankProf k2AttachmentBase.S 8))

/-- **The cells of full scope at a grade at least two are controllers**, at the grade two. -/
theorem exists_natAdd_of_gradedIndex {f : Fin k2Grade2.{u}.card} {K : ℕ}
    (hf : k2Grade2.{u}.toCellScheme.gradedIndex f = ((univ : Finset (Fin 4)), K)) (hK : 2 ≤ K) :
    K = 2 ∧ ∃ i, f = Fin.natAdd _ i := by
  induction f using Fin.addCases with
  | left z =>
    exfalso
    have hg : k2Grade2.{u}.toCellScheme.gradedIndex (Fin.castAdd _ z) =
        k2Ladder.{u}.toCellScheme.gradedIndex z :=
      Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ z
    refine k2Ladder_not_le z ?_
    rw [← hg, hf]
    exact ⟨subset_refl _, hK⟩
  | right i =>
    have hg : k2Grade2.{u}.toCellScheme.gradedIndex (Fin.natAdd _ i) =
        ((univ : Finset (Fin 4)), 2) :=
      Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i
    exact ⟨(congrArg Prod.snd (hf.symm.trans hg)), i, rfl⟩

/-- **The ladder point of the rank member of a state over a cell reads the cell**: for a state
lawful below `(univ, 1)` with values self-visible at the grade one, its controller row reads the
ladder point `(b, Sum.inr e)` of its rank member `b` as `e` (`ladderIndex_parent`). -/
theorem k2ControllerRow_ladPt_parent {R : Fin k2AttachmentBase.{u}.S.card → Label.{u}}
    (h : k2AttachmentBase.S.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 1) (fun e ↦ R e))
    (hv : ∀ e, IsSelfVisible 1 (R e)) (e : Fin k2AttachmentBase.{u}.S.card) :
    k2ControllerRow R
        (k2LadPt (Scheme.RankMember.ofLawfulBelowOne (H := 8) k2AttachmentBase.wf k2_card_le h,
          Sum.inr e)) = R e := by
  rw [k2ControllerRow_of_isLawfulBelow h, k2LadPt]
  change Fin.append R _ (Fin.natAdd _ _) = _
  rw [Fin.append_right, Scheme.baseIndex_natAdd, Equiv.symm_apply_apply]
  have hp := ladderIndex_parent (H := 8) (prof := Scheme.rankProf k2AttachmentBase.S 8)
    (parent := Prod.fst) (ceil := Scheme.ladderCeil (Scheme.rankProf k2AttachmentBase.S 8))
    (Scheme.ladderCeil_le (Scheme.rankProf_le k2AttachmentBase.S 8))
    (Scheme.RankMember.ofLawfulBelowOne (H := 8) k2AttachmentBase.wf k2_card_le h, Sum.inr e)
  rw [hp]
  change posTable R (Scheme.rankProf k2AttachmentBase.S 8 _ e) = R e
  rw [rankProf_ofLawfulBelowOne]
  exact posTable_rankVector hv e

/-- **The common shadow on the controller rows**: for states `R`, `Q` of the catalogue and an
attachment cell `e`, the ladder point of the rank member of `Q` over `e` is read by the row of `Q`
as `e`, and by the row of `R` as `e` at the cap `agreementHeight (grid 2 16) R Q`. -/
theorem k2ControllerRow_shadow {R Q : Fin k2AttachmentBase.{u}.S.card → Label.{u}}
    (hR : R ∈ k2Cat2) (hQ : Q ∈ k2Cat2) (e : Fin k2AttachmentBase.{u}.S.card) :
    ∃ v, k2ControllerRow Q (k2LadPt v) = k2ControllerRow Q (Fin.castAdd _ e) ∧
      min (k2ControllerRow R (k2LadPt v)) (agreementHeight (grid 2 16) R Q) =
        min (k2ControllerRow R (Fin.castAdd _ e)) (agreementHeight (grid 2 16) R Q) := by
  obtain ⟨-, hRl, -, -, -⟩ := mem_k2Cat2.mp hR
  obtain ⟨-, hQl, hQv, -, -⟩ := mem_k2Cat2.mp hQ
  have hR1 := isLawfulBelow_one_of_two hRl
  have hQ1 := isLawfulBelow_one_of_two hQl
  have hQe := k2ControllerRow_ladPt_parent hQ1 hQv e
  refine ⟨(Scheme.RankMember.ofLawfulBelowOne (H := 8) k2AttachmentBase.wf k2_card_le hQ1,
    Sum.inr e), ?_, ?_⟩
  · rw [hQe, k2ControllerRow_of_isLawfulBelow hQ1, Scheme.LadderBaseData.stateExtOf_castAdd']
  have hκm : agreementHeight (grid 2 16) R Q ∈ grid 2 16 :=
    (agreementHeight_spec (bot_mem_grid _ _) _ _).1
  by_cases hκ0 : agreementHeight (grid 2 16) R Q = ⊥
  · rw [hκ0, min_bot_right, min_bot_right]
  have hag := (agreementHeight_spec (bot_mem_grid 2 16) R Q).2
  have hmin := Scheme.LadderBaseData.min_stateExtOf_eq (B := k2AttachmentBase) k2_card_le hκ0
    ((isSelfVisible_of_mem_grid hκm).mono (by decide)) hQ1 hR1 hag
    (k2LadPt (Scheme.RankMember.ofLawfulBelowOne (H := 8) k2AttachmentBase.wf k2_card_le hQ1,
      Sum.inr e))
  rw [← k2ControllerRow_of_isLawfulBelow hR1, ← k2ControllerRow_of_isLawfulBelow hQ1, hQe] at hmin
  rw [hmin, ← hag e, k2ControllerRow_of_isLawfulBelow hR1,
    Scheme.LadderBaseData.stateExtOf_castAdd']

/-- **The one-member reading**, in the form of the hypothesis `hreadMember` of
`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed` for the grade-two scheme. -/
theorem k2Grade2_hreadMember : ∀ (f : Fin k2Grade2.{u}.card) K,
    k2Grade2.{u}.toCellScheme.gradedIndex f = ((univ : Finset (Fin 4)), K) → 2 ≤ K →
      ∃ (b : Scheme.RankMember k2AttachmentBase.{u}.S 8) (Φ : ℕ → Label.{u}), Monotone Φ ∧
        Φ 0 = ⊥ ∧ (∀ v, k2Grade2.{u}.rowAt f (Fin.castAdd _ (k2LadPt v)) = Φ (idx b v)) ∧
        ∀ e, k2AttachmentBase.{u}.S.toCellScheme.grade e ≤ K →
          k2Grade2.{u}.rowAt f (Fin.castAdd _ (Fin.castAdd _ e)) =
            Φ (Scheme.rankProf k2AttachmentBase.S 8 b e) := by
  intro f K hf hK
  obtain ⟨rfl, -⟩ := exists_natAdd_of_gradedIndex hf hK
  obtain ⟨b, Φ, hΦ, hΦ0, hl, ha⟩ := k2Grade2_readMember f hf
  exact ⟨b, Φ, hΦ, hΦ0, hl, fun e _ ↦ ha e⟩

/-- **The common shadow**, in the form of the hypothesis `hshadow` of
`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed` for the grade-two scheme: for the
controllers `f`, `u` of states `R`, `Q` and an attachment cell `e`, the ladder point of the rank
member of `Q` over `e` is read by `u` as `e`, and by `f` as `e` at the cap read by `f` at `u`
(the agreement height of `R` and `Q`). -/
theorem k2Grade2_hshadow : ∀ (f u : Fin k2Grade2.{u}.card) K k,
    k2Grade2.{u}.toCellScheme.gradedIndex f = ((univ : Finset (Fin 4)), K) →
    k2Grade2.{u}.toCellScheme.gradedIndex u = ((univ : Finset (Fin 4)), k) → 2 ≤ k → k ≤ K →
    ∀ e, k2AttachmentBase.{u}.S.toCellScheme.grade e = k → ∃ v,
      k2Grade2.{u}.rowAt u (Fin.castAdd _ (k2LadPt v)) =
          k2Grade2.{u}.rowAt u (Fin.castAdd _ (Fin.castAdd _ e)) ∧
        min (k2Grade2.{u}.rowAt f (Fin.castAdd _ (k2LadPt v))) (k2Grade2.{u}.rowAt f u) =
          min (k2Grade2.{u}.rowAt f (Fin.castAdd _ (Fin.castAdd _ e)))
            (k2Grade2.{u}.rowAt f u) := by
  intro f u K k hf hu hk2 hkK e _
  obtain ⟨-, i, rfl⟩ := exists_natAdd_of_gradedIndex hf (hk2.trans hkK)
  obtain ⟨-, i', rfl⟩ := exists_natAdd_of_gradedIndex hu hk2
  obtain ⟨v, h1, h2⟩ :=
    k2ControllerRow_shadow (k2Cat2.equivFin.symm i).2 (k2Cat2.equivFin.symm i').2 e
  refine ⟨v, ?_, ?_⟩
  · rw [k2Grade2_rowAt_natAdd_castAdd, k2Grade2_rowAt_natAdd_castAdd]
    exact h1
  · rw [k2Grade2_rowAt_natAdd_castAdd, k2Grade2_rowAt_natAdd_castAdd,
      k2Grade2_rowAt_natAdd_natAdd]
    exact h2

/-- **The twin**, in the form of the hypothesis `htwinAbove` of
`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed` for the grade-two scheme: each controller
is its own twin, reading itself as `gridPoint 2 16`, which bounds every value of its row. -/
theorem k2Grade2_htwinAbove : ∀ (f : Fin k2Grade2.{u}.card) K k,
    k2Grade2.{u}.toCellScheme.gradedIndex f = ((univ : Finset (Fin 4)), K) →
    2 ≤ k → k ≤ K → ∀ e, k2AttachmentBase.{u}.S.toCellScheme.grade e = k →
      ∃ et, k2Grade2.{u}.toCellScheme.gradedIndex et = ((univ : Finset (Fin 4)), k) ∧
        k2Grade2.{u}.rowAt f (Fin.castAdd _ (Fin.castAdd _ e)) ≤ k2Grade2.{u}.rowAt f et := by
  intro f K k hf hk2 hkK e _
  obtain ⟨rfl, i, rfl⟩ := exists_natAdd_of_gradedIndex hf (hk2.trans hkK)
  obtain rfl : k = 2 := le_antisymm hkK hk2
  refine ⟨Fin.natAdd _ i, hf, ?_⟩
  rw [k2Grade2_rowAt_natAdd, k2Grade2_rowAt_natAdd, k2Phi_natAdd,
    agreementHeight_self (gridPoint_mem_grid le_rfl) (fun _ hx ↦ le_gridPoint_of_mem_grid hx)]
  exact le_gridPoint_of_mem_codeGrid (k2Phi_mem_codeGrid (k2Cat2.equivFin.symm i).2 _)

end VaughtConjecture.ProcessRank
