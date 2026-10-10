/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedLift

/-!
# The lift from a mixed face into the full face

Roadmap, Layer 3 ((R3) and (R4), the mixed-coatom lift of the replicated carrier).

**The bottom pattern of a decoded controller row** (`Seed.decode_controller_dichotomy`).  Let `P`
be lawful below `(U, j)`, `U` mixed, and `θ` a capped decoder of `P` at the copy at `U` of a
controller `u` at a grade `K ≥ 2` with state `R`.  The controller reads every cell of the attachment
of grade at most `K` as `R`, and `R e` is the positive table of `R` at the rank of `e`, the reading
of a rung of the rank member of `R`.  The copied ladder at `U` has the shape of the table of one
member (`Seed.copyLadder_exists_shape`): the copied rungs of the rank member of `R` are all positive
or all `⊥`.  So `θ` either sends every reading of a cell of the attachment to `⊥`, or sends exactly
the readings `⊥` to `⊥`.

**Scope.**  Part of the earlier route (the replicated scheme over the height-set tower, or the
ladder tower of the amalgam), whose open inputs the levels re-rendered per grade replace; not used
by the main theorem through the levels (`VaughtConjecture.MainTheorem.GrowthLevelRoute`), and kept
as reusable constructions.

## References

Bountifulness is [Kni26, Definition 2.5.14]; witnesses are [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}
  {U : Finset (Fin (m + 2))}

/-- The replicated scheme. -/
local notation "𝔼" => Seed.replicated I g H Γ A B'

/-- The ladder tower over the attachment. -/
local notation "𝕋" => Seed.attachTower I g H Γ A B'

/-- **The bottom pattern of a decoded controller row**: a capped decoder at the copy of a
controller of grade `K ≥ 2` sends all its readings of the cells of the attachment of grade at most
`K` to `⊥`, or exactly the readings `⊥`. -/
theorem decode_controller_dichotomy (hU : U ∈ I.mixedFaces g) (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) {j : ℕ} {P : Fin (𝔼).card → Label.{u}}
    (hP : (𝔼).rows.IsLawfulBelow (U, j) fun d ↦ P d) (hj1 : 1 ≤ j) {K : ℕ} (hK2 : 2 ≤ K)
    (hKm : K ≤ m + 1) (hKU : K ≤ #U) {u : Fin (𝕋).card}
    (hu : (𝕋).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), K))
    {θ : Label.{u} → Label.{u}} (hθ_bot : θ ⊥ = ⊥)
    (hθ : ∀ d ∈ (𝔼).toCellScheme.below
        ((𝔼).toCellScheme.gradedIndex (copyFull H Γ A B' hU u hu hKU)),
      θ ((𝔼).rowAt (copyFull H Γ A B' hU u hu hKU) d) =
        min (P d) (P (copyFull H Γ A B' hU u hu hKU))) :
    (∀ e : Fin (I.attachment g).card, (I.attachment g).toCellScheme.grade e ≤ K →
        θ ((𝕋).rowAt u ((I.attachmentBase g).baseCellEmb m e)) = ⊥) ∨
      ∀ e : Fin (I.attachment g).card, (I.attachment g).toCellScheme.grade e ≤ K →
        (θ ((𝕋).rowAt u ((I.attachmentBase g).baseCellEmb m e)) = ⊥ ↔
          (𝕋).rowAt u ((I.attachmentBase g).baseCellEmb m e) = ⊥) := by
  have hu' : (𝕋).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), K - 2 + 2) := by
    rw [show K - 2 + 2 = K by omega]; exact hu
  obtain ⟨R, -, hR, hrowA, hrowL⟩ :=
    Scheme.LadderBaseData.exists_controller_ladderTower (B := I.attachmentBase g) (A := A)
      (Γ := Γ) (B' := B') hcard (K - 2) m (by omega) u hu'
  set b := Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR with hb
  have hU1 : 1 ≤ #U := (by omega : 1 ≤ K).trans hKU
  -- the reading of a cell is the reading of a rung of `b`
  have hrung (e : Fin (I.attachment g).card) (he : (I.attachment g).toCellScheme.grade e ≤ K)
      (hRe : R e ≠ ⊥) :
      ∃ (i : ℕ) (hi : i < H), θ ((𝕋).rowAt u ((I.attachmentBase g).baseCellEmb m e)) =
        min (P (copyLadder H Γ A B' hU (b, Sum.inl ⟨i, hi⟩)))
          (P (copyFull H Γ A B' hU u hu hKU)) := by
    have hr0 : rankVector R e ≠ 0 := fun h ↦ hRe ((rankVector_eq_zero_iff e).mp h)
    have hrH : rankVector R e ≤ H := (rankVector_le e).trans (by rw [Fintype.card_fin]; exact hcard)
    have hi : rankVector R e - 1 < H := by omega
    refine ⟨rankVector R e - 1, hi, ?_⟩
    have hpt := Scheme.baseIndex_self (Scheme.rankProf_le (I.attachmentBase g).S H)
      ((b, Sum.inl ⟨rankVector R e - 1, hi⟩) :
        Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H)
    have hre : (𝕋).rowAt u ((I.attachmentBase g).baseCellEmb m e) =
        (𝕋).rowAt u (ladCell H Γ A B' (b, Sum.inl ⟨rankVector R e - 1, hi⟩)) := by
      refine (hrowA e (show (I.attachment g).toCellScheme.grade e ≤ K - 2 + 2 by omega)).trans
        (Eq.trans ?_ (hrowL _).symm)
      rw [hpt]
      change R e = posTable R (rankVector R e - 1 + 1)
      rw [show rankVector R e - 1 + 1 = rankVector R e by omega]
      exact (posTable_rankVector ((I.attachmentBase g).isSelfVisible_one_of_isLawful hR) e).symm
    rw [hre, decode_copyFull hU hu hKU hθ (gradedIndex_ladCell _) (by omega)]
    rfl
  have hR' (e : Fin (I.attachment g).card) (he : (I.attachment g).toCellScheme.grade e ≤ K) :
      (𝕋).rowAt u ((I.attachmentBase g).baseCellEmb m e) = R e :=
    hrowA e (show (I.attachment g).toCellScheme.grade e ≤ K - 2 + 2 by omega)
  -- the shape of the copied ladder
  rcases copyLadder_exists_shape hH hU hP (show (U, 1) ≤ (U, j) from ⟨subset_rfl, hj1⟩) with
    hall | ⟨a, gg, σ, hwit, hch, hbot⟩
  · left
    intro e he
    by_cases hRe : R e = ⊥
    · rw [hR' e he, hRe, hθ_bot]
    · obtain ⟨i, hi, hθe⟩ := hrung e he hRe
      rw [hθe, hall, min_eq_left bot_le]
  · by_cases hκ : rankCut H (Scheme.rankProf (I.attachmentBase g).S H a)
        (Scheme.rankProf (I.attachmentBase g).S H b) = 0 ∨
        P (copyFull H Γ A B' hU u hu hKU) = ⊥
    · left
      intro e he
      by_cases hRe : R e = ⊥
      · rw [hR' e he, hRe, hθ_bot]
      · obtain ⟨i, hi, hθe⟩ := hrung e he hRe
        rw [hθe]
        rcases hκ with h0 | h0
        · have hzero : ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
              (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) a
                (b, Sum.inl ⟨i, hi⟩) = 0 := by
            change min (rankCut H (Scheme.rankProf (I.attachmentBase g).S H a)
              (Scheme.rankProf (I.attachmentBase g).S H b)) (i + 1) = 0
            rw [h0]
            exact Nat.zero_min _
          rw [(hbot _).mpr hzero, min_eq_left bot_le]
        · rw [h0, min_eq_right bot_le]
    · right
      push Not at hκ
      intro e he
      refine ⟨fun h0 ↦ ?_, fun h0 ↦ by rw [h0, hθ_bot]⟩
      rw [hR' e he]
      by_contra hRe
      obtain ⟨i, hi, hθe⟩ := hrung e he hRe
      rw [hθe] at h0
      rcases min_eq_bot.mp h0 with h | h
      · have hpos : ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
            (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) a
              (b, Sum.inl ⟨i, hi⟩) ≠ 0 := by
          change min (rankCut H (Scheme.rankProf (I.attachmentBase g).S H a)
            (Scheme.rankProf (I.attachmentBase g).S H b)) (i + 1) ≠ 0
          have := hκ.1
          omega
        exact hpos ((hbot _).mp h)
      · exact hκ.2 h

/-- **The cells of the replicated scheme**: a cell has an original of full scope at its grade (a
cell of full scope of the tower or a copy), or is a cell of the attachment. -/
theorem cell_cases (z : Fin (𝔼).card) :
    (∃ v, (𝕋).mirrorOrig (I.mixedFaces g) z = v ∧
        (𝕋).toCellScheme.gradedIndex v =
          ((univ : Finset (Fin (m + 2))), (𝔼).toCellScheme.grade z)) ∨
      ∃ e, z = I.attachEmb g H Γ A B' e := by
  induction z using Fin.addCases with
  | left x =>
    by_cases hx : (𝕋).toCellScheme.scope x = univ
    · left
      refine ⟨x, Scheme.mirrorOrig_castAdd _ _ x, Prod.ext hx ?_⟩
      exact (congrArg Prod.snd (Scheme.gradedIndex_mirror_castAdd
        (hmix := I.not_subset_scope_tower g H Γ A B') x)).symm
    · right
      obtain ⟨e, rfl⟩ := (I.attachmentBase g).mem_range_baseCellEmb m x hx
      exact ⟨e, rfl⟩
  | right j =>
    left
    refine ⟨_, rfl, Prod.ext ?_ rfl⟩
    rw [Scheme.mirrorOrig_natAdd]
    exact (((𝕋).copyEquiv (I.mixedFaces g)).symm j).2.2.1

/-- **The bottom pattern of the decoded top rung**: a capped decoder at the copy of the top rung
of a member `a` whose copy dominates the copied ladder sends all readings of the cells of the
attachment of grade one by the original top rung to `⊥`, or exactly the readings `⊥`. -/
theorem decode_one_dichotomy (hU : U ∈ I.mixedFaces g) (hH : 0 < H) {j : ℕ}
    {P : Fin (𝔼).card → Label.{u}} (hP : (𝔼).rows.IsLawfulBelow (U, j) fun d ↦ P d)
    (hj1 : 1 ≤ j) (hU1 : 1 ≤ #U) (a : Scheme.RankMember (I.attachmentBase g).S H)
    (hmax : ∀ v, P (copyLadder H Γ A B' hU v) ≤
      P (copyLadder H Γ A B' hU (a, Sum.inl ⟨H - 1, by omega⟩)))
    {θ : Label.{u} → Label.{u}}
    (hθ : ∀ d ∈ (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex
        (copyFull H Γ A B' hU (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
          (gradedIndex_ladCell _) hU1)),
      θ ((𝔼).rowAt (copyFull H Γ A B' hU (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
          (gradedIndex_ladCell _) hU1) d) =
        min (P d) (P (copyFull H Γ A B' hU (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
          (gradedIndex_ladCell _) hU1))) :
    (∀ e : Fin (I.attachment g).card, (I.attachment g).toCellScheme.grade e = 1 →
        θ ((𝕋).rowAt (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
          ((I.attachmentBase g).baseCellEmb m e)) = ⊥) ∨
      ∀ e : Fin (I.attachment g).card, (I.attachment g).toCellScheme.grade e = 1 →
        (θ ((𝕋).rowAt (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
          ((I.attachmentBase g).baseCellEmb m e)) = ⊥ ↔
        (𝕋).rowAt (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
          ((I.attachmentBase g).baseCellEmb m e) = ⊥) := by
  set top : Scheme.LadderPt (I.attachmentBase g).S
    (Scheme.RankMember (I.attachmentBase g).S H) H := (a, Sum.inl ⟨H - 1, by omega⟩) with htop
  -- the reading of `e` is the reading of the shadow of `e` for `a`
  have hread (e : Fin (I.attachment g).card) (he : (I.attachment g).toCellScheme.grade e = 1) :
      θ ((𝕋).rowAt (ladCell H Γ A B' top) ((I.attachmentBase g).baseCellEmb m e)) =
        P (copyLadder H Γ A B' hU (a, Sum.inr e)) ∧
      (𝕋).rowAt (ladCell H Γ A B' top) ((I.attachmentBase g).baseCellEmb m e) =
        ladderSource H (Scheme.rankProf (I.attachmentBase g).S H a e) := by
    rw [rowAt_ladCell_baseCellEmb top he]
    refine ⟨?_, ?_⟩
    · rw [decode_copyFull hU (gradedIndex_ladCell top) hU1 hθ (gradedIndex_ladCell _) le_rfl]
      exact min_eq_left (hmax _)
    · rw [rowAt_ladCell_ladCell, Scheme.baseIndex_natAdd, Equiv.symm_apply_apply]
      have h := ladderIndex_parent (H := H) (prof := Scheme.rankProf (I.attachmentBase g).S H)
        (parent := Prod.fst) (Scheme.ladderCeil_le (Scheme.rankProf_le _ H))
        ((a, Sum.inr e) : Scheme.LadderPt (I.attachmentBase g).S
          (Scheme.RankMember (I.attachmentBase g).S H) H)
      rw [h]
      change ladderSource (H - 1 + 1) (Scheme.rankProf (I.attachmentBase g).S H a e) = _
      rw [show H - 1 + 1 = H by omega]
  rcases copyLadder_exists_shape hH hU hP (show (U, 1) ≤ (U, j) from ⟨subset_rfl, hj1⟩) with
    hall | ⟨b, gg, σ, hwit, hch, hbot⟩
  · left
    intro e he
    rw [(hread e he).1, hall]
  · by_cases htop0 : P (copyLadder H Γ A B' hU top) = ⊥
    · left
      intro e he
      rw [(hread e he).1]
      exact le_bot_iff.mp (htop0 ▸ hmax _)
    · right
      have hcut : rankCut H (Scheme.rankProf (I.attachmentBase g).S H b)
          (Scheme.rankProf (I.attachmentBase g).S H a) ≠ 0 := by
        intro h0
        apply htop0
        rw [hbot]
        change min (rankCut H (Scheme.rankProf (I.attachmentBase g).S H b)
          (Scheme.rankProf (I.attachmentBase g).S H a)) (H - 1 + 1) = 0
        rw [h0]
        exact Nat.zero_min _
      intro e he
      rw [(hread e he).1, (hread e he).2, hbot, ladderSource_eq_bot_iff]
      change min (rankCut H (Scheme.rankProf (I.attachmentBase g).S H b)
        (Scheme.rankProf (I.attachmentBase g).S H a))
        (Scheme.rankProf (I.attachmentBase g).S H a e) = 0 ↔ _
      constructor
      · intro h
        rcases Nat.min_eq_zero_iff.mp h with h' | h'
        · exact absurd h' hcut
        · rw [h']; exact Nat.zero_min _
      · intro h
        rcases Nat.min_eq_zero_iff.mp h with h' | h'
        · rw [h']; exact Nat.min_zero _
        · omega

end Seed

end VaughtConjecture
