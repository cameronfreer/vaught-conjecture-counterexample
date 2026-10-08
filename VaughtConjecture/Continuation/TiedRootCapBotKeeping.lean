/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapSelective

/-!
# Bot-keeping labellings and completions

Roadmap, Layer 3 ((R3) of the table of 3.4).

A labelling `r` of a scheme is **bot-keeping** (`Scheme.BotKeeping`) when every cell of full scope
not labelled `⊥` reads every cell of proper scope labelled `⊥` as `⊥`.  A completion below the full
grade is bot-keeping (`CompletionBelowFullGrade.BotKeeping`) when its labelling is.

* **Field layers keep it** (`Scheme.exists_botKeeping_fieldLayer`, compiled in this repository
  (theorem named)): a bot-keeping lawful section extends, literally on the old cells, to a
  bot-keeping lawful section of the field layer (`Scheme.exists_isLawful_fieldLayer_bot`).  The
  old cells keep their rows (`Scheme.rowAt_appendFullCells_castAdd`).
* **The tower** (`Seed.exists_botKeeping_tower`, compiled): every scheme of the tower of field
  layers has a bot-keeping lawful section literal on the amalgam, by induction on the layers (the
  amalgam has no cell of full scope).
* **Completions** (`Seed.exists_botKeeping_of_towerInvariant`, compiled): under the lifting
  invariant at the top grade, the tower completion relabelled by that section is a bot-keeping
  completion; at the arities `m ≤ 2` with no hypothesis (`Seed.exists_botKeeping_of_le_two`).
* **The apex keeps it** (`CompletionBelowFullGrade.BotKeeping.rowAt_completion_eq_bot`, compiled):
  in the completion of a bot-keeping completion, every cell of full scope that is the apex or not
  labelled `⊥` reads every cell of proper scope labelled `⊥` as `⊥`.
* **A selective coface** (`BottomRootCounterexample.isSelectiveCoface_of_botKeeping`, compiled):
  the completion of a bot-keeping completion of `BottomRootCounterexample.seedFour` is a selective
  coface of the context with root cells labelled `⊥`.

The completion below the full grade at every arity (the profile tower) is not on this branch; its
bot-keeping is not compiled here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n}

/-- A labelling is **bot-keeping**: every cell of full scope not labelled `⊥` reads every cell of
proper scope labelled `⊥` as `⊥`. -/
def BotKeeping (S : Scheme.{u} n) (r : Fin S.card → Label.{u}) : Prop :=
  ∀ u y, S.toCellScheme.scope u = univ → r u ≠ ⊥ → S.toCellScheme.scope y ≠ univ → r y = ⊥ →
    S.rowAt u y = ⊥

/-- **The old cells keep their rows after appending cells of full scope.** -/
theorem rowAt_appendFullCells_castAdd {k M : ℕ} {r : Fin M → Fin (S.card + M) → Label.{u}}
    {h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d} (u x : Fin S.card) :
    (S.appendFullCells k M r h).rowAt (Fin.castAdd M u) (Fin.castAdd M x) = S.rowAt u x := by
  by_cases hx : x ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u)
  · have hx' : Fin.castAdd M x ∈ (S.appendFullCells k M r h).toCellScheme.below
        ((S.appendFullCells k M r h).toCellScheme.gradedIndex (Fin.castAdd M u)) := by
      rw [CellScheme.mem_below] at hx ⊢
      simpa using hx
    rw [rowAt_of_mem hx', rowAt_of_mem hx, appendFullCells_row_castAdd]
    rfl
  · have hx' : Fin.castAdd M x ∉ (S.appendFullCells k M r h).toCellScheme.below
        ((S.appendFullCells k M r h).toCellScheme.gradedIndex (Fin.castAdd M u)) := by
      rw [CellScheme.mem_below] at hx ⊢
      simpa using hx
    rw [rowAt_of_notMem hx', rowAt_of_notMem hx]

variable {k : ℕ} {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- **Field layers keep bot-keeping.**  A bot-keeping lawful section of `S` extends, literally on
the old cells, to a bot-keeping lawful section of the field layer at `k`. -/
theorem exists_botKeeping_fieldLayer {p : Fin S.card → Label.{u}} (hp : S.rows.IsLawful p)
    (hb : S.BotKeeping p) :
    ∃ r, (S.fieldLayer k hS).rows.IsLawful r ∧ (∀ d, r (Fin.castAdd _ d) = p d) ∧
      (S.fieldLayer k hS).BotKeeping r := by
  obtain ⟨r, hr, hrp, hrb⟩ := exists_isLawful_fieldLayer_bot (hS := hS) hp
  refine ⟨r, hr, hrp, fun u y hsu hu hsy hy ↦ ?_⟩
  change Fin (S.card + (S.catalogue k).card) at u y
  -- the cell `y` is old
  induction y using Fin.addCases with
  | right i' => exact absurd (appendFullCellsScheme_scope_natAdd S k _ i') hsy
  | left y' =>
  rw [hrp] at hy
  induction u using Fin.addCases with
  | left u' =>
    rw [hrp] at hu
    refine (rowAt_appendFullCells_castAdd u' y').trans (hb u' y' ?_ hu ?_ hy)
    · exact (appendFullCellsScheme_scope_castAdd S k _ u').symm.trans hsu
    · exact fun h ↦ hsy ((appendFullCellsScheme_scope_castAdd S k _ y').trans h)
  | right i =>
    by_cases hm : (Fin.castAdd _ y' : Fin (S.card + (S.catalogue k).card)) ∈
        (S.fieldLayer k hS).toCellScheme.below
          ((S.fieldLayer k hS).toCellScheme.gradedIndex (Fin.natAdd _ i))
    · rw [rowAt_of_mem hm, fieldLayer_row_natAdd, fieldRow_castAdd]
      refine hrb i hu y' ?_ hy
      have h := hm
      rw [CellScheme.mem_below] at h
      have hg : (S.fieldLayer k hS).toCellScheme.grade (Fin.castAdd _ y') ≤ k :=
        (Prod.le_def.mp (h.trans_eq (appendFullCellsScheme_gradedIndex_natAdd S k _ i))).2
      exact (appendFullCellsScheme_grade_castAdd S k _ y').symm.trans_le hg
    · exact rowAt_of_notMem hm

end Scheme

/-! ### The tower and its completion -/

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- **Every scheme of the tower has a bot-keeping lawful section literal on the amalgam.** -/
theorem exists_botKeeping_tower : (j : ℕ) →
    ∃ r, (I.tower j).rows.IsLawful r ∧ (∀ d, r (I.towerEmbed j d) = I.amalgam.label d) ∧
      (I.tower j).BotKeeping r
  | 0 => ⟨I.amalgam.label, I.amalgam.isLawful, fun _ ↦ rfl, fun u _ hsu ↦ by
      rcases I.tower_grade_le_or 0 u with h | h
      · have := I.amalgam.isWellFormed.isWellFormed.grade_pos u
        exact absurd h (by change ¬ I.amalgam.toCellScheme.grade u ≤ 0; omega)
      · exact absurd hsu h⟩
  | j + 1 => by
    obtain ⟨r, hr, hre, hrb⟩ := exists_botKeeping_tower j
    obtain ⟨r', hr', hr'r, hr'b⟩ := Scheme.exists_botKeeping_fieldLayer
      (S := I.tower j) (k := j + 1) (hS := I.not_univ_succ_le_tower j) hr hrb
    exact ⟨r', hr', fun d ↦ (hr'r _).trans (hre d), hr'b⟩

end Seed

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- A completion below the full grade is **bot-keeping** when its labelling is. -/
def BotKeeping (F : CompletionBelowFullGrade I) : Prop := F.scheme.BotKeeping F.label

/-- Stage reduction sends exactly `⊥` to `⊥`. -/
private theorem reduce_eq_bot_iff {x : Label.{u}} : Label.reduce α x = ⊥ ↔ x = ⊥ := by
  by_cases hx : x < α
  · rw [reduce_of_lt hx]
  · rw [reduce_of_le (not_lt.mp hx)]
    refine ⟨fun h ↦ absurd h top_ne_bot, fun h ↦ ?_⟩
    subst h
    exact absurd (WithBot.bot_lt_coe _) hx

/-- **The apex keeps it**: in the completion of a bot-keeping completion, every cell of full scope
that is the apex or not labelled `⊥` reads every cell of proper scope labelled `⊥` as `⊥`. -/
theorem BotKeeping.rowAt_completion_eq_bot {F : CompletionBelowFullGrade I} (hF : F.BotKeeping)
    (hα : Order.IsSuccPrelimit α) (u y : Fin (F.completion hα).card)
    (hsu : (F.completion hα).toCellScheme.scope u = univ)
    (hu : (F.completion hα).toCellScheme.grade u = m + 2 ∨ (F.completion hα).label u ≠ ⊥)
    (hys : (F.completion hα).toCellScheme.scope y ≠ univ)
    (hyb : (F.completion hα).label y = ⊥) : (F.completion hα).rowAt u y = ⊥ := by
  have hyl : y ≠ Fin.last _ := fun h ↦ hys (by
    rw [h]
    exact StageType.addApex_scope_last (t := F.truncate hα) F.isLegalBelowFullGrade
      (Nat.succ_pos _))
  obtain ⟨y', rfl⟩ : ∃ y' : Fin (F.truncate hα).card, y = y'.castSucc :=
    ⟨y.castPred hyl, (Fin.castSucc_castPred _ _).symm⟩
  change Fin ((F.truncate hα).card + 1) at u
  induction u using Fin.lastCases with
  | last =>
    exact (StageType.rowAt_addApex_last_eq_bot_iff F.isLegalBelowFullGrade (Nat.succ_pos _)
      _).mpr hyb
  | cast d =>
  refine (Scheme.rowAt_appendFullCell_castSucc (h := F.isLegalBelowFullGrade.not_le) d
    y').trans ?_
  have hlab (x : Fin (F.truncate hα).card) :
      (F.completion hα).label x.castSucc = Label.reduce α (F.label x) :=
    StageType.addApex_label_castSucc (t := F.truncate hα) F.isLegalBelowFullGrade _ x
  refine hF d y' ((Scheme.appendFullCellScheme_scope_castSucc _ _ d).symm.trans hsu) ?_
    (fun h ↦ hys ((Scheme.appendFullCellScheme_scope_castSucc _ _ y').trans h))
    ((reduce_eq_bot_iff (α := α)).mp ((hlab y').symm.trans hyb))
  rcases hu with h4 | hne
  · have h4' : F.scheme.toCellScheme.grade d = m + 2 :=
      (Scheme.appendFullCellScheme_grade_castSucc _ _ d).symm.trans h4
    exact absurd h4' (F.isLegalBelowFullGrade.grade_lt d).ne
  · exact fun hL0 ↦ hne ((hlab d).trans ((reduce_eq_bot_iff (α := α)).mpr hL0))

end CompletionBelowFullGrade

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- **A bot-keeping completion under the lifting invariant at the top grade**: the tower completion
relabelled by a bot-keeping section of the tower (`Seed.exists_botKeeping_tower`). -/
theorem exists_botKeeping_of_towerInvariant (hinv : I.TowerInvariant (m + 1)) :
    ∃ F : CompletionBelowFullGrade I, F.BotKeeping := by
  obtain ⟨L, hL, hLe, hLb⟩ := I.exists_botKeeping_tower (m + 1)
  exact ⟨{ I.completionBelowFullGradeOfTowerInvariant hinv with
    label := L, isLawful := hL, label_embed := hLe }, hLb⟩

/-- **A bot-keeping completion at the arities `m ≤ 2`**, with no hypothesis. -/
theorem exists_botKeeping_of_le_two (hm : m ≤ 2) :
    ∃ F : CompletionBelowFullGrade I, F.BotKeeping :=
  I.exists_botKeeping_of_towerInvariant (I.towerInvariant_of_le_two hm (m + 1) le_rfl)

end Seed

/-! ### The selective coface from a bot-keeping completion -/

namespace BottomRootCounterexample

open StageType
open TiedRootCapCounterexample (rootEmb)

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- **A bot-keeping completion of `seedFour` gives a selective coface** of the context with root
cells labelled `⊥`. -/
theorem isSelectiveCoface_of_botKeeping {F : CompletionBelowFullGrade (seedFour hα)}
    (hF : F.BotKeeping) : IsSelectiveCoface hα (F.completion hα.isSuccPrelimit) := by
  have hα' := hα.isSuccPrelimit
  have hq₁ : restrictFace Fin.castSuccEmb (F.completion hα') = some (context hα) :=
    F.restrictFace_left_completion hα'
  refine ⟨⟨F.isLegal_completion hα', hq₁⟩, fun u hsu _ hu y hy ↦ ?_⟩
  have hroot : restrictFace (rootEmb.trans Fin.castSuccEmb) (F.completion hα') = some root := by
    rw [← restrictFace_trans _ _ _ hq₁]
    exact restrictFace_context hα
  obtain ⟨z, rfl⟩ := exists_faceCell_eq hroot hy
  refine hF.rowAt_completion_eq_bot hα' u _ hsu hu ?_ ((label_faceCell hroot z).trans rfl)
  rw [scope_faceCell]
  intro h
  have h1 := congrArg Finset.card h
  rw [card_map, card_univ, Fintype.card_fin] at h1
  have h2 := card_le_univ ((root (α := α)).toCellScheme.scope z)
  rw [Fintype.card_fin] at h2
  omega

end BottomRootCounterexample

end VaughtConjecture
