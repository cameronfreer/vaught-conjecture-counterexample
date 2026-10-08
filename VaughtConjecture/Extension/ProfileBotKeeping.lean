/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.BotKeeping
import VaughtConjecture.Extension.ProfileTowerCompletion

/-!
# Level bot-keeping of the profile tower

Roadmap, Layer 3, 3.1, (R6) (the completion below the full grade at every arity).

Every seed has a bot-keeping completion below the full grade
(`CompletionBelowFullGrade.BotKeeping`), through the profile tower.  Compiled in this repository
(theorem named):

* **The tower section keeps the bottoms** (`Seed.towerSection_rowAt_eq_bot`): at a cell of full
  scope of `T j` where the tower section of `w` is not `⊥`, the row reads every old cell where `w`
  is `⊥` as `⊥`.  The decoded layer is the upper decoder (which sends `⊥` to `⊥`,
  `Label.upperDecoderAt_bot`) at the agreement height of the orbit code of the splice with the
  catalogue entry, `⊥` when the two differ in their bottoms
  (`Label.eq_bot_of_agreementHeight_ne_bot`); the row of the new cell at an old cell is the entry.
* **Section bot-keeping of the levels** (`ProfileTower.Lvl.SectionBotKeeping`,
  `ProfileTower.base_sectionBotKeeping`, `ProfileTower.Lvl.Good.sectionBotKeeping_next`,
  `ProfileTower.lvl_sectionBotKeeping`): for every profile `P`, at a cell of full scope where the
  section of `P` is not `⊥`, the row reads every old cell where `P` is `⊥` as `⊥`.  At the next
  level the section at an old cell of the level is the upper decoder of the section of the code
  of `P` (whose bottoms contain those of `P`, `ProfileTower.code_eq_bot`), and at a new cell the
  upper decoder of an agreement height; the row of a new cell at an old cell is its profile (the
  section is literal at the old cells).
* **Level bot-keeping** (`ProfileTower.Lvl.Good.exists_botKeeping`): a good level at the grade
  `m` with section bot-keeping has a lawful section literal on the amalgam that is bot-keeping:
  the section of the amalgam labelling at the cells of grade at most `m`, and the amalgam labels at
  the old cells of the grade `m + 1`, glued over the two coatoms at the grade `m + 1` and
  `(univ, m)` (`CellScheme.Rows.IsLawfulBelow.glue₃`).
* **Every seed has a bot-keeping completion** (`Seed.exists_botKeeping`): at `m ≤ 2` the tower
  (`Seed.exists_botKeeping_of_le_two`), at `m ≥ 3` the completion over the good level
  (`ProfileTower.exists_botKeeping_of_three_le`, through
  `CompletionBelowFullGrade.exists_botKeeping_of_eq_fieldLayer`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### The tower section keeps the bottoms -/

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (B : ℕ)

/-- **The tower section keeps the bottoms**: at a cell of full scope of `T j` where the tower
section of `w` is not `⊥`, the row reads every old cell where `w` is `⊥` as `⊥`. -/
theorem towerSection_rowAt_eq_bot : ∀ (j : ℕ) (w : Fin I.amalgam.card → Label.{u})
    (u : Fin (I.tower j).card) (d : Fin I.amalgam.card),
    (I.tower j).toCellScheme.scope u = univ → I.towerSection B j w u ≠ ⊥ → w d = ⊥ →
      (I.tower j).rowAt u (I.towerEmbed j d) = ⊥
  | 0, _, u, _, hsu, _, _ => absurd hsu (I.scope_ne_univ u)
  | j + 1, w, u, d, hsu, hu, hd => by
    change Fin ((I.tower j).card + ((I.tower j).catalogue (j + 1)).card) at u
    rw [towerEmbed_succ]
    induction u using Fin.addCases with
    | left u' =>
      rw [towerSection_castAdd] at hu
      have hsu' : (I.tower j).toCellScheme.scope u' = univ :=
        (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ u').symm.trans hsu
      change ((I.tower j).fieldLayer (j + 1) (I.not_univ_succ_le_tower j)).rowAt
        (Fin.castAdd _ u') (Fin.castAdd _ (I.towerEmbed j d)) = ⊥
      exact (Scheme.rowAt_appendFullCells_castAdd u' _).trans
        (towerSection_rowAt_eq_bot j w u' d hsu' hu hd)
    | right i =>
      rw [towerSection_natAdd] at hu
      have hah : agreementHeight ((I.tower j).fieldGrid (j + 1))
          (orbitCode (j + 1) (I.layerSplice j (I.towerSection B j w)))
          ((I.tower j).catalogueEntry (j + 1) i) ≠ ⊥ := fun h ↦ hu (by
        unfold layerSection
        rw [h]
        exact upperDecoderAt_bot)
      change ((I.tower j).fieldLayer (j + 1) (I.not_univ_succ_le_tower j)).rowAt
        (Fin.natAdd _ i) (Fin.castAdd _ (I.towerEmbed j d)) = ⊥
      by_cases hm : (Fin.castAdd _ (I.towerEmbed j d) :
          Fin ((I.tower j).card + ((I.tower j).catalogue (j + 1)).card)) ∈
          ((I.tower j).fieldLayer (j + 1) (I.not_univ_succ_le_tower j)).toCellScheme.below
            (((I.tower j).fieldLayer (j + 1) (I.not_univ_succ_le_tower j)).toCellScheme.gradedIndex
              (Fin.natAdd _ i))
      · rw [Scheme.rowAt_of_mem hm, Scheme.fieldLayer_row_natAdd, Scheme.fieldRow_castAdd]
        refine Label.eq_bot_of_agreementHeight_ne_bot (bot_mem_grid _ _) hah ?_
        rw [orbitCode_eq_bot_iff]
        change CellScheme.splice _ (j + 1) (fun _ ↦ ⊥) (I.towerSection B j w)
          (I.towerEmbed j d) = ⊥
        unfold CellScheme.splice
        split_ifs
        · rw [towerSection_towerEmbed]
          exact hd
        · rfl
      · exact Scheme.rowAt_of_notMem hm

end Seed

/-! ### Section bot-keeping of the levels -/

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **Section bot-keeping** of a level: for every profile `P`, at a cell of full scope where the
section of `P` is not `⊥`, the row reads every old cell where `P` is `⊥` as `⊥`. -/
def Lvl.SectionBotKeeping {g : ℕ} (L : Lvl I g) : Prop :=
  ∀ (P : Prof I) (u : Fin L.S.card) (d : Fin I.amalgam.card), L.S.toCellScheme.scope u = univ →
    L.σ P u ≠ ⊥ → P d = ⊥ → L.S.rowAt u (L.embed d) = ⊥

variable (I) in
/-- The base level has section bot-keeping (`Seed.towerSection_rowAt_eq_bot`). -/
theorem base_sectionBotKeeping : (base I).SectionBotKeeping :=
  fun P u d hsu hu hd ↦ I.towerSection_rowAt_eq_bot (bound I) 2 P u d hsu hu hd

/-- The code of a profile has the bottoms of the profile. -/
theorem code_eq_bot {k : ℕ} {P : Prof I} {d : Fin I.amalgam.card} (hd : P d = ⊥) :
    code k P d = ⊥ := by
  rw [orbitCode_eq_bot_iff]
  unfold hat CellScheme.splice
  split_ifs
  · exact hd
  · rfl

/-- **The next level of a good level keeps section bot-keeping.** -/
theorem Lvl.Good.sectionBotKeeping_next {g : ℕ} {L : Lvl I g} (hL : L.Good)
    (hS : L.SectionBotKeeping) : L.next.SectionBotKeeping := by
  intro P u d hsu hu hd
  change Fin (L.S.card + (cat I (g + 1)).card) at u
  rw [Lvl.next_embed_apply]
  change L.nextS.rowAt u (Fin.castAdd _ (L.embed d)) = ⊥
  induction u using Fin.addCases with
  | left u' =>
    have hsu' : L.S.toCellScheme.scope u' = univ :=
      (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ u').symm.trans hsu
    have hg : L.S.toCellScheme.grade u' ≤ g := (L.inv u').resolve_right (not_not.mpr hsu')
    have hu' : L.σ (code (g + 1) P) u' ≠ ⊥ := by
      intro h
      apply hu
      change L.nextσ P (Fin.castAdd _ u') = ⊥
      have hg' : (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).grade
          (Fin.castAdd _ u') ≤ g + 1 := by
        rw [Scheme.appendFullCellsScheme_grade_castAdd]
        omega
      unfold Lvl.nextσ
      rw [ite_eq_left hg']
      unfold Lvl.Φ
      rw [Fin.append_left, h, upperDecoderAt_bot]
    exact (Scheme.rowAt_appendFullCells_castAdd u' _).trans
      (hS _ u' d hsu' hu' (code_eq_bot hd))
  | right i =>
    have hah : agreementHeight (grid (g + 1) (bound I)) (code (g + 1) P) (entry I (g + 1) i)
        ≠ ⊥ := by
      intro h
      apply hu
      change L.nextσ P (Fin.natAdd _ i) = ⊥
      have hg' : (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).grade
          (Fin.natAdd _ i) ≤ g + 1 := by
        rw [Scheme.appendFullCellsScheme_grade_natAdd]
      unfold Lvl.nextσ
      rw [ite_eq_left hg']
      unfold Lvl.Φ
      rw [Fin.append_right, h, upperDecoderAt_bot]
    have hentry : entry I (g + 1) i d = ⊥ :=
      Label.eq_bot_of_agreementHeight_ne_bot (bot_mem_grid _ _) hah (code_eq_bot hd)
    by_cases hm : (Fin.castAdd _ (L.embed d) : Fin (L.S.card + (cat I (g + 1)).card)) ∈
        L.nextS.toCellScheme.below (L.nextS.toCellScheme.gradedIndex (Fin.natAdd _ i))
    · rw [Scheme.rowAt_of_mem hm, Scheme.appendFullCells_row_natAdd]
      unfold Lvl.Φ
      rw [Fin.append_left, hL.literal]
      exact hentry
    · exact Scheme.rowAt_of_notMem hm

variable (I) in
/-- **Every good level up to the grade `m` has section bot-keeping.** -/
theorem lvl_sectionBotKeeping (hm : 2 ≤ m) : (j : ℕ) → j + 2 ≤ m → (lvl I j).SectionBotKeeping
  | 0, _ => base_sectionBotKeeping I
  | j + 1, hj => (lvl_good hm j (by omega)).sectionBotKeeping_next
      (lvl_sectionBotKeeping hm j (by omega))

/-! ### Level bot-keeping -/

/-- **Level bot-keeping**: a good level at the grade `m` with section bot-keeping has a lawful
section, literal on the amalgam, that is bot-keeping: the section of the amalgam labelling at the
cells of grade at most `m`, the amalgam labels at the old cells of the grade `m + 1`. -/
theorem Lvl.Good.exists_botKeeping {N : Lvl I m} (hN : N.Good) (hS : N.SectionBotKeeping) :
    ∃ p : Fin N.S.card → Label.{u}, N.S.rows.IsLawful p ∧
      (∀ d, p (N.embed d) = I.amalgam.label d) ∧ N.S.BotKeeping p := by
  classical
  set P₀ : Prof I := I.amalgam.label
  set p : Fin N.S.card → Label.{u} := fun z ↦
    if N.S.toCellScheme.grade z ≤ m then N.σ P₀ z
    else Function.extend N.embed I.amalgam.label (fun _ ↦ ⊥) z with hp_def
  have hpe (d : Fin I.amalgam.card) : p (N.embed d) = I.amalgam.label d := by
    by_cases hg : N.S.toCellScheme.grade (N.embed d) ≤ m
    · rw [hp_def]
      simp only [hg, ite_true]
      exact hN.literal P₀ d
    · rw [hp_def]
      simp only [hg, ite_false]
      exact N.embed.injective.extend_apply _ _ d
  have hcut : IsCutLawful I m P₀ :=
    ⟨I.amalgam.isLawful.isLawfulBelow _, I.amalgam.isLawful.isLawfulBelow _⟩
  have hold (z : Fin (m + 2)) :
      N.S.rows.IsLawfulBelow (univ.erase z, m + 1) fun e ↦ p e := by
    refine (hN.isLawfulBelow_old_iff (w := p) (Seed.ne_univ_erase z)).mpr ?_
    exact (CellScheme.Rows.isLawfulBelow_congr (R := I.amalgam.rows) (X := (univ.erase z, m + 1))
      (w := I.amalgam.label) (w' := fun d ↦ p (N.embed d)) fun d _ ↦ (hpe d).symm).mp
      (I.amalgam.isLawful.isLawfulBelow _)
  have hlow : N.S.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), m) fun e ↦ p e := by
    refine (CellScheme.Rows.isLawfulBelow_congr (R := N.S.rows)
      (X := ((univ : Finset (Fin (m + 2))), m)) (w := fun z ↦ N.σ P₀ z) (w' := p)
      fun z hz ↦ ?_).mp (hN.lawful P₀ hcut)
    have hz' : N.S.toCellScheme.grade z ≤ m := hz.2
    rw [hp_def]
    simp only [hz', ite_true]
  have hglue : N.S.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), m + 1) fun e ↦ p e :=
    CellScheme.Rows.IsLawfulBelow.glue₃ (U := (univ.erase (Fin.last (m + 1)), m + 1))
      (V := ((univ : Finset (Fin (m + 2))), m))
      (W := (univ.erase (Fin.castSucc (Fin.last m)), m + 1)) (hold _) hlow (hold _)
      (hN.mem_below_cover (by simp) (by simp) Seed.last_ne_castSucc)
  have hall (z : Fin N.S.card) :
      z ∈ N.S.toCellScheme.below ((univ : Finset (Fin (m + 2))), m + 1) :=
    ⟨subset_univ _, by
      have := hN.grade_lt z
      change N.S.toCellScheme.grade z ≤ m + 1
      omega⟩
  refine ⟨p, hglue.isLawful hall, hpe, fun u y hsu hu hsy hy ↦ ?_⟩
  have hg : N.S.toCellScheme.grade u ≤ m := (N.inv u).resolve_right (not_not.mpr hsu)
  have hu' : N.σ P₀ u ≠ ⊥ := by
    rw [hp_def] at hu
    simpa only [hg, ite_true] using hu
  obtain ⟨d, rfl⟩ := hN.mem_range y hsy
  rw [hpe] at hy
  exact hS P₀ u d hsu hu' hy

/-- **Every seed on `m + 2 ≥ 5` points has a bot-keeping completion below the full grade**: the
completion over the good level at the grade `m` (`ProfileTower.Lvl.Good.completion`), relabelled
through its top field layer (`CompletionBelowFullGrade.exists_botKeeping_of_eq_fieldLayer`). -/
theorem exists_botKeeping_of_three_le (I : Seed.{u} α m) (hm : 3 ≤ m) :
    ∃ F : CompletionBelowFullGrade I, F.BotKeeping := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  have hL := lvl_good (I := I) (by omega) j (by omega)
  have hN := hL.next (by omega)
  have hS := hL.sectionBotKeeping_next (lvl_sectionBotKeeping I (by omega) j (by omega))
  obtain ⟨p, hp, hpe, hpb⟩ := hN.exists_botKeeping hS
  exact (hN.completion hL.hasBotExtension_next (by omega)).exists_botKeeping_of_eq_fieldLayer
    (hS := (lvl I j).next.not_le) rfl hp hpb fun d x hx ↦ by
      obtain rfl : x = (lvl I j).next.embed d := Fin.ext hx.symm
      exact hpe d

end ProfileTower

/-- **Every seed has a bot-keeping completion below the full grade.** -/
theorem Seed.exists_botKeeping {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) :
    ∃ F : CompletionBelowFullGrade I, F.BotKeeping := by
  rcases le_or_gt m 2 with hm | hm
  · exact I.exists_botKeeping_of_le_two hm
  · exact ProfileTower.exists_botKeeping_of_three_le I hm

end VaughtConjecture
