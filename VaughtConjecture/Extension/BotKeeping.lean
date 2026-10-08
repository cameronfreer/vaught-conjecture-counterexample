/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.TwoFaceLift
import VaughtConjecture.Extension.CodedSection

/-!
# Bot-keeping labellings and completions

Roadmap, Layer 3, 3.1, (R6) (the completion below the full grade).

A labelling `r` of a scheme is **bot-keeping** (`Scheme.BotKeeping`) when every cell of full scope
not labelled `⊥` reads every cell of proper scope labelled `⊥` as `⊥`.  A completion below the full
grade is bot-keeping (`CompletionBelowFullGrade.BotKeeping`) when its labelling is.  Compiled in
this repository (theorem named):

* **The extension at `⊥` through a field layer keeps the bottoms**
  (`Scheme.exists_isLawful_fieldLayer_bot`, with `Label.eq_bot_of_agreementHeight_ne_bot`): the
  new cell of an entry reads the agreement height of that entry with the orbit code of the input,
  `⊥` when the two differ in their bottoms.
* **Field layers keep bot-keeping** (`Scheme.exists_botKeeping_fieldLayer`), with the rows of the
  old cells (`Scheme.rowAt_appendFullCells_castAdd`, `Scheme.rowAt_appendFullCell_castSucc`, in
  `VaughtConjecture.Extension.FieldLayer`).
  Stage reduction keeps exactly the bottoms (`Label.reduce_eq_bot_iff`).
* **The tower** (`Seed.exists_botKeeping_tower`) and its completion under the lifting invariant
  (`Seed.exists_botKeeping_of_towerInvariant`), at the arities `m ≤ 2` with no hypothesis
  (`Seed.exists_botKeeping_of_le_two`); `Seed.exists_completion_rowAt_eq_bot`.
* **The apex keeps it** (`CompletionBelowFullGrade.BotKeeping.rowAt_completion_eq_bot`): the apex
  reads a cell as `⊥` exactly where its label is `⊥` (`StageType.rowAt_addApex_last_eq_bot_iff`, in
  `VaughtConjecture.Extension.Apex`).
* **A completion whose scheme is a field layer at the top grade**
  (`CompletionBelowFullGrade.exists_botKeeping_of_eq_fieldLayer`): bot-keeping after relabelling,
  from a bot-keeping lawful section below literal on the amalgam.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### The extension at `⊥` through a field layer keeps the bottoms -/

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {k : ℕ}
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- **The extension at `⊥` through a field layer keeps the bottoms.**  Every lawful section `p` of
`S` extends to a lawful section `r` of the field layer at `k`, equal to `p` on the old cells, such
that the new cell of every catalogue entry not `⊥` at some cell of grade at most `k` where `p` is
`⊥` is labelled `⊥` by `r`. -/
theorem exists_isLawful_fieldLayer_bot {p : Fin S.card → Label.{u}} (hp : S.rows.IsLawful p) :
    ∃ r, (S.fieldLayer k hS).rows.IsLawful r ∧ (∀ d, r (Fin.castAdd _ d) = p d) ∧
      ∀ i, r (Fin.natAdd _ i) ≠ ⊥ → ∀ d, S.toCellScheme.grade d ≤ k → p d = ⊥ →
        S.catalogueEntry k i d = ⊥ := by
  set t := S.toCellScheme.splice k (fun _ ↦ ⊥) p
  have hpb := hp.isLawfulBelow (univ, k)
  have hb := orbitCode_splice_bot_mem_catalogue hpb
  set r₀ : (S.fieldLayer k hS).toCellScheme.below (univ, k) → Label.{u} :=
    fun x ↦ orbitDecoder k t (gridPoint k 0) (S.fieldRow k (orbitCode k t) x) with hr₀_def
  have hr₀ : (S.fieldLayer k hS).rows.IsLawfulBelow (univ, k) r₀ :=
    ((isLawful_fieldRow (hS := hS) hb).isLawfulBelow _).map_of_apply_eq_bot (fun x ↦ x.2.2)
      (isWitness_orbitDecoder (isSelfVisible_gridPoint k 0) (gridPoint_ne_bot k 0))
      fun _ ↦ eq_bot_of_orbitDecoder_eq_bot (gridPoint_ne_bot k 0)
  have hr₀p (d : Fin S.card) (hd : S.toCellScheme.grade d ≤ k) :
      r₀ ⟨Fin.castAdd _ d, castAdd_mem_below hd⟩ = p d := by
    change orbitDecoder k t (gridPoint k 0) (S.fieldRow k (orbitCode k t) (Fin.castAdd _ d)) = p d
    rw [fieldRow_castAdd, orbitDecoder_orbitCode (fun e ↦ min_orbitCode_gridPoint_zero e)]
    exact CellScheme.splice_of_le hd
  obtain ⟨i₀, -⟩ := exists_catalogueEntry_eq hb
  set r : Fin (S.card + (S.catalogue k).card) → Label.{u} :=
    Fin.append p fun i ↦ r₀ ⟨Fin.natAdd _ i, natAdd_mem_below i⟩ with hr_def
  have hrr₀ (x : (S.fieldLayer k hS).toCellScheme.below (univ, k)) : r x.1 = r₀ x := by
    obtain ⟨x, hx⟩ := x
    induction x using Fin.addCases with
    | left d =>
      rw [hr_def, Fin.append_left]
      exact (hr₀p d (by simpa using hx.2)).symm
    | right i => rw [hr_def, Fin.append_right]
  have hrb : (S.fieldLayer k hS).rows.IsLawfulBelow (univ, k) fun x ↦ r x := by
    convert hr₀ using 1
    exact funext hrr₀
  obtain ⟨hvis, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hrb
  refine ⟨r, isLawful_appendFullCells ?_ (fun i ↦ ?_) (fun i ↦ ?_) fun s hs ↦ ?_,
    fun d ↦ Fin.append_left _ _ d, fun i hi d hd hpd ↦ ?_⟩
  · convert hp using 1
    exact funext fun d ↦ Fin.append_left _ _ d
  · have hg : (S.fieldLayer k hS).toCellScheme.grade (Fin.natAdd S.card i) = k :=
      appendFullCellsScheme_grade_natAdd S k _ i
    have h := hvis _ (natAdd_mem_below i)
    rwa [hg] at h
  · have h := hloc _ (natAdd_mem_below i)
    rwa [appendFullCells_row_natAdd_eq] at h
  · have hsc : (S.fieldLayer k hS).toCellScheme.scope (Fin.natAdd S.card i₀) = univ :=
      appendFullCellsScheme_scope_natAdd S k _ i₀
    obtain ⟨u, hu, hle⟩ := havail s _ (natAdd_mem_below i₀) (hsc ▸ subset_univ _)
      (hs.trans (appendFullCellsScheme_grade_natAdd S k _ i₀).symm)
    obtain ⟨i, rfl⟩ := exists_natAdd_eq (hS := hS)
      (hu.trans (appendFullCellsScheme_gradedIndex_natAdd S k _ i₀))
    exact ⟨i, hle⟩
  · have hi' : r₀ ⟨Fin.natAdd _ i, natAdd_mem_below i⟩ ≠ ⊥ := by
      rwa [hr_def, Fin.append_right] at hi
    change orbitDecoder k t (gridPoint k 0) (S.fieldRow k (orbitCode k t) (Fin.natAdd _ i)) ≠ ⊥
      at hi'
    rw [fieldRow_natAdd] at hi'
    have hah : agreementHeight (S.fieldGrid k) (orbitCode k t) (S.catalogueEntry k i) ≠ ⊥ :=
      fun h ↦ hi' (by rw [h]; exact orbitDecoder_bot)
    refine eq_bot_of_agreementHeight_ne_bot (bot_mem_grid _ _) hah ?_
    rw [orbitCode_eq_bot_iff]
    change S.toCellScheme.splice k (fun _ ↦ ⊥) p d = ⊥
    rw [CellScheme.splice_of_le hd]
    exact hpd

end Scheme

/-! ### A completion whose cells of full scope at the top grade keep the bottoms -/

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- **A completion whose cells of full scope at the top grade keep the bottoms.**  Under the
lifting invariant at the top grade, some completion below the full grade of `I` (the tower of field
layers, labelled through its top layer by `Scheme.exists_isLawful_fieldLayer_bot`) has, after
adding the apex, the following property: every cell of full scope and grade at least `m + 1` that
is the apex or is not labelled `⊥` reads every cell of proper scope labelled `⊥` as `⊥`. -/
theorem exists_completion_rowAt_eq_bot (hinv : I.TowerInvariant (m + 1))
    (hα : Order.IsSuccPrelimit α) :
    ∃ F : CompletionBelowFullGrade I, ∀ u y : Fin (F.completion hα).card,
      (F.completion hα).toCellScheme.scope u = univ →
      m + 1 ≤ (F.completion hα).toCellScheme.grade u →
      ((F.completion hα).toCellScheme.grade u = m + 2 ∨ (F.completion hα).label u ≠ ⊥) →
      (F.completion hα).toCellScheme.scope y ≠ univ → (F.completion hα).label y = ⊥ →
        (F.completion hα).rowAt u y = ⊥ := by
  set F₀ := I.completionBelowFullGradeOfTowerInvariant hinv
  obtain ⟨p, hp, hpe⟩ := I.exists_isLawful_tower m I.amalgam.isLawful
  obtain ⟨L, hL, hLe, hLbot⟩ := Scheme.exists_isLawful_fieldLayer_bot
    (S := I.tower m) (k := m + 1) (hS := I.not_univ_succ_le_tower m) hp
  let F : CompletionBelowFullGrade I :=
    { F₀ with label := L, isLawful := hL, label_embed := fun d ↦ (hLe _).trans (hpe d) }
  refine ⟨F, fun u y hsu hgu hu hys hyb ↦ ?_⟩
  -- the cell `y` is an old cell of the truncation
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
  refine (Scheme.rowAt_appendFullCell_castSucc (h := F.isLegalBelowFullGrade.not_le) d y').trans ?_
  have hsd : F.scheme.toCellScheme.scope d = univ :=
    (Scheme.appendFullCellScheme_scope_castSucc _ _ d).symm.trans hsu
  have hgd : m + 1 ≤ F.scheme.toCellScheme.grade d :=
    hgu.trans_eq (Scheme.appendFullCellScheme_grade_castSucc _ _ d)
  have hlab (x : Fin (F.truncate hα).card) :
      (F.completion hα).label x.castSucc = Label.reduce α (L x) :=
    StageType.addApex_label_castSucc (t := F.truncate hα) F.isLegalBelowFullGrade _ x
  have hLd : L d ≠ ⊥ := by
    rcases hu with h4 | hne
    · have h4' : F.scheme.toCellScheme.grade d = m + 2 :=
        (Scheme.appendFullCellScheme_grade_castSucc _ _ d).symm.trans h4
      exact absurd h4' (F.isLegalBelowFullGrade.grade_lt d).ne
    · exact fun hL0 ↦ hne ((hlab d).trans ((Label.reduce_eq_bot_iff (α := α)).mpr hL0))
  have hy'b : L y' = ⊥ := (Label.reduce_eq_bot_iff (α := α)).mp ((hlab y').symm.trans hyb)
  have hy's : F.scheme.toCellScheme.scope y' ≠ univ := fun h ↦
    hys ((Scheme.appendFullCellScheme_scope_castSucc _ _ y').trans h)
  have hgy' : F.scheme.toCellScheme.grade y' < m + 2 := F.isLegalBelowFullGrade.grade_lt y'
  change Fin ((I.tower m).card + ((I.tower m).catalogue (m + 1)).card) at d y'
  induction d using Fin.addCases with
  | left e =>
    exfalso
    have hge : m + 1 ≤ (I.tower m).toCellScheme.grade e :=
      hgd.trans_eq (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ e)
    rcases I.tower_grade_le_or m e with he | he
    · omega
    · exact he ((Scheme.appendFullCellsScheme_scope_castAdd _ _ _ e).symm.trans hsd)
  | right i =>
  induction y' using Fin.addCases with
  | right i' => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i') hy's
  | left y₂ =>
  have hy₂ : p y₂ = ⊥ := (hLe y₂).symm.trans hy'b
  have hg₂ : (I.tower m).toCellScheme.grade y₂ ≤ m + 1 := by
    have h : (I.tower m).toCellScheme.grade y₂ < m + 2 :=
      (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ y₂).symm.trans_lt hgy'
    omega
  have hentry := hLbot i hLd y₂ hg₂ hy₂
  change ((I.tower m).fieldLayer (m + 1) (I.not_univ_succ_le_tower m)).rowAt (Fin.natAdd _ i)
    (Fin.castAdd _ y₂) = ⊥
  by_cases hm : (Fin.castAdd _ y₂ : Fin ((I.tower m).card + ((I.tower m).catalogue (m + 1)).card))
      ∈ ((I.tower m).fieldLayer (m + 1) (I.not_univ_succ_le_tower m)).toCellScheme.below
        (((I.tower m).fieldLayer (m + 1) (I.not_univ_succ_le_tower m)).toCellScheme.gradedIndex
          (Fin.natAdd _ i))
  · rw [Scheme.rowAt_of_mem hm, Scheme.fieldLayer_row_natAdd, Scheme.fieldRow_castAdd]
    exact hentry
  · exact Scheme.rowAt_of_notMem hm

end Seed

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n}

/-- A labelling is **bot-keeping**: every cell of full scope not labelled `⊥` reads every cell of
proper scope labelled `⊥` as `⊥`. -/
def BotKeeping (S : Scheme.{u} n) (r : Fin S.card → Label.{u}) : Prop :=
  ∀ u y, S.toCellScheme.scope u = univ → r u ≠ ⊥ → S.toCellScheme.scope y ≠ univ → r y = ⊥ →
    S.rowAt u y = ⊥

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
  | 0 => ⟨I.amalgam.label, I.amalgam.isLawful, fun _ ↦ rfl, fun u _ hsu ↦
      absurd hsu (I.scope_ne_univ u)⟩
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
    ((Label.reduce_eq_bot_iff (α := α)).mp ((hlab y').symm.trans hyb))
  rcases hu with h4 | hne
  · have h4' : F.scheme.toCellScheme.grade d = m + 2 :=
      (Scheme.appendFullCellScheme_grade_castSucc _ _ d).symm.trans h4
    exact absurd h4' (F.isLegalBelowFullGrade.grade_lt d).ne
  · exact fun hL0 ↦ hne ((hlab d).trans ((Label.reduce_eq_bot_iff (α := α)).mpr hL0))

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

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **A completion whose scheme is a field layer at the top grade is bot-keeping after
relabelling**, as soon as the scheme below has a bot-keeping lawful section literal on the
amalgam: the section extends through the layer (`Scheme.exists_botKeeping_fieldLayer`), and the
old cells, of proper scope, lie below the layer. -/
theorem exists_botKeeping_of_eq_fieldLayer (F₀ : CompletionBelowFullGrade I)
    {S : Scheme.{u} (m + 2)}
    {hS : ∀ d, ¬ ((univ : Finset (Fin (m + 2))), m + 1) ≤ S.toCellScheme.gradedIndex d}
    (hsch : F₀.scheme = S.fieldLayer (m + 1) hS) {p : Fin S.card → Label.{u}}
    (hp : S.rows.IsLawful p) (hpb : S.BotKeeping p)
    (hpe : ∀ d (x : Fin S.card), (F₀.embed d : ℕ) = x → p x = I.amalgam.label d) :
    ∃ F : CompletionBelowFullGrade I, F.BotKeeping := by
  obtain ⟨r, hr, hrp, hrb⟩ := Scheme.exists_botKeeping_fieldLayer (hS := hS) hp hpb
  obtain ⟨scheme, embed, hle, hsc, hrows, hrange, hfaces, hlegal, label, hlaw, hlab⟩ := F₀
  change scheme = _ at hsch
  subst hsch
  refine ⟨⟨_, embed, hle, hsc, hrows, hrange, hfaces, hlegal, r, hr, fun d ↦ ?_⟩, hrb⟩
  have hne : I.amalgam.toCellScheme.scope d ≠ univ := I.scope_ne_univ d
  by_cases hlt : (embed d : ℕ) < S.card
  · have he : embed d = Fin.castAdd _ ⟨embed d, hlt⟩ := Fin.ext rfl
    rw [he, hrp]
    exact hpe d _ rfl
  · exfalso
    have hk : (embed d : ℕ) - S.card < (S.catalogue (m + 1)).card := by
      have := (embed d).isLt
      change (embed d : ℕ) < S.card + (S.catalogue (m + 1)).card at this
      omega
    have he : embed d = Fin.natAdd _ ⟨(embed d : ℕ) - S.card, hk⟩ :=
      Fin.ext (by simp only [Fin.val_natAdd]; omega)
    refine hne ((hsc d).symm.trans ?_)
    rw [he]
    exact Scheme.appendFullCellsScheme_scope_natAdd S (m + 1) _ _

end CompletionBelowFullGrade

end VaughtConjecture
