/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ProfileBotKeeping
import VaughtConjecture.Extension.StronglyCodedAmalgamation
import VaughtConjecture.Realization.Families

/-!
# Strongly coded bot-keeping completions and the strongly coded bot-keeping coface

Roadmap, Layer 3, 3.1, (R6) (the completion below the full grade) and Correspondence, item 1 (the
strongly coded legal stage types).  All results here are native constructions of this repository.

The acquisition of marked-cap contexts (`Realization.rootBottomAcquisition_of_botKeeping`) realizes
the completion of a bot-keeping completion below the full grade (`Seed.exists_botKeeping`), whose
apex row is the block coding of the labels (`StageType.addApex`); it need not be strongly coded.
This file shows that the bot-keeping construction keeps the scheme of the strongly coded completion,
and that the strongly coded apex reads the cells labelled `⊥` as `⊥`, so the strongly coded
completion of a bot-keeping completion is a strongly coded bot-keeping coface.

**The bot-keeping construction keeps the scheme.**

* (a) `Seed.BotKeepingSameSchemeTarget`, proved (`Seed.botKeepingSameSchemeTarget`): at `m ≥ 3`
  the bot-keeping completion of `ProfileTower.exists_botKeeping_of_three_le` is the completion over
  the good level (`ProfileTower.Lvl.Good.completion`, the completion of
  `Seed.exists_completionBelowFullGrade_isStronglyCoded` at `m ≥ 3`) with another labelling: its
  scheme is the same field layer (`CompletionBelowFullGrade.exists_botKeeping_of_eq_fieldLayer`
  keeps the scheme, `CompletionBelowFullGrade.exists_botKeeping_scheme_eq_of_eq_fieldLayer`), which
  is strongly coded when the amalgam is (`Scheme.isStronglyCoded_fieldLayer`,
  `ProfileTower.Lvl.Good.isStronglyCoded_next`, `ProfileTower.isStronglyCoded_lvl`).
* (b) `Seed.StrongCodingSameSchemeTarget`, proved (`Seed.strongCodingSameSchemeTarget`): strong
  coding is a property of the rows, so it passes between completions on one scheme; the relabelling
  changes only the labels (no cell renaming is involved).
* (c) `Seed.BotKeepingTowerTarget`, proved (`Seed.botKeepingTowerTarget`): at `m ≤ 2` the
  construction (`Seed.exists_botKeeping_of_le_two`) is the tower completion
  (`Seed.completionBelowFullGradeOfTowerInvariant`) under the invariant
  `Seed.TowerInvariant (m + 1)` of `Seed.towerInvariant_of_le_two`, which is
  `Seed.towerInvariant_of_twoFaceLift` of `Seed.forall_twoFaceLift_of_two_le`, the invariant used
  by `Seed.exists_completionBelowFullGrade_isStronglyCoded` at `m ≤ 2`.  The invariant is a
  proposition and the scheme is the tower `I.tower (m + 1)` in either case; it is strongly coded
  when the amalgam is (`Seed.isStronglyCoded_tower`).
* `Seed.exists_botKeeping_isStronglyCoded`, proved: every seed with a strongly coded amalgam has a
  bot-keeping completion below the full grade with a strongly coded scheme.

**The strongly coded apex reads `⊥` as `⊥`.**

* `StageType.StrongApexReadsBotTarget`, proved (`StageType.rowAt_addStrongApex_last_eq_bot_iff`):
  the strongly coded apex reads a cell as `⊥` exactly when it is labelled `⊥`; its row is
  `Label.strongEncode` of the labels, and `Label.strongEncode_eq_bot_iff`.
* `CompletionBelowFullGrade.BotKeeping.rowAt_strongCompletion_eq_bot`, proved: the counterpart of
  `CompletionBelowFullGrade.BotKeeping.rowAt_completion_eq_bot` for the strongly coded completion
  (`CompletionBelowFullGrade.strongCompletion`).

**The coface.**  `StageType.StronglyCodedBotKeepingCofaceTarget`, proved
(`StageType.stronglyCodedBotKeepingCofaceTarget`): over a legal, strongly coded `q₀` with a face
along the first points, at a stage that is zero or a limit, the strongly coded completion of a
strongly coded bot-keeping completion of the seed of `q₀` with itself is a legal, strongly coded
coface of `q₀` whose cells of full scope that are the apex or not labelled `⊥` read every cell of
proper scope labelled `⊥` as `⊥`.  Its unrestricted form is `StageType.exists_botKeepingCoface`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### The bot-keeping construction keeps the scheme -/

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The relabelling through the top field layer keeps the scheme**:
`CompletionBelowFullGrade.exists_botKeeping_of_eq_fieldLayer`, with the scheme of the bot-keeping
completion that of `F₀`. -/
theorem exists_botKeeping_scheme_eq_of_eq_fieldLayer (F₀ : CompletionBelowFullGrade I)
    {S : Scheme.{u} (m + 2)}
    {hS : ∀ d, ¬ ((univ : Finset (Fin (m + 2))), m + 1) ≤ S.toCellScheme.gradedIndex d}
    (hsch : F₀.scheme = S.fieldLayer (m + 1) hS) {p : Fin S.card → Label.{u}}
    (hp : S.rows.IsLawful p) (hpb : S.BotKeeping p)
    (hpe : ∀ d (x : Fin S.card), (F₀.embed d : ℕ) = x → p x = I.amalgam.label d) :
    ∃ F : CompletionBelowFullGrade I, F.BotKeeping ∧ F.scheme = F₀.scheme := by
  obtain ⟨r, hr, hrp, hrb⟩ := Scheme.exists_botKeeping_fieldLayer (hS := hS) hp hpb
  obtain ⟨scheme, embed, hle, hsc, hrows, hrange, hfaces, hlegal, label, hlaw, hlab⟩ := F₀
  change scheme = _ at hsch
  subst hsch
  refine ⟨⟨_, embed, hle, hsc, hrows, hrange, hfaces, hlegal, r, hr, fun d ↦ ?_⟩, hrb, rfl⟩
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

namespace Seed

/-- **(a) Target: at `m ≥ 3` the bot-keeping construction relabels a completion** `F₀` whose scheme
is strongly coded when the amalgam is: some bot-keeping completion has the scheme of `F₀`. -/
def BotKeepingSameSchemeTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃m : ℕ⦄ (I : Seed.{u} α m), 3 ≤ m →
    ∃ F₀ F : CompletionBelowFullGrade I, F.BotKeeping ∧ F.scheme = F₀.scheme ∧
      (I.amalgam.rows.IsStronglyCoded → F₀.scheme.rows.IsStronglyCoded)

/-- **(a) proved** (native construction): `F₀` is the completion over the good level at the grade
`m` (`ProfileTower.Lvl.Good.completion`), a field layer at the top grade, and the bot-keeping
completion of `ProfileTower.exists_botKeeping_of_three_le` relabels it
(`CompletionBelowFullGrade.exists_botKeeping_scheme_eq_of_eq_fieldLayer`). -/
theorem botKeepingSameSchemeTarget : BotKeepingSameSchemeTarget.{u} := by
  intro α m I hm
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  have hL := ProfileTower.lvl_good (I := I) (by omega) j (by omega)
  have hN := hL.next (by omega)
  have hS := hL.sectionBotKeeping_next
    (ProfileTower.lvl_sectionBotKeeping I (by omega) j (by omega))
  obtain ⟨p, hp, hpe, hpb⟩ := hN.exists_botKeeping hS
  obtain ⟨F, hF, hFs⟩ := (hN.completion hL.hasBotExtension_next (by omega)
    ).exists_botKeeping_scheme_eq_of_eq_fieldLayer
    (hS := (ProfileTower.lvl I j).next.not_le) rfl hp hpb fun d x hx ↦ by
      obtain rfl : x = (ProfileTower.lvl I j).next.embed d := Fin.ext hx.symm
      exact hpe d
  exact ⟨_, F, hF, hFs, fun h ↦ Scheme.isStronglyCoded_fieldLayer
    (hS := (ProfileTower.lvl I j).next.not_le)
    (hL.isStronglyCoded_next (ProfileTower.isStronglyCoded_lvl (by omega) h j (by omega)))⟩

/-- **(b) Target: strong coding passes between completions on one scheme.** -/
def StrongCodingSameSchemeTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃m : ℕ⦄ (I : Seed.{u} α m) (F F₀ : CompletionBelowFullGrade I),
    F.scheme = F₀.scheme → F₀.scheme.rows.IsStronglyCoded → F.scheme.rows.IsStronglyCoded

/-- **(b) proved**: strong coding is a property of the rows of the scheme. -/
theorem strongCodingSameSchemeTarget : StrongCodingSameSchemeTarget.{u} :=
  fun _ _ _ _ _ h h₀ ↦ h ▸ h₀

/-- **(c) Target: at `m ≤ 2` the bot-keeping construction is on the tower**: some bot-keeping
completion has the scheme `I.tower (m + 1)`. -/
def BotKeepingTowerTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃m : ℕ⦄ (I : Seed.{u} α m), m ≤ 2 →
    ∃ F : CompletionBelowFullGrade I, F.BotKeeping ∧ F.scheme = I.tower (m + 1)

/-- **(c) proved** (native construction): `Seed.exists_botKeeping_of_le_two` is the tower completion
`Seed.completionBelowFullGradeOfTowerInvariant` under `Seed.towerInvariant_of_le_two`, relabelled by
a bot-keeping section of the tower (`Seed.exists_botKeeping_tower`); its scheme is the tower. -/
theorem botKeepingTowerTarget : BotKeepingTowerTarget.{u} := by
  intro α m I hm
  obtain ⟨L, hL, hLe, hLb⟩ := I.exists_botKeeping_tower (m + 1)
  exact ⟨{ I.completionBelowFullGradeOfTowerInvariant
    (I.towerInvariant_of_le_two hm (m + 1) le_rfl) with
    label := L, isLawful := hL, label_embed := hLe }, hLb, rfl⟩

variable {α : Ordinal.{u}} {m : ℕ}

/-- **A strongly coded bot-keeping completion** (native construction): every seed with a strongly
coded amalgam has a bot-keeping completion below the full grade with a strongly coded scheme; at
`m ≤ 2` by (c) and `Seed.isStronglyCoded_tower`, at `m ≥ 3` by (a) and (b). -/
theorem exists_botKeeping_isStronglyCoded (I : Seed.{u} α m)
    (h : I.amalgam.rows.IsStronglyCoded) :
    ∃ F : CompletionBelowFullGrade I, F.BotKeeping ∧ F.scheme.rows.IsStronglyCoded := by
  rcases le_or_gt m 2 with hm | hm
  · obtain ⟨F, hF, hFs⟩ := botKeepingTowerTarget I hm
    exact ⟨F, hF, hFs ▸ I.isStronglyCoded_tower h (m + 1)⟩
  · obtain ⟨F₀, F, hF, hFs, hF₀⟩ := botKeepingSameSchemeTarget I hm
    exact ⟨F, hF, strongCodingSameSchemeTarget I F F₀ hFs (hF₀ h)⟩

end Seed

/-! ### The strongly coded apex reads `⊥` as `⊥` -/

namespace StageType

/-- **Target: the strongly coded apex reads a cell as `⊥` exactly when it is labelled `⊥`.** -/
def StrongApexReadsBotTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n : ℕ⦄ (t : StageType.{u} α n) (ht : t.IsLegalBelowFullGrade)
    (hn : 0 < n) (z : Fin (t.addStrongApex ht hn).card),
    (t.addStrongApex ht hn).toScheme.rowAt (Fin.last _) z = ⊥ ↔
      (t.addStrongApex ht hn).label z = ⊥

variable {α : Ordinal.{u}} {n : ℕ} {t : StageType.{u} α n}

/-- **The strongly coded apex reads a cell as `⊥` exactly when it is labelled `⊥`** (native
construction): every cell is below the apex, the row of the apex is the strongly coded encoding
of the labels (`StageType.strongApexRow`), and the encoding is `⊥` exactly at `⊥`
(`Label.strongEncode_eq_bot_iff`). -/
theorem rowAt_addStrongApex_last_eq_bot_iff (ht : t.IsLegalBelowFullGrade) (hn : 0 < n)
    (z : Fin (t.addStrongApex ht hn).card) :
    (t.addStrongApex ht hn).toScheme.rowAt (Fin.last _) z = ⊥ ↔
      (t.addStrongApex ht hn).label z = ⊥ := by
  have hz : z ∈ (t.addStrongApex ht hn).toCellScheme.below
      ((t.addStrongApex ht hn).toCellScheme.gradedIndex (Fin.last _)) := by
    have hlast : (t.addStrongApex ht hn).toCellScheme.gradedIndex (Fin.last _) = (univ, n) :=
      Scheme.appendFullCellScheme_gradedIndex_last _ _
    rw [CellScheme.mem_below, hlast]
    exact Prod.mk_le_mk.mpr ⟨subset_univ _, (t.addStrongApex ht hn).grade_le z⟩
  rw [Scheme.rowAt_of_mem hz]
  change (t.toScheme.appendFullCell n t.strongApexRow ht.not_le).rows.row (Fin.last _) ⟨z, hz⟩ =
    ⊥ ↔ apexLabel (t := t) z = ⊥
  rw [Scheme.appendFullCell_row_last]
  change t.strongApexRow z = ⊥ ↔ apexLabel (t := t) z = ⊥
  clear hz
  induction z using Fin.lastCases with
  | last => simp only [strongApexRow_last, apexLabel_last, strongEncode_eq_bot_iff]
  | cast d => simp only [strongApexRow_castSucc, apexLabel_castSucc, strongEncode_eq_bot_iff]

/-- **The target is proved.** -/
theorem strongApexReadsBotTarget : StrongApexReadsBotTarget.{u} :=
  fun _ _ _ ht hn z ↦ rowAt_addStrongApex_last_eq_bot_iff ht hn z

end StageType

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The strongly coded apex keeps it** (native construction): as
`CompletionBelowFullGrade.BotKeeping.rowAt_completion_eq_bot`, for the strongly coded completion;
the apex reads `⊥` as `⊥` by `StageType.rowAt_addStrongApex_last_eq_bot_iff`. -/
theorem BotKeeping.rowAt_strongCompletion_eq_bot {F : CompletionBelowFullGrade I}
    (hF : F.BotKeeping) (hα : Order.IsSuccPrelimit α) (u y : Fin (F.strongCompletion hα).card)
    (hsu : (F.strongCompletion hα).toCellScheme.scope u = univ)
    (hu : (F.strongCompletion hα).toCellScheme.grade u = m + 2 ∨
      (F.strongCompletion hα).label u ≠ ⊥)
    (hys : (F.strongCompletion hα).toCellScheme.scope y ≠ univ)
    (hyb : (F.strongCompletion hα).label y = ⊥) : (F.strongCompletion hα).rowAt u y = ⊥ := by
  have hyl : y ≠ Fin.last _ := fun h ↦ hys (by
    rw [h]
    exact Scheme.appendFullCellScheme_scope_last _ _)
  obtain ⟨y', rfl⟩ : ∃ y' : Fin (F.truncate hα).card, y = y'.castSucc :=
    ⟨y.castPred hyl, (Fin.castSucc_castPred _ _).symm⟩
  change Fin ((F.truncate hα).card + 1) at u
  induction u using Fin.lastCases with
  | last =>
    exact (StageType.rowAt_addStrongApex_last_eq_bot_iff F.isLegalBelowFullGrade
      (Nat.succ_pos _) _).mpr hyb
  | cast d =>
  refine (Scheme.rowAt_appendFullCell_castSucc (h := F.isLegalBelowFullGrade.not_le) d
    y').trans ?_
  have hlab (x : Fin (F.truncate hα).card) :
      (F.strongCompletion hα).label x.castSucc = Label.reduce α (F.label x) :=
    StageType.apexLabel_castSucc (t := F.truncate hα) x
  refine hF d y' ((Scheme.appendFullCellScheme_scope_castSucc _ _ d).symm.trans hsu) ?_
    (fun h ↦ hys ((Scheme.appendFullCellScheme_scope_castSucc _ _ y').trans h))
    ((Label.reduce_eq_bot_iff (α := α)).mp ((hlab y').symm.trans hyb))
  rcases hu with h4 | hne
  · have h4' : F.scheme.toCellScheme.grade d = m + 2 :=
      (Scheme.appendFullCellScheme_grade_castSucc _ _ d).symm.trans h4
    exact absurd h4' (F.isLegalBelowFullGrade.grade_lt d).ne
  · exact fun hL0 ↦ hne ((hlab d).trans ((Label.reduce_eq_bot_iff (α := α)).mpr hL0))

end CompletionBelowFullGrade

/-! ### The strongly coded bot-keeping coface -/

namespace StageType

/-- **A bot-keeping coface** (native construction): over a legal stage type `q₀` on `m + 1` points
with a face along the first `m` points, at a stage that is zero or a limit, some coface `qs` of
`q₀` has every cell of full scope that is its apex (grade `m + 2`) or not labelled `⊥` reading
every cell of proper scope labelled `⊥` as `⊥`.  It is the completion of a bot-keeping completion
below the full grade of the seed of `q₀` with itself (`Seed.exists_botKeeping`,
`CompletionBelowFullGrade.BotKeeping.rowAt_completion_eq_bot`), the coface used in
`Realization.rootBottomAcquisition_of_botKeeping`.  Its apex row is the block coding of the labels,
which need not be strongly coded. -/
theorem exists_botKeepingCoface {α : Ordinal.{u}} {m : ℕ} (hα : Order.IsSuccPrelimit α)
    {q₀ : StageType.{u} α (m + 1)} (hl : q₀.IsLegal) {p : StageType.{u} α m}
    (hp : restrictFace Fin.castSuccEmb q₀ = some p) :
    ∃ qs ∈ q₀.cofaces, ∀ u y, qs.toCellScheme.scope u = univ →
      (qs.toCellScheme.grade u = m + 2 ∨ qs.label u ≠ ⊥) → qs.toCellScheme.scope y ≠ univ →
        qs.label y = ⊥ → qs.rowAt u y = ⊥ := by
  obtain ⟨F, hF⟩ := (Seed.ofCoatoms hl hl hp hp).exists_botKeeping
  exact ⟨F.completion hα, ⟨F.isLegal_completion _, F.restrictFace_left_completion hα⟩,
    fun u y hsu hu hys hyb ↦ hF.rowAt_completion_eq_bot hα u y hsu hu hys hyb⟩

/-- **Target: a strongly coded bot-keeping coface**: `StageType.exists_botKeepingCoface` for a
strongly coded `q₀`, with a coface `qs` whose rows are strongly coded.  This is what the
bottom-pattern step of `Realization.rootBottomAcquisition` needs in the strongly coded receiving
class, where only cofaces with strongly coded rows are received; receiving `qs` at a permitted
cutoff then realizes its bottom pattern (`StageType.receivingFamily_subset_bottomPatternFamily`). -/
def StronglyCodedBotKeepingCofaceTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃m : ℕ⦄ (q₀ : StageType.{u} α (m + 1)) (p : StageType.{u} α m),
    Order.IsSuccPrelimit α → q₀.IsLegal → q₀.rows.IsStronglyCoded →
    restrictFace Fin.castSuccEmb q₀ = some p →
    ∃ qs ∈ q₀.cofaces, qs.rows.IsStronglyCoded ∧ ∀ u y, qs.toCellScheme.scope u = univ →
      (qs.toCellScheme.grade u = m + 2 ∨ qs.label u ≠ ⊥) → qs.toCellScheme.scope y ≠ univ →
        qs.label y = ⊥ → qs.rowAt u y = ⊥

/-- **A strongly coded bot-keeping coface** (native construction): the strongly coded completion
(`CompletionBelowFullGrade.strongCompletion`) of a strongly coded bot-keeping completion
(`Seed.exists_botKeeping_isStronglyCoded`) of the seed of `q₀` with itself, whose amalgam is
strongly coded (`Seed.isStronglyCoded_amalgam`); it is legal (`StageType.isLegal_addStrongApex`),
has `q₀` as its face along the first points (`StageType.restrictFace_addStrongApex`,
`CompletionBelowFullGrade.restrictFace_left_truncate`), is strongly coded
(`StageType.isStronglyCoded_addStrongApex`), and keeps the bottoms
(`CompletionBelowFullGrade.BotKeeping.rowAt_strongCompletion_eq_bot`). -/
theorem stronglyCodedBotKeepingCofaceTarget : StronglyCodedBotKeepingCofaceTarget.{u} := by
  intro α m q₀ p hα hl hsc hp
  let I := Seed.ofCoatoms hl hl hp hp
  obtain ⟨F, hF, hFs⟩ := I.exists_botKeeping_isStronglyCoded (I.isStronglyCoded_amalgam hsc hsc)
  refine ⟨F.strongCompletion hα, ⟨isLegal_addStrongApex _ _, ?_⟩,
    isStronglyCoded_addStrongApex _ _ hFs,
    fun u y hsu hu hys hyb ↦ hF.rowAt_strongCompletion_eq_bot hα u y hsu hu hys hyb⟩
  exact (restrictFace_addStrongApex _ _ _ Coatom.univ_map_left_ne).trans
    (F.restrictFace_left_truncate hα)

end StageType

end VaughtConjecture
