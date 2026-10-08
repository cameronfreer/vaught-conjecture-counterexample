/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapBottomCarrier
import VaughtConjecture.Continuation.TiedRootCapVacuous

/-!
# A selective coface of the context with root cells labelled `⊥`

Roadmap, Layer 3 ((R3) of the table of 3.4).

`BottomRootCounterexample.markedCapContextBelow'_of_mem_bottomPatternFamily` acquires, over an
occurrence of the context of `BottomRootCounterexample`, a cap respecting the root bottoms through
the bottom-pattern clause, from a **selective coface**
(`BottomRootCounterexample.IsSelectiveCoface`: a legal coface whose cells of full scope and grade
`4`, and those of grade `3` not labelled `⊥`, read the root cells as `⊥`).  This file builds one.

* **The extension at `⊥` through a field layer keeps the bottoms**
  (`Scheme.exists_isLawful_fieldLayer_bot`, compiled in this repository (theorem named)): every
  lawful section `p` of `S` extends to a lawful section of the field layer at `k` (`p` on the old
  cells) which is `⊥` at every new cell whose catalogue entry is not `⊥` at some cell of grade at
  most `k` where `p` is `⊥`.  The extension of `Scheme.exists_isLawful_fieldLayer` reads, at the new
  cell of an entry, the agreement height of that entry with the orbit code of `p`; it is `⊥` when
  the two differ in their bottoms (`Label.agreementHeight`).
* **The rows of the old cells after appending a cell of full scope**
  (`Scheme.rowAt_appendFullCell_castSucc`, compiled).
* **A completion keeping the bottoms at the top grade** (`Seed.exists_completion_rowAt_eq_bot`,
  compiled): under the lifting invariant at the top grade `m + 1`, the tower of field layers
  (`Seed.completionBelowFullGradeOfTowerInvariant`), labelled through its top layer by the
  extension above, with the apex added, has every cell of full scope and grade at least `m + 1`
  that is the apex or not labelled `⊥` reading every cell of proper scope labelled `⊥` as `⊥`.  The
  cells of full scope and grade `m + 1` are the new cells of the top layer, which read their
  catalogue entries; the apex reads the labels.
* **The selective coface** (`BottomRootCounterexample.hasSelectiveCoface`, compiled): that
  completion for `BottomRootCounterexample.seedFour` (`m = 2`, where the lifting invariant holds,
  `Seed.towerInvariant_of_le_two`).
* **Acquisition over an occurrence of the context**
  (`BottomRootCounterexample.exists_markedCapContextBelow'`, compiled): in a model, over every
  tuple whose type is the context, some one-point extension has a type in
  `TiedRootCapRelabel.MarkedCapContextBelow'` along the root (the bottom-pattern clause with the
  scheme and labels of the selective coface,
  `BottomRootCounterexample.markedCapContextBelow'_of_mem_bottomPatternFamily`).

This is the acquisition of `TiedRootCapRelabel.MarkedCapContextBelow'` over this occurrence, not
`Realization.RootBottomAcquisition`: over an occurrence of another type the same construction needs
a completion below the full grade at its arity (here for seeds with `m ≤ 2`,
`Seed.towerInvariant_of_le_two`), a top cap of a grade below the top layer is read by a lower
layer of the tower, and the extended occurrence must keep the root's row inequality at its tops
(here vacuous: the root has no cell labelled `⊤`) (argued, not formalized).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### The extension at `⊥` through a field layer keeps the bottoms -/

namespace Label

variable {ι : Type*} [Fintype ι] {G : Finset Label.{u}} {a b : ι → Label.{u}}

/-- **An agreement height other than `⊥` keeps the bottoms**: where `a` is `⊥`, so is `b`. -/
theorem eq_bot_of_agreementHeight_ne_bot (hG : ⊥ ∈ G) (h : agreementHeight G a b ≠ ⊥) {d : ι}
    (hd : a d = ⊥) : b d = ⊥ := by
  have hspec := (agreementHeight_spec hG a b).2 d
  rw [hd, min_eq_left bot_le] at hspec
  rcases min_eq_bot.mp hspec.symm with h' | h'
  · exact h'
  · exact absurd h' h

end Label

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

/-- **The rows of the old cells after appending a cell of full scope** are their rows before. -/
theorem rowAt_appendFullCell_castSucc {j : ℕ} {r : Fin (S.card + 1) → Label.{u}}
    {h : ∀ d, ¬ ((univ : Finset (Fin n)), j) ≤ S.toCellScheme.gradedIndex d} (u x : Fin S.card) :
    (S.appendFullCell j r h).rowAt u.castSucc x.castSucc = S.rowAt u x := by
  by_cases hx : x ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u)
  · have hx' : x.castSucc ∈ (S.appendFullCell j r h).toCellScheme.below
        ((S.appendFullCell j r h).toCellScheme.gradedIndex u.castSucc) := by
      rw [CellScheme.mem_below] at hx ⊢
      simpa using hx
    rw [rowAt_of_mem hx', rowAt_of_mem hx]
    have hrow := congrArg (fun R : S.toCellScheme.Rows ↦ R.row u ⟨x, hx⟩)
      (comap_rows_castSucc (S := S) (j := j) (r := r) (h := h))
    simp only [CellScheme.Rows.comap_row] at hrow
    exact hrow
  · have hx' : x.castSucc ∉ (S.appendFullCell j r h).toCellScheme.below
        ((S.appendFullCell j r h).toCellScheme.gradedIndex u.castSucc) := by
      rw [CellScheme.mem_below] at hx ⊢
      simpa using hx
    rw [rowAt_of_notMem hx', rowAt_of_notMem hx]

end Scheme

/-! ### A completion whose cells of full scope at the top grade keep the bottoms -/

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- Stage reduction sends exactly `⊥` to `⊥`. -/
private theorem reduce_eq_bot_iff {x : Label.{u}} : Label.reduce α x = ⊥ ↔ x = ⊥ := by
  by_cases hx : x < α
  · rw [reduce_of_lt hx]
  · rw [reduce_of_le (not_lt.mp hx)]
    refine ⟨fun h ↦ absurd h top_ne_bot, fun h ↦ ?_⟩
    subst h
    exact absurd (WithBot.bot_lt_coe _) hx

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
    · exact fun hL0 ↦ hne ((hlab d).trans ((reduce_eq_bot_iff (α := α)).mpr hL0))
  have hy'b : L y' = ⊥ := (reduce_eq_bot_iff (α := α)).mp ((hlab y').symm.trans hyb)
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

/-! ### The selective coface -/

namespace BottomRootCounterexample

open StageType
open TiedRootCapCounterexample (rootEmb)

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- **The context has a selective coface**: the completion of
`Seed.exists_completion_rowAt_eq_bot` for `seedFour` (lifting invariant at the arity `m = 2`). -/
theorem hasSelectiveCoface : HasSelectiveCoface hα := by
  have hα' := hα.isSuccPrelimit
  obtain ⟨F, hF⟩ := (seedFour hα).exists_completion_rowAt_eq_bot
    ((seedFour hα).towerInvariant_of_le_two le_rfl 3 le_rfl) hα'
  have hq₁ : restrictFace Fin.castSuccEmb (F.completion hα') = some (context hα) :=
    F.restrictFace_left_completion hα'
  refine ⟨F.completion hα', ⟨F.isLegal_completion hα', hq₁⟩, fun u hsu hgu hu y hy ↦ ?_⟩
  have hroot : restrictFace (rootEmb.trans Fin.castSuccEmb) (F.completion hα') = some root := by
    rw [← restrictFace_trans _ _ _ hq₁]
    exact restrictFace_context hα
  obtain ⟨z, rfl⟩ := exists_faceCell_eq hroot hy
  refine hF u _ hsu hgu hu ?_ ((label_faceCell hroot z).trans rfl)
  rw [scope_faceCell]
  intro h
  have h1 := congrArg Finset.card h
  rw [card_map, card_univ, Fintype.card_fin] at h1
  have h2 := card_le_univ ((root (α := α)).toCellScheme.scope z)
  rw [Fintype.card_fin] at h2
  omega

/-- **Acquisition of a cap respecting the root bottoms over an occurrence of the context.**  In a
model, over every tuple whose type is the context, the bottom-pattern clause with the scheme and
labels of the selective coface realizes a one-point extension whose type is a marked-cap context
along the root, with root offsets below its cap and its cap reading the root cells as `⊥`. -/
theorem exists_markedCapContextBelow' {M : Type*} {R : Realization.{u} α M} (hR : R.IsModel)
    {c : Fin 3 ↪ M} (hc : R.eval c = some (context hα)) :
    ∃ (v : Fin 4 ↪ M) (q : StageType.{u} α 4), Fin.castSuccEmb.trans v = c ∧
      R.eval v = some q ∧ TiedRootCapRelabel.MarkedCapContextBelow' q
        (rootEmb.trans Fin.castSuccEmb) := by
  obtain ⟨qs, hqs⟩ := hasSelectiveCoface hα
  set x : R.Occurrence := ⟨3, c, context hα, hc⟩
  have hne : (x.type.cofaces ∩ bottomPatternFamily qs.toScheme qs.label).Nonempty :=
    ⟨qs, hqs.1, rfl, fun i j hij _ ↦ by obtain rfl : i = j := Fin.ext hij; rfl⟩
  obtain ⟨v, hv, q, hq, he⟩ :=
    (hR.bottomPattern x qs.toScheme qs.label hne).inter_cofaces hR.isConsistent hR.isLegal
  exact ⟨v, q, hv, he, markedCapContextBelow'_of_mem_bottomPatternFamily hα hqs hq⟩

end BottomRootCounterexample

end VaughtConjecture
