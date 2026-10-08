/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapAdmittedCoface

/-!
# Cutoff determination at the twisted seed

Roadmap, Layer 3 ((R2) of the table of 3.4: cutoff determination for source-gap contexts, in its
coatom form); the LOW-admitted coface of `VaughtConjecture.Continuation.SourceGapAdmittedCoface`.

**The key step** (`MixedSeed.key_DU`).  Let `ℓ` be a lawful labelling of the scheme of the
LOW-admitted coface `MixedSeed.DU`, agreeing with the coface at the cells visible through the
context face (the input `T`) and with it capped at a cutoff `δ > v` everywhere.  Then `ℓ` agrees
with the coface at the cells visible through the donor face: the donor copies of the input
(`MixedSeed.exists_right_of_mem_below`).  At `y'` (shared with the context), by the context face; at
`e'` (`⊥`) and `r'` (`v`), by the agreement below `δ`; at `z'`, by lawfulness of the donor face
(`z = y`, `SeparationObstruction.eq_lab_of_isLawful`); at `o'`, by the determination in the
LOW-admitted completion (`MixedSeed.eq_top_of_admittedT`: `o` at `⊤`, `r'` below `⊤`).

**Cutoff determination** (`MixedSeed.isDeterminedWithin_DU`): at a stage that is zero or a limit,
for `v ≠ ⊤` and every cutoff `δ > v`, the donor `TwistedDonor.Utop` is determined over the input
`T α` along the root `{0}` within the receiving family of `MixedSeed.DU` at `δ`
(`StageType.isDeterminedWithin_apexOf`, from the key step).

**The coatom form at this input** (`MixedSeed.coatomCutoffDetermination_U`): at a limit stage the
input is a source-gap context of grade `2` along `{0}`
(`SeparationObstruction.isSourceGapContextAt_T`), the donor has top grade at most `2`, and some
coface with face the donor and some permitted cutoff (`MixedSeed.exists_permittedCutoff_gt`)
determine it: the clause of the coatom cutoff determination for the source-gap contexts at this
input, with the identity as `g` and the donor as `tb`.  This is the first such determination at a
donor other than the context whose new top `o'` is not forced by a root top.  It is an instance;
the clause for every source-gap context and donor is open.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

/-! ### Cutoff determination at the twisted seed -/

namespace MixedSeed

open StageType SeparationObstruction TwistedDonor

variable {α : Ordinal.{u}} {v : Label.{u}}

/-- The old cell of the LOW-admitted completion over the context copy of `z`. -/
noncomputable abbrev oL (z : Fin 5) : Fin (admittedT α).card :=
  Fin.castAdd _ (Fin.castAdd _ (lc α z))

/-- The old cell of the LOW-admitted completion over the donor copy of `z`. -/
noncomputable abbrev oR (z : Fin 5) : Fin (admittedT α).card :=
  Fin.castAdd _ (Fin.castAdd _ (rc α z))

theorem scope_oL (z : Fin 5) :
    (admittedT α).toCellScheme.scope (oL z) = (cells.scope z).map (Coatom.left 1) :=
  ((Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
    (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _)).trans
    (congrArg Prod.fst (gradedIndex_lc z))

/-- **The key step**: a lawful labelling of the LOW-admitted coface agreeing with it on the context
face and capped at `δ > v` agrees with it on the donor face. -/
theorem key_DU (hα : Order.IsSuccPrelimit α) (hv : IsSelfVisible 2 v) (hvα : AtStage α v)
    (hvt : v ≠ ⊤) {δ : Label.{u}} (hvδ : v < δ) (ℓ : Fin ((admittedT α).card + 1) → Label.{u})
    (hl : (apexOf isLegalBelowFullGrade_admittedT (isLawful_qT hα hv) (atStage_qT hv)
      (Nat.succ_pos 2)).rows.IsLawful ℓ)
    (hleft : ∀ x ∈ (apexOf isLegalBelowFullGrade_admittedT (isLawful_qT hα hv) (atStage_qT hv)
      (Nat.succ_pos 2)).toScheme.visibleCells Fin.castSuccEmb,
        ℓ x = (apexOf isLegalBelowFullGrade_admittedT (isLawful_qT hα hv) (atStage_qT hv)
          (Nat.succ_pos 2)).label x)
    (hag : ∀ x, min (ℓ x) δ = min ((apexOf isLegalBelowFullGrade_admittedT (isLawful_qT hα hv)
      (atStage_qT hv) (Nat.succ_pos 2)).label x) δ) :
    ∀ y ∈ (apexOf isLegalBelowFullGrade_admittedT (isLawful_qT hα hv) (atStage_qT hv)
      (Nat.succ_pos 2)).toScheme.visibleCells (extendByLast Fin.castSuccEmb),
        ℓ y = (apexOf isLegalBelowFullGrade_admittedT (isLawful_qT hα hv) (atStage_qT hv)
          (Nat.succ_pos 2)).label y := by
  have hlab (x : Fin (admittedT α).card) :
      (apexOf isLegalBelowFullGrade_admittedT (isLawful_qT hα hv) (atStage_qT hv)
        (Nat.succ_pos 2)).label (Fin.castSucc x) = qT hv x :=
    apexOf_label_castSucc isLegalBelowFullGrade_admittedT (isLawful_qT hα hv) (atStage_qT hv)
      (Nat.succ_pos 2) x
  have hsc (x : Fin (admittedT α).card) :
      (apexOf isLegalBelowFullGrade_admittedT (isLawful_qT hα hv) (atStage_qT hv)
        (Nat.succ_pos 2)).toCellScheme.scope (Fin.castSucc x) =
        (admittedT α).toCellScheme.scope x :=
    apexOf_scope_castSucc isLegalBelowFullGrade_admittedT (isLawful_qT hα hv) (atStage_qT hv)
      (Nat.succ_pos 2) x
  have hL (z : Fin 5) : ℓ (Fin.castSucc (oL z)) = lab ⊤ ⊤ ⊤ z := by
    have hoL : oL (α := α) z ∈ (admittedT α).visibleCells Fin.castSuccEmb := by
      refine Scheme.mem_visibleCells.mpr fun x hx ↦ ?_
      have hx' : x ∈ (cells.scope z).map (Coatom.left 1) := by rw [← scope_oL z]; exact hx
      obtain ⟨y, -, rfl⟩ := mem_map.mp hx'
      exact ⟨y, rfl⟩
    have hmem := apexOf_castSucc_mem_visibleCells isLegalBelowFullGrade_admittedT
      (isLawful_qT hα hv) (atStage_qT hv) (Nat.succ_pos 2) hoL
    exact ((hleft _ hmem).trans (hlab (oL z))).trans (qT_lc hv z)
  have hR (z : Fin 5) :
      (apexOf isLegalBelowFullGrade_admittedT (isLawful_qT hα hv) (atStage_qT hv)
        (Nat.succ_pos 2)).label (Fin.castSucc (oR z)) = lab ⊤ ⊤ v z := by
    rw [hlab, qT_rc hv hvα]
  have hl'' : (admittedT α).rows.IsLawful (ℓ ∘ Fin.castSucc) :=
    isLawful_castSucc_addApex (t := ofLegalBelow (admittedT α) isLegalBelowFullGrade_admittedT
      (qT hv) (isLawful_qT hα hv) (atStage_qT hv)) isLegalBelowFullGrade_admittedT
      (Nat.succ_pos 2) hl
  have hr' : ℓ (Fin.castSucc (oR 4)) = v := by
    have e := (hag (Fin.castSucc (oR 4))).trans (congrArg (fun t ↦ min t δ) (hR 4))
    exact Label.eq_of_min_eq_of_lt e.symm hvδ
  have he' : ℓ (Fin.castSucc (oR 1)) = ⊥ := by
    have e := (hag (Fin.castSucc (oR 1))).trans (congrArg (fun t ↦ min t δ) (hR 1))
    change min (ℓ (Fin.castSucc (oR 1))) δ = min ⊥ δ at e
    rw [min_bot_left] at e
    rcases min_eq_bot.mp e with h | h
    · exact h
    · exact absurd h (ne_bot_of_gt hvδ)
  have ho' : ℓ (Fin.castSucc (oR 3)) = ⊤ := by
    refine eq_top_of_admittedT (q := ℓ ∘ Fin.castSucc) (hl''.isLawfulBelow _) (hL 3) ?_
    change ℓ (Fin.castSucc (oR 4)) < ⊤
    rw [hr']
    exact lt_top_iff_ne_top.mpr hvt
  have h0 : oR (α := α) 0 = oL 0 := by rw [oR, oL, lc_zero]
  have hz' : ℓ (Fin.castSucc (oR 2)) = ⊤ := by
    have hlow := Scheme.isLawful_comp_castAdd (S := lowerT α) (k := 2)
      (M := ((lowerT α).admittedCatalogue 2 (AdmU α)).card)
      (r := fun i ↦ (lowerT α).fieldRowOn 2 ((lowerT α).admittedCatalogue 2 (AdmU α))
        (Scheme.entryOn _ i)) (h := (I α).not_univ_two_le_doubledLower (hLR α)) hl''
    obtain ⟨hde, -, -⟩ := eq_lab_of_isLawful (isLawful_donT (hlow.isLawfulBelow pairR))
    have h2 := congrFun hde 2
    change ℓ (Fin.castSucc (oR 2)) = ℓ (Fin.castSucc (oR 0)) at h2
    rw [h2, h0, hL]
    rfl
  intro y hy
  have hone : (1 : Fin 3) ∉ Set.range (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) := by
    rintro ⟨i, hi⟩
    revert hi
    revert i
    decide
  obtain ⟨x, hx, rfl⟩ := exists_castSucc_of_mem_visibleCells isLegalBelowFullGrade_admittedT
    (isLawful_qT hα hv) (atStage_qT hv) (Nat.succ_pos 2) ⟨1, hone⟩ hy
  have hx0 := Scheme.mem_visibleCells.mp hx
  induction x using Fin.addCases with
  | right i =>
    have h1 : (admittedT α).toCellScheme.scope (Fin.natAdd _ i) = univ :=
      Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i
    exact absurd (hx0 (mem_coe.mpr (h1 ▸ mem_univ 1))) hone
  | left e =>
    have h1 : (admittedT α).toCellScheme.scope (Fin.castAdd _ e) =
        (lowerT α).toCellScheme.scope e :=
      Scheme.appendFullCellsScheme_scope_castAdd _ _ _ e
    have hsub : ((lowerT α).toCellScheme.scope e : Set (Fin 3)) ⊆
        Set.range (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) :=
      (congrArg (fun s : Finset (Fin 3) ↦ (s : Set (Fin 3))) h1).symm.subset.trans hx0
    have he : e ∈ (lowerT α).toCellScheme.below pairR := by
      refine (CellScheme.mem_below _).mpr ⟨fun p hp ↦ ?_, grade_lowerT_le e⟩
      have hp2 : p ∈ (lowerT α).toCellScheme.scope e := hp
      have hp' := hsub (mem_coe.mpr hp2)
      refine mem_erase.mpr ⟨fun h ↦ hone (by subst h; exact hp'), mem_univ _⟩
    obtain ⟨c, rfl⟩ := exists_right_of_mem_below he
    change ℓ (Fin.castSucc (oR c)) = _
    refine Eq.trans ?_ (hR c).symm
    fin_cases c
    · change ℓ (Fin.castSucc (oR 0)) = lab ⊤ ⊤ v 0
      rw [h0, hL]; rfl
    · exact he'
    · exact hz'
    · exact ho'
    · exact hr'

/-- **Cutoff determination at the twisted seed** (the first at a donor other than the context
with a new top not forced by a root top).  At a stage that is zero or a limit, with the donor
`TwistedDonor.Utop` (labels `(⊤, ⊥, ⊤, ⊤, v)`, `v` below `⊤`) and every cutoff `δ` above `v`, every
member of the receiving family of the LOW-admitted coface `MixedSeed.DU` at `δ` with face the input
`T α` has face the donor along the root `{0}` followed by the new point. -/
theorem isDeterminedWithin_DU (hα : Order.IsSuccPrelimit α) (hv : IsSelfVisible 2 v)
    (hvα : AtStage α v) (hvt : v ≠ ⊤) {δ : Label.{u}} (hvδ : v < δ) :
    IsDeterminedWithin (receivingFamily (DU hα hv) δ) (T α) Fin.castSuccEmb (Utop hv hvα) :=
  isDeterminedWithin_apexOf isLegalBelowFullGrade_admittedT (isLawful_qT hα hv) (atStage_qT hv)
    (Nat.succ_pos 2) (restrictFace_DU hα hv hvα).1 (restrictFace_DU hα hv hvα).2
    (key_DU hα hv hvα hvt hvδ)

/-- A permitted cutoff above a label below a limit stage. -/
theorem exists_permittedCutoff_gt (hα : Order.IsSuccLimit α) {w : Label.{u}}
    (hw : w < (α : Label.{u})) : ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧ w < δ := by
  induction w using WithBot.recBotCoe with
  | bot =>
    refine ⟨((0 : Ordinal.{u}) : Label.{u}), isPermittedCutoff_coe.mpr hα.bot_lt,
      WithBot.bot_lt_coe _⟩
  | coe w =>
    induction w using WithTop.recTopCoe with
    | top => exact absurd hw (not_lt.mpr le_top)
    | coe o =>
      have ho : o < α := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hw)
      obtain ⟨c, hoc, hcα, -⟩ := exists_lt_lt_isSelfVisible hα.isSuccPrelimit ho 0
      exact ⟨(c : Label.{u}), isPermittedCutoff_coe.mpr hcα,
        WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hoc)⟩

/-- **The coatom form of cutoff determination at the twisted seed.**  At a limit stage, the input
`T α` is a source-gap context of grade `2` along the root `{0}` (`Fin.castSuccEmb`), the twisted
donor `TwistedDonor.Utop` (labels `(⊤, ⊥, ⊤, ⊤, v)`, `v` below `⊤`) is a legal coface of the coatom
face of top grade at most `2`, and the LOW-admitted coface `MixedSeed.DU` with a permitted cutoff
above `v` determines the donor: the clause of `Realization.CoatomCutoffDetermination` for the
source-gap contexts at this input (root `g = id`, `tb = d` the donor). -/
theorem coatomCutoffDetermination_U (hα : Order.IsSuccLimit α) (hv : IsSelfVisible 2 v)
    (hvα : AtStage α v) (hvt : v ≠ ⊤) :
    (T α).IsSourceGapContext 2 Fin.castSuccEmb ∧ (Utop hv hvα).topGrade ≤ 2 ∧
    ∃ D' ∈ (T α).cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some (Utop hv hvα) ∧
      ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
        IsDeterminedWithin (receivingFamily D' δ) (T α) Fin.castSuccEmb (Utop hv hvα) := by
  have hvlt : v < (α : Label.{u}) := hvα.resolve_right hvt
  obtain ⟨δ, hδ, hvδ⟩ := exists_permittedCutoff_gt hα hvlt
  exact ⟨⟨1, cellT α 3, cellT α 4, isSourceGapContextAt_T α⟩,
    topGrade_le_iff.mpr fun d _ ↦ (Utop hv hvα).grade_le d,
    DU hα.isSuccPrelimit hv, mem_cofaces_DU hα.isSuccPrelimit hv hvα,
    (restrictFace_DU hα.isSuccPrelimit hv hvα).2, δ, hδ,
    isDeterminedWithin_DU hα.isSuccPrelimit hv hvα hvt hvδ⟩

end MixedSeed

end VaughtConjecture
