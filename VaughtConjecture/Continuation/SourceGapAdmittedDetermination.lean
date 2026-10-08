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

**The key step** (`MixedSeed.key_DU`, for an admission).  Let `ℓ` be a lawful labelling of the
scheme of the admitted coface `MixedSeed.DU`, agreeing with the coface at the cells visible through
the context face (the input `T`) and with it capped at a cutoff `δ > ⊥` everywhere.  Then `ℓ`
agrees with the coface at the cells visible through the donor face (the donor copies of the input,
`MixedSeed.exists_right_of_mem_below`), provided the admitted completion determines `o'` and `r'`:
at `y'` (shared with the context), by the context face; at `e'` (`⊥`), by the agreement below `δ`;
at `z'`, by lawfulness of the donor face (`z = y`, `SeparationObstruction.eq_lab_of_isLawful`).  For
the owner-as-partner clause, `r'` (`v`) by the agreement below `δ > v` and `o'` by
`MixedSeed.eq_top_of_admittedT` (`o` at `⊤`, `r'` below `⊤`).

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

**The self donor** (`MixedSeed.isDeterminedWithin_DS`, `MixedSeed.coatomCutoffDetermination_T`):
with the self-seed clause `SeparationObstruction.LowViaSelf` and `v = ⊤` (the twisted donor is then
the input, `MixedSeed.utop_top_eq_T`), `o'` and `r'` are `⊤` by
`MixedSeed.eq_top_of_admittedSelf`, so at a limit stage the input is determined over itself within
the receiving family of the self-admitted coface at every permitted cutoff: the clause of the
coatom cutoff determination at this input with the donor the input.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

/-! ### Cutoff determination at the twisted seed -/

namespace MixedSeed

open StageType SeparationObstruction TwistedDonor

variable {α : Ordinal.{u}} {v : Label.{u}} {Adm : (Fin 5 → Label.{u}) → (Fin 5 → Label.{u}) → Prop}

variable (Adm) in
/-- The old cell of the admitted completion over the context copy of `z`. -/
noncomputable abbrev oL (z : Fin 5) : Fin (admittedBy α Adm).card :=
  Fin.castAdd _ (Fin.castAdd _ (lc α z))

variable (Adm) in
/-- The old cell of the admitted completion over the donor copy of `z`. -/
noncomputable abbrev oR (z : Fin 5) : Fin (admittedBy α Adm).card :=
  Fin.castAdd _ (Fin.castAdd _ (rc α z))

variable (Adm) in
theorem scope_oL (z : Fin 5) :
    (admittedBy α Adm).toCellScheme.scope (oL Adm z) = (cells.scope z).map (Coatom.left 1) :=
  ((Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
    (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _)).trans
    (congrArg Prod.fst (gradedIndex_lc z))

/-- The admitted coface, as the stage type of the admitted completion with the apex. -/
noncomputable abbrev apexDU (hA : IsLowAdmission Adm) (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v))
    (hα : Order.IsSuccPrelimit α) (hv : IsSelfVisible 2 v) : StageType.{u} α 3 :=
  apexOf (isLegalBelowFullGrade_admittedBy hA) (isLawful_qT hA hα hv hst) (atStage_qT hA hv hst)
    (Nat.succ_pos 2)

/-- **The key step**, for an admission: let `ℓ` be a lawful labelling of the admitted coface
agreeing with it on the context face and capped at a cutoff `δ > ⊥`.  If every lawful labelling of
the admitted completion with the labels of the input on the context copy, agreeing with
`(⊤, ⊥, ⊤, ⊤, v)` on the donor copy capped at `δ`, has the donor's `o'` and `r'` of
`(⊤, ⊥, ⊤, ⊤, v)` (`hdet`), then `ℓ` agrees with the coface on the donor face: at `y'` by the
context face, at `e'` by the cap, at `z'` by lawfulness (`z = y`), at `o'` and `r'` by `hdet`. -/
theorem key_DU (hA : IsLowAdmission Adm) (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v))
    (hα : Order.IsSuccPrelimit α) (hv : IsSelfVisible 2 v) (hvα : AtStage α v) {δ : Label.{u}}
    (hδ : ⊥ < δ)
    (hdet : ∀ q : Fin (admittedBy α Adm).card → Label.{u}, (admittedBy α Adm).rows.IsLawful q →
      (∀ z, q (oL Adm z) = lab ⊤ ⊤ ⊤ z) → (∀ z, min (q (oR Adm z)) δ = min (lab ⊤ ⊤ v z) δ) →
      q (oR Adm 3) = lab ⊤ ⊤ v 3 ∧ q (oR Adm 4) = lab ⊤ ⊤ v 4)
    (ℓ : Fin ((admittedBy α Adm).card + 1) → Label.{u})
    (hl : (apexDU hA hst hα hv).rows.IsLawful ℓ)
    (hleft : ∀ x ∈ (apexDU hA hst hα hv).toScheme.visibleCells Fin.castSuccEmb,
      ℓ x = (apexDU hA hst hα hv).label x)
    (hag : ∀ x, min (ℓ x) δ = min ((apexDU hA hst hα hv).label x) δ) :
    ∀ y ∈ (apexDU hA hst hα hv).toScheme.visibleCells (extendByLast Fin.castSuccEmb),
      ℓ y = (apexDU hA hst hα hv).label y := by
  have hlab (x : Fin (admittedBy α Adm).card) :
      (apexDU hA hst hα hv).label (Fin.castSucc x) = qT hA hv hst x :=
    apexOf_label_castSucc (isLegalBelowFullGrade_admittedBy hA) (isLawful_qT hA hα hv hst)
      (atStage_qT hA hv hst) (Nat.succ_pos 2) x
  have hL (z : Fin 5) : ℓ (Fin.castSucc (oL Adm z)) = lab ⊤ ⊤ ⊤ z := by
    have hoL : oL (α := α) Adm z ∈ (admittedBy α Adm).visibleCells Fin.castSuccEmb := by
      refine Scheme.mem_visibleCells.mpr fun x hx ↦ ?_
      have hx' : x ∈ (cells.scope z).map (Coatom.left 1) := by
        rw [← scope_oL Adm z]; exact hx
      obtain ⟨y, -, rfl⟩ := mem_map.mp hx'
      exact ⟨y, rfl⟩
    have hmem := apexOf_castSucc_mem_visibleCells (isLegalBelowFullGrade_admittedBy hA)
      (isLawful_qT hA hα hv hst) (atStage_qT hA hv hst) (Nat.succ_pos 2) hoL
    exact ((hleft _ hmem).trans (hlab (oL Adm z))).trans (qT_lc hA hv hst z)
  have hR (z : Fin 5) : (apexDU hA hst hα hv).label (Fin.castSucc (oR Adm z)) = lab ⊤ ⊤ v z := by
    rw [hlab, qT_rc hA hv hvα hst]
  have hl'' : (admittedBy α Adm).rows.IsLawful (ℓ ∘ Fin.castSucc) :=
    isLawful_castSucc_addApex (t := ofLegalBelow (admittedBy α Adm)
      (isLegalBelowFullGrade_admittedBy hA) (qT hA hv hst) (isLawful_qT hA hα hv hst)
      (atStage_qT hA hv hst)) (isLegalBelowFullGrade_admittedBy hA) (Nat.succ_pos 2) hl
  have hcap (z : Fin 5) : min (ℓ (Fin.castSucc (oR Adm z))) δ = min (lab ⊤ ⊤ v z) δ :=
    (hag (Fin.castSucc (oR Adm z))).trans (congrArg (fun t ↦ min t δ) (hR z))
  obtain ⟨ho', hr'⟩ := hdet (ℓ ∘ Fin.castSucc) hl'' hL hcap
  have he' : ℓ (Fin.castSucc (oR Adm 1)) = ⊥ := by
    have e := hcap 1
    change min (ℓ (Fin.castSucc (oR Adm 1))) δ = min ⊥ δ at e
    rw [min_bot_left] at e
    rcases min_eq_bot.mp e with h | h
    · exact h
    · exact absurd h hδ.ne'
  have h0 : oR (α := α) Adm 0 = oL Adm 0 := by rw [oR, oL, lc_zero]
  have hz' : ℓ (Fin.castSucc (oR Adm 2)) = ⊤ := by
    have hlow := Scheme.isLawful_comp_castAdd (S := lowerT α) (k := 2)
      (M := ((lowerT α).admittedCatalogue 2 (AdmBy α Adm)).card)
      (r := fun i ↦ (lowerT α).fieldRowOn 2 ((lowerT α).admittedCatalogue 2 (AdmBy α Adm))
        (Scheme.entryOn _ i)) (h := (I α).not_univ_two_le_doubledLower (hLR α)) hl''
    obtain ⟨hde, -, -⟩ := eq_lab_of_isLawful (isLawful_donT (hlow.isLawfulBelow pairR))
    have h2 := congrFun hde 2
    change ℓ (Fin.castSucc (oR Adm 2)) = ℓ (Fin.castSucc (oR Adm 0)) at h2
    rw [h2, h0, hL]
    rfl
  intro y hy
  have hone : (1 : Fin 3) ∉ Set.range (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) := by
    rintro ⟨i, hi⟩
    revert hi
    revert i
    decide
  obtain ⟨x, hx, rfl⟩ := exists_castSucc_of_mem_visibleCells (isLegalBelowFullGrade_admittedBy hA)
    (isLawful_qT hA hα hv hst) (atStage_qT hA hv hst) (Nat.succ_pos 2) ⟨1, hone⟩ hy
  have hx0 := Scheme.mem_visibleCells.mp hx
  induction x using Fin.addCases with
  | right i =>
    have h1 : (admittedBy α Adm).toCellScheme.scope (Fin.natAdd _ i) = univ :=
      Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i
    exact absurd (hx0 (mem_coe.mpr (h1 ▸ mem_univ 1))) hone
  | left e =>
    have h1 : (admittedBy α Adm).toCellScheme.scope (Fin.castAdd _ e) =
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
    change ℓ (Fin.castSucc (oR Adm c)) = _
    refine Eq.trans ?_ (hR c).symm
    fin_cases c
    · change ℓ (Fin.castSucc (oR Adm 0)) = lab ⊤ ⊤ v 0
      rw [h0, hL]; rfl
    · exact he'
    · exact hz'
    · exact ho'
    · exact hr'

/-- **Cutoff determination at the seed, for an admission**: from the determination of `o'` and `r'`
in the admitted completion (`hdet`), the donor `(⊤, ⊥, ⊤, ⊤, v)` is determined over the input along
the root `{0}` within the receiving family of the admitted coface at `δ > ⊥`. -/
theorem isDeterminedWithin_DU_of (hA : IsLowAdmission Adm) (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v))
    (hα : Order.IsSuccPrelimit α) (hv : IsSelfVisible 2 v) (hvα : AtStage α v) {δ : Label.{u}}
    (hδ : ⊥ < δ)
    (hdet : ∀ q : Fin (admittedBy α Adm).card → Label.{u}, (admittedBy α Adm).rows.IsLawful q →
      (∀ z, q (oL Adm z) = lab ⊤ ⊤ ⊤ z) → (∀ z, min (q (oR Adm z)) δ = min (lab ⊤ ⊤ v z) δ) →
      q (oR Adm 3) = lab ⊤ ⊤ v 3 ∧ q (oR Adm 4) = lab ⊤ ⊤ v 4) :
    IsDeterminedWithin (receivingFamily (DU hA hst hα hv) δ) (T α) Fin.castSuccEmb
      (Utop hv hvα) :=
  isDeterminedWithin_apexOf (isLegalBelowFullGrade_admittedBy hA) (isLawful_qT hA hα hv hst)
    (atStage_qT hA hv hst) (Nat.succ_pos 2) (restrictFace_DU hA hst hα hv hvα).1
    (restrictFace_DU hA hst hα hv hvα).2 (key_DU hA hst hα hv hvα hδ hdet)

/-- **Cutoff determination at the twisted seed** (the first at a donor other than the context
with a new top not forced by a root top).  At a stage that is zero or a limit, with the donor
`TwistedDonor.Utop` (labels `(⊤, ⊥, ⊤, ⊤, v)`, `v` below `⊤`) and every cutoff `δ` above `v`, every
member of the receiving family of the LOW-admitted coface (the owner-as-partner admission) at `δ`
with face the input `T α` has face the donor along the root `{0}` followed by the new point:
`r'` is `v` by the cap, and `o'` is `⊤` by `MixedSeed.eq_top_of_admittedT`. -/
theorem isDeterminedWithin_DU (hα : Order.IsSuccPrelimit α) (hv : IsSelfVisible 2 v)
    (hvα : AtStage α v) (hvt : v ≠ ⊤) {δ : Label.{u}} (hvδ : v < δ) :
    IsDeterminedWithin (receivingFamily (DU isLowAdmission_lowVia (lowVia_Utop v) hα hv) δ) (T α)
      Fin.castSuccEmb (Utop hv hvα) := by
  refine isDeterminedWithin_DU_of isLowAdmission_lowVia (lowVia_Utop v) hα hv hvα
    (bot_le.trans_lt hvδ) fun q hq hqL hqc ↦ ?_
  have hr' : q (oR LowVia 4) = v := Label.eq_of_min_eq_of_lt (hqc 4).symm hvδ
  refine ⟨?_, hr'⟩
  exact eq_top_of_admittedT (hq.isLawfulBelow _) (hqL 3)
    (by rw [hr']; exact lt_top_iff_ne_top.mpr hvt)

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
    DU isLowAdmission_lowVia (lowVia_Utop v) hα.isSuccPrelimit hv,
    mem_cofaces_DU isLowAdmission_lowVia (lowVia_Utop v) hα.isSuccPrelimit hv hvα,
    (restrictFace_DU isLowAdmission_lowVia (lowVia_Utop v) hα.isSuccPrelimit hv hvα).2, δ, hδ,
    isDeterminedWithin_DU hα.isSuccPrelimit hv hvα hvt hvδ⟩

/-! ### The self donor -/

/-- The twisted donor with `v = ⊤` is the input. -/
theorem utop_top_eq_T : Utop (α := α) (isSelfVisible_top 2) (Or.inr rfl) = T α :=
  StageType.ext rfl fun i j hij ↦ by
    obtain rfl : i = j := Fin.ext hij
    rfl

/-- **Cutoff determination at the self seed**: at a stage that is zero or a limit and every cutoff
`δ > ⊥`, the input `T α` is determined over itself along the root `{0}` within the receiving family
of the coface admitted by the self-seed clause `SeparationObstruction.LowViaSelf`: `o'` and `r'`
are `⊤` by `MixedSeed.eq_top_of_admittedSelf` (`e'` is `⊥`, below `⊤ = o`). -/
theorem isDeterminedWithin_DS (hα : Order.IsSuccPrelimit α) {δ : Label.{u}} (hδ : ⊥ < δ) :
    IsDeterminedWithin (receivingFamily (DU isLowAdmission_lowViaSelf lowViaSelf_T hα
      (isSelfVisible_top 2)) δ) (T α) Fin.castSuccEmb (T α) := by
  rw [← utop_top_eq_T]
  refine isDeterminedWithin_DU_of isLowAdmission_lowViaSelf lowViaSelf_T hα (isSelfVisible_top 2)
    (Or.inr rfl) hδ fun q hq hqL _ ↦ ?_
  obtain ⟨-, h3, h4⟩ := eq_top_of_admittedSelf (hq.isLawfulBelow _) (hqL 3)
  exact ⟨h3, h4⟩

/-- **The coatom form of cutoff determination at the self seed.**  At a limit stage, the input
`T α` is a source-gap context of grade `2` along the root `{0}`, a legal coface of its coatom face
of top grade at most `2`, and the coface admitted by the self-seed clause with a permitted cutoff
determines it: the clause of `Realization.CoatomCutoffDetermination` for the source-gap contexts at
this input with the donor the input itself. -/
theorem coatomCutoffDetermination_T (hα : Order.IsSuccLimit α) :
    (T α).IsSourceGapContext 2 Fin.castSuccEmb ∧ (T α).topGrade ≤ 2 ∧
    ∃ D' ∈ (T α).cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some (T α) ∧
      ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
        IsDeterminedWithin (receivingFamily D' δ) (T α) Fin.castSuccEmb (T α) := by
  obtain ⟨δ, hδ, hδ0⟩ := exists_permittedCutoff_gt hα (w := ⊥) (WithBot.bot_lt_coe _)
  have hface := (restrictFace_DU isLowAdmission_lowViaSelf lowViaSelf_T hα.isSuccPrelimit
    (isSelfVisible_top 2) (Or.inr rfl)).2
  rw [utop_top_eq_T] at hface
  exact ⟨⟨1, cellT α 3, cellT α 4, isSourceGapContextAt_T α⟩,
    topGrade_le_iff.mpr fun d _ ↦ (T α).grade_le d,
    DU isLowAdmission_lowViaSelf lowViaSelf_T hα.isSuccPrelimit (isSelfVisible_top 2),
    mem_cofaces_DU isLowAdmission_lowViaSelf lowViaSelf_T hα.isSuccPrelimit
      (isSelfVisible_top 2) (Or.inr rfl), hface, δ, hδ,
    isDeterminedWithin_DS hα.isSuccPrelimit hδ0⟩

end MixedSeed

end VaughtConjecture
