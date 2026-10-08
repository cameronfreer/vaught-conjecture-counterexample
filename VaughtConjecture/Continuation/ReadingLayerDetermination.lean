/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerAcquired
import VaughtConjecture.Continuation.TopReadingCarrier

/-!
# Determination at a cutoff at the acquired context `oneType`

Roadmap, Layer 3 ((R3) of the table of 3.4).

* **Copied lemmas** (`StageType.exists_faceCell_eq`, `StageType.exists_isPermittedCutoff_gt`,
  `StageType.isDeterminedWithin_receivingFamily_iff`, compiled in this repository (theorem named);
  `Realization.HollowCoatomCutoffDetermination`, defined here): faces as cells, a permitted cutoff
  above the labels other than `⊤`, determination at a cutoff as the top clause, and the statement
  of hollow coatom cutoff determination.
* **The carrier** (`TopReadingApexExample.completionOne`, `TopReadingApexExample.carrierOne`,
  defined here; `TopReadingApexExample.carrierOne_mem_cofaces`,
  `TopReadingApexExample.restrictFace_right_carrierOne`, compiled): the restricted reading layer at
  `seedOne` with the glued labelling, as a completion below the full grade, and the apex added: a
  legal coface of `oneType` whose face along `extendByLast Fin.castSuccEmb` is `rightType`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Permitted cutoffs and determination at a cutoff -/

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ}

/-- Every cell visible through `h` is a cell of the face along `h`. -/
theorem exists_faceCell_eq {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} (ht : restrictFace h t' = some t) {i : Fin t'.card}
    (hi : i ∈ t'.visibleCells h) : ∃ y, faceCell ht y = i := by
  obtain ⟨z, rfl⟩ : i ∈ Set.range (t'.toScheme.cellMap h) := by
    rw [Scheme.range_cellMap]
    exact hi
  exact ⟨Fin.cast (congrArg Scheme.card (comap_toScheme_of_restrictFace ht)) z, by
    simp [faceCell, Scheme.faceCell]⟩

/-- **A permitted cutoff above the labels other than `⊤`**: at a limit stage, the labels of a
stage type other than `⊤` lie below some permitted cutoff. -/
theorem exists_isPermittedCutoff_gt (hα : Order.IsSuccLimit α) {k : ℕ}
    (D : StageType.{u} α k) :
    ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧ ∀ j, D.label j ≠ ⊤ → D.label j < δ := by
  have h0 : ((0 : Ordinal.{u}) : Label.{u}) < α :=
    WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hα.bot_lt)
  obtain ⟨c, h0c, hcα, -, hc⟩ := exists_isSelfVisible_bound hα.isSuccPrelimit 0 h0 D.label
  induction c using recBotCoeTop with
  | bot => exact absurd h0c (not_le.mpr (WithBot.bot_lt_coe _))
  | top => exact absurd hcα (not_lt.mpr le_top)
  | coe o =>
    have hoα : o < α := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hcα)
    refine ⟨((o + 1 : Ordinal.{u}) : Label.{u}), ⟨WithBot.bot_lt_coe _, ?_⟩, fun j hj ↦ ?_⟩
    · exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (hα.add_one_lt hoα))
    · have hjα : D.label j < α := (D.atStage j).resolve_right hj
      exact (hc j hjα).trans_lt
        (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (Order.lt_add_one_iff.mpr le_rfl)))

/-- **Determination at a cutoff is the top clause.**  Let `D` restrict along `extendByLast h` to
`d`, and let `δ` lie above every label of `D` other than `⊤`.  The donor is determined within the
receiving family of `D` at `δ` exactly when every member literal on `t'` is `⊤` at every cell of
`d` labelled `⊤`.  The members agree with `D` below `δ`, hence with `d` at every cell of `d`
labelled other than `⊤`; at a cell of `d` labelled `⊤` they are only asked to be at least `δ`. -/
theorem isDeterminedWithin_receivingFamily_iff {k n : ℕ} {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)} {D : StageType.{u} α (k + 1)}
    (h₂ : restrictFace (extendByLast h) D = some d) {δ : Label.{u}}
    (hδ : ∀ j, D.label j ≠ ⊤ → D.label j < δ) :
    IsDeterminedWithin (receivingFamily D δ) t' h d ↔
      ∀ q ∈ receivingFamily D δ, restrictFace Fin.castSuccEmb q = some t' →
        ∀ (i : Fin q.card) (j : Fin d.card), (i : ℕ) = faceCell h₂ j → d.label j = ⊤ →
          q.label i = ⊤ := by
  constructor
  · rintro hdet ⟨S, ℓ, hw, hcod, hl, hat⟩ hq hq₁ i j hij hj
    have hq₂ := hdet _ hq hq₁
    obtain ⟨hS, -⟩ := hq
    change S = D.toScheme at hS
    subst hS
    obtain rfl : i = faceCell h₂ j := Fin.ext hij
    exact (label_faceCell hq₂ j).trans hj
  · rintro H ⟨S, ℓ, hw, hcod, hl, hat⟩ hq hq₁
    have H' := H _ hq hq₁
    obtain ⟨hS, hcut⟩ := hq
    change S = D.toScheme at hS
    subst hS
    refine (restrictFace_congr_label (t := ⟨D.toScheme, ℓ, hw, hcod, hl, hat⟩) (s := D) rfl
      fun i j hij hi ↦ ?_).trans h₂
    obtain rfl : i = j := Fin.ext hij
    obtain ⟨z, rfl⟩ := exists_faceCell_eq h₂ hi
    change ℓ (faceCell h₂ z) = D.label (faceCell h₂ z)
    by_cases hz : d.label z = ⊤
    · exact (H' _ z rfl hz).trans ((label_faceCell h₂ z).trans hz).symm
    · have hlt : D.label (faceCell h₂ z) < δ := hδ _ (by rw [label_faceCell]; exact hz)
      have hmin : min (ℓ (faceCell h₂ z)) δ = D.label (faceCell h₂ z) :=
        (hcut _ _ rfl).trans (min_eq_left hlt.le)
      have hℓ : ℓ (faceCell h₂ z) < δ :=
        (min_lt_iff.mp (hmin ▸ hlt)).resolve_right (lt_irrefl δ)
      rw [← hmin, min_eq_left hℓ.le]

end StageType

namespace Realization

open StageType

/-- **Hollow coatom cutoff determination** for `P`: the statement of `CoatomCutoffDetermination`
without the bound on the top grade of the donor.  Not proved for any `P` here. -/
structure HollowCoatomCutoffDetermination
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop) : Prop where
  /-- Every donor through a coface of the coatom face is determined at a cutoff. -/
  exists_coface ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α (k + 1))
    (g : Fin n ↪ Fin k) (p : StageType.{u} α k) :
    Order.IsSuccLimit α → t'.IsLegal → P t' (g.trans Fin.castSuccEmb) →
      restrictFace Fin.castSuccEmb t' = some p → ∀ tb ∈ p.cofaces, ∀ d : StageType.{u} α (n + 1),
        restrictFace (extendByLast g) tb = some d →
          ∃ D' ∈ t'.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
            ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
              IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d

end Realization

/-! ### The completion at `seedOne` and its carrier -/

namespace TopReadingApexExample

open TwoFaceLiftExistsCounterexample CaseSplitCounterexample TowerProfile StageType

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- The new top: the cell `{3}` of `rightType`. -/
noncomputable abbrev topOne : Fin (rightType α).card :=
  Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)

/-- The glued labelling of `seedOne` on the profile layer. -/
noncomputable def gluedOne : Fin (scheme (seedOne hα)).card → Label.{u} :=
  fun d ↦ (exists_isLawful_top (I := seedOne hα)).choose (Fin.castAdd _ d)

theorem isLawfulBelow_gluedOne :
    (scheme (seedOne hα)).rows.IsLawfulBelow (univ, 4) fun d ↦ gluedOne hα d := by
  have hq := (exists_isLawful_top (I := seedOne hα)).choose_spec.1
  have hL := hq.comap (Scheme.isLowerEmbedding_fieldLayer (scheme (seedOne hα)) 4
    not_univ_four_le)
  rw [Scheme.comap_rows_fieldLayer] at hL
  exact hL.isLawfulBelow _

theorem gluedOne_embed3 (d : Fin (seedOne hα).amalgam.card) :
    gluedOne hα (embed3 (seedOne hα) d) = (seedOne hα).amalgam.label d :=
  (exists_isLawful_top (I := seedOne hα)).choose_spec.2 d

theorem grade_marker_one :
    (scheme (seedOne hα)).toCellScheme.grade (leftCell (seedOne hα) (Fin.last _)) = 4 :=
  (grade_leftCell (I := seedOne hα) _).trans (grade_oneType_last hα)

theorem grade_newTops_one {x : Fin (scheme (seedOne hα)).card}
    (hx : x ∈ newTops (seedOne hα) (topOne (α := α))) :
    (scheme (seedOne hα)).toCellScheme.grade x ≤ 4 := by
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
  rw [← CellScheme.gradedIndex_snd, gradedIndex_embed3, CellScheme.gradedIndex_snd]
  exact (StageType.grade_faceCell _ _).trans_le ((seedOne hα).right.grade_le _)

/-- **The completion below the full grade at `seedOne` through the restricted reading layer**
(`TowerProfile.readingCompletion`, the layer legal by
`TopReadingApexExample.isLegalBelowFullGrade_readingTop_seedOne`). -/
noncomputable def completionOne : CompletionBelowFullGrade (seedOne hα) :=
  readingCompletion (seedOne hα) _ _ (isLegalBelowFullGrade_readingTop_seedOne hα)
    (grade_marker_one hα).le (fun _ hx ↦ grade_newTops_one hα hx) (gluedOne hα)
    (isLawfulBelow_gluedOne hα)
    (fun x hx ↦ by
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      rw [mem_singleton.mp hz, gluedOne_embed3]
      exact le_of_le_of_eq le_top
        ((StageType.label_faceCell _ _).trans (rightNewTop_rightType α).label_eq).symm)
    (gluedOne_embed3 hα)

/-- **The carrier**: the completion of `seedOne`, the apex added. -/
noncomputable def carrierOne : StageType.{u} α 5 :=
  (completionOne hα).completion hα.isSuccPrelimit

theorem carrierOne_mem_cofaces : carrierOne hα ∈ (oneType hα).cofaces :=
  ⟨(completionOne hα).isLegal_completion _, (completionOne hα).restrictFace_left_completion _⟩

theorem restrictFace_right_carrierOne :
    restrictFace (extendByLast Fin.castSuccEmb) (carrierOne hα) = some (rightType α) :=
  (completionOne hα).restrictFace_right_completion _

end TopReadingApexExample

end VaughtConjecture
