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
* **The cells of a proper face of a completion** (`CompletionBelowFullGrade.faceCell_completion`,
  `CompletionBelowFullGrade.rowAt_completion`,
  `CompletionBelowFullGrade.exists_castSucc_of_gradedIndex_completion`, compiled): the old cells,
  with their rows.
* **The carrier reads the new top** (`TopReadingApexExample.isTopReadingCarrier_carrierOne`,
  compiled): for every donor `d` of `rightType` along the point `3` (the root empty), the carrier
  is a top-reading carrier at the apex of `oneType` as cap and marker: in the carrier the marker is
  the old cell of the apex of `oneType` and the new top of `d` the old cell of the cell `{3}` of
  `rightType`, and every cell of graded index `(univ, 4)` reads the second at least as the first
  (`TowerProfile.rowAt_readingTop_le`).
* **Determination at a cutoff** (`TopReadingApexExample.exists_isDeterminedWithin_carrierOne`,
  compiled; through `TopReadingApexExample.exists_isDeterminedWithin_of_isTopReadingCarrier`):
  for every donor `d` of `rightType` along the point `3`, some permitted cutoff `δ` has `d`
  determined within the receiving family of the carrier at `δ`, along the empty root.  The apex of
  `oneType` is the top cap and the marker, labelled `⊤`; a member literal on `oneType` is `⊤`
  there, so `⊤` at the new top of `d`.
* **The root `{2, 3}` fails at the carrier**
  (`TopReadingApexExample.not_isDeterminedWithin_rootTwoThree`, compiled): the carrier has no face
  along `{2, 3, 4}`, a set in neither coatom, and the carrier itself, a member of each of its
  receiving families, defeats determination along `rootTwoThree` for every donor and cutoff.
* **The clause of hollow coatom cutoff determination at one input**
  (`TopReadingApexExample.hollowCoatomCutoffDetermination_oneType`, compiled; feasibility): the
  clause `exists_coface` of `Realization.HollowCoatomCutoffDetermination` for
  `TiedRootCapRelabel.MarkedCapContextBelow'` at `t' = oneType`, the empty root, `p = faceT5` and
  `tb = rightType`: its hypotheses hold (`oneType` is an acquired context along the empty root,
  `TopReadingApexExample.markedCapContextBelow'_oneType_empty`), a donor exists, and the carrier,
  one for every donor, determines each donor at a permitted cutoff.  The roots of the clause lie in
  the common face `{0, 1, 2}`; the root `{2, 3}` of the acquired context along which the reading
  layer at `seedOne` was shown legal is not among them.

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

/-- A cell of scope the new point is a cell of the face along `extendByLast Fin.castSuccEmb`, of
scope the last point there. -/
theorem exists_faceCell_right_of_scope {D : StageType.{u} α (k + 2)}
    {tb : StageType.{u} α (k + 1)} (hR : restrictFace (extendByLast Fin.castSuccEmb) D = some tb)
    {x : Fin D.card} (hx : D.toCellScheme.scope x = {Fin.last (k + 1)}) :
    ∃ z, faceCell hR z = x ∧ tb.toCellScheme.scope z = {Fin.last k} := by
  obtain ⟨z, hz⟩ := D.toScheme.exists_faceCell_eq (comap_toScheme_of_restrictFace hR) (d := x)
    (Scheme.mem_visibleCells.mpr fun y hy ↦ by
      rw [hx, coe_singleton, Set.mem_singleton_iff] at hy
      exact ⟨Fin.last k, hy ▸ extendByLast_last _⟩)
  refine ⟨z, hz, map_injective (extendByLast Fin.castSuccEmb) ?_⟩
  rw [← scope_faceCell hR z, map_singleton, extendByLast_last]
  exact (congrArg D.toCellScheme.scope hz).trans hx

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

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The cells of a proper face of the completion are the old cells**: along an embedding whose
image is not the whole ground set, the cell of the completion at a cell of a face is the old cell
of the amalgam at that cell. -/
theorem faceCell_completion (F : CompletionBelowFullGrade I) (hα : Order.IsSuccPrelimit α)
    {k : ℕ} {f : Fin k ↪ Fin (m + 2)} (hf : univ.map f ≠ univ) {s : StageType.{u} α k}
    (h : StageType.restrictFace f (F.completion hα) = some s)
    (h' : StageType.restrictFace f I.amalgam = some s) (i : Fin s.card) :
    StageType.faceCell h i = Fin.castSucc (F.embed (StageType.faceCell h' i)) := by
  have hT : StageType.restrictFace f (F.truncate hα) = some s :=
    (StageType.restrictFace_addApex _ _ _ hf).symm.trans h
  have e₂ := StageType.comap_toScheme_of_restrictFace hT
  have e₃ := StageType.comap_toScheme_of_restrictFace h'
  have h₁ := Scheme.cellMap_eq_of_strictMono_of_mem_range (S := (F.truncate hα).toScheme)
    (T := (F.completion hα).toScheme) f (φ := Fin.castSucc) Fin.strictMono_castSucc
    (Scheme.appendFullCellScheme_scope_castSucc _ _)
    (StageType.mem_range_castSucc_of_addApex _ _ f hf)
    (i := Fin.cast (congrArg Scheme.card e₂).symm i)
    (k := Fin.cast (congrArg Scheme.card (StageType.comap_toScheme_of_restrictFace h)).symm i) rfl
  have h₂ := Scheme.cellMap_eq_of_strictMono_of_mem_range (S := I.amalgam.toScheme)
    (T := (F.truncate hα).toScheme) f (φ := F.embed) F.embed.strictMono F.scope_embed
    (fun z hz ↦ F.mem_range_embed z fun he ↦ hf (eq_univ_of_forall fun x ↦ by
      obtain ⟨y, rfl⟩ : x ∈ Set.range f := hz (mem_coe.mpr (he.symm ▸ mem_univ x))
      exact mem_map_of_mem _ (mem_univ y)))
    (i := Fin.cast (congrArg Scheme.card e₃).symm i)
    (k := Fin.cast (congrArg Scheme.card e₂).symm i) rfl
  exact h₁.trans (congrArg Fin.castSucc h₂)

/-- The faces of the completion are those of the amalgam. -/
theorem faces_completion (F : CompletionBelowFullGrade I) (hα : Order.IsSuccPrelimit α) :
    (F.completion hα).toCellScheme.faces = I.amalgam.toCellScheme.faces :=
  F.faces_eq

/-- The old cells of the completion read as in the completed scheme. -/
theorem rowAt_completion (F : CompletionBelowFullGrade I) (hα : Order.IsSuccPrelimit α)
    (a b : Fin F.scheme.card) :
    (F.completion hα).rowAt (Fin.castSucc a) (Fin.castSucc b) = F.scheme.rowAt a b :=
  Scheme.rowAt_of_comap (Scheme.isLowerEmbedding_castSucc _ _ F.isLegalBelowFullGrade.not_le)
    Scheme.comap_rows_castSucc a b

/-- A cell of the completion of full scope and grade below `m + 2` is an old cell. -/
theorem exists_castSucc_of_gradedIndex_completion (F : CompletionBelowFullGrade I)
    (hα : Order.IsSuccPrelimit α) {k : ℕ} (hk : k < m + 2) {u : Fin (F.completion hα).card}
    (hu : (F.completion hα).toCellScheme.gradedIndex u = (univ, k)) :
    ∃ w, Fin.castSucc w = u ∧ F.scheme.toCellScheme.gradedIndex w = (univ, k) := by
  change Fin (F.scheme.card + 1) at u
  induction u using Fin.lastCases with
  | last =>
    have h := congrArg Prod.snd hu
    change (Scheme.appendFullCellScheme _ (m + 2)).grade (Fin.last _) = k at h
    rw [Scheme.appendFullCellScheme_grade_last] at h
    omega
  | cast w =>
    refine ⟨w, rfl, ?_⟩
    change (Scheme.appendFullCellScheme _ (m + 2)).gradedIndex (Fin.castSucc w) = _ at hu
    rwa [Scheme.appendFullCellScheme_gradedIndex_castSucc] at hu

end CompletionBelowFullGrade

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

/-! ### The carrier reads the new top at least as the marker -/

/-- The only cell of `rightType` of scope `{3}` is the new top. -/
theorem eq_topOne_of_scope {z : Fin (rightType α).card}
    (hz : (rightType α).toCellScheme.scope z = {Fin.last 3}) : z = topOne := by
  have key : ∀ y : Fin 19, TwoFaceLiftCounterexample.cellScope y = {Fin.last 3} → y = 3 := by decide
  change Fin (CaseSplitCounterexample.S.{u}.card + 1) at z
  induction z using Fin.lastCases with
  | last =>
    change (Scheme.appendFullCellScheme _ 4).scope (Fin.last _) = _ at hz
    rw [Scheme.appendFullCellScheme_scope_last] at hz
    exact absurd hz (by decide)
  | cast y =>
    change (Scheme.appendFullCellScheme _ 4).scope (Fin.castSucc y) = _ at hz
    rw [Scheme.appendFullCellScheme_scope_castSucc] at hz
    exact congrArg Fin.castSucc (key y hz)

variable {g : Fin 0 ↪ Fin 3} {d : StageType.{u} α 1}

/-- The face of the amalgam of `seedOne` along the point `4` is the donor. -/
theorem restrictFace_amalgam_one (hd : restrictFace (extendByLast g) (rightType α) = some d) :
    restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (seedOne hα).amalgam = some d :=
  (congrArg (restrictFace · (seedOne hα).amalgam) (extendByLast_trans g Fin.castSuccEmb)).symm.trans
    ((restrictFace_trans _ _ _ (seedOne hα).restrictFace_right).symm.trans hd)

/-- The face of the carrier along the point `4` is the donor. -/
theorem restrictFace_carrierOne_one (hd : restrictFace (extendByLast g) (rightType α) = some d) :
    restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (carrierOne hα) = some d :=
  (congrArg (restrictFace · (carrierOne hα)) (extendByLast_trans g Fin.castSuccEmb)).symm.trans
    ((restrictFace_trans _ _ _ (restrictFace_right_carrierOne hα)).symm.trans hd)

/-- The point `4` is a proper face. -/
theorem univ_map_point_ne : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ≠ univ := by
  intro h
  have := congrArg Finset.card h
  simp at this

/-- **The marker in the carrier** is the old cell of the apex of the left coatom type. -/
theorem faceCell_marker_carrierOne :
    faceCell (carrierOne_mem_cofaces hα).2 (Fin.last _) =
      Fin.castSucc (Fin.castAdd _ (leftCell (seedOne hα) (Fin.last _))) :=
  (completionOne hα).faceCell_completion hα.isSuccPrelimit Coatom.univ_map_left_ne _
    (seedOne hα).restrictFace_left _

/-- **The new top of the donor in the carrier** is the old cell of the new top of `rightType`. -/
theorem faceCell_newTop_carrierOne (hd : restrictFace (extendByLast g) (rightType α) = some d)
    {j : Fin d.card} (hj : Fin.last 0 ∈ d.toCellScheme.scope j) :
    faceCell (restrictFace_carrierOne_one hα hd) j =
      Fin.castSucc (Fin.castAdd _
        (embed3 (seedOne hα) (faceCell (seedOne hα).restrictFace_right (topOne (α := α))))) := by
  refine ((completionOne hα).faceCell_completion hα.isSuccPrelimit univ_map_point_ne _
    (restrictFace_amalgam_one hα hd) j).trans (congrArg (fun x ↦ Fin.castSucc (Fin.castAdd _
      (embed3 (seedOne hα) x))) ?_)
  have hsj : d.toCellScheme.scope j = {Fin.last 0} :=
    eq_singleton_iff_unique_mem.mpr ⟨hj, fun x _ ↦ Subsingleton.elim _ _⟩
  have hs : (seedOne hα).amalgam.toCellScheme.scope (faceCell (restrictFace_amalgam_one hα hd) j)
      = {Fin.last 4} := by
    rw [scope_faceCell, hsj, map_singleton, extendByLast_last]
  obtain ⟨z, hz, hzs⟩ := exists_faceCell_right_of_scope (seedOne hα).restrictFace_right hs
  rw [← hz, eq_topOne_of_scope hzs]

/-- **The carrier is a top-reading carrier** for every donor of `rightType` along the point `3`,
the cap and the marker the apex of `oneType`: every cell of graded index `(univ, 4)` reads the new
top at least as the marker (`TowerProfile.rowAt_readingTop_le`). -/
theorem isTopReadingCarrier_carrierOne
    (hd : restrictFace (extendByLast g) (rightType α) = some d) :
    (oneType hα).IsTopReadingCarrier (g.trans Fin.castSuccEmb) d (Fin.last _) (Fin.last _)
      (carrierOne hα) where
  isLegal := (carrierOne_mem_cofaces hα).1
  restrictFace_castSucc := (carrierOne_mem_cofaces hα).2
  restrictFace_extendByLast := restrictFace_carrierOne_one hα hd
  reads u hu _ j hj _ := by
    obtain ⟨w, rfl, hw⟩ := (completionOne hα).exists_castSucc_of_gradedIndex_completion
      hα.isSuccPrelimit (k := 4) (by omega) (hu.trans (by rw [grade_oneType_last]))
    rw [faceCell_marker_carrierOne, faceCell_newTop_carrierOne hα hd hj]
    exact ((completionOne hα).rowAt_completion hα.isSuccPrelimit w _).trans_le
      ((rowAt_readingTop_le (grade_marker_one hα).le (fun _ hx ↦ grade_newTops_one hα hx) hw
        (mem_image_of_mem _ (mem_singleton_self _))).trans_eq
        ((completionOne hα).rowAt_completion hα.isSuccPrelimit w _).symm)

/-! ### Determination at a cutoff -/

/-- The apex of `oneType` is a top cap. -/
theorem isTopCap_oneType_last : (oneType hα).IsTopCap (Fin.last _) :=
  ⟨StageType.addApex_scope_last (t := oneBase hα) isLegalBelowFullGrade_S (by omega),
    label_oneType_last hα,
    fun x _ ↦ ((oneType hα).grade_le x).trans_eq (grade_oneType_last hα).symm⟩

/-- **The common face along the empty root**: the face of `oneType` along the empty root and the
face of the donor along its first points agree. -/
theorem exists_root_face (hd : restrictFace (extendByLast g) (rightType α) = some d) :
    ∃ t, restrictFace (g.trans Fin.castSuccEmb) (oneType hα) = some t ∧
      restrictFace Fin.castSuccEmb d = some t := by
  have hg : (restrictFace g (faceT5 α)).isSome := by
    rw [isSome_restrictFace_iff, univ_eq_empty, map_empty]
    exact (faceT5 α).isWellFormed.isPlan.empty_mem
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hg
  refine ⟨t, (restrictFace_trans _ _ _ (restrictFace_oneType hα)).symm.trans ht, ?_⟩
  refine (restrictFace_trans _ _ _ hd).trans (((congrArg (restrictFace · (rightType α))
    (castSuccEmb_trans_extendByLast g))).trans ?_)
  exact (restrictFace_trans _ _ _ (restrictFace_rightType α)).symm.trans ht

/-- **Cutoff determination at `oneType` from a top-reading carrier**: a top-reading carrier over
`oneType` for a donor of `rightType` along the point `3`, with cap and marker the apex, is a coface
of `oneType`, and determines the donor within its receiving family at a permitted cutoff. -/
theorem exists_isDeterminedWithin_of_isTopReadingCarrier
    (hd : restrictFace (extendByLast g) (rightType α) = some d) {D : StageType.{u} α 5}
    (hD : (oneType hα).IsTopReadingCarrier (g.trans Fin.castSuccEmb) d (Fin.last _)
      (Fin.last _) D) :
    D ∈ (oneType hα).cofaces ∧ ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
      IsDeterminedWithin (receivingFamily D δ) (oneType hα) (g.trans Fin.castSuccEmb) d := by
  obtain ⟨t, ht, htd⟩ := exists_root_face hα hd
  obtain ⟨δ, hδ, hδD⟩ := exists_isPermittedCutoff_gt hα D
  exact ⟨⟨hD.isLegal, hD.restrictFace_castSucc⟩, δ, hδ,
    isDeterminedWithin_receivingFamily_of_isTopReadingCarrier ht htd (isTopCap_oneType_last hα)
      (label_oneType_last hα) (by rw [grade_oneType_last]; omega) hD hδD⟩

/-- **The carrier determines every donor of `rightType` along the point `3` at a cutoff**
(`TopReadingApexExample.exists_isDeterminedWithin_of_isTopReadingCarrier` at
`TopReadingApexExample.isTopReadingCarrier_carrierOne`). -/
theorem exists_isDeterminedWithin_carrierOne
    (hd : restrictFace (extendByLast g) (rightType α) = some d) :
    ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
      IsDeterminedWithin (receivingFamily (carrierOne hα) δ) (oneType hα)
        (g.trans Fin.castSuccEmb) d :=
  (exists_isDeterminedWithin_of_isTopReadingCarrier hα hd
    (isTopReadingCarrier_carrierOne hα hd)).2

/-- **The root `{2, 3}` is not a root at the carrier**: the face of the carrier along `{2, 3, 4}`
is undefined, as every face of the amalgam of a seed other than the ground set lies in one of the
two coatoms. -/
theorem restrictFace_rootTwoThree_carrierOne :
    restrictFace (extendByLast rootTwoThree) (carrierOne hα) = none := by
  rw [restrictFace_eq_none_iff]
  intro hB
  have hB' : univ.map (extendByLast rootTwoThree) ∈ (seedOne hα).amalgam.toCellScheme.faces :=
    (completionOne hα).faces_completion hα.isSuccPrelimit ▸ hB
  have hne : univ.map (extendByLast rootTwoThree) ≠ univ := by
    intro h
    have := congrArg Finset.card h
    simp at this
  rcases (seedOne hα).subset_or_subset _ hB' hne with h | h
  · exact (mem_erase.mp (h (mem_map_of_mem _ (mem_univ (Fin.last 2))))).1
      (extendByLast_last _)
  · exact (mem_erase.mp (h (mem_map_of_mem _ (mem_univ (Fin.castSucc 1))))).1
      ((extendByLast_castSucc _ _).trans rfl)

/-- **Determination at the root `{2, 3}` fails at the carrier**: the carrier is a member of each
of its receiving families with face `oneType`, and has no face along `{2, 3, 4}`. -/
theorem not_isDeterminedWithin_rootTwoThree (e : StageType.{u} α 3) (δ : Label.{u}) :
    ¬ IsDeterminedWithin (receivingFamily (carrierOne hα) δ) (oneType hα) rootTwoThree e :=
  fun h ↦ by
    have := h (carrierOne hα) ⟨rfl, fun i j hij ↦ by rw [Fin.ext hij]⟩ (carrierOne_mem_cofaces hα).2
    rw [restrictFace_rootTwoThree_carrierOne] at this
    exact absurd this (by simp)

/-! ### The clause of hollow coatom cutoff determination at `oneType` and `rightType` -/

/-- No cell of `oneType` is visible through the empty root: every scope is nonempty. -/
theorem not_mem_visibleCells_oneType (y : Fin (oneType hα).card) :
    y ∉ (oneType hα).visibleCells (g.trans Fin.castSuccEmb) := fun hy ↦ by
  have key : ∀ a : Fin 19, (TwoFaceLiftCounterexample.cellScope a).Nonempty := by decide
  have hne : ((oneType hα).toCellScheme.scope y).Nonempty := by
    rcases cases_oneType hα y with rfl | ⟨a, rfl⟩
    · exact ⟨0, Eq.mpr (congrArg (0 ∈ ·) (StageType.addApex_scope_last (t := oneBase hα)
        isLegalBelowFullGrade_S (by omega))) (mem_univ _)⟩
    · exact Eq.mpr (congrArg Finset.Nonempty
        (congrArg Prod.fst (gradedIndex_oneType_castSucc hα a))) (key a)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨i, -⟩ := Scheme.mem_visibleCells.mp hy (mem_coe.mpr hx)
  exact i.elim0

/-- `oneType` is an acquired marked-cap context respecting the root bottoms along the empty root
(`StageType.markedCapContextBelow'_addApex`, its conditions on the root cells vacuous). -/
theorem markedCapContextBelow'_oneType_empty :
    TiedRootCapRelabel.MarkedCapContextBelow' (oneType hα) (g.trans Fin.castSuccEmb) :=
  StageType.markedCapContextBelow'_addApex (t₀ := oneBase hα) isLegalBelowFullGrade_S
    (by omega) (by omega) (fun y hy ↦ absurd hy (not_mem_visibleCells_oneType hα y))
    fun y hy ↦ absurd hy (not_mem_visibleCells_oneType hα y)

/-- `rightType` has a donor along the point `3`: its face along `{3}` is defined, `{3}` the scope of
the new top. -/
theorem exists_donor_rightType (g : Fin 0 ↪ Fin 3) :
    ∃ d : StageType.{u} α 1, restrictFace (extendByLast g) (rightType α) = some d := by
  have hs : (rightType α).toCellScheme.scope (topOne (α := α)) = {Fin.last 3} := by
    change (Scheme.appendFullCellScheme CaseSplitCounterexample.S 4).scope
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) = _
    rw [Scheme.appendFullCellScheme_scope_castSucc]
    decide
  have hm : univ.map (extendByLast g) = {Fin.last 3} := by
    rw [show (univ : Finset (Fin (0 + 1))) = {Fin.last 0} by decide, map_singleton,
      extendByLast_last]
  have hf : univ.map (extendByLast g) ∈ (rightType α).toCellScheme.faces := by
    rw [hm, ← hs]
    exact (rightType α).isWellFormed.isWellFormed.scope_mem _
  exact Option.isSome_iff_exists.mp ((isSome_restrictFace_iff _ _).mpr hf)

/-- **The clause of hollow coatom cutoff determination for acquired contexts at `oneType` and
`rightType`** (feasibility, one input): the clause `exists_coface` of
`Realization.HollowCoatomCutoffDetermination` for `TiedRootCapRelabel.MarkedCapContextBelow'` at
`t' = oneType`, the empty root `g`, `p = faceT5` and `tb = rightType`.  Its hypotheses hold, a donor
exists, and for every donor `d` the carrier `TopReadingApexExample.carrierOne`, the same for every
donor, is a coface of `oneType` with face `rightType` determining `d` at a permitted cutoff. -/
theorem hollowCoatomCutoffDetermination_oneType (g : Fin 0 ↪ Fin 3) :
    (oneType hα).IsLegal ∧
      TiedRootCapRelabel.MarkedCapContextBelow' (oneType hα) (g.trans Fin.castSuccEmb) ∧
      restrictFace Fin.castSuccEmb (oneType hα) = some (faceT5 α) ∧
      rightType α ∈ (faceT5 α).cofaces ∧
      (∃ d : StageType.{u} α 1, restrictFace (extendByLast g) (rightType α) = some d) ∧
      ∀ d : StageType.{u} α 1, restrictFace (extendByLast g) (rightType α) = some d →
        ∃ D' ∈ (oneType hα).cofaces,
          restrictFace (extendByLast Fin.castSuccEmb) D' = some (rightType α) ∧
          ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
            IsDeterminedWithin (receivingFamily D' δ) (oneType hα) (g.trans Fin.castSuccEmb) d :=
  ⟨isLegal_oneType hα, markedCapContextBelow'_oneType_empty hα, restrictFace_oneType hα,
    ⟨isLegal_rightType α, restrictFace_rightType α⟩, exists_donor_rightType g,
    fun _ hd ↦ ⟨carrierOne hα, carrierOne_mem_cofaces hα, restrictFace_right_carrierOne hα,
      exists_isDeterminedWithin_carrierOne hα hd⟩⟩

end TopReadingApexExample

end VaughtConjecture
