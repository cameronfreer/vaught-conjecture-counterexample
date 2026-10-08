/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapAdmittedSeed

/-!
# The LOW-admitted coface at the twisted seed, and cutoff determination there

Roadmap, Layer 3 ((R2) of the table of 3.4); the LOW-admitted completion of
`VaughtConjecture.Continuation.SourceGapAdmittedSeed`.

**Faces through an equality of amalgams** (`Seed.restrictFace_addApex_of_eq`).  The amalgam of the
twisted seed has the scheme of the amalgam of the input with itself, as an equality
(`TwistedDonor.amalgam_seedU`), not by unfolding the cardinalities.  A scheme built over the latter,
with a labelling that is the glued labelling of the twisted seed on the old cells, gives, with the
apex, a stage type whose faces are the coatom types of the twisted seed: the equality is used by
substitution, after which the completion below the full grade of the seed is assembled from the
data and the faces are those of `CompletionBelowFullGrade.restrictFace_withLabel`.

**The admitted coface** (`MixedSeed.DU`): for an admission `Adm` (`MixedSeed.IsLowAdmission`)
admitting the state `((⊤, ⊥, ⊤, ⊤, ⊤), (⊤, ⊥, ⊤, ⊤, v))`, the admitted completion
(`MixedSeed.admittedBy α Adm`) with the labels of the seed truncated to the stage
(`MixedSeed.qT`), and the apex.  It is legal (`MixedSeed.isLegal_DU`), and its faces along the two
coatoms are the input `SeparationObstruction.T α` and the twisted donor `TwistedDonor.Utop`
(`MixedSeed.restrictFace_DU`, `MixedSeed.mem_cofaces_DU`), at every stage that is zero or a limit.
The owner-as-partner clause gives the LOW-admitted coface at `v`; the self-seed clause, at
`v = ⊤`, a coface with both faces the input.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

/-! ### Generic: lawfulness below the top pair, and faces through an equality of amalgams -/

namespace Scheme

/-- A labelling lawful below `(univ, k)`, over a scheme whose cells have grade at most `k`, is
lawful. -/
theorem isLawful_of_isLawfulBelow {n k : ℕ} {S : Scheme.{u} n}
    (hgr : ∀ d, S.toCellScheme.grade d ≤ k)
    {q : Fin S.card → Label.{u}}
    (hq : S.rows.IsLawfulBelow ((univ : Finset (Fin n)), k) (fun x ↦ q x)) : S.rows.IsLawful q :=
  hq.isLawful fun d ↦ ⟨subset_univ _, hgr d⟩

end Scheme

namespace StageType

/-- The stage type on a scheme legal below the full grade with a lawful labelling at the stage. -/
noncomputable def ofLegalBelow {α : Ordinal.{u}} {n : ℕ} (S : Scheme.{u} n)
    (hS : S.IsLegalBelowFullGrade) (q : Fin S.card → Label.{u}) (hq : S.rows.IsLawful q)
    (hqα : ∀ d, AtStage α (q d)) : StageType.{u} α n :=
  ⟨S, q, hS.isWellFormed, hS.isCoded, hq, hqα⟩

end StageType

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ}

/-- **The faces of a completion given over a scheme equal to the amalgam.**  Let the amalgam of a
seed `J` have the scheme `A` (an equality, used by substitution), and let `Sch` extend `A` by cells
of full scope, legal below the full grade, with a lawful labelling at the stage that is the glued
labelling of `J` on the old cells.  With the apex added, the faces along the two coatoms are the
coatom types of `J`. -/
theorem restrictFace_addApex_of_eq (J : Seed.{u} α m) {A : Scheme.{u} (m + 2)}
    (E : J.amalgam.toScheme = A) {Sch : Scheme.{u} (m + 2)} (emb : Fin A.card ↪o Fin Sch.card)
    (hlow : A.toCellScheme.IsLowerEmbedding Sch.toCellScheme emb)
    (hscope : ∀ d, Sch.toCellScheme.scope (emb d) = A.toCellScheme.scope d)
    (hrows : Sch.rows.comap hlow = A.rows)
    (hrange : ∀ z, Sch.toCellScheme.scope z ≠ univ → z ∈ Set.range emb)
    (hfaces : Sch.toCellScheme.faces = A.toCellScheme.faces) (hleg : Sch.IsLegalBelowFullGrade)
    {q : Fin Sch.card → Label.{u}} (hq : Sch.rows.IsLawful q) (hqα : ∀ d, AtStage α (q d))
    (hqe : ∀ d, q (emb d) = J.amalgam.label (Fin.cast (congrArg Scheme.card E).symm d)) :
    StageType.restrictFace Fin.castSuccEmb
        ((StageType.ofLegalBelow Sch hleg q hq hqα).addApex hleg (Nat.succ_pos _)) =
      some J.left ∧
    StageType.restrictFace (extendByLast Fin.castSuccEmb)
        ((StageType.ofLegalBelow Sch hleg q hq hqα).addApex hleg (Nat.succ_pos _)) =
      some J.right := by
  subst E
  let F : CompletionBelowFullGrade J :=
    { scheme := Sch, embed := emb, isLowerEmbedding := hlow, scope_embed := hscope,
      comap_rows := hrows, mem_range_embed := hrange, faces_eq := hfaces,
      isLegalBelowFullGrade := hleg, label := q, isLawful := hq,
      label_embed := fun d ↦ (hqe d).trans (by rfl) }
  have hqe' : ∀ d, q (F.embed d) = J.amalgam.label d := F.label_embed
  exact ⟨(StageType.restrictFace_addApex _ _ _ Coatom.univ_map_left_ne).trans
      ((F.restrictFace_withLabel hq hqα hqe' _ Coatom.univ_map_left_ne).trans J.restrictFace_left),
    (StageType.restrictFace_addApex _ _ _ Coatom.univ_map_right_ne).trans
      ((F.restrictFace_withLabel hq hqα hqe' _ Coatom.univ_map_right_ne).trans
        J.restrictFace_right)⟩

end Seed

/-! ### The admitted coface at the seed -/

namespace MixedSeed

open StageType SeparationObstruction TwistedDonor

variable {α : Ordinal.{u}} {v : Label.{u}} {Adm : (Fin 5 → Label.{u}) → (Fin 5 → Label.{u}) → Prop}

theorem grade_admittedBy_le (hA : IsLowAdmission Adm) (d : Fin (admittedBy α Adm).card) :
    (admittedBy α Adm).toCellScheme.grade d ≤ 2 :=
  Nat.lt_succ_iff.mp ((isLegalBelowFullGrade_admittedBy (α := α) hA).grade_lt d)

/-- The labels of the seed with the donor `(⊤, ⊥, ⊤, ⊤, v)` on the admitted completion (a
choice). -/
noncomputable def qT0 (hA : IsLowAdmission Adm) (hv : IsSelfVisible 2 v)
    (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v)) : Fin (admittedBy α Adm).card → Label.{u} :=
  (exists_isLawful_admittedBy (α := α) hA hv hst).choose

theorem isLawful_qT0 (hA : IsLowAdmission Adm) (hv : IsSelfVisible 2 v)
    (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v)) : (admittedBy α Adm).rows.IsLawful (qT0 hA hv hst) :=
  Scheme.isLawful_of_isLawfulBelow (grade_admittedBy_le hA)
    (exists_isLawful_admittedBy hA hv hst).choose_spec.1

theorem qT0_lc (hA : IsLowAdmission Adm) (hv : IsSelfVisible 2 v)
    (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v)) (z : Fin 5) :
    qT0 (α := α) hA hv hst (Fin.castAdd _ (Fin.castAdd _ (lc α z))) = lab ⊤ ⊤ ⊤ z :=
  (exists_isLawful_admittedBy hA hv hst).choose_spec.2.1 z

theorem qT0_rc (hA : IsLowAdmission Adm) (hv : IsSelfVisible 2 v)
    (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v)) (z : Fin 5) :
    qT0 (α := α) hA hv hst (Fin.castAdd _ (Fin.castAdd _ (rc α z))) = lab ⊤ ⊤ v z :=
  (exists_isLawful_admittedBy hA hv hst).choose_spec.2.2 z

/-- The labels truncated to the stage. -/
noncomputable def qT (hA : IsLowAdmission Adm) (hv : IsSelfVisible 2 v)
    (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v)) : Fin (admittedBy α Adm).card → Label.{u} :=
  Label.reduce α ∘ qT0 hA hv hst

theorem isLawful_qT (hA : IsLowAdmission Adm) (hα : Order.IsSuccPrelimit α)
    (hv : IsSelfVisible 2 v) (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v)) :
    (admittedBy α Adm).rows.IsLawful (qT hA hv hst) := (isLawful_qT0 hA hv hst).reduce hα

theorem atStage_qT (hA : IsLowAdmission Adm) (hv : IsSelfVisible 2 v)
    (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v)) (d : Fin (admittedBy α Adm).card) :
    AtStage α (qT hA hv hst d) :=
  atStage_reduce α _

theorem lab_atStage (hvα : AtStage α v) (z : Fin 5) : AtStage α (lab ⊤ ⊤ v z) := by
  fin_cases z
  exacts [Or.inr rfl, Or.inl (WithBot.bot_lt_coe _), Or.inr rfl, Or.inr rfl, hvα]

theorem qT_lc (hA : IsLowAdmission Adm) (hv : IsSelfVisible 2 v)
    (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v)) (z : Fin 5) :
    qT (α := α) hA hv hst (Fin.castAdd _ (Fin.castAdd _ (lc α z))) = lab ⊤ ⊤ ⊤ z := by
  rw [qT, Function.comp_apply, qT0_lc]
  exact AtStage.reduce_eq (lab_atStage (Or.inr rfl) z)

theorem qT_rc (hA : IsLowAdmission Adm) (hv : IsSelfVisible 2 v) (hvα : AtStage α v)
    (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v)) (z : Fin 5) :
    qT hA hv hst (Fin.castAdd _ (Fin.castAdd _ (rc α z))) = lab ⊤ ⊤ v z := by
  rw [qT, Function.comp_apply, qT0_rc]
  exact AtStage.reduce_eq (lab_atStage hvα z)

variable (Adm) in
/-- The old cells of the admitted completion. -/
noncomputable def embT : Fin (I α).amalgam.card ↪o Fin (admittedBy α Adm).card :=
  (Fin.castAddOrderEmb _).trans (Fin.castAddOrderEmb _)

variable (Adm) in
theorem isLowerEmbedding_castAdd_lowerT :
    (lowerT α).toCellScheme.IsLowerEmbedding (admittedBy α Adm).toCellScheme (Fin.castAdd _) :=
  Scheme.isLowerEmbedding_castAdd (S := lowerT α) 2
    ((lowerT α).admittedCatalogue 2 (AdmBy α Adm)).card
    (fun i ↦ (lowerT α).fieldRowOn 2 ((lowerT α).admittedCatalogue 2 (AdmBy α Adm))
      (Scheme.entryOn _ i)) ((I α).not_univ_two_le_doubledLower (hLR α))

theorem isLowerEmbedding_castAdd_amalgam :
    (I α).amalgam.toCellScheme.IsLowerEmbedding (lowerT α).toCellScheme (Fin.castAdd _) :=
  Scheme.isLowerEmbedding_castAdd (S := (I α).amalgam.toScheme) 1 ((I α).nFull 1)
    ((I α).lowerRow (hLR α)) ((I α).not_univ_le 1)

variable (Adm) in
theorem isLowerEmbedding_embT :
    (I α).amalgam.toCellScheme.IsLowerEmbedding (admittedBy α Adm).toCellScheme (embT Adm) :=
  (isLowerEmbedding_castAdd_lowerT Adm).comp isLowerEmbedding_castAdd_amalgam

variable (Adm) in
theorem comap_rows_embT :
    (admittedBy α Adm).rows.comap (isLowerEmbedding_embT (α := α) Adm) = (I α).amalgam.rows := by
  have h1 : (admittedBy α Adm).rows.comap (isLowerEmbedding_castAdd_lowerT (α := α) Adm) =
      (lowerT α).rows :=
    Scheme.comap_rows_castAdd (S := lowerT α) (k := 2)
      (M := ((lowerT α).admittedCatalogue 2 (AdmBy α Adm)).card)
      (r := fun i ↦ (lowerT α).fieldRowOn 2 ((lowerT α).admittedCatalogue 2 (AdmBy α Adm))
        (Scheme.entryOn _ i)) (h := (I α).not_univ_two_le_doubledLower (hLR α))
  have h2 : (lowerT α).rows.comap (isLowerEmbedding_castAdd_amalgam (α := α)) =
      (I α).amalgam.rows :=
    Scheme.comap_rows_castAdd (S := (I α).amalgam.toScheme) (k := 1) (M := (I α).nFull 1)
      (r := (I α).lowerRow (hLR α)) (h := (I α).not_univ_le 1)
  calc (admittedBy α Adm).rows.comap (isLowerEmbedding_embT (α := α) Adm)
      = ((admittedBy α Adm).rows.comap (isLowerEmbedding_castAdd_lowerT Adm)).comap
          isLowerEmbedding_castAdd_amalgam :=
        (CellScheme.Rows.comap_comap (admittedBy α Adm).rows (isLowerEmbedding_castAdd_lowerT Adm)
          isLowerEmbedding_castAdd_amalgam).symm
    _ = (I α).amalgam.rows := by rw [h1, h2]

/-- **The admitted coface at the seed**: the admitted completion with the labels of the seed
(the input, and `(⊤, ⊥, ⊤, ⊤, v)`) truncated to the stage, and the apex. -/
noncomputable def DU (hA : IsLowAdmission Adm) (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v))
    (hα : Order.IsSuccPrelimit α) (hv : IsSelfVisible 2 v) : StageType.{u} α 3 :=
  (StageType.ofLegalBelow (admittedBy α Adm) (isLegalBelowFullGrade_admittedBy hA) (qT hA hv hst)
    (isLawful_qT hA hα hv hst) (atStage_qT hA hv hst)).addApex
    (isLegalBelowFullGrade_admittedBy hA) (Nat.succ_pos _)

theorem isLegal_DU (hA : IsLowAdmission Adm) (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v))
    (hα : Order.IsSuccPrelimit α) (hv : IsSelfVisible 2 v) :
    (DU hA hst hα hv).IsLegal := StageType.isLegal_addApex _ _

/-- **The faces of the admitted coface are the input and the donor `(⊤, ⊥, ⊤, ⊤, v)`.** -/
theorem restrictFace_DU (hA : IsLowAdmission Adm) (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v))
    (hα : Order.IsSuccPrelimit α) (hv : IsSelfVisible 2 v) (hvα : AtStage α v) :
    restrictFace Fin.castSuccEmb (DU (α := α) hA hst hα hv) = some (T α) ∧
    restrictFace (extendByLast Fin.castSuccEmb) (DU hA hst hα hv) = some (Utop hv hvα) := by
  have hrows := comap_rows_embT (α := α) Adm
  refine Seed.restrictFace_addApex_of_eq (seedU hv hvα) (amalgam_seedU hv hvα) (embT Adm)
    (isLowerEmbedding_embT Adm) (fun d ↦ (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
      (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _)) hrows (fun z hz ↦ ?_) rfl
    (isLegalBelowFullGrade_admittedBy hA) (isLawful_qT hA hα hv hst) (atStage_qT hA hv hst)
    (fun d ↦ ?_)
  · induction z using Fin.addCases with
    | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
    | left z =>
      induction z using Fin.addCases with
      | right i =>
        exact absurd ((Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
          (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i)) hz
      | left a => exact ⟨a, rfl⟩
  · change qT hA hv hst (Fin.castAdd _ (Fin.castAdd _ d)) = _
    have keyL (c : Fin 5) : qT hA hv hst (Fin.castAdd _ (Fin.castAdd _ (lc α c))) =
        (seedU hv hvα).amalgam.label
          (Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm (lc α c)) := by
      rw [qT_lc hA hv hst, cast_lc]
      exact (StageType.label_faceCell (seedU hv hvα).restrictFace_left _).symm
    have keyR (c : Fin 5) : qT hA hv hst (Fin.castAdd _ (Fin.castAdd _ (rc α c))) =
        (seedU hv hvα).amalgam.label
          (Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm (rc α c)) := by
      rw [qT_rc hA hv hvα hst, cast_rc]
      exact (StageType.label_faceCell (seedU hv hvα).restrictFace_right _).symm
    rcases (I α).eq_faceCell_or (hLR α) d with he | he
    · rw [← he]; exact keyL _
    · rw [← he]; exact keyR _

theorem mem_cofaces_DU (hA : IsLowAdmission Adm) (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v))
    (hα : Order.IsSuccPrelimit α) (hv : IsSelfVisible 2 v) (hvα : AtStage α v) :
    DU hA hst hα hv ∈ (T α).cofaces :=
  ⟨isLegal_DU hA hst hα hv, (restrictFace_DU hA hst hα hv hvα).1⟩

end MixedSeed

/-! ### Generic: faces and labels on one scheme, and restrictions of lawful labellings -/

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-- **Stage types on one scheme with one face along `g` agree at the cells visible through it**
(the argument of the private lemma of `VaughtConjecture.Continuation.SourceGapTopReading`). -/
theorem label_eq_of_restrictFace_eq_some {S : Scheme.{u} m}
    {ℓ ℓ' : Fin S.card → Label.{u}} {hw hw' : S.IsWellFormed} {hc hc' : S.IsCoded}
    {hl : S.rows.IsLawful ℓ} {hl' : S.rows.IsLawful ℓ'} {ha : ∀ d, AtStage α (ℓ d)}
    {ha' : ∀ d, AtStage α (ℓ' d)} {g : Fin n ↪ Fin m} {t : StageType.{u} α n}
    (hq : restrictFace g (⟨S, ℓ, hw, hc, hl, ha⟩ : StageType.{u} α m) = some t)
    (hD : restrictFace g (⟨S, ℓ', hw', hc', hl', ha'⟩ : StageType.{u} α m) = some t)
    {y : Fin S.card} (hy : y ∈ S.visibleCells g) : ℓ y = ℓ' y := by
  obtain ⟨hfq, hq⟩ := (restrictFace_eq_some_iff _ g).mp hq
  obtain ⟨hfD, hD⟩ := (restrictFace_eq_some_iff _ g).mp hD
  obtain ⟨i, rfl⟩ : y ∈ Set.range (S.cellMap g) := by
    rw [Scheme.range_cellMap]
    exact hy
  exact label_congr (hq.trans hD.symm) (i := i) (j := i) rfl

/-- **Stage types on one scheme agreeing at the cells visible through `g` have one face along
`g`.** -/
theorem restrictFace_eq_of_label_eq {S : Scheme.{u} m}
    {ℓ ℓ' : Fin S.card → Label.{u}} {hw hw' : S.IsWellFormed} {hc hc' : S.IsCoded}
    {hl : S.rows.IsLawful ℓ} {hl' : S.rows.IsLawful ℓ'} {ha : ∀ d, AtStage α (ℓ d)}
    {ha' : ∀ d, AtStage α (ℓ' d)} {g : Fin n ↪ Fin m}
    (h : ∀ y ∈ S.visibleCells g, ℓ y = ℓ' y) :
    restrictFace g (⟨S, ℓ, hw, hc, hl, ha⟩ : StageType.{u} α m) =
      restrictFace g (⟨S, ℓ', hw', hc', hl', ha'⟩ : StageType.{u} α m) := by
  by_cases hf : univ.map g ∈ S.toCellScheme.faces
  · rw [restrictFace_of_mem _ g hf, restrictFace_of_mem _ g hf]
    refine congrArg some (ext rfl fun i j hij ↦ ?_)
    rw [comap_label, comap_label]
    obtain rfl : i = j := Fin.ext hij
    exact h _ (S.cellMap_mem g i)
  · rw [restrictFace_of_notMem _ g hf, restrictFace_of_notMem _ g hf]

/-- A lawful labelling of a stage type with the apex is lawful on the old cells. -/
theorem isLawful_castSucc_addApex {t : StageType.{u} α n} (ht : t.IsLegalBelowFullGrade)
    (hn : 0 < n) {p : Fin (t.card + 1) → Label.{u}} (hp : (t.addApex ht hn).rows.IsLawful p) :
    t.rows.IsLawful (p ∘ Fin.castSucc) := by
  have h := hp.comap (Scheme.isLowerEmbedding_castSucc n (apexRow ht) ht.not_le)
  have e : (t.toScheme.appendFullCell n (apexRow ht) ht.not_le).rows.comap
      (Scheme.isLowerEmbedding_castSucc n (apexRow ht) ht.not_le) = t.rows :=
    Scheme.comap_rows_castSucc (h := ht.not_le)
  exact e ▸ h

end StageType

namespace Scheme

/-- A lawful labelling after appending cells is lawful on the old cells. -/
theorem isLawful_comp_castAdd {n k M : ℕ} {S : Scheme.{u} n}
    {r : Fin M → Fin (S.card + M) → Label.{u}}
    {h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}
    {p : Fin (S.card + M) → Label.{u}} (hp : (S.appendFullCells k M r h).rows.IsLawful p) :
    S.rows.IsLawful (p ∘ Fin.castAdd M) := by
  have h' := hp.comap (isLowerEmbedding_castAdd k M r h)
  rwa [comap_rows_castAdd] at h'

end Scheme

/-! ### Generic: the stage type of a scheme with the apex, and determination there -/

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ} {S : Scheme.{u} n} (hS : S.IsLegalBelowFullGrade)
  {q : Fin S.card → Label.{u}} (hq : S.rows.IsLawful q) (hqα : ∀ d, AtStage α (q d)) (hn : 0 < n)

/-- The stage type of a scheme legal below the full grade with a lawful labelling at the stage,
with the apex. -/
noncomputable abbrev apexOf : StageType.{u} α n := (ofLegalBelow S hS q hq hqα).addApex hS hn

theorem apexOf_label_castSucc (x : Fin S.card) :
    (apexOf hS hq hqα hn).label (Fin.castSucc x) = q x :=
  addApex_label_castSucc (t := ofLegalBelow S hS q hq hqα) hS hn x

theorem apexOf_scope_castSucc (x : Fin S.card) :
    (apexOf hS hq hqα hn).toCellScheme.scope (Fin.castSucc x) = S.toCellScheme.scope x :=
  Scheme.appendFullCellScheme_scope_castSucc _ _ x

theorem apexOf_scope_last :
    (apexOf hS hq hqα hn).toCellScheme.scope (Fin.last S.card) = univ :=
  Scheme.appendFullCellScheme_scope_last _ _

/-- An old cell visible through `f` stays visible after adding the apex. -/
theorem apexOf_castSucc_mem_visibleCells {p : ℕ} {f : Fin p ↪ Fin n} {x : Fin S.card}
    (hx : x ∈ S.visibleCells f) :
    (Fin.castSucc x : Fin (apexOf hS hq hqα hn).card) ∈
      (apexOf hS hq hqα hn).toScheme.visibleCells f :=
  Scheme.mem_visibleCells.mpr ((congrArg (fun s : Finset (Fin n) ↦ (s : Set (Fin n)))
    (apexOf_scope_castSucc hS hq hqα hn x)).subset.trans (Scheme.mem_visibleCells.mp hx))

/-- A cell visible through a face missing a point is an old cell visible through it. -/
theorem exists_castSucc_of_mem_visibleCells {p : ℕ} {f : Fin p ↪ Fin n}
    (hf : ∃ a, a ∉ Set.range f) {y : Fin (S.card + 1)}
    (hy : y ∈ (apexOf hS hq hqα hn).toScheme.visibleCells f) :
    ∃ x ∈ S.visibleCells f, y = Fin.castSucc x := by
  have hy' := Scheme.mem_visibleCells.mp hy
  induction y using Fin.lastCases with
  | last =>
    obtain ⟨a, ha⟩ := hf
    have hsl := apexOf_scope_last hS hq hqα hn
    exact absurd (hy' (show a ∈ (((apexOf hS hq hqα hn).toCellScheme.scope (Fin.last S.card)) :
      Set (Fin n)) from mem_coe.mpr (hsl ▸ mem_univ a))) ha
  | cast x =>
    refine ⟨x, Scheme.mem_visibleCells.mpr ?_, rfl⟩
    exact (congrArg (fun s : Finset (Fin n) ↦ (s : Set (Fin n)))
      (apexOf_scope_castSucc hS hq hqα hn x)).symm.subset.trans hy'

/-- **Determination over a coface with the apex, from agreement on the donor face**: if every
labelling of the scheme lawful, agreeing with the coface at the cells visible through the context
face and capped at `δ` everywhere, agrees with it at the cells visible through the donor face, then
the donor face is determined within the receiving family at `δ`. -/
theorem isDeterminedWithin_apexOf {k p : ℕ} {S : Scheme.{u} (k + 1)}
    (hS : S.IsLegalBelowFullGrade) {q : Fin S.card → Label.{u}} (hq : S.rows.IsLawful q)
    (hqα : ∀ d, AtStage α (q d)) (hn : 0 < k + 1) {t' : StageType.{u} α k}
    {h : Fin p ↪ Fin k} {d : StageType.{u} α (p + 1)} {δ : Label.{u}}
    (hT : restrictFace Fin.castSuccEmb (apexOf hS hq hqα hn) = some t')
    (hd : restrictFace (extendByLast h) (apexOf hS hq hqα hn) = some d)
    (key : ∀ ℓ : Fin (S.card + 1) → Label.{u}, (apexOf hS hq hqα hn).rows.IsLawful ℓ →
      (∀ x ∈ (apexOf hS hq hqα hn).toScheme.visibleCells Fin.castSuccEmb,
        ℓ x = (apexOf hS hq hqα hn).label x) →
      (∀ x, min (ℓ x) δ = min ((apexOf hS hq hqα hn).label x) δ) →
      ∀ y ∈ (apexOf hS hq hqα hn).toScheme.visibleCells (extendByLast h),
        ℓ y = (apexOf hS hq hqα hn).label y) :
    IsDeterminedWithin (receivingFamily (apexOf hS hq hqα hn) δ) t' h d := by
  intro Q hQ hQT
  obtain ⟨hs, hlab⟩ := hQ
  obtain ⟨S', ℓ', hw', hc', hl', ha'⟩ := Q
  obtain rfl : S' = (apexOf hS hq hqα hn).toScheme := hs
  have hleft (x) (hx : x ∈ (apexOf hS hq hqα hn).toScheme.visibleCells Fin.castSuccEmb) :
      ℓ' x = (apexOf hS hq hqα hn).label x :=
    label_eq_of_restrictFace_eq_some hQT hT hx
  rw [← hd]
  exact restrictFace_eq_of_label_eq (key ℓ' hl' hleft fun x ↦ hlab x x rfl)

end StageType

end VaughtConjecture
