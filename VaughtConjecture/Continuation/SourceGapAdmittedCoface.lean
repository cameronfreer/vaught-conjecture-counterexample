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

**The LOW-admitted coface** (`MixedSeed.DU`): the LOW-admitted completion
(`MixedSeed.admittedT`) with the labels of the twisted seed truncated to the stage
(`MixedSeed.qT`), and the apex.  It is legal (`MixedSeed.isLegal_DU`), and its faces along the two
coatoms are the input `SeparationObstruction.T α` and the twisted donor `TwistedDonor.Utop`
(`MixedSeed.restrictFace_DU`, `MixedSeed.mem_cofaces_DU`), at every stage that is zero or a limit.

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

/-! ### The LOW-admitted coface at the twisted seed -/

namespace MixedSeed

open StageType SeparationObstruction TwistedDonor

variable {α : Ordinal.{u}} {v : Label.{u}}

theorem grade_admittedT_le (d : Fin (admittedT α).card) : (admittedT α).toCellScheme.grade d ≤ 2 :=
  Nat.lt_succ_iff.mp ((isLegalBelowFullGrade_admittedT (α := α)).grade_lt d)

/-- The labels of the twisted seed on the LOW-admitted completion (a choice). -/
noncomputable def qT0 (hv : IsSelfVisible 2 v) : Fin (admittedT α).card → Label.{u} :=
  (exists_isLawful_admittedT (α := α) hv).choose

theorem isLawful_qT0 (hv : IsSelfVisible 2 v) : (admittedT α).rows.IsLawful (qT0 hv) :=
  Scheme.isLawful_of_isLawfulBelow grade_admittedT_le (exists_isLawful_admittedT hv).choose_spec.1

theorem qT0_lc (hv : IsSelfVisible 2 v) (z : Fin 5) :
    qT0 (α := α) hv (Fin.castAdd _ (Fin.castAdd _ (lc α z))) = lab ⊤ ⊤ ⊤ z :=
  (exists_isLawful_admittedT hv).choose_spec.2.1 z

theorem qT0_rc (hv : IsSelfVisible 2 v) (z : Fin 5) :
    qT0 (α := α) hv (Fin.castAdd _ (Fin.castAdd _ (rc α z))) = lab ⊤ ⊤ v z :=
  (exists_isLawful_admittedT hv).choose_spec.2.2 z

/-- The labels truncated to the stage. -/
noncomputable def qT (hv : IsSelfVisible 2 v) : Fin (admittedT α).card → Label.{u} :=
  Label.reduce α ∘ qT0 hv

theorem isLawful_qT (hα : Order.IsSuccPrelimit α) (hv : IsSelfVisible 2 v) :
    (admittedT α).rows.IsLawful (qT hv) := (isLawful_qT0 hv).reduce hα

theorem atStage_qT (hv : IsSelfVisible 2 v) (d : Fin (admittedT α).card) : AtStage α (qT hv d) :=
  atStage_reduce α _

theorem lab_atStage (hvα : AtStage α v) (z : Fin 5) : AtStage α (lab ⊤ ⊤ v z) := by
  fin_cases z
  exacts [Or.inr rfl, Or.inl (WithBot.bot_lt_coe _), Or.inr rfl, Or.inr rfl, hvα]

theorem qT_lc (hv : IsSelfVisible 2 v) (z : Fin 5) :
    qT (α := α) hv (Fin.castAdd _ (Fin.castAdd _ (lc α z))) = lab ⊤ ⊤ ⊤ z := by
  rw [qT, Function.comp_apply, qT0_lc]
  exact AtStage.reduce_eq (lab_atStage (Or.inr rfl) z)

theorem qT_rc (hv : IsSelfVisible 2 v) (hvα : AtStage α v) (z : Fin 5) :
    qT hv (Fin.castAdd _ (Fin.castAdd _ (rc α z))) = lab ⊤ ⊤ v z := by
  rw [qT, Function.comp_apply, qT0_rc]
  exact AtStage.reduce_eq (lab_atStage hvα z)

/-- The old cells of the LOW-admitted completion. -/
noncomputable def embT : Fin (I α).amalgam.card ↪o Fin (admittedT α).card :=
  (Fin.castAddOrderEmb _).trans (Fin.castAddOrderEmb _)

theorem isLowerEmbedding_castAdd_lowerT :
    (lowerT α).toCellScheme.IsLowerEmbedding (admittedT α).toCellScheme (Fin.castAdd _) :=
  Scheme.isLowerEmbedding_castAdd (S := lowerT α) 2 ((lowerT α).admittedCatalogue 2 (AdmU α)).card
    (fun i ↦ (lowerT α).fieldRowOn 2 ((lowerT α).admittedCatalogue 2 (AdmU α))
      (Scheme.entryOn _ i)) ((I α).not_univ_two_le_doubledLower (hLR α))

theorem isLowerEmbedding_castAdd_amalgam :
    (I α).amalgam.toCellScheme.IsLowerEmbedding (lowerT α).toCellScheme (Fin.castAdd _) :=
  Scheme.isLowerEmbedding_castAdd (S := (I α).amalgam.toScheme) 1 ((I α).nFull 1)
    ((I α).lowerRow (hLR α)) ((I α).not_univ_le 1)

theorem isLowerEmbedding_embT :
    (I α).amalgam.toCellScheme.IsLowerEmbedding (admittedT α).toCellScheme (embT (α := α)) :=
  isLowerEmbedding_castAdd_lowerT.comp isLowerEmbedding_castAdd_amalgam

theorem comap_rows_embT :
    (admittedT α).rows.comap (isLowerEmbedding_embT (α := α)) = (I α).amalgam.rows := by
  have h1 : (admittedT α).rows.comap (isLowerEmbedding_castAdd_lowerT (α := α)) =
      (lowerT α).rows :=
    Scheme.comap_rows_castAdd (S := lowerT α) (k := 2)
      (M := ((lowerT α).admittedCatalogue 2 (AdmU α)).card)
      (r := fun i ↦ (lowerT α).fieldRowOn 2 ((lowerT α).admittedCatalogue 2 (AdmU α))
        (Scheme.entryOn _ i)) (h := (I α).not_univ_two_le_doubledLower (hLR α))
  have h2 : (lowerT α).rows.comap (isLowerEmbedding_castAdd_amalgam (α := α)) =
      (I α).amalgam.rows :=
    Scheme.comap_rows_castAdd (S := (I α).amalgam.toScheme) (k := 1) (M := (I α).nFull 1)
      (r := (I α).lowerRow (hLR α)) (h := (I α).not_univ_le 1)
  calc (admittedT α).rows.comap (isLowerEmbedding_embT (α := α))
      = ((admittedT α).rows.comap isLowerEmbedding_castAdd_lowerT).comap
          isLowerEmbedding_castAdd_amalgam :=
        (CellScheme.Rows.comap_comap (admittedT α).rows isLowerEmbedding_castAdd_lowerT
          isLowerEmbedding_castAdd_amalgam).symm
    _ = (I α).amalgam.rows := by rw [h1, h2]

/-- **The LOW-admitted coface at the twisted seed**: the LOW-admitted completion with the labels of
the twisted seed truncated to the stage, and the apex. -/
noncomputable def DU (hα : Order.IsSuccPrelimit α) (hv : IsSelfVisible 2 v) :
    StageType.{u} α 3 :=
  (StageType.ofLegalBelow (admittedT α) isLegalBelowFullGrade_admittedT (qT hv)
    (isLawful_qT hα hv) (atStage_qT hv)).addApex isLegalBelowFullGrade_admittedT (Nat.succ_pos _)

theorem isLegal_DU (hα : Order.IsSuccPrelimit α) (hv : IsSelfVisible 2 v) :
    (DU hα hv).IsLegal := StageType.isLegal_addApex _ _

/-- **The faces of the LOW-admitted coface are the input and the twisted donor.** -/
theorem restrictFace_DU (hα : Order.IsSuccPrelimit α) (hv : IsSelfVisible 2 v)
    (hvα : AtStage α v) :
    restrictFace Fin.castSuccEmb (DU (α := α) hα hv) = some (T α) ∧
    restrictFace (extendByLast Fin.castSuccEmb) (DU hα hv) = some (Utop hv hvα) := by
  have hrows := comap_rows_embT (α := α)
  refine Seed.restrictFace_addApex_of_eq (seedU hv hvα) (amalgam_seedU hv hvα) embT
    isLowerEmbedding_embT (fun d ↦ (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
      (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _)) hrows (fun z hz ↦ ?_) rfl
    isLegalBelowFullGrade_admittedT (isLawful_qT hα hv) (atStage_qT hv) (fun d ↦ ?_)
  · induction z using Fin.addCases with
    | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
    | left z =>
      induction z using Fin.addCases with
      | right i =>
        exact absurd ((Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
          (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i)) hz
      | left a => exact ⟨a, rfl⟩
  · change qT hv (Fin.castAdd _ (Fin.castAdd _ d)) = _
    have keyL (c : Fin 5) : qT hv (Fin.castAdd _ (Fin.castAdd _ (lc α c))) =
        (seedU hv hvα).amalgam.label
          (Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm (lc α c)) := by
      rw [qT_lc hv, cast_lc]
      exact (StageType.label_faceCell (seedU hv hvα).restrictFace_left _).symm
    have keyR (c : Fin 5) : qT hv (Fin.castAdd _ (Fin.castAdd _ (rc α c))) =
        (seedU hv hvα).amalgam.label
          (Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm (rc α c)) := by
      rw [qT_rc hv hvα, cast_rc]
      exact (StageType.label_faceCell (seedU hv hvα).restrictFace_right _).symm
    rcases (I α).eq_faceCell_or (hLR α) d with he | he
    · rw [← he]; exact keyL _
    · rw [← he]; exact keyR _

theorem mem_cofaces_DU (hα : Order.IsSuccPrelimit α) (hv : IsSelfVisible 2 v)
    (hvα : AtStage α v) : DU hα hv ∈ (T α).cofaces :=
  ⟨isLegal_DU hα hv, (restrictFace_DU hα hv hvα).1⟩

end MixedSeed

end VaughtConjecture
