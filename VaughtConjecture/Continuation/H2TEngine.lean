/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2ArityOne

/-!
# One clause for both donors of the input `T`

WORK FILE (branch `research/work-h2`).  No `sorry`.

The clause `H2.SelfLowG` (every designated top its own field), with the designation read off the
donor, runs through the admitted completion at the seed of the input `SeparationObstruction.T`
with itself (`VaughtConjecture.Continuation.SourceGapAdmittedSeed`):

* it is an admission there for every designation with the designated tops among `z'`, `o'`, `r'`
  (`MixedSeed.isLowAdmission_selfLow`, from `H2.selfLow_isStateAdmission` with donor raising
  `FieldAdmission.donorRaising_S` and owner lowering `FieldAdmission.ownerLowering_S`);
* in its completion, with the context at the labels of the input, a designated top above the
  designated cells below the top is `⊤` (`MixedSeed.eq_top_of_admittedSelfLow`; recognition with
  the shifter commuting with the replacement at `2`);
* so the twisted donor `(⊤, ⊥, ⊤, ⊤, v)`, `v ≠ ⊤` (designation `e'`, `r'` below the top; tops
  `z'`, `o'`) and the input itself (designation `e'`; tops `z'`, `o'`, `r'`) are both determined
  at a limit stage through the same clause (`MixedSeed.coatomCutoffDetermination_U_selfLow`,
  `MixedSeed.coatomCutoffDetermination_T_selfLow`).
-/

universe u

namespace VaughtConjecture.MixedSeed

open Finset Label StageType SeparationObstruction TwistedDonor FieldAdmission H2

variable {α : Ordinal.{u}}

/-- **The clause is an admission at the seed of the input with itself**, for every designation
with the designated tops among `z'`, `o'`, `r'`. -/
theorem isLowAdmission_selfLow {Lo Tops : Finset (Fin 5)}
    (hTops : ∀ t ∈ Tops, t = 2 ∨ t = 3 ∨ t = 4) :
    IsLowAdmission (SelfLowG.{u} (3 : Fin 5) 4 2 Lo Tops) := by
  have hS := selfLow_isStateAdmission (rc := root5) (rd := root5) (K := 2)
    (C := S.{u}.rows.IsLawful) (D := S.{u}.rows.IsLawful) (o := (3 : Fin 5)) (r := 4) (Lo := Lo)
    (Tops := Tops) Set.univ (fun _ hf ↦ hf.orderly 3) (fun _ hf _ _ ↦ frontierAt_le_T hf)
    (donorRaising_S hTops fun _ hf ↦ hf.orderly 0) ownerLowering_S
  refine ⟨hS.bot, fun t ht _ ↦ ?_, fun {_} hσ hσ0 hc {_ _} h ↦ hS.comp hσ hσ0 hc h,
    fun {h} hh {L R f} hL hR hy hadm hf hfL ↦ ?_, fun {h} hh {L R f} hL hR hy hadm hf hfR ↦ ?_⟩
  · rcases hTops t ht with rfl | rfl | rfl <;> exact le_top
  · obtain ⟨W, hW, hWr, hWR, hA⟩ := hS.context hh hL hR (fun _ ↦ hy) hadm hf hfL
    exact ⟨W, hW, hWr 0, hWR, hA⟩
  · obtain ⟨W, hW, hWr, hWL, hA⟩ := hS.donor hh hL hR (fun _ ↦ hy) hadm hf hfR
    exact ⟨W, hW, hWr 0, hWL, hA⟩

/-- **Determination of the designated tops in the completion of the clause**: in every labelling
lawful below `(univ, 2)` with the context copy at the labels of the input, a designated top above
the designated cells below the top is `⊤`. -/
theorem eq_top_of_admittedSelfLow {Lo Tops : Finset (Fin 5)}
    (hTops : ∀ t ∈ Tops, t = 2 ∨ t = 3 ∨ t = 4)
    {q : Fin (admittedBy α (SelfLowG.{u} (3 : Fin 5) 4 2 Lo Tops)).card → Label.{u}}
    (hq : (admittedBy α (SelfLowG.{u} (3 : Fin 5) 4 2 Lo Tops)).rows.IsLawfulBelow
      ((univ : Finset (Fin 3)), 2) (fun x ↦ q x))
    (hctx : ∀ z, q (oL _ z) = lab ⊤ ⊤ ⊤ z) {t : Fin 5} (ht : t ∈ Tops)
    (hlt : Lo.sup (fun x ↦ q (oR _ x)) < q (oR _ t)) : q (oR _ t) = ⊤ := by
  have hA := isLowAdmission_selfLow.{u} (Lo := Lo) hTops
  have hx₀ : (lowerT α).toCellScheme.grade (Fin.castAdd _ (lc α 3)) = 2 :=
    congrArg Prod.snd gradedIndex_left_three
  obtain ⟨a, -, hAa, σ, hσ, hσ0, hc, hold⟩ :=
    Scheme.exists_admitted_image (hS := (I α).not_univ_two_le_doubledLower (hLR α))
      (admBy_bot (α := α) hA) grade_lowerT_le hq hx₀ (hctx 3)
  have hcl := hA.comp hσ hσ0 hc hAa
  have hL (z : Fin 5) : σ (privT a z) = lab ⊤ ⊤ ⊤ z := by
    rw [← hctx z]
    exact (hold _).symm
  have hR (z : Fin 5) : σ (donT a z) = q (oR _ z) := (hold _).symm
  have h := hcl t ht (by
    change Lo.sup (fun z ↦ σ (donT a z)) < σ (donT a t)
    simp only [hR]
    exact hlt)
  change min (σ (privT a 3)) (visibilityReplace 2 2 (σ (privT a 4))) ≤ σ (donT a t) at h
  rw [hL, hL, hR] at h
  change min ⊤ (visibilityReplace 2 2 ⊤) ≤ _ at h
  rw [visibilityReplace_top, min_self, top_le_iff] at h
  exact h

/-- The tops of the twisted donor. -/
theorem topsU_sub' : ∀ t ∈ topsU, t = 2 ∨ t = 3 ∨ t = 4 := topsU_sub

/-- The state of the twisted seed is admitted by the clause. -/
theorem selfLow_Utop (v : Label.{u}) :
    SelfLowG.{u} (3 : Fin 5) 4 2 loU topsU (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v) := by
  intro t ht _
  simp only [topsU, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl <;> exact le_top

/-- The state of the self seed is admitted by the clause. -/
theorem selfLow_T :
    SelfLowG.{u} (3 : Fin 5) 4 2 loSelf topsSelf (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ ⊤) := by
  intro t ht _
  simp only [topsSelf, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl <;> exact le_top

/-- **The twisted donor through the clause**: at a stage that is zero or a limit, every cutoff above
`v` (so `v ≠ ⊤`). -/
theorem isDeterminedWithin_DU_selfLow (hα : Order.IsSuccPrelimit α) {v : Label.{u}}
    (hv : IsSelfVisible 2 v) (hvα : AtStage α v) {δ : Label.{u}} (hvδ : v < δ) :
    IsDeterminedWithin (receivingFamily (DU (isLowAdmission_selfLow topsU_sub) (selfLow_Utop v)
      hα hv) δ) (T α) Fin.castSuccEmb (Utop hv hvα) := by
  refine isDeterminedWithin_DU_of _ _ hα hv hvα (bot_le.trans_lt hvδ) fun q hq hqL hqc ↦ ?_
  have hr' : q (oR _ 4) = v := Label.eq_of_min_eq_of_lt (hqc 4).symm hvδ
  have he' : q (oR _ 1) = ⊥ := by
    have e := hqc 1
    change min (q (oR _ 1)) δ = min ⊥ δ at e
    rw [min_bot_left] at e
    rcases min_eq_bot.mp e with h | h
    · exact h
    · exact absurd h (ne_bot_of_gt hvδ)
  have ho' : δ ≤ q (oR _ 3) := by
    have e := hqc 3
    change min (q (oR _ 3)) δ = min ⊤ δ at e
    rw [min_eq_right le_top] at e
    exact min_eq_right_iff.mp e
  refine ⟨?_, hr'⟩
  refine eq_top_of_admittedSelfLow topsU_sub (hq.isLawfulBelow _) hqL (by simp [topsU]) ?_
  have hsup : loU.sup (fun x ↦ q (oR (SelfLowG.{u} (3 : Fin 5) 4 2 loU topsU) x)) = v := by
    simp [loU, he', hr']
  rw [hsup]
  exact hvδ.trans_le ho'

/-- **The input itself through the clause**: at a stage that is zero or a limit, every cutoff
above `⊥`. -/
theorem isDeterminedWithin_DS_selfLow (hα : Order.IsSuccPrelimit α) {δ : Label.{u}}
    (hδ : ⊥ < δ) :
    IsDeterminedWithin (receivingFamily (DU (isLowAdmission_selfLow topsSelf_sub) selfLow_T hα
      (isSelfVisible_top 2)) δ) (T α) Fin.castSuccEmb (T α) := by
  rw [← utop_top_eq_T]
  refine isDeterminedWithin_DU_of _ _ hα (isSelfVisible_top 2) (Or.inr rfl) hδ
    fun q hq hqL hqc ↦ ?_
  have he' : q (oR _ 1) = ⊥ := by
    have e := hqc 1
    change min (q (oR _ 1)) δ = min ⊥ δ at e
    rw [min_bot_left] at e
    rcases min_eq_bot.mp e with h | h
    · exact h
    · exact absurd h hδ.ne'
  have hge (z : Fin 5) (hz : lab (⊤ : Label.{u}) ⊤ ⊤ z = ⊤) : δ ≤ q (oR _ z) := by
    have e := hqc z
    rw [hz, min_eq_right le_top] at e
    exact min_eq_right_iff.mp e
  have hsup : loSelf.sup (fun x ↦ q (oR (SelfLowG.{u} (3 : Fin 5) 4 2 loSelf topsSelf) x)) = ⊥ := by
    simp [loSelf, he']
  refine ⟨?_, ?_⟩
  · refine eq_top_of_admittedSelfLow topsSelf_sub (hq.isLawfulBelow _) hqL (by simp [topsSelf]) ?_
    rw [hsup]
    exact hδ.trans_le (hge 3 rfl)
  · refine eq_top_of_admittedSelfLow topsSelf_sub (hq.isLawfulBelow _) hqL (by simp [topsSelf]) ?_
    rw [hsup]
    exact hδ.trans_le (hge 4 rfl)

/-- **The coatom form for the twisted donor through the clause.** -/
theorem coatomCutoffDetermination_U_selfLow (hα : Order.IsSuccLimit α) {v : Label.{u}}
    (hv : IsSelfVisible 2 v) (hvα : AtStage α v) (hvt : v ≠ ⊤) :
    ∃ D' ∈ (T α).cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some (Utop hv hvα) ∧
      ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
        IsDeterminedWithin (receivingFamily D' δ) (T α) Fin.castSuccEmb (Utop hv hvα) := by
  have hvlt : v < (α : Label.{u}) := hvα.resolve_right hvt
  obtain ⟨δ, hδ, hvδ⟩ := exists_permittedCutoff_gt hα hvlt
  exact ⟨_, mem_cofaces_DU _ _ hα.isSuccPrelimit hv hvα,
    (restrictFace_DU (isLowAdmission_selfLow topsU_sub) (selfLow_Utop v) hα.isSuccPrelimit hv
      hvα).2, δ, hδ, isDeterminedWithin_DU_selfLow hα.isSuccPrelimit hv hvα hvδ⟩

/-- **The coatom form for the input itself through the clause.** -/
theorem coatomCutoffDetermination_T_selfLow (hα : Order.IsSuccLimit α) :
    ∃ D' ∈ (T α).cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some (T α) ∧
      ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
        IsDeterminedWithin (receivingFamily D' δ) (T α) Fin.castSuccEmb (T α) := by
  obtain ⟨δ, hδ, hδ0⟩ := exists_permittedCutoff_gt hα (w := ⊥) (WithBot.bot_lt_coe _)
  have hface := (restrictFace_DU (isLowAdmission_selfLow topsSelf_sub) selfLow_T
    hα.isSuccPrelimit (isSelfVisible_top 2) (Or.inr rfl)).2
  rw [utop_top_eq_T] at hface
  exact ⟨_, mem_cofaces_DU _ _ hα.isSuccPrelimit (isSelfVisible_top 2) (Or.inr rfl), hface, δ,
    hδ, isDeterminedWithin_DS_selfLow hα.isSuccPrelimit hδ0⟩

end VaughtConjecture.MixedSeed
