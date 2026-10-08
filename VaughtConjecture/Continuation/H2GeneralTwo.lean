/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2GeneralOwner
import VaughtConjecture.Continuation.H2OneRaise

/-!
# h2 at every arity: the engine at two points (work file)

WORK FILE (branch `research/work-h2`).  No `sorry`.

**The engine at two points** (`H2.admittedCompletionsAt_one`, the input `H2.AdmittedCompletionsAt`
at `k = 1`): at the grade `1` it is `H2.exists_completion_recProp_one_of_admission` (the grade-`1`
faces are `H2.LawfulOne`), and at the grade `2` it is `H2.exists_completion_of_stateAdmission`
(the grade-`2` faces are the lawful labellings, `H2.lawfulAt_iff_isLawful`).

So **at two points the completions with the reading property follow from owner lowering below the
full grade alone** (`H2.hasRecCompletions_one_of_below`): the SCAFFOLD
`H2.exists_completion_recProp_one` of `VaughtConjecture.Continuation.H2Two` is not needed once
`H2.OwnerLoweringBelowAt 1` (owner lowering between the grade-`1` faces at grade `1`) holds.
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission

variable {α : Ordinal.{u}}

/-- An admission of states passes along equivalent classes of faces. -/
theorem isStateAdmission_congr {ιC ιD ιR : Type*} {rc : ιR → ιC} {rd : ιR → ιD} {K : ℕ}
    {C C' : (ιC → Label.{u}) → Prop} {D D' : (ιD → Label.{u}) → Prop}
    {Adm : (ιC → Label.{u}) → (ιD → Label.{u}) → Prop} (hC : ∀ f, C f ↔ C' f)
    (hD : ∀ f, D f ↔ D' f) (h : IsStateAdmission rc rd K C D Adm) :
    IsStateAdmission rc rd K C' D' Adm where
  bot := h.bot
  comp := h.comp
  context hh _ _ _ hL hR hy hadm hf hfL := by
    obtain ⟨W, hW, hWr, hWR, hWa⟩ :=
      h.context hh ((hC _).mpr hL) ((hD _).mpr hR) hy hadm ((hC _).mpr hf) hfL
    exact ⟨W, (hD W).mp hW, hWr, hWR, hWa⟩
  donor hh _ _ _ hL hR hy hadm hf hfR := by
    obtain ⟨W, hW, hWr, hWL, hWa⟩ :=
      h.donor hh ((hC _).mpr hL) ((hD _).mpr hR) hy hadm ((hD _).mpr hf) hfR
    exact ⟨W, (hC W).mp hW, hWr, hWL, hWa⟩

/-- **The engine at two points** (the input `H2.AdmittedCompletionsAt` at `k = 1`). -/
theorem admittedCompletionsAt_one : AdmittedCompletionsAt.{u} 1 := by
  intro α K n t' hleg g o r hs p hp tb htbleg htbp Lo Tops _ hTops hS
  have hK0 : 0 < K := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  have hK2 : K ≤ 2 := hs.grade_owner ▸ t'.grade_le o
  rcases (show K = 1 ∨ K = 2 by omega) with rfl | rfl
  · exact exists_completion_recProp_one_of_admission hleg hs hp htbleg htbp
      (fun x hx ↦ ⟨(hTops x hx).1, (hTops x hx).2.1⟩) hS
  · have hLo2 : (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ 2) = Lo :=
      filter_true_of_mem fun x _ ↦ tb.grade_le x
    rw [hLo2] at hS
    exact exists_completion_of_stateAdmission hleg hs.grade_owner hp htbleg htbp
      (fun x hx ↦ (hTops x hx).1)
      (isStateAdmission_congr (fun _ ↦ lawfulAt_iff_isLawful t'.grade_le)
        (fun _ ↦ lawfulAt_iff_isLawful tb.grade_le) hS)

/-- **Completions with the reading property at two points from owner lowering below the full
grade** (no SCAFFOLD). -/
theorem hasRecCompletions_one_of_below (hOL : OwnerLoweringBelowAt.{u} 1) :
    HasRecCompletions.{u} 1 :=
  hasRecCompletions_of (donorRaisingAt 1) (ownerLoweringAt_of_below hOL) admittedCompletionsAt_one

end VaughtConjecture.H2
