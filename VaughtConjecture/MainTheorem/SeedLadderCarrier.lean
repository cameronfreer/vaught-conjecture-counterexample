/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.SeedLadderCompletion
import VaughtConjecture.MainTheorem.GrowthAdmittedCarrier
import VaughtConjecture.MainTheorem.GrowthCarrierExistence

/-!
# The ladder growth carrier at the seed position

Roadmap, Layer 3 ((R3) and (R4), the assembly of the recognizing growth carrier).

**The old cells of a completion.**  In the completion of a completion below the full grade
(`CompletionBelowFullGrade.completion`: the scheme with the apex appended), the cells of the
scheme keep their rows and graded indices (`CompletionBelowFullGrade.rowAt_completion_castSucc`),
and along every proper face the cells of the completion are the old cells of the amalgam, in their
order (`CompletionBelowFullGrade.cellMap_completion`).

## References

The completion of [Kni26, Definition 4.3.14]; the controllers of the growth step are those of
[Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)
  (hα : Order.IsSuccPrelimit α)

/-- **The completion reads the old cells as the scheme does.** -/
theorem rowAt_completion_castSucc (z x : Fin F.scheme.card) :
    (F.completion hα).toScheme.rowAt z.castSucc x.castSucc = F.scheme.rowAt z x :=
  Scheme.rowAt_appendFullCell_castSucc (h := F.isLegalBelowFullGrade.not_le) z x

/-- The old cells keep their graded indices in the completion. -/
theorem gradedIndex_completion_castSucc (z : Fin F.scheme.card) :
    (F.completion hα).toCellScheme.gradedIndex z.castSucc = F.scheme.toCellScheme.gradedIndex z :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc _ _ z

/-- The apex has the full grade. -/
theorem gradedIndex_completion_last :
    (F.completion hα).toCellScheme.gradedIndex (Fin.last _) =
      ((univ : Finset (Fin (m + 2))), m + 2) :=
  Scheme.appendFullCellScheme_gradedIndex_last _ _

/-- **Along a proper face the cells of the completion are the old cells of the amalgam**, in
their order. -/
theorem cellMap_completion {k : ℕ} (f : Fin k ↪ Fin (m + 2)) (hf : univ.map f ≠ univ)
    {i : Fin (I.amalgam.toScheme.comap f).card}
    {j : Fin ((F.completion hα).toScheme.comap f).card} (hij : (i : ℕ) = j) :
    (F.completion hα).toScheme.cellMap f j =
      (F.embed (I.amalgam.toScheme.cellMap f i)).castSucc := by
  refine Scheme.cellMap_eq_of_strictMono_of_mem_range f (S := I.amalgam.toScheme)
    (T := (F.completion hα).toScheme) (φ := fun d ↦ (F.embed d).castSucc)
    (fun a b hab ↦ Fin.castSucc_lt_castSucc_iff.mpr (F.embed.strictMono hab)) (fun d ↦ ?_)
    (fun z hz ↦ ?_) hij
  · change (F.scheme.appendFullCellScheme (m + 2)).scope (F.embed d).castSucc = _
    rw [Scheme.appendFullCellScheme_scope_castSucc, F.scope_embed]
  · induction z using Fin.lastCases with
    | last =>
      exfalso
      change (((F.truncate hα).toScheme.appendFullCellScheme (m + 2)).scope (Fin.last _) :
        Set (Fin (m + 2))) ⊆ Set.range f at hz
      rw [Scheme.appendFullCellScheme_scope_last, coe_univ] at hz
      exact hf (eq_univ_of_forall fun x ↦ by
        obtain ⟨y, rfl⟩ := hz (Set.mem_univ x)
        exact mem_map_of_mem _ (mem_univ y))
    | cast z =>
      change (((F.truncate hα).toScheme.appendFullCellScheme (m + 2)).scope z.castSucc :
        Set (Fin (m + 2))) ⊆ Set.range f at hz
      rw [Scheme.appendFullCellScheme_scope_castSucc] at hz
      have hz' : (F.scheme.toCellScheme.scope z : Set (Fin (m + 2))) ⊆ Set.range f := hz
      obtain ⟨d, rfl⟩ := F.mem_range_embed z fun he ↦ hf (eq_univ_of_forall fun x ↦ by
        rw [he, coe_univ] at hz'
        obtain ⟨y, rfl⟩ := hz' (Set.mem_univ x)
        exact mem_map_of_mem _ (mem_univ y))
      exact ⟨d, rfl⟩

end CompletionBelowFullGrade

end VaughtConjecture
