/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ApexLayer
import VaughtConjecture.Extension.CompletionInput
import VaughtConjecture.Extension.PinnedExtension

/-!
# The coatom extension from a seed

Roadmap, Layer 3 (the coatom extension construction: from the completion below the full grade to
the coatom extension property with apex); semantic contract, items 2–4.

A seed `F` of a completion input `I` (`CompletionInput.Seed`) is a stage type on `m + 2` points
(`CompletionInput.Seed.toStageType`) that is legal below the full grade
(`CompletionInput.Seed.isLegalBelowFullGrade`).  Its **completion**
(`CompletionInput.Seed.completion`) is its apex layer (`StageType.apexLayer`): it is legal, has a
cell of full scope and full grade `m + 2` carrying the largest label, and its faces along the two
coatoms are literally the two coatom types of `I`
(`CompletionInput.Seed.exists_coatomExtension`).

The literal faces are proved by the uniqueness of the enumeration of visible cells
(`Scheme.cellMap_eq_of_strictMono`): the old cells of the seed, and then of the apex layer, are
strictly monotone lower embeddings keeping scopes, rows, and labels, and every cell visible in a
coatom has scope other than the ground set, so it is old
(`StageType.restrictFace_eq_of_strictMono`).  The faces of the completion along the coatoms are
therefore those of the amalgam, which are the coatom types.

**The coatom extension property from seeds** (`StageType.HasApexCoatomExtensions.of_seed`): if
every completion input built by `CompletionInput.ofCoatoms` from two legal coatom types with a
common face has a seed, then `StageType.HasApexCoatomExtensions α` holds, and hence
`StageType.HasCoatomExtensions α` (`StageType.HasCoatomExtensions.of_seed`).  The obligation is
the same at every arity: two coatom types on one point over the empty face (`m = 0`) and on two
points (`m = 1`) give completion inputs of the same shape.  No hypothesis on the stage `α` is
used.

## References

The coatom extension with apex is [Kni26, Corollary 4.3.22], through the completion of
[Kni26, Definition 4.3.14] of the amalgam of [Kni26, Definition 4.3.1].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace CompletionInput.Seed

variable {α : Ordinal.{u}} {m : ℕ} {I : CompletionInput.{u} α m}

/-- The seed as a stage type on `m + 2` points. -/
def toStageType (F : Seed I) : StageType.{u} α (m + 2) where
  toScheme := F.scheme
  label := F.label
  isWellFormed := F.isWellFormed
  isCoded := F.isCoded
  isLawful := F.isLawful
  atStage := F.atStage

/-- **A seed is legal below the full grade.** -/
theorem isLegalBelowFullGrade (F : Seed I) : F.toStageType.IsLegalBelowFullGrade where
  isConsistent := F.isConsistent
  isBountiful := F.isBountiful
  grade_lt d := Nat.lt_succ_of_le (F.grade_le d)
  exists_gradedIndex_eq X hX hXn := F.isComplete X hX (Nat.le_of_lt_succ hXn)

/-- **The faces of a seed along a proper face are those of the amalgam**, including
definedness. -/
theorem restrictFace_toStageType (F : Seed I) {k : ℕ} (f : Fin k ↪ Fin (m + 2))
    (hf : univ.map f ≠ univ) :
    StageType.restrictFace f F.toStageType = StageType.restrictFace f I.amalgam := by
  refine StageType.restrictFace_eq_of_strictMono (t := F.toStageType) (s := I.amalgam) f
    (φ := F.embed) F.embed.strictMono F.isLowerEmbedding F.scope_embed F.comap_rows
    (F.isWellFormed.ground_eq.trans I.amalgam.isWellFormed.ground_eq.symm) F.faces_eq
    F.label_embed fun z hz ↦ F.mem_range_embed z fun he ↦ hf (eq_univ_of_forall fun x ↦ ?_)
  obtain ⟨y, rfl⟩ : x ∈ Set.range f := hz (by
    change x ∈ ((F.scheme.toCellScheme.scope z : Finset (Fin (m + 2))) : Set (Fin (m + 2)))
    rw [he]
    simp)
  exact mem_map_of_mem _ (mem_univ y)

/-- The **completion** of a seed: its apex layer, with one cell of full scope and full grade
`m + 2` labelled with the formal top. -/
noncomputable def completion (F : Seed I) : StageType.{u} α (m + 2) :=
  F.toStageType.apexLayer F.isLegalBelowFullGrade (Nat.succ_pos _)

/-- **The completion is legal.** -/
theorem isLegal_completion (F : Seed I) : F.completion.IsLegal :=
  StageType.isLegal_apexLayer _ _

/-- **The completion has an apex**: a cell of full scope and full grade `m + 2` carrying the
largest label. -/
theorem exists_apex_completion (F : Seed I) :
    ∃ d, F.completion.toCellScheme.gradedIndex d = (univ, m + 2) ∧
    ∀ e, F.completion.label e ≤ F.completion.label d :=
  StageType.exists_apex_apexLayer _ _

/-- The first coatom is not the whole ground set. -/
private theorem univ_map_left_ne : univ.map (Coatom.left m) ≠ univ := fun he ↦
  Coatom.last_notMem_univ_map_left (he ▸ mem_univ (Fin.last (m + 1)))

/-- The second coatom is not the whole ground set. -/
private theorem univ_map_right_ne : univ.map (Coatom.right m) ≠ univ := fun he ↦ by
  have h := mem_univ (Fin.castSucc (Fin.last m))
  rw [← he, Coatom.univ_map_right] at h
  exact notMem_erase _ _ h

/-- **The face of the completion along `Fin.castSuccEmb` is the first coatom type**, literally,
labels included. -/
theorem restrictFace_left_completion (F : Seed I) :
    StageType.restrictFace (Coatom.left m) F.completion = some I.left := by
  rw [completion, StageType.restrictFace_apexLayer _ _ _ univ_map_left_ne,
    F.restrictFace_toStageType _ univ_map_left_ne, I.restrictFace_left]

/-- **The face of the completion along `extendByLast Fin.castSuccEmb` is the second coatom
type**, literally, labels included. -/
theorem restrictFace_right_completion (F : Seed I) :
    StageType.restrictFace (Coatom.right m) F.completion = some I.right := by
  rw [completion, StageType.restrictFace_apexLayer _ _ _ univ_map_right_ne,
    F.restrictFace_toStageType _ univ_map_right_ne, I.restrictFace_right]

/-- **The coatom extension with apex from a seed** [Kni26, Corollary 4.3.22]: a legal stage type
on `m + 2` points whose faces along the two coatoms are the coatom types of `I`, with a cell of
full scope and full grade carrying the largest label. -/
theorem exists_coatomExtension (F : Seed I) : ∃ t : StageType.{u} α (m + 2), t.IsLegal ∧
    StageType.restrictFace Fin.castSuccEmb t = some I.left ∧
    StageType.restrictFace (extendByLast Fin.castSuccEmb) t = some I.right ∧
    ∃ d, t.toCellScheme.gradedIndex d = (univ, m + 2) ∧ ∀ e, t.label e ≤ t.label d :=
  ⟨F.completion, F.isLegal_completion, F.restrictFace_left_completion,
    F.restrictFace_right_completion, F.exists_apex_completion⟩

end CompletionInput.Seed

namespace StageType

variable {α : Ordinal.{u}}

/-- **The coatom extension property with apex from seeds** [Kni26, Corollary 4.3.22]: if the
completion input of any two legal coatom types with the same face along `Fin.castSuccEmb` has a
seed, then any two such types are the faces of one legal stage type with an apex. -/
theorem HasApexCoatomExtensions.of_seed
    (hseed : ∀ (m : ℕ) (ta tb : StageType.{u} α (m + 1)) (p : StageType.{u} α m)
      (hla : ta.IsLegal) (hlb : tb.IsLegal) (hpa : restrictFace Fin.castSuccEmb ta = some p)
      (hpb : restrictFace Fin.castSuccEmb tb = some p),
      Nonempty (CompletionInput.Seed (CompletionInput.ofCoatoms hla hlb hpa hpb))) :
    HasApexCoatomExtensions.{u} α := fun m ta tb p hla hlb hpa hpb ↦
  (hseed m ta tb p hla hlb hpa hpb).some.exists_coatomExtension

/-- **The coatom extension property from seeds**: forget the apex. -/
theorem HasCoatomExtensions.of_seed
    (hseed : ∀ (m : ℕ) (ta tb : StageType.{u} α (m + 1)) (p : StageType.{u} α m)
      (hla : ta.IsLegal) (hlb : tb.IsLegal) (hpa : restrictFace Fin.castSuccEmb ta = some p)
      (hpb : restrictFace Fin.castSuccEmb tb = some p),
      Nonempty (CompletionInput.Seed (CompletionInput.ofCoatoms hla hlb hpa hpb))) :
    HasCoatomExtensions.{u} α :=
  (HasApexCoatomExtensions.of_seed hseed).hasCoatomExtensions

end StageType

end VaughtConjecture
