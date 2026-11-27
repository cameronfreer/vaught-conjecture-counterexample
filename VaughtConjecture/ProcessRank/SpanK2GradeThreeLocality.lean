/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanK2GradeThreeSection

/-!
# Capped locality of two grade-three sections on the grade-two scheme of the test with `K = 2`

Process rank `ω₁`, the finite span of mutual rigidity: two states `P`, `Q` of the grade-three
catalogue `ProcessRank.k2Cat3` have sections (`ProcessRank.k2Sec3`) that agree on every cell of the
grade-two scheme after capping at `κ = agreementHeight (grid 3 16) P Q`.  This is the locality the
lawfulness of the grade-three rows will use when the grade-three cells are appended: the row of
the cell of `P` reads the cell of `Q` as `κ`, and reads the old cells through the section of `P`.

Compiled here (theorem named):
* **the grade-two rows agree capped below the grade two** (`ProcessRank.min_k2Phi_orbitCode_eq`):
  for the orbit codes at the grade two of two grade-three states, at every cap `Γ` self-visible
  and short at the grade two at which the codes agree capped, the rows `k2Phi` agree capped at
  `Γ`: on the ladder by `Scheme.LadderBaseData.min_stateExtOf_eq`, on the controllers by
  `Label.min_agreementHeight_eq_of_isShort`;
* **capped locality** (`ProcessRank.min_k2Sec3_eq`): `min (k2Sec3 P z) κ = min (k2Sec3 Q z) κ` at
  every cell `z`.  The cap `κ` is in `grid 3 16`, so self-visible and short at the grade three,
  the states agree capped at it (`Label.agreementHeight_spec`) and lie below `gridPoint 3 16`, and
  the decoders of `P` and of `Q` keep the capped agreement
  (`Label.min_upperDecoderAt_comp_eq_of_codes`, at the grade two with cap grade three);
* **the witness form** (`ProcessRank.transformsTo_k2Sec3`): the section of `Q` transforms to the
  section of `P` capped at `κ` through the witness `(constStepSuppressor 3 κ, id)`, the form of the
  locality clause of `CellScheme.Rows.isLawfulBelow_iff_forall` at the cell of `Q`.

Open: the grade-three cells and their consistency, the grade four, legality of the completed
scheme, the four-point span of mutual rigidity of the test pair, and the countable upper bound on
the Scott classes.  None of these is claimed here.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label
open scoped Ordinal

/-- The members of a grid are short at its grade. -/
theorem isShort_of_mem_grid {k B : ℕ} {x : Label.{u}} (hx : x ∈ grid k B) : IsShort k x := by
  rcases mem_grid.mp hx with rfl | ⟨b, -, rfl⟩
  · exact isShort_bot k
  · exact isShort_gridPoint k b

/-- **The grade-two rows of the orbit codes of two grade-three states agree capped** at every cap
`Γ` self-visible and short at the grade two at which the codes agree capped. -/
theorem min_k2Phi_orbitCode_eq {P Q : Fin k2AttachmentBase.{u}.S.card → Label.{u}}
    (hP : P ∈ k2Cat3) (hQ : Q ∈ k2Cat3) (Γ : Label.{u}) (hΓ : IsSelfVisible 2 Γ)
    (hΓs : IsShort 2 Γ) (hag : ∀ d, min (orbitCode 2 P d) Γ = min (orbitCode 2 Q d) Γ)
    (z : Fin k2Grade2.{u}.card) :
    min (k2Phi (orbitCode 2 P) z) Γ = min (k2Phi (orbitCode 2 Q) z) Γ := by
  obtain ⟨hPB, hPl, -, -, -⟩ := mem_k2Cat2.mp (orbitCode_mem_k2Cat2 hP)
  obtain ⟨hQB, hQl, -, -, -⟩ := mem_k2Cat2.mp (orbitCode_mem_k2Cat2 hQ)
  have hP1 := isLawfulBelow_one_of_two hPl
  have hQ1 := isLawfulBelow_one_of_two hQl
  induction z using Fin.addCases with
  | left t =>
    rw [k2Phi_castAdd, k2Phi_castAdd]
    by_cases hΓ0 : Γ = ⊥
    · rw [hΓ0, min_bot_right, min_bot_right]
    rw [k2ControllerRow_of_isLawfulBelow hP1, k2ControllerRow_of_isLawfulBelow hQ1]
    exact Scheme.LadderBaseData.min_stateExtOf_eq (B := k2AttachmentBase) k2_card_le hΓ0
      (hΓ.mono (by decide)) hQ1 hP1 hag t
  | right i =>
    rw [k2Phi_natAdd, k2Phi_natAdd]
    exact min_agreementHeight_eq_of_isShort hΓ hΓs (fun e ↦ ⟨hPB e, hQB e⟩) hag _

/-- **Capped locality of two grade-three sections**: the sections of two grade-three states agree
on every cell of the grade-two scheme after capping at the agreement height of the states in
`grid 3 16`. -/
theorem min_k2Sec3_eq {P Q : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hP : P ∈ k2Cat3)
    (hQ : Q ∈ k2Cat3) (z : Fin k2Grade2.{u}.card) :
    min (k2Sec3 P z) (agreementHeight (grid 3 16) P Q) =
      min (k2Sec3 Q z) (agreementHeight (grid 3 16) P Q) := by
  obtain ⟨hPB, -, -, -, -⟩ := mem_k2Cat3.mp hP
  have hκ := agreementHeight_spec (bot_mem_grid 3 16) P Q
  exact min_upperDecoderAt_comp_eq_of_codes (k := 2) (K := 3) (B := 16) (by decide)
    (isSelfVisible_of_mem_grid hκ.1) (isShort_of_mem_grid hκ.1)
    (fun d ↦ le_gridPoint_of_mem_codeGrid (hPB d)) hκ.2 k2Phi
    (fun Γ hΓ hΓs hag z ↦ min_k2Phi_orbitCode_eq hP hQ Γ hΓ hΓs hag z) z

/-- **Capped locality in the witness form**: the section of `Q` transforms to the section of `P`
capped at `κ = agreementHeight (grid 3 16) P Q` through the witness `(constStepSuppressor 3 κ, id)`.
This is the locality clause of the lawfulness of the row of the cell of `P` at the cell of `Q`,
which the row of `P` reads as `κ`, on the old cells. -/
theorem transformsTo_k2Sec3 {P Q : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hP : P ∈ k2Cat3)
    (hQ : Q ∈ k2Cat3) :
    TransformsTo (fun d : Fin k2Grade2.{u}.card ↦ k2Grade2.{u}.toCellScheme.grade d) (k2Sec3 Q)
      (fun d ↦ min (k2Sec3 P d) (agreementHeight (grid 3 16) P Q)) := by
  have hκv : IsSelfVisible 3 (agreementHeight (grid 3 16) P Q) :=
    isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid 3 16) P Q).1
  refine ⟨constStepSuppressor 3 (agreementHeight (grid 3 16) P Q), id,
    ⟨antitone_constStepSuppressor _ _, isSelfVisible_constStepSuppressor hκv, rfl, monotone_id,
      fun _ _ _ _ _ ↦ rfl⟩, fun d ↦ ?_⟩
  rw [constStepSuppressor_of_le _ ((k2Grade2_grade_le d).trans (by decide)), id]
  exact min_k2Sec3_eq hP hQ d

end VaughtConjecture.ProcessRank
