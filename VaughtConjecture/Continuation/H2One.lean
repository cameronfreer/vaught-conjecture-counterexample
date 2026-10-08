/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2Two

/-!
# h2 at two points, top grade `1`: the state-level provisions (work file)

WORK FILE (branch `research/work-twolift`).  No `sorry`.

At top grade `1` the clause `H2.SelfLowG o r 1 Lo Tops` is an admission of states from donor
raising and owner lowering at the grade `1` (`H2.stateAdmission_one`): the order law at the owner
and the frontier bound (`StageType.IsSourceGapContextAt.frontier_le`) come from the context, as at
the grade `2` (`H2.stateAdmission_two`).  Unlike the grade `2`, owner lowering is a hypothesis here:
`FieldAdmission.ownerLowering_of_isLegal` needs the grade of the owner above the arity of the
common face, and at two points both are `1`.  Its proof lifts the root of the donor face capped at
`h` to the context and then caps the cells of the owner's grade at `h`
(`CellScheme.Rows.IsLawful.capTopGrade`); with `n < K` the root cells have lower grade and are
kept.  At `K = n = 1` the root cells (scope the common point, grade `1`) have the owner's grade, so
that cap also caps the root, which must be kept literally.  Capping only the cells through the
lost point (`CellScheme.Rows.IsLawful.min_const_of_mem_scope`) keeps the root but needs that
availability carry no root value above `h` into those cells: a root cell of grade `1` with value
above `h` lies below every cell of graded index `(univ, 1)`, the owner's, so some cell of that
graded index other than the owner must carry it.  That is the configuration owner lowering at
grade `1` has to handle.  The designation `Tops` is a parameter, so the
statement serves any designation (in particular one without the root-determined cells).
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission

variable {α : Ordinal.{u}}

/-- **The state-level provisions at grade `1`**, from donor raising and owner lowering at the
grade `1` (both hypotheses). -/
theorem stateAdmission_one {t' : StageType.{u} α 2} {n : ℕ}
    {g : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 1 (g.trans Fin.castSuccEmb) l o r) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α 2}
    (htbp : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)}
    (hDR : DonorRaising (StageType.faceCell hp) (StageType.faceCell htbp) 1 t'.rows.IsLawful
      tb.rows.IsLawful (rootTops hp l) Tops)
    (hOL : OwnerLowering (StageType.faceCell hp) (StageType.faceCell htbp) o r 1
      t'.rows.IsLawful tb.rows.IsLawful) :
    IsStateAdmission (StageType.faceCell hp) (StageType.faceCell htbp) 1 t'.rows.IsLawful
      tb.rows.IsLawful (SelfLowG o r 1 Lo Tops) := by
  refine selfLow_isStateAdmission (rootTops hp l) (fun f hf ↦ ?_) (fun f hf a ha ↦ ?_) hDR hOL
  · have := hf.orderly o
    rwa [hs.grade_owner] at this
  · exact hs.frontier_le hf ((StageType.label_faceCell hp a).trans ha.1) ha.2

end VaughtConjecture.H2
