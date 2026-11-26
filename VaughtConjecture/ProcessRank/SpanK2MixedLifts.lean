/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanK2GradeTwoRows
import VaughtConjecture.ProcessRank.SpanMirrorDisjoint

/-!
# The mixed-face lifts of the mirrored grade-two scheme of the test with `K = 2`

Process rank `ω₁`, the finite span of mutual rigidity: the capped lifts out of the mixed faces of
the interval plan of `Fin 4` (`{1, 2}`, `{0, 1, 2}`, `{1, 2, 3}`) on the grade-two scheme
`ProcessRank.k2Grade2` mirrored at those faces (`ProcessRank.k2Mirror`).

**The premises of the mirror theorem** (`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed`) for
`k2Grade2`, with the attachment cells `ProcessRank.k2Att`, the ladder points `ProcessRank.k2Lad`,
the rank members at the height `8` and their rank profiles, compiled here (theorem named):
* positive grades (`ProcessRank.k2Grade2_hpos`), the attachment cells keep their graded indices
  (`ProcessRank.k2Grade2_hatt`), every cell of proper scope is an attachment cell
  (`ProcessRank.k2Grade2_hproperScope`), every attachment cell lies in `{0, 1}` or `{2, 3}`
  (`ProcessRank.k2_hAtt`), so no mixed face lies inside the scope of a cell of proper scope
  (`ProcessRank.k2Grade2_hmix`);
* the ladder: the ladder points at `(univ, 1)` (`ProcessRank.k2Grade2_hlad`), their rows
  (`ProcessRank.k2Grade2_hrowLL`, `ProcessRank.k2Grade2_hrowLA`), and every cell at `(univ, 1)` a
  ladder point (`ProcessRank.k2Grade2_hone`);
* a controller at the grade two (`ProcessRank.k2Grade2_hexist`, the controller
  `ProcessRank.k2SepCell`);
* the controller rows (`ProcessRank.k2Grade2_hreadMember`, `ProcessRank.k2Grade2_hshadow`,
  `ProcessRank.k2Grade2_htwinAbove`).

**The lifts** (`ProcessRank.k2Mirror_cappedLift`): from `(U, j)` to `(W, k)` for a mixed face `U`,
a face `W ⊇ U` of the interval plan, and `1 ≤ j ≤ k ≤ 2`.  A face of the plan containing a mixed
face is mixed or the ground set; the lift at the grade `j` is
`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed_mixed` or
`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed_univ`, and the move from `j` to `k` on `W` is
`CellScheme.Rows.cappedLift_of_fst_eq`.  The concrete instance from `({1, 2}, 1)` to
`({0, 1, 2}, 2)` is `ProcessRank.k2Mirror_cappedLift_one_two`.

Open: the controller conditions across grades, the grades three and four, legality of the completed
scheme, the four-point span of mutual rigidity of the test pair, and the countable upper bound on
the Scott classes.  None of these is claimed here.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label MirrorAttachment
open scoped Ordinal

set_option quotPrecheck false in
/-- The index of a ladder point for a member. -/
local notation "idx" => ladderIndex 8 (Scheme.rankProf k2AttachmentBase.S 8) Prod.fst
  (Scheme.ladderCeil (Scheme.rankProf k2AttachmentBase.S 8))

/-- The attachment cells of the grade-two scheme. -/
noncomputable abbrev k2Att (e : Fin k2AttachmentBase.{u}.S.card) : Fin k2Grade2.{u}.card :=
  Fin.castAdd _ (Fin.castAdd _ e)

/-- The ladder points of the grade-two scheme. -/
noncomputable abbrev k2Lad
    (v : Scheme.LadderPt k2AttachmentBase.{u}.S (Scheme.RankMember k2AttachmentBase.{u}.S 8) 8) :
    Fin k2Grade2.{u}.card :=
  Fin.castAdd _ (k2LadPt v)

/-- The mixed faces of the interval plan of `Fin 4`. -/
abbrev k2MF : Finset (Finset (Fin 4)) := mixedFacesOf (Geometry.intervalPlan univ)

/-! ### Graded indices -/

/-- An old cell of the grade-two scheme keeps its graded index in the ladder. -/
theorem k2Grade2_gradedIndex_castAdd (z : Fin k2Ladder.{u}.card) :
    k2Grade2.{u}.toCellScheme.gradedIndex (Fin.castAdd _ z) =
      k2Ladder.{u}.toCellScheme.gradedIndex z :=
  Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ z

/-- The controllers lie at `(univ, 2)`. -/
theorem k2Grade2_gradedIndex_natAdd (i : Fin k2Cat2.{u}.card) :
    k2Grade2.{u}.toCellScheme.gradedIndex (Fin.natAdd _ i) = ((univ : Finset (Fin 4)), 2) :=
  Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i

/-- An attachment cell keeps its graded index in the ladder. -/
theorem k2Ladder_gradedIndex_castAdd (e : Fin k2AttachmentBase.{u}.S.card) :
    k2Ladder.{u}.toCellScheme.gradedIndex (Fin.castAdd _ e) =
      k2AttachmentBase.{u}.S.toCellScheme.gradedIndex e :=
  Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e

/-- The ladder points lie at `(univ, 1)` in the ladder. -/
theorem k2Ladder_gradedIndex_natAdd
    (j : Fin (Scheme.ladderCard k2AttachmentBase.{u}.S
      (Scheme.RankMember k2AttachmentBase.S 8) 8)) :
    k2Ladder.{u}.toCellScheme.gradedIndex (Fin.natAdd _ j) = ((univ : Finset (Fin 4)), 1) :=
  Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ j

/-! ### The premises of the mirror theorem -/

/-- **Positive grades** (`hpos`). -/
theorem k2Grade2_hpos : ∀ d, 1 ≤ k2Grade2.{u}.toCellScheme.grade d :=
  fun d ↦ k2Grade2Type.isWellFormed.isWellFormed.grade_pos d

/-- **The attachment cells keep their graded indices** (`hatt`). -/
theorem k2Grade2_hatt : ∀ e, k2Grade2.{u}.toCellScheme.gradedIndex (k2Att e) =
    k2AttachmentBase.{u}.S.toCellScheme.gradedIndex e :=
  fun e ↦ (k2Grade2_gradedIndex_castAdd _).trans (k2Ladder_gradedIndex_castAdd e)

/-- **Every cell of proper scope is an attachment cell** (`hproperScope`). -/
theorem k2Grade2_hproperScope :
    ∀ x, k2Grade2.{u}.toCellScheme.scope x ≠ univ → ∃ e, x = k2Att e := by
  intro x hx
  induction x using Fin.addCases with
  | right i => exact absurd (congrArg Prod.fst (k2Grade2_gradedIndex_natAdd i)) hx
  | left z =>
    induction z using Fin.addCases with
    | left e => exact ⟨e, rfl⟩
    | right j =>
      exact absurd ((congrArg Prod.fst (k2Grade2_gradedIndex_castAdd _)).trans
        (congrArg Prod.fst (k2Ladder_gradedIndex_natAdd j))) hx

/-- **Every attachment cell lies in `{0, 1}` or `{2, 3}`** (`hAtt`). -/
theorem k2_hAtt : ∀ e, k2AttachmentBase.{u}.S.toCellScheme.scope e ⊆ leftFace ∨
    k2AttachmentBase.{u}.S.toCellScheme.scope e ⊆ rightFace :=
  fun e ↦ (by decide : ∀ e : Fin 8, attScope e ⊆ leftFace ∨ attScope e ⊆ rightFace) e

/-- **No mixed face lies inside the scope of a cell of proper scope** (`hmix`). -/
theorem k2Grade2_hmix : ∀ c, k2Grade2.{u}.toCellScheme.scope c ≠ univ →
    ∀ U ∈ k2MF, ¬ U ⊆ k2Grade2.{u}.toCellScheme.scope c :=
  hmix_of_attachment k2Grade2_hatt k2Grade2_hproperScope k2_hAtt

/-- **The ladder points lie at `(univ, 1)`** (`hlad`). -/
theorem k2Grade2_hlad :
    ∀ p, k2Grade2.{u}.toCellScheme.gradedIndex (k2Lad p) = ((univ : Finset (Fin 4)), 1) :=
  fun _ ↦ (k2Grade2_gradedIndex_castAdd _).trans (k2Ladder_gradedIndex_natAdd _)

/-- **A ladder point reads another** through its ceiling and the ladder index of its member
(`hrowLL`). -/
theorem k2Grade2_hrowLL : ∀ p v, k2Grade2.{u}.rowAt (k2Lad p) (k2Lad v) =
    ladderSource (Scheme.ladderCeil (Scheme.rankProf k2AttachmentBase.S 8) p) (idx p.1 v) := by
  intro p v
  refine (Scheme.rowAt_appendFullCells_castAdd _ _).trans ?_
  refine (Scheme.rowAt_ladderBase_ladder (hS := k2AttachmentBase.noFull)
    k2AttachmentBase.wf p v).trans ?_
  rw [Scheme.baseIndex_natAdd, Equiv.symm_apply_apply]

/-- **A ladder point reads an attachment cell of grade one as the ladder point of its member over
that cell** (`hrowLA`). -/
theorem k2Grade2_hrowLA : ∀ p e, k2AttachmentBase.{u}.S.toCellScheme.grade e = 1 →
    k2Grade2.{u}.rowAt (k2Lad p) (k2Att e) =
      k2Grade2.{u}.rowAt (k2Lad p) (k2Lad (p.1, Sum.inr e)) := by
  intro p e he
  rw [k2Grade2_hrowLL]
  refine (Scheme.rowAt_appendFullCells_castAdd _ _).trans ?_
  refine (Scheme.rowAt_ladderBase_old (hS := k2AttachmentBase.noFull)
    k2AttachmentBase.wf p he).trans ?_
  have hp := ladderIndex_parent (H := 8) (prof := Scheme.rankProf k2AttachmentBase.S 8)
    (parent := Prod.fst) (ceil := Scheme.ladderCeil (Scheme.rankProf k2AttachmentBase.S 8))
    (Scheme.ladderCeil_le (Scheme.rankProf_le k2AttachmentBase.S 8)) (p.1, Sum.inr e)
  rw [hp]
  rfl

/-- **Every cell at `(univ, 1)` is a ladder point** (`hone`). -/
theorem k2Grade2_hone : ∀ x, k2Grade2.{u}.toCellScheme.gradedIndex x =
    ((univ : Finset (Fin 4)), 1) → ∃ p, x = k2Lad p := by
  intro x hx
  induction x using Fin.addCases with
  | right i =>
    exact absurd (congrArg Prod.snd (hx.symm.trans (k2Grade2_gradedIndex_natAdd i))) (by decide)
  | left z =>
    induction z using Fin.addCases with
    | left e =>
      exact absurd ((congrArg Prod.fst (k2Grade2_hatt e)).symm.trans (congrArg Prod.fst hx))
        (k2AttachmentBase.scope_ne_univ e)
    | right j =>
      refine ⟨(Scheme.ladderEquiv _ _ 8).symm j, ?_⟩
      change _ = Fin.castAdd _ (Fin.natAdd _ (Scheme.ladderEquiv _ _ 8 _))
      rw [Equiv.apply_symm_apply]

/-- **A controller at the grade two** (`hexist`, through the grade two). -/
theorem k2Grade2_hexist {j : ℕ} (hj : j ≤ 2) : ∀ k, 2 ≤ k → k ≤ j →
    ∃ f, k2Grade2.{u}.toCellScheme.gradedIndex f = ((univ : Finset (Fin 4)), k) := by
  intro k hk hkj
  obtain rfl : k = 2 := le_antisymm (hkj.trans hj) hk
  exact ⟨k2SepCell, k2SepCell_spec.1⟩

/-! ### The lifts -/

/-- **The mirrored grade-two scheme**: `k2Grade2` mirrored at the mixed faces of the interval
plan. -/
noncomputable abbrev k2Mirror : Scheme.{u} 4 := Scheme.mirror k2Grade2_hmix

/-- A face of the interval plan containing a mixed face is mixed or the ground set. -/
theorem mem_k2MF_or_eq_univ {U W : Finset (Fin 4)} (hU : U ∈ k2MF)
    (hW : W ∈ Geometry.intervalPlan univ) (hUW : U ⊆ W) : W ∈ k2MF ∨ W = univ := by
  by_cases hWu : W = univ
  · exact .inr hWu
  obtain ⟨hl, hr⟩ := not_subset_of_mem_mixedFacesOf U hU
  exact .inl (mem_filter.mpr ⟨hW, fun h ↦ hl (hUW.trans h), fun h ↦ hr (hUW.trans h), hWu⟩)

/-- **The mixed-face lifts through the grade two**: on the mirrored grade-two scheme the rows lift
capped from `(U, j)` to `(W, k)` for a mixed face `U` of the interval plan, a face `W ⊇ U` of the
plan and `1 ≤ j ≤ k ≤ 2`.  The controller conditions across grades, the grades three and four,
legality of the completed scheme, the four-point span of mutual rigidity and the countable upper
bound on the Scott classes stay open. -/
theorem k2Mirror_cappedLift {U W : Finset (Fin 4)} (hU : U ∈ k2MF)
    (hW : W ∈ Geometry.intervalPlan univ) (hUW : U ⊆ W) {j k : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hk2 : k ≤ 2) :
    k2Mirror.{u}.rows.CappedLift (X := (U, j)) (Y := (W, k)) ⟨hUW, hjk⟩ := by
  have : Fact (∀ U ∈ k2MF, 1 ≤ #U ∧ U ≠ univ) := ⟨mixedFacesOf_spec⟩
  have : Fact (∀ q d, Scheme.rankProf k2AttachmentBase.{u}.S 8 q d ≤ 8) :=
    ⟨fun _ _ ↦ Scheme.rankProf_le _ 8 _ _⟩
  have hjU : j ≤ #U := by
    rw [k2MF, mixedFacesOf_intervalPlan] at hU
    have h2 : 2 ≤ #U := by
      rcases mem_insert.mp hU with rfl | hU
      · decide
      rcases mem_insert.mp hU with rfl | hU
      · decide
      rw [mem_singleton.mp hU]
      decide
    omega
  have hj2 := hjk.trans hk2
  have hlift : k2Mirror.{u}.rows.CappedLift (X := (U, j)) (Y := (W, j)) ⟨hUW, le_rfl⟩ := by
    rcases mem_k2MF_or_eq_univ hU hW hUW with hWm | rfl
    · exact cappedLift_mirror_mixed_mixed (H := 8) (Att := k2AttachmentBase.S)
        (FA := leftFace) (FB := rightFace) (Pf := Scheme.RankMember k2AttachmentBase.S 8)
        (prof := Scheme.rankProf k2AttachmentBase.S 8) (att := k2Att) (lad := k2Lad)
        (by decide) isConsistent_k2Grade2 k2Grade2_hpos k2Grade2_hatt k2Grade2_hproperScope
        k2_hAtt (by decide) (by decide) not_subset_of_mem_mixedFacesOf k2Grade2_hlad
        k2Grade2_hrowLL k2Grade2_hrowLA k2Grade2_hone k2Grade2_hreadMember k2Grade2_hshadow
        k2Grade2_htwinAbove hU hWm hUW (k2Grade2_hexist hj2) hj1 hjU
    · exact cappedLift_mirror_mixed_univ (H := 8) (Att := k2AttachmentBase.S)
        (FA := leftFace) (FB := rightFace) (Pf := Scheme.RankMember k2AttachmentBase.S 8)
        (prof := Scheme.rankProf k2AttachmentBase.S 8) (att := k2Att) (lad := k2Lad)
        (by decide) isConsistent_k2Grade2 k2Grade2_hpos k2Grade2_hatt k2Grade2_hproperScope
        k2_hAtt (by decide) (by decide) not_subset_of_mem_mixedFacesOf k2Grade2_hlad
        k2Grade2_hrowLL k2Grade2_hrowLA k2Grade2_hone k2Grade2_hreadMember k2Grade2_hshadow
        k2Grade2_htwinAbove hU (k2Grade2_hexist hj2) hj1 hjU
  exact hlift.trans (CellScheme.Rows.cappedLift_of_fst_eq (X := (W, j)) (Y := (W, k))
    ⟨subset_refl _, hjk⟩ rfl)

/-- **The lift from `({1, 2}, 1)` to `({0, 1, 2}, 2)`** on the mirrored grade-two scheme. -/
theorem k2Mirror_cappedLift_one_two :
    k2Mirror.{u}.rows.CappedLift (X := (({1, 2} : Finset (Fin 4)), 1))
      (Y := (({0, 1, 2} : Finset (Fin 4)), 2)) ⟨by decide, by decide⟩ :=
  k2Mirror_cappedLift (by rw [k2MF, mixedFacesOf_intervalPlan]; decide) (by decide) (by decide)
    le_rfl one_le_two le_rfl

end VaughtConjecture.ProcessRank
