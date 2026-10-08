/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2OwnerAt
import VaughtConjecture.Continuation.H2Final

/-!
# The root below the designated tops fails at a legal context (work file)

WORK FILE (branch `research/work-ownerAt`).  No `sorry`.

**`H2.RootBelowTopsAt 1` is false** (`OwnerGradeOneTop.not_rootBelowTopsAt_one`), at the legal
source-gap context `OwnerGradeOneTop.ctx` of the owner lane (two points, grade `1`, lost point
`1`, owner the cell `2` at `(univ, 1)`, lost top the cell `1` at `({1}, 1)`, root top the cell `0`
at `({0}, 1)`), with the context itself as donor.  Its lawful labellings on the cells of grade `1`
satisfy `w 1 ≤ w 0 ≤ w 2` (`OwnerGradeOneTop.conditions_univ`): the designated lost top may lie
strictly below the root top.  The donor face `(ω + 2, 2, ω·2 + 2, ⊥)` on the grade-`1` faces, the
cap `1`, the designation `Lo = {3}`, all cells designated: the designated top `1` has value `2`,
at least the cap and above the replaced low maximum `⊥`, while the root has value `ω + 2`.

So the cap through the lost point at the root maximum (`H2.ownerLoweringBelow_of_rootBelowTops`)
is too strong as a route: the lost top lies below the root top in the rows of the owner, and the
cap has to be taken on the cells read by the owner at most the lost top, not on the cells through
the lost point (the construction of the owner lane at grade `1`, with the owner alone at its graded
index).  The residual shape that fails: a root cell labelled `⊤`, read by the owner above the lost
top, whose donor value is above a designated top.
-/

universe u

namespace VaughtConjecture.OwnerGradeOneTop

open Finset Label CellScheme StageType FieldAdmission H2
open SeparatedInstance (omegaAddTwo)
open SeparationObstruction (low low_lt_omegaAddTwo)
open OwnerPartner (high omegaAddTwo_lt_high)
open OwnerGradeOne (cells)

private theorem sv_low : IsSelfVisible 1 low.{u} := (isSelfVisible_natCast 2).mpr (by omega)

private theorem sv_omegaAddTwo : IsSelfVisible 1 omegaAddTwo.{u} :=
  isSelfVisible_coe_add Ordinal.isSuccLimit_omega0.isSuccPrelimit (by omega)

private theorem sv_high : IsSelfVisible 1 high.{u} :=
  OwnerPartner.isSelfVisible_high.mono (by omega)

/-- **The root below the designated tops fails at `OwnerGradeOneTop.ctx`**, with the context itself
as donor. -/
theorem not_rootBelowTops (α : Ordinal.{u}) :
    ¬ RootBelowTops (StageType.faceCell (restrictFace_ctx α)) 1 (LawfulAt (ctx α) 1)
      ((({3} : Finset (Fin 4)) : Finset (Fin (ctx α).card)).filter
        fun x ↦ (ctx α).toCellScheme.grade x ≤ 1) Finset.univ := by
  intro hres
  set g : Fin (ctx α).card → Label.{u} := lab omegaAddTwo low high ⊥ with hgdef
  have hg : LawfulAt (ctx α) 1 g := by
    refine ⟨by exact isLawfulBelow_of_isLawful (isLawful_lab sv_omegaAddTwo sv_low sv_high
      (isSelfVisible_bot 2) bot_le low_lt_omegaAddTwo.le
      omegaAddTwo_lt_high.le) _, fun d hd ↦ ?_⟩
    have key : ∀ d : Fin 4, ¬ cells.grade d ≤ 1 → d = 3 := by decide
    obtain rfl := key d hd
    rfl
  have h1 : IsSelfVisible 1 (1 : Label.{u}) := isSelfVisible_one.mpr le_rfl
  have hfilt : ((({3} : Finset (Fin 4)) : Finset (Fin (ctx α).card)).filter
      fun x ↦ (ctx α).toCellScheme.grade x ≤ 1) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr fun x hx hg1 ↦ ?_
    have hx3 : x = cellC α 3 := mem_singleton.mp hx
    subst hx3
    exact absurd hg1 (by change ¬ cells.grade 3 ≤ 1; decide)
  have hlow1 : (1 : Label.{u}) ≤ low := by simp [low]
  have hle := hres h1 hg (cellC α 1) (mem_univ _) hlow1 (by
    rw [hfilt, Finset.sup_empty, visibilityReplace_bot]
    exact (show (⊥ : Label.{u}) < 1 by simp).trans_le hlow1)
  -- the root contains the cell `0`
  obtain ⟨z, hz⟩ := StageType.exists_faceCell_eq_of_last_notMem (restrictFace_ctx α)
    (s := cellC α 0) (by change (1 : Fin 2) ∉ cells.scope 0; decide)
  have h0 : g (cellC α 0) ≤
      Finset.univ.sup fun x ↦ g (StageType.faceCell (restrictFace_ctx α) x) := by
    rw [← hz]
    exact Finset.le_sup (f := fun x ↦ g (StageType.faceCell (restrictFace_ctx α) x)) (mem_univ z)
  have := (h0.trans (le_visibilityReplace (by omega) _)).trans hle
  change omegaAddTwo ≤ low at this
  exact absurd this (not_le.mpr low_lt_omegaAddTwo)

/-- **`H2.RootBelowTopsAt 1` is false.** -/
theorem not_rootBelowTopsAt_one : ¬ RootBelowTopsAt.{u} 1 := by
  intro h
  have hs := isSourceGapContextAt_ctx.{u} 0 (Function.Embedding.ofIsEmpty (α := Fin 0))
  refine not_rootBelowTops.{u} 0 (h (ctx 0) (isLegal_ctx 0) _ hs le_rfl (restrictFace_ctx 0)
    (isLegal_ctx 0) (restrictFace_ctx 0) (fun x hx ↦ ?_) (fun x _ _ _ _ ↦ mem_univ x))
  have key : ∀ d : Fin 4, lab (⊤ : Label.{u}) ⊤ ⊤ ⊥ d ≠ ⊤ → d = 3 := by
    intro d hd
    fin_cases d <;> simp_all [lab]
  exact mem_singleton.mpr (key x hx)

end VaughtConjecture.OwnerGradeOneTop

namespace VaughtConjecture.H2

/-- **h2 with the lost point last with `H2.RootBelowTopsAt` in place of owner lowering below the
designated tops** (`H2.coatomCutoffDeterminationLastOnly_of` with
`H2.ownerLoweringBelowAt_of_rootBelowTopsAt`).  **It rests on refuted inputs**: the residual
`RootBelowTopsAt` fails at `k = 1` (`OwnerGradeOneTop.not_rootBelowTopsAt_one`; it is assumed here
only at `k ≥ 2`, where it is open), and `ExtAboveAt` fails at `k = 2`. -/
theorem coatomCutoffDeterminationLastOnly_of_rootBelowTops
    (hres : ∀ k, 2 ≤ k → RootBelowTopsAt.{u} k) (hext : ∀ k, 2 ≤ k → ExtAboveAt.{u} k) :
    CoatomCutoffDeterminationLastOnly.{u} :=
  coatomCutoffDeterminationLastOnly_of
    (fun k hk ↦ ownerLoweringBelowAt_of_rootBelowTopsAt (hres k hk)) hext

end VaughtConjecture.H2
