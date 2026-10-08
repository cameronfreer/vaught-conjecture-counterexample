/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2GeneralZero
import VaughtConjecture.Continuation.H2OwnerOneFace

/-!
# h2 with the lost point last: the assembled statement (work file)

WORK FILE (branch `research/work-h2`).  No `sorry`.

**The owner alone at its graded index** (`H2.OwnerOnlyAtIndex`): the condition under which owner
lowering below the designated tops between the grade-`1` faces holds at two points
(`H2.ownerLoweringBelow_oneFace`, from the owner lane), and so the case of top grade `1` at two
points (`H2.exists_completion_recProp_one_of_owner`).  It is not implied by the source-gap clauses:
the cells of graded index `(univ, 1)` other than the owner are not constrained by them.

**h2 with the lost point last** (`H2.coatomCutoffDeterminationLastOnly_of`), for the contexts whose
owner is alone at its graded index when `k = 1` and `K = 1`
(`H2.CoatomCutoffDeterminationLastOnly`), from two inputs at `k ≥ 2`: owner lowering below the
designated tops below the full grade (`H2.OwnerLoweringBelowAt`) and the extension above `K`
(`H2.ExtAboveAt`).  The cases `k = 0` (one point) and `k = 1` (two points) are compiled.
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission

variable {α : Ordinal.{u}}

/-- The **owner is alone at its graded index**. -/
def OwnerOnlyAtIndex {k : ℕ} (t' : StageType.{u} α k) (o : Fin t'.card) : Prop :=
  ∀ u, t'.toCellScheme.gradedIndex u = t'.toCellScheme.gradedIndex o → u = o

/-- **The case of top grade `1` at two points with the lost point last**, when the owner is alone at
its graded index (`H2.exists_completion_recProp_one_of_owner`). -/
theorem exists_completion_recProp_one_of_only {t' : StageType.{u} α 2} (hleg : t'.IsLegal)
    {n : ℕ} {g : Fin n ↪ Fin 1} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 1 (g.trans Fin.castSuccEmb) 1 o r)
    (honly : OwnerOnlyAtIndex t' o) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α 2}
    (htbleg : tb.IsLegal) (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {Lo Tops : Finset (Fin tb.card)} (hLo' : ∀ x, tb.label x ≠ ⊤ → x ∈ Lo)
    (hTops : ∀ x ∈ Tops, tb.label x = ⊤ ∧ tb.toCellScheme.grade x ≤ 1 ∧
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb)
    (hTops' : ∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≤ 1 →
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDet tb x → x ∈ Tops) :
    ∃ F : CompletionBelowFullGrade (Seed.ofCoatoms hleg htbleg hp htbp),
      RecProp F o r 1 Lo Tops :=
  exists_completion_recProp_one_of_owner hleg hs honly hp htbleg htbp hLo'
    (fun x hx ↦ ⟨(hTops x hx).1, (hTops x hx).2.1⟩) hTops' (A := rootTops hp 1)
    (fun _ ha ↦ ha) (root_one hp htbp hLo')

/-- **h2 at two points with the lost point last, when the owner is alone at its graded index at
the top grade `1`** (no `sorry`). -/
theorem exists_coface_two_last {K n : ℕ} {t' : StageType.{u} α 2} {g : Fin n ↪ Fin 1}
    {p : StageType.{u} α 1} (hα : Order.IsSuccLimit α) (hleg : t'.IsLegal) {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) 1 o r)
    (honly : K = 1 → OwnerOnlyAtIndex t' o) (hp : restrictFace Fin.castSuccEmb t' = some p)
    {tb : StageType.{u} α 2} (htbleg : tb.IsLegal)
    (htbp : restrictFace Fin.castSuccEmb tb = some p) {d : StageType.{u} α (n + 1)}
    (hd : restrictFace (extendByLast g) tb = some d) (hdK : d.topGrade ≤ K) :
    ∃ D' ∈ t'.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
      ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
        IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d := by
  refine exists_coface_two hα hleg hs hp
    (fun _ _ htbleg htbp _ _ hLo hT ↦ donorRaising_two_one hp htbleg htbp hLo hT)
    (fun hK _ htbleg htbp _ _ _ hLo' hT hT' ↦ ?_) htbleg htbp hd hdK
  subst hK
  exact exists_completion_recProp_one_of_only hleg hs (honly rfl) hp htbleg htbp hLo' hT hT'

/-- Owner lowering below the full grade on one point is vacuous (there is no grade `K ≤ 0`). -/
theorem ownerLoweringBelowAt_zero : OwnerLoweringBelowAt.{u} 0 := by
  intro α K n t' _ g o r hs hK
  have := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  omega

/-- **Coatom cutoff determination with the lost point last, for the contexts whose owner is alone
at its graded index when `k = 1` and `K = 1`.** -/
def CoatomCutoffDeterminationLastOnly : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α (k + 1)) (g : Fin n ↪ Fin k)
    (p : StageType.{u} α k), Order.IsSuccLimit α → t'.IsLegal →
    (∃ o r, t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) (Fin.last k) o r ∧
      (k = 1 → K = 1 → OwnerOnlyAtIndex t' o)) →
    restrictFace Fin.castSuccEmb t' = some p → ∀ tb ∈ p.cofaces, ∀ d : StageType.{u} α (n + 1),
      restrictFace (extendByLast g) tb = some d → d.topGrade ≤ K →
        ∃ D' ∈ t'.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
          ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
            IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d

/-- **h2 with the lost point last** (for the contexts whose owner is alone at its graded index at
two points and top grade `1`) **from owner lowering below the designated tops below the full grade
and the extension above `K`, at `k ≥ 2`**.  At `k = 0` the engine is
`H2.admittedCompletionsAt_zero`; at `k = 1` the case is `H2.exists_coface_two_last`. -/
theorem coatomCutoffDeterminationLastOnly_of (hOL : ∀ k, 2 ≤ k → OwnerLoweringBelowAt.{u} k)
    (hext : ∀ k, 2 ≤ k → ExtAboveAt.{u} k) : CoatomCutoffDeterminationLastOnly.{u} := by
  intro α K n k t' g p hα hleg ⟨o, r, hs, honly⟩ hp tb ⟨htbleg, htbp⟩ d hd hdK
  rcases k with _ | _ | k
  · exact exists_coface_last (hasRecCompletions_of_below ownerLoweringBelowAt_zero
      admittedCompletionsAt_zero) hα hleg hs hp htbleg htbp hd hdK
  · exact exists_coface_two_last hα hleg hs (honly rfl) hp htbleg htbp hd hdK
  · exact exists_coface_last (hasRecCompletions_of_below (hOL _ (by omega))
      (admittedCompletionsAt_of_below (by omega)
        (admittedCompletionsBelowAt_of_ext (by omega) (hext _ (by omega)))))
      hα hleg hs hp htbleg htbp hd hdK

end VaughtConjecture.H2
