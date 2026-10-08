/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapBottomRow
import VaughtConjecture.Extension.CapTransport

/-!
# The cleaned row of a cap, and the bottom class at the context with root cells labelled `⊥`

Roadmap, Layer 3 ((R3) of the table of 3.4).

The parallel development closes the ties at `⊥` with a bottom class and a cleaned template (the
row of the cap with `⊥` at the cells labelled `⊥`).  The engine's obstruction to a bottom class
(`CompletionBelowFullGrade.not_exists_coatom_eq_bot` and `CapRequests.not_botLiftProvisionOf_class`
on the engine's branch) asks of a completion that the row of every cell of `(univ, k)` read a
class cell `z` or the cap `c` as `⊥`, and fails when some labelling lawful below the private coatom
is other than `⊥` at both.

* **Cutting below a stage** (`Label.cutBelow`, `Label.isWitness_cutBelow`, compiled in this
  repository (theorem named)): sending the labels below a stage `μ`, zero or a limit, to `⊥` is a
  witness bounded by every grade.
* **The cleaned row** (`StageType.cleanRow`, defined here; `StageType.cleanRow_of_label_eq_bot`,
  `StageType.cleanRow_lt_omega0_sq`, `StageType.isLawfulBelow_cleanRow`, compiled): coded; lawful
  below the cell of a legal type when a stage `μ` (zero or a limit) separates the row (a cell
  below is labelled `⊥` exactly when its row value lies below `μ`); the general case is not
  settled here.
* **The obstruction is a property of the context** (`BottomRootCounterexample.exists_row_ne_bot`,
  compiled): every legal one-point extension of the context with root cells labelled `⊥` has a cell
  of `(univ, 3)` whose row reads a root cell labelled `⊥` and the cap both other than `⊥`, since a
  lawful extension of the separating labelling is `⊤` there and `1` at the root cell.  So no carrier
  of that context has its rows at the reading grade in the bottom class, whatever template is
  used: cleaning the template does not remove the engine's obstruction there.  The obstruction is
  absent exactly when no lawful labelling of the context `⊤` at the cap is other than `⊥` at a cell
  labelled `⊥`, which holds when the cap's row respects the bottoms
  (`StageType.RootBottomRespected`, at the root) and fails at this context
  (`BottomRootCounterexample.not_rootBottomRespected`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Cutting below a stage -/

namespace Label

open Classical in
/-- The map sending the labels below a stage `μ` to `⊥` and keeping the others. -/
noncomputable def cutBelow (μ : Ordinal.{u}) (x : Label.{u}) : Label.{u} :=
  if x < μ then ⊥ else x

variable {μ : Ordinal.{u}}

/-- **Cutting below a stage that is zero or a limit is a witness bounded by every grade.** -/
theorem isWitness_cutBelow (hμ : Order.IsSuccPrelimit μ) (K : ℕ) :
    IsWitness (stepSuppressor.{u} K) (cutBelow μ) := by
  have hw : IsWitness (fun _ ↦ (⊤ : Label.{u})) (cutBelow μ) := {
    antitone := antitone_const
    isSelfVisible := fun _ ↦ isSelfVisible_top _
    map_bot := by simp [cutBelow, show (⊥ : Label.{u}) < (μ : Label.{u}) from WithBot.bot_lt_coe _]
    monotone := fun a b hab ↦ by
      unfold cutBelow
      split_ifs with ha hb hb
      · exact le_rfl
      · exact bot_le
      · exact absurd (hab.trans_lt hb) ha
      · exact hab
    visibilityReplace_comm := fun x k _ i _ ↦ by
      unfold cutBelow
      by_cases hx : x < μ
      · rw [ite_eq_left ((visibilityReplace_lt_iff hμ).mpr hx), ite_eq_left hx,
          visibilityReplace_bot]
      · rw [ite_eq_right (fun h ↦ hx ((visibilityReplace_lt_iff hμ).mp h)), ite_eq_right hx] }
  exact hw.truncate K

end Label

/-! ### The cleaned row -/

namespace StageType

variable {α : Ordinal.{u}} {k : ℕ}

/-- The **cleaned row** of a cell `c`: the row of `c` with `⊥` at every cell labelled `⊥`. -/
noncomputable def cleanRow (t' : StageType.{u} α k) (c : Fin t'.card) (d : Fin t'.card) :
    Label.{u} :=
  if t'.label d = ⊥ then ⊥ else t'.rowAt c d

theorem cleanRow_of_label_eq_bot {t' : StageType.{u} α k} {c d : Fin t'.card}
    (hd : t'.label d = ⊥) : t'.cleanRow c d = ⊥ := by simp [cleanRow, hd]

/-- **The cleaned row is coded** when the rows are. -/
theorem cleanRow_lt_omega0_sq (t' : StageType.{u} α k) (c d : Fin t'.card) :
    t'.cleanRow c d < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  unfold cleanRow
  split_ifs
  · exact WithBot.bot_lt_coe _
  · unfold Scheme.rowAt
    split_ifs with hd
    · exact t'.isCoded c ⟨d, hd⟩
    · exact WithBot.bot_lt_coe _

/-- **The cleaned row is lawful below the cell** of a legal type when a stage `μ`, zero or a
limit, separates the row: below the cell, a cell is labelled `⊥` exactly when its row value lies
below `μ`.  It is the image of the row under cutting below `μ`, with the labels as lawful
companion (`CellScheme.Rows.IsLawfulBelow.map_of_bot_iff`). -/
theorem isLawfulBelow_cleanRow {t' : StageType.{u} α k} (ht' : t'.IsLegal) {c : Fin t'.card}
    {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ)
    (hsep : ∀ d ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex c),
      t'.label d = ⊥ ↔ t'.rowAt c d < μ) :
    t'.rows.IsLawfulBelow (t'.toCellScheme.gradedIndex c) fun d ↦ t'.cleanRow c d := by
  have hK (d : t'.toCellScheme.below (t'.toCellScheme.gradedIndex c)) :
      t'.toCellScheme.grade d ≤ t'.toCellScheme.grade c := by
    have := d.2
    rw [CellScheme.mem_below] at this
    exact this.2
  have h := (ht'.isConsistent c).map_of_bot_iff (t'.isLawful.isLawfulBelow _) hK
    (isWitness_cutBelow hμ _) fun d ↦ by
      rw [hsep d d.2, ← Scheme.rowAt_of_mem d.2]
      unfold cutBelow
      split_ifs with h
      · exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩
      · exact ⟨fun h' ↦ absurd (h'.symm ▸ (show (⊥ : Label.{u}) < (μ : Label.{u}) from
          WithBot.bot_lt_coe _)) h, fun h' ↦ absurd h' h⟩
  convert h using 1
  funext d
  change t'.cleanRow c d = cutBelow μ (t'.rows.row c d)
  rw [← Scheme.rowAt_of_mem d.2]
  unfold cleanRow cutBelow
  by_cases hl : t'.label d = ⊥
  · rw [ite_eq_left hl, ite_eq_left ((hsep d d.2).mp hl)]
  · rw [ite_eq_right hl, ite_eq_right (fun h ↦ hl ((hsep d d.2).mpr h))]

end StageType

/-! ### The bottom class is impossible at the context with root cells labelled `⊥` -/

namespace BottomRootCounterexample

open StageType
open TiedRootCapCounterexample (rootRow rootEmb)

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- **No carrier of the context with root cells labelled `⊥` has its rows at `(univ, 3)` in the
bottom class.**  For every legal one-point extension `D` of the context, some cell of graded index
`(univ, 3)` reads the first root cell (labelled `⊥`) and the cap both other than `⊥`: a lawful
extension of the separating labelling is `⊤` at a cell of `(univ, 3)` (availability from the cap)
and `1` at the root cell, so the row of that cell reads neither as `⊥` (locality).  This is the
hypothesis of the engine's obstruction to a bottom class on the rows
(`CompletionBelowFullGrade.not_exists_coatom_eq_bot` on the engine's branch): the obstruction is
a property of the context, through its lawful labellings, and not of a template. -/
theorem exists_row_ne_bot {D : StageType.{u} α 4} (hD : D.IsLegal)
    (h₁ : restrictFace Fin.castSuccEmb D = some (context hα)) :
    ∃ u, D.toCellScheme.gradedIndex u = ((univ : Finset (Fin 4)), 3) ∧
      D.rowAt u (faceCell h₁ (faceCell (restrictFace_context hα) (⟨0, by decide⟩ : Fin 2))) ≠ ⊥ ∧
      D.rowAt u (faceCell h₁ (capCell hα)) ≠ ⊥ := by
  obtain ⟨a, ha, hext⟩ := exists_isLawful_extend_of_restrictFace hD h₁ (isLawful_separating hα)
  obtain ⟨u₀, hu₀⟩ := hD.isComplete ((univ : Finset (Fin 4)), 3)
    ⟨D.univ_mem_faces, by omega, by simp⟩
  have hcg : D.toCellScheme.grade (faceCell h₁ (capCell hα)) = 3 :=
    (grade_faceCell h₁ _).trans (context_grade_cap hα)
  obtain ⟨u, hu, hcu⟩ := ha.availability (faceCell h₁ (capCell hα)) u₀
    (by rw [show D.toCellScheme.scope u₀ = univ from congrArg Prod.fst hu₀]; exact subset_univ _)
    (hcg.trans (congrArg Prod.snd hu₀).symm)
  have hu' := hu.trans hu₀
  have hau : a u = ⊤ := top_le_iff.mp (by rw [hext, separating_capCell] at hcu; exact hcu)
  obtain ⟨σ, hσ, hread⟩ := exists_isBoundedReading ha hau
  have hbelow (y : Fin D.card) (hy : D.toCellScheme.grade y ≤ 3) :
      y ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) := by
    rw [CellScheme.mem_below, hu']
    exact Prod.mk_le_mk.mpr ⟨subset_univ _, hy⟩
  refine ⟨u, hu', fun hz ↦ ?_, fun hc ↦ ?_⟩
  · have hzg : D.toCellScheme.grade
        (faceCell h₁ (faceCell (restrictFace_context hα) (⟨0, by decide⟩ : Fin 2))) ≤ 3 := by
      rw [grade_faceCell]
      exact (context hα).grade_le _
    have h := hread _ (hbelow _ hzg)
    rw [hz, hσ.map_bot, hext, separating_root] at h
    exact natCast_label_ne_bot _ h
  · have h := hread (faceCell h₁ (capCell hα)) (hbelow _ hcg.le)
    rw [hc, hσ.map_bot, hext, separating_capCell] at h
    exact top_ne_bot h

end BottomRootCounterexample

end VaughtConjecture
