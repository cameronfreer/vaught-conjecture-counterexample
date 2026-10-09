/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStepLow
import VaughtConjecture.MainTheorem.LowDisplayReadingRoute

/-!
# LOW displays on the faces `⊥` above the grade, for every donor

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3) and Layer 6 ("Status:
the hypotheses of the main theorem"); semantic contract, items 4, 5 and 8.

With the tie case for every LOW family (`StageType.IsLowFamily.lowStepTie`), the LOW layer over a
good level is a good level for every donor (`ProfileTower.Lvl.Good.lowNext'`).  The class
`StageType.LowBotClass` asked for a donor top of grade `K` only to make the LOW layer a good
level; the class `StageType.LowBotAllClass` drops it: the LOW families with `K ≤ k` and the
context and the donor labelled `⊥` at every grade in `(K, k]`.

**(R2) on the class of the faces `⊥` above `K`, for every donor**
(`StageType.hasLowLayersOn_lowBotAll`, `StageType.hasLowDisplaysOn_lowBotAll`,
`StageType.hasLowDisplaysOn_lowBotAll_or_root`, compiled in this repository): the completed
display over the LOW layer with the actual labels (`ProfileTower.lowReading_of_bot`,
`ProfileTower.LowReading.exists_isLowLayer`); with the donors whose tops avoid the new point, on
the union.

**Status.**  `StageType.HasLowDisplays` is proved (`StageType.hasLowDisplays_of_padded`, in
`VaughtConjecture.MainTheorem.LowPaddedRoute`, through the padded tower).  The LOW families left
outside the union of this file are those with `K = k + 1` and those with a label other than `⊥` at a
grade in `(K, k]`, `K < k` (for which the completed display carries no separator labelled `⊤`,
`StageType.not_lowReadingFamily`).  The donors without a top of grade `K` are no longer a separate
case.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.StageType

open Finset Label

variable (α : Ordinal.{u}) in
/-- **The class of the faces `⊥` above `K`, for every donor**: the LOW families with `K ≤ k` and
every cell of the context and of the donor of grade in `(K, k]` labelled `⊥` (no condition when
`K = k`). -/
def LowBotAllClass (K k : ℕ) (t' tb : StageType.{u} α (k + 1)) (_ : StageType.{u} α k)
    (_ _ : Fin t'.card) : Prop :=
  K ≤ k ∧
    (∀ x : Fin t'.card, K < t'.toCellScheme.grade x → t'.toCellScheme.grade x ≤ k →
      t'.label x = ⊥) ∧
    ∀ x : Fin tb.card, K < tb.toCellScheme.grade x → tb.toCellScheme.grade x ≤ k →
      tb.label x = ⊥

/-- The class of the faces `⊥` above `K` with a donor top of grade `K` is contained in the class
for every donor. -/
theorem LowBotClass.lowBotAllClass {α : Ordinal.{u}} {K k : ℕ} {t' tb : StageType.{u} α (k + 1)}
    {p : StageType.{u} α k} {o r : Fin t'.card} (h : LowBotClass α K k t' tb p o r) :
    LowBotAllClass α K k t' tb p o r :=
  h.2

/-- **LOW layers on the class of the faces `⊥` above `K`, for every donor**: the completed display
over the LOW layer, a good level by `ProfileTower.Lvl.Good.lowNext'`, with the actual labels
(`ProfileTower.lowReading_of_bot`). -/
theorem hasLowLayersOn_lowBotAll : HasLowLayersOn.{u} LowBotAllClass := by
  intro α K k t' tb p o r hα hF ⟨hKk, hl, hr⟩
  have hK0 := hF.grade_pos
  obtain ⟨g, rfl⟩ : ∃ g, K = g + 1 := ⟨K - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = g + 1 + j := ⟨k - (g + 1), by omega⟩
  exact ProfileTower.LowReading.exists_isLowLayer
    (ProfileTower.lowReading_of_bot
      (I := Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private hF.face_donor)
      hα.isSuccPrelimit hF.isSourceGapContextAt hF.topGrade_donor
      (ProfileTower.lvlZero_good g (by omega))
      ((ProfileTower.lvlZero_good g (by omega)).lowNext' (by omega) hF.isSourceGapContextAt
        hF.topGrade_donor)
      (ProfileTower.amalgam_label_eq_bot hl hr))

/-- **LOW displays on the class of the faces `⊥` above `K`, for every donor**: (R2) for these LOW
families. -/
theorem hasLowDisplaysOn_lowBotAll : HasLowDisplaysOn.{u} LowBotAllClass :=
  hasLowLayersOn_lowBotAll.hasLowDisplaysOn

/-- **LOW displays on the class of the faces `⊥` above `K` or of the donors without new tops**:
`StageType.hasLowDisplaysOn_lowBotAll`, and the exact pinned extension when every donor top avoids
the new point (`StageType.exists_isLowDisplay_of_forall_top_root`). -/
theorem hasLowDisplaysOn_lowBotAll_or_root :
    HasLowDisplaysOn.{u} fun α K k t' tb p o r ↦ LowBotAllClass α K k t' tb p o r ∨
      ∀ x, tb.label x = ⊤ → Fin.last k ∉ tb.toCellScheme.scope x := by
  intro α K k t' tb p o r hα hF hS
  rcases hS with hS | hS
  · exact hasLowDisplaysOn_lowBotAll t' tb p o r hα hF hS
  · exact exists_isLowDisplay_of_forall_top_root hα hF.isLegal_private hF.face_private
      ⟨hF.isLegal_donor, hF.face_donor⟩ hS

end VaughtConjecture.StageType
