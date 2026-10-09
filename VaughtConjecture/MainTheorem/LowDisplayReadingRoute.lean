/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowDisplayActual
import VaughtConjecture.MainTheorem.LowDisplayRoute

/-!
# LOW layers from the reading of the completed display, on a class of LOW families

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3) and Layer 6 ("Status:
the hypotheses of the main theorem"); semantic contract, items 4, 5 and 8.

**LOW layers and LOW displays on a class of LOW families** (`StageType.HasLowLayersOn`,
`StageType.HasLowDisplaysOn`).  The statements of `StageType.HasLowLayers` and
`StageType.HasLowDisplays` for the LOW families satisfying a predicate `S`.  The compiled chain of
`VaughtConjecture.MainTheorem.LowDisplayRoute` is pointwise in the family, so LOW layers on `S`
give LOW displays on `S` (`StageType.HasLowLayersOn.hasLowDisplaysOn`, compiled in this
repository); on the class of all LOW families this is `StageType.HasLowDisplays`
(`StageType.HasLowDisplaysOn.hasLowDisplays`).

**The reading of a LOW family** (`StageType.LowReadingFamily`; decided at limit stages by
`StageType.lowReadingFamily_iff`).  For a LOW family
`(t', tb)` at `K = g + 1 ≤ k` with a donor top `z` of grade `K`: the reading
(`ProfileTower.LowReading`) of the completed display over the levels from the grade `0` at `g`
(`ProfileTower.lvlZero`) and the LOW layer at `K`, which is a good level
(`ProfileTower.Lvl.Good.lowNext`, from the capped lift `ProfileTower.Lvl.Good.cappedLift_lowS_seed`
with no open hypothesis).  The reading asks only for the labels: a lawful labelling at the stage
extending the glued labels with a separator of the LOW catalogue labelled by a proper label and
`⊤`.

**LOW layers on the class of the reading** (`StageType.hasLowLayersOn_lowReading`, compiled in
this repository).  On the class `StageType.LowReadingClass` of the LOW families with a donor top
of grade `K`, `K ≤ k`, and the reading, LOW layers exist: the completed display is legal, its
faces are the context and the donor literally, and it carries the LOW layer of
`ProfileTower.isLowLayer_lowDisplay`.  Hence LOW displays on that class
(`StageType.hasLowDisplaysOn_lowReading`).

**The reading holds exactly when the faces are `⊥` above `K`** (`StageType.lowReadingFamily_iff`,
compiled in this repository).  At a stage that is zero or a limit, for a LOW family with a donor top
of grade `K` and `K ≤ k`: the reading implies that every cell of the context and of the donor
of grade in `(K, k]` is labelled `⊥` (`StageType.LowReadingFamily.label_eq_bot`, from
`ProfileTower.LowReading.face_label_eq_bot`: the canonical levels above the controllers read every
controller of positive cutoff as `⊥`), and conversely (`StageType.lowReadingFamily_of_bot`, from
`ProfileTower.lowReading_of_bot`: the actual labels, the decoded row of the controller of the
actual profile, with its partner as the separator).  On a LOW family with `K < k` and a cell of
grade in `(K, k]` not labelled `⊥` the reading fails (`StageType.not_lowReadingFamily`).

**(R2) on the class of the faces `⊥` above `K`** (`StageType.hasLowLayersOn_lowBot`,
`StageType.hasLowDisplaysOn_lowBot`, compiled in this repository).  On the class
`StageType.LowBotClass` (a donor top of grade `K`, `K ≤ k`, and the context and the donor
labelled `⊥` at every grade in `(K, k]`; no condition on labels when `K = k`), LOW layers and LOW
displays exist; with the donors whose tops avoid the new point
(`StageType.exists_isLowDisplay_of_forall_top_root`), LOW displays exist on the union
(`StageType.hasLowDisplaysOn_lowBot_or_root`).

**Status.**  `StageType.HasLowDisplays` is proved (`StageType.hasLowDisplays_of_padded`, in
`VaughtConjecture.MainTheorem.LowPaddedRoute`, through the padded tower).  Outside the union of this
file the LOW families left are those with a donor top through the new point but none of grade `K`
(`StageType.LowStepTieLow`), those with `K = k + 1` (the grade of a LOW family is positive,
`StageType.IsLowFamily.grade_pos`), and those with a label other than `⊥` above `K < k`, for which
the completed display carries no separator labelled `⊤` (`StageType.not_lowReadingFamily`).  The
acquisition of (R2) can produce such families; for them a level above the LOW layer reading the
actual state suffices (`ProfileTower.ReadsActualOn.exists_isLowLayer_all`).

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.StageType

open Finset Label

/-! ### LOW layers and LOW displays on a class of LOW families -/

section Class

variable (S : ∀ (α : Ordinal.{u}) (_ k : ℕ) (t' _ : StageType.{u} α (k + 1)),
  StageType.{u} α k → Fin t'.card → Fin t'.card → Prop)

/-- **LOW layers on a class `S` of LOW families**: the statement of `StageType.HasLowLayers` for
the LOW families in `S`. -/
def HasLowLayersOn : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K k : ℕ⦄ (t' tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (o r : Fin t'.card), Order.IsSuccLimit α → IsLowFamily K t' tb p o r → S α K k t' tb p o r →
      ∃ (D : StageType.{u} α (k + 2)) (h₁ : restrictFace Fin.castSuccEmb D = some t')
        (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some tb) (G : Finset Label.{u})
        (entry : Fin D.card → LowField D → Label.{u}) (s : LowField D → Label.{u})
        (lo hi : Fin D.card), D.IsLegal ∧ D.label lo ≠ ⊤ ∧ D.label hi = ⊤ ∧
          IsLowLayer K h₁ h₂ o r G entry s lo hi

/-- **LOW displays on a class `S` of LOW families**: the statement of `StageType.HasLowDisplays`
for the LOW families in `S`. -/
def HasLowDisplaysOn : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K k : ℕ⦄ (t' tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (o r : Fin t'.card), Order.IsSuccLimit α → IsLowFamily K t' tb p o r → S α K k t' tb p o r →
      ∃ (D : StageType.{u} α (k + 2)) (a : Label.{u}), AtStage α a ∧ IsLowDisplay t' tb D a

variable {S}

/-- **LOW layers on a class give LOW displays on it**: the controller reading of the LOW layer
(`StageType.IsLowLayer.isControllerReading`), the separated display
(`StageType.IsSeparatedLowDisplay.of_controllerReading`), and a threshold at the stage
(`StageType.exists_isLowDisplay_of_separated`). -/
theorem HasLowLayersOn.hasLowDisplaysOn (h : HasLowLayersOn S) : HasLowDisplaysOn S := by
  intro α K k t' tb p o r hα hF hS
  obtain ⟨D, h₁, h₂, G, entry, s, lo, hi, hD, hlo, hhi, hL⟩ := h t' tb p o r hα hF hS
  have hs := hF.isSourceGapContextAt
  have hr : t'.toCellScheme.grade r ≤ K := hs.topGrade_eq ▸ grade_le_topGrade hs.label_lost
  obtain ⟨a, ha, hDa⟩ := exists_isLowDisplay_of_separated hα
    (IsSeparatedLowDisplay.of_controllerReading hs hF.topGrade_donor hD h₁ h₂ hlo hhi
      (congrArg Prod.snd hL.gradedIndex_lo).le (congrArg Prod.snd hL.gradedIndex_hi).le
      (hL.isControllerReading hs.grade_owner.le hr hF.topGrade_donor))
  exact ⟨D, a, ha, hDa⟩

/-- On the class of all LOW families, LOW displays on the class are `StageType.HasLowDisplays`. -/
theorem HasLowDisplaysOn.hasLowDisplays (h : HasLowDisplaysOn.{u} fun _ _ _ _ _ _ _ _ ↦ True) :
    HasLowDisplays.{u} :=
  fun _ _ _ t' tb p o r hα hF ↦ h t' tb p o r hα hF trivial

end Class

/-! ### The reading of a LOW family -/

variable {α : Ordinal.{u}} {k : ℕ}

/-- **The grade of a LOW family is positive**: it is the grade of the owner, and grades of cells
are positive. -/
theorem IsLowFamily.grade_pos {K : ℕ} {t' tb : StageType.{u} α (k + 1)} {p : StageType.{u} α k}
    {o r : Fin t'.card} (hF : IsLowFamily K t' tb p o r) : 0 < K :=
  hF.isSourceGapContextAt.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o

/-- **The reading of a LOW family** (open): for every decomposition `K = g + 1`, `k = g + 1 + j`
and every donor top `z` of grade `K`, the reading (`ProfileTower.LowReading`) of the completed
display over the levels from the grade `0` at `g` and the LOW layer at `K` of the seed of the
family; the LOW layer is a good level by `ProfileTower.Lvl.Good.lowNext`. -/
def LowReadingFamily (K : ℕ) (t' tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (o r : Fin t'.card) : Prop :=
  ∀ (hF : IsLowFamily K t' tb p o r) (g j : ℕ) (hK : K = g + 1) (hk : k = g + 1 + j)
    (z : Fin tb.card) (hz : tb.label z = ⊤) (hzK : tb.toCellScheme.grade z = K), by
    subst hK hk
    exact ProfileTower.LowReading
      (I := Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private hF.face_donor) o r
      (ProfileTower.lvlZero _ g) (ProfileTower.lvlZero_good g (by omega))
      ((ProfileTower.lvlZero_good g (by omega)).lowNext (by omega) hF.isSourceGapContextAt
        hF.topGrade_donor hz hzK)

/-- **The class of the reading**: the LOW families with a donor top of grade `K`, `K ≤ k`, and
the reading (`StageType.LowReadingFamily`). -/
def LowReadingClass (α : Ordinal.{u}) (K k : ℕ) (t' tb : StageType.{u} α (k + 1))
    (p : StageType.{u} α k) (o r : Fin t'.card) : Prop :=
  (∃ z, tb.label z = ⊤ ∧ tb.toCellScheme.grade z = K) ∧ K ≤ k ∧
    LowReadingFamily K t' tb p o r

/-- **LOW layers on the class of the reading** (`ProfileTower.LowReading.exists_isLowLayer`). -/
theorem hasLowLayersOn_lowReading : HasLowLayersOn.{u} LowReadingClass := by
  intro α K k t' tb p o r _ hF ⟨⟨z, hz, hzK⟩, hKk, hread⟩
  have hK0 := hF.grade_pos
  obtain ⟨g, rfl⟩ : ∃ g, K = g + 1 := ⟨K - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = g + 1 + j := ⟨k - (g + 1), by omega⟩
  exact ProfileTower.LowReading.exists_isLowLayer (hread hF g j rfl rfl z hz hzK)

/-- **LOW displays on the class of the reading.** -/
theorem hasLowDisplaysOn_lowReading : HasLowDisplaysOn.{u} LowReadingClass :=
  hasLowLayersOn_lowReading.hasLowDisplaysOn

/-! ### The reading forces `⊥` above `K` -/

variable {K : ℕ} {t' tb : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {o r : Fin t'.card}

/-- **The reading forces `⊥` above `K`**: on a LOW family with a donor top of grade `K` and
`K ≤ k`, the reading implies that every cell of the context and of the donor of grade in
`(K, k]` is labelled `⊥` (`ProfileTower.LowReading.face_label_eq_bot`). -/
theorem LowReadingFamily.label_eq_bot (hF : IsLowFamily K t' tb p o r)
    (hread : LowReadingFamily K t' tb p o r) {z : Fin tb.card} (hz : tb.label z = ⊤)
    (hzK : tb.toCellScheme.grade z = K) (hKk : K ≤ k) :
    (∀ x : Fin t'.card, K < t'.toCellScheme.grade x → t'.toCellScheme.grade x ≤ k →
      t'.label x = ⊥) ∧
    ∀ x : Fin tb.card, K < tb.toCellScheme.grade x → tb.toCellScheme.grade x ≤ k →
      tb.label x = ⊥ := by
  have hK0 := hF.grade_pos
  obtain ⟨g, rfl⟩ : ∃ g, K = g + 1 := ⟨K - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = g + 1 + j := ⟨k - (g + 1), by omega⟩
  exact ProfileTower.LowReading.face_label_eq_bot (hread hF g j rfl rfl z hz hzK)

/-- **The reading fails above `K`**: on a LOW family with a donor top of grade `K`, `K ≤ k`,
and a cell of the context or of the donor of grade in `(K, k]` not labelled `⊥`, the reading of
the completed display fails. -/
theorem not_lowReadingFamily (hF : IsLowFamily K t' tb p o r) {z : Fin tb.card}
    (hz : tb.label z = ⊤) (hzK : tb.toCellScheme.grade z = K) (hKk : K ≤ k)
    (hne : (∃ x : Fin t'.card, K < t'.toCellScheme.grade x ∧ t'.toCellScheme.grade x ≤ k ∧
      t'.label x ≠ ⊥) ∨
      ∃ x : Fin tb.card, K < tb.toCellScheme.grade x ∧ tb.toCellScheme.grade x ≤ k ∧
        tb.label x ≠ ⊥) :
    ¬ LowReadingFamily K t' tb p o r := fun hread ↦ by
  obtain ⟨h₁, h₂⟩ := hread.label_eq_bot hF hz hzK hKk
  rcases hne with ⟨x, hxK, hxk, hx⟩ | ⟨x, hxK, hxk, hx⟩
  · exact hx (h₁ x hxK hxk)
  · exact hx (h₂ x hxK hxk)

/-! ### The reading holds exactly when the faces are `⊥` above `K` -/

variable (α) in
/-- **The class of the faces `⊥` above `K`**: the LOW families with a donor top of grade `K`,
`K ≤ k`, and every cell of the context and of the donor of grade in `(K, k]` labelled `⊥`
(no condition when `K = k`). -/
def LowBotClass (K k : ℕ) (t' tb : StageType.{u} α (k + 1)) (_ : StageType.{u} α k)
    (_ _ : Fin t'.card) : Prop :=
  (∃ z, tb.label z = ⊤ ∧ tb.toCellScheme.grade z = K) ∧ K ≤ k ∧
    (∀ x : Fin t'.card, K < t'.toCellScheme.grade x → t'.toCellScheme.grade x ≤ k →
      t'.label x = ⊥) ∧
    ∀ x : Fin tb.card, K < tb.toCellScheme.grade x → tb.toCellScheme.grade x ≤ k →
      tb.label x = ⊥

/-- **The faces `⊥` above `K` give the reading**, at a stage that is zero or a limit
(`ProfileTower.lowReading_of_bot`). -/
theorem lowReadingFamily_of_bot (hα : Order.IsSuccPrelimit α)
    (hl : ∀ x : Fin t'.card, K < t'.toCellScheme.grade x → t'.toCellScheme.grade x ≤ k →
      t'.label x = ⊥)
    (hr : ∀ x : Fin tb.card, K < tb.toCellScheme.grade x → tb.toCellScheme.grade x ≤ k →
      tb.label x = ⊥) : LowReadingFamily K t' tb p o r := by
  intro hF g j hK hk z hz hzK
  subst hK hk
  exact ProfileTower.lowReading_of_bot hα hF.isSourceGapContextAt hF.topGrade_donor _ _
    (ProfileTower.amalgam_label_eq_bot (I := Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor
      hF.face_private hF.face_donor) hl hr)

/-- **The reading holds exactly when the faces are `⊥` above `K`**: at a stage that is zero or a
limit, for a LOW family with a donor top of grade `K` and `K ≤ k`
(`StageType.LowReadingFamily.label_eq_bot`, `StageType.lowReadingFamily_of_bot`). -/
theorem lowReadingFamily_iff (hα : Order.IsSuccPrelimit α) (hF : IsLowFamily K t' tb p o r)
    {z : Fin tb.card} (hz : tb.label z = ⊤) (hzK : tb.toCellScheme.grade z = K) (hKk : K ≤ k) :
    LowReadingFamily K t' tb p o r ↔
      (∀ x : Fin t'.card, K < t'.toCellScheme.grade x → t'.toCellScheme.grade x ≤ k →
        t'.label x = ⊥) ∧
      ∀ x : Fin tb.card, K < tb.toCellScheme.grade x → tb.toCellScheme.grade x ≤ k →
        tb.label x = ⊥ :=
  ⟨fun h ↦ h.label_eq_bot hF hz hzK hKk, fun ⟨hl, hr⟩ ↦ lowReadingFamily_of_bot hα hl hr⟩

/-- **LOW layers on the class of the faces `⊥` above `K`**: the completed display over the LOW
layer with the actual labels (`StageType.hasLowLayersOn_lowReading`,
`StageType.lowReadingFamily_of_bot`). -/
theorem hasLowLayersOn_lowBot : HasLowLayersOn.{u} LowBotClass := by
  intro α K k t' tb p o r hα hF ⟨htop, hKk, hl, hr⟩
  exact hasLowLayersOn_lowReading t' tb p o r hα hF
    ⟨htop, hKk, lowReadingFamily_of_bot hα.isSuccPrelimit hl hr⟩

/-- **LOW displays on the class of the faces `⊥` above `K`**: (R2) for these LOW families. -/
theorem hasLowDisplaysOn_lowBot : HasLowDisplaysOn.{u} LowBotClass :=
  hasLowLayersOn_lowBot.hasLowDisplaysOn

/-- **LOW displays on the class of the faces `⊥` above `K` or of the donors without new tops**:
`StageType.hasLowDisplaysOn_lowBot`, and the exact pinned extension when every donor top avoids
the new point (`StageType.exists_isLowDisplay_of_forall_top_root`). -/
theorem hasLowDisplaysOn_lowBot_or_root :
    HasLowDisplaysOn.{u} fun α K k t' tb p o r ↦ LowBotClass α K k t' tb p o r ∨
      ∀ x, tb.label x = ⊤ → Fin.last k ∉ tb.toCellScheme.scope x := by
  intro α K k t' tb p o r hα hF hS
  rcases hS with hS | hS
  · exact hasLowDisplaysOn_lowBot t' tb p o r hα hF hS
  · exact exists_isLowDisplay_of_forall_top_root hα hF.isLegal_private hF.face_private
      ⟨hF.isLegal_donor, hF.face_donor⟩ hS

end VaughtConjecture.StageType
