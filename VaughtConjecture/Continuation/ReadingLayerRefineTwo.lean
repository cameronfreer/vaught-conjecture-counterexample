/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerShapeInstance

/-!
# Refining servers at the grades `1` and `2`

Roadmap, Layer 3 ((R3) of the table of 3.4).

* **The statements** (`TowerProfile.RefiningServerOne`, `TowerProfile.RefiningServerTwo`, defined
  here): "a refining server exists at the grade `j`" for `j = 1, 2` at a seed on five points, the
  target on the layer below the grade `j` (`I.tower (j - 1)`), the fill lawful below `(univ, j)`,
  equal to the target, agreeing with `e` capped at `h`, and at least `V` where `e` is at least `h`.
  `TowerProfile.refiningServerOne` (compiled): the grade `1`, at every seed.
* **The grade `2`: the lexicographic construction is refuted at a state** (not the statement;
  `Scheme.min_eq_of_catalogueEntry_eq`, `Scheme.eq_of_agree_gridPoint`,
  `Scheme.not_agree_of_ne_frozen`, `Scheme.not_separates_of_agree_gridPoint`, compiled): the grid
  points of the field grid at the grade `k` are `ω * b + k`, so the codes `ω * β + j` (`j < k`) of
  the critical block lie below every grid point of the block.  An entry receiving the agreement
  transfer from an available entry `a₀` at such a grid point codes alike the cells `a₀` codes
  alike there (they are frozen), and its cell reads them alike: it separates no target there.  The
  first raise of the two-level route (lifting those codes to the finite part `k`) breaks the
  agreement, so its cell receives no transfer above the block.  A different server would need its
  bound `h ≤ e u` from elsewhere: from the availability of `e` itself at a cell whose entry
  already separates the frozen cells, or from a transfer through a cell coded below the block
  where the witness of `e` is already at least `h`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label
open scoped Ordinal

/-! ### A cell of full scope reads alike the cells its entry codes alike -/

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {k : ℕ}
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- **A new cell reads alike two old cells of one grade that its entry codes alike**: every
labelling lawful below `(univ, k)` in the field layer is, capped at the new cell, equal at them. -/
theorem min_eq_of_catalogueEntry_eq {w : Fin (S.fieldLayer k hS).card → Label.{u}}
    (hw : (S.fieldLayer k hS).rows.IsLawfulBelow (univ, k) fun d ↦ w d)
    (i : Fin (S.catalogue k).card) {d₁ d₂ : Fin S.card} (hg₁ : S.toCellScheme.grade d₁ ≤ k)
    (hg : S.toCellScheme.grade d₁ = S.toCellScheme.grade d₂)
    (he : S.catalogueEntry k i d₁ = S.catalogueEntry k i d₂) :
    min (w (Fin.castAdd _ d₁)) (w (Fin.natAdd _ i)) =
      min (w (Fin.castAdd _ d₂)) (w (Fin.natAdd _ i)) := by
  obtain ⟨-, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hw
  have hub : Fin.natAdd S.card i ∈ (S.fieldLayer k hS).toCellScheme.below (univ, k) :=
    natAdd_mem_below i
  have hu' : (S.fieldLayer k hS).toCellScheme.gradedIndex (Fin.natAdd S.card i) = (univ, k) :=
    appendFullCellsScheme_gradedIndex_natAdd _ _ _ _
  have hmem (d : Fin S.card) (hd : S.toCellScheme.grade d ≤ k) :
      Fin.castAdd (S.catalogue k).card d ∈ (S.fieldLayer k hS).toCellScheme.below
        ((S.fieldLayer k hS).toCellScheme.gradedIndex (Fin.natAdd S.card i)) := by
    rw [hu']; exact castAdd_mem_below hd
  have hg₂ : S.toCellScheme.grade d₂ ≤ k := hg ▸ hg₁
  have hrow (d : Fin S.card) (hd : S.toCellScheme.grade d ≤ k) :
      (S.fieldLayer k hS).rows.row (Fin.natAdd S.card i) ⟨_, hmem d hd⟩ =
        S.catalogueEntry k i d := by
    rw [fieldLayer_row_natAdd, fieldRow_castAdd]
  have hgr (d : Fin S.card) : (S.fieldLayer k hS).toCellScheme.grade (Fin.castAdd _ d) =
      S.toCellScheme.grade d := appendFullCellsScheme_grade_castAdd _ _ _ _
  have h1 := (hloc _ hub).le_of_le (d := ⟨_, hmem d₁ hg₁⟩) (d' := ⟨_, hmem d₂ hg₂⟩)
    (by rw [hrow d₁ hg₁, hrow d₂ hg₂, he]) (by
      change (S.fieldLayer k hS).toCellScheme.grade (Fin.castAdd _ d₂) ≤
        (S.fieldLayer k hS).toCellScheme.grade (Fin.castAdd _ d₁)
      rw [hgr, hgr, hg])
  have h2 := (hloc _ hub).le_of_le (d := ⟨_, hmem d₂ hg₂⟩) (d' := ⟨_, hmem d₁ hg₁⟩)
    (by rw [hrow d₁ hg₁, hrow d₂ hg₂, he]) (by
      change (S.fieldLayer k hS).toCellScheme.grade (Fin.castAdd _ d₁) ≤
        (S.fieldLayer k hS).toCellScheme.grade (Fin.castAdd _ d₂)
      rw [hgr, hgr, hg])
  exact le_antisymm h1 h2

/-- **Entries agreeing capped at a height code alike the cells coded alike below it**: the cells
frozen by an agreement transfer. -/
theorem eq_of_agree_of_lt {a a₀ : Fin S.card → Label.{u}} {c : Label.{u}}
    (hag : ∀ d, min (a d) c = min (a₀ d) c) {d₁ d₂ : Fin S.card}
    (h₁ : a₀ d₁ < c) (h₂ : a₀ d₂ < c) (he : a₀ d₁ = a₀ d₂) : a d₁ = a d₂ :=
  (Label.eq_of_min_eq_of_lt (hag d₁).symm h₁).trans
    (he.trans (Label.eq_of_min_eq_of_lt (hag d₂).symm h₂).symm)

/-- **The agreement transfer at the grade `2` freezes the codes of the grade `1` of a block**: the
grid points of the field grid at the grade `k` are `ω * b + k`, so two cells coded `ω * β + j` with
`j < k` by an entry `a₀` lie strictly below the grid point `ω * β + k` of their block, and every
entry agreeing with `a₀` capped at a grid point of a block at least `β` codes them alike. -/
theorem eq_of_agree_gridPoint {a a₀ : Fin S.card → Label.{u}} {b β : ℕ} (hβb : β ≤ b) {j : ℕ}
    (hj : j < k) (hag : ∀ d, min (a d) (gridPoint k b) = min (a₀ d) (gridPoint k b))
    {d₁ d₂ : Fin S.card}
    (h₁ : a₀ d₁ = ((ω * (β : Ordinal.{u}) + (j : Ordinal.{u}) : Ordinal.{u}) : Label.{u}))
    (h₂ : a₀ d₂ = ((ω * (β : Ordinal.{u}) + (j : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) :
    a d₁ = a d₂ := by
  have hlt : ((ω * (β : Ordinal.{u}) + (j : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) <
      gridPoint k b := by
    unfold gridPoint
    refine WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ?_)
    calc ω * (β : Ordinal.{u}) + (j : Ordinal.{u}) < ω * (β : Ordinal.{u}) + (k : Ordinal.{u}) :=
          (add_lt_add_iff_left _).mpr (by exact_mod_cast hj)
      _ ≤ ω * (b : Ordinal.{u}) + (k : Ordinal.{u}) := by
          gcongr
  exact eq_of_agree_of_lt hag (h₁ ▸ hlt) (h₂ ▸ hlt) (h₁.trans h₂.symm)

/-- **A lift of a frozen code breaks the agreement**: an entry changing the code `ω * β + j`
(`j < k`) of a cell does not agree with `a₀` capped at any grid point of a block at least `β`; so
the first raise of the two-level route (lifting the codes of the grade `1` of the critical block to
the finite part `k`) leaves its cell without an agreement transfer above the block. -/
theorem not_agree_of_ne_frozen {a a₀ : Fin S.card → Label.{u}} {b β j : ℕ} (hβb : β ≤ b)
    (hj : j < k) {d : Fin S.card}
    (h₀ : a₀ d = ((ω * (β : Ordinal.{u}) + (j : Ordinal.{u}) : Ordinal.{u}) : Label.{u}))
    (hne : a d ≠ a₀ d) :
    ¬ ∀ d, min (a d) (gridPoint k b) = min (a₀ d) (gridPoint k b) := fun hag ↦
  hne (eq_of_agree_gridPoint (a₀ := a₀) hβb hj hag (d₁ := d) (d₂ := d) h₀ h₀ |>.trans
    (Label.eq_of_min_eq_of_lt (hag d).symm (by
      rw [h₀]
      unfold gridPoint
      refine WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ?_)
      calc ω * (β : Ordinal.{u}) + (j : Ordinal.{u}) <
            ω * (β : Ordinal.{u}) + (k : Ordinal.{u}) :=
            (add_lt_add_iff_left _).mpr (by exact_mod_cast hj)
        _ ≤ ω * (b : Ordinal.{u}) + (k : Ordinal.{u}) := by gcongr)))

/-- **The lexicographic construction at the grade `k ≥ 2` does not separate the frozen cells**
(a refutation of that construction at a state, not of the statement): let `a₀` be an entry coding
two old cells of one grade at most `k` alike at `ω * β + j` with `j < k`, and let the cell of an
entry `a` serve by an agreement transfer from `a₀` at a grid point `ω * b + k` with `β ≤ b` (that
is, `a` agrees with `a₀` capped there).  Then every labelling lawful below `(univ, k)` in the
field layer is equal at the two cells, capped at the cell of `a`: that cell does not refine a
target separating them below its own value. -/
theorem not_separates_of_agree_gridPoint {w : Fin (S.fieldLayer k hS).card → Label.{u}}
    (hw : (S.fieldLayer k hS).rows.IsLawfulBelow (univ, k) fun d ↦ w d)
    (i : Fin (S.catalogue k).card) {a₀ : Fin S.card → Label.{u}} {b β j : ℕ} (hβb : β ≤ b)
    (hj : j < k)
    (hag : ∀ d, min (S.catalogueEntry k i d) (gridPoint k b) = min (a₀ d) (gridPoint k b))
    {d₁ d₂ : Fin S.card} (hg₁ : S.toCellScheme.grade d₁ ≤ k)
    (hg : S.toCellScheme.grade d₁ = S.toCellScheme.grade d₂)
    (h₁ : a₀ d₁ = ((ω * (β : Ordinal.{u}) + (j : Ordinal.{u}) : Ordinal.{u}) : Label.{u}))
    (h₂ : a₀ d₂ = ((ω * (β : Ordinal.{u}) + (j : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) :
    ¬ (w (Fin.castAdd _ d₁) ≠ w (Fin.castAdd _ d₂) ∧ w (Fin.castAdd _ d₁) ≤ w (Fin.natAdd _ i) ∧
      w (Fin.castAdd _ d₂) ≤ w (Fin.natAdd _ i)) := by
  rintro ⟨hne, h1, h2⟩
  have := min_eq_of_catalogueEntry_eq hw i hg₁ hg (eq_of_agree_gridPoint hβb hj hag h₁ h₂)
  rw [min_eq_left h1, min_eq_left h2] at this
  exact hne this

end Scheme

/-! ### The statements "a refining server exists at the grade `j`" -/

namespace TowerProfile

variable {α : Ordinal.{u}}

/-- **"A refining server exists at the grade `1`"** at a seed on five points: for every labelling
`e` lawful below `(univ, 1)` in the profile layer, positive cap `h` self-visible at `4`, value
`V ≥ h` self-visible at `1`, and target `q` on the amalgam lawful below `(univ, 1)`, agreeing with
`e` capped at `h` and at least `V` where at least `h`, with a cell of grade `1` where `e` is at
least `h`, some labelling of the profile layer lawful below `(univ, 1)` is `q` on the amalgam,
agrees with `e` capped at `h`, and is at least `V` where `e` is at least `h`. -/
def RefiningServerOne (I : Seed.{u} α 3) : Prop :=
  ∀ e : Fin (scheme I).card → Label.{u}, (scheme I).rows.IsLawfulBelow (univ, 1) (fun d ↦ e d) →
    ∀ h : Label.{u}, IsSelfVisible 4 h → ⊥ < h → ∀ V : Label.{u}, IsSelfVisible 1 V → h ≤ V →
    ∀ q : Fin I.amalgam.card → Label.{u},
      (I.tower 0).rows.IsLawfulBelow (univ, 1) (fun d ↦ q d.1) →
      (∀ d, I.amalgam.toCellScheme.grade d ≤ 1 → min (q d) h = min (e (embed3 I d)) h) →
      (∀ d, I.amalgam.toCellScheme.grade d ≤ 1 → h ≤ q d → V ≤ q d) →
      (∃ z₀, I.amalgam.toCellScheme.grade z₀ = 1 ∧ h ≤ e (embed3 I z₀)) →
      ∃ w : Fin (scheme I).card → Label.{u},
        (scheme I).rows.IsLawfulBelow (univ, 1) (fun d ↦ w d) ∧
        (∀ d, I.amalgam.toCellScheme.grade d ≤ 1 → w (embed3 I d) = q d) ∧
        (∀ x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 1),
          min (w x) h = min (e x) h) ∧
        ∀ x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 1), h ≤ e x → V ≤ w x

/-- **A refining server exists at the grade `1`** at every seed on five points
(`TowerProfile.exists_one_of_target`, the lexicographic raise). -/
theorem refiningServerOne (I : Seed.{u} α 3) : RefiningServerOne I :=
  fun _ he _ hh hhb _ hV hhV _ hq hqe hqV ⟨_, hz₀, hez₀⟩ ↦
    exists_one_of_target he hh hhb hV hhV hq hqe hqV hz₀ hez₀

/-- **"A refining server exists at the grade `2`"** at a seed on five points: the statement of
`TowerProfile.RefiningServerOne` one grade up, the target on the layer at the grade `1`
(`I.tower 1`, the amalgam and the cells of graded index `(univ, 1)`), in the profile layer through
`TowerProfile.oneCell`.  Not proved here: the lexicographic construction does not apply
(`Scheme.not_separates_of_agree_gridPoint`).  It holds under separating servers
(`TowerProfile.refiningServerTwo_of_separating`) and fails at `seedL`
(`TowerProfile.not_refiningServerTwo_seedL`).  With the target capped by `V` at the cells of
grade `2` at least `h` it holds at every seed (`TowerProfile.RefiningServerTwo'`,
`TowerProfile.refiningServerTwo'`). -/
def RefiningServerTwo (I : Seed.{u} α 3) : Prop :=
  ∀ e : Fin (scheme I).card → Label.{u}, (scheme I).rows.IsLawfulBelow (univ, 2) (fun d ↦ e d) →
    ∀ h : Label.{u}, IsSelfVisible 4 h → ⊥ < h → ∀ V : Label.{u}, IsSelfVisible 2 V → h ≤ V →
    ∀ q : Fin (I.tower 1).card → Label.{u},
      (I.tower 1).rows.IsLawfulBelow (univ, 2) (fun d ↦ q d.1) →
      (∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 → min (q d) h = min (e (oneCell I d)) h) →
      (∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 → h ≤ q d → V ≤ q d) →
      (∃ z₀, (I.tower 1).toCellScheme.grade z₀ = 2 ∧ h ≤ e (oneCell I z₀)) →
      ∃ w : Fin (scheme I).card → Label.{u},
        (scheme I).rows.IsLawfulBelow (univ, 2) (fun d ↦ w d) ∧
        (∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 → w (oneCell I d) = q d) ∧
        (∀ x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 2),
          min (w x) h = min (e x) h) ∧
        ∀ x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 2), h ≤ e x → V ≤ w x

end TowerProfile

end VaughtConjecture
