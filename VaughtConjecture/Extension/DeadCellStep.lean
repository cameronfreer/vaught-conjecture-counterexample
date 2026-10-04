/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.TwoFaceLift

/-!
# The step from the grade `j` to `j + 1` when the old cells of the grade `j + 1` are dead

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.6 (the recursion on the grade; here a step that does not
use the two-face lift); semantic contract, items 2–4.

Let `I` be a seed on `m + 2` points, with coatoms `C = univ.erase x` and `D = univ.erase y` and
tower `T j` (module `VaughtConjecture.Extension.Tower`).  The old cells of the grade `j + 1` are
*dead* (`Seed.DeadAt j`) when every labelling of the amalgam lawful below a coatom at the grade
`j + 1` is `⊥` at the cells of the grade `j + 1` below that coatom.

**The step from deadness** (`Seed.towerInvariant_succ_of_dead`).  For `j + 1 ≤ m`, the invariant
at the grade `j` and deadness of the cells of the grade `j + 1` give the invariant at `j + 1`, with
no two-face lift.  The one-grade lift from `(C, j + 1)` to `(univ, j + 1)` uses the two boundary
triples of the step to the top grade (`Seed.towerInvariant_top`):

* at the cap `⊥`: `U = (C, j + 1)`, `V = (D, j + 1)` and `O` the common face, with the extension
  at `⊥` through the whole tower (`Seed.extendsFromBoundary_bot_tower`);
* at the positive caps: `U = (C, j + 1)`, `V = (univ, j)` and `O = (C, j)`, with the invariant as
  the lift from `O` to `V`.  The boundary labelling is completed below `(univ, j + 1)` by `⊥` at
  the cells of the grade `j + 1` of `D` (`Seed.exists_isLawfulBelow_dead`): this splice of the
  boundary labelling with `⊥` above the grade `j` is lawful below `(D, j + 1)`
  (`CellScheme.Rows.IsLawfulBelow.splice`), it agrees with the boundary at the cells of the
  common face of the grade `j + 1`, which are `⊥` there by deadness on `C`, and it agrees with the
  ambient capped at the cap, the ambient being `⊥` there by deadness on `D`.  It is then extended
  through the new cells of the grade `j + 1` (`Seed.extendsFromBoundary_tower_dead`).

This is the boundary triple through `(univ, j)`, whose fill of the other coatom over the common
face is a union fill; the union fill fails for some seeds
(module `VaughtConjecture.Extension.UnionFillCounterexample`), and deadness is one hypothesis on the
seed under which it holds.

**The invariant and the completion from a choice at each grade**
(`Seed.towerInvariant_of_twoFaceLift_or_deadAt`,
`Seed.nonempty_completionBelowFullGrade_of_twoFaceLift_or_deadAt`).  If at each grade
`2 ≤ j < m` either `2FL(j)` holds or the old cells of the grade `j + 1` are dead, the invariant
holds up to the grade `m + 1` and the seed has a completion below the full grade.  The choice is
made per seed and per grade; it does not cover every seed (see the open point in the module
`VaughtConjecture.Extension.TwoFaceLift`).  A legal seed on five points where `2FL(2)` fails and
the cells of the grade `3` are dead is in the module
`VaughtConjecture.Extension.TwoFaceLiftCounterexample`.

## Placement

Checkpoint 2.6 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.Seed

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- **The old cells of the grade `j + 1` are dead**: for both coatoms, every labelling of the
amalgam lawful below the coatom at the grade `j + 1` is `⊥` at every cell of the grade `j + 1`
below it. -/
def DeadAt (j : ℕ) : Prop :=
  ∀ x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))),
    ∀ p : Fin I.amalgam.card → Label.{u},
      I.amalgam.rows.IsLawfulBelow (univ.erase x, j + 1) (fun d ↦ p d) →
      ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j + 1),
        I.amalgam.toCellScheme.grade d = j + 1 → p d = ⊥

/-- **The boundary labelling completed when the old cells of the grade `j + 1` are dead.**  Let
`C = univ.erase x` and `D = univ.erase y` be the two coatoms, `w` a labelling of the scheme reached
after the grade `j` lawful below `(C, j + 1)` and `(univ, j)`, and `a` a lawful labelling agreeing
with `w` capped at `h` on the cells below `(C, j + 1)` or `(univ, j)`.  Then `w` on those cells
and `⊥` at the other cells is lawful below `(univ, j + 1)` and agrees with `a` capped at `h` at
every cell below `(univ, j + 1)`: below `(D, j + 1)` it is the splice of `w` with `⊥` above the
grade `j` (the cells of the grade `j + 1` on the common face are `⊥` in `w` by deadness on `C`),
and the three pieces are glued (`CellScheme.Rows.IsLawfulBelow.glue₃`); at the cells of the grade
`j + 1` of `D`, `a` is `⊥` by deadness on `D`. -/
theorem exists_isLawfulBelow_dead {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) {j : ℕ} (hdead : I.DeadAt j)
    {w : Fin (I.tower j).card → Label.{u}}
    (hwU : (I.tower j).rows.IsLawfulBelow (univ.erase x, j + 1) fun d ↦ w d)
    (hwV : (I.tower j).rows.IsLawfulBelow (univ, j) fun d ↦ w d)
    {a : Fin (I.tower j).card → Label.{u}} (ha : (I.tower j).rows.IsLawful a) {h : Label.{u}}
    (hag : ∀ e, e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
      e ∈ (I.tower j).toCellScheme.below (univ, j) → min (w e) h = min (a e) h) :
    ∃ g : Fin (I.tower j).card → Label.{u},
      (I.tower j).rows.IsLawfulBelow (univ, j + 1) (fun d ↦ g d) ∧
      (∀ e, e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
        e ∈ (I.tower j).toCellScheme.below (univ, j) → g e = w e) ∧
      ∀ e ∈ (I.tower j).toCellScheme.below (univ, j + 1), min (g e) h = min (a e) h := by
  classical
  -- An old cell of the grade `j + 1` below a coatom is `⊥` in a labelling lawful below it.
  have hdead' (z : Fin (m + 2))
      (hz : z ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
      (p : Fin (I.tower j).card → Label.{u})
      (hp : (I.tower j).rows.IsLawfulBelow (univ.erase z, j + 1) fun d ↦ p d)
      (e : Fin (I.tower j).card) (he : e ∈ (I.tower j).toCellScheme.below (univ.erase z, j + 1))
      (hge : ¬ (I.tower j).toCellScheme.grade e ≤ j) : p e = ⊥ := by
    obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed j e fun hsc ↦
      ne_univ_erase z (univ_subset_iff.mp (hsc.ge.trans he.1))
    have hd := I.towerEmbed_mem_below_iff.mp he
    rw [grade_towerEmbed] at hge
    exact hdead z hz (fun d ↦ p (I.towerEmbed j d))
      ((I.isLawfulBelow_tower_iff (g := p) (ne_univ_erase z)).mp hp) d hd
      (le_antisymm hd.2 (by omega))
  set g : Fin (I.tower j).card → Label.{u} := fun e ↦
    if e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
      e ∈ (I.tower j).toCellScheme.below (univ, j) then w e else ⊥ with hg_def
  have hgb (e : Fin (I.tower j).card)
      (he : e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
        e ∈ (I.tower j).toCellScheme.below (univ, j)) : g e = w e := by
    rw [hg_def]; exact ite_eq_left he
  -- Below the other coatom, `g` is the splice of `w` at the grade `j` with `⊥`.
  have hgD (e : Fin (I.tower j).card)
      (he : e ∈ (I.tower j).toCellScheme.below (univ.erase y, j + 1)) :
      g e = (I.tower j).toCellScheme.splice j (fun _ ↦ ⊥) w e := by
    by_cases hej : (I.tower j).toCellScheme.grade e ≤ j
    · rw [CellScheme.splice_of_le hej, hgb e (.inr ⟨subset_univ _, hej⟩)]
    · rw [CellScheme.splice_of_lt (not_le.mp hej)]
      by_cases hb : e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
          e ∈ (I.tower j).toCellScheme.below (univ, j)
      · rw [hgb e hb]
        rcases hb with hb | hb
        · exact hdead' x hx w hwU e hb hej
        · exact absurd hb.2 hej
      · rw [hg_def]; exact ite_eq_right hb
  have hspl : (I.tower j).rows.IsLawfulBelow (univ.erase y, j + 1)
      fun e ↦ (I.tower j).toCellScheme.splice j (fun _ ↦ ⊥) w e :=
    Rows.IsLawfulBelow.splice (M := ⊥) (Rows.isLawfulBelow_const_bot _)
      (hwV.mono (X := (univ.erase y, j)) ⟨subset_univ _, le_rfl⟩) (fun _ _ _ ↦ le_rfl)
      fun _ _ ↦ by simp
  refine ⟨g, Rows.IsLawfulBelow.glue₃ (U := (univ.erase x, j + 1)) (V := (univ, j))
    (W := (univ.erase y, j + 1)) ?_ ?_ ?_ (I.mem_below_cover_tower hx hy hxy), hgb,
    fun e he ↦ ?_⟩
  · convert hwU using 1
    exact funext fun e ↦ hgb e (.inl e.2)
  · convert hwV using 1
    exact funext fun e ↦ hgb e (.inr e.2)
  · convert hspl using 1
    exact funext fun e ↦ hgD e e.2
  · rcases I.mem_below_cover_tower hx hy hxy e he with hb | hb | hb
    · rw [hgb e (.inl hb)]
      exact hag e (.inl hb)
    · rw [hgb e (.inr hb)]
      exact hag e (.inr hb)
    · rw [hgD e hb]
      by_cases hej : (I.tower j).toCellScheme.grade e ≤ j
      · rw [CellScheme.splice_of_le hej]
        exact hag e (.inr ⟨subset_univ _, hej⟩)
      · rw [CellScheme.splice_of_lt (not_le.mp hej),
          hdead' y hy a (ha.isLawfulBelow _) e hb hej]

/-- **Extension from the boundary of `(C, j + 1)` and `(univ, j)` when the old cells of the grade
`j + 1` are dead**, at every cap `h` self-visible and short at `j + 1` with `⊥ < h`, along the row
of every new cell of the grade `j + 1`: the boundary labelling completed on the scheme before
(`Seed.exists_isLawfulBelow_dead`), then extended through the new cells
(`Seed.extendsFromBoundary_tower_of_forall`). -/
theorem extendsFromBoundary_tower_dead {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) {j : ℕ} (hdead : I.DeadAt j) {u : Fin (I.tower (j + 1)).card}
    (hu : (I.tower (j + 1)).toCellScheme.gradedIndex u = (univ, j + 1)) {h : Label.{u}}
    (hh : IsSelfVisible (j + 1) h) (hs : IsShort (j + 1) h) (hbot : ⊥ < h) :
    (I.tower (j + 1)).rows.ExtendsFromBoundary (univ.erase x, j + 1) (univ, j) (univ, j + 1) h
      ((I.tower (j + 1)).rows.rowBelow u hu) :=
  I.extendsFromBoundary_tower_of_forall (fun h ↦ ne_univ_erase x (univ_subset_iff.mp h.1))
    (fun h ↦ absurd h.2 (by simp only; omega)) le_rfl (Nat.le_succ j) hh hs hbot
    (fun _ ha _ hwU hwV hag ↦ I.exists_isLawfulBelow_dead hx hy hxy hdead hwU hwV
      (Scheme.mem_catalogue.mp ha).1 hag) hu

/-- **The step from the grade `j` to `j + 1` when the old cells of the grade `j + 1` are dead**,
for `j ≤ m`, with no two-face lift.  The lift from a coatom `C = univ.erase x` to `(univ, j + 1)`
is `CellScheme.Rows.cappedLift_of_boundaries_short` with the two boundary triples of
`Seed.towerInvariant_top`: at `⊥`, `(C, j + 1)`, `(D, j + 1)` and the common face, with
`Seed.extendsFromBoundary_bot_tower`; at the positive caps, `(C, j + 1)`, `(univ, j)` and `(C, j)`,
with the invariant from `(C, j)` to `(univ, j)` and `Seed.extendsFromBoundary_tower_dead`. -/
theorem towerInvariant_succ_of_dead {j : ℕ} (hjm : j ≤ m) (hinv : I.TowerInvariant j)
    (hdead : I.DeadAt j) : I.TowerInvariant (j + 1) := by
  intro x hx j' hj'
  rcases Nat.lt_or_eq_of_le hj' with hlt | rfl
  · exact I.cappedLift_tower_succ (Nat.lt_succ_iff.mp hlt)
      (hinv x hx j' (Nat.lt_succ_iff.mp hlt))
  obtain ⟨y, hy, hxy⟩ := exists_other hx
  have hlift := I.cappedLift_tower_succ le_rfl (hinv x hx j le_rfl)
  -- `I.tower (j + 1)` is the field layer of `I.tower j` (`Seed.tower_succ`, by `rfl`); the generic
  -- one-grade lift is stated for the field layer.
  change ((I.tower j).fieldLayer (j + 1) (I.not_univ_succ_le_tower j)).rows.CappedLift
    (X := (univ.erase x, j + 1)) (Y := (univ, j + 1)) ⟨erase_subset _ _, le_rfl⟩
  refine Rows.cappedLift_of_boundaries_short (C := univ.erase x) (B := univ) (j := j)
    (U₀ := (univ.erase x, j + 1)) (V₀ := (univ.erase y, j + 1))
    (O₀ := (univ.erase x ∩ univ.erase y, min (j + 1) m))
    (U := (univ.erase x, j + 1)) (V := (univ, j)) (O := (univ.erase x, j))
    (erase_subset _ _) ?_ hlift le_rfl ⟨inter_subset_left, min_le_left _ _⟩
    ⟨inter_subset_right, min_le_left _ _⟩ ⟨erase_subset _ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩
    (fun d hdU hdV ↦ I.mem_below_commonFace_tower hx hy hxy (k := j + 1) (by omega) d hdU hdV)
    (Rows.cappedLift_refl _) (I.cappedLift_commonFace_tower hx hy hxy (by omega))
    (I.extendsFromBoundary_bot_tower (I.scope_subset_or hx hy hxy) (j + 1))
    le_rfl ⟨subset_rfl, Nat.le_succ j⟩ ⟨subset_univ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩
    ⟨subset_rfl, Nat.le_succ j⟩ (fun d hdU hdV ↦ ⟨hdU.1, hdV.2⟩) (Rows.cappedLift_refl _) hlift
    (I.exists_gradedIndex_eq_univ_tower j) fun u hu ↦
      ⟨I.isConsistent_tower (j + 1) u, fun d ↦ (I.isShort_ne_top_rowBelow_tower hu d).1,
        fun d ↦ (I.isShort_ne_top_rowBelow_tower hu d).2, fun h hh hs hbot ↦
        I.extendsFromBoundary_tower_dead hx hy hxy hdead hu hh hs hbot⟩
  exact I.exists_gradedIndex_eq_tower (j + 1)
    ⟨I.erase_mem_faces hx, Nat.succ_pos j, by rw [card_erase]; omega⟩ (ne_univ_erase x)

/-- **The invariant up to the grade `m + 1` when at each grade `2 ≤ j < m` either `2FL(j)` holds
or the old cells of the grade `j + 1` are dead.**  The grades `0` and `1` are the base; the step to
the grade `2` uses `2FL(1)` (`Seed.twoFaceLift_one`); the steps to the grades `j + 1` with
`2 ≤ j < m` use `Seed.towerInvariant_succ` or `Seed.towerInvariant_succ_of_dead`, as the hypothesis
provides; the step to the top grade is `Seed.towerInvariant_top`. -/
theorem towerInvariant_of_twoFaceLift_or_deadAt
    (h2 : ∀ j, 2 ≤ j → j < m → I.TwoFaceLift j ∨ I.DeadAt j) :
    ∀ j ≤ m + 1, I.TowerInvariant j
  | 0, _ => I.towerInvariant_zero
  | 1, _ => I.towerInvariant_one
  | j + 2, hj =>
    if hjm : j + 1 < m then
      if hj0 : j = 0 then by
        subst hj0
        exact I.towerInvariant_succ hjm.le I.towerInvariant_one I.twoFaceLift_one
      else
        (h2 (j + 1) (by omega) hjm).elim
          (I.towerInvariant_succ hjm.le
            (towerInvariant_of_twoFaceLift_or_deadAt h2 (j + 1) (by omega)))
          (I.towerInvariant_succ_of_dead hjm.le
            (towerInvariant_of_twoFaceLift_or_deadAt h2 (j + 1) (by omega)))
    else by
      have hinv := towerInvariant_of_twoFaceLift_or_deadAt h2 (j + 1) (by omega)
      rw [show j + 1 = m by omega] at hinv
      rw [show j + 2 = m + 1 by omega]
      exact I.towerInvariant_top hinv

/-- **The completion below the full grade when at each grade `2 ≤ j < m` either `2FL(j)` holds or
the old cells of the grade `j + 1` are dead**: the scheme `T (m + 1)` of the tower
(`Seed.completionBelowFullGradeOfTowerInvariant`), with the invariant at the top grade from
`Seed.towerInvariant_of_twoFaceLift_or_deadAt`. -/
theorem nonempty_completionBelowFullGrade_of_twoFaceLift_or_deadAt
    (h2 : ∀ j, 2 ≤ j → j < m → I.TwoFaceLift j ∨ I.DeadAt j) :
    Nonempty (CompletionBelowFullGrade I) :=
  ⟨I.completionBelowFullGradeOfTowerInvariant
    (I.towerInvariant_of_twoFaceLift_or_deadAt h2 (m + 1) le_rfl)⟩

end VaughtConjecture.Seed
