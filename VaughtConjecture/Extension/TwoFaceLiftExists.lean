/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.DeadCellStep
import VaughtConjecture.Label.StepWitness

/-!
# The existential two-face lift: the hypothesis of the step of the tower, stated exactly

Roadmap, Layer 3, 3.1, (R6), checkpoints 2.6 and 2.7 (the recursion on the grade; here the
hypothesis of the step from the grade `j` to `j + 1`, stated exactly); semantic contract,
items 2–4.

Let `I` be a seed on `m + 2` points, with coatoms `C = univ.erase x` and `D = univ.erase y` (both
orders of the two omitted points), common face `E`, and tower `T j` (module
`VaughtConjecture.Extension.Tower`).

**The existential two-face lift** `2FL∃(j)` (`Seed.TwoFaceLiftExists j`).  For both orders of the
coatoms, every catalogue entry `a` at the grade `j + 1`, every cap `h` self-visible and short at
`j + 1` with `⊥ < h`, and every labelling `w_C` of the amalgam lawful below `(C, j + 1)` that
agrees with `a` capped at `h` there, *some* labelling `w_D` lawful below `(D, j + 1)`, equal to
`w_C` at the cells of `E` of grade at most `j + 1` and agreeing with `a` capped at `h` below
`(D, j + 1)`, is such that the labelling glued from `w_C` and `w_D` satisfies the conclusion of the
two-face lift `2FL(j)` (`Seed.TwoFaceLift`): it extends, unchanged at the old cells of grade at most
`j`, to a labelling lawful below `(univ, j)` that agrees with `a` capped at `h`.  In `2FL(j)` the
labelling on `D` is given; here it is chosen.

**It is the hypothesis of the step, stated exactly**, a reformulation of the missing step through
the tower, not a weaker sufficient hypothesis and not a proof of the step:

* *for `j ≤ m` and under the invariant at the grade `j`*, the invariant at the grade `j + 1` holds
  exactly when `2FL∃(j)` does (`Seed.towerInvariant_succ_iff_twoFaceLiftExists`);
* the invariant at the top grade `m + 1` holds exactly when `2FL∃(j)` holds at every grade
  `2 ≤ j < m` (`Seed.towerInvariant_top_iff`), with no hypothesis on the stage.

Sufficiency (`Seed.towerInvariant_succ_of_twoFaceLiftExists`, for `j ≤ m`, under the invariant at
`j`): the one-grade lift `CellScheme.Rows.cappedLift_of_boundaries_short` uses at the cap `⊥` the
triple of the two coatoms and the common face, and at the positive caps the degenerate triple
`U = V = O = (C, j + 1)`, whose extension from the boundary is the labelling chosen by `2FL∃(j)`
glued over `(C, j + 1)`, `(univ, j)` and `(D, j + 1)`
(`Seed.exists_isLawfulBelow_of_twoFaceLiftExists`) and extended through the new cells of the grade
`j + 1`.  Necessity (`Seed.twoFaceLiftExists_of_towerInvariant`, from the invariant at `j + 1`):
the lift from `(C, j + 1)` to `(univ, j + 1)` along the row of the new cell whose entry is `a`
chooses `w_D` (its trace on `D`) and the extension (its trace below `(univ, j)`).  The invariant
restricts to lower grades (`Seed.towerInvariant_of_le`).

**Each per-seed hypothesis of the library implies it.**  `2FL(j)` implies `2FL∃(j)` for
`j ≤ m` (`Seed.twoFaceLiftExists_of_twoFaceLift`: `w_D` is the lift of `w_C` from the common face
into `D`).  Deadness of the old cells of the grade `j + 1` (`Seed.DeadAt j`), together with the
invariant at `j`, implies it (`Seed.twoFaceLiftExists_of_deadAt`: `w_D` is the invariant's lift of
`w_C` from `(C, j)`, read on `D`, with `⊥` at the grade `j + 1`).  `2FL∃(j)` does not imply the
disjunction: for a legal seed on five points `2FL∃(2)` holds while `2FL(2)` and deadness both fail
(`CaseSplitCounterexample.twoFaceLiftExists_and_not_twoFaceLift_or_deadAt`, module
`VaughtConjecture.Extension.CaseSplitCounterexample`), so the case split
`2FL(j) ∨ Seed.DeadAt j` does not cover every legal seed, while the completion of that seed exists.

**A sufficient condition on the amalgam: the raised union fill** (`Seed.RaisedUnionFill j`;
`Seed.twoFaceLiftExists_of_raisedUnionFill`, under the invariant at `j`).  For a cap `h` with
`⊥ < h`, self-visible at `j + 1`, the labelling `a` *raised to `⊤` above `h`* is `raise h ∘ a`
(`Label.raise`): `⊤` where `a ≥ h` and `a` elsewhere.  Below the pairs of grade at most `j` it is
lawful where `a` is, `raise h` being a witness bounded by the grade `j` (`Label.isWitness_raise`),
and it agrees with `a` capped at `h`.  The condition mentions no tower: for such a cap `h`, also
short at `j + 1`, it asks for a cap `c ≥ h`, self-visible at `j` and at most `w_C` at the cells of
`(C, j)` where `a` reaches `h`, such that every labelling lawful below `(D, j)` that agrees with
the raised `a` capped at `c` and with `w_C` on the common face is filled at the cells of the grade
`j + 1` of `D`, taking `w_C` on the common face and agreeing with `a` capped at `h`.  The
invariant's lift of `w_C` from `(C, j)` to `(univ, j)` along the raised `a`, at the cap `c`, is
then the two-face extension.  Deadness gives the raised union fill
(`Seed.raisedUnionFill_of_deadAt`: the cap `h` and the fill by `⊥`).  It fills the same cells as
the union fill refuted in the module
`VaughtConjecture.Extension.UnionFillCounterexample`, but only for the labellings that agree with
the raised `a` at the cap `c`; that union fill is not used.

**The completion.**  A seed satisfying `2FL∃(j)` at the grades `2 ≤ j < m` has a completion below
the full grade (`Seed.nonempty_completionBelowFullGrade_of_twoFaceLiftExists`, a hypothesis on the
seed).

**Where the step fails, and what is open.**  `2FL∃(j)` remains the exact hypothesis of the step.
It holds at `j` for the seeds satisfying `2FL(j)`, for the seeds whose old cells of the grade
`j + 1` are dead and which satisfy the invariant at `j`, and, at `j = 2`, for the seeds whose two
coatom types are the type `T5` of the module `VaughtConjecture.Extension.CaseSplitCounterexample`.
The step fails for a legal seed: for the seed `seedL` on five points of the module
`VaughtConjecture.Extension.TwoFaceLiftExistsCounterexample`, whose two coatom types differ,
`2FL∃(2)` fails (`TwoFaceLiftExistsCounterexample.not_twoFaceLiftExists_two_seedL`), so the
invariant of its tower fails at the top grade
(`TwoFaceLiftExistsCounterexample.not_towerInvariant_top_seedL`) and `2FL∃(j)` at the grades
`2 ≤ j < m` is false as a statement about every seed, at every stage
(`TwoFaceLiftExistsCounterexample.not_forall_twoFaceLiftExists`).  The tower does not complete
every seed.  Not refuted: a completion below the full grade of `seedL` by another construction,
and `StageType.HasApexCoatomExtensions` and `StageType.HasCoatomExtensions`, which remain to be
proved.  `seedL` has a completion below the full grade by other constructions
(`ThinCompletion.nonempty_completionBelowFullGrade_seedL`, `ProfileTowerExamples.seedL_completion`).
That module gives
a necessary condition, argued and not formalized (a cell at `(univ, 2)` where the labelling reaches
the cap and whose row reads the cell `({3}, 1)` strictly below the cell `({4}, 1)`; for the
catalogue entry `a` and the cap `h` of the failure, no cell of the tower at `(univ, 2)` where `a`
reaches `h` separates these two cells, while separating cells where `a < h` may exist), and a
prospective candidate.

## Placement

Checkpoints 2.6 and 2.7 of the completion of the coatom extension construction
(`roadmap/README.md`, Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.Seed

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-! ### The existential two-face lift and the step -/

open Classical in
/-- **The existential two-face lift `2FL∃(j)`.**  For both orders of the coatoms
`C = univ.erase x` and `D = univ.erase y`, every catalogue entry `a` at the grade `j + 1`, every cap
`h` self-visible and short at `j + 1` with `⊥ < h`, and every labelling `wC` of the amalgam lawful
below `(C, j + 1)` that agrees with `a` capped at `h` there, *some* labelling `wD` lawful below
`(D, j + 1)`, equal to `wC` at the cells of the common face of grade at most `j + 1` and agreeing
with `a` capped at `h` below `(D, j + 1)`, is such that the labelling glued from `wC` (on `C`) and
`wD` (elsewhere) satisfies the conclusion of `2FL(j)`: it extends, unchanged at the old cells of
grade at most `j`, to a labelling lawful below `(univ, j)` that agrees with `a` capped at `h`.

For `j ≤ m` and under the invariant at the grade `j`, this is the hypothesis of the step to the
grade `j + 1`, stated exactly (`Seed.towerInvariant_succ_iff_twoFaceLiftExists`). -/
def TwoFaceLiftExists (j : ℕ) : Prop :=
  ∀ x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))),
  ∀ y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))), x ≠ y →
  ∀ a ∈ (I.tower j).catalogue (j + 1),
  ∀ h : Label.{u}, IsSelfVisible (j + 1) h → IsShort (j + 1) h → ⊥ < h →
  ∀ wC : Fin I.amalgam.card → Label.{u},
    I.amalgam.rows.IsLawfulBelow (univ.erase x, j + 1) (fun d ↦ wC d) →
    (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j + 1),
      min (wC d) h = min (a (I.towerEmbed j d)) h) →
    ∃ wD : Fin I.amalgam.card → Label.{u},
      I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) (fun d ↦ wD d) ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j + 1),
        d ∈ I.amalgam.toCellScheme.below (univ.erase y, j + 1) → wD d = wC d) ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase y, j + 1),
        min (wD d) h = min (a (I.towerEmbed j d)) h) ∧
      ∃ r : (I.tower j).toCellScheme.below (univ, j) → Label.{u},
        (I.tower j).rows.IsLawfulBelow (univ, j) r ∧
        (∀ d (hd : I.amalgam.toCellScheme.grade d ≤ j),
          r ⟨I.towerEmbed j d, I.towerEmbed_mem_below hd⟩ =
            if d ∈ I.amalgam.toCellScheme.below (univ.erase x, j + 1) then wC d else wD d) ∧
        ∀ e, min (r e) h = min (a e) h

/-- **The boundary labelling of one coatom, completed on the scheme reached after the grade `j`,
under `2FL∃(j)`.**  A labelling `w` lawful below `(C, j + 1)` agreeing with a catalogue entry `a`
capped at `h` there is, on those cells, a labelling lawful below `(univ, j + 1)` agreeing with `a`
capped at `h`: the chosen `wD` and the two-face extension `r`, glued over `(C, j + 1)`,
`(univ, j)` and `(D, j + 1)`. -/
theorem exists_isLawfulBelow_of_twoFaceLiftExists {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) {j : ℕ} (hE : I.TwoFaceLiftExists j) {a : Fin (I.tower j).card → Label.{u}}
    (ha : a ∈ (I.tower j).catalogue (j + 1)) {h : Label.{u}} (hh : IsSelfVisible (j + 1) h)
    (hs : IsShort (j + 1) h) (hbot : ⊥ < h) {w : Fin (I.tower j).card → Label.{u}}
    (hw : (I.tower j).rows.IsLawfulBelow (univ.erase x, j + 1) fun e ↦ w e)
    (hag : ∀ e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1),
      min (w e) h = min (a e) h) :
    ∃ g : Fin (I.tower j).card → Label.{u},
      (I.tower j).rows.IsLawfulBelow (univ, j + 1) (fun e ↦ g e) ∧
      (∀ e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1), g e = w e) ∧
      ∀ e ∈ (I.tower j).toCellScheme.below (univ, j + 1), min (g e) h = min (a e) h := by
  classical
  obtain ⟨wD, hwD, hDE, hDa, r, hr, hrw, hra⟩ := hE x hx y hy hxy a ha h hh hs hbot
    (fun d ↦ w (I.towerEmbed j d)) ((I.isLawfulBelow_tower_iff (g := w) (ne_univ_erase x)).mp hw)
    fun d hd ↦ hag _ (I.towerEmbed_mem_below_iff.mpr hd)
  set W : Fin (I.tower j).card → Label.{u} := Function.extend (I.towerEmbed j) wD (fun _ ↦ ⊥)
    with hW
  have hWe (d : Fin I.amalgam.card) : W (I.towerEmbed j d) = wD d :=
    (I.towerEmbed j).injective.extend_apply _ _ _
  set g : Fin (I.tower j).card → Label.{u} := fun e ↦
    if he : e ∈ (I.tower j).toCellScheme.below (univ, j) then r ⟨e, he⟩
    else if e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) then w e else W e with hg
  have hold (e : Fin (I.tower j).card) (hsc : (I.tower j).toCellScheme.scope e ≠ univ) :
      ∃ d, I.towerEmbed j d = e := I.mem_range_towerEmbed j e hsc
  have hgC (e : Fin (I.tower j).card)
      (he : e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1)) : g e = w e := by
    by_cases hej : e ∈ (I.tower j).toCellScheme.below (univ, j)
    · rw [hg]; simp only [dite_eq_left hej]
      obtain ⟨d, rfl⟩ := hold e fun hu ↦ ne_univ_erase x (univ_subset_iff.mp (hu.ge.trans he.1))
      have hd : I.amalgam.toCellScheme.grade d ≤ j := (I.grade_towerEmbed j d).symm.trans_le hej.2
      rw [hrw d hd, ite_eq_left (I.towerEmbed_mem_below_iff.mp he)]
    · rw [hg]; simp only [dite_eq_right hej, ite_eq_left he]
  have hgD (e : Fin (I.tower j).card)
      (he : e ∈ (I.tower j).toCellScheme.below (univ.erase y, j + 1)) : g e = W e := by
    obtain ⟨d, rfl⟩ := hold e fun hu ↦ ne_univ_erase y (univ_subset_iff.mp (hu.ge.trans he.1))
    have hdD := I.towerEmbed_mem_below_iff.mp he
    rw [hWe]
    by_cases hej : I.towerEmbed j d ∈ (I.tower j).toCellScheme.below (univ, j)
    · rw [hg]; simp only [dite_eq_left hej]
      have hd : I.amalgam.toCellScheme.grade d ≤ j := (I.grade_towerEmbed j d).symm.trans_le hej.2
      rw [hrw d hd]
      split_ifs with hdC
      · exact (hDE d hdC hdD).symm
      · rfl
    · rw [hg]; simp only [dite_eq_right hej]
      split_ifs with hdC
      · exact (hDE d (I.towerEmbed_mem_below_iff.mp hdC) hdD).symm
      · exact hWe d
  have hgV (e : Fin (I.tower j).card) (he : e ∈ (I.tower j).toCellScheme.below (univ, j)) :
      g e = r ⟨e, he⟩ := by
    rw [hg]; simp only [dite_eq_left he]
  have hWD : (I.tower j).rows.IsLawfulBelow (univ.erase y, j + 1) fun e ↦ W e := by
    rw [I.isLawfulBelow_tower_iff (ne_univ_erase y)]
    simpa only [hWe] using hwD
  refine ⟨g, Rows.IsLawfulBelow.glue₃ (U := (univ.erase x, j + 1)) (V := (univ, j))
    (W := (univ.erase y, j + 1)) ?_ ?_ ?_ (I.mem_below_cover_tower hx hy hxy), hgC,
    fun e he ↦ ?_⟩
  · convert hw using 1
    exact funext fun e ↦ hgC e e.2
  · convert hr using 1
    exact funext fun e ↦ hgV e e.2
  · convert hWD using 1
    exact funext fun e ↦ hgD e e.2
  · rcases I.mem_below_cover_tower hx hy hxy e he with hb | hb | hb
    · rw [hgC e hb]; exact hag e hb
    · rw [hgV e hb]; exact hra _
    · rw [hgD e hb]
      obtain ⟨d, rfl⟩ := hold e fun hu ↦ ne_univ_erase y (univ_subset_iff.mp (hu.ge.trans hb.1))
      rw [hWe]
      exact hDa d (I.towerEmbed_mem_below_iff.mp hb)

/-- **The step from the grade `j` to `j + 1` under `2FL∃(j)`**, for `j ≤ m` and under the
invariant at the grade `j`.  The one-grade lift
(`CellScheme.Rows.cappedLift_of_boundaries_short`) uses at the cap `⊥` the triple of the two
coatoms and the common face, and at the positive caps the degenerate triple
`U = V = O = (C, j + 1)`: its boundary is `(C, j + 1)` alone, the lifts into `U` and from `O` to
`V` are identities, and the extension from the boundary is the completion of
`Seed.exists_isLawfulBelow_of_twoFaceLiftExists` extended through the new cells. -/
theorem towerInvariant_succ_of_twoFaceLiftExists {j : ℕ} (hjm : j ≤ m)
    (hinv : I.TowerInvariant j) (hE : I.TwoFaceLiftExists j) : I.TowerInvariant (j + 1) := by
  intro x hx j' hj'
  rcases Nat.lt_or_eq_of_le hj' with hlt | rfl
  · exact I.cappedLift_tower_succ (Nat.lt_succ_iff.mp hlt)
      (hinv x hx j' (Nat.lt_succ_iff.mp hlt))
  obtain ⟨y, hy, hxy⟩ := exists_other hx
  have hlift := I.cappedLift_tower_succ le_rfl (hinv x hx j le_rfl)
  have hnot : ¬ ((univ : Finset (Fin (m + 2))), j + 1) ≤ (univ.erase x, j + 1) :=
    fun h ↦ ne_univ_erase x (univ_subset_iff.mp h.1)
  change ((I.tower j).fieldLayer (j + 1) (I.not_univ_succ_le_tower j)).rows.CappedLift
    (X := (univ.erase x, j + 1)) (Y := (univ, j + 1)) ⟨erase_subset _ _, le_rfl⟩
  refine Rows.cappedLift_of_boundaries_short (C := univ.erase x) (B := univ) (j := j)
    (U₀ := (univ.erase x, j + 1)) (V₀ := (univ.erase y, j + 1))
    (O₀ := (univ.erase x ∩ univ.erase y, min (j + 1) m))
    (U := (univ.erase x, j + 1)) (V := (univ.erase x, j + 1)) (O := (univ.erase x, j + 1))
    (erase_subset _ _) ?_ hlift le_rfl ⟨inter_subset_left, min_le_left _ _⟩
    ⟨inter_subset_right, min_le_left _ _⟩ ⟨erase_subset _ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩
    (fun d hdU hdV ↦ I.mem_below_commonFace_tower hx hy hxy (k := j + 1) (by omega) d hdU hdV)
    (Rows.cappedLift_refl _) (I.cappedLift_commonFace_tower hx hy hxy (by omega))
    (I.extendsFromBoundary_bot_tower (I.scope_subset_or hx hy hxy) (j + 1))
    le_rfl le_rfl le_rfl ⟨erase_subset _ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩
    (fun d hdU _ ↦ hdU) (Rows.cappedLift_refl _) (Rows.cappedLift_refl _)
    (I.exists_gradedIndex_eq_univ_tower j) fun u hu ↦
      ⟨I.isConsistent_tower (j + 1) u, fun d ↦ (I.isShort_ne_top_rowBelow_tower hu d).1,
        fun d ↦ (I.isShort_ne_top_rowBelow_tower hu d).2, fun h hh hs hbot ↦
        I.extendsFromBoundary_tower_of_forall hnot hnot le_rfl le_rfl hh hs hbot
          (fun a ha w hwU _ hag ↦ by
            obtain ⟨g, hg, hgw, hga⟩ := I.exists_isLawfulBelow_of_twoFaceLiftExists hx hy hxy hE
              ha hh hs hbot hwU fun e he ↦ hag e (.inl he)
            exact ⟨g, hg, fun e he ↦ hgw e (he.elim id id), hga⟩) hu⟩
  exact I.exists_gradedIndex_eq_tower (j + 1)
    ⟨I.erase_mem_faces hx, Nat.succ_pos j, by rw [card_erase]; omega⟩ (ne_univ_erase x)

/-- **`2FL(j)` implies `2FL∃(j)`**, for `j ≤ m`: choose `wD` as the lift of `wC` from the common
face into the other coatom (a lift of the amalgam), and apply `2FL(j)` to the glued labelling. -/
theorem twoFaceLiftExists_of_twoFaceLift {j : ℕ} (hj : j ≤ m) (h2 : I.TwoFaceLift j) :
    I.TwoFaceLiftExists j := by
  classical
  intro x hx y hy hxy a ha h hh hs hbot wC hwC hag
  have hl : I.amalgam.rows.CappedLift (X := (univ.erase x ∩ univ.erase y, min (j + 1) m))
      (Y := (univ.erase y, j + 1)) ⟨inter_subset_right, min_le_left _ _⟩ :=
    (I.cappedLift_tower_iff _ (ne_univ_erase y)).mp
      (I.cappedLift_commonFace_tower hx hy hxy (j := j + 1) (by omega))
  have hEC : ((univ.erase x ∩ univ.erase y, min (j + 1) m) : Finset (Fin (m + 2)) × ℕ) ≤
      (univ.erase x, j + 1) := ⟨inter_subset_left, min_le_left _ _⟩
  have haL : (I.tower j).rows.IsLawful a := (Scheme.mem_catalogue.mp ha).1
  have haD : I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) fun d ↦ a (I.towerEmbed j d) :=
    (I.isLawfulBelow_tower_iff (g := a) (ne_univ_erase y)).mp (haL.isLawfulBelow _)
  obtain ⟨v, hv, hva, hvw⟩ := (Rows.cappedLift_iff_forall_exists _).mp hl h hh
    (fun d ↦ wC d) (fun d ↦ a (I.towerEmbed j d)) (hwC.mono hEC) haD
    fun d ↦ (hag d (I.amalgam.toCellScheme.below_mono hEC d.2)).symm
  set wD : Fin I.amalgam.card → Label.{u} := Rows.extendBot (univ.erase y, j + 1) v with hwD_def
  have hwDv (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase y, j + 1)) :
      wD d = v ⟨d, hd⟩ := Rows.extendBot_of_mem v hd
  have hwDl : I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) fun d ↦ wD d :=
    Rows.isLawfulBelow_extendBot.mpr hv
  have hDE (d : Fin I.amalgam.card) (hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase x, j + 1))
      (hdD : d ∈ I.amalgam.toCellScheme.below (univ.erase y, j + 1)) : wD d = wC d := by
    have hdE : d ∈ I.amalgam.toCellScheme.below (univ.erase x ∩ univ.erase y, min (j + 1) m) :=
      I.mem_below_commonFace_tower hx hy hxy (k := 0) (by omega) d hdC hdD
    rw [hwDv d hdD]
    exact hvw ⟨d, hdE⟩
  have hDa (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase y, j + 1)) :
      min (wD d) h = min (a (I.towerEmbed j d)) h := by
    rw [hwDv d hd]; exact hva ⟨d, hd⟩
  set w : Fin I.amalgam.card → Label.{u} := fun d ↦
    if d ∈ I.amalgam.toCellScheme.below (univ.erase x, j + 1) then wC d else wD d with hw_def
  have hwx : I.amalgam.rows.IsLawfulBelow (univ.erase x, j + 1) fun d ↦ w d := by
    convert hwC using 1
    funext d
    exact ite_eq_left d.2
  have hwy : I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) fun d ↦ w d := by
    convert hwDl using 1
    funext d
    rw [hw_def]
    dsimp only
    split_ifs with hdC
    · exact (hDE d hdC d.2).symm
    · rfl
  have hwa (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ j + 1) :
      min (w d) h = min (a (I.towerEmbed j d)) h := by
    rw [hw_def]
    dsimp only
    split_ifs with hdC
    · exact hag d hdC
    · rcases I.scope_subset_or hx hy hxy d with hsc | hsc
      · exact absurd ⟨hsc, hd⟩ hdC
      · exact hDa d ⟨hsc, hd⟩
  obtain ⟨r, hr, hrw, hra⟩ : ∃ r : (I.tower j).toCellScheme.below (univ, j) → Label.{u},
      (I.tower j).rows.IsLawfulBelow (univ, j) r ∧
      (∀ d (hd : I.amalgam.toCellScheme.grade d ≤ j),
        r ⟨I.towerEmbed j d, I.towerEmbed_mem_below hd⟩ = w d) ∧
      ∀ e, min (r e) h = min (a e) h := by
    rcases pair_cases hx hy hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h2 a ha h hh hs hbot w hwx hwy hwa
    · exact h2 a ha h hh hs hbot w hwy hwx hwa
  exact ⟨wD, hwDl, hDE, hDa, r, hr, hrw, hra⟩

/-- **Deadness and the invariant at `j` imply `2FL∃(j)`**: choose as `wD` the lift of `wC` from
`(C, j)` to `(univ, j)` given by the invariant, read on the other coatom, with `⊥` at its cells
of the grade `j + 1`; the two-face extension is that lift itself. -/
theorem twoFaceLiftExists_of_deadAt {j : ℕ} (hinv : I.TowerInvariant j) (hdead : I.DeadAt j) :
    I.TwoFaceLiftExists j := by
  classical
  intro x hx y hy hxy a ha h hh hs hbot wC hwC hag
  have haL : (I.tower j).rows.IsLawful a := (Scheme.mem_catalogue.mp ha).1
  have haD : I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) fun d ↦ a (I.towerEmbed j d) :=
    (I.isLawfulBelow_tower_iff (g := a) (ne_univ_erase y)).mp (haL.isLawfulBelow _)
  set P : Fin (I.tower j).card → Label.{u} := Function.extend (I.towerEmbed j) wC (fun _ ↦ ⊥)
  have hPe (d : Fin I.amalgam.card) : P (I.towerEmbed j d) = wC d :=
    (I.towerEmbed j).injective.extend_apply _ _ _
  have hPC : (I.tower j).rows.IsLawfulBelow (univ.erase x, j) fun e ↦ P e := by
    rw [I.isLawfulBelow_tower_iff (ne_univ_erase x)]
    simp only [hPe]
    exact hwC.mono (X := (univ.erase x, j)) ⟨subset_rfl, Nat.le_succ j⟩
  obtain ⟨v, hv, hva, hvP⟩ := (Rows.cappedLift_iff_forall_exists _).mp (hinv x hx j le_rfl) h
    (hh.mono (Nat.le_succ j)) (fun e ↦ P e) (fun e ↦ a e) hPC (haL.isLawfulBelow _) fun e ↦ by
      obtain ⟨d, hd⟩ := I.mem_range_towerEmbed j e.1 fun hu ↦
        ne_univ_erase x (univ_subset_iff.mp (hu.ge.trans e.2.1))
      have hdC := I.towerEmbed_mem_below_iff.mp (hd ▸ e.2)
      change min (a e.1) h = min (P e.1) h
      rw [← hd, hPe]
      exact (hag d ⟨hdC.1, hdC.2.trans (Nat.le_succ j)⟩).symm
  set V : Fin I.amalgam.card → Label.{u} := fun d ↦ Rows.extendBot (univ, j) v (I.towerEmbed j d)
    with hV
  have hVD : I.amalgam.rows.IsLawfulBelow (univ.erase y, j) fun d ↦ V d :=
    (I.isLawfulBelow_tower_iff (g := Rows.extendBot (univ, j) v) (ne_univ_erase y)).mp
      ((Rows.isLawfulBelow_extendBot.mpr hv).mono (X := (univ.erase y, j)) ⟨subset_univ _, le_rfl⟩)
  set wD : Fin I.amalgam.card → Label.{u} := I.amalgam.toCellScheme.splice j (fun _ ↦ ⊥) V
    with hwD_def
  have hwDl : I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) fun d ↦ wD d :=
    Rows.IsLawfulBelow.splice (M := ⊥) (Rows.isLawfulBelow_const_bot _) hVD
      (fun _ _ _ ↦ le_rfl) fun _ _ ↦ by simp
  have hwDle (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ j) :
      wD d = v ⟨I.towerEmbed j d, I.towerEmbed_mem_below hd⟩ := by
    rw [hwD_def, CellScheme.splice_of_le hd, hV]
    exact Rows.extendBot_of_mem v _
  have hwDgt (d : Fin I.amalgam.card) (hd : ¬ I.amalgam.toCellScheme.grade d ≤ j) : wD d = ⊥ := by
    rw [hwD_def, CellScheme.splice_of_lt (not_le.mp hd)]
  have hvC (d : Fin I.amalgam.card) (hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase x, j + 1))
      (hd : I.amalgam.toCellScheme.grade d ≤ j) :
      v ⟨I.towerEmbed j d, I.towerEmbed_mem_below hd⟩ = wC d := by
    have := hvP ⟨I.towerEmbed j d, I.towerEmbed_mem_below_iff.mpr ⟨hdC.1, hd⟩⟩
    rw [← hPe d]
    exact this
  refine ⟨wD, hwDl, fun d hdC hdD ↦ ?_, fun d hdD ↦ ?_, v, hv, fun d hd ↦ ?_, hva⟩
  · by_cases hd : I.amalgam.toCellScheme.grade d ≤ j
    · rw [hwDle d hd, hvC d hdC hd]
    · rw [hwDgt d hd, hdead x (by simpa using hx) wC hwC d hdC (le_antisymm hdC.2 (by omega))]
  · by_cases hd : I.amalgam.toCellScheme.grade d ≤ j
    · rw [hwDle d hd]; exact hva _
    · rw [hwDgt d hd, hdead y (by simpa using hy) (fun d ↦ a (I.towerEmbed j d)) haD d hdD
        (le_antisymm hdD.2 (by omega))]
  · split_ifs with hdC
    · exact hvC d hdC hd
    · exact (hwDle d hd).symm

/-- Lifts carried down to the previous scheme: between pairs of grade at most `j`, a capped lift
of the scheme reached after the grade `j + 1` is one of the scheme reached after the grade `j`. -/
theorem cappedLift_tower_of_succ {j j' : ℕ} (hj' : j' ≤ j) {X : Finset (Fin (m + 2)) × ℕ}
    {hX : X ≤ (univ, j')} (hl : (I.tower (j + 1)).rows.CappedLift hX) :
    (I.tower j).rows.CappedLift hX := by
  have h := I.isSourcePrefix_tower_succ hj'
  have hc : (I.tower (j + 1)).rows.comap h.isLowerEmbedding = (I.tower j).rows :=
    I.comap_rows_tower_succ j
  rw [← hc, h.cappedLift_iff hX le_rfl]
  exact hl

/-- The invariant at `j + 1` restricts to the invariant at `j`. -/
theorem towerInvariant_of_succ {j : ℕ} (hinv : I.TowerInvariant (j + 1)) : I.TowerInvariant j :=
  fun x hx j' hj' ↦ I.cappedLift_tower_of_succ hj' (hinv x hx j' (hj'.trans (Nat.le_succ j)))

/-- The invariant at `k` restricts to the invariant at every `j ≤ k`. -/
theorem towerInvariant_of_le {j k : ℕ} (hjk : j ≤ k) (hinv : I.TowerInvariant k) :
    I.TowerInvariant j := by
  induction k, hjk using Nat.le_induction with
  | base => exact hinv
  | succ k _ ih => exact ih (I.towerInvariant_of_succ hinv)

/-- **The invariant at `j + 1` implies `2FL∃(j)`**: the lift from `(C, j + 1)` to `(univ, j + 1)`
along the row of the new cell whose entry is `a`, at the cap `h`, chooses `wD` (its trace on the
other coatom) and gives the two-face extension (its trace below `(univ, j)`).  So `2FL∃(j)` is
necessary for the step; no hypothesis beyond the invariant at `j + 1` is used. -/
theorem twoFaceLiftExists_of_towerInvariant {j : ℕ} (hinv : I.TowerInvariant (j + 1)) :
    I.TwoFaceLiftExists j := by
  classical
  intro x hx y hy hxy a ha h hh hs hbot wC hwC hag
  obtain ⟨i, rfl⟩ := Scheme.exists_catalogueEntry_eq (S := I.tower j) (k := j + 1) ha
  have hu : (I.tower (j + 1)).toCellScheme.gradedIndex (Fin.natAdd _ i) = (univ, j + 1) :=
    Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i
  set q := (I.tower (j + 1)).rows.rowBelow (Fin.natAdd _ i) hu with hq_def
  have hq : (I.tower (j + 1)).rows.IsLawfulBelow (univ, j + 1) q :=
    Rows.isLawfulBelow_rowBelow hu (I.isConsistent_tower (j + 1) _)
  have hrow (e : Fin (I.tower j).card)
      (he : Fin.castAdd ((I.tower j).catalogue (j + 1)).card e ∈
        (I.tower (j + 1)).toCellScheme.below (univ, j + 1)) :
      q ⟨_, he⟩ = (I.tower j).catalogueEntry (j + 1) i e :=
    (Scheme.fieldLayer_row_natAdd (hS := I.not_univ_succ_le_tower j) i _).trans
      (Scheme.fieldRow_castAdd _ _)
  set P : Fin (I.tower (j + 1)).card → Label.{u} :=
    Function.extend (I.towerEmbed (j + 1)) wC (fun _ ↦ ⊥)
  have hPe (d : Fin I.amalgam.card) : P (I.towerEmbed (j + 1) d) = wC d :=
    (I.towerEmbed (j + 1)).injective.extend_apply _ _ _
  have hPC : (I.tower (j + 1)).rows.IsLawfulBelow (univ.erase x, j + 1) fun e ↦ P e := by
    rw [I.isLawfulBelow_tower_iff (ne_univ_erase x)]
    simpa only [hPe] using hwC
  obtain ⟨r', hr', hr'q, hr'P⟩ := (Rows.cappedLift_iff_forall_exists _).mp
    (hinv x hx (j + 1) le_rfl) h hh (fun e ↦ P e) q hPC hq fun e ↦ by
      obtain ⟨e, he⟩ := e
      obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed (j + 1) e fun hu ↦
        ne_univ_erase x (univ_subset_iff.mp (hu.ge.trans he.1))
      have hdC := I.towerEmbed_mem_below_iff.mp he
      have h1 : q ⟨I.towerEmbed (j + 1) d, I.towerEmbed_mem_below hdC.2⟩ =
          (I.tower j).catalogueEntry (j + 1) i (I.towerEmbed j d) :=
        hrow (I.towerEmbed j d) (I.towerEmbed_mem_below hdC.2)
      change min (q ⟨I.towerEmbed (j + 1) d, _⟩) h = min (P (I.towerEmbed (j + 1) d)) h
      rw [h1, hPe]
      exact (hag d hdC).symm
  set R' : Fin (I.tower (j + 1)).card → Label.{u} := Rows.extendBot (univ, j + 1) r' with hR'
  set wD : Fin I.amalgam.card → Label.{u} := fun d ↦ R' (I.towerEmbed (j + 1) d) with hwD_def
  have hwDl : I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) fun d ↦ wD d :=
    (I.isLawfulBelow_tower_iff (g := R') (ne_univ_erase y)).mp
      ((Rows.isLawfulBelow_extendBot.mpr hr').mono (X := (univ.erase y, j + 1))
        ⟨subset_univ _, le_rfl⟩)
  have hmemU (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ j + 1) :
      I.towerEmbed (j + 1) d ∈ (I.tower (j + 1)).toCellScheme.below (univ, j + 1) :=
    I.towerEmbed_mem_below hd
  have hwDr (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ j + 1) :
      wD d = r' ⟨I.towerEmbed (j + 1) d, hmemU d hd⟩ := Rows.extendBot_of_mem r' _
  have hr'C (d : Fin I.amalgam.card)
      (hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase x, j + 1)) :
      r' ⟨I.towerEmbed (j + 1) d, hmemU d hdC.2⟩ = wC d := by
    have := hr'P ⟨I.towerEmbed (j + 1) d, I.towerEmbed_mem_below_iff.mpr hdC⟩
    rw [← hPe d]
    exact this
  have hmem (e : (I.tower j).toCellScheme.below (univ, j)) :
      Fin.castAdd ((I.tower j).catalogue (j + 1)).card e.1 ∈
        (I.tower (j + 1)).toCellScheme.below (univ, j + 1) :=
    Scheme.castAdd_mem_below (hS := I.not_univ_succ_le_tower j) (e.2.2.trans (Nat.le_succ j))
  refine ⟨wD, hwDl, fun d hdC _ ↦ (hwDr d hdC.2).trans (hr'C d hdC), fun d hdD ↦ ?_,
    fun e ↦ r' ⟨_, hmem e⟩, ?_, fun d hd ↦ ?_, fun e ↦ ?_⟩
  · rw [hwDr d hdD.2, hr'q]
    exact congrArg (min · h) (hrow (I.towerEmbed j d) _)
  · -- Lawfulness below `(univ, j)`, carried back through the source prefix.
    have P' := I.isSourcePrefix_tower_succ (j := j) le_rfl
    have hc : (I.tower (j + 1)).rows.comap P'.isLowerEmbedding = (I.tower j).rows :=
      I.comap_rows_tower_succ j
    have hrj : (I.tower (j + 1)).rows.IsLawfulBelow (univ, j) fun t ↦
        Rows.extendBot (univ, j + 1) r' t :=
      (Rows.isLawfulBelow_extendBot.mpr hr').mono (X := (univ, j)) ⟨subset_rfl, Nat.le_succ j⟩
    have := (P'.isLawfulBelow_iff le_rfl).mpr hrj
    rw [hc] at this
    convert this using 1
    funext e
    exact (Rows.extendBot_of_mem r' (hmem e)).symm
  · split_ifs with hdC
    · exact hr'C d hdC
    · exact (hwDr d (hd.trans (Nat.le_succ j))).symm
  · exact (hr'q _).trans (congrArg (min · h) (hrow e.1 (hmem e)))

/-- **For `j ≤ m` and under the invariant at the grade `j`, the invariant at `j + 1` holds exactly
when `2FL∃(j)` does**: `2FL∃(j)` is the hypothesis of the step, stated exactly
(`Seed.towerInvariant_succ_of_twoFaceLiftExists`, `Seed.twoFaceLiftExists_of_towerInvariant`), a
reformulation of the step through the tower and not a weaker sufficient hypothesis. -/
theorem towerInvariant_succ_iff_twoFaceLiftExists {j : ℕ} (hjm : j ≤ m)
    (hinv : I.TowerInvariant j) : I.TowerInvariant (j + 1) ↔ I.TwoFaceLiftExists j :=
  ⟨I.twoFaceLiftExists_of_towerInvariant, I.towerInvariant_succ_of_twoFaceLiftExists hjm hinv⟩

/-- **The invariant up to the grade `m + 1` under `2FL∃(j)` at the grades `2 ≤ j < m`.**  The
grades `0` and `1` are the base, the step to the grade `2` uses `2FL(1)` (`Seed.twoFaceLift_one`),
the steps to the grades `j + 1` with `2 ≤ j < m` use
`Seed.towerInvariant_succ_of_twoFaceLiftExists`, and the step to the top grade is
`Seed.towerInvariant_top`. -/
theorem towerInvariant_of_twoFaceLiftExists
    (hE : ∀ j, 2 ≤ j → j < m → I.TwoFaceLiftExists j) : ∀ j ≤ m + 1, I.TowerInvariant j
  | 0, _ => I.towerInvariant_zero
  | 1, _ => I.towerInvariant_one
  | j + 2, hj =>
    if hjm : j + 1 < m then
      if hj0 : j = 0 then by
        subst hj0
        exact I.towerInvariant_succ hjm.le I.towerInvariant_one I.twoFaceLift_one
      else
        I.towerInvariant_succ_of_twoFaceLiftExists hjm.le
          (towerInvariant_of_twoFaceLiftExists hE (j + 1) (by omega)) (hE (j + 1) (by omega) hjm)
    else by
      have hinv := towerInvariant_of_twoFaceLiftExists hE (j + 1) (by omega)
      rw [show j + 1 = m by omega] at hinv
      rw [show j + 2 = m + 1 by omega]
      exact I.towerInvariant_top hinv

/-- **The completion below the full grade under `2FL∃(j)` at the grades `2 ≤ j < m`**: the scheme
`T (m + 1)` of the tower (`Seed.completionBelowFullGradeOfTowerInvariant`).  The hypothesis is on
the seed `I`. -/
theorem nonempty_completionBelowFullGrade_of_twoFaceLiftExists
    (hE : ∀ j, 2 ≤ j → j < m → I.TwoFaceLiftExists j) : Nonempty (CompletionBelowFullGrade I) :=
  ⟨I.completionBelowFullGradeOfTowerInvariant
    (I.towerInvariant_of_twoFaceLiftExists hE (m + 1) le_rfl)⟩

/-- **`2FL∃(j)` is necessary for the invariant**: if the invariant holds up to the top grade, then
`2FL∃(j)` holds at every grade `j ≤ m`. -/
theorem twoFaceLiftExists_of_towerInvariant_top (hinv : I.TowerInvariant (m + 1)) {j : ℕ}
    (hjm : j ≤ m) : I.TwoFaceLiftExists j :=
  I.twoFaceLiftExists_of_towerInvariant (I.towerInvariant_of_le (by omega) hinv)

/-- **The invariant up to the top grade holds exactly when `2FL∃(j)` holds at the grades
`2 ≤ j < m`**, with no hypothesis on the stage: the hypothesis of the steps of the tower from the
grade `2` on, stated exactly. -/
theorem towerInvariant_top_iff :
    I.TowerInvariant (m + 1) ↔ ∀ j, 2 ≤ j → j < m → I.TwoFaceLiftExists j :=
  ⟨fun hinv _ _ hjm ↦ I.twoFaceLiftExists_of_towerInvariant_top hinv hjm.le,
    fun hE ↦ I.towerInvariant_of_twoFaceLiftExists hE (m + 1) le_rfl⟩

/-! ### The raised union fill -/

open Classical in
/-- **The raised union fill at the grade `j`**, a condition on the amalgam.  For both orders of the
coatoms `C = univ.erase x`, `D = univ.erase y`, every labelling `a` of the amalgam lawful below
both coatoms at the grade `j + 1`, every cap `h` self-visible and short at `j + 1` with `⊥ < h`,
and every prescription `wC` lawful below `(C, j + 1)` agreeing with `a` capped at `h`, some cap
`c ≥ h` self-visible at `j` is below `wC` at every cell of `(C, j)` where `a` reaches `h`, and
every labelling `V` lawful below `(D, j)` that agrees with `a` *raised to `⊤` above `h`* capped at
`c` (and with `wC` on the common face) extends to `(D, j + 1)`, the cells of the grade `j + 1`
taking `wC` on the common face and agreeing with `a` capped at `h`.  The caps `h` are those of
`2FL∃(j)` (`Seed.TwoFaceLiftExists`). -/
def RaisedUnionFill (j : ℕ) : Prop :=
  ∀ x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))),
  ∀ y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))), x ≠ y →
  ∀ a : Fin I.amalgam.card → Label.{u},
    I.amalgam.rows.IsLawfulBelow (univ.erase x, j + 1) (fun d ↦ a d) →
    I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) (fun d ↦ a d) →
  ∀ h : Label.{u}, IsSelfVisible (j + 1) h → IsShort (j + 1) h → ⊥ < h →
  ∀ wC : Fin I.amalgam.card → Label.{u},
    I.amalgam.rows.IsLawfulBelow (univ.erase x, j + 1) (fun d ↦ wC d) →
    (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j + 1), min (wC d) h = min (a d) h) →
    ∃ c : Label.{u}, IsSelfVisible j c ∧ h ≤ c ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j), h ≤ a d → c ≤ wC d) ∧
      ∀ V : Fin I.amalgam.card → Label.{u},
        I.amalgam.rows.IsLawfulBelow (univ.erase y, j) (fun d ↦ V d) →
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase y, j),
          min (V d) c = min (raise h (a d)) c) →
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j),
          d ∈ I.amalgam.toCellScheme.below (univ.erase y, j) → V d = wC d) →
        ∃ wD : Fin I.amalgam.card → Label.{u},
          I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) (fun d ↦ wD d) ∧
          (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase y, j), wD d = V d) ∧
          (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j + 1),
            d ∈ I.amalgam.toCellScheme.below (univ.erase y, j + 1) →
            j < I.amalgam.toCellScheme.grade d → wD d = wC d) ∧
          ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase y, j + 1),
            j < I.amalgam.toCellScheme.grade d → min (wD d) h = min (a d) h

/-- **The raised union fill and the invariant at `j` give `2FL∃(j)`**: lift the prescription from
`(C, j)` to `(univ, j)` along the catalogue entry raised to `⊤` above the cap (a lawful ambient,
`raise` being a witness bounded by the grade `j`), at the cap `c` of the condition; fill the other
coatom's cells of the grade `j + 1`; the lift is the two-face extension. -/
theorem twoFaceLiftExists_of_raisedUnionFill {j : ℕ} (hinv : I.TowerInvariant j)
    (hR : I.RaisedUnionFill j) : I.TwoFaceLiftExists j := by
  classical
  intro x hx y hy hxy a ha h hh hs hbot wC hwC hag
  have haL : (I.tower j).rows.IsLawful a := (Scheme.mem_catalogue.mp ha).1
  have haX (z : Fin (m + 2)) : I.amalgam.rows.IsLawfulBelow (univ.erase z, j + 1)
      fun d ↦ a (I.towerEmbed j d) :=
    (I.isLawfulBelow_tower_iff (g := a) (ne_univ_erase z)).mp (haL.isLawfulBelow _)
  obtain ⟨c, hc, hhc, hcw, hfill⟩ := hR x hx y hy hxy (fun d ↦ a (I.towerEmbed j d)) (haX x)
    (haX y) h hh hs hbot wC hwC hag
  -- The raised ambient.
  set q' : (I.tower j).toCellScheme.below (univ, j) → Label.{u} := fun e ↦ raise h (a e)
    with hq'_def
  have hq' : (I.tower j).rows.IsLawfulBelow (univ, j) q' :=
    (haL.isLawfulBelow (univ, j)).map_of_apply_eq_bot (K := j) (fun d ↦ d.2.2)
      (isWitness_raise (K := j) hh hbot) fun _ hd ↦ eq_bot_of_raise_eq_bot hd
  -- The prescription on `(C, j)`.
  set P : Fin (I.tower j).card → Label.{u} := Function.extend (I.towerEmbed j) wC (fun _ ↦ ⊥)
  have hPe (d : Fin I.amalgam.card) : P (I.towerEmbed j d) = wC d :=
    (I.towerEmbed j).injective.extend_apply _ _ _
  have hPC : (I.tower j).rows.IsLawfulBelow (univ.erase x, j) fun e ↦ P e := by
    rw [I.isLawfulBelow_tower_iff (ne_univ_erase x)]
    simp only [hPe]
    exact hwC.mono (X := (univ.erase x, j)) ⟨subset_rfl, Nat.le_succ j⟩
  obtain ⟨v, hv, hvq, hvP⟩ := (Rows.cappedLift_iff_forall_exists _).mp (hinv x hx j le_rfl) c
    hc (fun e ↦ P e) q' hPC hq' fun e ↦ by
      obtain ⟨e, he⟩ := e
      obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed j e fun hu ↦
        ne_univ_erase x (univ_subset_iff.mp (hu.ge.trans he.1))
      have hdC := I.towerEmbed_mem_below_iff.mp he
      have hdC1 : d ∈ I.amalgam.toCellScheme.below (univ.erase x, j + 1) :=
        ⟨hdC.1, hdC.2.trans (Nat.le_succ j)⟩
      change min (raise h (a (I.towerEmbed j d))) c = min (P (I.towerEmbed j d)) c
      rw [hPe]
      have hagd := hag d hdC1
      by_cases hle : h ≤ a (I.towerEmbed j d)
      · unfold raise
        rw [ite_eq_left hle, min_top_left]
        exact (min_eq_right (hcw d hdC hle)).symm
      · unfold raise
        rw [ite_eq_right hle, eq_of_min_eq_of_lt hagd.symm (not_le.mp hle)]
  -- The lift read on the amalgam.
  set V : Fin I.amalgam.card → Label.{u} := fun d ↦ Rows.extendBot (univ, j) v (I.towerEmbed j d)
    with hV
  have hVv (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ j) :
      V d = v ⟨I.towerEmbed j d, I.towerEmbed_mem_below hd⟩ := Rows.extendBot_of_mem v _
  have hVD : I.amalgam.rows.IsLawfulBelow (univ.erase y, j) fun d ↦ V d :=
    (I.isLawfulBelow_tower_iff (g := Rows.extendBot (univ, j) v) (ne_univ_erase y)).mp
      ((Rows.isLawfulBelow_extendBot.mpr hv).mono (X := (univ.erase y, j)) ⟨subset_univ _, le_rfl⟩)
  have hvC (d : Fin I.amalgam.card) (hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase x, j)) :
      V d = wC d := by
    rw [hVv d hdC.2, ← hPe d]
    exact hvP ⟨I.towerEmbed j d, I.towerEmbed_mem_below_iff.mpr hdC⟩
  obtain ⟨wD, hwD, hwDV, hwDE, hwDa⟩ := hfill V hVD
    (fun d hd ↦ by rw [hVv d hd.2]; exact hvq ⟨I.towerEmbed j d, I.towerEmbed_mem_below hd.2⟩)
    fun d hdC _ ↦ hvC d hdC
  refine ⟨wD, hwD, fun d hdC hdD ↦ ?_, fun d hdD ↦ ?_, v, hv, fun d hd ↦ ?_, fun e ↦ ?_⟩
  · by_cases hdj : I.amalgam.toCellScheme.grade d ≤ j
    · rw [hwDV d ⟨hdD.1, hdj⟩, hvC d ⟨hdC.1, hdj⟩]
    · exact hwDE d hdC hdD (not_le.mp hdj)
  · by_cases hdj : I.amalgam.toCellScheme.grade d ≤ j
    · rw [hwDV d ⟨hdD.1, hdj⟩, hVv d hdj]
      have := min_eq_min_of_le (hvq ⟨I.towerEmbed j d, I.towerEmbed_mem_below hdj⟩) hhc
      change min (v _) h = min (raise h (a (I.towerEmbed j d))) h at this
      rw [this, min_raise]
    · exact hwDa d hdD (not_le.mp hdj)
  · split_ifs with hdC
    · rw [← hVv d hd]; exact hvC d ⟨hdC.1, hd⟩
    · rcases I.scope_subset_or hx hy hxy d with hsc | hsc
      · exact absurd ⟨hsc, hd.trans (Nat.le_succ j)⟩ hdC
      · rw [hwDV d ⟨hsc, hd⟩, hVv d hd]
  · have := min_eq_min_of_le (hvq e) hhc
    rw [this]
    exact min_raise h (a e)

/-- **Deadness gives the raised union fill**, with the cap `h` and `⊥` at the cells of the grade
`j + 1` of the other coatom. -/
theorem raisedUnionFill_of_deadAt {j : ℕ} (hdead : I.DeadAt j) : I.RaisedUnionFill j := by
  classical
  intro x hx y hy hxy a hax hay h hh _ hbot wC hwC hag
  refine ⟨h, hh.mono (Nat.le_succ j), le_rfl, fun d hd hle ↦ ?_, fun V hV _ _ ↦ ?_⟩
  · have := hag d ⟨hd.1, hd.2.trans (Nat.le_succ j)⟩
    rw [min_eq_right hle] at this
    exact min_eq_right_iff.mp this
  · refine ⟨I.amalgam.toCellScheme.splice j (fun _ ↦ ⊥) V,
      Rows.IsLawfulBelow.splice (M := ⊥) (Rows.isLawfulBelow_const_bot _) hV
        (fun _ _ _ ↦ le_rfl) (fun _ _ ↦ by simp),
      fun d hd ↦ CellScheme.splice_of_le hd.2, fun d hdC _ hdj ↦ ?_, fun d hdD hdj ↦ ?_⟩
    · rw [CellScheme.splice_of_lt hdj, hdead x hx wC hwC d hdC (le_antisymm hdC.2 hdj)]
    · rw [CellScheme.splice_of_lt hdj, hdead y hy a hay d hdD (le_antisymm hdD.2 hdj)]

/-- **The step from the grade `j` to `j + 1` under the raised union fill**, for `j ≤ m` and under
the invariant at the grade `j`. -/
theorem towerInvariant_succ_of_raisedUnionFill {j : ℕ} (hjm : j ≤ m)
    (hinv : I.TowerInvariant j) (hR : I.RaisedUnionFill j) : I.TowerInvariant (j + 1) :=
  I.towerInvariant_succ_of_twoFaceLiftExists hjm hinv
    (I.twoFaceLiftExists_of_raisedUnionFill hinv hR)

end VaughtConjecture.Seed
