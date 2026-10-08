/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.SmallArities

/-!
# The tower of field layers, and the step from the grade `j` to `j + 1`

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.6 (the recursion on the grade; here its first part: the
tower, the lifting invariant, and the step from the grade `j` to `j + 1`, under the two-face lift
at the grades `2 ≤ j + 1 ≤ m`); semantic contract, items 2–4.

Let `I` be a seed on `m + 2` points.  Its two coatoms are `univ.erase x` for the two points
`x ∈ {Fin.last (m + 1), Fin.castSucc (Fin.last m)}`; they meet in the **common face**, on `m`
points, a face of the amalgam (`Seed.commonFace_mem_faces`).

**The tower** (`Seed.tower`).  The canonical field layer of a scheme `S` at a grade `k`
(`Scheme.fieldLayer`, `VaughtConjecture.Extension.FieldLayer`) appends to `S` one cell of full
scope and grade `k` for each lawful labelling of `S` that is bottom above the grade `k` and fixed by
the orbit code at `k`, its *catalogue entry*; the row of each new cell reads its entry on the cells
of `S` and agreement heights on the new cells.  The *tower of field layers* is the sequence of
schemes `T j`: `T 0` is the amalgam, and `T (j + 1)` is the canonical field layer of `T j` at the
grade `j + 1` (`Seed.tower_succ`, by `rfl`), its *layer* at the grade `j + 1`.  It is defined by
recursion together with the property that every cell of `T j` has grade at most `j` or scope other
than the ground set (`Seed.tower_grade_le_or`), which makes the next layer defined.  The cells of
the amalgam, carried along `Fin.castAdd` through each layer (`Seed.towerEmbed`), are the *old
cells*; the others, the *new cells*, have full scope.

* **Prefix equations.**  The old cells form a lower embedding keeping scopes and grades, every cell
  of proper scope is old, the rows pull back to those of the amalgam, and the faces are those of the
  amalgam (`Seed.isLowerEmbedding_tower`, `Seed.mem_range_towerEmbed`, `Seed.comap_rows_tower`,
  `Seed.faces_tower`).  So the amalgam is a source prefix of every `T j` at the pairs whose face is
  not the ground set (`Seed.isSourcePrefix_tower`), and `T j` is a source prefix of `T (j + 1)` at
  the pairs of grade at most `j` (`Seed.isSourcePrefix_tower_succ`); lawfulness and lifts there are
  those of the scheme before (`Seed.isLawfulBelow_tower_iff`, `Seed.cappedLift_tower_iff`,
  `Seed.cappedLift_tower_succ`).
* **Structural laws.**  Every `T j` is consistent and coded, well formed up to the grade `m + 2`,
  of grades below `m + 2` up to the grade `m + 1`; its graded faces of proper scope carry old cells,
  and its layer at the grade `j + 1` has a cell at `(univ, j + 1)`.
* **Extension at the cap `⊥`** (`Seed.exists_isLawfulBelow_tower`, `Seed.exists_isLawful_tower`).
  A labelling of the amalgam lawful below the two coatoms at the grade `j` extends, unchanged at the
  old cells, to one lawful below `(univ, j)` in `T j`: at each layer the extension below the
  previous grade and the old cells of the grade are glued (`CellScheme.Rows.IsLawfulBelow.glue₃`)
  and extended through the new cells.  A lawful section of the amalgam extends to every `T j`,
  keeping every old label literally, the labels `⊤` included.  At the grade `2`, the extension
  through `T 1`, glued with the old cells of grade `2` and spliced with `⊥` above, has a catalogue
  entry of the layer at the grade `2` as its orbit code (`Seed.exists_orbitCode_mem_catalogue_two`).
* **Literal faces** (`TowerExamples.towerType`, `TowerExamples.restrictFace_left_towerType`,
  `TowerExamples.restrictFace_right_towerType`).  At a stage that is zero or a limit, `T j` for
  `j ≤ m + 2`, with the labels of the amalgam extended through the tower and reduced to the stage,
  is a stage type whose faces along the two coatoms are the two coatom types of the seed, labels
  included.

**The lifting invariant** (`Seed.TowerInvariant j`): for both coatoms `C` and every `j' ≤ j`, the
rows of `T j` lift capped from `(C, j')` to `(univ, j')`, at every cap self-visible at `j'` and for
every lawful ambient.  It holds at the grade `0` (no cells) and at the grade `1` at every arity
(`Seed.towerInvariant_one`): there the one-grade lift uses the coatoms at the grade `1` and the
common face, whose lift into the other coatom is a lift of the amalgam
(`Seed.cappedLift_commonFace_tower`); no lower layer is read.

**The step** (`Seed.towerInvariant_succ`, `Seed.towerInvariant_top`).  For the one-grade lift from
`(C, j + 1)` to `(B, j + 1)`, a *boundary triple* is a triple of pairs `U, V ≤ (B, j + 1)` and
`O ≤ U, V` with `(C, j + 1) ≤ U`, such that every cell below both `U` and `V` lies below `O`,
together with capped lifts from `(C, j + 1)` to `U` and from `O` to `V`; its *boundary* is the set
of cells below `U` or `V`.  In both cases below, the lift at the lower grade, which the
restoration of the lower prescriptions uses, is the invariant from `(C, j)` to `(univ, j)`.

* **At the grades `j + 1 ≤ m`, under the two-face lift** (`Seed.towerInvariant_succ`), one
  boundary triple serves at `⊥` and at the positive caps
  (`CellScheme.Rows.cappedLift_of_boundary_short`): `U = (C, j + 1)`, `V = (D, j + 1)` for the
  other coatom `D`, and `O` the common face at the grade `min (j + 1) m`; the lift from `O` to `V`
  is a lift of the amalgam.  At `⊥` the extension from the boundary is the extension at `⊥` through
  the whole tower (`Seed.extendsFromBoundary_bot_tower`).  At a positive cap `h` short at `j + 1`,
  along the row of a new cell with catalogue entry `a`, the boundary labelling is extended through
  the new cells of the layers `1, …, j` by the two-face lift `2FL(j)` below, glued with the old
  cells of the grade `j + 1` over `(C, j + 1)`, `(univ, j)` and `(D, j + 1)`, and extended through
  the new cells of the layer `j + 1` at the short cap
  (`Seed.extendsFromBoundary_tower_of_twoFaceLift`).
* **The step to the top grade `m + 1`, with no hypothesis beyond the invariant at `m`**
  (`Seed.towerInvariant_top`): at `⊥` the same triple, and at the positive caps
  `U = (C, m + 1)`, `V = (univ, m)`, `O = (C, m)`, with the invariant as the lift from `O` to `V`
  (`CellScheme.Rows.cappedLift_of_boundaries_short`).  The common face, on `m` points, carries no
  cell of the grade `m + 1`, so the other coatom's cells of the grade `m + 1` are reached by a lift
  within that coatom from the grade `m` (`Seed.exists_lift_union_of_lt_grade`), and the extension
  from the boundary reads no new cell across the two faces (`Seed.extendsFromBoundary_tower_top`).

**The two-face lift** `2FL(j)` (`Seed.TwoFaceLift j`): along every catalogue entry `a` of the layer
at the grade `j + 1`, at every cap `h` self-visible and short at `j + 1` with `⊥ < h`, a labelling
of the amalgam lawful below both coatoms at the grade `j + 1` and agreeing with `a` capped at `h`
extends through the new cells of the layers `1, …, j`, unchanged at the old cells of grade at most
`j`, to one lawful below `(univ, j)` agreeing with `a` capped at `h`.  It chooses one labelling of
the lower layers that respects both faces and the cap at once.  The cap `h` is short at `j + 1` but
need not be short at the grades of the layers it crosses.

* The invariant up to the grade `m + 1` holds under `2FL(j)` at the grades `2 ≤ j + 1 ≤ m`
  (`Seed.towerInvariant_of_twoFaceLift`), and at the arities `m ≤ 1` with no hypothesis
  (`Seed.towerInvariant_of_le_one`, which does not use `Seed.TwoFaceLift`).  `2FL(0)` holds, below
  `(univ, 0)` there being no cells (`Seed.twoFaceLift_zero`); `2FL(1)` is the first instance the
  step assumes, and at the arity `2` the only one.  It holds at every arity (`Seed.twoFaceLift_one`,
  module `VaughtConjecture.Extension.TwoFaceLift`).
* `2FL(j)` is a hypothesis on the seed here, at the grades `2 ≤ j + 1 ≤ m`: it is not a field of
  `Seed` and is not derived from the bountifulness of the amalgam.  For `j ≥ 2` it is not a property
  of every seed: `2FL(2)` fails for a legal seed on five points
  (`TwoFaceLiftCounterexample.not_twoFaceLift_two`, module
  `VaughtConjecture.Extension.TwoFaceLiftCounterexample`), a non-existence of the extension, not a
  limitation of an encoding.  For that seed the old cells of the grade `3` are *dead* (`⊥` in every
  labelling lawful below a coatom, `Seed.DeadAt 2`), and the step from deadness
  (`Seed.towerInvariant_succ_of_dead`, module `VaughtConjecture.Extension.DeadCellStep`), which uses
  the boundary triples of the step to the top grade, gives the invariant without `2FL(2)`.  The
  hypothesis of the step, stated exactly, is the existential two-face lift
  (`Seed.TwoFaceLiftExists`, module `VaughtConjecture.Extension.TwoFaceLiftExists`), implied by
  `2FL(j)` (for `j ≤ m`) and by deadness together with the invariant at `j`, and holding for a legal
  seed where neither `2FL(j)` nor deadness does.  It fails at `j = 2` for another legal seed on five
  points (`TwoFaceLiftExistsCounterexample.not_twoFaceLiftExists_two_seedL`, module
  `VaughtConjecture.Extension.TwoFaceLiftExistsCounterexample`), so the tower does not complete
  every seed; a completion of that seed by another construction is not refuted.  Bountifulness and
  legality of the tower and the completion below the full grade are proved from the invariant at the
  top grade in the module `VaughtConjecture.Extension.TwoFaceLift`: with no hypothesis at the
  arities `m ≤ 2`, and for a seed satisfying `2FL(j)` at the grades `2 ≤ j < m` at every arity.
  `StageType.HasApexCoatomExtensions` and `StageType.HasCoatomExtensions` at the stages that are
  zero or a limit are compiled in this repository (theorem named) by the levels of rank-normalized
  profiles over `T 2` (`StageType.hasApexCoatomExtensions`, `StageType.hasCoatomExtensions`), not by
  the tower alone.

**The union fill is refuted as a universal statement.**  With `V = (univ, j)` at every grade, as at
the top grade, the step would fill the other coatom's cells of the grade `j + 1` over the union of
the common face at the grade `j + 1` and `(D, j)`.  That *union fill* fails for a legal
seed on four points at the grade `2` (module `VaughtConjecture.Extension.UnionFillCounterexample`):
a row of the other coatom can couple a cell of the common face at the grade `j + 1` to a cell of
lower grade off it.  This refutes the union fill as a universal statement about seeds, not the
completion below the full grade, and it does not make every conditional instance vacuous: the
union fill holds, for instance, whenever the common face carries no cell of the grade, which is the
case of the top grade above.

No hypothesis on the stage enters, and no completion is assumed: the lifts off the full face come
from the bountifulness of the amalgam through the source prefix.  The completion at the arities
`m ≤ 1` is built without the tower (module `VaughtConjecture.Extension.SmallArityOne`).

## Placement

Checkpoint 2.6 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

The amalgam is [Kni26, Definition 4.3.1], with its bountifulness [Kni26, Lemma 4.3.2]; the
completion has the shape of [Kni26, Definition 4.3.14], not its rows.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-! ### The tower -/

/-- A scheme on `m + 2` points whose cells all have grade at most `j` or scope other than the
ground set lies above no cell at `(univ, j + 1)`. -/
private theorem not_univ_succ_le_of_forall {S : Scheme.{u} (m + 2)} {j : ℕ}
    (hS : ∀ d, S.toCellScheme.grade d ≤ j ∨ S.toCellScheme.scope d ≠ univ) (d : Fin S.card) :
    ¬ ((univ : Finset (Fin (m + 2))), j + 1) ≤ S.toCellScheme.gradedIndex d := fun hd ↦
  (hS d).elim (fun h ↦ absurd hd.2 (by simp only [CellScheme.gradedIndex_snd]; omega))
    fun h ↦ h (univ_subset_iff.mp hd.1)

/-- The tower together with the property that makes the next layer defined: every cell of the
scheme at the grade `j` has grade at most `j` or scope other than the ground set. -/
noncomputable def towerAux : (j : ℕ) → {S : Scheme.{u} (m + 2) //
    ∀ d, S.toCellScheme.grade d ≤ j ∨ S.toCellScheme.scope d ≠ univ}
  | 0 => ⟨I.amalgam.toScheme, fun d ↦ .inr (I.scope_ne_univ d)⟩
  | j + 1 => ⟨(towerAux j).1.fieldLayer (j + 1) (not_univ_succ_le_of_forall (towerAux j).2),
      fun d ↦ by
        induction d using Fin.addCases with
        | left d =>
          rw [Scheme.appendFullCellsScheme_grade_castAdd,
            Scheme.appendFullCellsScheme_scope_castAdd]
          exact ((towerAux j).2 d).imp_left fun h ↦ h.trans (Nat.le_succ j)
        | right i => exact .inl (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le⟩

/-- The **tower of field layers** of a seed: the scheme `T j` reached after the grade `j`.  It is
the amalgam at `j = 0`, and `T (j + 1)` is the canonical field layer of `T j` at the grade `j + 1`
(`Seed.tower_succ`). -/
noncomputable abbrev tower (j : ℕ) : Scheme.{u} (m + 2) := (I.towerAux j).1

/-- Every cell of the scheme reached after the grade `j` has grade at most `j` or scope other than
the ground set: the new cells of the layers up to `j` have grade at most `j`, the old cells have
proper scope. -/
theorem tower_grade_le_or (j : ℕ) (d : Fin (I.tower j).card) :
    (I.tower j).toCellScheme.grade d ≤ j ∨ (I.tower j).toCellScheme.scope d ≠ univ :=
  (I.towerAux j).2 d

/-- No cell of the scheme reached after the grade `j` lies above `(univ, j + 1)`. -/
theorem not_univ_succ_le_tower (j : ℕ) (d : Fin (I.tower j).card) :
    ¬ ((univ : Finset (Fin (m + 2))), j + 1) ≤ (I.tower j).toCellScheme.gradedIndex d :=
  not_univ_succ_le_of_forall (I.tower_grade_le_or j) d

/-- The tower starts at the amalgam. -/
theorem tower_zero : I.tower 0 = I.amalgam.toScheme := rfl

/-- **The tower equation**: the scheme reached after the grade `j + 1` is the canonical field
layer at the grade `j + 1` of the scheme reached after the grade `j`. -/
theorem tower_succ (j : ℕ) :
    I.tower (j + 1) = (I.tower j).fieldLayer (j + 1) (I.not_univ_succ_le_tower j) := rfl

/-- The **old cells** in the scheme reached after the grade `j`: the cells of the amalgam, along
`Fin.castAdd` once for each layer. -/
noncomputable def towerEmbed : (j : ℕ) → Fin I.amalgam.card ↪o Fin (I.tower j).card
  | 0 => RelEmbedding.refl _
  | j + 1 => (towerEmbed j).trans (Fin.castAddOrderEmb ((I.tower j).catalogue (j + 1)).card)

/-- At the grade `0` the old cells are the cells of the amalgam. -/
@[simp] theorem towerEmbed_zero (d : Fin I.amalgam.card) : I.towerEmbed 0 d = d := rfl

/-- At each layer the old cells are carried along `Fin.castAdd`. -/
@[simp] theorem towerEmbed_succ (j : ℕ) (d : Fin I.amalgam.card) :
    I.towerEmbed (j + 1) d =
      Fin.castAdd ((I.tower j).catalogue (j + 1)).card (I.towerEmbed j d) := rfl

/-- **The old cells form a lower embedding** of the amalgam into the scheme reached after the
grade `j`. -/
theorem isLowerEmbedding_tower : (j : ℕ) →
    I.amalgam.toCellScheme.IsLowerEmbedding (I.tower j).toCellScheme (I.towerEmbed j)
  | 0 => IsLowerEmbedding.id _
  | j + 1 => (Scheme.isLowerEmbedding_fieldLayer (I.tower j) (j + 1)
      (I.not_univ_succ_le_tower j)).comp (isLowerEmbedding_tower j)

/-- The old cells keep their scopes. -/
@[simp] theorem scope_towerEmbed : (j : ℕ) → (d : Fin I.amalgam.card) →
    (I.tower j).toCellScheme.scope (I.towerEmbed j d) = I.amalgam.toCellScheme.scope d
  | 0, _ => rfl
  | j + 1, d => (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans (scope_towerEmbed j d)

/-- The old cells keep their grades. -/
@[simp] theorem grade_towerEmbed (j : ℕ) (d : Fin I.amalgam.card) :
    (I.tower j).toCellScheme.grade (I.towerEmbed j d) = I.amalgam.toCellScheme.grade d :=
  (I.isLowerEmbedding_tower j).grade_eq d

/-- The old cells keep their graded indices. -/
@[simp] theorem gradedIndex_towerEmbed (j : ℕ) (d : Fin I.amalgam.card) :
    (I.tower j).toCellScheme.gradedIndex (I.towerEmbed j d) =
      I.amalgam.toCellScheme.gradedIndex d :=
  Prod.ext (I.scope_towerEmbed j d) (I.grade_towerEmbed j d)

/-- **Every cell of scope other than the ground set is old.** -/
theorem mem_range_towerEmbed : (j : ℕ) → (z : Fin (I.tower j).card) →
    (I.tower j).toCellScheme.scope z ≠ univ → z ∈ Set.range (I.towerEmbed j)
  | 0, z, _ => ⟨z, rfl⟩
  | j + 1, z, hz => by
    -- `I.tower (j + 1)` is the field layer of `I.tower j` (`Seed.tower_succ`, by `rfl`); `rw` does
    -- not apply under the dependent card, so the type is restated by `change`.
    change Fin ((I.tower j).fieldLayer (j + 1) (I.not_univ_succ_le_tower j)).card at z
    induction z using Fin.addCases with
    | left z =>
      obtain ⟨d, rfl⟩ := mem_range_towerEmbed j z
        ((Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).symm.trans_ne hz)
      exact ⟨d, rfl⟩
    | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz

/-- The faces of every scheme of the tower are those of the amalgam. -/
theorem faces_tower : (j : ℕ) → (I.tower j).toCellScheme.faces = I.amalgam.toCellScheme.faces
  | 0 => rfl
  | j + 1 => faces_tower j

/-- **The amalgam is a source prefix of every scheme of the tower** at every pair whose face is not
the ground set. -/
theorem isSourcePrefix_tower {j : ℕ} {Y : Finset (Fin (m + 2)) × ℕ} (hY : Y.1 ≠ univ) :
    I.amalgam.toCellScheme.IsSourcePrefix (I.tower j).toCellScheme (I.towerEmbed j) Y :=
  ⟨I.isLowerEmbedding_tower j, I.scope_towerEmbed j, fun d hd ↦ I.mem_range_towerEmbed j d
    fun he ↦ hY (univ_subset_iff.mp (he ▸ (hd.1 : (I.tower j).toCellScheme.scope d ⊆ Y.1)))⟩

/-- **Each scheme of the tower is a source prefix of the next** at every pair of grade at most
the grade of the scheme. -/
theorem isSourcePrefix_tower_succ {j j' : ℕ} (hj' : j' ≤ j) :
    (I.tower j).toCellScheme.IsSourcePrefix (I.tower (j + 1)).toCellScheme
      (Fin.castAdd ((I.tower j).catalogue (j + 1)).card) (univ, j') :=
  Scheme.isSourcePrefix_fieldLayer _ _ (I.not_univ_succ_le_tower j) fun h ↦
    absurd h.2 (by simp only; omega)

/-- **The rows of every scheme of the tower pull back to those of the amalgam** along the old
cells. -/
theorem comap_rows_tower : (j : ℕ) →
    (I.tower j).rows.comap (I.isLowerEmbedding_tower j) = I.amalgam.rows
  | 0 => rfl
  | j + 1 => by
    -- `I.tower (j + 1)` is the field layer of `I.tower j` (`Seed.tower_succ`, by `rfl`).
    change (((I.tower j).fieldLayer (j + 1) (I.not_univ_succ_le_tower j)).rows.comap
      (Scheme.isLowerEmbedding_fieldLayer _ _ _)).comap (I.isLowerEmbedding_tower j) = _
    rw [Scheme.comap_rows_fieldLayer, comap_rows_tower j]

/-- **The rows of the next scheme pull back to those of the scheme reached before**, along the
cells of the layers below. -/
theorem comap_rows_tower_succ (j : ℕ) :
    (I.tower (j + 1)).rows.comap (Scheme.isLowerEmbedding_fieldLayer (I.tower j) (j + 1)
      (I.not_univ_succ_le_tower j)) = (I.tower j).rows :=
  Scheme.comap_rows_fieldLayer (hS := I.not_univ_succ_le_tower j)

/-- **Lawfulness below a pair whose face is not the ground set** is lawfulness in the amalgam, on
the old cells. -/
theorem isLawfulBelow_tower_iff {j : ℕ} {X : Finset (Fin (m + 2)) × ℕ} (hX : X.1 ≠ univ)
    {g : Fin (I.tower j).card → Label.{u}} :
    (I.tower j).rows.IsLawfulBelow X (fun x ↦ g x) ↔
      I.amalgam.rows.IsLawfulBelow X (fun d ↦ g (I.towerEmbed j d)) := by
  have h := I.isSourcePrefix_tower (j := j) hX
  have hc : (I.tower j).rows.comap h.isLowerEmbedding = I.amalgam.rows := I.comap_rows_tower j
  rw [← h.isLawfulBelow_iff le_rfl, hc]
  rfl

/-- **Lifts below a pair whose face is not the ground set** are those of the amalgam. -/
theorem cappedLift_tower_iff {j : ℕ} {X Y : Finset (Fin (m + 2)) × ℕ} (hXY : X ≤ Y)
    (hY : Y.1 ≠ univ) : (I.tower j).rows.CappedLift hXY ↔ I.amalgam.rows.CappedLift hXY := by
  have h := I.isSourcePrefix_tower (j := j) hY
  have hc : (I.tower j).rows.comap h.isLowerEmbedding = I.amalgam.rows := I.comap_rows_tower j
  rw [← h.cappedLift_iff hXY le_rfl, hc]

/-- **Lifts carried to the next scheme**: between pairs of grade at most `j`, a capped lift of the
scheme reached after the grade `j` is a capped lift of the next one. -/
theorem cappedLift_tower_succ {j j' : ℕ} (hj' : j' ≤ j) {X : Finset (Fin (m + 2)) × ℕ}
    {hX : X ≤ (univ, j')} (hl : (I.tower j).rows.CappedLift hX) :
    (I.tower (j + 1)).rows.CappedLift hX := by
  have h := I.isSourcePrefix_tower_succ hj'
  have hc : (I.tower (j + 1)).rows.comap h.isLowerEmbedding = (I.tower j).rows :=
    I.comap_rows_tower_succ j
  rw [← h.cappedLift_iff hX le_rfl, hc]
  exact hl

/-! ### Structural laws -/

/-- Every scheme of the tower up to the grade `m + 2` is well formed. -/
theorem isWellFormed_tower : (j : ℕ) → j ≤ m + 2 → (I.tower j).IsWellFormed
  | 0, _ => I.amalgam.isWellFormed
  | j + 1, hj => Scheme.isWellFormed_fieldLayer (hS := I.not_univ_succ_le_tower j)
      (isWellFormed_tower j (by omega)) (Nat.succ_pos j) hj

/-- Every scheme of the tower is consistent. -/
theorem isConsistent_tower : (j : ℕ) → (I.tower j).rows.IsConsistent
  | 0 => I.isConsistent
  | j + 1 => Scheme.isConsistent_fieldLayer (hS := I.not_univ_succ_le_tower j)
      (isConsistent_tower j)

/-- Every scheme of the tower is coded. -/
theorem isCoded_tower : (j : ℕ) → (I.tower j).IsCoded
  | 0 => I.amalgam.isCoded
  | j + 1 => Scheme.isCoded_fieldLayer (hS := I.not_univ_succ_le_tower j) (isCoded_tower j)

/-- Up to the grade `m + 1`, every cell of the tower has grade below `m + 2`. -/
theorem grade_tower_lt {j : ℕ} (hj : j ≤ m + 1) (d : Fin (I.tower j).card) :
    (I.tower j).toCellScheme.grade d < m + 2 := by
  rcases I.tower_grade_le_or j d with h | h
  · omega
  · obtain ⟨e, rfl⟩ := I.mem_range_towerEmbed j d h
    rw [grade_towerEmbed]
    exact I.grade_lt e

/-- **The graded faces off the ground set carry old cells**: every graded face of the amalgam of
scope other than the ground set is the graded index of an old cell of every scheme of the tower. -/
theorem exists_gradedIndex_eq_tower (j : ℕ) {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ I.amalgam.toCellScheme.gradedFaces) (hne : X.1 ≠ univ) :
    ∃ d, (I.tower j).toCellScheme.gradedIndex d = X := by
  obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq X hX hne
  exact ⟨I.towerEmbed j d, (I.gradedIndex_towerEmbed j d).trans hd⟩

/-- **The new layer has a cell at `(univ, j + 1)`**: the cell of the orbit code of the bottom
labelling. -/
theorem exists_gradedIndex_eq_univ_tower (j : ℕ) :
    ∃ t, (I.tower (j + 1)).toCellScheme.gradedIndex t = (univ, j + 1) := by
  obtain ⟨i, -⟩ := Scheme.exists_catalogueEntry_eq (Scheme.orbitCode_splice_bot_mem_catalogue
    (S := I.tower j) (k := j + 1) (p := fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _))
  exact ⟨Fin.natAdd _ i, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i⟩

/-- An old cell of grade at most `j` lies below `(univ, j)`. -/
theorem towerEmbed_mem_below {j : ℕ} {d : Fin I.amalgam.card}
    (hd : I.amalgam.toCellScheme.grade d ≤ j) :
    I.towerEmbed j d ∈ (I.tower j).toCellScheme.below (univ, j) :=
  ⟨subset_univ _, (I.grade_towerEmbed j d).trans_le hd⟩

/-! ### Extension at the cap `⊥` through the tower -/

/-- **A lawful section of the amalgam extends through the tower**: unchanged at the old cells, to a
lawful section of every scheme of the tower (`Scheme.exists_isLawful_fieldLayer` at each layer).
It keeps every old label literally, the labels `⊤` and those above the grade of the layer
included. -/
theorem exists_isLawful_tower : (j : ℕ) → {p : Fin I.amalgam.card → Label.{u}} →
    I.amalgam.rows.IsLawful p →
    ∃ r, (I.tower j).rows.IsLawful r ∧ ∀ d, r (I.towerEmbed j d) = p d
  | 0, _, hp => ⟨_, hp, fun _ ↦ rfl⟩
  | j + 1, _, hp => by
    obtain ⟨r, hr, hrp⟩ := exists_isLawful_tower j hp
    obtain ⟨r', hr', hr'p⟩ := Scheme.exists_isLawful_fieldLayer (S := I.tower j) (k := j + 1)
      (hS := I.not_univ_succ_le_tower j) hr
    exact ⟨r', hr', fun d ↦ (hr'p _).trans (hrp d)⟩

/-- A face omitting a point is not the ground set. -/
theorem ne_univ_erase (x : Fin (m + 2)) : univ.erase x ≠ univ :=
  (erase_ssubset (mem_univ x)).ne

/-- An old cell lies below a pair exactly when the cell of the amalgam does. -/
theorem towerEmbed_mem_below_iff {j : ℕ} {X : Finset (Fin (m + 2)) × ℕ}
    {d : Fin I.amalgam.card} :
    I.towerEmbed j d ∈ (I.tower j).toCellScheme.below X ↔ d ∈ I.amalgam.toCellScheme.below X := by
  rw [CellScheme.mem_below, CellScheme.mem_below, gradedIndex_towerEmbed]

/-- **Extension at the cap `⊥` through the tower.**  Let `univ.erase x` and `univ.erase y` be two
faces such that the scope of every cell of the amalgam lies in one of them.  A labelling of the
amalgam lawful below `(univ.erase x, j)` and `(univ.erase y, j)` extends, unchanged at the old
cells of grade at most `j`, to a labelling lawful below `(univ, j)` in the scheme reached after the
grade `j`.  At each layer `ℓ ≤ j`, the extension below `(univ, ℓ - 1)` and the old cells of grade
`ℓ` are glued over `(univ, ℓ - 1)`, `(univ.erase x, ℓ)` and `(univ.erase y, ℓ)`
(`CellScheme.Rows.IsLawfulBelow.glue₃`), and the result is extended through the new cells
(`Scheme.exists_isLawfulBelow_fieldLayer`: the orbit code read by the orbit decoder at the least
grid point, the natural strip kept).  No ambient enters, so no lift across the other coatom is
used. -/
theorem exists_isLawfulBelow_tower {x y : Fin (m + 2)}
    (hcov : ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase x ∨
      I.amalgam.toCellScheme.scope d ⊆ univ.erase y) (j : ℕ) {w : Fin I.amalgam.card → Label.{u}}
    (hwx : I.amalgam.rows.IsLawfulBelow (univ.erase x, j) fun d ↦ w d)
    (hwy : I.amalgam.rows.IsLawfulBelow (univ.erase y, j) fun d ↦ w d) :
    ∃ r : (I.tower j).toCellScheme.below (univ, j) → Label.{u},
      (I.tower j).rows.IsLawfulBelow (univ, j) r ∧
      ∀ d (hd : I.amalgam.toCellScheme.grade d ≤ j),
        r ⟨I.towerEmbed j d, I.towerEmbed_mem_below hd⟩ = w d := by
  classical
  induction j generalizing w with
  | zero =>
    refine ⟨fun _ ↦ ⊥, Rows.isLawfulBelow_const_bot _, fun d hd ↦ absurd hd ?_⟩
    have := I.amalgam.isWellFormed.isWellFormed.grade_pos d
    omega
  | succ j ih =>
    obtain ⟨r₀, hr₀, hr₀w⟩ := ih (hwx.mono (X := (univ.erase x, j)) ⟨subset_rfl, Nat.le_succ j⟩)
      (hwy.mono (X := (univ.erase y, j)) ⟨subset_rfl, Nat.le_succ j⟩)
    -- The extension below `(univ, j)`, with the old cells of grade `j + 1` read from `w`.
    obtain ⟨g, hgr, hgw⟩ : ∃ g : Fin (I.tower j).card → Label.{u},
        (∀ e (he : e ∈ (I.tower j).toCellScheme.below (univ, j)), g e = r₀ ⟨e, he⟩) ∧
        ∀ d, g (I.towerEmbed j d) = w d := by
      refine ⟨fun e ↦ if he : e ∈ (I.tower j).toCellScheme.below (univ, j) then r₀ ⟨e, he⟩
        else Function.extend (I.towerEmbed j) w (fun _ ↦ ⊥) e, fun e he ↦ dite_eq_left he,
        fun d ↦ ?_⟩
      by_cases hd : I.amalgam.toCellScheme.grade d ≤ j
      · exact (dite_eq_left (I.towerEmbed_mem_below hd)).trans (hr₀w d hd)
      · exact (dite_eq_right fun h ↦ hd ((I.grade_towerEmbed j d).symm.trans_le h.2)).trans
          ((I.towerEmbed j).injective.extend_apply _ _ _)
    have hgx : (I.tower j).rows.IsLawfulBelow (univ.erase x, j + 1) fun e ↦ g e := by
      rw [I.isLawfulBelow_tower_iff (ne_univ_erase x)]
      simpa only [hgw] using hwx
    have hgy : (I.tower j).rows.IsLawfulBelow (univ.erase y, j + 1) fun e ↦ g e := by
      rw [I.isLawfulBelow_tower_iff (ne_univ_erase y)]
      simpa only [hgw] using hwy
    have hgj : (I.tower j).rows.IsLawfulBelow (univ, j) fun e ↦ g e := by
      convert hr₀ using 1
      exact funext fun e ↦ hgr e e.2
    have hg : (I.tower j).rows.IsLawfulBelow (univ, j + 1) fun e ↦ g e := by
      refine Rows.IsLawfulBelow.glue₃ hgx hgj hgy fun e he ↦ ?_
      by_cases hej : (I.tower j).toCellScheme.grade e ≤ j
      · exact .inr (.inl ⟨subset_univ _, hej⟩)
      · obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed j e ((I.tower_grade_le_or j e).resolve_left hej)
        have hd : I.amalgam.toCellScheme.grade d ≤ j + 1 :=
          (I.grade_towerEmbed j d).symm.trans_le he.2
        rcases hcov d with h | h
        · exact .inl (I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩)
        · exact .inr (.inr (I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩))
    obtain ⟨r, hr, hrg⟩ := Scheme.exists_isLawfulBelow_fieldLayer (S := I.tower j) (k := j + 1)
      (hS := I.not_univ_succ_le_tower j) (p := g) hg
    exact ⟨r, hr, fun d hd ↦ (hrg (I.towerEmbed j d) ((I.grade_towerEmbed j d).trans_le hd)).trans
      (hgw d)⟩

/-- **A labelling lawful below both coatoms at the grade `2` agrees with a labelling of `T 1`
whose orbit code is a catalogue entry**: if `w` is lawful below `(univ.erase x, 2)` for both
points `x` omitted by the coatoms, then some labelling `t` of the cells of `T 1` has its orbit code
at `2` in the catalogue of the layer at the grade `2`, and `t` equals `w` at the old cells of grade
at most `2`. -/
theorem exists_orbitCode_mem_catalogue_two {w : Fin I.amalgam.card → Label.{u}}
    (hwC : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (m + 1)), 2) fun d ↦ w d)
    (hwD : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last m)), 2)
      fun d ↦ w d) :
    ∃ t : Fin (I.tower 1).card → Label.{u}, orbitCode 2 t ∈ (I.tower 1).catalogue 2 ∧
      ∀ d, I.amalgam.toCellScheme.grade d ≤ 2 → t (I.towerEmbed 1 d) = w d := by
  -- `t` is the extension of `w` through `T 1` (`Seed.exists_isLawfulBelow_tower`), glued with the
  -- old cells of grade `2` and spliced with `⊥` above the grade `2`.
  classical
  have hcov (d : Fin I.amalgam.card) :
      I.amalgam.toCellScheme.scope d ⊆ univ.erase (Fin.last (m + 1)) ∨
        I.amalgam.toCellScheme.scope d ⊆ univ.erase (Fin.castSucc (Fin.last m)) :=
    I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem d) (I.scope_ne_univ d)
  have hwC1 : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (m + 1)), 1) fun d ↦ w d :=
    hwC.mono (X := (univ.erase (Fin.last (m + 1)), 1)) ⟨subset_rfl, by omega⟩
  have hwD1 : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last m)), 1)
      fun d ↦ w d :=
    hwD.mono (X := (univ.erase (Fin.castSucc (Fin.last m)), 1)) ⟨subset_rfl, by omega⟩
  obtain ⟨r₁, hr₁, hr₁w⟩ := I.exists_isLawfulBelow_tower (w := w) hcov 1 hwC1 hwD1
  set W : Fin (I.tower 1).card → Label.{u} := Function.extend (I.towerEmbed 1) w (fun _ ↦ ⊥)
  have hWe (d : Fin I.amalgam.card) : W (I.towerEmbed 1 d) = w d :=
    (I.towerEmbed 1).injective.extend_apply _ _ _
  set g : Fin (I.tower 1).card → Label.{u} := fun e ↦
    if he : e ∈ (I.tower 1).toCellScheme.below (univ, 1) then r₁ ⟨e, he⟩ else W e
  have hgold (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 2) :
      g (I.towerEmbed 1 d) = w d := by
    by_cases he : I.towerEmbed 1 d ∈ (I.tower 1).toCellScheme.below (univ, 1)
    · simp only [g, dite_eq_left he]
      exact hr₁w d (I.towerEmbed_mem_below_iff.mp he).2
    · simp only [g, dite_eq_right he]
      exact hWe d
  have hgb (e : Fin (I.tower 1).card)
      (he : e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.last (m + 1)), 2) ∨
        e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last m)), 2)) :
      g e = W e := by
    have hsc : (I.tower 1).toCellScheme.scope e ≠ univ := fun hu ↦ he.elim
      (fun h' ↦ ne_univ_erase _ (univ_subset_iff.mp (hu.ge.trans h'.1)))
      fun h' ↦ ne_univ_erase _ (univ_subset_iff.mp (hu.ge.trans h'.1))
    obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed 1 e hsc
    have hd : I.amalgam.toCellScheme.grade d ≤ 2 :=
      he.elim (fun h ↦ (I.towerEmbed_mem_below_iff.mp h).2)
        fun h ↦ (I.towerEmbed_mem_below_iff.mp h).2
    rw [hgold d hd, hWe]
  have hold (d : Fin I.amalgam.card)
      (he : I.towerEmbed 1 d ∈ (I.tower 1).toCellScheme.below (univ, 2)) :
      I.towerEmbed 1 d ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.last (m + 1)), 2) ∨
        I.towerEmbed 1 d ∈ (I.tower 1).toCellScheme.below (univ, 1) ∨
        I.towerEmbed 1 d ∈
          (I.tower 1).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last m)), 2) := by
    have hd : I.amalgam.toCellScheme.grade d ≤ 2 := (I.towerEmbed_mem_below_iff.mp he).2
    rcases hcov d with h | h
    · exact .inl (I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩)
    · exact .inr (.inr (I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩))
  have hglaw : (I.tower 1).rows.IsLawfulBelow (univ, 2) fun e ↦ g e := by
    refine Rows.IsLawfulBelow.glue₃ (U := (univ.erase (Fin.last (m + 1)), 2)) (V := (univ, 1))
      (W := (univ.erase (Fin.castSucc (Fin.last m)), 2)) ?_ ?_ ?_ ?_
    · have : (I.tower 1).rows.IsLawfulBelow (univ.erase (Fin.last (m + 1)), 2) fun e ↦ W e := by
        rw [I.isLawfulBelow_tower_iff (ne_univ_erase _)]
        simpa only [hWe] using hwC
      convert this using 1
      exact funext fun e ↦ hgb e (.inl e.2)
    · convert hr₁ using 1
      exact funext fun e ↦ by simp only [g, dite_eq_left e.2]
    · have : (I.tower 1).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last m)), 2)
          fun e ↦ W e := by
        rw [I.isLawfulBelow_tower_iff (ne_univ_erase _)]
        simpa only [hWe] using hwD
      convert this using 1
      exact funext fun e ↦ hgb e (.inr e.2)
    · intro e he
      rcases I.tower_grade_le_or 1 e with h1 | hsc
      · by_cases hsu : (I.tower 1).toCellScheme.scope e = univ
        · exact .inr (.inl ⟨hsu ▸ subset_rfl, h1⟩)
        · obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed 1 e hsu
          exact hold d he
      · obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed 1 e hsc
        exact hold d he
  refine ⟨(I.tower 1).toCellScheme.splice 2 (fun _ ↦ ⊥) g,
    Scheme.orbitCode_splice_bot_mem_catalogue (S := I.tower 1) (k := 2) (p := g) hglaw,
    fun d hd ↦ ?_⟩
  rw [CellScheme.splice_of_le (by rw [Seed.grade_towerEmbed]; exact hd), hgold d hd]

/-! ### The two coatoms and the common face -/

/-- The two points omitted by the coatoms are distinct. -/
theorem last_ne_castSucc : (Fin.last (m + 1) : Fin (m + 2)) ≠ Fin.castSucc (Fin.last m) :=
  (Fin.castSucc_lt_last _).ne'

/-- Two distinct points omitted by the coatoms are the two points, in some order. -/
theorem pair_cases {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) :
    (x = Fin.last (m + 1) ∧ y = Fin.castSucc (Fin.last m)) ∨
      (x = Fin.castSucc (Fin.last m) ∧ y = Fin.last (m + 1)) := by
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩
  · exact absurd rfl hxy

/-- Each point omitted by a coatom has another one. -/
theorem exists_other {x : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2)))) :
    ∃ y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))), x ≠ y := by
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨_, mem_insert_of_mem (mem_singleton_self _), last_ne_castSucc⟩
  · exact ⟨_, mem_insert_self _ _, last_ne_castSucc.symm⟩

/-- **The common face of the two coatoms is a face of the amalgam**: it is the face of the first
coatom type along `Fin.castSuccEmb`, and that type is the face of the amalgam along
`Fin.castSuccEmb`. -/
theorem commonFace_mem_faces : (univ.erase (Fin.last (m + 1))).erase (Fin.castSucc (Fin.last m)) ∈
    I.amalgam.toCellScheme.faces := by
  have h := (StageType.restrictFace_trans _ _ _ I.restrictFace_left).symm.trans
    I.restrictFace_face_left
  have hmem := (StageType.isSome_restrictFace_iff _ _).mp (by rw [h]; rfl)
  convert hmem using 1
  ext z
  simp only [mem_erase, mem_univ, and_true, mem_map, true_and, Function.Embedding.trans_apply,
    Fin.castSuccEmb_apply, ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨z, by omega⟩, rfl⟩
  · rintro ⟨a, ha⟩
    have := a.isLt
    omega

/-- The common face of two coatoms, in either order. -/
private theorem erase_inter_erase {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) :
    univ.erase x ∩ univ.erase y =
      (univ.erase (Fin.last (m + 1))).erase (Fin.castSucc (Fin.last m)) := by
  rcases pair_cases hx hy hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · ext z
    simp only [mem_inter, mem_erase, mem_univ, and_true]
    exact and_comm
  · ext z
    simp only [mem_inter, mem_erase, mem_univ, and_true]

/-- A coatom is a face of the amalgam. -/
theorem erase_mem_faces {x : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2)))) :
    univ.erase x ∈ I.amalgam.toCellScheme.faces := by
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  exacts [I.erase_last_mem_faces, I.erase_castSucc_mem_faces]

/-- A coatom has `m + 1` points. -/
theorem card_erase (x : Fin (m + 2)) : #(univ.erase x) = m + 1 := by
  rw [card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin]
  rfl

/-- The common face has `m` points. -/
private theorem card_erase_inter_erase {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) : #(univ.erase x ∩ univ.erase y) = m := by
  rw [erase_inter_erase hx hy hxy, card_erase_of_mem (mem_erase.mpr ⟨last_ne_castSucc.symm,
    mem_univ _⟩), card_erase]
  rfl

/-- Every cell of the amalgam lies on one of the two coatoms. -/
theorem scope_subset_or {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) (d : Fin I.amalgam.card) :
    I.amalgam.toCellScheme.scope d ⊆ univ.erase x ∨
      I.amalgam.toCellScheme.scope d ⊆ univ.erase y := by
  have h := I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem d)
    (I.scope_ne_univ d)
  rcases pair_cases hx hy hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [h, h.symm]

/-- **The lift from the common face to the other coatom**, a lift of the amalgam: from
`(univ.erase x ∩ univ.erase y, min j m)` to `(univ.erase y, j)` in every scheme of the tower up
to the grade `m + 1`, through the source prefix and the bountifulness of the amalgam; below the
empty face, or at the grade `0`, there are no cells. -/
theorem cappedLift_commonFace_tower {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) {j : ℕ} (hj : j ≤ m + 1) :
    (I.tower j).rows.CappedLift (X := (univ.erase x ∩ univ.erase y, min j m))
      (Y := (univ.erase y, j)) ⟨inter_subset_right, min_le_left _ _⟩ := by
  by_cases h0 : min j m = 0
  · exact (I.isWellFormed_tower j (by omega)).isWellFormed.cappedLift _ (Or.inl h0) _
  refine (I.cappedLift_tower_iff _ (ne_univ_erase y)).mpr (I.isBountiful ⟨?_, ?_, ?_⟩
    ⟨I.erase_mem_faces hy, ?_, ?_⟩ _)
  · rw [erase_inter_erase hx hy hxy]
    exact I.commonFace_mem_faces
  · exact Nat.pos_of_ne_zero h0
  · exact (min_le_right _ _).trans (card_erase_inter_erase hx hy hxy).ge
  · -- The grade of the coatom pair.
    change 0 < j
    omega
  · simp only [card_erase]
    exact hj

/-- **Extension at the cap `⊥` from the two coatoms**: in every scheme of the tower, a labelling
lawful below the two coatoms at the grade `j` extends, unchanged on them, to one lawful below
`(univ, j)` (`Seed.exists_isLawfulBelow_tower`). -/
theorem extendsFromBoundary_bot_tower {x y : Fin (m + 2)}
    (hcov : ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase x ∨
      I.amalgam.toCellScheme.scope d ⊆ univ.erase y) (j : ℕ) :
    (I.tower j).rows.ExtendsFromBoundary (univ.erase x, j) (univ.erase y, j) (univ, j) ⊥
      fun _ ↦ ⊥ := by
  intro w hwx hwy _
  obtain ⟨r, hr, hrw⟩ := I.exists_isLawfulBelow_tower hcov j (w := fun d ↦ w (I.towerEmbed j d))
    ((I.isLawfulBelow_tower_iff (g := w) (ne_univ_erase x)).mp hwx)
    ((I.isLawfulBelow_tower_iff (g := w) (ne_univ_erase y)).mp hwy)
  refine ⟨r, hr, fun d hd ↦ ?_, fun _ ↦ by simp⟩
  obtain ⟨d, hdj⟩ := d
  have hsc : (I.tower j).toCellScheme.scope d ≠ univ := fun he ↦ hd.elim
    (fun h ↦ ne_univ_erase x (univ_subset_iff.mp (he.ge.trans h.1)))
    fun h ↦ ne_univ_erase y (univ_subset_iff.mp (he.ge.trans h.1))
  obtain ⟨e, rfl⟩ := I.mem_range_towerEmbed j d hsc
  exact hrw e ((I.grade_towerEmbed j e).symm.trans_le hdj.2)

/-- **The cells below both coatoms lie below the common face**: at every grade `i`, in every scheme
of the tower up to the grade `m + 2`, a cell below `(univ.erase x, i)` and `(univ.erase y, i)` lies
below the common face at the grade `min i m`, its grade being at most the size of its scope. -/
theorem mem_below_commonFace_tower {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) {k i : ℕ} (hk : k ≤ m + 2) (d : Fin (I.tower k).card)
    (hdx : d ∈ (I.tower k).toCellScheme.below (univ.erase x, i))
    (hdy : d ∈ (I.tower k).toCellScheme.below (univ.erase y, i)) :
    d ∈ (I.tower k).toCellScheme.below (univ.erase x ∩ univ.erase y, min i m) := by
  have hsub := subset_inter hdx.1 hdy.1
  exact ⟨hsub, le_min hdx.2 (((I.isWellFormed_tower k hk).isWellFormed.grade_le_card d).trans
    ((card_le_card hsub).trans (card_erase_inter_erase hx hy hxy).le))⟩

/-- **The rows of the new cells are short and never `⊤`**: the row of a cell of graded index
`(univ, j + 1)` in the scheme reached after the grade `j + 1` is the field row of its catalogue
entry, short at `j + 1` (`Scheme.isShort_ne_top_row_fieldLayer`). -/
theorem isShort_ne_top_rowBelow_tower {j : ℕ} {u : Fin (I.tower (j + 1)).card}
    (hu : (I.tower (j + 1)).toCellScheme.gradedIndex u = (univ, j + 1))
    (d : (I.tower (j + 1)).toCellScheme.below (univ, j + 1)) :
    IsShort (j + 1) ((I.tower (j + 1)).rows.rowBelow u hu d) ∧
      (I.tower (j + 1)).rows.rowBelow u hu d ≠ ⊤ := by
  obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq (S := I.tower j) (k := j + 1)
    (hS := I.not_univ_succ_le_tower j) hu
  exact Scheme.isShort_ne_top_row_fieldLayer (hS := I.not_univ_succ_le_tower j) i _

/-- **The cover of `(univ, j + 1)`**: in the scheme reached after the grade `j`, every cell below
`(univ, j + 1)` lies below one of the coatoms at the grade `j + 1` or below `(univ, j)`: the new
cells have grade at most `j`, and every old cell lies on a coatom. -/
theorem mem_below_cover_tower {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) {j : ℕ} (e : Fin (I.tower j).card)
    (he : e ∈ (I.tower j).toCellScheme.below (univ, j + 1)) :
    e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
      e ∈ (I.tower j).toCellScheme.below (univ, j) ∨
        e ∈ (I.tower j).toCellScheme.below (univ.erase y, j + 1) := by
  by_cases hej : (I.tower j).toCellScheme.grade e ≤ j
  · exact .inr (.inl ⟨subset_univ _, hej⟩)
  · obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed j e ((I.tower_grade_le_or j e).resolve_left hej)
    have hd : I.amalgam.toCellScheme.grade d ≤ j + 1 :=
      (I.grade_towerEmbed j d).symm.trans_le he.2
    rcases I.scope_subset_or hx hy hxy d with h | h
    · exact .inl (I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩)
    · exact .inr (.inr (I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩))

/-! ### The invariant -/

/-- The **lifting invariant** of the tower at the grade `j`: for both coatoms `univ.erase x` and
every grade `j' ≤ j`, the scheme reached after the grade `j` lifts capped from
`(univ.erase x, j')` to `(univ, j')`, at every cap self-visible at `j'` and for every lawful
ambient.  The lift is unrestricted: the restoration of the lower prescriptions uses it at the
owner labels, and the step to the top grade `m + 1` uses it at caps that are short at `m + 1` but
not at `m`, along ambients that are not rows of cells. -/
def TowerInvariant (j : ℕ) : Prop :=
  ∀ x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))), ∀ j' ≤ j,
    (I.tower j).rows.CappedLift (X := (univ.erase x, j')) (Y := (univ, j'))
      ⟨erase_subset _ _, le_rfl⟩

/-- **The invariant at the grade `0`**: there are no cells of grade `0`. -/
theorem towerInvariant_zero : I.TowerInvariant 0 := by
  intro x _ j' hj'
  obtain rfl : j' = 0 := by omega
  exact (I.isWellFormed_tower 0 (by omega)).isWellFormed.cappedLift _ (Or.inl rfl) _

/-- **The lift at grade one: the amalgam boundary.**  For the coatoms `univ.erase x` and
`univ.erase y`, the one-grade lift `CellScheme.Rows.cappedLift_of_boundary` at `j = 0` applies to
the first layer, with `U = (univ.erase x, 1)`, `V = (univ.erase y, 1)` and `O` the common face at
the grade `min 1 m`: the lower lift is from a pair with no cells, the lift from `O` to `V` is a lift
of the amalgam (`Seed.cappedLift_commonFace_tower`), the boundary is every old cell of grade `1`,
and the field layer extends from it at `⊥` and at every positive cap, its old cells of grade at
most `1` all having grade `1`. -/
theorem cappedLift_tower_one {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) :
    (I.tower 1).rows.CappedLift (X := (univ.erase x, 1)) (Y := (univ, 1))
      ⟨erase_subset _ _, le_rfl⟩ := by
  have hwf := (I.isWellFormed_tower 1 (by omega)).isWellFormed
  have hnot (z : Fin (m + 2)) : ¬ ((univ : Finset (Fin (m + 2))), 1) ≤ (univ.erase z, 1) :=
    fun h ↦ ne_univ_erase z (univ_subset_iff.mp h.1)
  have hcover (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 1) :
      I.amalgam.toCellScheme.gradedIndex d ≤ (univ.erase x, 1) ∨
        I.amalgam.toCellScheme.gradedIndex d ≤ (univ.erase y, 1) :=
    (I.scope_subset_or hx hy hxy d).imp (fun h ↦ ⟨h, hd⟩) fun h ↦ ⟨h, hd⟩
  have hpos (d : Fin I.amalgam.card) : 1 ≤ I.amalgam.toCellScheme.grade d :=
    (I.amalgam.isWellFormed.isWellFormed.gradedIndex_mem d).2.1
  -- `I.tower 1` is the field layer of `I.tower 0` (`Seed.tower_succ`, by `rfl`).
  change ((I.tower 0).fieldLayer 1 (I.not_univ_succ_le_tower 0)).rows.CappedLift _
  refine Rows.cappedLift_of_boundary (C := univ.erase x) (B := univ) (j := 0)
    (U := (univ.erase x, 1)) (V := (univ.erase y, 1))
    (O := (univ.erase x ∩ univ.erase y, min 1 m)) (erase_subset _ _) ?_
    (hwf.cappedLift _ (Or.inl rfl) _) le_rfl ⟨inter_subset_left, min_le_left _ _⟩
    ⟨inter_subset_right, min_le_left _ _⟩ ⟨erase_subset _ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩
    (fun d hdU hdV ↦ I.mem_below_commonFace_tower hx hy hxy (k := 1) (by omega) d hdU hdV)
    (Rows.cappedLift_refl _) (I.cappedLift_commonFace_tower hx hy hxy (j := 1) (by omega))
    (Scheme.extendsFromBoundary_bot_fieldLayer (hnot x) (hnot y) hcover)
    (I.exists_gradedIndex_eq_univ_tower 0) fun u hu ↦
      ⟨Scheme.isConsistent_fieldLayer I.isConsistent u,
        fun d ↦ (I.isShort_ne_top_rowBelow_tower (j := 0) hu d).1,
        fun d ↦ (I.isShort_ne_top_rowBelow_tower (j := 0) hu d).2, fun h hh hbot ↦
        Scheme.extendsFromBoundary_fieldLayer (fun d hd ↦ le_antisymm hd (hpos d)) (hnot x)
          (hnot y) hcover hu hh hbot⟩
  exact I.exists_gradedIndex_eq_tower 1
    ⟨I.erase_mem_faces hx, one_pos, by rw [card_erase]; omega⟩ (ne_univ_erase x)

/-- **The invariant at the grade `1`**, at every arity: the amalgam boundary
(`Seed.cappedLift_tower_one`).  No lower layer is crossed at the grade `1`. -/
theorem towerInvariant_one : I.TowerInvariant 1 := by
  intro x hx j' hj'
  obtain ⟨y, hy, hxy⟩ := exists_other hx
  rcases (show j' = 0 ∨ j' = 1 by omega) with rfl | rfl
  · exact (I.isWellFormed_tower 1 (by omega)).isWellFormed.cappedLift _ (Or.inl rfl) _
  · exact I.cappedLift_tower_one hx hy hxy

/-! ### The lift from the union within the face -/

/-- **The lift from the union within the face.**  Let `E` have fewer than `j + 1` points.  Every
cell below `(E, j + 1)` then has grade at most `j`, so on the face `univ.erase y` the union of the
cells below `(E, j + 1)` and below `(univ.erase y, j)` lies below `(univ.erase y, j)`.  A labelling
lawful below `(univ.erase y, j)` that agrees there with `a`, lawful below `(univ.erase y, j + 1)`,
capped at a cap `h` self-visible at `j + 1`, extends, unchanged on that union, to one lawful below
`(univ.erase y, j + 1)` agreeing with `a` capped at `h`: the lift within the face from the grade
`j` to `j + 1` (`CellScheme.Rows.cappedLift_of_fst_eq`).  This is the case of the union fill that
holds for every seed (compare `VaughtConjecture.Extension.UnionFillCounterexample`, where the
common face carries a cell of the grade). -/
theorem exists_lift_union_of_lt_grade {y : Fin (m + 2)} {E : Finset (Fin (m + 2))} {j : ℕ}
    (hj : #E < j + 1) {h : Label.{u}} (hh : IsSelfVisible (j + 1) h)
    {a : Fin I.amalgam.card → Label.{u}}
    (ha : I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) (fun d ↦ a d))
    {w : Fin I.amalgam.card → Label.{u}}
    (hw : I.amalgam.rows.IsLawfulBelow (univ.erase y, j) (fun d ↦ w d))
    (hag : ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase y, j), min (w d) h = min (a d) h) :
    ∃ v : I.amalgam.toCellScheme.below (univ.erase y, j + 1) → Label.{u},
      I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) v ∧
      (∀ d : I.amalgam.toCellScheme.below (univ.erase y, j + 1),
        (d : Fin I.amalgam.card) ∈ I.amalgam.toCellScheme.below (E, j + 1) ∨
          (d : Fin I.amalgam.card) ∈ I.amalgam.toCellScheme.below (univ.erase y, j) →
            v d = w d) ∧
      ∀ d, min (v d) h = min (a d) h := by
  have hDD : ((univ.erase y, j) : Finset (Fin (m + 2)) × ℕ) ≤ (univ.erase y, j + 1) :=
    ⟨subset_rfl, Nat.le_succ j⟩
  obtain ⟨v, hv, hva, hvw⟩ := (Rows.cappedLift_iff_forall_exists hDD).mp
    (Rows.cappedLift_of_fst_eq hDD rfl) h hh (fun d ↦ w d) (fun d ↦ a d) hw ha
    fun d ↦ (hag d.1 d.2).symm
  refine ⟨v, hv, fun d hd ↦ ?_, hva⟩
  have hdD : (d : Fin I.amalgam.card) ∈ I.amalgam.toCellScheme.below (univ.erase y, j) := by
    refine hd.elim (fun hE ↦ ⟨d.2.1, ?_⟩) id
    have h1 := I.amalgam.isWellFormed.isWellFormed.grade_le_card d
    have h2 : #(I.amalgam.toCellScheme.scope d) ≤ #E := card_le_card hE.1
    -- The second component of the graded index is the grade.
    change I.amalgam.toCellScheme.grade d ≤ j
    omega
  exact hvw ⟨d, hdD⟩

/-- **The lift from the union within the face, from the grade `m` on**: the common face of the two
coatoms, on `m` points, carries no cell of a grade `j + 1 > m`, and the lift from the union of the
common face at the grade `j + 1` and the other coatom at the grade `j` is a lift within the other
coatom (`Seed.exists_lift_union_of_lt_grade`). -/
theorem exists_lift_union_of_le {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) {j : ℕ} (hj : m ≤ j) {h : Label.{u}} (hh : IsSelfVisible (j + 1) h)
    {a : Fin I.amalgam.card → Label.{u}}
    (ha : I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) (fun d ↦ a d))
    {w : Fin I.amalgam.card → Label.{u}}
    (hw : I.amalgam.rows.IsLawfulBelow (univ.erase y, j) (fun d ↦ w d))
    (hag : ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase y, j), min (w d) h = min (a d) h) :
    ∃ v : I.amalgam.toCellScheme.below (univ.erase y, j + 1) → Label.{u},
      I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) v ∧
      (∀ d : I.amalgam.toCellScheme.below (univ.erase y, j + 1),
        (d : Fin I.amalgam.card) ∈
            I.amalgam.toCellScheme.below (univ.erase x ∩ univ.erase y, j + 1) ∨
          (d : Fin I.amalgam.card) ∈ I.amalgam.toCellScheme.below (univ.erase y, j) →
            v d = w d) ∧
      ∀ d, min (v d) h = min (a d) h :=
  I.exists_lift_union_of_lt_grade (by rw [card_erase_inter_erase hx hy hxy]; omega) hh ha hw hag

/-! ### The two-face lift -/

/-- **The two-face lift `2FL(j)`** of the tower at the grade `j`: for every catalogue entry `a` of
the layer at the grade `j + 1` and every cap `h` self-visible and short at `j + 1` with `⊥ < h`,
every labelling `w` of the amalgam lawful below both coatoms at the grade `j + 1` that agrees with
`a` capped at `h` at the old cells of grade at most `j + 1` extends, unchanged at the old cells of
grade at most `j`, to a labelling lawful below `(univ, j)` in the scheme reached after the grade
`j` that agrees with `a` capped at `h` at every cell below `(univ, j)`.

It is the extension from the boundary that the step to the grade `j + 1` uses at the positive caps
(`Seed.extendsFromBoundary_tower_of_twoFaceLift`), read on the scheme before the layer, and
equivalent to that hypothesis of the step (`Seed.twoFaceLift_iff_extendsFromBoundary`):

* `a` ranges over the catalogue entries at the grade `j + 1`, not over all lawful labellings: the
  ambient at a positive cap is the row of a cell of the new layer, which reads its entry on the
  scheme before (`Scheme.fieldRow_castAdd`);
* `h` ranges over the caps self-visible and short at `j + 1` with `⊥ < h`, the source caps of the
  owner alignment; at the cap `⊥` no ambient enters, and the extension is
  `Seed.exists_isLawfulBelow_tower`.  The cap need not be short at the grades `1, …, j` of the
  layers below `(univ, j)`;
* `w` ranges over the labellings lawful below both coatoms at the grade `j + 1` that agree with `a`
  capped at `h`: in the step it is the aligned encoding of the prescription on one coatom glued
  with its lift into the other coatom, a lift of the amalgam.  The one-grade lift
  (`CellScheme.Rows.cappedLift_of_boundary_short`) asks for the extension along every row of the
  new layer, at every such cap, of every such labelling; the step itself meets only the rows of
  the new cells to which its owner alignments align, the source caps and the glued aligned
  encodings of those alignments.

Lawfulness of `w` at the grade `j + 1`, not only at `j`, is part of the hypothesis: the old cells of
the grade `j + 1` are not below `(univ, j)`, but they constrain `w` below it.

It is not the invariant at the grade `j + 1` in another form.  It concerns the scheme before the
layer at the grade `j + 1` and asserts nothing about the new cells of that grade; it prescribes both
coatoms at once, rather than lifting from one coatom with the other free; it is required only at
the caps short at `j + 1` and along catalogue entries, not at every self-visible cap and ambient;
and its labelling agrees with `a` only capped at `h`, with nothing asserted above `h` on the new
cells.  The invariant at `j + 1` follows from it together with the invariant at `j`, the
restoration of the lower prescriptions, the owner alignment, and the extension through the layer at
`j + 1` (`Seed.towerInvariant_succ`).  At the grade `j = 0`
it holds (`Seed.twoFaceLift_zero`); it is assumed by the step at the grades `2 ≤ j + 1 ≤ m`
(`Seed.towerInvariant_of_twoFaceLift`).  `2FL(1)` holds at every arity (`Seed.twoFaceLift_one`);
`2FL(2)` fails for a legal seed on five points (`TwoFaceLiftCounterexample.not_twoFaceLift_two`),
so for `j ≥ 2` it is a hypothesis on the seed, not a property of every seed. -/
def TwoFaceLift (j : ℕ) : Prop :=
  ∀ a ∈ (I.tower j).catalogue (j + 1),
  ∀ h : Label.{u}, IsSelfVisible (j + 1) h → IsShort (j + 1) h → ⊥ < h →
  ∀ w : Fin I.amalgam.card → Label.{u},
    I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (m + 1)), j + 1) (fun d ↦ w d) →
    I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last m)), j + 1)
      (fun d ↦ w d) →
    (∀ d, I.amalgam.toCellScheme.grade d ≤ j + 1 →
      min (w d) h = min (a (I.towerEmbed j d)) h) →
    ∃ r : (I.tower j).toCellScheme.below (univ, j) → Label.{u},
      (I.tower j).rows.IsLawfulBelow (univ, j) r ∧
      (∀ d (hd : I.amalgam.toCellScheme.grade d ≤ j),
        r ⟨I.towerEmbed j d, I.towerEmbed_mem_below hd⟩ = w d) ∧
      ∀ e, min (r e) h = min (a e) h

/-- **`2FL(0)` holds**: below `(univ, 0)` there are no cells. -/
theorem twoFaceLift_zero : I.TwoFaceLift 0 := by
  intro a _ h _ _ _ w _ _ _
  have hno (e : Fin (I.tower 0).card) : e ∉ (I.tower 0).toCellScheme.below (univ, 0) := by
    intro he
    have h1 := (I.isWellFormed_tower 0 (by omega)).isWellFormed.grade_pos e
    have h2 : (I.tower 0).toCellScheme.grade e ≤ 0 := he.2
    omega
  refine ⟨fun _ ↦ ⊥, Rows.isLawfulBelow_const_bot _, fun d hd ↦ ?_, fun e ↦ absurd e.2 (hno _)⟩
  have := I.amalgam.isWellFormed.isWellFormed.grade_pos d
  omega

/-! ### The step from the grade `j` to `j + 1` -/

/-- **Extension from the boundary through the new layer.**  Let `U` and `V` be pairs of grade at
most `j + 1` not above `(univ, j + 1)`, and `h` self-visible and short at `j + 1` with `⊥ < h`.
Suppose that in the scheme reached after the grade `j`, along every catalogue entry `a` at the grade
`j + 1`, every labelling lawful below `U` and `V` that agrees with `a` capped at `h` on their cells
is, on those cells, some labelling lawful below `(univ, j + 1)` that agrees with `a` capped at `h`
below `(univ, j + 1)`.  Then the rows of the scheme reached after the grade `j + 1` extend from the
boundary of `U` and `V` at `h` along the row of every new cell of the grade `j + 1`: restrict to
the scheme before, complete there, and extend through the new cells
(`Scheme.exists_extension_fieldLayer`, at a short cap, where the orbit code has relative room). -/
theorem extendsFromBoundary_tower_of_forall {j : ℕ} {U V : Finset (Fin (m + 2)) × ℕ}
    (hU : ¬ ((univ : Finset (Fin (m + 2))), j + 1) ≤ U)
    (hV : ¬ ((univ : Finset (Fin (m + 2))), j + 1) ≤ V) (hUj : U.2 ≤ j + 1) (hVj : V.2 ≤ j + 1)
    {h : Label.{u}} (hh : IsSelfVisible (j + 1) h) (hs : IsShort (j + 1) h) (hbot : ⊥ < h)
    (hfill : ∀ a ∈ (I.tower j).catalogue (j + 1), ∀ w : Fin (I.tower j).card → Label.{u},
      (I.tower j).rows.IsLawfulBelow U (fun e ↦ w e) →
      (I.tower j).rows.IsLawfulBelow V (fun e ↦ w e) →
      (∀ e, e ∈ (I.tower j).toCellScheme.below U ∨ e ∈ (I.tower j).toCellScheme.below V →
        min (w e) h = min (a e) h) →
      ∃ g : Fin (I.tower j).card → Label.{u},
        (I.tower j).rows.IsLawfulBelow (univ, j + 1) (fun e ↦ g e) ∧
        (∀ e, e ∈ (I.tower j).toCellScheme.below U ∨ e ∈ (I.tower j).toCellScheme.below V →
          g e = w e) ∧
        ∀ e ∈ (I.tower j).toCellScheme.below (univ, j + 1), min (g e) h = min (a e) h)
    {u : Fin (I.tower (j + 1)).card}
    (hu : (I.tower (j + 1)).toCellScheme.gradedIndex u = (univ, j + 1)) :
    (I.tower (j + 1)).rows.ExtendsFromBoundary U V (univ, j + 1) h
      ((I.tower (j + 1)).rows.rowBelow u hu) := by
  intro w hwU hwV hwS
  obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq (S := I.tower j) (k := j + 1)
    (hS := I.not_univ_succ_le_tower j) hu
  set a := (I.tower j).catalogueEntry (j + 1) i
  have ha := Scheme.catalogueEntry_mem (S := I.tower j) (k := j + 1) i
  have hrowBelow (d : (I.tower (j + 1)).toCellScheme.below (univ, j + 1)) :
      (I.tower (j + 1)).rows.rowBelow (Fin.natAdd _ i) hu d = (I.tower j).fieldRow (j + 1) a d.1 :=
    Scheme.fieldLayer_row_natAdd (hS := I.not_univ_succ_le_tower j) i _
  have hw₁U : (I.tower j).rows.IsLawfulBelow U fun e ↦ w (Fin.castAdd _ e) :=
    (Scheme.isLawfulBelow_appendFullCells_iff (S := I.tower j) (k := j + 1)
      (r := fun i ↦ (I.tower j).fieldRow (j + 1) ((I.tower j).catalogueEntry (j + 1) i))
      (h := I.not_univ_succ_le_tower j) (v := w) hU).mp hwU
  have hw₁V : (I.tower j).rows.IsLawfulBelow V fun e ↦ w (Fin.castAdd _ e) :=
    (Scheme.isLawfulBelow_appendFullCells_iff (S := I.tower j) (k := j + 1)
      (r := fun i ↦ (I.tower j).fieldRow (j + 1) ((I.tower j).catalogueEntry (j + 1) i))
      (h := I.not_univ_succ_le_tower j) (v := w) hV).mp hwV
  have hgi (e : Fin (I.tower j).card) :
      ((I.tower j).fieldLayer (j + 1) (I.not_univ_succ_le_tower j)).toCellScheme.gradedIndex
        (Fin.castAdd _ e) = (I.tower j).toCellScheme.gradedIndex e :=
    Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e
  -- An old cell lies below a pair in the field layer exactly when it does in the scheme before.
  have hmem {X : Finset (Fin (m + 2)) × ℕ} (e : Fin (I.tower j).card) :
      Fin.castAdd ((I.tower j).catalogue (j + 1)).card e ∈
          (I.tower (j + 1)).toCellScheme.below X ↔ e ∈ (I.tower j).toCellScheme.below X := by
    -- `I.tower (j + 1)` is the field layer of `I.tower j` (`Seed.tower_succ`, by `rfl`).
    change ((I.tower j).fieldLayer (j + 1)
      (I.not_univ_succ_le_tower j)).toCellScheme.gradedIndex (Fin.castAdd _ e) ≤ X ↔ _
    rw [hgi]
    rfl
  have hag (e : Fin (I.tower j).card)
      (he : e ∈ (I.tower j).toCellScheme.below U ∨ e ∈ (I.tower j).toCellScheme.below V) :
      min (w (Fin.castAdd _ e)) h = min (a e) h := by
    have hle : (I.tower j).toCellScheme.grade e ≤ j + 1 :=
      he.elim (fun h' ↦ h'.2.trans hUj) fun h' ↦ h'.2.trans hVj
    have := hwS ⟨_, Scheme.castAdd_mem_below (hS := I.not_univ_succ_le_tower j) hle⟩
      (he.imp (hmem e).mpr (hmem e).mpr)
    rwa [hrowBelow, Scheme.fieldRow_castAdd] at this
  obtain ⟨g, hg, hgw, hga⟩ := hfill a ha (fun e ↦ w (Fin.castAdd _ e)) hw₁U hw₁V hag
  obtain ⟨r, hr, hrg, hrS⟩ := Scheme.exists_extension_fieldLayer (S := I.tower j) (k := j + 1)
    (hS := I.not_univ_succ_le_tower j) (p := g) hg ha hh hbot (.inl hs)
    fun d hd ↦ hga d ⟨subset_univ _, hd⟩
  refine ⟨r, hr, fun d hd ↦ ?_, fun d ↦ by rw [hrowBelow]; exact hrS d⟩
  obtain ⟨e, he, rfl⟩ := Scheme.exists_castAdd_eq_of_boundary (S := I.tower j) (k := j + 1)
    (hS := I.not_univ_succ_le_tower j) hU hV hd
  rw [hrg e he]
  exact hgw e (hd.imp (hmem e).mp (hmem e).mp)

/-- **The boundary labelling at the top grade, completed on the scheme reached after the grade
`j`.**  Let `m ≤ j`, `C = univ.erase x` and `D = univ.erase y` the two coatoms, `w` a labelling of
the scheme reached after the grade `j` lawful below `(C, j + 1)` and `(univ, j)`, and `a` a lawful
section of it agreeing with `w` capped at `h` (self-visible at `j + 1`) on the cells below
`(C, j + 1)` or `(univ, j)`.  Some labelling lawful below `(univ, j + 1)` is `w` on those cells and
agrees with `a` capped at `h` at every cell below `(univ, j + 1)`.  Below `(D, j + 1)` there are
only old cells; there the boundary labelling is lifted within `D` from the grade `j`, read on the
amalgam (`Seed.exists_lift_union_of_le`: the common face carries no cell of the grade `j + 1`), and
the three pieces are glued (`CellScheme.Rows.IsLawfulBelow.glue₃`): every new cell has grade at most
`j`, and an old cell of grade `j + 1` lies on `C` or on `D`.  The new cells keep the cap of `w`; the
lift within `D` does not reach them. -/
theorem exists_isLawfulBelow_top {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) {j : ℕ} (hj : m ≤ j)
    {w : Fin (I.tower j).card → Label.{u}}
    (hwU : (I.tower j).rows.IsLawfulBelow (univ.erase x, j + 1) fun d ↦ w d)
    (hwV : (I.tower j).rows.IsLawfulBelow (univ, j) fun d ↦ w d)
    {a : Fin (I.tower j).card → Label.{u}} (ha : (I.tower j).rows.IsLawful a) {h : Label.{u}}
    (hh : IsSelfVisible (j + 1) h)
    (hag : ∀ e, e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
      e ∈ (I.tower j).toCellScheme.below (univ, j) → min (w e) h = min (a e) h) :
    ∃ g : Fin (I.tower j).card → Label.{u},
      (I.tower j).rows.IsLawfulBelow (univ, j + 1) (fun d ↦ g d) ∧
      (∀ e, e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
        e ∈ (I.tower j).toCellScheme.below (univ, j) → g e = w e) ∧
      ∀ e ∈ (I.tower j).toCellScheme.below (univ, j + 1), min (g e) h = min (a e) h := by
  classical
  have hDne := ne_univ_erase y
  -- The lift within the other coatom, read on the amalgam.
  obtain ⟨v, hv, hvw, hva⟩ := I.exists_lift_union_of_le hx hy hxy hj hh
    (a := fun d ↦ a (I.towerEmbed j d))
    ((I.isLawfulBelow_tower_iff (g := a) hDne).mp (ha.isLawfulBelow _))
    (w := fun d ↦ w (I.towerEmbed j d))
    ((I.isLawfulBelow_tower_iff (g := w) hDne).mp
      (hwV.mono (X := (univ.erase y, j)) ⟨subset_univ _, le_rfl⟩))
    fun d hd ↦ hag _ (.inr (I.towerEmbed_mem_below_iff.mpr ⟨hd.1.trans (subset_univ _), hd.2⟩))
  -- The lift, carried to the scheme reached after the grade `j`.
  have P := I.isSourcePrefix_tower (j := j) (Y := (univ.erase y, j + 1)) hDne
  have hc : (I.tower j).rows.comap P.isLowerEmbedding = I.amalgam.rows := I.comap_rows_tower j
  obtain ⟨v', hv', hv'v⟩ := P.exists_isLawfulBelow le_rfl (s := v) (by rw [hc]; exact hv)
  have hv't (t : I.amalgam.toCellScheme.below (univ.erase y, j + 1)) :
      v' ⟨I.towerEmbed j t, I.towerEmbed_mem_below_iff.mpr t.2⟩ = v t :=
    hv'v t
  -- A cell below `(D, j + 1)` is old.
  have hold (e : Fin (I.tower j).card)
      (he : e ∈ (I.tower j).toCellScheme.below (univ.erase y, j + 1)) :
      ∃ t : I.amalgam.toCellScheme.below (univ.erase y, j + 1), I.towerEmbed j t = e := by
    obtain ⟨t, rfl⟩ := I.mem_range_towerEmbed j e fun hsc ↦
      hDne (univ_subset_iff.mp (hsc.ge.trans he.1))
    exact ⟨⟨t, I.towerEmbed_mem_below_iff.mp he⟩, rfl⟩
  -- The glued labelling: `w` on the boundary, the lift elsewhere below `(D, j + 1)`.
  obtain ⟨g, hgb, hgo⟩ : ∃ g : Fin (I.tower j).card → Label.{u},
      (∀ e, e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
        e ∈ (I.tower j).toCellScheme.below (univ, j) → g e = w e) ∧
      ∀ e (he : e ∈ (I.tower j).toCellScheme.below (univ.erase y, j + 1)),
        ¬ (e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
          e ∈ (I.tower j).toCellScheme.below (univ, j)) → g e = v' ⟨e, he⟩ :=
    ⟨fun e ↦ if e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
        e ∈ (I.tower j).toCellScheme.below (univ, j) then w e
      else Rows.extendBot (univ.erase y, j + 1) v' e,
      fun e hb ↦ ite_eq_left hb, fun e he hb ↦ (ite_eq_right hb).trans
        (Rows.extendBot_of_mem v' he)⟩
  have hgD (e : Fin (I.tower j).card)
      (he : e ∈ (I.tower j).toCellScheme.below (univ.erase y, j + 1)) : g e = v' ⟨e, he⟩ := by
    by_cases hb : e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
        e ∈ (I.tower j).toCellScheme.below (univ, j)
    · rw [hgb e hb]
      obtain ⟨t, rfl⟩ := hold e he
      rw [hv't t]
      refine (hvw t ?_).symm
      rcases hb with hb | hb
      · exact .inl ⟨subset_inter (I.towerEmbed_mem_below_iff.mp hb).1 t.2.1, t.2.2⟩
      · exact .inr ⟨t.2.1, (I.towerEmbed_mem_below_iff.mp hb).2⟩
    · exact hgo e he hb
  refine ⟨g, Rows.IsLawfulBelow.glue₃ (U := (univ.erase x, j + 1)) (V := (univ, j))
    (W := (univ.erase y, j + 1)) ?_ ?_ ?_ (I.mem_below_cover_tower hx hy hxy), hgb,
    fun e he ↦ ?_⟩
  · convert hwU using 1
    exact funext fun e ↦ hgb e (.inl e.2)
  · convert hwV using 1
    exact funext fun e ↦ hgb e (.inr e.2)
  · convert hv' using 1
    exact funext fun e ↦ hgD e e.2
  · rcases I.mem_below_cover_tower hx hy hxy e he with hb | hb | hb
    · rw [hgb e (.inl hb)]
      exact hag e (.inl hb)
    · rw [hgb e (.inr hb)]
      exact hag e (.inr hb)
    · rw [hgD e hb]
      obtain ⟨t, rfl⟩ := hold e hb
      rw [hv't t]
      exact hva t

/-- **Extension from the boundary at the top grade, at a short positive cap.**  For `m ≤ j`,
along the row of a new cell `u` of graded index `(univ, j + 1)`, at a cap `h` self-visible and
short at `j + 1` with `⊥ < h`, every labelling lawful below `(univ.erase x, j + 1)` and below
`(univ, j)` that agrees with the row of `u` capped at `h` on the boundary extends, unchanged there,
to a labelling lawful below `(univ, j + 1)` that agrees with the row of `u` capped at `h`
everywhere: the boundary labelling is completed below `(univ, j + 1)` in the scheme reached after
the grade `j` along the catalogue entry of `u` (`Seed.exists_isLawfulBelow_top`), then extended
through the new cells. -/
theorem extendsFromBoundary_tower_top {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) {j : ℕ} (hj : m ≤ j) {u : Fin (I.tower (j + 1)).card}
    (hu : (I.tower (j + 1)).toCellScheme.gradedIndex u = (univ, j + 1)) {h : Label.{u}}
    (hh : IsSelfVisible (j + 1) h) (hs : IsShort (j + 1) h) (hbot : ⊥ < h) :
    (I.tower (j + 1)).rows.ExtendsFromBoundary (univ.erase x, j + 1) (univ, j) (univ, j + 1) h
      ((I.tower (j + 1)).rows.rowBelow u hu) :=
  I.extendsFromBoundary_tower_of_forall (fun h ↦ ne_univ_erase x (univ_subset_iff.mp h.1))
    (fun h ↦ absurd h.2 (by simp only; omega)) le_rfl (Nat.le_succ j) hh hs hbot
    (fun _ ha _ hwU hwV hag ↦ I.exists_isLawfulBelow_top hx hy hxy hj hwU hwV
      (Scheme.mem_catalogue.mp ha).1 hh hag) hu

/-- **The boundary labelling, completed on the scheme reached after the grade `j`, by the two-face
lift.**  Let `C = univ.erase x` and `D = univ.erase y` be the two coatoms, `a` a catalogue entry at
the grade `j + 1`, `h` self-visible and short at `j + 1` with `⊥ < h`, and `w` a labelling of the
scheme reached after the grade `j` lawful below `(C, j + 1)` and `(D, j + 1)` that agrees with `a`
capped at `h` on their cells.  Under `2FL(j)` some labelling lawful below `(univ, j + 1)` is `w` on
those cells and agrees with `a` capped at `h` at every cell below `(univ, j + 1)`: the two-face lift
below `(univ, j)`, glued with `w` over `(C, j + 1)`, `(univ, j)` and `(D, j + 1)`
(`CellScheme.Rows.IsLawfulBelow.glue₃`).  The old cells below `(univ, j)` lie on `C` or on `D`,
where the two-face lift is `w`. -/
theorem exists_isLawfulBelow_of_twoFaceLift {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) {j : ℕ} (h2 : I.TwoFaceLift j) {a : Fin (I.tower j).card → Label.{u}}
    (ha : a ∈ (I.tower j).catalogue (j + 1)) {h : Label.{u}} (hh : IsSelfVisible (j + 1) h)
    (hs : IsShort (j + 1) h) (hbot : ⊥ < h) {w : Fin (I.tower j).card → Label.{u}}
    (hwx : (I.tower j).rows.IsLawfulBelow (univ.erase x, j + 1) fun e ↦ w e)
    (hwy : (I.tower j).rows.IsLawfulBelow (univ.erase y, j + 1) fun e ↦ w e)
    (hag : ∀ e, e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
      e ∈ (I.tower j).toCellScheme.below (univ.erase y, j + 1) → min (w e) h = min (a e) h) :
    ∃ g : Fin (I.tower j).card → Label.{u},
      (I.tower j).rows.IsLawfulBelow (univ, j + 1) (fun e ↦ g e) ∧
      (∀ e, e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
        e ∈ (I.tower j).toCellScheme.below (univ.erase y, j + 1) → g e = w e) ∧
      ∀ e ∈ (I.tower j).toCellScheme.below (univ, j + 1), min (g e) h = min (a e) h := by
  classical
  have hwx₀ := (I.isLawfulBelow_tower_iff (g := w) (ne_univ_erase x)).mp hwx
  have hwy₀ := (I.isLawfulBelow_tower_iff (g := w) (ne_univ_erase y)).mp hwy
  have hag₀ (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ j + 1) :
      min (w (I.towerEmbed j d)) h = min (a (I.towerEmbed j d)) h :=
    hag _ ((I.scope_subset_or hx hy hxy d).imp
      (fun hsc ↦ I.towerEmbed_mem_below_iff.mpr ⟨hsc, hd⟩)
      fun hsc ↦ I.towerEmbed_mem_below_iff.mpr ⟨hsc, hd⟩)
  -- The two-face lift, with the coatoms in the order of the seed.
  obtain ⟨r, hr, hrw, hra⟩ : ∃ r : (I.tower j).toCellScheme.below (univ, j) → Label.{u},
      (I.tower j).rows.IsLawfulBelow (univ, j) r ∧
      (∀ d (hd : I.amalgam.toCellScheme.grade d ≤ j),
        r ⟨I.towerEmbed j d, I.towerEmbed_mem_below hd⟩ = w (I.towerEmbed j d)) ∧
      ∀ e, min (r e) h = min (a e) h := by
    rcases pair_cases hx hy hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h2 a ha h hh hs hbot (fun d ↦ w (I.towerEmbed j d)) hwx₀ hwy₀ hag₀
    · exact h2 a ha h hh hs hbot (fun d ↦ w (I.towerEmbed j d)) hwy₀ hwx₀ hag₀
  -- The glued labelling: the two-face lift below `(univ, j)`, `w` elsewhere.
  obtain ⟨g, hgr, hgw⟩ : ∃ g : Fin (I.tower j).card → Label.{u},
      (∀ e (he : e ∈ (I.tower j).toCellScheme.below (univ, j)), g e = r ⟨e, he⟩) ∧
      ∀ e, e ∉ (I.tower j).toCellScheme.below (univ, j) → g e = w e :=
    ⟨fun e ↦ if he : e ∈ (I.tower j).toCellScheme.below (univ, j) then r ⟨e, he⟩ else w e,
      fun e he ↦ dite_eq_left he, fun e he ↦ dite_eq_right he⟩
  have hgb (e : Fin (I.tower j).card)
      (he : e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
        e ∈ (I.tower j).toCellScheme.below (univ.erase y, j + 1)) : g e = w e := by
    by_cases hej : e ∈ (I.tower j).toCellScheme.below (univ, j)
    · rw [hgr e hej]
      have hsc : (I.tower j).toCellScheme.scope e ≠ univ := fun hu ↦ he.elim
        (fun h' ↦ ne_univ_erase x (univ_subset_iff.mp (hu.ge.trans h'.1)))
        fun h' ↦ ne_univ_erase y (univ_subset_iff.mp (hu.ge.trans h'.1))
      obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed j e hsc
      exact hrw d ((I.grade_towerEmbed j d).symm.trans_le hej.2)
    · exact hgw e hej
  refine ⟨g, Rows.IsLawfulBelow.glue₃ (U := (univ.erase x, j + 1)) (V := (univ, j))
    (W := (univ.erase y, j + 1)) ?_ ?_ ?_ (I.mem_below_cover_tower hx hy hxy), hgb,
    fun e he ↦ ?_⟩
  · convert hwx using 1
    exact funext fun e ↦ hgb e (.inl e.2)
  · convert hr using 1
    exact funext fun e ↦ hgr e e.2
  · convert hwy using 1
    exact funext fun e ↦ hgb e (.inr e.2)
  · rcases I.mem_below_cover_tower hx hy hxy e he with hb | hb | hb
    · rw [hgb e (.inl hb)]
      exact hag e (.inl hb)
    · rw [hgr e hb]
      exact hra _
    · rw [hgb e (.inr hb)]
      exact hag e (.inr hb)

/-- **Extension from the boundary of the two coatoms, at a short positive cap, under `2FL(j)`.**
Along the row of a new cell `u` of graded index `(univ, j + 1)`, at a cap `h` self-visible and
short at `j + 1` with `⊥ < h`, every labelling lawful below `(univ.erase x, j + 1)` and below
`(univ.erase y, j + 1)` that agrees with the row of `u` capped at `h` on the boundary extends,
unchanged there, to a labelling lawful below `(univ, j + 1)` that agrees with the row of `u` capped
at `h` everywhere: restricted to the scheme reached after the grade `j` and to the amalgam, the
boundary labelling is extended through the new cells of the layers `1, …, j` by `2FL(j)` along the
catalogue entry of `u`, glued with its old cells of the grade `j + 1`
(`Seed.exists_isLawfulBelow_of_twoFaceLift`), and extended through the new cells of the layer
`j + 1` at the short cap (`Scheme.exists_extension_fieldLayer`). -/
theorem extendsFromBoundary_tower_of_twoFaceLift {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) {j : ℕ} (h2 : I.TwoFaceLift j) {u : Fin (I.tower (j + 1)).card}
    (hu : (I.tower (j + 1)).toCellScheme.gradedIndex u = (univ, j + 1)) {h : Label.{u}}
    (hh : IsSelfVisible (j + 1) h) (hs : IsShort (j + 1) h) (hbot : ⊥ < h) :
    (I.tower (j + 1)).rows.ExtendsFromBoundary (univ.erase x, j + 1) (univ.erase y, j + 1)
      (univ, j + 1) h ((I.tower (j + 1)).rows.rowBelow u hu) :=
  I.extendsFromBoundary_tower_of_forall (fun h ↦ ne_univ_erase x (univ_subset_iff.mp h.1))
    (fun h ↦ ne_univ_erase y (univ_subset_iff.mp h.1)) le_rfl le_rfl hh hs hbot
    (fun _ ha _ hwU hwV hag ↦ I.exists_isLawfulBelow_of_twoFaceLift hx hy hxy h2 ha hh hs hbot
      hwU hwV hag) hu

/-- **`2FL(j)` is the extension from the boundary used by the step.**  The two-face lift
`2FL(j)` holds if and only if, along the row of every new cell of graded index `(univ, j + 1)`, at
every cap `h` self-visible and short at `j + 1` with `⊥ < h`, every labelling lawful below the two
coatoms at the grade `j + 1` that agrees with the row capped at `h` on their cells extends,
unchanged there, to one lawful below `(univ, j + 1)` that agrees with the row capped at `h`
everywhere.  The right-hand side is the clause of the hypothesis on the rows that
`Seed.towerInvariant_succ` passes to `CellScheme.Rows.cappedLift_of_boundary_short` at the
positive caps.

So `2FL(j)` is exactly that hypothesis of the step, read on the scheme reached after the grade `j`:
it is broader than what the construction of the step meets only in the universal quantifiers over
the boundary labelling, the row and the short cap, which the generic one-grade lift forces.  The
forward direction is `Seed.extendsFromBoundary_tower_of_twoFaceLift`.  Conversely, a catalogue
entry is the row of a new cell (`Scheme.fieldLayer_row_natAdd`); a labelling of the amalgam is
carried to the scheme reached after the grade `j + 1` on the old cells, extended there, and the
extension restricted to the cells below `(univ, j)` through the source prefix.  Nothing is
asserted here about any implication between `2FL(j)` and the invariant at the grade `j + 1`. -/
theorem twoFaceLift_iff_extendsFromBoundary {j : ℕ} :
    I.TwoFaceLift j ↔
      ∀ (u : Fin (I.tower (j + 1)).card)
        (hu : (I.tower (j + 1)).toCellScheme.gradedIndex u = (univ, j + 1)) (h : Label.{u}),
        IsSelfVisible (j + 1) h → IsShort (j + 1) h → ⊥ < h →
        (I.tower (j + 1)).rows.ExtendsFromBoundary (univ.erase (Fin.last (m + 1)), j + 1)
          (univ.erase (Fin.castSucc (Fin.last m)), j + 1) (univ, j + 1) h
          ((I.tower (j + 1)).rows.rowBelow u hu) := by
  classical
  refine ⟨fun h2 u hu h hh hs hbot ↦ I.extendsFromBoundary_tower_of_twoFaceLift
    (mem_insert_self _ _) (mem_insert_of_mem (mem_singleton_self _)) last_ne_castSucc h2 hu hh hs
    hbot, fun hext ↦ ?_⟩
  intro a ha h hh hs hbot w hwx hwy hag
  obtain ⟨i, rfl⟩ := Scheme.exists_catalogueEntry_eq (S := I.tower j) (k := j + 1) ha
  have hu : (I.tower (j + 1)).toCellScheme.gradedIndex (Fin.natAdd _ i) = (univ, j + 1) :=
    Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i
  -- `w` carried to the scheme reached after the grade `j + 1` on the old cells, `⊥` elsewhere.
  set W : Fin (I.tower (j + 1)).card → Label.{u} :=
    Function.extend (I.towerEmbed (j + 1)) w (fun _ ↦ ⊥)
  have hWe (d : Fin I.amalgam.card) : W (I.towerEmbed (j + 1) d) = w d :=
    (I.towerEmbed (j + 1)).injective.extend_apply _ _ _
  have hWx : (I.tower (j + 1)).rows.IsLawfulBelow (univ.erase (Fin.last (m + 1)), j + 1)
      fun e ↦ W e := by
    rw [I.isLawfulBelow_tower_iff (ne_univ_erase _)]; simpa only [hWe] using hwx
  have hWy : (I.tower (j + 1)).rows.IsLawfulBelow
      (univ.erase (Fin.castSucc (Fin.last m)), j + 1) fun e ↦ W e := by
    rw [I.isLawfulBelow_tower_iff (ne_univ_erase _)]; simpa only [hWe] using hwy
  -- The row of the new cell `Fin.natAdd _ i` reads the catalogue entry on the old cells.
  have hrow (e : Fin (I.tower j).card)
      (he : Fin.castAdd ((I.tower j).catalogue (j + 1)).card e ∈
        (I.tower (j + 1)).toCellScheme.below (univ, j + 1)) :
      (I.tower (j + 1)).rows.rowBelow (Fin.natAdd _ i) hu ⟨_, he⟩ =
        (I.tower j).catalogueEntry (j + 1) i e :=
    (Scheme.fieldLayer_row_natAdd (hS := I.not_univ_succ_le_tower j) i _).trans
      (Scheme.fieldRow_castAdd _ _)
  obtain ⟨r, hr, hrW, hrS⟩ := hext (Fin.natAdd _ i) hu h hh hs hbot W hWx hWy fun d hd ↦ by
    obtain ⟨dd, hdd⟩ := d
    have hsc : (I.tower (j + 1)).toCellScheme.scope dd ≠ univ := fun he ↦ hd.elim
      (fun h' ↦ ne_univ_erase _ (univ_subset_iff.mp (he.ge.trans h'.1)))
      fun h' ↦ ne_univ_erase _ (univ_subset_iff.mp (he.ge.trans h'.1))
    obtain ⟨e, rfl⟩ := I.mem_range_towerEmbed (j + 1) dd hsc
    have hge : I.amalgam.toCellScheme.grade e ≤ j + 1 :=
      (I.grade_towerEmbed (j + 1) e).symm.trans_le hdd.2
    rw [hWe, hag e hge]
    exact (congrArg (min · h) (hrow (I.towerEmbed j e) hdd)).symm
  have hmem (e : (I.tower j).toCellScheme.below (univ, j)) :
      Fin.castAdd ((I.tower j).catalogue (j + 1)).card e.1 ∈
        (I.tower (j + 1)).toCellScheme.below (univ, j + 1) :=
    Scheme.castAdd_mem_below (hS := I.not_univ_succ_le_tower j) (e.2.2.trans (Nat.le_succ j))
  refine ⟨fun e ↦ r ⟨_, hmem e⟩, ?_, fun d hd ↦ ?_, fun e ↦ ?_⟩
  · -- Lawfulness below `(univ, j)`, carried back through the source prefix.
    have P := I.isSourcePrefix_tower_succ (j := j) le_rfl
    have hc : (I.tower (j + 1)).rows.comap P.isLowerEmbedding = (I.tower j).rows :=
      I.comap_rows_tower_succ j
    have hrj : (I.tower (j + 1)).rows.IsLawfulBelow (univ, j) fun t ↦
        Rows.extendBot (univ, j + 1) r t :=
      (Rows.isLawfulBelow_extendBot.mpr hr).mono (X := (univ, j)) ⟨subset_rfl, Nat.le_succ j⟩
    have := (P.isLawfulBelow_iff le_rfl).mpr hrj
    rw [hc] at this
    convert this using 1
    funext e
    exact (Rows.extendBot_of_mem r (hmem e)).symm
  · -- An old cell of grade at most `j` lies on one of the two coatoms.
    have hb := (I.scope_subset_or (mem_insert_self _ _)
      (mem_insert_of_mem (mem_singleton_self _)) last_ne_castSucc d).imp
      (fun hsc ↦ (I.towerEmbed_mem_below_iff (j := j + 1)
        (X := (univ.erase (Fin.last (m + 1)), j + 1))).mpr ⟨hsc, hd.trans (Nat.le_succ j)⟩)
      fun hsc ↦ (I.towerEmbed_mem_below_iff (j := j + 1)
        (X := (univ.erase (Fin.castSucc (Fin.last m)), j + 1))).mpr
          ⟨hsc, hd.trans (Nat.le_succ j)⟩
    exact (hrW ⟨_, hmem ⟨_, I.towerEmbed_mem_below hd⟩⟩ hb).trans (hWe d)
  · exact (hrS _).trans (congrArg (min · h) (hrow e.1 (hmem e)))

/-- **The step from the grade `j` to `j + 1`, under `2FL(j)`.**  For `j ≤ m`, if the invariant
holds at the grade `j` and the two-face lift `2FL(j)` holds, the invariant holds at the grade
`j + 1`.  The lifts at the grades `j' ≤ j` are carried to the next scheme through the source
prefix.  The lift from a coatom `C = univ.erase x` to `(univ, j + 1)` is
`CellScheme.Rows.cappedLift_of_boundary_short`, with the invariant from `(C, j)` to `(univ, j)` as
the lift at the lower grade (used by the restoration of the lower prescriptions) and one boundary
triple: `U = (C, j + 1)`, `V = (D, j + 1)` for the other coatom `D`, and `O` the common face at the
grade `min (j + 1) m`, the lift from `O` to `V` being a lift of the amalgam.  The extension from
the boundary is the extension at `⊥` through the whole tower (`Seed.extendsFromBoundary_bot_tower`)
at `⊥`, and `Seed.extendsFromBoundary_tower_of_twoFaceLift` at the short positive caps.  The
recursion uses it at the grades `2 ≤ j + 1 ≤ m` (`Seed.towerInvariant_of_twoFaceLift`); the step to
the top grade needs no hypothesis beyond the invariant at `m` (`Seed.towerInvariant_top`). -/
theorem towerInvariant_succ {j : ℕ} (hjm : j ≤ m) (hinv : I.TowerInvariant j)
    (h2 : I.TwoFaceLift j) : I.TowerInvariant (j + 1) := by
  intro x hx j' hj'
  rcases Nat.lt_or_eq_of_le hj' with hlt | rfl
  · exact I.cappedLift_tower_succ (Nat.lt_succ_iff.mp hlt)
      (hinv x hx j' (Nat.lt_succ_iff.mp hlt))
  obtain ⟨y, hy, hxy⟩ := exists_other hx
  -- `I.tower (j + 1)` is the field layer of `I.tower j` (`Seed.tower_succ`, by `rfl`); the generic
  -- one-grade lift is stated for the field layer.
  change ((I.tower j).fieldLayer (j + 1) (I.not_univ_succ_le_tower j)).rows.CappedLift
    (X := (univ.erase x, j + 1)) (Y := (univ, j + 1)) ⟨erase_subset _ _, le_rfl⟩
  refine Rows.cappedLift_of_boundary_short (C := univ.erase x) (B := univ) (j := j)
    (U := (univ.erase x, j + 1)) (V := (univ.erase y, j + 1))
    (O := (univ.erase x ∩ univ.erase y, min (j + 1) m)) (erase_subset _ _) ?_
    (I.cappedLift_tower_succ le_rfl (hinv x hx j le_rfl)) le_rfl
    ⟨inter_subset_left, min_le_left _ _⟩ ⟨inter_subset_right, min_le_left _ _⟩
    ⟨erase_subset _ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩
    (fun d hdU hdV ↦ I.mem_below_commonFace_tower hx hy hxy (k := j + 1) (by omega) d hdU hdV)
    (Rows.cappedLift_refl _) (I.cappedLift_commonFace_tower hx hy hxy (by omega))
    (I.extendsFromBoundary_bot_tower (I.scope_subset_or hx hy hxy) (j + 1))
    (I.exists_gradedIndex_eq_univ_tower j) fun u hu ↦
      ⟨I.isConsistent_tower (j + 1) u, fun d ↦ (I.isShort_ne_top_rowBelow_tower hu d).1,
        fun d ↦ (I.isShort_ne_top_rowBelow_tower hu d).2, fun h hh hs hbot ↦
        I.extendsFromBoundary_tower_of_twoFaceLift hx hy hxy h2 hu hh hs hbot⟩
  exact I.exists_gradedIndex_eq_tower (j + 1)
    ⟨I.erase_mem_faces hx, Nat.succ_pos j, by rw [card_erase]; omega⟩ (ne_univ_erase x)

/-- **The step to the top grade `m + 1`**, with no hypothesis beyond the invariant at the grade
`m`.  The lifts at the grades `j' ≤ m` are carried through the source prefix.  The lift from a
coatom `C = univ.erase x` to `(univ, m + 1)` is `CellScheme.Rows.cappedLift_of_boundaries_short`,
with the invariant from `(C, m)` to `(univ, m)` as the lift at the lower grade and two boundary
triples:

* at the cap `⊥`: `U = (C, m + 1)`, `V = (D, m + 1)` for the other coatom `D`, and `O` the common
  face at the grade `m`; the lift from `O` to `V` is a lift of the amalgam, and the extension from
  the boundary is the extension at `⊥` through the whole tower
  (`Seed.extendsFromBoundary_bot_tower`);
* at the positive caps: `U = (C, m + 1)`, `V = (univ, m)`, `O = (C, m)`; the lift from `O` to `V`
  is the invariant, used at every self-visible cap and along every lawful ambient, and the
  extension from the boundary along the row of each new cell of grade `m + 1`, at the short caps,
  is `Seed.extendsFromBoundary_tower_top`, which lifts within the other coatom. -/
theorem towerInvariant_top (hinv : I.TowerInvariant m) : I.TowerInvariant (m + 1) := by
  intro x hx j' hj'
  rcases Nat.lt_or_eq_of_le hj' with hlt | rfl
  · exact I.cappedLift_tower_succ (Nat.lt_succ_iff.mp hlt)
      (hinv x hx j' (Nat.lt_succ_iff.mp hlt))
  obtain ⟨y, hy, hxy⟩ := exists_other hx
  have hlift := I.cappedLift_tower_succ le_rfl (hinv x hx m le_rfl)
  -- `I.tower (m + 1)` is the field layer of `I.tower m` (`Seed.tower_succ`, by `rfl`); the generic
  -- one-grade lift is stated for the field layer.
  change ((I.tower m).fieldLayer (m + 1) (I.not_univ_succ_le_tower m)).rows.CappedLift
    (X := (univ.erase x, m + 1)) (Y := (univ, m + 1)) ⟨erase_subset _ _, le_rfl⟩
  refine Rows.cappedLift_of_boundaries_short (C := univ.erase x) (B := univ) (j := m)
    (U₀ := (univ.erase x, m + 1)) (V₀ := (univ.erase y, m + 1))
    (O₀ := (univ.erase x ∩ univ.erase y, min (m + 1) m))
    (U := (univ.erase x, m + 1)) (V := (univ, m)) (O := (univ.erase x, m))
    (erase_subset _ _) ?_ hlift le_rfl ⟨inter_subset_left, min_le_left _ _⟩
    ⟨inter_subset_right, min_le_left _ _⟩ ⟨erase_subset _ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩
    (fun d hdU hdV ↦ I.mem_below_commonFace_tower hx hy hxy (k := m + 1) (by omega) d hdU hdV)
    (Rows.cappedLift_refl _) (I.cappedLift_commonFace_tower hx hy hxy le_rfl)
    (I.extendsFromBoundary_bot_tower (I.scope_subset_or hx hy hxy) (m + 1))
    le_rfl ⟨subset_rfl, Nat.le_succ m⟩ ⟨subset_univ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩
    ⟨subset_rfl, Nat.le_succ m⟩ (fun d hdU hdV ↦ ⟨hdU.1, hdV.2⟩) (Rows.cappedLift_refl _) hlift
    (I.exists_gradedIndex_eq_univ_tower m) fun u hu ↦
      ⟨I.isConsistent_tower (m + 1) u, fun d ↦ (I.isShort_ne_top_rowBelow_tower hu d).1,
        fun d ↦ (I.isShort_ne_top_rowBelow_tower hu d).2, fun h hh hs hbot ↦
        I.extendsFromBoundary_tower_top hx hy hxy le_rfl hu hh hs hbot⟩
  exact I.exists_gradedIndex_eq_tower (m + 1)
    ⟨I.erase_mem_faces hx, Nat.succ_pos m, by rw [card_erase]⟩ (ne_univ_erase x)

/-- **The invariant up to the grade `m + 1`, under `2FL(j)` at the grades `2 ≤ j + 1 ≤ m`.**  The
base is the grade `1` (`Seed.towerInvariant_one`); the steps below the top are
`Seed.towerInvariant_succ`, and the step to the grade `m + 1` is `Seed.towerInvariant_top`.  So
`2FL(j)` is assumed only at the grades `j + 1` with `2 ≤ j + 1 ≤ m`; at the arity `2` that is
`2FL(1)` alone.  The hypothesis is on the seed `I`; at the arity `3` it fails for some legal seeds
(`TwoFaceLiftCounterexample.not_twoFaceLift_two`), for which
`Seed.towerInvariant_of_twoFaceLift_or_deadAt` can serve instead. -/
theorem towerInvariant_of_twoFaceLift (h2 : ∀ j, 1 ≤ j → j < m → I.TwoFaceLift j) :
    ∀ j ≤ m + 1, I.TowerInvariant j
  | 0, _ => I.towerInvariant_zero
  | 1, _ => I.towerInvariant_one
  | j + 2, hj =>
    if hjm : j + 1 < m then
      I.towerInvariant_succ hjm.le (towerInvariant_of_twoFaceLift h2 (j + 1) (by omega))
        (h2 (j + 1) (by omega) hjm)
    else by
      have hinv := towerInvariant_of_twoFaceLift h2 (j + 1) (by omega)
      rw [show j + 1 = m by omega] at hinv
      rw [show j + 2 = m + 1 by omega]
      exact I.towerInvariant_top hinv

/-- **The invariant up to the grade `m + 1` at the arities `m ≤ 1`**, with no hypothesis: the
grades `0` and `1` are the base, and the grade `2` at `m = 1` is the top grade
(`Seed.towerInvariant_top`).  It does not use the two-face lift. -/
theorem towerInvariant_of_le_one (hm : m ≤ 1) : ∀ j ≤ m + 1, I.TowerInvariant j
  | 0, _ => I.towerInvariant_zero
  | 1, _ => I.towerInvariant_one
  | j + 2, hj => by
    have hinv := I.towerInvariant_one
    rw [show 1 = m by omega] at hinv
    rw [show j + 2 = m + 1 by omega]
    exact I.towerInvariant_top hinv

end Seed

/-! ### Literal faces of the tower -/

namespace TowerExamples

section LiteralFaces

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (hα : Order.IsSuccPrelimit α) {j : ℕ}
  (hj : j ≤ m + 2)

/-- The scheme reached after the grade `j`, with the glued labelling extended through the tower and
reduced to the stage `α`, zero or a limit: a stage type on `m + 2` points. -/
noncomputable def towerType : StageType.{u} α (m + 2) where
  toScheme := I.tower j
  label d := Label.reduce α ((I.exists_isLawful_tower j I.amalgam.isLawful).choose d)
  isWellFormed := I.isWellFormed_tower j hj
  isCoded := I.isCoded_tower j
  isLawful := (I.exists_isLawful_tower j I.amalgam.isLawful).choose_spec.1.reduce hα
  atStage _ := atStage_reduce α _

/-- The stage type of the tower keeps the glued labels on the old cells. -/
theorem towerType_label_embed (d : Fin I.amalgam.card) :
    (towerType I hα hj).label (I.towerEmbed j d) = I.amalgam.label d :=
  (congrArg (Label.reduce α) ((I.exists_isLawful_tower j I.amalgam.isLawful).choose_spec.2 d)).trans
    (I.amalgam.atStage d).reduce_eq

/-- **The faces of the tower along a proper face are those of the amalgam**, labels included. -/
theorem restrictFace_towerType {k : ℕ} (f : Fin k ↪ Fin (m + 2)) (hf : univ.map f ≠ univ) :
    StageType.restrictFace f (towerType I hα hj) = StageType.restrictFace f I.amalgam := by
  refine StageType.restrictFace_eq_of_strictMono (t := towerType I hα hj) (s := I.amalgam) f
    (φ := I.towerEmbed j) (I.towerEmbed j).strictMono (I.isLowerEmbedding_tower j)
    (I.scope_towerEmbed j) (I.comap_rows_tower j)
    ((I.isWellFormed_tower j hj).ground_eq.trans I.amalgam.isWellFormed.ground_eq.symm)
    (I.faces_tower j) (towerType_label_embed I hα hj) fun z hz ↦
      I.mem_range_towerEmbed j z fun he ↦ hf (eq_univ_of_forall fun x ↦ ?_)
  obtain ⟨y, rfl⟩ : x ∈ Set.range f := hz (mem_coe.mpr (he.symm ▸ mem_univ x))
  exact mem_map_of_mem _ (mem_univ y)

/-- **The face of the tower along the first coatom is the first coatom type**, literally. -/
theorem restrictFace_left_towerType :
    StageType.restrictFace (Coatom.left m) (towerType I hα hj) = some I.left := by
  refine (restrictFace_towerType I hα hj _ fun he ↦ ?_).trans I.restrictFace_left
  exact Coatom.last_notMem_univ_map_left (he ▸ mem_univ (Fin.last (m + 1)))

/-- **The face of the tower along the second coatom is the second coatom type**, literally. -/
theorem restrictFace_right_towerType :
    StageType.restrictFace (Coatom.right m) (towerType I hα hj) = some I.right := by
  refine (restrictFace_towerType I hα hj _ fun he ↦ ?_).trans I.restrictFace_right
  have h := mem_univ (Fin.castSucc (Fin.last m))
  rw [← he, Coatom.univ_map_right] at h
  exact notMem_erase _ _ h

end LiteralFaces

end TowerExamples

end VaughtConjecture
