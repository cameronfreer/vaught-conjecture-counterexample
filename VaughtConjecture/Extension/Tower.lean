/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.SmallArities

/-!
# The tower of field layers, and the step from the grade `j` to `j + 1`

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.6 (the recursion on the grade; here its first part: the
tower, the lifting invariant, and the step from the grade `j` to `j + 1` under the union fill);
semantic contract, items 2–4.

Let `I` be a seed on `m + 2` points.  Its two coatoms are `univ.erase x` for the two points
`x ∈ {Fin.last (m + 1), Fin.castSucc (Fin.last m)}`; they meet in the **common face**, on `m`
points, a face of the amalgam (`Seed.common_mem_faces`).

**The tower** (`Seed.tower`).  The canonical field layer of a scheme `S` at a grade `k`
(`Scheme.fieldLayer`, `VaughtConjecture.Extension.FieldLayer`) appends to `S` one cell of full
scope and grade `k` for each lawful labelling of `S` that is bottom above the grade `k` and fixed by
the orbit code at `k`; the row of each new cell reads its labelling on the cells of `S` and
agreement heights on the new cells.  The *tower of field layers* is the sequence of schemes `T j`:
`T 0` is the amalgam, and `T (j + 1)` is the canonical field layer of `T j` at the grade `j + 1`
(`Seed.tower_succ`, by `rfl`), its *layer* at the grade `j + 1`.  It is defined by recursion
together with the property that every cell of `T j` has grade at most `j` or scope other than the
ground set (`Seed.tower_grade_le_or`), which makes the next layer defined.  The cells of the
amalgam, carried along `Fin.castAdd` through each layer (`Seed.towerEmbed`), are the *old cells*;
the others, the *new cells*, have full scope.

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
  keeping every old label literally, the labels `⊤` included.

**The lifting invariant** (`Seed.TowerInvariant j`): for both coatoms `C` and every `j' ≤ j`, the
rows of `T j` lift capped from `(C, j')` to `(univ, j')`, at every cap self-visible at `j'` and for
every lawful ambient.  It holds at the grade `0` (no cells) and at the grade `1` at every arity
(`Seed.towerInvariant_one`): there the one-grade lift uses the coatoms at the grade `1` and the
common face, whose lift into the other coatom is a lift of the amalgam
(`Seed.cappedLift_commonFace_tower`); no lower layer is read.

**The step** (`Seed.towerInvariant_succ`).  For the one-grade lift from `(C, j + 1)` to
`(B, j + 1)`, a *boundary triple* is a triple of pairs `U, V ≤ (B, j + 1)` and `O ≤ U, V` with
`(C, j + 1) ≤ U`, such that every cell below both `U` and `V` lies below `O`, together with capped
lifts from `(C, j + 1)` to `U` and from `O` to `V`; its *boundary* is the set of cells below `U` or
`V`.  The step uses one boundary triple at the cap `⊥` and another at the positive caps
(`CellScheme.Rows.cappedLift_of_boundaries_short`), with the invariant from `(C, j)` to `(univ, j)`
as the lift at the lower grade, used by the restoration of the lower prescriptions.

* At `⊥`: `U = (C, j + 1)`, `V = (D, j + 1)` for the other coatom `D`, and `O` the common face at
  the grade `min (j + 1) m`; the lift from `O` to `V` is a lift of the amalgam, and the extension
  from the boundary is the extension at `⊥` through the whole tower
  (`Seed.extendsFromBoundary_bot_tower`).
* At the positive caps: `U = (C, j + 1)`, `V = (univ, j)`, `O = (C, j)`; the lift from `O` to `V`
  is the invariant, at the source caps of the owner alignment, which are short at `j + 1` but not
  at `j`, along the rows of the new cells.  The extension from the boundary along the row of a new
  cell, at a cap short at `j + 1` (`Seed.extendsFromBoundary_tower`), restricts to `T j`, fills the
  other coatom's cells of the grade `j + 1` by the union fill, glues over `(C, j + 1)`, `(univ, j)`
  and `(D, j + 1)`, and extends through the new cells (`Scheme.exists_extension_fieldLayer` at a
  short cap).  The new cells of `T j` keep the cap of the boundary labelling, which they get from
  the invariant; the fill on `D` reads only old cells.

**The union fill** (`Seed.UnionFill`): on the other coatom `D`, a labelling lawful below the common
face at the grade `j + 1` and below `(D, j)`, agreeing with a lawful `a` capped at `h` on their
union, extends, unchanged on the union, to one lawful below `(D, j + 1)` agreeing with `a` capped
at `h`.  It is a lift from the union of two pairs that do not cover `(D, j + 1)`: neither the
bountifulness of the amalgam nor a lift within a face gives it in general, and it is a hypothesis
of the step here, never derived from the bountifulness of the amalgam.

* When the common face carries no cell of the grade `j + 1`, that is from the grade `m + 1` on, it
  is a lift within the face (`Seed.unionFill_of_lt_grade`, `Seed.unionFill_of_le`).  So the
  invariant up to the grade `m + 1` needs the union fill only at the grades `2 ≤ j + 1 ≤ m`
  (`Seed.towerInvariant_of_unionFill`), and at the arities `m ≤ 1` it needs none
  (`Seed.towerInvariant_of_le_one`): the completion at those arities
  (`Seed.nonempty_completionBelowFullGrade_of_le_one`) does not depend on it.
* **At the grades `2 ≤ j + 1 ≤ m` the union fill is still to be proved.**  Its case where the
  prescription on the common face at the grade `j + 1` is at most the cap, by a splice, and the
  more general case of a witness at a larger cap, are checkpoint 2.6b; from the union fill,
  bountifulness, legality below the full grade, and the completion below the full grade at every
  arity (checkpoint 2.6c), and the coatom extension property at every stage that is zero or a limit
  (checkpoint 2.7), follow.

No hypothesis on the stage enters, and no completion is assumed: the lifts off the full face come
from the bountifulness of the amalgam through the source prefix.

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

/-! ### The one-grade lift with two boundary triples -/

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {U V O U₀ V₀ O₀ : Finset α × ℕ}
  {B C : Finset α} {j : ℕ}

/-- **The one-grade lift with one boundary triple at the cap `⊥` and another at the positive
caps.**  Let `C ⊆ B`, with finitely many cells below `(C, j + 1)`, some cell of graded index
`(C, j + 1)`, and the lift at the lower grade, from `(C, j)` to `(B, j)`.  Suppose:

* at the cap `⊥`: pairs `(C, j + 1) ≤ U₀`, `O₀ ≤ U₀, V₀`, `U₀, V₀ ≤ (B, j + 1)`, the cells below
  both `U₀` and `V₀` lying below `O₀`, capped lifts from `(C, j + 1)` to `U₀` and from `O₀` to
  `V₀`, and the extension from the boundary of `U₀` and `V₀` at `⊥`;
* at the positive caps: pairs `U`, `V`, `O` with the same properties, some cell of graded index
  `(B, j + 1)`, and at every such cell a row lawful below `(B, j + 1)`, short at `j + 1`, never the
  formal top, along which the rows extend from the boundary of `U` and `V` at every positive cap
  short and self-visible at `j + 1`.

Then the rows lift capped from `(C, j + 1)` to `(B, j + 1)`
(`CellScheme.Rows.cappedLift_of_ownerCappedLift`): at `⊥` by
`CellScheme.Rows.hasOwnerCappedLifts_bot_of_boundary` with the first triple, at a positive cap by
`CellScheme.Rows.hasOwnerCappedLifts_of_rows_short` and
`CellScheme.Rows.cappedLiftAtShort_of_boundary` with the second.  With both triples equal it is
`CellScheme.Rows.cappedLift_of_boundary_short`. -/
theorem cappedLift_of_boundaries_short [Finite (D.below (C, j + 1))] (hCB : C ⊆ B)
    (hX : ∃ c, D.gradedIndex c = (C, j + 1))
    (hlift : R.CappedLift (X := (C, j)) (Y := (B, j)) ⟨hCB, le_rfl⟩)
    (hCU₀ : ((C, j + 1) : Finset α × ℕ) ≤ U₀) (hOU₀ : O₀ ≤ U₀) (hOV₀ : O₀ ≤ V₀)
    (hUY₀ : U₀ ≤ (B, j + 1)) (hVY₀ : V₀ ≤ (B, j + 1))
    (hinter₀ : ∀ d ∈ D.below U₀, d ∈ D.below V₀ → d ∈ D.below O₀)
    (hleft₀ : R.CappedLift hCU₀) (hright₀ : R.CappedLift hOV₀)
    (hbot : R.ExtendsFromBoundary U₀ V₀ (B, j + 1) ⊥ fun _ ↦ ⊥)
    (hCU : ((C, j + 1) : Finset α × ℕ) ≤ U) (hOU : O ≤ U) (hOV : O ≤ V)
    (hUY : U ≤ (B, j + 1)) (hVY : V ≤ (B, j + 1))
    (hinter : ∀ d ∈ D.below U, d ∈ D.below V → d ∈ D.below O)
    (hleft : R.CappedLift hCU) (hright : R.CappedLift hOV)
    (hY : ∃ t, D.gradedIndex t = (B, j + 1))
    (hrow : ∀ u (hu : D.gradedIndex u = (B, j + 1)),
      R.IsLawfulBelow (D.gradedIndex u) (R.row u) ∧ (∀ d, IsShort (j + 1) (R.rowBelow u hu d)) ∧
      (∀ d, R.rowBelow u hu d ≠ ⊤) ∧
      ∀ h, IsSelfVisible (j + 1) h → IsShort (j + 1) h → ⊥ < h →
        R.ExtendsFromBoundary U V (B, j + 1) h (R.rowBelow u hu)) :
    R.CappedLift (X := (C, j + 1)) (Y := (B, j + 1)) ⟨hCB, le_rfl⟩ := by
  refine cappedLift_of_ownerCappedLift hCB hX hlift fun c hc ↦ ?_
  rcases eq_bot_or_bot_lt c with rfl | hcbot
  · exact hasOwnerCappedLifts_bot_of_boundary hCB hCU₀ hOU₀ hOV₀ hUY₀ hVY₀ hinter₀ hleft₀
      hright₀ hbot
  refine hasOwnerCappedLifts_of_rows_short hCB hcbot hc hY fun u hu ↦ ?_
  obtain ⟨hcons, hshort, htop, hext⟩ := hrow u hu
  exact ⟨hcons, hshort, htop, cappedLiftAtShort_of_boundary hCU hOU hOV hUY hVY hinter hleft
    hright (isLawfulBelow_rowBelow hu hcons) hext⟩

end CellScheme.Rows

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
private theorem ne_univ_erase (x : Fin (m + 2)) : univ.erase x ≠ univ :=
  (erase_ssubset (mem_univ x)).ne

/-- An old cell lies below a pair exactly when the cell of the amalgam does. -/
theorem towerEmbed_mem_below_iff {j : ℕ} {X : Finset (Fin (m + 2)) × ℕ}
    {d : Fin I.amalgam.card} :
    I.towerEmbed j d ∈ (I.tower j).toCellScheme.below X ↔ d ∈ I.amalgam.toCellScheme.below X := by
  rw [CellScheme.mem_below, CellScheme.mem_below, gradedIndex_towerEmbed]

/-- **Extension at the cap `⊥` through the tower.**  Let `univ.erase x` and `univ.erase y` be two
faces containing the scopes of all cells of the amalgam.  A labelling of the amalgam lawful below
`(univ.erase x, j)` and `(univ.erase y, j)` extends, unchanged at the old cells of grade at most
`j`, to a labelling lawful below `(univ, j)` in the scheme reached after the grade `j`.  At each
layer `ℓ ≤ j`, the extension below `(univ, ℓ - 1)` and the old cells of grade `ℓ` are glued over
`(univ, ℓ - 1)`, `(univ.erase x, ℓ)` and `(univ.erase y, ℓ)`
(`CellScheme.Rows.IsLawfulBelow.glue₃`), and the result is extended through the new cells
(`Scheme.exists_isLawfulBelow_fieldLayer`: the orbit code read by the orbit decoder at the least
grid point, the natural strip kept).  No ambient enters, so no lift across the other coatom is
needed. -/
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


/-! ### The two coatoms and the common face -/

/-- The two points omitted by the coatoms are distinct. -/
private theorem last_ne_castSucc : (Fin.last (m + 1) : Fin (m + 2)) ≠ Fin.castSucc (Fin.last m) :=
  (Fin.castSucc_lt_last _).ne'

/-- Two distinct points omitted by the coatoms are the two points, in some order. -/
private theorem pair_cases {x y : Fin (m + 2)}
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
private theorem exists_other {x : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2)))) :
    ∃ y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))), x ≠ y := by
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨_, mem_insert_of_mem (mem_singleton_self _), last_ne_castSucc⟩
  · exact ⟨_, mem_insert_self _ _, last_ne_castSucc.symm⟩

/-- **The common face of the two coatoms is a face of the amalgam**: it is the face of the first
coatom type along `Fin.castSuccEmb`, and that type is the face of the amalgam along
`Fin.castSuccEmb`. -/
theorem common_mem_faces : (univ.erase (Fin.last (m + 1))).erase (Fin.castSucc (Fin.last m)) ∈
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
private theorem erase_mem_faces {x : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2)))) :
    univ.erase x ∈ I.amalgam.toCellScheme.faces := by
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  exacts [I.erase_last_mem_faces, I.erase_castSucc_mem_faces]

/-- A coatom has `m + 1` points. -/
private theorem card_erase (x : Fin (m + 2)) : #(univ.erase x) = m + 1 := by
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
private theorem scope_subset_or {x y : Fin (m + 2)}
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
    exact I.common_mem_faces
  · exact Nat.pos_of_ne_zero h0
  · exact (min_le_right _ _).trans (card_erase_inter_erase hx hy hxy).ge
  · change 0 < j
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

/-! ### The invariant -/

/-- The **lifting invariant** of the tower at the grade `j`: for both coatoms `univ.erase x` and
every grade `j' ≤ j`, the scheme reached after the grade `j` lifts capped from
`(univ.erase x, j')` to `(univ, j')`, at every cap self-visible at `j'` and for every lawful
ambient.  The lift is unrestricted: the step to the grade `j + 1` uses it at caps that are short at
`j + 1` but not at `j`, along ambients that are not rows of cells. -/
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
  change ((I.tower 0).fieldLayer 1 (I.not_univ_succ_le_tower 0)).rows.CappedLift _
  refine Rows.cappedLift_of_boundary (C := univ.erase x) (B := univ) (j := 0)
    (U := (univ.erase x, 1)) (V := (univ.erase y, 1))
    (O := (univ.erase x ∩ univ.erase y, min 1 m)) (erase_subset _ _) ?_
    (hwf.cappedLift _ (Or.inl rfl) _) le_rfl ⟨inter_subset_left, min_le_left _ _⟩
    ⟨inter_subset_right, min_le_left _ _⟩ ⟨erase_subset _ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩
    ?_ (Rows.cappedLift_refl _) (I.cappedLift_commonFace_tower hx hy hxy (j := 1) (by omega))
    (Scheme.extendsFromBoundary_bot_fieldLayer (hnot x) (hnot y) hcover)
    (I.exists_gradedIndex_eq_univ_tower 0) fun u hu ↦
      ⟨Scheme.isConsistent_fieldLayer I.isConsistent u, ?_, ?_, fun h hh hbot ↦
        Scheme.extendsFromBoundary_fieldLayer (fun d hd ↦ le_antisymm hd (hpos d)) (hnot x)
          (hnot y) hcover hu hh hbot⟩
  · exact I.exists_gradedIndex_eq_tower 1
      ⟨I.erase_mem_faces hx, one_pos, by rw [card_erase]; omega⟩ (ne_univ_erase x)
  · intro d hdU hdV
    have hsub := subset_inter hdU.1 hdV.1
    exact ⟨hsub, le_min hdU.2 ((hwf.grade_le_card d).trans
      ((card_le_card hsub).trans (card_erase_inter_erase hx hy hxy).le))⟩
  · intro d
    obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq hu
    exact (Scheme.isShort_ne_top_row_fieldLayer i _).1
  · intro d
    obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq hu
    exact (Scheme.isShort_ne_top_row_fieldLayer i _).2

/-- **The invariant at the grade `1`**, at every arity: the amalgam boundary
(`Seed.cappedLift_tower_one`).  No union fill arises at the grade `1`: there are no lower
layers. -/
theorem towerInvariant_one : I.TowerInvariant 1 := by
  intro x hx j' hj'
  obtain ⟨y, hy, hxy⟩ := exists_other hx
  rcases (show j' = 0 ∨ j' = 1 by omega) with rfl | rfl
  · exact (I.isWellFormed_tower 1 (by omega)).isWellFormed.cappedLift _ (Or.inl rfl) _
  · exact I.cappedLift_tower_one hx hy hxy

/-! ### The union fill -/

/-- The **union fill** of the amalgam on the coatom `D = univ.erase y`, over a face `E ⊆ D`, at
the grade `j + 1`: at every cap `h` self-visible and short at `j + 1` with `⊥ < h`, along every `a`
lawful below `(D, j + 1)`, every labelling `w` lawful below `(E, j + 1)` and below `(D, j)` that
agrees with `a` capped at `h` on the union of the two extends, unchanged on the union, to one lawful
below `(D, j + 1)` that agrees with `a` capped at `h` everywhere.

In the step from the grade `j` to `j + 1` (`Seed.extendsFromBoundary_tower`), `E` is the common face
of the two coatoms: the other coatom's cells of grade `j + 1` are filled over the union of its
lower grades and the common face at the grade `j + 1`.  This is a lift into one coatom from the
union of two pairs that do not cover it, a simultaneous lift of two faces of different grades; it
is not derived here from the bountifulness of the amalgam.  It holds when the common face has no
cell of grade `j + 1` (`Seed.unionFill_of_lt_grade`, a lift within the face).  At the grades
`2 ≤ j + 1 ≤ m` it is still to be proved. -/
def UnionFill (y : Fin (m + 2)) (E : Finset (Fin (m + 2))) (j : ℕ) : Prop :=
  ∀ h : Label.{u}, IsSelfVisible (j + 1) h → IsShort (j + 1) h → ⊥ < h →
  ∀ a : Fin I.amalgam.card → Label.{u},
    I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) (fun d ↦ a d) →
  ∀ w : Fin I.amalgam.card → Label.{u},
    I.amalgam.rows.IsLawfulBelow (E, j + 1) (fun d ↦ w d) →
    I.amalgam.rows.IsLawfulBelow (univ.erase y, j) (fun d ↦ w d) →
    (∀ d, d ∈ I.amalgam.toCellScheme.below (E, j + 1) ∨
      d ∈ I.amalgam.toCellScheme.below (univ.erase y, j) → min (w d) h = min (a d) h) →
    ∃ v : I.amalgam.toCellScheme.below (univ.erase y, j + 1) → Label.{u},
      I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) v ∧
      (∀ d : I.amalgam.toCellScheme.below (univ.erase y, j + 1),
        (d : Fin I.amalgam.card) ∈ I.amalgam.toCellScheme.below (E, j + 1) ∨
          (d : Fin I.amalgam.card) ∈ I.amalgam.toCellScheme.below (univ.erase y, j) →
            v d = w d) ∧
      ∀ d, min (v d) h = min (a d) h

/-- **The union fill within the face.**  If `E ⊆ univ.erase y` has fewer than `j + 1` points, every
cell below `(E, j + 1)` has grade at most `j`, so the union is below `(univ.erase y, j)`, and the
union fill is the lift within the face `univ.erase y` from the grade `j` to `j + 1`
(`CellScheme.Rows.cappedLift_of_fst_eq`), at every cap self-visible at `j + 1`. -/
theorem unionFill_of_lt_grade {y : Fin (m + 2)} {E : Finset (Fin (m + 2))} {j : ℕ}
    (hE : E ⊆ univ.erase y) (hj : #E < j + 1) : I.UnionFill y E j := by
  intro h hh _ _ a ha w _ hwD hag
  have hsub (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (E, j + 1)) :
      d ∈ I.amalgam.toCellScheme.below (univ.erase y, j) :=
    ⟨hd.1.trans hE, by
      have h1 := I.amalgam.isWellFormed.isWellFormed.grade_le_card d
      have h2 : #(I.amalgam.toCellScheme.scope d) ≤ #E := card_le_card hd.1
      change I.amalgam.toCellScheme.grade d ≤ j
      omega⟩
  have hDD : ((univ.erase y, j) : Finset (Fin (m + 2)) × ℕ) ≤ (univ.erase y, j + 1) :=
    ⟨subset_rfl, Nat.le_succ j⟩
  obtain ⟨v, hv, hva, hvw⟩ := (Rows.cappedLift_iff_forall_exists hDD).mp
    (Rows.cappedLift_of_fst_eq hDD rfl) h hh (fun d ↦ w d) (fun d ↦ a d) hwD ha
    fun d ↦ (hag d.1 (.inr d.2)).symm
  refine ⟨v, hv, fun d hd ↦ ?_, hva⟩
  have hdD : (d : Fin I.amalgam.card) ∈ I.amalgam.toCellScheme.below (univ.erase y, j) :=
    hd.elim (hsub d) id
  exact hvw ⟨d, hdD⟩

/-- **The union fill at the grades above the common face**: from the grade `m + 1` on, the common
face of the two coatoms, on `m` points, carries no cell of the grade, and the union fill is a lift
within the other coatom. -/
theorem unionFill_of_le {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) {j : ℕ} (hj : m ≤ j) : I.UnionFill y (univ.erase x ∩ univ.erase y) j :=
  I.unionFill_of_lt_grade inter_subset_right (by rw [card_erase_inter_erase hx hy hxy]; omega)

/-! ### The step from the grade `j` to `j + 1` -/

/-- **The boundary labelling, completed on the scheme reached after the grade `j`, by the union
fill.**  Let `C = univ.erase x` and `D = univ.erase y` be the two coatoms, `w` a labelling of the
scheme reached after the grade `j` lawful below `(C, j + 1)` and `(univ, j)`, and `a` a lawful
section of it agreeing with `w` capped at `h` (self-visible and short at `j + 1`, `⊥ < h`) on the
cells below `(C, j + 1)` or `(univ, j)`.  Under the union fill on `D`, some labelling lawful below
`(univ, j + 1)` is `w` on those cells and agrees with `a` capped at `h` at every cell below
`(univ, j + 1)`.  Below `(D, j + 1)` there are only old cells; the boundary labelling is filled
there over the union of the common face at the grade `j + 1` and `(D, j)`, read on the amalgam, and
the three pieces are glued (`CellScheme.Rows.IsLawfulBelow.glue₃`): every new cell has grade at most
`j`, and an old cell of grade `j + 1` lies on `C` or on `D`.  The new cells keep the cap of `w`;
the fill on `D` does not reach them. -/
theorem exists_isLawfulBelow_unionFill {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) {j : ℕ} (hU : I.UnionFill y (univ.erase x ∩ univ.erase y) j)
    {w : Fin (I.tower j).card → Label.{u}}
    (hwU : (I.tower j).rows.IsLawfulBelow (univ.erase x, j + 1) fun d ↦ w d)
    (hwV : (I.tower j).rows.IsLawfulBelow (univ, j) fun d ↦ w d)
    {a : Fin (I.tower j).card → Label.{u}} (ha : (I.tower j).rows.IsLawful a) {h : Label.{u}}
    (hh : IsSelfVisible (j + 1) h) (hs : IsShort (j + 1) h) (hbot : ⊥ < h)
    (hag : ∀ e, e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
      e ∈ (I.tower j).toCellScheme.below (univ, j) → min (w e) h = min (a e) h) :
    ∃ g : Fin (I.tower j).card → Label.{u},
      (I.tower j).rows.IsLawfulBelow (univ, j + 1) (fun d ↦ g d) ∧
      (∀ e, e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
        e ∈ (I.tower j).toCellScheme.below (univ, j) → g e = w e) ∧
      ∀ e ∈ (I.tower j).toCellScheme.below (univ, j + 1), min (g e) h = min (a e) h := by
  classical
  have hDne := ne_univ_erase y
  have hEne : univ.erase x ∩ univ.erase y ≠ univ := fun he ↦
    hDne (univ_subset_iff.mp (he.ge.trans inter_subset_right))
  -- The union fill, read on the amalgam.
  obtain ⟨v, hv, hvw, hva⟩ := hU h hh hs hbot (fun d ↦ a (I.towerEmbed j d))
    ((I.isLawfulBelow_tower_iff (g := a) hDne).mp (ha.isLawfulBelow _))
    (fun d ↦ w (I.towerEmbed j d))
    ((I.isLawfulBelow_tower_iff (g := w) hEne).mp
      (hwU.mono (X := (univ.erase x ∩ univ.erase y, j + 1)) ⟨inter_subset_left, le_rfl⟩))
    ((I.isLawfulBelow_tower_iff (g := w) hDne).mp
      (hwV.mono (X := (univ.erase y, j)) ⟨subset_univ _, le_rfl⟩))
    fun d hd ↦ hag _ (hd.imp
      (fun h ↦ I.towerEmbed_mem_below_iff.mpr ⟨h.1.trans inter_subset_left, h.2⟩)
      fun h ↦ I.towerEmbed_mem_below_iff.mpr ⟨h.1.trans (subset_univ _), h.2⟩)
  -- The fill, carried to the scheme reached after the grade `j`.
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
  -- The glued labelling: `w` on the boundary, the fill elsewhere below `(D, j + 1)`.
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
  -- Every cell below `(univ, j + 1)` lies below one of the three pairs.
  have hcover (e : Fin (I.tower j).card)
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
  refine ⟨g, Rows.IsLawfulBelow.glue₃ (U := (univ.erase x, j + 1)) (V := (univ, j))
    (W := (univ.erase y, j + 1)) ?_ ?_ ?_ hcover, hgb, fun e he ↦ ?_⟩
  · convert hwU using 1
    exact funext fun e ↦ hgb e (.inl e.2)
  · convert hwV using 1
    exact funext fun e ↦ hgb e (.inr e.2)
  · convert hv' using 1
    exact funext fun e ↦ hgD e e.2
  · rcases hcover e he with hb | hb | hb
    · rw [hgb e (.inl hb)]
      exact hag e (.inl hb)
    · rw [hgb e (.inr hb)]
      exact hag e (.inr hb)
    · rw [hgD e hb]
      obtain ⟨t, rfl⟩ := hold e hb
      rw [hv't t]
      exact hva t

/-- **Extension from the boundary at the grade `j + 1`, at a short positive cap, under the union
fill.**  Along the row of a new cell `u` of graded index `(univ, j + 1)`, at a cap `h` self-visible
and short at `j + 1` with `⊥ < h`, every labelling lawful below `(univ.erase x, j + 1)` and below
`(univ, j)` that agrees with the row of `u` capped at `h` on the boundary extends, unchanged there,
to a labelling lawful below `(univ, j + 1)` that agrees with the row of `u` capped at `h`
everywhere: the boundary labelling is completed below `(univ, j + 1)` in the scheme reached after
the grade `j` along the catalogue entry of `u` (`Seed.exists_isLawfulBelow_unionFill`), then
extended through the new cells (`Scheme.exists_extension_fieldLayer`, at a short cap, where the
orbit code has relative room). -/
theorem extendsFromBoundary_tower {x y : Fin (m + 2)}
    (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hy : y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))))
    (hxy : x ≠ y) {j : ℕ} (hU : I.UnionFill y (univ.erase x ∩ univ.erase y) j)
    {u : Fin (I.tower (j + 1)).card}
    (hu : (I.tower (j + 1)).toCellScheme.gradedIndex u = (univ, j + 1)) {h : Label.{u}}
    (hh : IsSelfVisible (j + 1) h) (hs : IsShort (j + 1) h) (hbot : ⊥ < h) :
    (I.tower (j + 1)).rows.ExtendsFromBoundary (univ.erase x, j + 1) (univ, j) (univ, j + 1) h
      ((I.tower (j + 1)).rows.rowBelow u hu) := by
  intro w hwU hwV hwS
  obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq (S := I.tower j) (k := j + 1)
    (hS := I.not_univ_succ_le_tower j) hu
  set a := (I.tower j).catalogueEntry (j + 1) i
  have ha := Scheme.catalogueEntry_mem (S := I.tower j) (k := j + 1) i
  have hrowBelow (d : (I.tower (j + 1)).toCellScheme.below (univ, j + 1)) :
      (I.tower (j + 1)).rows.rowBelow (Fin.natAdd _ i) hu d = (I.tower j).fieldRow (j + 1) a d.1 :=
    Scheme.fieldLayer_row_natAdd (hS := I.not_univ_succ_le_tower j) i _
  have hnotU : ¬ ((univ : Finset (Fin (m + 2))), j + 1) ≤ (univ.erase x, j + 1) :=
    fun h ↦ ne_univ_erase x (univ_subset_iff.mp h.1)
  have hnotV : ¬ ((univ : Finset (Fin (m + 2))), j + 1) ≤ (univ, j) :=
    fun h ↦ absurd h.2 (by simp only; omega)
  have hw₁U : (I.tower j).rows.IsLawfulBelow (univ.erase x, j + 1)
      fun e ↦ w (Fin.castAdd _ e) :=
    (Scheme.isLawfulBelow_appendFullCells_iff (S := I.tower j) (k := j + 1)
      (r := fun i ↦ (I.tower j).fieldRow (j + 1) ((I.tower j).catalogueEntry (j + 1) i))
      (h := I.not_univ_succ_le_tower j) (v := w) hnotU).mp hwU
  have hw₁V : (I.tower j).rows.IsLawfulBelow (univ, j) fun e ↦ w (Fin.castAdd _ e) :=
    (Scheme.isLawfulBelow_appendFullCells_iff (S := I.tower j) (k := j + 1)
      (r := fun i ↦ (I.tower j).fieldRow (j + 1) ((I.tower j).catalogueEntry (j + 1) i))
      (h := I.not_univ_succ_le_tower j) (v := w) hnotV).mp hwV
  have hgi (e : Fin (I.tower j).card) :
      ((I.tower j).fieldLayer (j + 1) (I.not_univ_succ_le_tower j)).toCellScheme.gradedIndex
        (Fin.castAdd _ e) = (I.tower j).toCellScheme.gradedIndex e :=
    Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e
  have hag (e : Fin (I.tower j).card)
      (he : e ∈ (I.tower j).toCellScheme.below (univ.erase x, j + 1) ∨
        e ∈ (I.tower j).toCellScheme.below (univ, j)) :
      min (w (Fin.castAdd _ e)) h = min (a e) h := by
    have hle : (I.tower j).toCellScheme.grade e ≤ j + 1 :=
      he.elim (·.2) fun h ↦ h.2.trans (Nat.le_succ j)
    have := hwS ⟨_, Scheme.castAdd_mem_below (hS := I.not_univ_succ_le_tower j) hle⟩ (by
      rcases he with he | he
      · left
        change ((I.tower j).fieldLayer (j + 1)
          (I.not_univ_succ_le_tower j)).toCellScheme.gradedIndex (Fin.castAdd _ e) ≤ _
        rw [hgi]
        exact he
      · right
        change ((I.tower j).fieldLayer (j + 1)
          (I.not_univ_succ_le_tower j)).toCellScheme.gradedIndex (Fin.castAdd _ e) ≤ _
        rw [hgi]
        exact he)
    rwa [hrowBelow, Scheme.fieldRow_castAdd] at this
  obtain ⟨g, hg, hgw, hga⟩ := I.exists_isLawfulBelow_unionFill hx hy hxy hU hw₁U hw₁V
    (Scheme.mem_catalogue.mp ha).1 hh hs hbot hag
  obtain ⟨r, hr, hrg, hrS⟩ := Scheme.exists_extension_fieldLayer (S := I.tower j) (k := j + 1)
    (hS := I.not_univ_succ_le_tower j) (p := g) hg ha hh hbot (.inl hs)
    fun d hd ↦ hga d ⟨subset_univ _, hd⟩
  refine ⟨r, hr, fun d hd ↦ ?_, fun d ↦ by rw [hrowBelow]; exact hrS d⟩
  obtain ⟨e, he, rfl⟩ := Scheme.exists_castAdd_eq_of_boundary (S := I.tower j) (k := j + 1)
    (hS := I.not_univ_succ_le_tower j) hnotU hnotV hd
  rw [hrg e he]
  refine hgw e (hd.imp (fun h ↦ ?_) fun h ↦ ?_)
  · change (I.tower j).toCellScheme.gradedIndex e ≤ _
    rw [← hgi]
    exact h
  · change (I.tower j).toCellScheme.gradedIndex e ≤ _
    rw [← hgi]
    exact h

/-- **The step from the grade `j` to `j + 1`, under the union fill.**  For `j ≤ m`, if the
invariant holds at the grade `j` and the union fill holds on each coatom over the common face at
the grade `j + 1`, the invariant holds at the grade `j + 1`.  The lifts at the grades `j' ≤ j` are
carried to the next scheme through the source prefix.  The lift from a coatom `C = univ.erase x` to
`(univ, j + 1)` is `CellScheme.Rows.cappedLift_of_boundaries_short`, with the invariant from
`(C, j)` to `(univ, j)` as the lift at the lower grade (used by the restoration of the lower
prescriptions) and two boundary triples:

* at the cap `⊥`: `U = (C, j + 1)`, `V = (D, j + 1)` for the other coatom `D`, and `O` the common
  face at the grade `min (j + 1) m`; the lift from `O` to `V` is a lift of the amalgam, and the
  extension from the boundary is the extension at `⊥` through the whole tower
  (`Seed.extendsFromBoundary_bot_tower`), with no union fill;
* at the positive caps: `U = (C, j + 1)`, `V = (univ, j)`, `O = (C, j)`; the lift from `O` to `V` is
  the invariant, used at every self-visible cap and along every lawful ambient, and the extension
  from the boundary along the row of each new cell of grade `j + 1`, at the short caps, is
  `Seed.extendsFromBoundary_tower`, under the union fill. -/
theorem towerInvariant_succ {j : ℕ} (hjm : j ≤ m) (hinv : I.TowerInvariant j)
    (hU : ∀ x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))),
      ∀ y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))), x ≠ y →
        I.UnionFill y (univ.erase x ∩ univ.erase y) j) :
    I.TowerInvariant (j + 1) := by
  intro x hx j' hj'
  rcases Nat.lt_or_eq_of_le hj' with hlt | rfl
  · exact I.cappedLift_tower_succ (Nat.lt_succ_iff.mp hlt)
      (hinv x hx j' (Nat.lt_succ_iff.mp hlt))
  obtain ⟨y, hy, hxy⟩ := exists_other hx
  have hlift := I.cappedLift_tower_succ le_rfl (hinv x hx j le_rfl)
  have hwf := (I.isWellFormed_tower (j + 1) (by omega)).isWellFormed
  change ((I.tower j).fieldLayer (j + 1) (I.not_univ_succ_le_tower j)).rows.CappedLift
    (X := (univ.erase x, j + 1)) (Y := (univ, j + 1)) ⟨erase_subset _ _, le_rfl⟩
  refine Rows.cappedLift_of_boundaries_short (C := univ.erase x) (B := univ) (j := j)
    (U₀ := (univ.erase x, j + 1)) (V₀ := (univ.erase y, j + 1))
    (O₀ := (univ.erase x ∩ univ.erase y, min (j + 1) m))
    (U := (univ.erase x, j + 1)) (V := (univ, j)) (O := (univ.erase x, j))
    (erase_subset _ _) ?_ hlift le_rfl ⟨inter_subset_left, min_le_left _ _⟩
    ⟨inter_subset_right, min_le_left _ _⟩ ⟨erase_subset _ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩
    ?_ (Rows.cappedLift_refl _) (I.cappedLift_commonFace_tower hx hy hxy (by omega))
    (I.extendsFromBoundary_bot_tower (I.scope_subset_or hx hy hxy) (j + 1))
    le_rfl ⟨subset_rfl, Nat.le_succ j⟩ ⟨subset_univ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩
    ⟨subset_rfl, Nat.le_succ j⟩ (fun d hdU hdV ↦ ⟨hdU.1, hdV.2⟩) (Rows.cappedLift_refl _) hlift
    (I.exists_gradedIndex_eq_univ_tower j) fun u hu ↦
      ⟨I.isConsistent_tower (j + 1) u, ?_, ?_, fun h hh hs hbot ↦
        I.extendsFromBoundary_tower hx hy hxy (hU x hx y hy hxy) hu hh hs hbot⟩
  · exact I.exists_gradedIndex_eq_tower (j + 1)
      ⟨I.erase_mem_faces hx, Nat.succ_pos j, by rw [card_erase]; omega⟩ (ne_univ_erase x)
  · intro d hdU hdV
    have hsub := subset_inter hdU.1 hdV.1
    exact ⟨hsub, le_min hdU.2 ((hwf.grade_le_card d).trans
      ((card_le_card hsub).trans (card_erase_inter_erase hx hy hxy).le))⟩
  · intro d
    obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq (S := I.tower j) (k := j + 1)
      (hS := I.not_univ_succ_le_tower j) hu
    exact (Scheme.isShort_ne_top_row_fieldLayer i _).1
  · intro d
    obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq (S := I.tower j) (k := j + 1)
      (hS := I.not_univ_succ_le_tower j) hu
    exact (Scheme.isShort_ne_top_row_fieldLayer i _).2

/-- **The invariant up to the grade `m + 1`, under the union fill at the grades `2` to `m`.**  The
base is the grade `1` (`Seed.towerInvariant_one`); the steps are `Seed.towerInvariant_succ`; at the
step to the grade `m + 1` the union fill holds within the face (`Seed.unionFill_of_le`).  So the
union fill is needed only at the grades `j + 1` with `2 ≤ j + 1 ≤ m`. -/
theorem towerInvariant_of_unionFill
    (hU : ∀ j, 1 ≤ j → j < m →
      ∀ x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))),
      ∀ y ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))), x ≠ y →
        I.UnionFill y (univ.erase x ∩ univ.erase y) j) :
    ∀ j ≤ m + 1, I.TowerInvariant j
  | 0, _ => I.towerInvariant_zero
  | 1, _ => I.towerInvariant_one
  | j + 2, hj => I.towerInvariant_succ (by omega)
      (towerInvariant_of_unionFill hU (j + 1) (by omega))
      fun x hx y hy hxy ↦ if hjm : j + 1 < m then hU (j + 1) (by omega) hjm x hx y hy hxy
        else I.unionFill_of_le hx hy hxy (by omega)

/-- **The invariant up to the grade `m + 1` at the arities `m ≤ 1`**, with no union fill: there are
no grades `j + 1` with `2 ≤ j + 1 ≤ m`. -/
theorem towerInvariant_of_le_one (hm : m ≤ 1) : ∀ j ≤ m + 1, I.TowerInvariant j :=
  I.towerInvariant_of_unionFill fun _ hj hjm ↦ absurd hjm (by omega)

end Seed

end VaughtConjecture
