/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Stage.Bountiful
import VaughtConjecture.Stage.Countable

/-!
# Legal schemes and legal stage types

Roadmap, Layer 1 (countable stage types and exact partial face maps; stage-reduction coherence;
bountifulness); semantic contract, items 3–4; the expositions, §1–2.

A stage type (`StageType α n`) is the unrestricted structure: a well-formed scheme with coded rows
and a lawful label section at stage `α`.  Nothing forces its rows to be consistent, bountiful, or
complete.  The types of [Kni26, Definition 3.1.1] are built over a domain with its semantics
([Kni26, Definition 2.6.1]), whose semantics is coded, consistent, bountiful, and complete; this
is **legality**.  Definition 2.6.1 also asks that `⟨B,j⟩`, `P↾B`, `D⟨B,j⟩`, and `E⟨B,j⟩` be
recoverable from a cell; here that holds by representation (the rows are a field of the scheme),
and `Scheme.IsCoded` is only the range normalisation of [Kni26, Lemma 2.5.13].

* `Scheme.IsLegal S`: the scheme is well formed, its rows are coded (`Scheme.IsCoded`),
  consistent (`CellScheme.Rows.IsConsistent`), and bountiful (`CellScheme.Rows.IsBountiful`), and
  it is complete (`CellScheme.IsComplete`).  Legality passes to the restriction to a closed face
  (`IsLegal.comap`) and to reindexing along a bijection of points (`IsLegal.reindex`).
* `StageType.IsLegal t`: the scheme of `t` is legal.  Since a stage type is already well formed
  with coded rows, this is consistency, bountifulness, and completeness (`StageType.isLegal_iff`).
  Legal stage types are closed under the face maps where defined (`IsLegal.restrictFace`),
  reindexing (`IsLegal.reindex`), and stage reduction (`isLegal_reduce_iff`); at a stage with
  countably many ordinals below it there are countably many of them on `n` points
  (`countable_setOf_isLegal`, from `StageType.countable`), the faithful form of
  [Kni26, Proposition 3.1.4].

**Reduction and the stage.**  `StageType.reduce` takes no bound relating the target stage `β` to
the stage `α` of the type.  For `β ≤ α` it is the reduction of [Kni26, Definition 3.1.2], whose
content is `StageType.reduce_label` with `Label.reduce_of_lt` (a label below `β` is kept) and
`Label.reduce_eq_top_iff` (a label at or above `β` becomes the formal top).  For `α ≤ β` it
changes no label (`StageType.reduce_label_of_le`) and only relabels the stage:
`t.reduce hβ = t.castLE hαβ` (`reduce_eq_castLE`), where `castLE` reads a stage type at stage `α`
as one at the larger stage `β`.  Relabelling is invisible to reduction (`reduce_castLE`) and to
legality (`isLegal_castLE_iff`).

**Lifting across a face restriction.**  The cell map of the restriction along `f` maps the cells
below a pair onto the cells below its image (`Scheme.image_cellMap_below`), so the restricted rows
lift capped (`CellScheme.Rows.CappedLift`) between two pairs exactly when the rows lift capped
between their images (`Scheme.cappedLift_comap_iff`).  In particular a type whose face along `f`
is defined and bountiful lifts capped between the images of the graded faces of that face, with no
assumption on its rows outside the face (`StageType.cappedLift_of_restrictFace`).

## Placement

`StageType.castLE`, `castLE_toScheme`, `castLE_label`, `castLE_refl`, `castLE_castLE`,
`reduce_eq_castLE`, and `reduce_castLE` belong in the "Stage reduction" section of
`VaughtConjecture.Stage.Basic`, beside `StageType.reduce_label_of_le` and `StageType.reduce_self`;
only `isLegal_castLE_iff` stays here.  `Scheme.cappedLift_comap_iff` belongs in
`VaughtConjecture.Stage.Bountiful`, beside `Scheme.isBountiful_comap`, and
`Scheme.image_cellMap_below` belongs in `VaughtConjecture.Stage.Scheme`, beside
`Scheme.map_comap_gradedIndex`.  They are stated here so that those files are unchanged.

## References

Types are [Kni26, Definition 3.1.1], over the domains with their semantics of
[Kni26, Definition 2.6.1]; coding, consistency, bountifulness, and completeness of a semantics are
[Kni26, Lemma 2.5.13 and Definitions 2.5.12, 2.5.14, and 2.5.15]; stage reduction and the
restriction to a face of the plan are [Kni26, Definition 3.1.2], the preservation of the
laws under restriction is [Kni26, Lemma 2.5.5 and Proposition 2.6.3], and the countability of
the type spaces is [Kni26, Proposition 3.1.4], for R. W. Knight,
*A counterexample to Vaught's Conjecture using generalised Stone spaces* (draft, 20 February
2026).
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Legal schemes -/

namespace Scheme

variable {n m : ℕ} (S : Scheme.{u} n) (f : Fin m ↪ Fin n)

/-- A scheme on `n` points is **legal**: it is well formed, and its rows are coded, consistent,
and bountiful, and it is complete; that is, it is a domain with a semantics as required for the
types of [Kni26, Definition 3.1.1].  The recoverability of `⟨B,j⟩`, `P↾B`, `D⟨B,j⟩`, and
`E⟨B,j⟩` from a cell in [Kni26, Definition 2.6.1] holds by representation (the rows are a field of
the scheme); `IsCoded` is only the range normalisation of [Kni26, Lemma 2.5.13]. -/
structure IsLegal : Prop where
  /-- The scheme is well formed. -/
  isWellFormed : S.IsWellFormed
  /-- The rows are coded. -/
  isCoded : S.IsCoded
  /-- The rows are consistent. -/
  isConsistent : S.rows.IsConsistent
  /-- The rows are bountiful. -/
  isBountiful : S.rows.IsBountiful
  /-- Every graded face is the graded index of a cell. -/
  isComplete : S.toCellScheme.IsComplete

variable {S}

/-- **Restriction to a closed face** of a legal scheme is legal. -/
theorem IsLegal.comap (hS : S.IsLegal) (hf : univ.map f ∈ S.toCellScheme.faces) :
    (S.comap f).IsLegal where
  isWellFormed := hS.isWellFormed.comap f hf
  isCoded := hS.isCoded.comap f
  isConsistent := isConsistent_comap f hS.isConsistent
  isBountiful := isBountiful_comap f hS.isBountiful
  isComplete := isComplete_comap f hS.isComplete

/-- **Reindexing** a legal scheme along a bijection of points gives a legal scheme. -/
theorem IsLegal.reindex (hS : S.IsLegal) (e : Fin m ≃ Fin n) :
    (S.comap e.toEmbedding).IsLegal :=
  hS.comap _ (by simpa [map_univ_equiv] using hS.isWellFormed.univ_mem_faces)

/-! ### Capped lifting across a face restriction -/

variable (S)

/-- The cell map of the restriction along `f` maps the cells below a pair onto the cells below its
image. -/
theorem image_cellMap_below (X : Finset (Fin m) × ℕ) :
    S.cellMap f '' (S.comap f).toCellScheme.below X =
      S.toCellScheme.below (Prod.map (Finset.map f) id X) := by
  have h : S.cellMap f '' (S.comap f).toCellScheme.below X =
      Subtype.val '' (S.cellEquiv f '' (S.cellEquiv f ⁻¹' (S.toCellScheme.comap f).below X)) := by
    rw [Set.image_image]
    rfl
  rw [h, Equiv.image_preimage]
  exact CellScheme.image_val_below_comap _ f X

/-- The restricted rows lift capped from `X` to `Y` exactly when the rows lift capped between the
images of `X` and `Y`. -/
theorem cappedLift_comap_iff {X Y : Finset (Fin m) × ℕ} (h : X ≤ Y) :
    (S.comap f).rows.CappedLift h ↔
      S.rows.CappedLift (X := Prod.map (Finset.map f) id X) (Y := Prod.map (Finset.map f) id Y)
        ⟨map_subset_map.mpr h.1, h.2⟩ :=
  CellScheme.Rows.cappedLift_comap_iff (S.isLowerEmbedding_comap f) (S.image_cellMap_below f X)
    (S.image_cellMap_below f Y) rfl

end Scheme

/-! ### Legal stage types -/

namespace StageType

variable {α β γ : Ordinal.{u}} {n m : ℕ} (t : StageType.{u} α n) (f : Fin m ↪ Fin n)

/-- A stage type is **legal** when its scheme is legal: its rows are consistent and bountiful and
its scheme is complete [Kni26, Definition 3.1.1].  A `StageType` alone is the unrestricted
structure. -/
def IsLegal : Prop := t.toScheme.IsLegal

variable {t}

/-- A stage type is legal exactly when its rows are consistent and bountiful and its scheme is
complete; well-formedness and coding are part of every stage type. -/
theorem isLegal_iff :
    t.IsLegal ↔ t.rows.IsConsistent ∧ t.rows.IsBountiful ∧ t.toCellScheme.IsComplete :=
  ⟨fun h ↦ ⟨h.isConsistent, h.isBountiful, h.isComplete⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ⟨t.isWellFormed, t.isCoded, h₁, h₂, h₃⟩⟩

/-- The restriction of a legal stage type to a closed face is legal. -/
theorem IsLegal.comap (ht : t.IsLegal) (hf : univ.map f ∈ t.toCellScheme.faces) :
    (t.comap f hf).IsLegal :=
  Scheme.IsLegal.comap f ht hf

/-- **Face maps preserve legality**: a defined face of a legal stage type is legal. -/
theorem IsLegal.restrictFace (ht : t.IsLegal) {u : StageType.{u} α m}
    (hu : restrictFace f t = some u) : u.IsLegal := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t f).mp hu
  exact ht.comap f hf

/-- Reindexing a legal stage type along a bijection of points gives a legal stage type. -/
theorem IsLegal.reindex (ht : t.IsLegal) (e : Fin m ≃ Fin n) : (t.reindex e).IsLegal :=
  ht.comap _ _

/-- **Stage reduction preserves legality**: reduction keeps the scheme. -/
@[simp] theorem isLegal_reduce_iff (hβ : Order.IsSuccPrelimit β) :
    (t.reduce hβ).IsLegal ↔ t.IsLegal :=
  Iff.rfl

/-- Stage reduction of a legal stage type is legal. -/
theorem IsLegal.reduce (ht : t.IsLegal) (hβ : Order.IsSuccPrelimit β) : (t.reduce hβ).IsLegal :=
  ht

/-- **Countably many legal stage types**: if there are countably many ordinals below the stage
`α`, there are countably many legal stage types at stage `α` on `n` points.  This is the faithful
form of [Kni26, Proposition 3.1.4]: the type space at stage `α` on `n` points is the set of legal
stage types. -/
theorem countable_setOf_isLegal (hα : (Set.Iio α).Countable) (n : ℕ) :
    {t : StageType.{u} α n | t.IsLegal}.Countable :=
  have := StageType.countable hα n
  Set.to_countable _

/-! ### Reduction and relabelling of the stage -/

variable (t)

/-- A stage type at stage `α` read at a larger stage `β`: the same scheme and labels, each of
which occurs at stage `β`. -/
def castLE (h : α ≤ β) : StageType.{u} β n :=
  { t with atStage := fun d ↦ (t.atStage d).mono h }

/-- Relabelling the stage keeps the scheme. -/
@[simp] theorem castLE_toScheme (h : α ≤ β) : (t.castLE h).toScheme = t.toScheme := rfl

/-- Relabelling the stage keeps the labels. -/
@[simp] theorem castLE_label (h : α ≤ β) (d : Fin t.card) : (t.castLE h).label d = t.label d :=
  rfl

/-- Relabelling to the same stage is the identity. -/
@[simp] theorem castLE_refl : t.castLE le_rfl = t := rfl

/-- Relabelling twice is relabelling once. -/
@[simp] theorem castLE_castLE (h : α ≤ β) (h' : β ≤ γ) :
    (t.castLE h).castLE h' = t.castLE (h.trans h') :=
  rfl

/-- Relabelling the stage does not change legality. -/
@[simp] theorem isLegal_castLE_iff (h : α ≤ β) : (t.castLE h).IsLegal ↔ t.IsLegal :=
  Iff.rfl

/-- **Reduction to a larger stage only relabels the stage**: for `α ≤ β`, the reduction of a
stage type at stage `α` to `β` is the type itself, read at stage `β`. -/
theorem reduce_eq_castLE (hβ : Order.IsSuccPrelimit β) (h : α ≤ β) :
    t.reduce hβ = t.castLE h :=
  ext rfl fun i j hij ↦ by
    rw [Fin.ext hij]
    exact t.reduce_label_of_le hβ h j

/-- Reduction does not see the stage at which a type is read. -/
@[simp] theorem reduce_castLE (h : α ≤ β) (hγ : Order.IsSuccPrelimit γ) :
    (t.castLE h).reduce hγ = t.reduce hγ :=
  rfl

/-! ### Capped lifting across a defined face -/

/-- **Lifting across a defined face.**  If the face map of `t` along `f` is defined with
bountiful rows, then the rows of `t` lift capped between the images of any two graded faces
`X ≤ Y` of that face.  Nothing is assumed about the rows of `t` outside the face. -/
theorem cappedLift_of_restrictFace {u : StageType.{u} α m} (hu : restrictFace f t = some u)
    (hb : u.rows.IsBountiful) {X Y : Finset (Fin m) × ℕ} (hX : X ∈ u.toCellScheme.gradedFaces)
    (hY : Y ∈ u.toCellScheme.gradedFaces) (h : X ≤ Y) :
    t.rows.CappedLift (X := Prod.map (Finset.map f) id X) (Y := Prod.map (Finset.map f) id Y)
      ⟨map_subset_map.mpr h.1, h.2⟩ := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t f).mp hu
  exact (t.toScheme.cappedLift_comap_iff f h).mp (hb.cappedLift hX hY h)

end StageType

end VaughtConjecture
