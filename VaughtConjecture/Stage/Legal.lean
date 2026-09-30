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
`t.reduce hβ = t.castLE hαβ` (`StageType.reduce_eq_castLE`, in `VaughtConjecture.Stage.Basic`),
where `castLE` reads a stage type at stage `α` as one at the larger stage `β`.  Relabelling is
invisible to reduction (`StageType.reduce_castLE`) and to legality (`isLegal_castLE_iff`).

**Lifting across a defined face.**  The restricted rows lift capped
(`CellScheme.Rows.CappedLift`) between two pairs exactly when the rows lift capped between their
images (`Scheme.cappedLift_comap_iff`, in `VaughtConjecture.Stage.Bountiful`).  In particular a
type whose face along `f` is defined and bountiful lifts capped between the images of the graded
faces of that face, with no assumption on its rows outside the face
(`StageType.cappedLift_of_restrictFace`).

## References

Types are [Kni26, Definition 3.1.1], over the domains with their semantics of
[Kni26, Definition 2.6.1]; coding, consistency, bountifulness, and completeness of a semantics are
[Kni26, Lemma 2.5.13 and Definitions 2.5.12, 2.5.14, and 2.5.15]; stage reduction and the
restriction to a face of the plan are [Kni26, Definition 3.1.2], the preservation of the
laws under restriction is [Kni26, Lemma 2.5.5 and Proposition 2.6.3], and the countability of
the type spaces is [Kni26, Proposition 3.1.4].
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

/-! ### Relabelling the stage -/

variable (t)

/-- Relabelling the stage does not change legality. -/
@[simp] theorem isLegal_castLE_iff (h : α ≤ β) : (t.castLE h).IsLegal ↔ t.IsLegal :=
  Iff.rfl

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
