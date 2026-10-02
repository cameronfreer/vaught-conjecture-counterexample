/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Classical
import VaughtConjecture.Extension.PinnedExtension
import VaughtConjecture.Language.HullOperations

/-!
# The finite age of top-free charts and its hereditary property

Roadmap, the section "The top-free witnesses: the finite age and its classical limit", step 1
(finite top-free charts) and the hereditary half of step 2; semantic contract, item 12 (the age of
top-free charts is closed under reindexing and restriction to closed faces).

A stage type is **top-free** (`StageType.IsTopFree`) when no cell carries the label `⊤`.  Top-free
stage types are closed under restriction to closed faces and reindexing
(`StageType.IsTopFree.comap`, `StageType.IsTopFree.restrictFace`, `StageType.IsTopFree.reindex`);
every stage type on no points is top-free (`StageType.isTopFree_of_zero`), and so is the bottom
labelling of a legal scheme (`Scheme.IsLegal.isTopFree_toStageType`).  With the closure of
legality under the same operations (`StageType.IsLegal.comap`, `StageType.IsLegal.reindex`), the
legal top-free stage types at a stage form an age in the sense of semantic contract, item 12.

**The family and the age.**  A **top-free index** at stage `α` (`TopFreeIndex α`) is a legal
top-free stage type at `α` on some finite number of points.  Its **top-free chart**
(`topFreeChart α i`) is the chart of the stage type (`StageType.Chart`), a finite structure of the
hull language `hullLanguage α` whose relations are literally the closed faces with their types,
bundled in `Type`.  The **age of top-free charts** (`topFreeAge α`) is the representative class of
this family: the structures isomorphic to a top-free chart.

**Step 1.**  The index is inhabited, by the chart on no points (`TopFreeIndex.empty`), with no
hypothesis on `α`; it is countable when there are countably many ordinals below `α`
(`countable_topFreeIndex`, an instance at `ω`); every top-free chart is finite, hence countable,
and finitely generated (`fg_topFreeChart`).

**The hereditary property** (half of step 2).  Every substructure of a top-free chart is
isomorphic to a top-free chart (`exists_equiv_topFreeChart`): it is the chart of the literal
restriction of the stage type to a closed face (`StageType.exists_equiv_comap`), which is legal and
top-free.  This is the hypothesis of `representativeClass_hereditary`, so the age is hereditary
(`hereditary_topFreeAge`); it has countably many isomorphism types when there are countably many
ordinals below `α` (`countable_quotient_topFreeAge`).  Nothing here assumes the coatom extension
property.

**What this file does not contain.**

* **Joint embedding and amalgamation** (the other half of step 2): two top-free charts with chart
  embeddings of a common chart are amalgamated by `StageType.exists_amalgam`, and the amalgam is
  capped at a proper cap self-visible at its arity and above every label of the two charts
  (`CellScheme.Rows.IsLawful.min_const_of_isSelfVisible`); joint embedding is amalgamation over
  the empty chart.  These will need the hypotheses `StageType.HasCoatomExtensions α`, `0 < α`, and
  `Order.IsSuccPrelimit α`.
* **Classical existence** (step 3): `exists_isFraisseLimit_representativeClass`, with the
  countability of the index (`countable_topFreeIndex`) and of the function symbols
  (`hullLanguage.countable_functions`) supplied by `haveI`.
* **Finite-age reconstruction** (steps 4–7).

**Dependencies.**  This is the first module of the library that imports ComputableModelTheory, and
it does so only through its classical entry module `ComputableModelTheory.Classical`, for
`FirstOrder.Language.representativeClass` and its properties.
`VaughtConjecture.Extension.PinnedExtension` is imported only for the stage types on no points
(`StageType.card_eq_zero`) and the one-point scheme with its bottom labelling (`Scheme.onePoint`,
`Scheme.IsLegal.toStageType`); no module of `VaughtConjecture.Construction` is imported.

## Placement

This file belongs to the section on the top-free witnesses of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open FirstOrder Language Structure Finset CategoryTheory
open scoped Ordinal

/-! ### Top-free stage types -/

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-- A stage type is **top-free** when no cell carries the label `⊤`. -/
def IsTopFree (t : StageType.{u} α n) : Prop :=
  ∀ d, t.label d ≠ ⊤

variable {t : StageType.{u} α n}

/-- The restriction of a top-free stage type to a closed face is top-free: its labels are labels
of the stage type. -/
theorem IsTopFree.comap (ht : t.IsTopFree) {f : Fin m ↪ Fin n}
    (hf : univ.map f ∈ t.toCellScheme.faces) : (t.comap f hf).IsTopFree :=
  fun _ ↦ ht _

/-- A face of a top-free stage type is top-free. -/
theorem IsTopFree.restrictFace (ht : t.IsTopFree) {f : Fin m ↪ Fin n} {u : StageType.{u} α m}
    (hu : restrictFace f t = some u) : u.IsTopFree := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t f).mp hu
  exact ht.comap hf

/-- A reindexing of a top-free stage type is top-free. -/
theorem IsTopFree.reindex (ht : t.IsTopFree) (e : Fin m ≃ Fin n) : (t.reindex e).IsTopFree :=
  ht.comap _

/-- A stage type on no points is top-free: it has no cells (`card_eq_zero`). -/
theorem isTopFree_of_zero (t : StageType.{u} α 0) : t.IsTopFree := fun d ↦
  (Fin.cast t.card_eq_zero d).elim0

end StageType

/-- The bottom labelling of a legal scheme is top-free. -/
theorem Scheme.IsLegal.isTopFree_toStageType {n : ℕ} {S : Scheme.{u} n} (hS : S.IsLegal)
    (α : Ordinal.{u}) : (hS.toStageType α).IsTopFree :=
  fun _ ↦ bot_ne_top

/-! ### The family of top-free charts -/

/-- A **top-free index** at stage `α`: a legal top-free stage type at stage `α` on some finite
number of points. -/
def TopFreeIndex (α : Ordinal.{u}) : Type (u + 1) :=
  Σ k : ℕ, {P : StageType.{u} α k // P.IsLegal ∧ P.IsTopFree}

/-- The **top-free chart** of a top-free index: the chart of its stage type, a finite structure of
the hull language whose relations are its closed faces with their types, bundled in `Type`. -/
noncomputable def topFreeChart (α : Ordinal.{u}) (i : TopFreeIndex.{u} α) :
    Bundled.{0} (hullLanguage.{u} α).Structure :=
  ⟨i.2.1.Chart, inferInstance⟩

/-- The **age of top-free charts** at stage `α`: the structures of the hull language isomorphic to
a top-free chart, the representative class of the top-free charts. -/
def topFreeAge (α : Ordinal.{u}) : Set (Bundled.{0} (hullLanguage.{u} α).Structure) :=
  representativeClass (topFreeChart α)

namespace TopFreeIndex

variable (α : Ordinal.{u})

/-- The legal one-point stage type with the bottom label, as a top-free index: the one-point
scheme with its bottom labelling. -/
noncomputable def point : TopFreeIndex.{u} α :=
  ⟨1, Scheme.isLegal_onePoint.toStageType α, Scheme.isLegal_onePoint.isLegal_toStageType α,
    Scheme.isLegal_onePoint.isTopFree_toStageType α⟩

/-- The empty face of a stage type on one point is closed. -/
private theorem map_ofIsEmpty_mem_faces (t : StageType.{u} α 1) :
    univ.map (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin 1) ∈ t.toCellScheme.faces :=
  (StageType.isSome_restrictFace_iff t _).mp (t.isSome_restrictFace_of_zero _)

/-- The **empty chart**, as a top-free index: the restriction of the one-point stage type to its
empty face, the only stage type on no points (`StageType.eq_of_zero`). -/
noncomputable def empty : TopFreeIndex.{u} α :=
  ⟨0, (point α).2.1.comap _ (map_ofIsEmpty_mem_faces α _), (point α).2.2.1.comap _ _,
    StageType.isTopFree_of_zero _⟩

/-- There is a top-free index at every stage: the empty chart. -/
noncomputable instance : Nonempty (TopFreeIndex.{u} α) :=
  ⟨empty α⟩

end TopFreeIndex

variable {α : Ordinal.{u}}

/-- **Countably many top-free indices**: if there are countably many ordinals below the stage `α`,
there are countably many top-free indices at stage `α`. -/
theorem countable_topFreeIndex (hα : (Set.Iio α).Countable) : Countable (TopFreeIndex.{u} α) := by
  have := StageType.countable hα
  exact inferInstanceAs (Countable (Σ k : ℕ, {P : StageType.{u} α k // P.IsLegal ∧ P.IsTopFree}))

/-- There are countably many top-free indices at stage `ω`. -/
instance countable_topFreeIndex_omega : Countable (TopFreeIndex.{u} ω) :=
  countable_topFreeIndex (Set.countable_coe_iff.mp countable_Iio_omega0_coe)

/-- A top-free chart is finite. -/
instance (i : TopFreeIndex.{u} α) : Finite (topFreeChart α i) :=
  inferInstanceAs (Finite (Fin i.1))

/-- A top-free chart is finitely generated. -/
theorem fg_topFreeChart (i : TopFreeIndex.{u} α) :
    Structure.FG (hullLanguage.{u} α) (topFreeChart α i) :=
  Structure.FG.of_finite

/-- A top-free chart belongs to the age of top-free charts. -/
theorem topFreeChart_mem_topFreeAge (i : TopFreeIndex.{u} α) : topFreeChart α i ∈ topFreeAge α :=
  mem_representativeClass _ i

/-- The age of top-free charts is nonempty: it contains the empty chart. -/
theorem nonempty_topFreeAge : (topFreeAge α).Nonempty :=
  representativeClass_nonempty _

/-- The members of the age of top-free charts are finitely generated. -/
theorem fg_of_mem_topFreeAge {M : Bundled.{0} (hullLanguage.{u} α).Structure}
    (hM : M ∈ topFreeAge α) : Structure.FG (hullLanguage.{u} α) M :=
  representativeClass_fg _ fg_topFreeChart hM

/-! ### The hereditary property -/

/-- **Substructures of top-free charts are top-free charts**: every substructure of a top-free
chart, with the induced structure, is isomorphic to a top-free chart, the chart of the literal
restriction of its stage type to the closed face of its points (`StageType.exists_equiv_comap`).
This is the hypothesis of `representativeClass_hereditary`; finite generation of the substructure
is not needed. -/
theorem exists_equiv_topFreeChart (i : TopFreeIndex.{u} α)
    (S : (hullLanguage.{u} α).Substructure (topFreeChart α i)) (_ : S.FG) :
    ∃ j : TopFreeIndex.{u} α, Nonempty (S ≃[hullLanguage.{u} α] topFreeChart α j) := by
  obtain ⟨m, g, hg, -, hS⟩ := StageType.exists_equiv_comap i.2.2.1 S
  exact ⟨⟨m, i.2.1.comap g hg, i.2.2.1.comap g hg, i.2.2.2.comap hg⟩, hS⟩

/-- **The age of top-free charts is hereditary.** -/
theorem hereditary_topFreeAge : Hereditary (topFreeAge.{u} α) :=
  representativeClass_hereditary _ exists_equiv_topFreeChart

/-- **Countably many isomorphism types**: if there are countably many ordinals below the stage
`α`, the age of top-free charts at `α` has countably many isomorphism types. -/
theorem countable_quotient_topFreeAge (hα : (Set.Iio α).Countable) :
    (Quotient.mk' '' topFreeAge.{u} α).Countable :=
  haveI := countable_topFreeIndex hα
  representativeClass_countable_quotient _

end VaughtConjecture
