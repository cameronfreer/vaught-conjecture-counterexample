/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GlobalRowAnchor

/-!
# Which occurrences carry a cell

Roadmap, Layer 4 (cover-hollowness and the anchor definition of hollowness); semantic contract,
item 8.  A research file: for the same-cell relation `Realization.IsSameCell` of
`VaughtConjecture.Continuation.GlobalRowAnchor`, the occurrences in which a given cell has a
representative are exactly those whose points contain the scope of the cell, read on the
carrier.

**The test** (`Realization.existsUnique_isSameCell_iff`).  Under exact consistency and covering,
a cell `a` of the type of an occurrence `x` is the same cell as exactly one cell of the type of
an occurrence `y` if and only if its scope, read on the carrier,
`(x.type.toCellScheme.scope a).map x.tuple`, lies in the points `y.support = univ.map y.tuple`
of `y`.  Premises by direction:

* (→) exact consistency only (`Realization.IsSameCell.scope_map_subset_support`): the same cell
  has the same scope on the carrier (`Realization.IsSameCell.scope_map_eq`), and the scope of a
  cell of `y` lies in the points of `y`;
* (←) exact consistency and an occurrence `u` above both `x` and `y`
  (`Realization.exists_isSameCell_of_le`), which covering provides
  (`Realization.IsCovering.isDirected`); covering enters only there.  The cell of `u` at the
  position of `a` on the face of `x` has scope inside the face of `y` in `u`, so it is the cell
  at some position of that face (`StageType.exists_isFaceCell_of_scope_subset`), a cell of `y`;
* uniqueness: exact consistency (`Realization.IsSameCell.unique`).

**Which cells an occurrence carries** (`Realization.exists_isSameCell_iff`).  The test minus
uniqueness: under exact consistency and covering, the class of `a` under the same-cell relation
has a representative in `y` exactly when the scope of `a` on the carrier lies in the points of
`y`.  The right-hand side is an invariant of the class (`Realization.IsSameCell.scope_map_eq`),
and two cells of `y` in one class are equal (`Realization.IsSameCell.eq`), so the cells of `y`
are in bijection with the classes whose scope on the carrier lies in the points of `y`.  That
statement is fully expressed over representatives, and no quotient by the same-cell relation is
introduced.  Its form between two occurrences is `Realization.sameCellEquiv`: the cells of `x`
whose scope on the carrier lies in the points of `y` correspond, by the same cell, to the cells
of `y` whose scope on the carrier lies in the points of `x`.

**Open.**  The statements here concern realizations of this repository and the positional cells
of their types, and nothing here assumes strong coding.  The reconstruction of the printed coded
domains of [Kni26, Definition 3.2.5, p. 31] is not addressed; what remains to be established for
it are correspondence requirements, not hypotheses shown to be necessary:

* codes: the cells here are positions, with the codes of the cells forgotten (roadmap,
  `IMPLEMENTATION.md`, "Manuscript concordance", note 7); no map from classes under the same cell
  to the printed coded elements is defined;
* identification: the same-cell relation keeps distinct cells of one type distinct
  (`Realization.IsSameCell.eq`), and the scope, grade and label of a cell are not used as a
  criterion of identification; no compiled example is given either way of two distinct cells
  sharing them, and no coding separating the classes is assumed;
* domains: the printed domain of the type of a tuple is not matched with the cells of an
  occurrence; that needs the correspondence between the models of `S^α` of
  [Kni26, Definition 3.2.1] and the models of this repository, which is not addressed;
* values and semantics: labels, rows and below-domains are invariant under the same cell
  (`Realization.IsSameCell.label_eq`, `IsSameCell.rowAt_eq`, `IsSameCell.mem_below_iff`), and
  their correspondence with the printed values and semantics is not addressed;
* tuples without a type: they enter here only through covering, and the printed domains of
  arbitrary finite sets are not compared.

## Placement

This file belongs to Layer 4 of `roadmap/README.md` (research).

## References

The value of an element allotted by the model is [Kni26, Definition 3.2.5 and Lemma 3.2.6,
p. 31].
-/

universe u v

namespace VaughtConjecture

open Finset

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}
  {x y : R.Occurrence} {a : Fin x.type.card} {e : Fin y.type.card}

/-- **The scope of the same cell lies in the points of each occurrence carrying it**, under
exact consistency: if `a` and `e` are the same cell, the scope of `a` on the carrier lies in the
points of `y`. -/
theorem IsSameCell.scope_map_subset_support (hR : R.IsConsistent) (h : R.IsSameCell x a y e) :
    (x.type.toCellScheme.scope a).map x.tuple ⊆ y.support := by
  rw [← h.scope_map_eq hR]
  exact map_subset_map.mpr (subset_univ _)

/-- **A cell has a representative in every occurrence containing its scope**, given an
occurrence `u` above `x` and `y`, under exact consistency.  The cell `a'` of `u` at the position
of `a` on the face of `x` is the same cell as `a`; its scope lies in the face of `y` in `u`, so
`a'` is the cell at the position of a cell `e` of `y` on that face. -/
theorem exists_isSameCell_of_le (hR : R.IsConsistent) {u : R.Occurrence} (hxu : x ≤ u)
    (hyu : y ≤ u) (hs : (x.type.toCellScheme.scope a).map x.tuple ⊆ y.support) :
    ∃ e : Fin y.type.card, R.IsSameCell x a y e := by
  obtain ⟨f, hf, -⟩ := (Occurrence.le_iff_exists_restrictFace hR).mp hxu
  obtain ⟨g, hg, -⟩ := (Occurrence.le_iff_exists_restrictFace hR).mp hyu
  obtain ⟨a', -, ha'⟩ := exists_isSameCell_of_trans_eq hR hf a
  have hs' : u.type.toCellScheme.scope a' ⊆ univ.map g := by
    refine (map_subset_map (f := u.tuple)).mp ?_
    rw [ha'.scope_map_eq hR, Finset.map_map, hg]
    exact hs
  obtain ⟨c, hc⟩ := StageType.exists_isFaceCell_of_scope_subset hs'
  let e : Fin y.type.card := ⟨c, lt_card_of_isFaceCell hR hg hc⟩
  exact ⟨e, ha'.trans hR (isSameCell_of_trans_eq (x := y) (a := e) hg hc).symm⟩

/-- **Which cells an occurrence carries**, under exact consistency and covering: a cell `a` of
`x` is the same cell as some cell of `y` exactly when its scope on the carrier lies in the
points of `y`.  The right-hand side depends only on the class of `a` under the same cell
(`Realization.IsSameCell.scope_map_eq`).  Coded domains and the correspondence of model classes
are not addressed. -/
theorem exists_isSameCell_iff (hR : R.IsConsistent) (hc : R.IsCovering) :
    (∃ e : Fin y.type.card, R.IsSameCell x a y e) ↔
      (x.type.toCellScheme.scope a).map x.tuple ⊆ y.support := by
  refine ⟨fun ⟨_, h⟩ ↦ h.scope_map_subset_support hR, fun hs ↦ ?_⟩
  have := hc.isDirected
  obtain ⟨u, hxu, hyu⟩ := directed_of (· ≤ ·) x y
  exact exists_isSameCell_of_le hR hxu hyu hs

/-- **The test**: under exact consistency and covering, a cell `a` of the type of `x` is the same
cell as exactly one cell of the type of `y` if and only if its scope on the carrier,
`(x.type.toCellScheme.scope a).map x.tuple`, lies in the points `y.support` of `y`.  Coded
domains and the correspondence of model classes are not addressed. -/
theorem existsUnique_isSameCell_iff (hR : R.IsConsistent) (hc : R.IsCovering) (x y : R.Occurrence)
    (a : Fin x.type.card) :
    (∃! e : Fin y.type.card, R.IsSameCell x a y e) ↔
      (x.type.toCellScheme.scope a).map x.tuple ⊆ y.support := by
  refine ⟨fun h ↦ (exists_isSameCell_iff hR hc).mp h.exists, fun hs ↦ ?_⟩
  obtain ⟨e, he⟩ := (exists_isSameCell_iff hR hc).mpr hs
  exact ⟨e, he, fun e' he' ↦ he'.symm.trans hR he |>.eq⟩

/-- **The cells two occurrences share**, under exact consistency and covering: the cells of `x`
whose scope on the carrier lies in the points of `y` correspond, by the same cell, to the cells
of `y` whose scope on the carrier lies in the points of `x`
(`Realization.isSameCell_sameCellEquiv`). -/
noncomputable def sameCellEquiv (hR : R.IsConsistent) (hc : R.IsCovering) (x y : R.Occurrence) :
    {a : Fin x.type.card // (x.type.toCellScheme.scope a).map x.tuple ⊆ y.support} ≃
      {e : Fin y.type.card // (y.type.toCellScheme.scope e).map y.tuple ⊆ x.support} where
  toFun a := ⟨((exists_isSameCell_iff hR hc).mpr a.2).choose,
    ((exists_isSameCell_iff hR hc).mpr a.2).choose_spec.symm.scope_map_subset_support hR⟩
  invFun e := ⟨((exists_isSameCell_iff hR hc).mpr e.2).choose,
    ((exists_isSameCell_iff hR hc).mpr e.2).choose_spec.symm.scope_map_subset_support hR⟩
  left_inv a := Subtype.ext <| by
    dsimp only
    generalize_proofs h₁ h₂
    exact (h₁.choose_spec.trans hR h₂.choose_spec).eq.symm
  right_inv e := Subtype.ext <| by
    dsimp only
    generalize_proofs h₁ h₂
    exact (h₁.choose_spec.trans hR h₂.choose_spec).eq.symm

/-- A cell of `x` and its image under `Realization.sameCellEquiv` are the same cell. -/
theorem isSameCell_sameCellEquiv (hR : R.IsConsistent) (hc : R.IsCovering)
    (a : {a : Fin x.type.card // (x.type.toCellScheme.scope a).map x.tuple ⊆ y.support}) :
    R.IsSameCell x a y (sameCellEquiv hR hc x y a) := by
  dsimp only [sameCellEquiv, Equiv.coe_fn_mk]
  exact ((exists_isSameCell_iff hR hc).mpr a.2).choose_spec

end Realization

end VaughtConjecture
