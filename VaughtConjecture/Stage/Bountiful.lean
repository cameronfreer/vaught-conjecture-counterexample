/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Scheme.Transport
import VaughtConjecture.Stage.Scheme

/-!
# Bountifulness of face restrictions

Roadmap, Layer 1 (bountifulness; restriction and pullback; countable stage types and exact
partial face maps); semantic contract, item 3 (capping is not stage reduction; bountifulness is a
statement about cap balls of lawful labellings, cap by cap); the expositions, §2.

Bountifulness of the rows of a scheme on `n` points (`CellScheme.Rows.IsBountiful` of
`Scheme.rows`) passes to its restriction along every embedding `f : Fin m ↪ Fin n`
(`Scheme.isBountiful_comap`).  The restriction pulls the rows back along the cells visible
through `f` and then reindexes them in increasing order, so this is the pullback of bountifulness
along an embedding of ground sets (`CellScheme.Rows.IsBountiful.comap`) followed by its transport
along an equivalence of cells (`CellScheme.Rows.IsBountiful.reindex`).  No condition on `f` is
needed: in particular the statement holds whether or not the range of `f` is a closed face, and
so whether or not the corresponding face map of stage types is defined.

## References

Bountifulness is Definition 2.5.14 and face restriction is the horizontal restriction of §3.1 of
R. W. Knight, *A counterexample to Vaught's Conjecture using generalised Stone spaces* (draft,
20 February 2026) (numbering to be verified against the manuscript).
-/

universe u

namespace VaughtConjecture.Scheme

variable {n m : ℕ} (f : Fin m ↪ Fin n)

/-- The restriction of a scheme with bountiful rows has bountiful rows. -/
theorem isBountiful_comap {S : Scheme.{u} n} (hS : S.rows.IsBountiful) :
    (S.comap f).rows.IsBountiful :=
  (hS.comap f).reindex (S.cellEquiv f)

/-- Regression: the restriction of a scheme with mute rows has bountiful rows, through
`isBountiful_comap` rather than by recomputing the restricted rows. -/
private theorem isBountiful_comap_of_rows_eq_mute {S : Scheme.{u} n}
    (hS : S.rows = CellScheme.Rows.mute S.toCellScheme) : (S.comap f).rows.IsBountiful :=
  isBountiful_comap f (hS ▸ CellScheme.Rows.isBountiful_mute)

/-- Regression: the restriction of a scheme with mute rows has mute rows. -/
private theorem comap_rows_of_rows_eq_mute {S : Scheme.{u} n}
    (hS : S.rows = CellScheme.Rows.mute S.toCellScheme) :
    (S.comap f).rows = CellScheme.Rows.mute (S.comap f).toCellScheme := by
  rw [show (S.comap f).rows = S.rows.comap (S.isLowerEmbedding_comap f) from rfl, hS,
    CellScheme.Rows.comap_mute]

end VaughtConjecture.Scheme
