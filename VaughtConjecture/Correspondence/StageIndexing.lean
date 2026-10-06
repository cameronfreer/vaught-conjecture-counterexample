/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.Expansion

/-!
# The stage indexing of [AFK26] and the block stages

Roadmap, "Manuscript correspondence (required)", the index translation and item 1; concordance
row 1 (`IMPLEMENTATION.md`, "Manuscript concordance").

**The printed indexing.**  [AFK26] indexes its projections by the countable ordinals `β < ω₁` and
reads the projection of index `β` at the stage `ω · β`:

* the `β`-truncation function [AFK26, Definition 3.12] keeps an ordinal below `β` and sends every
  other ordinal, and `∞`, to `∞`; it is extended by `-∞ ↦ -∞` [AFK26, Definition 4.9].  It is the
  stage reduction `Label.reduce β` of a label, clause by clause (`Label.reduce_bot`,
  `Label.reduce_coe_eq_ite`, `Label.reduce_top`).  `Label.reduce_coe_eq_ite` is stated for all
  ordinals `β` and `o`; the printed function, with `β < ω₁` and domain `ω₁ ∪ {∞}`, is its
  restriction;
* the projection of index `β` is the truncation at `ω · β`: in the example of trees,
  `τ_β = τ⁻_{ω·β}` [AFK26, Definition 3.20], and for templates `τ_β(Q_t) = Q_{t*}` with `t*` the
  truncation of `t` at `ω · β` [AFK26, Definition 4.16];
* the limit ordinals below `ω₁` are the stages of the later of the two versions of 4 October 2026
  of [AFK26] (its Definition 4.23; the earlier version of that date defines them in its
  Definition 4.15); the current version has no separate notion of a stage.

Printed material, not used here: the structures of index `β` of the system of templates are asked
for density at the index `ω · β` [AFK26, Definition 4.20], density at an index being read through
the projection of that index [AFK26, Definition 2.10]; by [AFK26, Definition 4.16] that projection
is the truncation at `ω² · β`, not at `ω · β`.

**The comparison.**  The block stage `λ_ξ = ω + ω · ξ` (`blockStage`) is the printed stage of
the index `1 + ξ`: `blockStage ξ = ω * (1 + ξ)` (`blockStage_eq_mul`).  So the two indexings agree
at every infinite index (`blockStage_eq_omega0_mul_of_omega0_le`), and at a finite index `n` the
block stage is the printed stage of `n + 1` (`blockStage_natCast`).  The conventions:

* **at zero**: the printed index `0` reads the stage `ω · 0 = 0`, which is not a limit and is no
  block stage; the printed indices of block stages are exactly the positive ordinals
  (`exists_blockStage_eq_omega0_mul_iff`), and the reindexing `ξ ↦ 1 + ξ` is an order embedding
  (Mathlib's `add_right_strictMono`) onto them (`exists_one_add_eq_iff`) preserving countability
  (`one_add_lt_omega_one_iff`; these two in `VaughtConjecture.Realization.Expansion`);
* **at limits**: block stages are continuous (`isNormal_blockStage`): at a limit index the block
  stage is the supremum of the block stages below it (`blockStage_eq_iSup_of_isSuccLimit`), as
  the printed stage `ω · γ` is at a limit `γ`;
* **the stages**: the block stages are exactly the limit ordinals
  (`isSuccLimit_iff_exists_blockStage`), and those of countable index are exactly the limit
  ordinals below `ω₁` (`isSuccLimit_and_lt_omega_one_iff`).

**Departure.**  The printed index `0` reads the stage `0`, and the projection of that index is not
compatible with the base relations
(`VaughtConjecture.Correspondence.not_isCompatibleWith_omega0MulSystem`, in
`VaughtConjecture.Correspondence.InvariantSystem`): this index is corrected, and it has no block
index.  With the diagram of the stage types (`Correspondence.stageDiagram`), only the index `0`
is forced: the printed projections with the index `0` read at the stage `ω` form a compatible
system (`Correspondence.isCompatibleWith_omega0MulMaxOneSystem`) that agrees with the printed one
at every positive index (`Correspondence.omega0MulMaxOneSystem_τ_of_ne_zero`).
The shift by one at the other finite indices, the index of a block stage being the printed index
`1 + ξ` (`Correspondence.omega0MulSystem_τ_one_add`), is the convention of `blockStage`
(`λ_0 = ω`), not a consequence of compatibility.

## Placement

The concordance and its notes are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".

## References

[AFK26] is the draft *A counterexample to Vaught's Conjecture for `L_{ω₁ω}`* (2026), recorded in
`roadmap/REFERENCES.bib`.
-/

universe u

namespace VaughtConjecture

open Ordinal Order

/-! ### The printed truncation function -/

namespace Label

/-- **The truncation function of [AFK26] on an ordinal** [AFK26, Definition 3.12]: stage
reduction keeps an ordinal below the stage and sends every other ordinal to the formal top.  With
`Label.reduce_top` (the top is sent to the top) and `Label.reduce_bot` (the extension
`-∞ ↦ -∞` of [AFK26, Definition 4.9]) this is the printed function, clause by clause. -/
theorem reduce_coe_eq_ite (β o : Ordinal.{u}) :
    reduce β (o : Label.{u}) = if o < β then (o : Label.{u}) else ⊤ := by
  split_ifs with h
  · exact reduce_of_lt (by exact_mod_cast h)
  · exact reduce_of_le (by exact_mod_cast not_lt.mp h)

end Label

/-! ### Block stages as printed stages -/

/-- **The block stages at infinite indices are the printed stages**: for `ω ≤ ξ`,
`λ_ξ = ω · ξ`. -/
theorem blockStage_eq_omega0_mul_of_omega0_le {ξ : Ordinal.{u}} (hξ : ω ≤ ξ) :
    blockStage ξ = ω * ξ := by
  rw [blockStage_eq_mul, one_add_of_omega0_le hξ]

/-- **The block stage of a finite index `n` is the printed stage of `n + 1`**. -/
theorem blockStage_natCast (n : ℕ) :
    blockStage (n : Ordinal.{u}) = ω * ((n + 1 : ℕ) : Ordinal) := by
  rw [blockStage_eq_mul, Nat.add_comm n 1]
  push_cast
  rfl

/-- **The printed indices of the block stages are the positive ordinals**: the printed stage
`ω · β` is a block stage exactly when `β ≠ 0`.  The printed index `0` reads the stage `0`. -/
theorem exists_blockStage_eq_omega0_mul_iff {β : Ordinal.{u}} :
    (∃ ξ, blockStage ξ = ω * β) ↔ β ≠ 0 := by
  simp_rw [blockStage_eq_mul, mul_right_inj' omega0_ne_zero]
  exact exists_one_add_eq_iff

/-- The printed stage of index `0` is `0`, which is not a limit. -/
theorem not_isSuccLimit_omega0_mul_zero : ¬ IsSuccLimit (ω * 0 : Ordinal.{u}) := by
  simp

/-- **The block stages are exactly the limit ordinals.** -/
theorem isSuccLimit_iff_exists_blockStage {α : Ordinal.{u}} :
    IsSuccLimit α ↔ ∃ ξ, blockStage ξ = α := by
  refine ⟨fun hα ↦ ?_, fun ⟨ξ, hξ⟩ ↦ hξ ▸ isSuccLimit_blockStage ξ⟩
  obtain ⟨β, rfl⟩ := isSuccPrelimit_iff_omega0_dvd.mp hα.isSuccPrelimit
  refine exists_blockStage_eq_omega0_mul_iff.mpr fun h ↦ ?_
  subst h
  exact not_isSuccLimit_omega0_mul_zero hα

/-- A block stage is countable exactly when its index is. -/
theorem blockStage_lt_omega_one_iff {ξ : Ordinal.{u}} : blockStage ξ < ω₁ ↔ ξ < ω₁ :=
  ⟨fun h ↦ (le_blockStage ξ).trans_lt h, blockStage_lt_omega_one⟩

/-- **The countable limit ordinals are the block stages of countable index**: a limit
ordinal below `ω₁` is the block stage of a countable index, and conversely. -/
theorem isSuccLimit_and_lt_omega_one_iff {α : Ordinal.{u}} :
    IsSuccLimit α ∧ α < ω₁ ↔ ∃ ξ < ω₁, blockStage ξ = α := by
  rw [isSuccLimit_iff_exists_blockStage]
  constructor
  · rintro ⟨⟨ξ, rfl⟩, h⟩
    exact ⟨ξ, blockStage_lt_omega_one_iff.mp h, rfl⟩
  · rintro ⟨ξ, hξ, rfl⟩
    exact ⟨⟨ξ, rfl⟩, blockStage_lt_omega_one hξ⟩

/-! ### Continuity at limits -/

/-- **Block stages are a normal function**: strictly increasing and continuous at limits. -/
theorem isNormal_blockStage : IsNormal (blockStage : Ordinal.{u} → Ordinal.{u}) :=
  (isNormal_add_right (ω : Ordinal.{u})).comp (isNormal_mul_right omega0_pos)

/-- **The block stage at a limit index is the supremum of the block stages below it.** -/
theorem blockStage_eq_iSup_of_isSuccLimit {γ : Ordinal.{u}} (hγ : IsSuccLimit γ) :
    blockStage γ = ⨆ ξ : Set.Iio γ, blockStage ξ :=
  isNormal_blockStage.apply_of_isSuccLimit hγ

end VaughtConjecture
