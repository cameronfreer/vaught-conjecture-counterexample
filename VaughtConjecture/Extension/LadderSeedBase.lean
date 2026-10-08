/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderGlue
import VaughtConjecture.Extension.Seed

/-!
# The padded grade-one base of a seed

Roadmap, Layer 3 ((R3) and (R4), the attachment scheme and the padded grade-one base of the
recognizing growth carrier).

The **attachment scheme** of the growth carrier is the amalgam of a seed (`Seed`, two legal
coatom types with a common face, [Kni26, Definition 4.3.1]): over the growth seed
(`StageType.exists_growthSeed`) its first coatom type is the context `t'` and its face along the
root followed by the new point is the donor `d`, literally.  It has no cell of full scope, its rows
are consistent and coded, and its rows are bountiful [Kni26, Lemma 4.3.2]: in particular it lifts
capped from every graded face into the full face of grade one, where it has no cell.

**The padded grade-one base of a seed** (`Seed.ladderBase`) is the ladder base of the amalgam over
the rank members (`Scheme.RankMember`) at a height `H` at least the number of cells.  It is
consistent, well formed and coded, and **lifts capped between graded faces `X ≤ Y` whenever `Y`
is not of full scope or is the full face of grade one** (`Seed.cappedLift_ladderBase`): below a pair
not of full scope the base is the amalgam (`Scheme.cappedLift_ladderBase_iff`), and into the full
face of grade one the lift is that of the amalgam followed by gluing of rank members
(`Scheme.cappedLift_ladderBase_rankMember`).  The pairs of full scope at grades `2` and above are
those of the layers above the base.

## References

The amalgam of two coatom domains and its bountifulness are [Kni26, Definition 4.3.1 and
Lemma 4.3.2].
-/

universe u

namespace VaughtConjecture

open Finset

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (H : ℕ)

/-- The amalgam of a seed has no cell above the full face of grade one. -/
theorem noFullOne : I.amalgam.toScheme.NoFullOne := fun d ↦ I.not_univ_le 1 d

/-- **The padded grade-one base of a seed**: the ladder base of its amalgam over the rank members
at the height `H`. -/
noncomputable abbrev ladderBase : Scheme.{u} (m + 2) :=
  Scheme.ladderBase H (Scheme.rankProf.{u} I.amalgam.toScheme H) I.noFullOne

/-- The padded grade-one base of a seed is consistent. -/
theorem isConsistent_ladderBase (hH : 0 < H) : (I.ladderBase H).rows.IsConsistent :=
  Scheme.isConsistent_ladderBase_rankMember I.amalgam.isWellFormed I.isConsistent hH

/-- The padded grade-one base of a seed is well formed. -/
theorem isWellFormed_ladderBase : (I.ladderBase H).IsWellFormed :=
  Scheme.isWellFormed_ladderBase I.amalgam.isWellFormed (by omega)

/-- The padded grade-one base of a seed is coded. -/
theorem isCoded_ladderBase : (I.ladderBase H).IsCoded :=
  Scheme.isCoded_ladderBase I.amalgam.isCoded

/-- **The padded grade-one base of a seed lifts capped** between graded faces `X ≤ Y` when `Y` is
not of full scope or is the full face of grade one, at a height at least the number of cells of
the amalgam. -/
theorem cappedLift_ladderBase (hH : 0 < H) (hcard : I.amalgam.card ≤ H)
    {X Y : Finset (Fin (m + 2)) × ℕ} (hX : X ∈ I.amalgam.toCellScheme.gradedFaces)
    (hY : Y ∈ I.amalgam.toCellScheme.gradedFaces) (h : X ≤ Y)
    (hY1 : Y.1 ≠ univ ∨ Y = ((univ : Finset (Fin (m + 2))), 1)) :
    (I.ladderBase H).rows.CappedLift h := by
  rcases hY1 with hY1 | rfl
  · have hYu : ¬ ((univ : Finset (Fin (m + 2))), 1) ≤ Y := fun hle ↦
      hY1 (eq_univ_of_forall fun x ↦ hle.1 (mem_univ x))
    exact (Scheme.cappedLift_ladderBase_iff h hYu).mpr (I.isBountiful hX hY h)
  · by_cases hXu : X.1 = univ
    · exact CellScheme.Rows.cappedLift_of_fst_eq h hXu
    · have hXn : ¬ ((univ : Finset (Fin (m + 2))), 1) ≤ X := fun hle ↦
        hXu (eq_univ_of_forall fun x ↦ hle.1 (mem_univ x))
      exact Scheme.cappedLift_ladderBase_rankMember I.amalgam.isWellFormed hH hcard h hXn
        (I.isBountiful hX hY h)

end Seed

end VaughtConjecture
