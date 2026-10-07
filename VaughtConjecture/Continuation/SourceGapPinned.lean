/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapDetermination
import VaughtConjecture.Extension.PinnedExtension

/-!
# Separated pinned extensions without new tops, from coatom extensions

Roadmap, Layer 3 ((R2) of the table of 3.4, and row 6, the exact pinned extension); the separated
pinned extensions of `VaughtConjecture.Continuation.SourceGapDetermination`.

The separated pinned extension property (`StageType.HasSeparatedPinnedExtensions α`) asks, over a
legal source-gap context `t'` along `h`, for a legal one-point coface of `t'` with face a given
donor `d` along `h` followed by the new point, whose cells of graded index `(univ, K)` read every
new top at least as the lost top.  When `d` has no new top (no cell containing the new point is
labelled `⊤`), the reading condition is vacuous, and the coface is an exact pinned extension:
under the coatom extension property `StageType.HasCoatomExtensions α` it exists
(`StageType.exists_pinned_extension`).  So, under the coatom extension property, the separated
pinned extension property holds at every donor without a new top
(`StageType.exists_separated_of_hasCoatomExtensions`, compiled in this repository), over every
legal context and root, source-gap or not.  At donors with a new top the property fails: some
legal source-gap context and donor with a new top have no separating coface at all
(`SeparationObstruction.not_exists_separatesThrough`, in
`VaughtConjecture.Continuation.SourceGapSeparationObstruction`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **A new cell of the face along `h` followed by the new point is a new cell of the donor**: a
cell of `D'` visible in that face whose scope contains the new point comes from a cell of `d`
whose scope contains the new point of `d`. -/
theorem exists_faceCell_of_last_mem {D' : StageType.{u} α (k + 1)} {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} (hD'd : restrictFace (extendByLast h) D' = some d)
    {x : Fin D'.card} (hx : x ∈ D'.visibleCells (extendByLast h))
    (hxl : Fin.last k ∈ D'.toCellScheme.scope x) :
    ∃ y, faceCell hD'd y = x ∧ Fin.last n ∈ d.toCellScheme.scope y := by
  obtain ⟨y, rfl⟩ := D'.toScheme.exists_faceCell_eq (comap_toScheme_of_restrictFace hD'd) hx
  refine ⟨y, rfl, ?_⟩
  -- the scope of a cell of the face is the image of its scope in the face
  change Fin.last k ∈ D'.toCellScheme.scope (faceCell hD'd y) at hxl
  rw [scope_faceCell, mem_map] at hxl
  obtain ⟨z, hz, hzl⟩ := hxl
  obtain rfl : z = Fin.last n :=
    (extendByLast h).injective (hzl.trans (extendByLast_last h).symm)
  exact hz

/-- **Separated pinned extensions at donors without a new top, from coatom extensions**: under the
coatom extension property, over a legal `t'` with face `t` along `h`, every legal one-point coface
`d` of `t` none of whose cells containing the new point is labelled `⊤` is the face along `h`
followed by the new point of a legal one-point coface of `t'` that separates the new tops through
any cell at any grade (vacuously). -/
theorem exists_separated_of_hasCoatomExtensions (hext : HasCoatomExtensions.{u} α)
    {t' : StageType.{u} α k} (ht' : t'.IsLegal) {h : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace h t' = some t) {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces)
    (hnew : ∀ j, Fin.last n ∈ d.toCellScheme.scope j → d.label j ≠ ⊤) (K : ℕ)
    (r : Fin t'.card) :
    ∃ (D' : StageType.{u} α (k + 1)) (hD' : D' ∈ t'.cofaces),
      restrictFace (extendByLast h) D' = some d ∧ SeparatesThrough hD'.2 h K r := by
  obtain ⟨D', hD', hD't', hD'd⟩ := exists_pinned_extension hext ht' ht hd.1 hd.2
  refine ⟨D', ⟨hD', hD't'⟩, hD'd, fun x hx hxl hxt ↦ ?_⟩
  obtain ⟨y, rfl, hy⟩ := exists_faceCell_of_last_mem hD'd hx hxl
  exact absurd ((label_faceCell hD'd y).symm.trans hxt) (hnew y hy)

end StageType

end VaughtConjecture
