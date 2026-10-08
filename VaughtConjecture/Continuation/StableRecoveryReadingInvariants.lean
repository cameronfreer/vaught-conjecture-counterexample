/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryCodedReading
import VaughtConjecture.Extension.OrbitCode
import VaughtConjecture.Extension.Restoration

/-!
# The reading through the cap along normalization, splicing and capped agreement

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.1 (the catalogue layers of the completion); semantic contract, items 3 and 8.

The reading clause of a cap-reading extension (`StageType.IsCapReadingExtension`) is a condition on
the rows of the cells at `(univ, N)`; at the level of values it is
`StageType.ReadsThroughCapAt` (a labelling `r` reads `e` through the cap as a cell labelled `ℓ`).
In the catalogue layers of the completion (`Scheme.fieldLayer`, the profile layer of
`TowerProfile.scheme`) the rows of the new cells are catalogue entries, obtained from labellings
given by capped lifts, spliced with `⊥` above the grade and normalized by the orbit code
(`Scheme.orbitCode_splice_bot_mem_catalogue`).  This file tracks the reading along these three
operations, for a labelling `r` of the cells of a scheme `E` on one more point than `T⁺`.  Each
item below is compiled in this repository (theorem named), unless marked otherwise.

* **Normalization keeps the reading** (`StageType.ReadsThroughCapAt.orbitCode`): if `r` reads `e`
  through a cap of grade `N ≤ k`, so does its orbit code at `k`.  Two values `ω · c + i` and
  `ω · c + n` with `i, n < k` have one orbit key, keep their finite parts and move to one code block
  (`Label.orbitCode_omega0_mul_add`, in `VaughtConjecture.Extension.OrbitCode`); equal values have
  equal codes, and `⊥` is coded as `⊥`.
* **Splicing with `⊥` above the grade keeps the reading** (`StageType.ReadsThroughCapAt.splice`),
  when both the cap and the read cell `e` have grade at most `k` (two premises:
  `StageType.ReadsThroughCapAt` bounds the grades of the reference cells by that of the cap, but
  not the grade of `e`): the reading then involves cells of grade at most `k` only.
* **Capped agreement keeps the reading above every value**
  (`StageType.ReadsThroughCapAt.of_min_eq`): a labelling agreeing with `r` capped at a cap strictly
  above every value of `r` is `r`.  **Not below a value**
  (`StageType.ReadsThroughCapAt.exists_not_of_le`): if the value of `r` at `e` is at least the cap,
  some labelling agreeing with `r` capped at the cap does not read `e` (the value `⊤` at `e`).  So
  every lift lemma whose conclusion is capped agreement (`CellScheme.Rows.CappedLift`: the lifts of
  the tower, `TowerProfile.cappedLift_three`, `TowerProfile.cappedLift_top_four`, the extensions
  from the boundary) preserves the reading of a labelling all of whose values lie strictly below the
  cap, and, when the value at the read cell is at or above the cap, capped agreement alone does not
  preserve that reading; at the cap `⊥` (the extensions at `⊥`,
  `TowerProfile.extendsFromBoundary_bot_top`) it preserves nothing.
**Which cells the reading clause needs** (read off the definitions).
`StageType.IsCapReadingExtension` asks for `StageType.ReadsThroughCap` at every cell of graded index
`(univ, N)`, a condition on rows with no labelling; its recovery
(`StageType.IsStableRecoveryScheme.of_readsThroughCap`) takes the cell given by availability in an
arbitrary lawful stage type with face `T⁺`, which can be any cell there. A condition on the cells
labelled `⊤` in one labelling does not give it (argued, not formalized): the recovery quantifies
over every stage type on the scheme with face `T⁺`.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label
open Ordinal hiding univ

/-! ### The reading along normalization, splicing and capped agreement -/

namespace StageType

variable {α : Ordinal.{u}} {m : ℕ} {Tp : StageType.{u} α m} {E : Scheme.{u} (m + 1)}
  {r r' : Fin E.card → Label.{u}} {b : Fin (E.comap Fin.castSuccEmb).card} {e : Fin E.card}
  {ℓ : Label.{u}}

/-- **Normalization keeps the reading**: if `r` reads `e` through a cap of grade at most `k`, so
does the orbit code of `r` at `k`. -/
theorem ReadsThroughCapAt.orbitCode (h : Tp.ReadsThroughCapAt E r b e ℓ) {k : ℕ}
    (hk : E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b) ≤ k) :
    Tp.ReadsThroughCapAt E (Label.orbitCode k r) b e ℓ := by
  obtain ⟨hbot, htop, hord⟩ := h
  refine ⟨fun hℓ ↦ Label.orbitCode_eq_bot_iff.mpr (hbot hℓ), fun hℓ ↦ ?_, fun μ n hμ hℓ ↦ ?_⟩
  · rw [Label.orbitCode_apply, Label.orbitCode_apply, htop hℓ]
  obtain ⟨hn, a, a₀, i, c, haa₀, ha₀, hi, hag, hra, hre⟩ := hord μ n hμ hℓ
  obtain ⟨c', hra', hre'⟩ := Label.orbitCode_omega0_mul_add (k := k) (hi.trans_le hk)
    (hn.trans_le hk) hra hre
  exact ⟨hn, a, a₀, i, c', haa₀, ha₀, hi, hag, hra', hre'⟩

/-- **Splicing with `⊥` above the grade keeps the reading**, when the cap and `e` both have grade
at most `k` (`hk` and `he`; the reading bounds the grades of the reference cells by that of the cap,
not the grade of `e`): the reading involves the cap, the reference cells and `e`, all of grade at
most `k`. -/
theorem ReadsThroughCapAt.splice (h : Tp.ReadsThroughCapAt E r b e ℓ) {k : ℕ}
    (hk : E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b) ≤ k)
    (he : E.toCellScheme.grade e ≤ k) :
    Tp.ReadsThroughCapAt E (E.toCellScheme.splice k (fun _ ↦ ⊥) r) b e ℓ := by
  obtain ⟨hbot, htop, hord⟩ := h
  have hs {x : Fin E.card} (hx : E.toCellScheme.grade x ≤ k) :
      E.toCellScheme.splice k (fun _ ↦ ⊥) r x = r x :=
    CellScheme.splice_of_le hx
  refine ⟨fun hℓ ↦ by rw [hs he, hbot hℓ], fun hℓ ↦ by rw [hs he, hs hk, htop hℓ],
    fun μ n hμ hℓ ↦ ?_⟩
  obtain ⟨hn, a, a₀, i, c, haa₀, ha₀, hi, hag, hra, hre⟩ := hord μ n hμ hℓ
  exact ⟨hn, a, a₀, i, c, haa₀, ha₀, hi, hag, by rw [hs (hag.trans hk), hra],
    by rw [hs he, hre]⟩

/-- **Capped agreement above every value keeps the reading**: a labelling agreeing with `r` capped
at a cap above every value of `r` is `r`. -/
theorem ReadsThroughCapAt.of_min_eq (h : Tp.ReadsThroughCapAt E r b e ℓ) {c : Label.{u}}
    (hc : ∀ x, r x < c) (hr' : ∀ x, min (r' x) c = min (r x) c) :
    Tp.ReadsThroughCapAt E r' b e ℓ := by
  have heq : r' = r := funext fun x ↦ by
    have h1 := hr' x
    rw [min_eq_left (hc x).le] at h1
    rcases le_total (r' x) c with h2 | h2
    · rwa [min_eq_left h2] at h1
    · rw [min_eq_right h2] at h1
      exact absurd h1 (hc x).ne'
  rwa [heq]

/-- **Capped agreement at or below a value does not keep the reading**: if the value of `r` at `e`
is at least the cap `c` (no reading of `e` by `r` is assumed), then the labelling equal to `r`
except for the formal top at `e` agrees with `r` capped at `c` and does not read `e` through the
cap as a cell labelled `μ + n`. -/
theorem ReadsThroughCapAt.exists_not_of_le {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) (n : ℕ)
    {c : Label.{u}} (hce : c ≤ r e) :
    ∃ r' : Fin E.card → Label.{u}, (∀ x, min (r' x) c = min (r x) c) ∧
      ¬ Tp.ReadsThroughCapAt E r' b e ((μ + n : Ordinal.{u}) : Label.{u}) := by
  classical
  refine ⟨Function.update r e ⊤, fun x ↦ ?_, fun h ↦ ?_⟩
  · by_cases hx : x = e
    · subst hx
      rw [Function.update_self, min_eq_right le_top, min_eq_right hce]
    · rw [Function.update_of_ne hx]
  · obtain ⟨-, -, hord⟩ := h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hre⟩ := hord μ n hμ rfl
    rw [Function.update_self] at hre
    exact absurd hre.symm (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne

end StageType

end VaughtConjecture
