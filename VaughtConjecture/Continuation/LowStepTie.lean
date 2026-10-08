/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStep
import VaughtConjecture.Continuation.GrowthCappedDecoder

/-!
# The tie case of the LOW step through a top cell of the donor

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the LOW step from the
private coatom at the tie); semantic contract, items 3, 4 and 8.

At the tie of donor raising no witness image of a capped lift raises a donor top: a witness fixing
the donor maximum fixes its replacement.  The donor is read instead through the row of a cell `Z`
labelled `⊤` of graded index `(univ, K)`, the **template** `V = row_Z`: it reads every top above
the replacements of its readings of the proper cells (`StageType.visibilityReplace_rowAt_lt_of_top`,
the donor-side source gap), so a threshold `θ_b`, the largest such replacement, separates the tops
from the proper cells in `V`.

**The raise map** (`Label.raiseMap`, `Label.isWitness_raiseMap`, compiled in this repository).
For a map `θ` fixing `⊥`, monotone, commuting with visibility replacement at every threshold
`k ≤ K` with no guard and keeping its bottom under every replacement, a threshold `θ_b` and a cap
`c`, both self-visible at `K`, the map `ρ` equal to `θ` at and below `θ_b`, to `max (θ v) c` above,
and `⊥` where `θ` is `⊥`, is a witness bounded by `K`.

**The raise through the template** (`StageType.exists_raised_of_dominated`, compiled in this
repository).  Let `W₁` be a section of the donor lawful at `K` (bottom above `K`) dominated at `Z`:
every cell of grade at most `K` is read by `W₁` at most at `Z`, and `W₁ Z ≠ ⊥`.  With `θ` the
capped decoder of `W₁` at `Z` (`Scheme.exists_cappedDecoder`, from the locality of `W₁` at `Z`:
`θ (row_Z d) = min (W₁ d) (W₁ Z)`, exact by domination), the section `ρ ∘ V`, spliced with `⊥`
above `K`, is lawful at `K` (transport with `W₁` as lawful companion of the same bottom pattern,
`CellScheme.Rows.IsLawfulBelow.map_of_bot_iff`), equals `W₁` at every proper cell and every cell
`W₁` reads as `⊥`, and reads every other top `d` as `max (W₁ d) c`.

**The tie case from donor domination** (`StageType.lowStepTie_of_donorDomination`, compiled in this
repository).  If every capped lift of the donor from the root, literal on the root and agreeing
with the ambient donor face capped at the cap, can be chosen dominated at a top cell of graded index
`(univ, K)` (`StageType.DonorDomination`), the tie case `StageType.LowStepTie` holds: the raise
through the template keeps the root (proper root cells are kept, root tops are at least the
frontier already), keeps the capped agreement (the raised tops are at least the cap), and puts every
donor top off the root, at the tie or determined by the root included, at least at the frontier.
So the open part of the tie case is donor domination, the donor-side counterpart of the domination
by the owner on the private side.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Label

variable {K : ℕ}

open Classical in
/-- The **raise map**: `⊥` where `θ` is `⊥`, `θ` at and below the threshold `θb`, and `max (θ v) c`
above it. -/
noncomputable def raiseMap (θ : Label.{u} → Label.{u}) (θb c : Label.{u}) (v : Label.{u}) :
    Label.{u} :=
  if θ v = ⊥ then ⊥ else if v ≤ θb then θ v else max (θ v) c

variable {θ : Label.{u} → Label.{u}} {θb c : Label.{u}}

theorem raiseMap_of_bot {v : Label.{u}} (h : θ v = ⊥) : raiseMap θ θb c v = ⊥ := by
  simp [raiseMap, h]

theorem raiseMap_of_le {v : Label.{u}} (h0 : θ v ≠ ⊥) (h : v ≤ θb) : raiseMap θ θb c v = θ v := by
  simp [raiseMap, h0, h]

theorem raiseMap_of_lt {v : Label.{u}} (h0 : θ v ≠ ⊥) (h : θb < v) :
    raiseMap θ θb c v = max (θ v) c := by
  simp [raiseMap, h0, not_le.mpr h]

theorem le_raiseMap (v : Label.{u}) : θ v ≤ raiseMap θ θb c v := by
  by_cases h0 : θ v = ⊥
  · rw [h0]; exact bot_le
  by_cases h : v ≤ θb
  · rw [raiseMap_of_le h0 h]
  · rw [raiseMap_of_lt h0 (not_le.mp h)]; exact le_max_left _ _

theorem raiseMap_eq_bot_iff {v : Label.{u}} : raiseMap θ θb c v = ⊥ ↔ θ v = ⊥ :=
  ⟨fun h ↦ le_bot_iff.mp (h ▸ le_raiseMap v), raiseMap_of_bot⟩

/-- **The raise map is a witness bounded by `K`.** -/
theorem isWitness_raiseMap (hθm : Monotone θ) (hθ0 : θ ⊥ = ⊥)
    (hθc : ∀ k ≤ K, ∀ i ≤ k, ∀ x, θ (visibilityReplace k i x) = visibilityReplace k i (θ x))
    (hθb0 : ∀ x, θ x = ⊥ → ∀ k i, i ≤ k → θ (visibilityReplace k i x) = ⊥)
    (hb : IsSelfVisible K θb) (hc : IsSelfVisible K c) :
    IsWitness (stepSuppressor K) (raiseMap θ θb c) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := raiseMap_of_bot hθ0
  monotone x y hxy := by
    by_cases hx0 : θ x = ⊥
    · rw [raiseMap_of_bot hx0]; exact bot_le
    have hy0 : θ y ≠ ⊥ := fun h ↦ hx0 (le_bot_iff.mp (h ▸ hθm hxy))
    by_cases hy : y ≤ θb
    · rw [raiseMap_of_le hx0 (hxy.trans hy), raiseMap_of_le hy0 hy]; exact hθm hxy
    · rw [raiseMap_of_lt hy0 (not_le.mp hy)]
      by_cases hx : x ≤ θb
      · rw [raiseMap_of_le hx0 hx]; exact (hθm hxy).trans (le_max_left _ _)
      · rw [raiseMap_of_lt hx0 (not_le.mp hx)]; exact max_le_max (hθm hxy) le_rfl
  visibilityReplace_comm x k hx i hi := by
    by_cases hk : k ≤ K
    · by_cases hx0 : θ x = ⊥
      · rw [raiseMap_of_bot hx0, raiseMap_of_bot (hθb0 x hx0 k i hi), visibilityReplace_bot]
      have hR0 : θ (visibilityReplace k i x) ≠ ⊥ := by
        rw [hθc k hk i hi x, Ne, visibilityReplace_eq_bot_iff]; exact hx0
      by_cases hxb : x ≤ θb
      · have hRb : visibilityReplace k i x ≤ θb :=
          (monotone_visibilityReplace hi hxb).trans_eq ((hb.mono hk).visibilityReplace_eq i)
        rw [raiseMap_of_le hR0 hRb, raiseMap_of_le hx0 hxb, hθc k hk i hi x]
      · have hlt := not_le.mp hxb
        rw [raiseMap_of_lt hR0 (lt_visibilityReplace_of_lt hi (hb.mono hk) hlt),
          raiseMap_of_lt hx0 hlt, hθc k hk i hi x,
          (monotone_visibilityReplace hi).map_max, (hc.mono hk).visibilityReplace_eq i]
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff, raiseMap_eq_bot_iff] at hx
      rw [raiseMap_of_bot (hθb0 x hx k i hi), raiseMap_of_bot hx, visibilityReplace_bot]

end VaughtConjecture.Label
