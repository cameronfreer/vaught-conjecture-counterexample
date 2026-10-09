/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedApexInstance

/-!
# Decoding in two stages, and the strip of the cut

Roadmap, Layer 3 ((R3) and (R4), the context lift at a grade with the values per grade): the
lawfulness of the decoded lift in two stages, and the exact form of the comparison of decoders on
the strip of the cut.

**Two stages** (`Seed.isLawfulBelow_twoStage`).  The lift at the grade `k` is
`ρ ∘ orbitDecoder k f h ∘ w_P`, with `w_P` the writing of the orbit code `P` of the aligned codes
in the replicated scheme with the values `codeGrid k B`.  First, `orbitDecoder k f h ∘ w_P` is
lawful below `(univ, k)`: the orbit decoder is a witness bounded by `k`
(`Label.isWitness_orbitDecoder`) and sends only `⊥` to `⊥` at a cut `h ≠ ⊥`
(`Label.orbitDecoder_eq_bot_iff`); the writing is lawful for a lawful admitted `P` with values in
the code grid.  Second, `ρ` is applied with the ambient as the lawful companion
(`CellScheme.Rows.IsLawfulBelow.map_of_min_eq`), which asks exactly the capped agreement of the
decoded lift with the ambient at the cap `c ≠ ⊥`.  The companion introduces no other premise: the
ambient is lawful below `(univ, k)` by the input of the lift.

**The strip of the cut** (`Label.eq_at_cut_of_strip`, `Label.eq_at_two_of_one`).  The capped
agreement asked above fails exactly at the labels of the strip of the cut that the ambient reads
below the cap: if `visibilityReplace k k x = h` and the ambient's decoder `τ` reads `x` below `c`,
every witness `σ` bounded by `k` agreeing with `τ` capped at `c` at `x` agrees with `τ` at the cut
itself, `σ h = τ h`.  So a code placed at the cut is read as the ambient reads the cut, not as a
prescription value above it.  The case of the ladder value `1` below the cut `2`: `σ 2 = τ 2`
whenever `τ 1 < c` and `σ 1` agrees with it capped at `c`.  The orbit code places a code at the cut
exactly when the anchor takes the value of the cut at a cell; the decoder of
`Label.singleDecoder_spec` then reads that code as the prescription there, so the capped agreement
at `1` holds only if the prescription at that cell is read by `τ` at the cut.

## References

Witnesses and visibility replacement are [Kni26, Definitions 2.2.3 and 2.3.9]; lawful sections are
[Kni26, Definition 2.5.4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Label

variable {k : ℕ}

/-- **On the strip of the cut a witness is fixed by its value below the cap**: if
`visibilityReplace k k x = h`, `τ x < c`, and `σ` agrees with `τ` capped at `c` at `x`, then two
witnesses bounded by `k` agree at `h`. -/
theorem eq_at_cut_of_strip {σ τ : Label.{u} → Label.{u}} (hσ : IsWitness (stepSuppressor k) σ)
    (hτ : IsWitness (stepSuppressor k) τ) {x h c : Label.{u}} (hxh : visibilityReplace k k x = h)
    (hτc : τ x < c) (hag : min (σ x) c = min (τ x) c) : σ h = τ h := by
  have hσx : σ x = τ x := by
    rw [min_eq_left hτc.le] at hag
    rcases le_total (σ x) c with h' | h'
    · rwa [min_eq_left h'] at hag
    · rw [min_eq_right h'] at hag; exact absurd hag.symm hτc.ne
  have hg : ∀ z : Label.{u}, z ≤ stepSuppressor k k := fun _ ↦ by
    rw [stepSuppressor_of_le le_rfl]; exact le_top
  rw [← hxh, hσ.visibilityReplace_comm x k (hg _) k le_rfl,
    hτ.visibilityReplace_comm x k (hg _) k le_rfl, hσx]

/-- **The ladder value `1` below the cut `2`**: two witnesses bounded by `2` agreeing capped at
`c` at `1`, with `τ 1 < c`, agree at `2`. -/
theorem eq_at_two_of_one {σ τ : Label.{u} → Label.{u}} (hσ : IsWitness (stepSuppressor 2) σ)
    (hτ : IsWitness (stepSuppressor 2) τ) {c : Label.{u}} (hτc : τ 1 < c)
    (hag : min (σ 1) c = min (τ 1) c) : σ 2 = τ 2 := by
  have h12 : visibilityReplace 2 2 (1 : Label.{u}) = 2 := by
    have h1 : (1 : Label.{u}) = (((Ordinal.omega0 * (0 : Ordinal.{u}) + ((1 : ℕ) : Ordinal.{u}) :
        Ordinal.{u})) : Label.{u}) := by simp
    have h2 : (2 : Label.{u}) = (((Ordinal.omega0 * (0 : Ordinal.{u}) + ((2 : ℕ) : Ordinal.{u}) :
        Ordinal.{u})) : Label.{u}) := by simp
    rw [h1, h2, visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast]
    simp
  exact eq_at_cut_of_strip hσ hτ h12 hτc hag

end Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}

/-- **The lift decoded in two stages is lawful**, at the actual lifted section: for a lawful
admitted `P` with values in the code grid at `k` (a state of the catalogue of the replicated scheme
with the values `codeGrid k B` and the block bound `B'` of its heights, `codeGrid k B` below the
grid point at `2`), a cut `h ≠ ⊥` self-visible at `k`, a witness `ρ` bounded by `k`, a cap
`c ≠ ⊥`, and an ambient `q` lawful below `(univ, k)` with which the decoded lift agrees capped at
`c`, the lift `ρ ∘ orbitDecoder k f h ∘ w_P` is lawful below `(univ, k)`. -/
theorem isLawfulBelow_twoStage {B B' : ℕ}
    {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop}
    (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ codeGrid.{u} (m + 1) B, x ≤ gridPoint 2 B')
    (hA : ∀ k R, A (k + 3) R → A (k + 2) R) {P : Fin (I.attachment g).card → Label.{u}}
    (hP : P ∈ (I.attachmentBase g).towerCat (codeGrid (m + 1) B) A (m + 2)) {k : ℕ}
    {f : Fin (I.attachment g).card → Label.{u}} {h : Label.{u}} (hh : IsSelfVisible k h)
    (h0 : h ≠ ⊥) {ρ : Label.{u} → Label.{u}} (hρ : IsWitness (stepSuppressor k) ρ)
    {c : Label.{u}} (hc0 : c ≠ ⊥)
    {q : (I.replicated g H (codeGrid (m + 1) B) A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), k) → Label.{u}}
    (hq : (I.replicated g H (codeGrid (m + 1) B) A B').rows.IsLawfulBelow
      ((univ : Finset (Fin (m + 2))), k) q)
    (hag : ∀ d : (I.replicated g H (codeGrid (m + 1) B) A B').toCellScheme.below
        ((univ : Finset (Fin (m + 2))), k),
      min (ρ (orbitDecoder k f h (I.replicatedWriting g H (codeGrid (m + 1) B) A B' P d.1))) c =
        min (q d) c) :
    (I.replicated g H (codeGrid (m + 1) B) A B').rows.IsLawfulBelow
      ((univ : Finset (Fin (m + 2))), k)
      fun d ↦ ρ (orbitDecoder k f h (I.replicatedWriting g H (codeGrid (m + 1) B) A B' P d)) := by
  have hstage₁ := isLawfulBelow_map_replicatedWriting hH hcard hΓ hA hP
    ((univ : Finset (Fin (m + 2))), k) (isWitness_orbitDecoder hh h0) fun x hx ↦ by
      have : min x h ≤ orbitDecoder k f h x := le_max_left _ _
      rw [hx, le_bot_iff, min_eq_bot] at this
      exact this.resolve_right h0
  exact hstage₁.map_of_min_eq hq (fun d ↦ d.2.2) hρ hc0 hag

end Seed

end VaughtConjecture
