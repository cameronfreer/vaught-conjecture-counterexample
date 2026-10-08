/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthControllerRecovery
import VaughtConjecture.Label.StepWitness
import VaughtConjecture.Extension.CapTransport

/-!
# The capped decoder of a section at the cap

Roadmap, Layer 3 ((R3) and (R4), the relative lift of the growth construction).

Let `u` be a lawful section of a scheme and `c` a cell of grade `N`.  Locality at `c` gives a
witness `(g, σ)` with `min (u d) (u c) = min (σ (row_c d)) (g (grade d))` for every cell `d` below
`c`.  The **capped decoder** `θ x = min (min (σ x) (g N)) (u c)`
(`Scheme.exists_cappedDecoder`):

* sends the row of `c` to the section capped at `u c`: `θ (row_c d) = min (u d) (u c)` for every
  `d` below `c`;
* is bounded by `u c`, fixes `⊥`, is monotone;
* commutes with visibility replacement at **every** threshold `k ≤ N` with every value `i ≤ k`,
  unconditionally: below the suppressor at `N` the witness commutes since `g N ≤ g k`; above it
  the value `g N` is kept, by `Label.IsWitness.lt_apply_visibilityReplace`
  or by the crossing lemma `Label.IsSelfVisible.le_visibilityReplace_iff` at `k < N`, and by
  `Label.IsWitness.min_visibilityReplace` at `k = N`; capping at `u c`, self-visible at `N`,
  commutes with visibility replacement at `k ≤ N`.

So `θ` is a witness bounded by the grade `N` (`Label.IsWitness` with `Label.stepSuppressor N`),
the form in which lawfulness is transported (`CellScheme.Rows.IsLawful.map_of_bot_iff`).  This is
the decoder through which the donor of the growth construction reads the cap.

## References

Locality and witnesses are [Kni26, Definition 2.3.9 and Definition 2.5.12].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Label

/-- **A capped witness commutes with visibility replacement below the cap's threshold**: for a
witness `(g, σ)` and `k ≤ N`, `x ↦ min (σ x) (g N)` commutes with visibility replacement at `k`
with every value `i ≤ k`. -/
theorem IsWitness.min_visibilityReplace_of_le {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}
    (hw : IsWitness g σ) {N k i : ℕ} (hk : k ≤ N) (hi : i ≤ k) (x : Label.{u}) :
    min (σ (visibilityReplace k i x)) (g N) = visibilityReplace k i (min (σ x) (g N)) := by
  rcases hk.lt_or_eq with hlt | rfl
  swap
  · exact hw.min_visibilityReplace hi x
  have hgk : g N ≤ g k := hw.antitone hk
  have hvN : IsSelfVisible N (g N) := hw.isSelfVisible N
  have hvk : IsSelfVisible k (g N) := hvN.mono hk
  by_cases hx : σ x ≤ g N
  · rw [hw.visibilityReplace_comm x k (hx.trans hgk) i hi, min_eq_left hx,
      min_eq_left (visibilityReplace_le_of_le hi hvk hx)]
  · have hx' : g N < σ x := not_le.mp hx
    rw [min_eq_right hx'.le, hvk.visibilityReplace_eq]
    apply min_eq_right
    by_cases hxk : σ x ≤ g k
    · rw [hw.visibilityReplace_comm x k hxk i hi]
      obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
      exact (IsSelfVisible.le_visibilityReplace_iff hvN (by omega) hi (σ x)).mpr hx'.le
    · exact hgk.trans (hw.lt_apply_visibilityReplace (not_le.mp hxk) hi).le

end Label

namespace Scheme

variable {m : ℕ} {S : Scheme.{u} m}

/-- **The capped decoder of a lawful section at a cell `c` of grade `N`**: a monotone map fixing
`⊥`, bounded by `v c`, commuting with visibility replacement at every threshold `k ≤ N` with every
value `i ≤ k`, and sending the row of `c` at each cell `d` below `c` to `min (v d) (v c)`. -/
theorem exists_cappedDecoder {v : Fin S.card → Label.{u}} (hv : S.rows.IsLawful v)
    {c : Fin S.card} {N : ℕ} (hcN : S.toCellScheme.grade c = N) :
    ∃ θ : Label.{u} → Label.{u}, Monotone θ ∧ θ ⊥ = ⊥ ∧ (∀ x, θ x ≤ v c) ∧
      (∀ k ≤ N, ∀ i ≤ k, ∀ x, θ (visibilityReplace k i x) = visibilityReplace k i (θ x)) ∧
      (∀ x, θ x = ⊥ → ∀ k i, i ≤ k → θ (visibilityReplace k i x) = ⊥) ∧
      ∀ d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex c),
        θ (S.rowAt c d) = min (v d) (v c) := by
  obtain ⟨g, σ, hw, hq⟩ := hv.locality c
  have hcb : c ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex c) :=
    CellScheme.mem_below_gradedIndex _ c
  have hvc : IsSelfVisible N (v c) := hcN ▸ hv.orderly c
  have hqc := hq ⟨c, hcb⟩
  simp only [min_self] at hqc
  rw [hcN] at hqc
  -- `v c = min (σ (row_c c)) (g N)`
  have hvcg : v c ≤ g N := hqc ▸ min_le_right _ _
  refine ⟨fun x ↦ min (min (σ x) (g N)) (v c), fun x y hxy ↦
    min_le_min_right _ (min_le_min_right _ (hw.monotone hxy)), by simp [hw.map_bot],
    fun x ↦ min_le_right _ _, fun k hk i hi x ↦ ?_, fun x hx k i hi ↦ ?_, fun d hd ↦ ?_⟩
  · beta_reduce
    rw [hw.min_visibilityReplace_of_le hk hi,
      visibilityReplace_min_of_isSelfVisible hi (hvc.mono hk)]
  · beta_reduce at hx ⊢
    rcases min_eq_bot.mp hx with h | h
    · rcases min_eq_bot.mp h with h' | h'
      · rw [hw.apply_visibilityReplace_eq_bot h' k hi]; simp
      · rw [h']; simp
    · rw [h]; simp
  · have hqd := hq ⟨d, hd⟩
    simp only at hqd
    rw [← rowAt_of_mem hd] at hqd
    have hgd : g N ≤ g (S.toCellScheme.grade d) := by
      apply hw.antitone
      have := hd.2
      simp only [CellScheme.gradedIndex_snd] at this
      rw [hcN] at this
      exact this
    -- `min (v d) (v c) = min (σ (row d)) (g (grade d))`, which is at most `v c ≤ g N`
    have hle : min (v d) (v c) ≤ g N := (min_le_right _ _).trans hvcg
    have h1 : min (σ (S.rowAt c d)) (g N) = min (v d) (v c) := by
      apply le_antisymm
      · rw [hqd]
        refine le_min (min_le_left _ _) ((min_le_right _ _).trans hgd)
      · rw [hqd] at hle ⊢
        exact le_min (min_le_left _ _) hle
    beta_reduce
    rw [h1, min_assoc, min_self]

/-- **The capped decoder is a witness bounded by the grade `N`**: commuting with visibility
replacement at the thresholds `≤ N`, and above them its zero set is closed under every visibility
replacement (`Label.IsWitness.apply_visibilityReplace_eq_bot`). -/
theorem exists_cappedDecoder_isWitness {v : Fin S.card → Label.{u}} (hv : S.rows.IsLawful v)
    {c : Fin S.card} {N : ℕ} (hcN : S.toCellScheme.grade c = N) :
    ∃ θ : Label.{u} → Label.{u}, IsWitness (stepSuppressor N) θ ∧ (∀ x, θ x ≤ v c) ∧
      ∀ d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex c),
        θ (S.rowAt c d) = min (v d) (v c) := by
  obtain ⟨θ, hθm, hθb, hθle, hθv, hθz, hθr⟩ := exists_cappedDecoder hv hcN
  refine ⟨θ, ⟨(IsWitness.id_step N).antitone, (IsWitness.id_step N).isSelfVisible, hθb, hθm,
    fun x k hx i hi ↦ ?_⟩, hθle, hθr⟩
  by_cases hk : k ≤ N
  · exact hθv k hk i hi x
  · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
    rw [hx, visibilityReplace_bot]
    exact hθz x hx k i hi

end Scheme

end VaughtConjecture
