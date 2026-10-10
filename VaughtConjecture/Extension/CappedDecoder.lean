/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapTransport
import VaughtConjecture.Stage.Scheme
import VaughtConjecture.Label.StepWitness

/-!
# The capped decoder of a section at the cap

Roadmap, Layer 3 (the decoders of the constructions of 3.3: the LOW step of (R2) and the relative
lift of the growth construction of (R3) and (R4)).

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
the form in which lawfulness is transported (`CellScheme.Rows.IsLawful.map_of_bot_iff`).  The LOW
step reads the donor face at a cap through it (`VaughtConjecture.Continuation.LowStepTie`), and so
does the donor of the growth construction.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.

## References

Locality and witnesses are [Kni26, Definition 2.3.9 and Definition 2.5.12].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Label

/-- **The capped controller map commutes with visibility replacement**: for a witness `(g, σ)`,
`x ↦ min (σ x) (g N)` commutes with visibility replacement at `N` with every value `i ≤ N`. -/
theorem IsWitness.min_visibilityReplace {g : ℕ → Label.{u}}
    {σ : Label.{u} → Label.{u}} (hw : IsWitness g σ) {N i : ℕ} (hi : i ≤ N) (x : Label.{u}) :
    min (σ (visibilityReplace N i x)) (g N) = visibilityReplace N i (min (σ x) (g N)) := by
  by_cases hx : σ x ≤ g N
  · rw [hw.visibilityReplace_comm x N hx i hi, min_eq_left hx,
      min_eq_left (visibilityReplace_le_of_le hi (hw.isSelfVisible N) hx)]
  · have hlt := hw.lt_apply_visibilityReplace (not_le.mp hx) hi
    rw [min_eq_right hlt.le, min_eq_right (not_le.mp hx).le,
      (hw.isSelfVisible N).visibilityReplace_eq]

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

namespace Scheme

open Finset Label
variable {n : ℕ} {S : Scheme.{u} n}

/-- **The capped decoder of a section lawful below a pair**, at a cell `c` below the pair of grade
`N`: a witness bounded by `N`, bounded by the label of `c`, reading the row of `c` as the section
capped at `c` (`Scheme.exists_cappedDecoder_isWitness` for sections lawful below a pair). -/
theorem exists_cappedDecoder_below {Y : Finset (Fin n) × ℕ} {w : Fin S.card → Label.{u}}
    (hw : S.rows.IsLawfulBelow Y fun d ↦ w d) {c : Fin S.card}
    (hcY : c ∈ S.toCellScheme.below Y) {N : ℕ} (hcN : S.toCellScheme.grade c = N) :
    ∃ θ : Label.{u} → Label.{u}, IsWitness (stepSuppressor N) θ ∧ (∀ x, θ x ≤ w c) ∧
      ∀ d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex c),
        θ (S.rowAt c d) = min (w d) (w c) := by
  obtain ⟨hord, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hw
  obtain ⟨g, σ, hwit, hq⟩ := hloc c hcY
  have hcb : c ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex c) :=
    CellScheme.mem_below_gradedIndex _ c
  have hvc : IsSelfVisible N (w c) := hcN ▸ hord c hcY
  have hqc := hq ⟨c, hcb⟩
  simp only [min_self] at hqc
  rw [hcN] at hqc
  have hvcg : w c ≤ g N := hqc ▸ min_le_right _ _
  refine ⟨fun x ↦ min (min (σ x) (g N)) (w c),
    ⟨(IsWitness.id_step N).antitone, (IsWitness.id_step N).isSelfVisible, by simp [hwit.map_bot],
      fun x y hxy ↦ min_le_min_right _ (min_le_min_right _ (hwit.monotone hxy)),
      fun x k hx i hi ↦ ?_⟩, fun x ↦ min_le_right _ _, fun d hd ↦ ?_⟩
  · by_cases hk : k ≤ N
    · rw [hwit.min_visibilityReplace_of_le hk hi,
        visibilityReplace_min_of_isSelfVisible hi (hvc.mono hk)]
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
      rw [hx, visibilityReplace_bot]
      rcases min_eq_bot.mp hx with h | h
      · rcases min_eq_bot.mp h with h' | h'
        · rw [hwit.apply_visibilityReplace_eq_bot h' k hi]; simp
        · rw [h']; simp
      · rw [h]; simp
  · have hqd := hq ⟨d, hd⟩
    simp only at hqd
    rw [← rowAt_of_mem hd] at hqd
    have hgd : g N ≤ g (S.toCellScheme.grade d) := by
      apply hwit.antitone
      have := hd.2
      simp only [CellScheme.gradedIndex_snd] at this
      rw [hcN] at this
      exact this
    have hle : min (w d) (w c) ≤ g N := (min_le_right _ _).trans hvcg
    have h1 : min (σ (S.rowAt c d)) (g N) = min (w d) (w c) := by
      apply le_antisymm
      · rw [hqd]
        exact le_min (min_le_left _ _) ((min_le_right _ _).trans hgd)
      · rw [hqd] at hle ⊢
        exact le_min (min_le_left _ _) hle
    beta_reduce
    rw [h1, min_assoc, min_self]

end Scheme

namespace Scheme

open Finset Label
variable {n : ℕ} {S : Scheme.{u} n}

/-- **Equal readings give equal capped values**: in a section lawful below `Y`, two cells read
alike by a cell `u` below `Y` carry the same label capped at the label of `u`. -/
theorem min_eq_min_of_rowAt_eq {Y : Finset (Fin n) × ℕ} {w : Fin S.card → Label.{u}}
    (hw : S.rows.IsLawfulBelow Y fun d ↦ w d) {u t v : Fin S.card}
    (huY : u ∈ S.toCellScheme.below Y)
    (ht : t ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u))
    (hv : v ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u))
    (hrow : S.rowAt u t = S.rowAt u v) : min (w t) (w u) = min (w v) (w u) := by
  obtain ⟨θ, -, -, hθ⟩ := exists_cappedDecoder_below hw huY rfl
  rw [← hθ t ht, ← hθ v hv, hrow]

end Scheme

end VaughtConjecture
