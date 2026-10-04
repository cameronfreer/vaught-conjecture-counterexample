/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import VaughtConjecture.Continuation.Normalization

/-!
# Examples for normalization and the stable label

Special cases of `VaughtConjecture.Continuation.Normalization`:

* **repeated coordinates**: a tuple with a repeated coordinate has no rooted cover, so its stable
  offset is the empty supremum `0`; the stable label is meaningful only at covers, which is why the
  threshold lemma has a `Covers` hypothesis;
* **the stable value `⊤`**: the stable label is the formal top exactly when every threshold is
  forced by some rooted cover;
* **a finite stable offset**: under the hypotheses of the threshold lemma, the label is `λ_η + n`
  exactly when `n` is forced by some rooted cover and `n + 1` by none;
* **the block index `η = 0`**: normalization of labels at `λ_1 = ω + ω` from the reduction to `ω`;
* **the unconditional case**: two realizations at `λ_{η+1}` with equal reductions to `λ_η`, where
  the types of the first have no cell reducing to the formal top, are equal with no hypothesis on
  receiving or forcing donors.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture.Continuation.NormalizationExamples

open Ordinal Realization StageType

variable {α β : Ordinal.{u}} {hβ : Order.IsSuccPrelimit β} {M : Type v} {k : ℕ}

/-! ### Repeated coordinates -/

/-- A tuple with a repeated coordinate has no rooted cover. -/
theorem not_extendsToCover_pair {S : Realization.{u, v} β M} (a : M)
    (x : Σ m : ℕ, StageType.{u} β m × (Fin 2 ↪ Fin m)) : ¬ S.ExtendsToCover ![a, a] x :=
  fun h ↦ Fin.zero_ne_one (show (0 : Fin 2) = 1 from h.injective rfl)

/-- The stable offset at a tuple with a repeated coordinate is the empty supremum `0`. -/
example {S : Realization.{u, v} β M} (a : M) (p : StageType.{u} β 2) (d : Fin p.card) :
    S.stableOffset α hβ ![a, a] p d = 0 :=
  le_antisymm (iSup₂_le fun x hx ↦ absurd hx (not_extendsToCover_pair a x)) zero_le

/-! ### The stable value `⊤` -/

/-- **The stable value `⊤`**: at a cover of the root, the stable label is the formal top exactly
when every threshold is forced by some rooted cover.  It is never `β + ω`. -/
example {S : Realization.{u, v} β M} {c : Fin k → M} {p : StageType.{u} β k} {d : Fin p.card}
    (hc : S.Covers p c) (hd : p.label d = ⊤) :
    (S.stableLabel α hβ c p d = ⊤ ↔ ∀ n : ℕ, ∃ x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m),
      ForcesThreshold α hβ x.2.1 x.2.2 p d n ∧ S.ExtendsToCover c x) ∧
    S.stableLabel α hβ c p d ≠ ((β + ω : Ordinal.{u}) : Label.{u}) := by
  refine ⟨?_, Label.ofOffset_ne_coe_add_omega0⟩
  rw [stableLabel, Label.ofOffset_eq_top_iff, ENat.eq_top_iff_forall_ge]
  exact forall_congr' fun n ↦ natCast_le_stableOffset_iff hc hd

/-! ### A finite stable offset -/

section Finite

variable {η : Ordinal.{u}} {R : Realization.{u, v} (blockStage (η + 1)) M}
  {t : StageType.{u} (blockStage (η + 1)) k} {c : Fin k → M}

/-- **A finite stable offset**, conditional as the threshold lemma: the label of `d` is `λ_η + n`
exactly when some rooted cover forces `n` at `d` and none forces `n + 1`. -/
example (hR : R.IsConsistent) (hl : R.HasLegalTypes) (hrec : R.HasFiniteExtensionReceiving)
    (hF : ForcingDonors.{u} η) (hc : R.Covers t c) (d : Fin t.card)
    (hd : (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤) (n : ℕ) :
    t.label d = ((blockStage η + n : Ordinal.{u}) : Label.{u}) ↔
      (∃ x : Σ m : ℕ, StageType.{u} (blockStage η) m × (Fin k ↪ Fin m),
        ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η) x.2.1 x.2.2
          (t.reduce (isSuccPrelimit_blockStage η)) d n ∧
        (R.reduce (isSuccPrelimit_blockStage η)).ExtendsToCover c x) ∧
      ¬ ∃ x : Σ m : ℕ, StageType.{u} (blockStage η) m × (Fin k ↪ Fin m),
        ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η) x.2.1 x.2.2
          (t.reduce (isSuccPrelimit_blockStage η)) d (n + 1) ∧
        (R.reduce (isSuccPrelimit_blockStage η)).ExtendsToCover c x := by
  rw [← le_label_iff_exists_forcesThreshold hR hl hrec hF hc d hd,
    ← le_label_iff_exists_forcesThreshold hR hl hrec hF hc d hd, Nat.cast_succ, ← add_assoc]
  refine ⟨fun h ↦ ⟨h.ge, fun h' ↦ ?_⟩, fun ⟨h1, h2⟩ ↦
    le_antisymm (Label.lt_coe_add_one_iff.mp (not_le.mp h2)) h1⟩
  rw [h] at h'
  exact (Order.lt_add_one_iff.mpr le_rfl).not_ge (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h'))

end Finite

/-! ### The block index `η = 0` -/

/-- **Normalization of labels at `η = 0`**, conditional as the threshold lemma: at `λ_1 = ω + ω`,
the label of a cell reducing to the formal top at `ω` is its stable label, read in the reduction
to `ω`. -/
example {R : Realization.{u, v} (blockStage (0 + 1)) M}
    {t : StageType.{u} (blockStage (0 + 1)) k} {c : Fin k → M} (hR : R.IsConsistent)
    (hl : R.HasLegalTypes) (hrec : R.HasFiniteExtensionReceiving) (hF : ForcingDonors.{u} 0)
    (hc : R.Covers t c) (d : Fin t.card)
    (hd : (t.reduce (isSuccPrelimit_blockStage 0)).label d = ⊤) :
    t.label d = (R.reduce (isSuccPrelimit_blockStage 0)).stableLabel (blockStage (0 + 1))
      (isSuccPrelimit_blockStage 0) c (t.reduce (isSuccPrelimit_blockStage 0)) d :=
  label_eq_stableLabel hR hl hrec hF hc d hd

/-! ### The unconditional case -/

/-- **No cell reducing to the top**: if no type of `R` has a cell reducing to the formal top at
`λ_η`, then a realization `R'` with the same reduction to `λ_η` is `R`, with no hypothesis on
receiving, legality, consistency or forcing donors. -/
example {η : Ordinal.{u}} {R R' : Realization.{u, v} (blockStage (η + 1)) M}
    (hnt : ∀ {n : ℕ} (u : Fin n ↪ M) (t : StageType.{u} (blockStage (η + 1)) n),
      R.eval u = some t → ∀ i, (t.reduce (isSuccPrelimit_blockStage η)).label i ≠ ⊤)
    (h : R.reduce (isSuccPrelimit_blockStage η) = R'.reduce (isSuccPrelimit_blockStage η)) :
    R = R' := by
  refine Realization.ext fun u ↦ ?_
  have hu : (R.eval u).map (StageType.reduce · (isSuccPrelimit_blockStage η)) =
      (R'.eval u).map (StageType.reduce · (isSuccPrelimit_blockStage η)) := by
    rw [← reduce_eval, ← reduce_eval, h]
  cases ht : R.eval u with
  | none =>
    rw [ht, Option.map_none] at hu
    exact (Option.map_eq_none_iff.mp hu.symm).symm
  | some t =>
    rw [ht, Option.map_some] at hu
    obtain ⟨t', ht', htt'⟩ := Option.map_eq_some_iff.mp hu.symm
    rw [ht']
    exact congrArg some (eq_of_reduce_eq_of_label_eq _ htt'.symm fun i _ _ hi ↦
      absurd hi (hnt u t ht i))

end VaughtConjecture.Continuation.NormalizationExamples
