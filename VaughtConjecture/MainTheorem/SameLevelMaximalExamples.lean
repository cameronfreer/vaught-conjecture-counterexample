/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.SameLevelMaximal

/-!
# Special cases of the same-level maximal realization

Special cases of `VaughtConjecture.MainTheorem.SameLevelMaximal`:

* the age of top-free charts is contained in the age of legal charts;
* a realization at a block stage whose actual types are top-free is cover-hollow vacuously
  (`Realization.isCoverHollow_of_isTopFree`), hence terminal, with no hypothesis; for the
  reconstruction of a structure covered by top-free charts this is the terminality of the top-free
  witnesses (`reduce_ne_reconstruct`) at the next block stage;
* acceptance lemma 1 at the first block, `λ_0 = ω`, on the carrier `ℕ`, with a prescribed cover of
  the one-point stage type with the bottom label at the point `0`.

## Placement

This file belongs to the section "Reduction to full presentations" of `roadmap/README.md`.
-/

namespace VaughtConjecture.MainTheorem.SameLevelMaximalExamples

open FirstOrder Language Realization

/-- The age of top-free charts is contained in the age of legal charts. -/
example {α : Ordinal.{0}} : topFreeAge α ⊆ legalAge α := fun _ ⟨i, he⟩ ↦
  ⟨⟨i.1, i.2.1, i.2.2.1⟩, he⟩

/-- A realization at a block stage with top-free actual types is terminal. -/
example {ξ : Ordinal.{0}} {M : Type} {R : Realization.{0, 0} (blockStage ξ) M}
    (h : ∀ x : R.Occurrence, x.type.IsTopFree) : R.IsTerminalAt ξ :=
  (isCoverHollow_of_isTopFree h).isTerminalAt

/-- Acceptance lemma 1 at the first block, on `ℕ`, with the one-point stage type with the bottom
label covered by the point `0`. -/
example (hext : StageType.HasApexCoatomExtensions.{0} (blockStage 0))
    (hF : ForcingDonors.{0} 0) :
    ∃ H : Realization.{0, 0} (blockStage 0) ℕ, H.IsModel ∧
      H.Covers (TopFreeIndex.point (blockStage 0)).2.1 ![0] ∧ H.IsTerminalAt 0 := by
  obtain ⟨H, hH, hc, -, -, -, ht⟩ := exists_sameLevelMaximal_covers
    (Ordinal.omega0_pos.trans Ordinal.omega0_lt_omega_one) hext hF ℕ
    (TopFreeIndex.point (blockStage 0)).2.2.1 ⟨![0], fun i j _ ↦ Subsingleton.elim (α := Fin 1) i j⟩
  exact ⟨H, hH, hc, ht⟩

end VaughtConjecture.MainTheorem.SameLevelMaximalExamples
