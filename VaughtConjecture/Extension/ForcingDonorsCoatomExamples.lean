/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Expansion.UniquenessOfForcing
import VaughtConjecture.Extension.ForcingDonorsCoatom

/-!
# Examples: forcing donors from the coatom extension property

Roadmap, Layer 3 (the finite construction for forcing donors), for Layer 4, output 2, and the
hypotheses of the main theorem (Layer 6, "Status").

* **The hypothesis `ForcingDonors` follows from the apex form**: the coatom extension
  property with apex at every countable block stage gives forcing donors at every countable block
  index, and, with (R1), next-block uniqueness.
* **The smallest input no tie serves**: a two-point type, a cell of grade `1` labelled at least
  `λ_η + 2`, the threshold `2`; a donor exists unconditionally.
* **Two-point inputs up to the threshold `4`**, unconditionally, at `η = 0`.
* **The part below the full grade** of a legal type is legal below the full grade, and adding the
  apex to it gives a legal type with the same proper faces.
-/

universe u

namespace VaughtConjecture.ForcingDonorsCoatomExamples

open Finset Ordinal

/-- **Forcing donors at every countable block index from the apex form at every countable block
stage.** -/
example (hext : ∀ η < ω₁, StageType.HasApexCoatomExtensions.{0} (blockStage η)) :
    ∀ ξ < ω₁, ForcingDonors.{0} ξ :=
  forcingDonors_of_forall_hasApexCoatomExtensions hext

/-- **Next-block uniqueness from (R1) and the apex form**: forcing donors are no longer a separate
hypothesis. -/
example (hrec : Expansion.FiniteCutReceiving.{0})
    (hext : ∀ η < ω₁, StageType.HasApexCoatomExtensions.{0} (blockStage η)) :
    Expansion.NextBlockUniqueness.{0} :=
  Expansion.NextBlockUniqueness.of_forcingDonors hrec
    (forcingDonors_of_forall_hasApexCoatomExtensions hext)

/-- **The smallest input no tie serves has a donor**: a legal two-point type with a cell of grade
`1` reducing to the formal top and labelled at least `λ_η + 2` is forced to `2` by the reduction
of a legal extension. -/
example {η : Ordinal.{u}} (t : StageType.{u} (blockStage (η + 1)) 2) (ht : t.IsLegal)
    (d : Fin t.card) (hd : (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤)
    (hl : ((blockStage η + 2 : Ordinal.{u}) : Label.{u}) ≤ t.label d) :
    ∃ (m : ℕ) (D : StageType.{u} (blockStage (η + 1)) m) (g : Fin 2 ↪ Fin m),
      D.IsLegal ∧ StageType.restrictFace g D = some t ∧
      StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η)
        (D.reduce (isSuccPrelimit_blockStage η)) g (t.reduce (isSuccPrelimit_blockStage η)) d 2 :=
  exists_forcingDonor_twoPoint_le_two t ht d hd 2 hl le_rfl

/-- **Two-point inputs at `η = 0`, up to the threshold `4`**, unconditionally. -/
example : ForcingDonorsUpTo.{u} 0 2 4 := forcingDonorsUpTo_two_four

/-- **The part below the full grade, and the apex over it**: from a legal type on `N` points, a
legal type on `N` points with the same faces along every proper face. -/
example {α : Ordinal.{u}} {N k : ℕ} {W : StageType.{u} α N} (hW : W.IsLegal) (hN : 0 < N)
    (g : Fin k ↪ Fin N) (hg : Finset.univ.map g ≠ Finset.univ) :
    (W.partBelowFullGrade.addApex hW.isLegalBelowFullGrade_partBelowFullGrade hN).IsLegal ∧
      StageType.restrictFace g
        (W.partBelowFullGrade.addApex hW.isLegalBelowFullGrade_partBelowFullGrade hN) =
        StageType.restrictFace g W :=
  ⟨StageType.isLegal_addApex _ hN, (StageType.restrictFace_addApex _ hN g hg).trans
    (W.restrictFace_partBelowFullGrade g hg)⟩

end VaughtConjecture.ForcingDonorsCoatomExamples
