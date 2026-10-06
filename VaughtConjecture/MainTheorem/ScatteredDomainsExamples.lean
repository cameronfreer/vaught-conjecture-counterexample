/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ScatteredDomains

/-!
# Examples for thinness in scatteredness form on the expansion-domain route

Special cases of `VaughtConjecture.MainTheorem.ScatteredDomains`:

* the level `η = 0`: under the hypotheses of
  `densitySentence_bfScattered_of_terminalClassification`, the codes of models of the density
  sentence fall into countably many classes of `bfEquivSetoid densitySentence 0`;
* the generic statement with every class in every set: if all codes of models of a sentence are
  back-and-forth equivalent at every countable level, the sentence is back-and-forth scattered;
* the two thinness theorems are `isThinOn_of_bfScattered` applied to the scatteredness theorems,
  by `rfl`;
* every family of full presentations has scattered tails under the hypotheses of the terminal
  classification.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

namespace VaughtConjecture.MainTheorem

open Ordinal FirstOrder Language Structure baseLanguage Expansion
open scoped Ordinal

variable (hcap : CapToModel.{0}) (hrec : FiniteCutReceiving.{0})
  (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ) (hcont : ContinuationCriterion.{0})
  (hres : Realization.ResidualReceiving.{0, 0})
  (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock)

/-- At the level `0`, the codes of models of the density sentence fall into countably many
classes of back-and-forth equivalence, under the hypotheses of the terminal classification. -/
example : Countable (Quotient (bfEquivSetoid densitySentence.{0} 0)) :=
  densitySentence_bfScattered_of_terminalClassification hcap hrec hF hcont hres hhol 0
    (omega0_pos.trans omega0_lt_omega_one)

/-- The generic statement with every class in every set: back-and-forth equivalence of all codes
of models at every countable level gives back-and-forth scatteredness. -/
example {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]
    {φ : L.Sentenceω} (h : ∀ η < ω₁, ∀ c d : ModelsOf φ, CodeBFEquiv η c.1 d.1) :
    BFScattered (ModelsOf φ) :=
  bfScattered_of_countable_compl (fun _ ↦ Set.univ) (fun _ _ ↦ by simp)
    fun η hη c d _ _ ↦ h η hη c d

/-- Thinness from the terminal classification in scatteredness form is `isThinOn_of_bfScattered`
applied to back-and-forth scatteredness. -/
example : densitySentence_isThinOnNatModels_of_terminalClassification_bfScattered hcap hrec hF
    hcont hres hhol = isThinOn_of_bfScattered
      (densitySentence_bfScattered_of_terminalClassification hcap hrec hF hcont hres hhol) :=
  rfl

/-- Under the hypotheses of the terminal classification, every family of full presentations has
scattered tails. -/
example (P : FullPresentations DensityClass) : P.HasScatteredTails :=
  .of_bfScattered P
    (densitySentence_bfScattered_of_terminalClassification hcap hrec hF hcont hres hhol)

end VaughtConjecture.MainTheorem
