/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.AllCarriers

/-!
# Examples of the reduction to `ℕ`

The special cases of `VaughtConjecture.MainTheorem.AllCarriers`: the carrier `ℕ` itself, a carrier
in another universe, a finite carrier, and the universes of the statements for the density
sentence.

* **The carrier `ℕ`.**  In the universe `0`, a coded model `c` is also a countable model on `ℕ`
  itself, with the structure of `c` (`onNat c`).  The reduction to `ℕ` sends the class of `c` to
  the class of `onNat c`, and, when the sentence has no finite models, the inverse of the reduction
  to `ℕ` sends the class of `onNat c` back to the class of `c`: on `ℕ` the reduction to `ℕ` is the
  identity.
* **A countably infinite model in `Type 1`.**  For the empty language and the true sentence, the
  structure on `ULift.{1} ℕ` is a countable model on a carrier in the universe `1`, and its class is
  the class of a code (`mk_mem_range_classOfCode`), with no hypothesis on finite models.
* **Finite models are excluded by hypothesis.**  For the same sentence, the one-point model on
  `PUnit` (in any universe) is countable, and its class is not the class of any code: the reduction
  to `ℕ` is not onto when the sentence has finite models.
* **Universes.**  The classes of countable models of the density sentence on the carriers of the
  universe `w` form a type in the universe `w + 1`; the coded classes `DensityClass` are in the
  universe `1`.  The statements on all countable carriers for `w = 0` and `w = 1` follow from the
  spectrum on `ℕ` under the cap-to-model theorem for the carriers of the same universe.
-/

universe w

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Structure Cardinal

/-! ### The carrier `ℕ` -/

section Nat

variable {L : Language.{0, 1}} [L.IsRelational] {φ : L.Sentenceω}

/-- A coded model as a countable model on `ℕ` itself, in the universe `0`. -/
private noncomputable def onNat (c : ModelsOf φ) : CountableModel.{0} φ :=
  letI := c.1.toStructure
  { carrier := ℕ
    realize := (SmallVocabulary.mem_modelsOf_iff_realize L c.1 φ).mp c.2 }

/-- On `ℕ`, the reduction to `ℕ` sends the class of a code to the class of the code's own
structure. -/
example (c : ModelsOf φ) : classOfCode.{0} φ ⟦c⟧ = ⟦onNat c⟧ :=
  CountableModelClass.mk_eq_mk_iff.mpr ⟨CountableModel.ofCodeEquiv c⟩

/-- On `ℕ`, the inverse of the reduction to `ℕ` sends the class of a code's own structure back to
the class of the code. -/
example (hinf : ∀ (M : Type) [L.Structure M] [Countable M], φ.Realize M → Infinite M)
    (c : ModelsOf φ) : (codedClassEquiv hinf).symm ⟦onNat c⟧ = ⟦c⟧ :=
  (codedClassEquiv hinf).symm_apply_eq.mpr
    (CountableModelClass.mk_eq_mk_iff.mpr ⟨CountableModel.ofCodeEquiv c⟩).symm

end Nat

/-! ### The empty language: an infinite carrier in `Type 1`, and a finite carrier -/

section Empty

/-- The true sentence of the empty language. -/
private abbrev trueSentence : Language.empty.Sentenceω := ⊤

/-- The countable model `ULift.{1} ℕ` of the true sentence, on a carrier in the universe `1`. -/
private def natInTypeOne : CountableModel.{1} trueSentence :=
  { carrier := ULift.{1} ℕ
    str := Language.emptyStructure
    realize := fun h ↦ h }

/-- A countably infinite model in `Type 1` has the class of a code. -/
example : ⟦natInTypeOne⟧ ∈ Set.range (classOfCode.{1} trueSentence) :=
  have : Infinite natInTypeOne.carrier := inferInstanceAs (Infinite (ULift.{1} ℕ))
  mk_mem_range_classOfCode natInTypeOne

/-- The one-point model of the true sentence, on a carrier in the universe `w`. -/
private def point : CountableModel.{w} trueSentence :=
  { carrier := PUnit.{w + 1}
    str := Language.emptyStructure
    realize := fun h ↦ h }

/-- The class of the one-point model is not the class of any code: without the absence of finite
models, the reduction to `ℕ` is not onto. -/
example : ⟦point.{w}⟧ ∉ Set.range (classOfCode.{w} trueSentence) := by
  rintro ⟨q, hq⟩
  induction q using Quotient.inductionOn with
  | h c =>
    obtain ⟨e⟩ := CountableModelClass.mk_eq_mk_iff.mp hq
    have : Infinite (CountableModel.ofCode.{w} c).carrier :=
      inferInstanceAs (Infinite (ULift.{w} ℕ))
    have : Finite point.{w}.carrier := inferInstanceAs (Finite PUnit.{w + 1})
    have := Finite.of_injective _ e.injective
    exact not_finite (CountableModel.ofCode.{w} c).carrier

end Empty

/-! ### Universes of the statements for the density sentence -/

section Density

open baseLanguage

/-- The classes of countable models of the density sentence on the carriers of `Type 1` form a type
in the universe `2`. -/
example : Type 2 := CountableModelClass.{1} densitySentence.{0}

/-- The reduction to `ℕ` for the density sentence on the carriers of `Type`, under the cap-to-model
theorem for those carriers. -/
noncomputable example (hcap : CapToModel.{0}) :
    DensityClass ≃ CountableModelClass.{0} densitySentence.{0} :=
  hcap.codedClassEquiv

/-- The spectrum on all countable carriers of `Type 1` from the spectrum on `ℕ`, under the
cap-to-model theorem for the carriers of `Type 1`. -/
example (hcap : CapToModel.{1}) (hs : HasThinAlephOneSpectrum densitySentence.{0}) :
    HasThinAlephOneSpectrumOnCountableCarriers.{1} densitySentence.{0} :=
  (hasThinAlephOneSpectrumOnCountableCarriers_iff fun _ _ _ h ↦ hcap.infinite h).mpr hs

end Density

end VaughtConjecture.MainTheorem
