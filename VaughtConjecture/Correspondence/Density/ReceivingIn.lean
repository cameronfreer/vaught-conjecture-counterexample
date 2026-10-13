/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Density.ClassRealization
import VaughtConjecture.Realization.ReceivingInClass

/-!
# Receiving restricted to strongly coded donors gives donor density of the class reading

The receiving of `VaughtConjecture.Realization.ReceivingInClass`, restricted to the stage types
with strongly coded rows (`Realization.HasFiniteExtensionReceivingIn`), gives donor density
(`ClassRealization.HasDonorDensity`) of the class reading
(`Realization.HasFiniteExtensionReceivingIn.hasDonorDensity_classReading`, native construction):
a class donor has a representative with the type of the root as its face
(`TemplateClass.exists_renaming_restrictFace_eq`), that representative is a legal strongly coded
donor, and a positional witness is a witness up to renaming.

This reads a given positional realization and needs no presentation.  The converse, a positional
realization with this receiving whose class reading is a given class realization with donor
density, is the presentation target B.T7
(`VaughtConjecture.Correspondence.Density.ClassRealization`).
-/

universe u v

namespace VaughtConjecture

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-- **Receiving restricted to strongly coded donors gives donor density of the class reading.**
Native construction. -/
theorem HasFiniteExtensionReceivingIn.hasDonorDensity_classReading
    (h : R.HasFiniteExtensionReceivingIn fun t ↦ t.rows.IsStronglyCoded) :
    R.classReading.HasDonorDensity := by
  intro n m t p hp D g hD hDg x hx
  obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hp
  induction D using Quotient.inductionOn with
  | h D' =>
    obtain ⟨D'', hD'', hface⟩ := TemplateClass.exists_renaming_restrictFace_eq D' g hDg
    change D'.toClass.IsStronglyCodedLegal at hD
    rw [← hD''] at hD
    obtain ⟨u, hu, q, hq, he⟩ := h t p' hp' D'' g hD.1 hD.2 hface x hx
    refine ⟨u, hu, q.toClass, by rw [classReading_eval, he, Option.map_some], ?_⟩
    change q.toClass.ObservesAt x D'.toClass
    rw [← hD'']
    exact ⟨q, D'', rfl, rfl, hq⟩

end Realization

end VaughtConjecture
