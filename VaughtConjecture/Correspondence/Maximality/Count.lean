/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Maximality.Targets
import VaughtConjecture.MainTheorem.StronglyCodedTerminalCount

/-!
# The count of maximal structures

Numbering as in the current draft of [AFK26].  Write `λ_β = blockStage β = ω + ω · β`.  `K_β[L]` is
`templateStageClass M β`, and maximality at `β` is the printed [AFK26, Definition 2.20]
(`IsMaximalAt`).  The ordinals and the language are at universe `0`, as the native terminal count
`Realization.stronglyCodedTerminalClasses_countable`; the carriers are in any universe.

**The two statements.**

* `MaximalCountTarget β` (`VaughtConjecture.Correspondence.Maximality.Targets`, unchanged): for
  `β < ω₁`, a countable set `S` of structures on `ℕ`, each maximal at `β`, such that every
  structure maximal at `β` on a countable carrier is isomorphic, in the full language
  `L_b[L] ∪ L_c[L]`, to a member of `S`.  No nonemptiness premise: maximality includes membership
  in `K_β[L]`, whose first clause is a nonempty carrier.  Proved (`maximalCountTarget`).
* `Proposition435Target β` ([AFK26, Proposition 4.35] with the manuscript's convention of
  nonempty domains): the same statement with `[Nonempty M]` on the carrier, and nothing else.  It
  follows from `MaximalCountTarget β` (`proposition435Target_of_maximalCountTarget`), so it is
  proved (`proposition435Target`).  The
  converse direction, from terminality to maximality, is not stated.

**The proof of `MaximalCountTarget β`** (`maximalCountTarget`, no premise beyond `β < ω₁`).  Let
`β < ω₁`.

1. **The represented classes.**  Among the isomorphism classes of realizations on `ℕ` terminal in
   the strongly coded receiving class at `β` (`Realization.stronglyCodedTerminalClasses β`,
   countable by `Realization.stronglyCodedTerminalClasses_countable`), the represented ones are the
   classes `[R]` for which some `H` on `ℕ` has `IsMaximalAt β H`, `R.IsStronglyCodedReceiving` and
   `R.classReading = decode β H`.  They form a countable subset.  For each represented class choose
   one such `H` (`Classical.choice` over the represented subset only), and let `S` be the set of
   the chosen structures: it is countable, and each member is maximal at `β`.  No terminal
   realization is assumed to read as a maximal structure.
2. **A maximal structure on a countable carrier.**  Let `G` on a countable `M` be maximal at `β`.
   The carrier is infinite (`infinitudeTarget`), so `M ≃ ℕ`; the transport `G'` of `G` to `ℕ` is
   maximal at `β` (`isMaximalAt_transportStructure_iff`), and `G` is isomorphic to `G'`
   (`transportEquiv`).
3. **Its presentation is terminal.**  `G'` has a realization `R` on `ℕ` in the strongly coded
   receiving class with class reading `decode β G'` (`stronglyCodedPresentationTarget`), terminal
   in the class at `β` (`maximalToTerminalTarget`).  So `[R]` is represented, by `G'` itself.
4. **The chosen representative.**  The chosen `H` for `[R]` has a presentation `R_H` with
   `[R_H] = [R]`, so `R` and `R_H` are isomorphic realizations (the relation of
   `Realization.isoSetoid`).  The equality of classes gives the isomorphism directly; the shared
   restricted terminal property of `Realization.stronglyCodedTerminalIso` is not needed here, since
   the countable set counted is a set of isomorphism classes.
5. **The full-language isomorphism.**  An isomorphism of realizations is an isomorphism of the
   class-reading structures (`Realization.Iso.classReadingEquiv`), and these structures are `G'` and
   `H` (`IsTemplateCompatible.toStructure_decode`).  Composed with the transport, `G ≃ H` in
   `L_b[L] ∪ L_c[L]`.
-/

universe v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

/-- **Target: [AFK26, Proposition 4.35]**, with the manuscript's convention of nonempty domains:
for `β < ω₁`, a countable set `S` of structures on `ℕ`, each maximal at `β`, such that every
structure maximal at `β` on a countable nonempty carrier is isomorphic, in the full language
`L_b[L] ∪ L_c[L]`, to a member of `S`.  It is `MaximalCountTarget β` with `[Nonempty M]` added on
the carrier.  Correspondence with the printed definitions. -/
def Proposition435Target (β : Ordinal.{0}) : Prop :=
  β < ω₁ → ∃ S : Set (templateLanguage.{0}.Structure ℕ), S.Countable ∧
    (∀ H ∈ S, IsMaximalAt β H) ∧
    ∀ (M : Type v) [Countable M] [Nonempty M] (G : templateLanguage.{0}.Structure M),
      IsMaximalAt β G → ∃ H ∈ S, Nonempty (@Language.Equiv templateLanguage.{0} M ℕ G H)

/-- **[AFK26, Proposition 4.35] from the count of maximal structures**: the premise `[Nonempty M]`
is not used.  Correspondence with the printed definitions. -/
theorem proposition435Target_of_maximalCountTarget {β : Ordinal.{0}}
    (h : MaximalCountTarget.{v} β) : Proposition435Target.{v} β := fun hβ ↦
  let ⟨S, hS, hmax, hrep⟩ := h hβ
  ⟨S, hS, hmax, fun M _ _ G hG ↦ hrep M G hG⟩

/-! ### The represented terminal classes -/

/-- **The represented strongly coded terminal classes at `β`**: the isomorphism classes `[R]` of
realizations on `ℕ` terminal in the strongly coded receiving class at `β`
(`Realization.stronglyCodedTerminalClasses β`) with a member `R` that presents a structure `H` on
`ℕ` maximal at `β`: `R` is in the strongly coded receiving class and `R.classReading = decode β H`.
Native construction. -/
def representedTerminalClasses (β : Ordinal.{0}) :
    Set (Quotient (Realization.isoSetoid (blockStage β) ℕ)) :=
  {q | q ∈ Realization.stronglyCodedTerminalClasses β ∧
    ∃ (H : templateLanguage.{0}.Structure ℕ) (R : Realization.{0, 0} (blockStage β) ℕ),
      Quotient.mk _ R = q ∧ IsMaximalAt β H ∧ R.IsStronglyCodedReceiving ∧
        R.classReading = decode β H}

/-- **Countably many represented classes**, for `β < ω₁`: a subset of the countable set of strongly
coded terminal classes (`Realization.stronglyCodedTerminalClasses_countable`).
Native construction. -/
theorem representedTerminalClasses_countable {β : Ordinal.{0}} (hβ : β < ω₁) :
    (representedTerminalClasses β).Countable :=
  (Realization.stronglyCodedTerminalClasses_countable hβ).mono fun _ hq ↦ hq.1

/-- **The chosen maximal structure of a represented class**: a structure on `ℕ` maximal at `β`
presented by a member of the class, chosen (`Classical.choose`) over the represented classes
only.  Native construction. -/
@[instance_reducible] noncomputable def representedStructure {β : Ordinal.{0}}
    (q : representedTerminalClasses β) : templateLanguage.{0}.Structure ℕ :=
  Classical.choose q.2.2

/-- The chosen structure of a represented class is maximal at `β`, and presented by a member of
the class.  Native construction. -/
theorem representedStructure_spec {β : Ordinal.{0}} (q : representedTerminalClasses β) :
    ∃ R : Realization.{0, 0} (blockStage β) ℕ, Quotient.mk _ R = q.1 ∧
      IsMaximalAt β (representedStructure q) ∧ R.IsStronglyCodedReceiving ∧
        R.classReading = decode β (representedStructure q) :=
  Classical.choose_spec q.2.2

/-- Isomorphisms of structures compose, and are carried along equalities of the structures.
Native construction. -/
theorem nonempty_equiv_of_equiv_of_eq {L : Language} {M N P : Type*} {A : L.Structure M}
    {B : L.Structure N} {C C' : L.Structure P} (f : @Language.Equiv L M N A B)
    (g : @Language.Equiv L N P B C) (hC : C = C') : Nonempty (@Language.Equiv L M P A C') := by
  subst hC
  exact ⟨g.comp f⟩

/-- **The count of maximal structures holds** (`MaximalCountTarget β` for every `β`; native
construction, correspondence with the printed definitions).  `S` is the set of the chosen
structures of the represented classes (`representedStructure`), countable
(`representedTerminalClasses_countable`) and maximal at `β`.  A structure `G` maximal at `β` on a
countable carrier `M`: `M` is infinite (`infinitudeTarget`), so `M ≃ ℕ`; the transport `G'` of `G`
is maximal (`IsMaximalAt.transportStructure`); its strongly coded presentation `R`
(`stronglyCodedPresentationTarget`) is terminal (`maximalToTerminalTarget`), so `[R]` is
represented, by `G'`.  The chosen `H` of `[R]` is presented by `R_H` with `[R_H] = [R]`, so
`R` and `R_H` are isomorphic realizations (`Quotient.exact`, `Realization.isoSetoid_r`), and
`Realization.Iso.classReadingEquiv` is an isomorphism of their class-reading structures, which are
`G'` and `H` (`IsTemplateCompatible.toStructure_decode`).  Composed with `transportEquiv`. -/
theorem maximalCountTarget (β : Ordinal.{0}) : MaximalCountTarget.{v} β := by
  intro hβ
  have hc := (representedTerminalClasses_countable hβ).to_subtype
  refine ⟨Set.range (representedStructure (β := β)), Set.countable_range _, ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩
    obtain ⟨-, -, hH, -⟩ := representedStructure_spec q
    exact hH
  · intro M _ G hG
    have : Infinite M := infinitudeTarget β M hβ G hG.1
    obtain ⟨hD⟩ := nonempty_denumerable M
    set e : M ≃ ℕ := @Denumerable.eqv M hD
    have hG' := hG.transportStructure e
    obtain ⟨R, hR, hRG⟩ :=
      stronglyCodedPresentationTarget β ℕ hβ inferInstance _ hG'.1
    have hRt := maximalToTerminalTarget β ℕ hβ _ hG' R hR hRG
    let q : representedTerminalClasses β :=
      ⟨Quotient.mk _ R, ⟨R, rfl, hRt⟩, _, R, rfl, hG', hR, hRG⟩
    obtain ⟨RH, hRHq, hHmax, -, hRHH⟩ := representedStructure_spec q
    have hiso : R.IsIso RH := Realization.isoSetoid_r.mp (Quotient.exact hRHq.symm)
    obtain ⟨i⟩ := hiso
    have hG'eq : R.classReading.toStructure = transportStructure e G := by
      rw [hRG, hG'.1.2.1.toStructure_decode hG'.1.2.2.1]
    have hHeq : RH.classReading.toStructure = representedStructure q := by
      rw [hRHH, hHmax.1.2.1.toStructure_decode hHmax.1.2.2.1]
    refine ⟨representedStructure q, ⟨q, rfl⟩, ?_⟩
    refine nonempty_equiv_of_equiv_of_eq (transportEquiv e G) ?_ hHeq
    exact hG'eq ▸ i.classReadingEquiv

/-- **[AFK26, Proposition 4.35] holds** (`Proposition435Target β` for every `β`), from
`maximalCountTarget`.  Correspondence with the printed definitions. -/
theorem proposition435Target (β : Ordinal.{0}) : Proposition435Target.{v} β :=
  proposition435Target_of_maximalCountTarget (maximalCountTarget β)

end VaughtConjecture
