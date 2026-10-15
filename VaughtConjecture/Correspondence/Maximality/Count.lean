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
  in `K_β[L]`, whose first clause is a nonempty carrier.  Open.
* `Proposition435Target β` ([AFK26, Proposition 4.35] with the manuscript's convention of
  nonempty domains): the same statement with `[Nonempty M]` on the carrier, and nothing else.  It
  follows from `MaximalCountTarget β` (`proposition435Target_of_maximalCountTarget`, proved).  The
  converse direction, from terminality to maximality, is not stated.

**Plan of the proof of `MaximalCountTarget β`** (open; every input below is compiled).  Let
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

end VaughtConjecture
