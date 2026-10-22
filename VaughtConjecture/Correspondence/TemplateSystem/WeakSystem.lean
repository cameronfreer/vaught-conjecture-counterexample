/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.TemplateSystem.Conditions
import VaughtConjecture.Correspondence.Density.Structure

/-!
# The weak-system interface of `K[L]`: [AFK26, Theorem 4.23]

Numbering as in the current draft of [AFK26].  `K_β[L]` is `templateStageClass M β`, `τ_β` is
`projectStructure β` on structures and `LegalClass.project β` on legal classes, `ID[L]` is
`templateDiagram` (an `InvarianceDiagram` for `templateSignature`), and `σ[L]` is
`templateSentence`.

The abstract theorem [AFK26, Theorem 2.25] is about a weak system ([AFK26, Definition 2.17]) for
an invariance diagram and a compatible invariant system ([AFK26, Definitions 2.4, 2.6, 2.8]).  This
file states what the route through that theorem needs from the invariance-diagram side, for
`K[L]`, separately from the four conditions
(`VaughtConjecture.Correspondence.TemplateSystem.Conditions`) and from the spectrum statement
(`VaughtConjecture.Correspondence.TemplateSystem.Theorem436`).

* `TemplateBaseModelsTarget` ([AFK26, Theorem 4.23], second half): on a countable **nonempty**
  carrier, the base of `K[L]` is the class of models of `σ[L]`.  Proved.
* `TemplateInvariantSystemTarget` ([AFK26, Definitions 2.6 and 2.8, Lemma 4.19]): the projections
  `τ_β` of the legal classes form an invariant system on `L_b[L]` compatible with `ID[L]`.
  Stated; not proved.  The repository has the invariant systems of the stage types
  (`Correspondence.blockSystem` for `stageSignature`), not yet one for `templateSignature`.
* `WeakSystemClausesTarget` ([AFK26, Definition 2.17] for `K[L]`, the first half of
  [AFK26, Theorem 4.23]): isomorphism closure, compatibility with `ID[L]`, rank at most `β`,
  `α`-density for `α < β` in the form of [AFK26, Definition 2.10 (c)] (`ProjectedDensityAt`), and
  closure under `τ_α`.  Stated; not proved.  The density clause is the one used by
  [AFK26, Proposition 2.18]; the class `K_β[L]` is defined by the axioms `D[δ]`, `δ < ω + ω · β`
  ([AFK26, Definitions 4.20 and 4.21]), and the passage from `D[δ]` to `α`-density is part of the
  target.

The other clauses of the weak system are proved elsewhere and are cited, not repeated: closure under
`τ_α` is `projectionTarget`, invariance under bijections of carriers is
`mem_templateStageClass_transportStructure_iff`, compatibility with `ID[L]` is
`isCompatible_templateDiagram_iff`.

**Carriers.**  Members of `K_β[L]` have nonempty carriers by definition; models of `σ[L]` need not
(`realize_templateSentence_of_isEmpty`), so `TemplateBaseModelsTarget` assumes `Nonempty M`.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

/-! ### The base and the models of the sentence -/

/-- **Target: the base is the class of models of `σ[L]`** [AFK26, Theorem 4.23, for `K[L]`]: on a
countable **nonempty** carrier, `B` is in the base exactly when `B ⊨ σ[L]`.  The premise
`Nonempty M` is the convention of [AFK26, §1]: on an empty carrier `σ[L]` holds
(`realize_templateSentence_of_isEmpty`) and the base is empty.  Proved; route:
`realize_templateSentence_iff_exists_lift`, `projectionTarget` to the level `0`,
`baseReduct_projectStructure`.  Correspondence with the printed definitions. -/
def TemplateBaseModelsTarget (M : Type v) : Prop :=
  Countable M → Nonempty M → ∀ B : baseTemplateLanguage.{u}.Structure M,
    IsInTemplateBase B ↔ @Sentenceω.Realize _ templateSentence.{u} M B

/-- **The base is the class of models of `σ[L]`** (`TemplateBaseModelsTarget M` for every `M`):
a member of `K_β[L]` projects to `K_0[L]` with the same base reduct (`projectionTarget`,
`baseReduct_projectStructure`), and the models of `σ[L]` on a nonempty carrier are the base
reducts of `K_0[L]` (`realize_templateSentence_iff_exists_lift`).  Correspondence with the
printed definitions. -/
theorem templateBaseModelsTarget (M : Type v) : TemplateBaseModelsTarget.{u} M := by
  intro hc hne B
  have := hne
  rw [realize_templateSentence_iff_exists_lift]
  constructor
  · rintro ⟨β, hβ, G, hG, rfl⟩
    exact ⟨projectStructure 0 G, projectionTarget β 0 M hc hβ zero_le G hG,
      baseReduct_projectStructure G⟩
  · rintro ⟨G, hG, rfl⟩
    exact ⟨0, (Cardinal.isSuccLimit_omega 1).pos, G, hG, rfl⟩

/-! ### The invariant system of the legal classes -/

/-- **Target: the projections of the legal classes form an invariant system compatible with
`ID[L]`** [AFK26, Definitions 2.6, 2.8 and 4.16, Lemma 4.19]: an invariant system `S` on the
invariants `L_b[L]` of `templateSignature` whose map `τ_β`, `β < ω₁`, sends `Q_c` to `Q_{τ_β(c)}`,
and which is compatible with `templateDiagram`.  Stated; not proved.  Correspondence with the
printed definitions. -/
def TemplateInvariantSystemTarget : Prop :=
  ∃ S : Correspondence.InvariantSystem.{u} templateSignature.{u},
    (∀ (β : {β : Ordinal.{u} // β < ω₁}) {n : ℕ} (c : LegalClass.{u} n) (hn : 0 < n),
      (S.τ β ⟨TemplateSymbol.invariant c hn, trivial⟩).1 =
        TemplateSymbol.invariant (c.project β.1) hn) ∧
    templateDiagram.IsCompatibleWith S

/-! ### The clauses of a weak system -/

/-- **`α`-density in the form of [AFK26, Definition 2.10 (c)]**, for the invariants of `K[L]`:
whenever `(Q_u(x̄ ȳ), Q_t(x̄)) ∈ ID[L]` and `G ⊨ Q_t(x̄)`, there are `ȳ` and an invariant `Q_s`
with `τ_α(s) = τ_α(u)` and `G ⊨ Q_s(x̄ ȳ)`.  The classes `u` and `s` are of any rank.
Correspondence with the printed definitions. -/
def ProjectedDensityAt {M : Type v} (α : Ordinal.{u}) (G : templateLanguage.{u}.Structure M) :
    Prop :=
  ∀ ⦃n m : ℕ⦄ (hn : 0 < n) (t : LegalClass.{u} n) (u : LegalClass.{u} (n + m)),
    (⟨n + m, TemplateSymbol.invariant u (Nat.lt_add_right m hn),
      Correspondence.atom (L := templateLanguage) (TemplateSymbol.invariant t hn)
        (Fin.castAdd m)⟩ : Correspondence.DiagramPair templateLanguage.{u}) ∈
        templateDiagramPairs →
    ∀ x : Fin n → M, RelMap (L := templateLanguage.{u}) (self := G)
        (TemplateSymbol.invariant t hn) x →
      ∃ (y : Fin m → M) (s : LegalClass.{u} (n + m)), s.project α = u.project α ∧
        RelMap (L := templateLanguage.{u}) (self := G)
          (TemplateSymbol.invariant s (Nat.lt_add_right m hn)) (Fin.append x y)

/-- **Target: the clauses of a weak system for `K[L]`** [AFK26, Definition 2.17 and Theorem 4.23,
first half]: on a countable carrier, for `β < ω₁` and `G ∈ K_β[L]`: every structure isomorphic to
`G` in `L_b[L] ∪ L_c[L]`, on a carrier in the same universe, is in `K_β[L]`; `G` is compatible with
`ID[L]` (`IsTemplateCompatible`, equivalently `templateDiagram.IsCompatible`); `G` has rank at most
`β` (`τ_β(G) = G`); `G` is `α`-dense (`ProjectedDensityAt α G`) for every `α < β`; and
`τ_α(G) ∈ K_α[L]` for every `α ≤ β`.  Stated; not proved.  Correspondence with the printed
definitions. -/
def WeakSystemClausesTarget (M : Type v) : Prop :=
  Countable M → ∀ β : Ordinal.{u}, β < ω₁ → ∀ G ∈ templateStageClass M β,
    (∀ (N : Type v) (H : templateLanguage.{u}.Structure N),
      Nonempty (@Language.Equiv templateLanguage.{u} M N G H) → H ∈ templateStageClass N β) ∧
    IsTemplateCompatible G ∧ projectStructure β G = G ∧
    (∀ α < β, ProjectedDensityAt α G) ∧
    ∀ α ≤ β, projectStructure α G ∈ templateStageClass M α

end VaughtConjecture
