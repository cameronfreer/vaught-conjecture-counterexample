/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.TemplateSystem.RepresentativeDictionary

/-!
# The chosen symbols `Q_t` and the class symbols `Q_c`

Numbering as in the current draft of [AFK26].  The printed language `L_b[L]` of
[AFK26, Definition 4.15] has one symbol `Q_t` for each template `t` of the template system `L`,
of arity `n` when `t` is on `[n]`.  Here `L` is the system of chosen legal templates
`chosenLegalTemplates` ([AFK26, proof of Proposition 4.30]): the chosen representatives
`r(d) = chosenTemplateRepresentative d` of the legal classes `d` on `[n]`, `n > 0`.  The library's
`templateLanguage` names the same symbols by the classes, `TemplateSymbol.invariant d`.  Only the
symbols `Q_t` are treated: the symbols `P_k` and `R_t` and the translation of sentences are later
work.

**The two families of `Q`-symbols.**

* `ChosenSymbol n` — the chosen symbols of arity `n`: the chosen legal templates on `[n]`.
  `chosenLanguage` is the relational language with these symbols, the printed `L_b[L]`.
* `InvariantSymbol n` — the class symbols of arity `n`: the symbols `Q_d` of `templateLanguage`
  (`TemplateSymbol.IsInvariant`).
* `ChosenSymbol.toTemplateSymbol` sends `r(d)` to `Q_d` (by the class of the template), and
  `chosenSymbolOf d hn` is the chosen section, `Q_d ↦ r(d)`; `chosenSymbolMap` is the symbol map
  as a map of languages `chosenLanguage →ᴸ templateLanguage`.

**Arity zero.**  Both families are empty at arity `0`: chosen legal templates have positive arity
(`chosenLegalTemplates`), and every symbol of `templateLanguage` has positive arity
(`TemplateSymbol.pos`).  This is `ArityZeroTarget`, proved; the equivalence of
`ChosenSymbolEquivTarget` is stated at every arity, including `0`.

**Structures.**  A structure `G` of `templateLanguage` on `M` gives a structure of
`chosenLanguage` on the same carrier by transport along the symbol map, the reduct
`chosenReduct G` (`LHom.reduct` of `chosenSymbolMap`): `Q_{r(d)}` is read as `Q_d`.  So
corresponding symbols read the same on every tuple of `M` by definition of the reduct
(`SameReadingTarget`, proved).  Every structure of `chosenLanguage` is such a reduct
(`ChosenReductSurjectiveTarget`, stated); the reduct forgets `P_k` and `R_t`.

**Charts.**  The all-template reading `StageType.PrintedHolds` of
`VaughtConjecture.Correspondence.TemplateSystem.RepresentativeDictionary` is kept for literal
faces, whose templates need not be chosen.  On chosen templates it is the chosen-symbol reading:

* `ChosenChartReductTarget` — the reduct of the chart `StageType.TemplateChart` of `T` reads each
  chosen `Q_t` as `T.PrintedHolds t`.  **Proved**, by `printedClassReadingTarget`.
* `RealizesChosenChart H x T` — `x` realizes, in a structure `H` of `chosenLanguage`, the printed
  chart of `T` on the chosen symbols; `RealizesPrintedChartRestrictTarget` — a realization of the
  all-template printed chart (`RealizesPrintedChart`) restricts to one of the chosen chart.
  **Proved.**
* `RealizesChosenChartReductTarget` — `x` realizes the chosen chart of `T` in `chosenReduct G`
  exactly when every class symbol `Q_d` holds of `x ∘ xs` in `G` exactly when it holds of `xs` in
  the chart `StageType.Holds` of `T`.  **Stated.**

**Status.**  Proved: `ArityZeroTarget`, `SameReadingTarget`, `ChosenChartReductTarget`,
`RealizesPrintedChartRestrictTarget`.  Stated: `ChosenSymbolEquivTarget`,
`ChosenReductSurjectiveTarget`, `RealizesChosenChartReductTarget`.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal StageType

noncomputable section

/-! ### The two families of `Q`-symbols -/

/-- **The chosen symbols `Q_t` of arity `n`** ([AFK26, Definition 4.15], `L_b[L]` for the system
`L` of [AFK26, proof of Proposition 4.30]): the chosen legal templates on `[n]`.
Correspondence with the printed definitions. -/
abbrev ChosenSymbol (n : ℕ) : Type (u + 1) :=
  {t : StageType.{u} ω₁ n // t ∈ chosenLegalTemplates.{u} n}

/-- **The class symbols `Q_d` of arity `n`**: the symbols `TemplateSymbol.invariant` of
`templateLanguage`.  Correspondence with the printed definitions. -/
abbrev InvariantSymbol (n : ℕ) : Type (u + 1) :=
  {r : TemplateSymbol.{u} n // r.IsInvariant}

/-- **The language `L_b[L]` with the chosen symbols** [AFK26, Definition 4.15]: relational, one
symbol `Q_t` of arity `n` for each chosen legal template `t` on `[n]`.
Correspondence with the printed definitions. -/
def chosenLanguage : Language.{0, u + 1} where
  Functions _ := Empty
  Relations := ChosenSymbol.{u}

instance : chosenLanguage.{u}.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

namespace ChosenSymbol

variable {n : ℕ}

/-- A chosen symbol has positive arity. -/
theorem pos (t : ChosenSymbol.{u} n) : 0 < n :=
  t.2.1

/-- The class of a chosen symbol is legal. -/
theorem isStronglyCodedLegal_toClass (t : ChosenSymbol.{u} n) :
    t.1.toClass.IsStronglyCodedLegal := by
  obtain ⟨-, c, hc⟩ := t.2
  rw [← hc, toClass_chosenTemplateRepresentative]
  exact c.2

/-- **The legal class of a chosen symbol**: the class of its template. -/
def toLegalClass (t : ChosenSymbol.{u} n) : LegalClass.{u} n :=
  ⟨t.1.toClass, t.isStronglyCodedLegal_toClass⟩

/-- **The class symbol of a chosen symbol**: `Q_{r(d)} ↦ Q_d`. -/
def toTemplateSymbol (t : ChosenSymbol.{u} n) : TemplateSymbol.{u} n :=
  TemplateSymbol.invariant t.toLegalClass t.pos

/-- The class symbol of a chosen symbol is a symbol `Q_d`. -/
theorem isInvariant_toTemplateSymbol (t : ChosenSymbol.{u} n) : t.toTemplateSymbol.IsInvariant :=
  trivial

end ChosenSymbol

/-- **The chosen section** `Q_d ↦ Q_{r(d)}`: the chosen representative of a legal class on `[n]`,
`n > 0`, as a chosen symbol. -/
def chosenSymbolOf {n : ℕ} (c : LegalClass.{u} n) (hn : 0 < n) : ChosenSymbol.{u} n :=
  ⟨chosenTemplateRepresentative c.1, hn, c, rfl⟩

/-- The class symbol of the chosen symbol of `d` is `Q_d`. -/
@[simp] theorem toTemplateSymbol_chosenSymbolOf {n : ℕ} (c : LegalClass.{u} n) (hn : 0 < n) :
    (chosenSymbolOf c hn).toTemplateSymbol = TemplateSymbol.invariant c hn := by
  have hc : (chosenSymbolOf c hn).toLegalClass = c :=
    Subtype.ext (toClass_chosenTemplateRepresentative c.1)
  rw [ChosenSymbol.toTemplateSymbol, hc]

/-- **The symbol map `L_b[L] → templateLanguage`**: `Q_{r(d)} ↦ Q_d`.
Correspondence with the printed definitions. -/
def chosenSymbolMap : chosenLanguage.{u} →ᴸ templateLanguage.{u} where
  onFunction _ f := Empty.elim f
  onRelation _ t := ChosenSymbol.toTemplateSymbol t

/-! ### The equivalence of symbols, and arity zero -/

/-- **Target: the chosen symbols are the class symbols, arity by arity.**  At every arity `n`
there is an equivalence between the chosen symbols and the class symbols that sends `Q_{r(d)}` to
`Q_d` and whose inverse is the chosen section `Q_d ↦ Q_{r(d)}`.  At `n = 0` both sides are empty
(`ArityZeroTarget`).  Stated.  Correspondence with the printed definitions. -/
def ChosenSymbolEquivTarget : Prop :=
  ∀ n : ℕ, ∃ e : ChosenSymbol.{u} n ≃ InvariantSymbol.{u} n,
    (∀ t : ChosenSymbol.{u} n, (e t).1 = t.toTemplateSymbol) ∧
      ∀ (c : LegalClass.{u} n) (hn : 0 < n),
        e.symm ⟨TemplateSymbol.invariant c hn, trivial⟩ = chosenSymbolOf c hn

/-- **Target: at arity zero both families of `Q`-symbols are empty.**
Correspondence with the printed definitions. -/
def ArityZeroTarget : Prop :=
  IsEmpty (ChosenSymbol.{u} 0) ∧ IsEmpty (InvariantSymbol.{u} 0)

/-- **At arity zero both families of `Q`-symbols are empty, proved**: chosen legal templates and
symbols of `templateLanguage` have positive arity. -/
theorem arityZeroTarget : ArityZeroTarget.{u} :=
  ⟨⟨fun t ↦ (lt_irrefl 0) t.pos⟩, ⟨fun r ↦ (lt_irrefl 0) r.1.pos⟩⟩

/-! ### Structures: the reduct along the symbol map -/

section Structures

variable {M : Type v}

/-- **The chosen-symbol structure of a structure of `templateLanguage`**: the reduct along
`chosenSymbolMap`, on the same carrier; `Q_{r(d)}` is read as `Q_d`.
Correspondence with the printed definitions. -/
@[instance_reducible] def chosenReduct (G : templateLanguage.{u}.Structure M) :
    chosenLanguage.{u}.Structure M :=
  @LHom.reduct _ _ chosenSymbolMap M G

/-- The reduct reads each chosen symbol as its class symbol. -/
@[simp] theorem relMap_chosenReduct (G : templateLanguage.{u}.Structure M) {n : ℕ}
    (t : ChosenSymbol.{u} n) (x : Fin n → M) :
    RelMap (L := chosenLanguage.{u}) (self := chosenReduct G) t x ↔
      RelMap (L := templateLanguage.{u}) (self := G) t.toTemplateSymbol x :=
  Iff.rfl

end Structures

/-- **Target: corresponding symbols read the same on the same tuple.**  For a structure `G` of
`templateLanguage` on `M`, read in the chosen vocabulary through `chosenReduct G`, the chosen symbol
`Q_{r(d)}` and the class symbol `Q_d` hold of the same tuples `x : Fin n → M`.
Correspondence with the printed definitions. -/
def SameReadingTarget : Prop :=
  ∀ (M : Type v) (G : templateLanguage.{u}.Structure M) ⦃n : ℕ⦄ (c : LegalClass.{u} n)
    (hn : 0 < n) (x : Fin n → M),
      RelMap (L := chosenLanguage.{u}) (self := chosenReduct G) (chosenSymbolOf c hn) x ↔
        RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hn) x

/-- **Corresponding symbols read the same on the same tuple, proved**: by the definition of the
reduct and `toTemplateSymbol_chosenSymbolOf`. -/
theorem sameReadingTarget : SameReadingTarget.{u, v} := by
  intro M G n c hn x
  rw [relMap_chosenReduct, toTemplateSymbol_chosenSymbolOf]

/-- **Target: every chosen-symbol structure is a reduct.**  Every structure of `chosenLanguage`
on `M` is `chosenReduct G` for some structure `G` of `templateLanguage` on `M`.  Stated.
Correspondence with the printed definitions. -/
def ChosenReductSurjectiveTarget : Prop :=
  ∀ (M : Type v) (H : chosenLanguage.{u}.Structure M),
    ∃ G : templateLanguage.{u}.Structure M, chosenReduct G = H

/-! ### Charts on the chosen symbols -/

/-- **A tuple realizes the printed chart of `T` on the chosen symbols**: this reads only the
symbols `Q_t` of [AFK26, Definition 4.18] with `t` chosen.  In a structure `H` of
`chosenLanguage`, every chosen `Q_t` holds of `x ∘ xs` exactly when `T.PrintedHolds t xs`.
Correspondence with the printed definitions. -/
def RealizesChosenChart {M : Type v} {n : ℕ} (H : chosenLanguage.{u}.Structure M)
    (x : Fin n → M) (T : StageType.{u} ω₁ n) : Prop :=
  ∀ ⦃k : ℕ⦄ (t : ChosenSymbol.{u} k) (xs : Fin k → Fin n),
    RelMap (L := chosenLanguage.{u}) (self := H) t (x ∘ xs) ↔ T.PrintedHolds t.1 xs

/-- **The restriction of an all-template structure to the chosen symbols**: `Q_t` for chosen `t`
is read as `Q t`. -/
@[instance_reducible] def chosenRestriction {M : Type v}
    (Q : ∀ ⦃k : ℕ⦄, StageType.{u} ω₁ k → (Fin k → M) → Prop) :
    chosenLanguage.{u}.Structure M where
  funMap f := Empty.elim f
  RelMap t xs := Q t.1 xs

/-- **Target: the chosen chart of a template is the reduct of its class chart.**  At stage `ω₁`,
the reduct of the chart `StageType.TemplateChart` of `T` reads each chosen `Q_t` of `xs` as
`T.PrintedHolds t xs`.  Correspondence with the printed definitions. -/
def ChosenChartReductTarget : Prop :=
  ∀ ⦃n : ℕ⦄ (T : StageType.{u} ω₁ n) ⦃k : ℕ⦄ (t : ChosenSymbol.{u} k) (xs : Fin k → Fin n),
    RelMap (L := chosenLanguage.{u}) (self := chosenReduct inferInstance)
        (M := T.TemplateChart) t xs ↔ T.PrintedHolds t.1 xs

/-- **The chosen chart of a template is the reduct of its class chart, proved**: by
`printedClassReadingTarget`. -/
theorem chosenChartReductTarget : ChosenChartReductTarget.{u} := by
  intro n T k t xs
  exact (printedClassReadingTarget T t.1 t.isStronglyCodedLegal_toClass t.pos xs).symm

/-- **Target: a realization of the all-template printed chart restricts to the chosen symbols.**
Correspondence with the printed definitions. -/
def RealizesPrintedChartRestrictTarget : Prop :=
  ∀ {M : Type v} ⦃n : ℕ⦄ (Q : ∀ ⦃k : ℕ⦄, StageType.{u} ω₁ k → (Fin k → M) → Prop)
    (x : Fin n → M) (T : StageType.{u} ω₁ n),
      RealizesPrintedChart Q x T → RealizesChosenChart (chosenRestriction Q) x T

/-- **A realization of the all-template printed chart restricts to the chosen symbols, proved.** -/
theorem realizesPrintedChartRestrictTarget : RealizesPrintedChartRestrictTarget.{u, v} :=
  by
  intro M n Q x T hx k t xs
  exact hx t.1 xs

/-- **Target: the chosen chart in a reduct is the class chart on the symbols `Q_d`.**  For a
structure `G` of `templateLanguage` on `M`, a tuple `x : Fin n → M` and `T` at stage `ω₁`, `x`
realizes the printed chart of `T` on the chosen symbols in `chosenReduct G` exactly when, for
every legal class `d` on `[k]`, `k > 0`, and every `xs : Fin k → Fin n`, `Q_d` holds of `x ∘ xs`
in `G` exactly when it holds of `xs` in the chart `StageType.Holds` of `T`.  Stated.
Correspondence with the printed definitions. -/
def RealizesChosenChartReductTarget : Prop :=
  ∀ (M : Type v) (G : templateLanguage.{u}.Structure M) ⦃n : ℕ⦄ (x : Fin n → M)
    (T : StageType.{u} ω₁ n),
      RealizesChosenChart (chosenReduct G) x T ↔
        ∀ ⦃k : ℕ⦄ (c : LegalClass.{u} k) (hk : 0 < k) (xs : Fin k → Fin n),
          RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hk)
              (x ∘ xs) ↔ T.Holds (TemplateSymbol.invariant c hk) xs

end

end VaughtConjecture
