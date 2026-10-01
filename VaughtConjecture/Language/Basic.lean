/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Basic
import VaughtConjecture.Stage.Legal

/-!
# The language of legal stage types at the base stage

Roadmap, Layer 2 (the base-stage relational language, with one relation symbol for each legal
stage type, and no function symbols; symbol countability); semantic contract, item 1 (the language
is relational, with one relation for each base-stage finite type).

The **base language** (`baseLanguage`) is the relational language with one `n`-ary relation
symbol `P_p` for each legal stage type `p` at stage `ω` on `n` points, and no function symbols.
Its `n`-ary relation symbols are the legal stage types themselves (`baseLanguage.Relations n` is
the subtype `{p : StageType ω n // p.IsLegal}`); `baseLanguage.type p` is the stage type of the
symbol `p`, and `baseLanguage.symbol` makes a symbol of a legal stage type.  Two structures of the
base language are equal when the same relations hold of the same tuples
(`baseLanguage.structure_ext`, the case of `Structure.ext_of_isRelational`, which holds for every
relational language).

The language is countable: there are countably many stage types at stage `ω` on `n` points
(`StageType.countable_of_lt_omega_one`, as `ω < ω₁`), hence countably many relation symbols of
each arity, and countably many of all arities together.

**Universe level.**  The language is `Language.{0, u + 1}`: its relation symbols are stage types,
whose labels are ordinals of `Ordinal.{u}`.  The coded structure spaces of the infinitary-logic
library apply to it through the `SmallVocabulary` transport.  At `u = 0` it is `Language.{0, 1}`,
which the roadmap's `HasThinAlephOneSpectrum`,
`SmallVocabulary.isThinOnNatModels_of_countable_sentence_splits`, and
`exists_sentence_of_countable_of_presentation` accept; the unprefixed
`Sentenceω.isThinOnNatModels_of_countable_sentence_splits` would need a language in
`Language.{0, 0}`.

## References

This is the language `L` of [Kni26, Definition 3.3.1], whose countability is
[Kni26, Proposition 3.1.4] at `ω`, for R. W. Knight, *A counterexample to Vaught's Conjecture
using generalised Stone spaces* (draft, 20 February 2026).
-/

universe u

/-- **Extensionality** for structures of a relational language: with no function symbols, two
structures on the same carrier are equal when the same relations hold of the same tuples. -/
theorem FirstOrder.Language.Structure.ext_of_isRelational {L : FirstOrder.Language}
    [L.IsRelational] {M : Type*} {s t : L.Structure M}
    (h : ∀ ⦃n : ℕ⦄ (r : L.Relations n) (xs : Fin n → M),
      @Structure.RelMap L M s n r xs ↔ @Structure.RelMap L M t n r xs) : s = t :=
  Structure.ext (funext fun _ ↦ funext fun f ↦ isEmptyElim f)
    (funext fun _ ↦ funext fun r ↦ funext fun xs ↦ propext (h r xs))

namespace VaughtConjecture

open FirstOrder Language Ordinal

/-- The **base language** [Kni26, Definition 3.3.1]: the relational language with one `n`-ary
relation symbol for each legal stage type at stage `ω` on `n` points, and no function symbols. -/
def baseLanguage : Language.{0, u + 1} where
  Functions _ := Empty
  Relations n := {p : StageType.{u} ω n // p.IsLegal}

namespace baseLanguage

variable {n : ℕ}

/-- The stage type of a relation symbol. -/
def type (p : baseLanguage.{u}.Relations n) : StageType.{u} ω n :=
  Subtype.val (p : {p : StageType.{u} ω n // p.IsLegal})

/-- The stage type of a relation symbol is legal. -/
theorem isLegal_type (p : baseLanguage.{u}.Relations n) : (type p).IsLegal :=
  Subtype.property (p : {p : StageType.{u} ω n // p.IsLegal})

/-- The relation symbol of a legal stage type. -/
def symbol (p : StageType.{u} ω n) (hp : p.IsLegal) : baseLanguage.{u}.Relations n :=
  (⟨p, hp⟩ : {p : StageType.{u} ω n // p.IsLegal})

/-- The stage type of the symbol of `p` is `p`. -/
@[simp] theorem type_symbol (p : StageType.{u} ω n) (hp : p.IsLegal) : type (symbol p hp) = p :=
  rfl

/-- The symbol of the stage type of a relation symbol is the relation symbol. -/
@[simp] theorem symbol_type (p : baseLanguage.{u}.Relations n) :
    symbol (type p) (isLegal_type p) = p :=
  rfl

/-- A relation symbol is determined by its stage type. -/
theorem type_injective : Function.Injective (type : baseLanguage.{u}.Relations n → _) :=
  Subtype.val_injective

/-- Two relation symbols are equal exactly when their stage types are. -/
@[simp] theorem type_inj {p q : baseLanguage.{u}.Relations n} : type p = type q ↔ p = q :=
  type_injective.eq_iff

/-- The base language is relational. -/
instance isRelational : IsRelational baseLanguage.{u} :=
  fun _ ↦ inferInstanceAs (IsEmpty Empty)

/-- **Extensionality** for structures of the base language: with no function symbols, two
structures are equal when the same relations hold of the same tuples. -/
theorem structure_ext {M : Type*} {s t : baseLanguage.{u}.Structure M}
    (h : ∀ ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M),
      @Structure.RelMap _ M s n p xs ↔ @Structure.RelMap _ M t n p xs) : s = t :=
  Structure.ext_of_isRelational h

/-- **Countably many relation symbols of each arity** [Kni26, Proposition 3.1.4]: there are
countably many legal stage types at stage `ω` on `n` points. -/
instance countable_relations (n : ℕ) : Countable (baseLanguage.{u}.Relations n) :=
  have := StageType.countable_of_lt_omega_one (α := (ω : Ordinal.{u})) omega0_lt_omega_one n
  Subtype.countable

/-- **The base language is countable**: countably many relation symbols of all arities
together. -/
instance countable_sigma_relations : Countable (Σ n, baseLanguage.{u}.Relations n) :=
  inferInstance

end baseLanguage

end VaughtConjecture
