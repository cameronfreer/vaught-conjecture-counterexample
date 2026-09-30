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
symbol `p`, and `baseLanguage.symbol` makes a symbol of a legal stage type.

The language is countable: there are countably many ordinals below `ω`
(`baseLanguage.countable_Iio_omega0`), hence countably many legal stage types on `n` points
(`StageType.countable_setOf_isLegal`), and countably many relation symbols of all arities
together.  These are the hypotheses under which the coded structure spaces of the infinitary-logic
library apply to the language.

## References

This is the language `L` of [Kni26, Definition 3.3.1], whose countability is
[Kni26, Proposition 3.1.4] at `ω`, for R. W. Knight, *A counterexample to Vaught's Conjecture
using generalised Stone spaces* (draft, 20 February 2026).
-/

universe u

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

/-- There are countably many ordinals below `ω`. -/
theorem countable_Iio_omega0 : (Set.Iio (ω : Ordinal.{u})).Countable :=
  Cardinal.countable_Iio_of_lt_omega_one omega0_lt_omega_one

/-- The ordinals below `ω` form a countable type. -/
instance countable_Iio_omega0_coe : Countable (Set.Iio (ω : Ordinal.{u})) :=
  countable_Iio_omega0.to_subtype

/-- **Countably many relation symbols of each arity** [Kni26, Proposition 3.1.4]: there are
countably many legal stage types at stage `ω` on `n` points. -/
instance countable_relations (n : ℕ) : Countable (baseLanguage.{u}.Relations n) :=
  (StageType.countable_setOf_isLegal countable_Iio_omega0 n).to_subtype

/-- **The base language is countable**: countably many relation symbols of all arities
together. -/
instance countable_sigma_relations : Countable (Σ n, baseLanguage.{u}.Relations n) :=
  inferInstance

end baseLanguage

end VaughtConjecture
