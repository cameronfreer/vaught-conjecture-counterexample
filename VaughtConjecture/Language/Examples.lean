/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import VaughtConjecture.Language.Density

/-!
# A structure failing covering, and relations on repeated points

Roadmap, Layer 2 (the structural clauses of the sentence: injective tuples, unique labels, exact
face coherence, covering, and nonemptiness; no finite models); semantic contract, item 5.

**Covering is not automatic.**  On the one-point carrier, the structure in which no relation holds
(`pointStructure`) is a type assignment on a nonempty carrier whose realization, with no typed
tuple, is exactly consistent (`pointStructure_laws`).  It fails covering: the empty tuple is an
initial segment of no typed tuple (`not_isStructural_pointStructure`).  So neither the four-family
sentence nor the density sentence holds in it (`not_realize_fourFamilySentence_pointStructure`,
`not_realize_densitySentence_pointStructure`).  That the sentences are satisfiable at all is model
existence, which is not proved here.

**Relations on repeated points.**  The arity-preservation clause fails in any structure in which a
relation holds of a tuple with a repeated point (`not_realize_arityClause_of_relMap`), so then
neither sentence holds (`not_realize_fourFamilySentence_of_relMap`,
`not_realize_densitySentence_of_relMap`).

**No finite models.**  No structure on `Fin 3` satisfies the four-family sentence
(`not_realize_fourFamilySentence_fin_three`).

## References

The sentence is [Kni26, Definition 3.3.3], for R. W. Knight, *A counterexample to Vaught's
Conjecture using generalised Stone spaces* (draft, 20 February 2026).
-/

namespace VaughtConjecture.baseLanguage

open FirstOrder Language Structure

/-! ### The one-point structure with no relations -/

/-- The structure on the one-point carrier in which no relation holds. -/
@[instance_reducible] private def pointStructure : baseLanguage.{0}.Structure Unit where
  RelMap _ _ := False

/-- The one-point structure with no relations is a type assignment on a nonempty carrier, and its
realization is exactly consistent. -/
private theorem pointStructure_laws :
    @IsTypeAssignment Unit pointStructure ∧ Nonempty Unit ∧
      (@toRealization Unit pointStructure).IsConsistent := by
  let := pointStructure
  refine ⟨⟨fun _ _ _ h ↦ h.elim, fun _ _ _ _ h ↦ h.elim⟩, inferInstance, ?_⟩
  intro _ _ t p _ hp
  obtain ⟨_, _, h⟩ := exists_relMap_of_toRealization_eval hp
  exact h.elim

/-- **Covering fails** in the one-point structure with no relations: the empty tuple is an initial
segment of no typed tuple. -/
private theorem not_isStructural_pointStructure : ¬ @IsStructural Unit pointStructure :=
  fun h ↦ by
    let := pointStructure
    obtain ⟨_, _, _, hp⟩ := h.covering (Fin.elim0 : Fin 0 → Unit) fun i ↦ i.elim0
    exact hp

/-- The one-point structure with no relations does not satisfy the four-family sentence. -/
private theorem not_realize_fourFamilySentence_pointStructure :
    ¬ @Sentenceω.Realize _ fourFamilySentence Unit pointStructure := fun h ↦ by
  let := pointStructure
  exact not_isStructural_pointStructure
    ((realize_fourFamilySentence_iff_isFourFamilyModel Unit).mp h).toIsStructural

/-- The one-point structure with no relations does not satisfy the density sentence. -/
private theorem not_realize_densitySentence_pointStructure :
    ¬ @Sentenceω.Realize _ densitySentence Unit pointStructure := fun h ↦ by
  let := pointStructure
  obtain ⟨hT, hne, hcons, hcov, -⟩ := (realize_densitySentence_iff Unit).mp h
  exact not_isStructural_pointStructure (isStructural_iff.mpr ⟨hT, hne, hcons, hcov⟩)

/-! ### Relations on repeated points -/

section Repeated

variable {M : Type} [baseLanguage.{0}.Structure M] (p : baseLanguage.{0}.Relations 2) (x : M)

/-- **Arity preservation excludes repeated points**: if a relation holds of a pair with a repeated
point, the arity-preservation clause fails. -/
private theorem not_realize_arityClause_of_relMap (h : RelMap p ![x, x]) :
    ¬ arityClause.Realize M := fun hM ↦
  absurd ((realize_arityClause M).mp hM p _ h (show ![x, x] 0 = ![x, x] 1 from rfl)) (by decide)

/-- If a relation holds of a pair with a repeated point, the four-family sentence fails. -/
private theorem not_realize_fourFamilySentence_of_relMap (h : RelMap p ![x, x]) :
    ¬ fourFamilySentence.Realize M := fun hM ↦
  absurd ((isTypeAssignment_of_realize_fourFamilySentence hM).injective p _ h
    (show ![x, x] 0 = ![x, x] 1 from rfl)) (by decide)

/-- If a relation holds of a pair with a repeated point, the density sentence fails. -/
private theorem not_realize_densitySentence_of_relMap (h : RelMap p ![x, x]) :
    ¬ densitySentence.Realize M := fun hM ↦
  absurd (((realize_densitySentence_iff M).mp hM).1.injective p _ h
    (show ![x, x] 0 = ![x, x] 1 from rfl)) (by decide)

end Repeated

/-! ### No finite models -/

/-- No structure on `Fin 3` satisfies the four-family sentence. -/
private theorem not_realize_fourFamilySentence_fin_three [baseLanguage.{0}.Structure (Fin 3)] :
    ¬ fourFamilySentence.Realize (Fin 3) :=
  not_realize_fourFamilySentence_of_finite

end VaughtConjecture.baseLanguage
