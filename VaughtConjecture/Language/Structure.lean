/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Language.Basic
import VaughtConjecture.Realization.Model

/-!
# Structures of the base language and realizations at stage `ω`

Roadmap, Layer 2 (the realization/structure round trips, isomorphism preservation and
reflection; an abstract realization calculus is not a substitute for syntax correspondence);
semantic contract, items 1 and 4.

**From realizations to structures.**  A realization `R` at stage `ω` on `M` is read as a
structure of the base language on `M` (`Realization.toStructure`): the relation `P_p` holds of a
tuple `xs : Fin n → M` exactly when `xs` is injective and `R` evaluates it to the stage type of
`p`.  Tuples with repeated points satisfy no relation, and a tuple with an illegal type satisfies
none either: the language has symbols only for legal stage types.

**From structures to realizations.**  A structure `M` of the base language is read as a
realization at stage `ω` (`baseLanguage.toRealization`): an injective tuple is typed when some
relation holds of it, with the stage type of a chosen such relation.  The structures that arise
from realizations are the **type assignments** (`baseLanguage.IsTypeAssignment`): a relation
holds only of injective tuples, and at most one relation holds of each tuple.  These are the
arity-preservation clauses of the sentence of [Kni26, Definition 3.3.3], clause 1.

**Round trips.**  The structure of the realization of a type assignment is the type assignment
(`baseLanguage.toStructure_toRealization`), and the realization of the structure of a realization
with legal types is the realization (`baseLanguage.toRealization_toStructure`); so the type
assignments on `M` are exactly the structures of realizations on `M`
(`baseLanguage.isTypeAssignment_iff_exists_toStructure_eq`).  A realization has legal types
(`Realization.HasLegalTypes`) when every type it assigns is legal, as for a model; the realization
of a structure always has legal types (`baseLanguage.hasLegalTypes_toRealization`).

**Transport and isomorphism.**  The structure of the transport `R.map e` of a realization along a
bijection of carriers is the structure induced by `e` (`Realization.toStructure_map`).  So an
isomorphism of realizations is an isomorphism of their structures
(`Realization.Iso.toStructureEquiv`, from `Equiv.inducedStructureEquiv`), and conversely for
realizations with legal types an isomorphism of structures is an isomorphism of realizations
(`Realization.isIso_iff_nonempty_equiv`); the converse pulls tuples back along the isomorphism
(`relMap_trans_symm_toEmbedding`, stated for an arbitrary language).  On the structure side,
isomorphic type assignments have isomorphic realizations and conversely
(`baseLanguage.isIso_toRealization_iff`, from the round trips).  The structure induced on the
target of an isomorphism of structures of a relational language is the target structure
(`FirstOrder.Language.Equiv.inducedStructure_eq`).

## References

The structure of a realization is [Kni26, Definition 3.3.4], and the correspondence between
structures and realizations is the content of [Kni26, Proposition 3.3.5], for R. W. Knight,
*A counterexample to Vaught's Conjecture using generalised Stone spaces* (draft, 20 February
2026).
-/

universe u v w

open FirstOrder in
/-- **The structure induced along an isomorphism is the target structure**: for an isomorphism
`e : M ≃[L] N` of structures of a relational language, the structure induced on `N` by the
underlying bijection of `e` is the given structure of `N`. -/
theorem FirstOrder.Language.Equiv.inducedStructure_eq {L : FirstOrder.Language} [L.IsRelational]
    {M : Type v} {N : Type w} [L.Structure M] [t : L.Structure N] (e : M ≃[L] N) :
    @_root_.Equiv.inducedStructure L M N _ (e : M ≃ N) = t :=
  Structure.ext_of_isRelational fun _ r xs ↦ e.symm.map_rel r xs

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal baseLanguage

variable {M : Type v} {N : Type w} {n : ℕ}

/-- **Pulling a tuple back along an isomorphism of structures**: a relation holds of an injective
tuple of the target exactly when it holds of its pullback `t.trans e.symm.toEmbedding`. -/
theorem relMap_trans_symm_toEmbedding {L : Language} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) {k : ℕ} (r : L.Relations k) (t : Fin k ↪ N) :
    RelMap r ⇑(t.trans (e : M ≃ N).symm.toEmbedding) ↔ RelMap r ⇑t :=
  e.symm.map_rel r t

namespace Realization

variable (R : Realization.{u, v} ω M)

/-- The **structure of a realization** at stage `ω` [Kni26, Definition 3.3.4]: the relation `P_p`
holds of a tuple exactly when the tuple is injective and has the stage type of `p`. -/
@[instance_reducible] def toStructure : baseLanguage.{u}.Structure M where
  RelMap p xs := ∃ h : Function.Injective xs, R.eval ⟨xs, h⟩ = some (type p)

/-- A relation holds in the structure of a realization exactly when the tuple is injective and has
the stage type of the relation. -/
theorem relMap_toStructure (p : baseLanguage.{u}.Relations n) (xs : Fin n → M) :
    @RelMap _ M R.toStructure n p xs ↔
      ∃ h : Function.Injective xs, R.eval ⟨xs, h⟩ = some (type p) :=
  Iff.rfl

/-- On an injective tuple, a relation holds in the structure of a realization exactly when the
tuple has the stage type of the relation. -/
theorem relMap_toStructure_embedding (p : baseLanguage.{u}.Relations n) (t : Fin n ↪ M) :
    @RelMap _ M R.toStructure n p t ↔ R.eval t = some (type p) :=
  ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨t.injective, h⟩⟩

/-- **Transport of structures**: the structure of the transport of a realization along a bijection
of carriers is the structure induced by the bijection. -/
theorem toStructure_map (e : M ≃ N) :
    (R.map e).toStructure = @Equiv.inducedStructure baseLanguage.{u} M N R.toStructure e :=
  structure_ext fun _ _ xs ↦ ⟨fun ⟨h, hp⟩ ↦ ⟨e.symm.injective.comp h, hp⟩,
    fun ⟨h, hp⟩ ↦ ⟨(Function.Injective.of_comp_iff e.symm.injective xs).mp h, hp⟩⟩

variable {R} {S : Realization.{u, w} ω N}

/-- An **isomorphism of realizations** is an isomorphism of their structures: along `e`, the
structure of `R.map e` is the structure induced by `e` (`toStructure_map`), and `e` is an
isomorphism onto the induced structure (`Equiv.inducedStructureEquiv`). -/
def Iso.toStructureEquiv (i : R.Iso S) :
    @Language.Equiv baseLanguage.{u} M N R.toStructure S.toStructure :=
  letI := R.toStructure
  letI := S.toStructure
  { toEquiv := i.1
    map_fun' := fun f ↦ isEmptyElim f
    map_rel' := fun p xs ↦ by
      obtain ⟨e, rfl⟩ := i
      have h := @Language.Equiv.map_rel _ M N R.toStructure (Equiv.inducedStructure e)
        (Equiv.inducedStructureEquiv e) _ p xs
      rwa [Equiv.toFun_inducedStructureEquiv, ← toStructure_map] at h }

/-- The underlying bijection of the isomorphism of structures is that of the isomorphism of
realizations. -/
@[simp] theorem Iso.toStructureEquiv_toEquiv (i : R.Iso S) :
    @Language.Equiv.toEquiv baseLanguage.{u} M N R.toStructure S.toStructure
      i.toStructureEquiv = i.1 :=
  rfl

/-- **Isomorphisms of structures are isomorphisms of realizations**: for realizations with legal
types, a bijection of carriers that is an isomorphism of their structures carries one realization
to the other. -/
theorem map_eq_of_equiv (hR : R.HasLegalTypes) (hS : S.HasLegalTypes)
    (e : @Language.Equiv baseLanguage.{u} M N R.toStructure S.toStructure) :
    R.map (@Language.Equiv.toEquiv baseLanguage.{u} M N R.toStructure S.toStructure e) = S := by
  let := R.toStructure
  let := S.toStructure
  ext k t : 1
  rw [map_eval]
  have key (q : baseLanguage.{u}.Relations k) :
      R.eval (t.trans (e : M ≃ N).symm.toEmbedding) = some (type q) ↔ S.eval t = some (type q) := by
    rw [← relMap_toStructure_embedding, ← relMap_toStructure_embedding,
      relMap_trans_symm_toEmbedding]
  refine Option.ext fun q ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (key (symbol q (hR _ _ h))).mp h
  · exact (key (symbol q (hS _ _ h))).mpr h

/-- **Isomorphism of realizations is isomorphism of structures**, for realizations with legal
types. -/
theorem isIso_iff_nonempty_equiv (hR : R.HasLegalTypes) (hS : S.HasLegalTypes) :
    R.IsIso S ↔ Nonempty (@Language.Equiv baseLanguage.{u} M N R.toStructure S.toStructure) :=
  ⟨fun ⟨i⟩ ↦ ⟨i.toStructureEquiv⟩, fun ⟨e⟩ ↦ ⟨⟨_, map_eq_of_equiv hR hS e⟩⟩⟩

end Realization

namespace baseLanguage

section ToRealization

variable (M) [baseLanguage.{u}.Structure M]

open Classical in
/-- The **realization of a structure** of the base language: an injective tuple has the stage type
of a chosen relation holding of it, and no type if none holds. -/
noncomputable def toRealization : Realization.{u, v} ω M where
  eval {k} t :=
    if h : ∃ p : baseLanguage.{u}.Relations k, RelMap p ⇑t then some (type h.choose) else none

/-- The structure is a **type assignment**: a relation holds only of injective tuples, and at most
one relation holds of each tuple.  These are the arity-preservation clauses of
[Kni26, Definition 3.3.3], clause 1. -/
structure IsTypeAssignment : Prop where
  /-- A relation holds only of injective tuples. -/
  injective ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M) :
    RelMap p xs → Function.Injective xs
  /-- At most one relation holds of each tuple. -/
  unique ⦃n : ℕ⦄ (p q : baseLanguage.{u}.Relations n) (xs : Fin n → M) :
    RelMap p xs → RelMap q xs → p = q

variable {M}

/-- A tuple is typed in the realization of a structure exactly when some relation holds of it. -/
theorem isSome_toRealization_eval_iff (t : Fin n ↪ M) :
    ((toRealization M).eval t).isSome ↔ ∃ p : baseLanguage.{u}.Relations n, RelMap p ⇑t := by
  simp only [toRealization]
  split_ifs with h <;> simp [h]

/-- A tuple has the stage type of a relation in the realization of a structure when the relation
holds of it and no other relation does. -/
theorem toRealization_eval_eq_some_of_unique {t : Fin n ↪ M} {p : baseLanguage.{u}.Relations n}
    (hp : RelMap p ⇑t) (hu : ∀ q : baseLanguage.{u}.Relations n, RelMap q ⇑t → q = p) :
    (toRealization M).eval t = some (type p) := by
  have hex : ∃ p, RelMap p ⇑t := ⟨p, hp⟩
  simp only [toRealization, hex, ↓reduceDIte]
  exact congrArg (some ∘ type) (hu _ hex.choose_spec)

/-- A tuple is untyped in the realization of a structure exactly when no relation holds of it. -/
theorem toRealization_eval_eq_none_iff (t : Fin n ↪ M) :
    (toRealization M).eval t = none ↔ ∀ p : baseLanguage.{u}.Relations n, ¬ RelMap p ⇑t := by
  rw [← Option.not_isSome_iff_eq_none, isSome_toRealization_eval_iff, not_exists]

/-- **The realization of a structure has legal types**: its types are stage types of relation
symbols. -/
theorem hasLegalTypes_toRealization : (toRealization M).HasLegalTypes := by
  intro k t q hq
  simp only [toRealization] at hq
  split_ifs at hq with h
  exact Option.some_injective _ hq ▸ isLegal_type _

/-- The type of a tuple in the realization of a structure is the stage type of a relation holding
of it. -/
theorem exists_relMap_of_toRealization_eval {t : Fin n ↪ M} {q : StageType.{u} ω n}
    (hq : (toRealization M).eval t = some q) :
    ∃ p : baseLanguage.{u}.Relations n, type p = q ∧ RelMap p ⇑t := by
  simp only [toRealization] at hq
  split_ifs at hq with h
  exact ⟨_, Option.some_injective _ hq, h.choose_spec⟩

namespace IsTypeAssignment

variable (h : IsTypeAssignment M)
include h

/-- In the realization of a type assignment, an injective tuple has the stage type of a relation
exactly when the relation holds of it. -/
theorem toRealization_eval_eq_some_iff (t : Fin n ↪ M) (p : baseLanguage.{u}.Relations n) :
    (toRealization M).eval t = some (type p) ↔ RelMap p ⇑t := by
  refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
  · obtain ⟨p', hp', h'⟩ := exists_relMap_of_toRealization_eval hp
    rwa [type_injective hp'] at h'
  · exact toRealization_eval_eq_some_of_unique hp fun q hq ↦ h.unique _ _ _ hq hp

/-- In a type assignment, a relation holds of a tuple exactly when the tuple is injective and has
the stage type of the relation in the realization. -/
theorem relMap_iff (p : baseLanguage.{u}.Relations n) (xs : Fin n → M) :
    RelMap p xs ↔ ∃ hx : Function.Injective xs, (toRealization M).eval ⟨xs, hx⟩ = some (type p) :=
  ⟨fun hp ↦ ⟨h.injective p xs hp, (h.toRealization_eval_eq_some_iff ⟨xs, _⟩ p).mpr hp⟩,
    fun ⟨hx, hp⟩ ↦ (h.toRealization_eval_eq_some_iff ⟨xs, hx⟩ p).mp hp⟩

end IsTypeAssignment

/-- **Round trip on structures**: the structure of the realization of a type assignment is the
type assignment. -/
theorem toStructure_toRealization (h : IsTypeAssignment M) :
    (toRealization M).toStructure = ‹baseLanguage.{u}.Structure M› :=
  structure_ext fun _ p xs ↦ (h.relMap_iff p xs).symm

end ToRealization

/-- The structure of a realization is a type assignment. -/
theorem isTypeAssignment_toStructure (R : Realization.{u, v} ω M) :
    @IsTypeAssignment M R.toStructure :=
  letI := R.toStructure
  ⟨fun _ _ _ ⟨h, _⟩ ↦ h, fun _ _ _ _ ⟨_, hp⟩ ⟨_, hq⟩ ↦ type_injective
    (Option.some_injective _ (hp.symm.trans hq))⟩

/-- **Round trip on realizations**: the realization of the structure of a realization with legal
types is the realization. -/
theorem toRealization_toStructure {R : Realization.{u, v} ω M} (hR : R.HasLegalTypes) :
    @toRealization M R.toStructure = R := by
  let := R.toStructure
  ext k t : 1
  refine Option.ext fun q ↦ ⟨fun hq ↦ ?_, fun hq ↦ ?_⟩
  · obtain ⟨p, rfl, hp⟩ := exists_relMap_of_toRealization_eval hq
    exact (R.relMap_toStructure_embedding p t).mp hp
  · rw [← type_symbol q (hR t q hq)] at hq ⊢
    exact ((isTypeAssignment_toStructure R).toRealization_eval_eq_some_iff t _).mpr
      ((R.relMap_toStructure_embedding _ t).mpr hq)

/-- **The type assignments are the structures of realizations**: a structure of the base language
is a type assignment exactly when it is the structure of a realization (which may be taken with
legal types, as the realization of the structure). -/
theorem isTypeAssignment_iff_exists_toStructure_eq [baseLanguage.{u}.Structure M] :
    IsTypeAssignment M ↔ ∃ R : Realization.{u, v} ω M, R.toStructure = ‹_› :=
  ⟨fun h ↦ ⟨_, toStructure_toRealization h⟩, fun ⟨R, hR⟩ ↦ hR ▸ isTypeAssignment_toStructure R⟩

section Iso

variable [baseLanguage.{u}.Structure M] [baseLanguage.{u}.Structure N]

/-- **Transport of realizations of structures**: along an isomorphism of structures, the
realization of a type assignment is carried to the realization of the target. -/
theorem toRealization_map (h : IsTypeAssignment M) (e : M ≃[baseLanguage.{u}] N) :
    (toRealization M).map (e : M ≃ N) = toRealization N := by
  ext k t : 1
  rw [Realization.map_eval]
  set t' : Fin k ↪ M := t.trans (e : M ≃ N).symm.toEmbedding
  have hrel (p : baseLanguage.{u}.Relations k) : RelMap p ⇑t ↔ RelMap p ⇑t' :=
    (relMap_trans_symm_toEmbedding e p t).symm
  refine Option.ext fun q ↦ ⟨fun hq ↦ ?_, fun hq ↦ ?_⟩
  · obtain ⟨p, rfl, hp⟩ := exists_relMap_of_toRealization_eval hq
    exact toRealization_eval_eq_some_of_unique ((hrel p).mpr hp) fun q hq ↦
      h.unique _ _ _ ((hrel q).mp hq) hp
  · obtain ⟨p, rfl, hp⟩ := exists_relMap_of_toRealization_eval hq
    exact (h.toRealization_eval_eq_some_iff t' p).mpr ((hrel p).mp hp)

/-- **Isomorphic type assignments have isomorphic realizations, and conversely**: two type
assignments are isomorphic structures exactly when their realizations are isomorphic. -/
theorem isIso_toRealization_iff (hM : IsTypeAssignment M) (hN : IsTypeAssignment N) :
    (toRealization M).IsIso (toRealization N) ↔ Nonempty (M ≃[baseLanguage.{u}] N) := by
  rw [Realization.isIso_iff_nonempty_equiv hasLegalTypes_toRealization hasLegalTypes_toRealization,
    toStructure_toRealization hM, toStructure_toRealization hN]

end Iso

end baseLanguage

end VaughtConjecture
