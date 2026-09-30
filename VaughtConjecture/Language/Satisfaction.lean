/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Cardinal.NatCard
import VaughtConjecture.Language.Sentence

/-!
# Satisfaction of the four-family sentence and models at stage `ω`

Roadmap, Layer 2 (equivalence of the sentence with modelhood in both directions, round trips,
isomorphism preservation and reflection, no finite models); semantic contract, items 1 and 5
(actual library satisfaction; the absence of finite models identifies the spectra of the models
on `ℕ` and on all countable carriers).

**Satisfaction.**  For a structure `M` of the base language, the extension clauses read on `M`
are those of its realization (`IsTypeAssignment.realizesOver_iff`), and the structural conditions
are a type assignment on a nonempty carrier whose realization is exactly consistent and covering
(`isStructural_iff`).  Hence (`realize_fourFamilySentence_iff`)

  `M ⊨ fourFamilySentence ↔ IsTypeAssignment M ∧ (toRealization M).IsModel`,

and for a realization `R` with legal types, `R.toStructure ⊨ fourFamilySentence ↔ R.IsModel`
(`realize_toStructure_fourFamilySentence_iff`); in particular the structure of a model satisfies
the sentence (`Realization.IsModel.realize_fourFamilySentence`).

**The correspondence** [Kni26, Proposition 3.3.5].  On a fixed carrier `M`, `R ↦ R.toStructure`
is a bijection from the models at stage `ω` on `M` to the structures on `M` satisfying the
four-family sentence, with inverse `toRealization` (`modelEquiv`).  It preserves and reflects
isomorphism: two models are isomorphic exactly when their structures are
(`Realization.IsModel.isIso_iff_nonempty_equiv`), and two structures satisfying the sentence are
isomorphic exactly when their realizations are (`isIso_toRealization_iff_of_realize`).  So the
countable models of the sentence up to isomorphism correspond to the countable models at stage `ω`
up to isomorphism.

**No finite models.**  A model at a positive stage is infinite
(`Realization.IsModel.infinite`): covering gives an occurrence, and the dominance clause at
`γ = 0` extends every occurrence by a new point, and the empty face is closed, so there are
occurrences of every arity (`Realization.IsModel.exists_arity_eq`).  Hence every structure
satisfying the four-family sentence is infinite (`infinite_of_realize_fourFamilySentence`).

## Placement

`Realization.IsModel.exists_le_arity` and `Realization.IsModel.infinite` belong in
`VaughtConjecture.Realization.Model`, beside `Realization.IsModel.nonempty_occurrence`; they are on
the placement list of `VaughtConjecture.Language.Basic`.

## References

The correspondence between the countable models of the sentence `T` and the countable models of
`S^ω` is [Kni26, Proposition 3.3.5], for R. W. Knight, *A counterexample to Vaught's Conjecture
using generalised Stone spaces* (draft, 20 February 2026).
-/

universe u v w

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal StageType baseLanguage

variable {M : Type v} {N : Type w} {n : ℕ}

/-! ### Models are infinite -/

namespace Realization

variable {α : Ordinal.{u}} {R : Realization.{u, v} α M}

/-- A model at a positive stage has an occurrence of every arity: the empty face of any
occurrence is closed, so the empty tuple is typed, and the dominance clause at `γ = 0` extends
every occurrence by a new point. -/
theorem IsModel.exists_arity_eq (hR : R.IsModel) (hα : 0 < α) (k : ℕ) :
    ∃ x : R.Occurrence, x.arity = k := by
  induction k with
  | zero =>
    obtain ⟨x⟩ := hR.nonempty_occurrence
    have h := Realization.eval_face hR.isConsistent x (Function.Embedding.ofIsEmpty (α := Fin 0))
    have hs : (R.eval (Function.Embedding.ofIsEmpty (α := Fin 0))).isSome := by
      rw [show (Function.Embedding.ofIsEmpty (α := Fin 0)).trans x.tuple
        = Function.Embedding.ofIsEmpty from by ext i; exact i.elim0] at h
      rw [h, StageType.isSome_restrictFace_iff]
      simpa using x.type.isWellFormed.isWellFormed.isPlan.empty_mem
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨⟨0, _, p, hp⟩, rfl⟩
  | succ k ih =>
    obtain ⟨x, rfl⟩ := ih
    obtain ⟨u, -, q, -, hq⟩ := hR.dominance x 0 hα
    exact ⟨⟨_, u, q, hq⟩, rfl⟩

/-- A model at a positive stage has occurrences of arbitrarily large arity. -/
theorem IsModel.exists_le_arity (hR : R.IsModel) (hα : 0 < α) (k : ℕ) :
    ∃ x : R.Occurrence, k ≤ x.arity :=
  (hR.exists_arity_eq hα k).imp fun _ h ↦ h.ge

/-- **A model at a positive stage is infinite.** -/
theorem IsModel.infinite (hR : R.IsModel) (hα : 0 < α) : Infinite M := by
  refine not_finite_iff_infinite.mp fun _ ↦ ?_
  obtain ⟨x, hx⟩ := hR.exists_le_arity hα (Nat.card M + 1)
  have h := Finite.card_le_of_embedding x.tuple
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  omega

end Realization

namespace baseLanguage

/-! ### The clauses on the realization of a structure -/

section Structure

variable [baseLanguage.{u}.Structure M]

/-- The occurrence of the realization of a type assignment given by a tuple on which a relation
holds. -/
noncomputable def IsTypeAssignment.occurrence (h : IsTypeAssignment M)
    (p : baseLanguage.{u}.Relations n) (xs : Fin n → M) (hp : RelMap p xs) :
    (toRealization M).Occurrence :=
  ⟨n, ⟨xs, h.injective p xs hp⟩, type p, (h.toRealization_eval_eq_some_iff _ p).mpr hp⟩

/-- The relation of the type of an occurrence of the realization of a structure holds of its
tuple. -/
theorem relMap_occurrence (x : (toRealization M).Occurrence) :
    RelMap (symbol x.type (hasLegalTypes_toRealization _ _ x.eval_tuple)) ⇑x.tuple := by
  obtain ⟨p, hp, h⟩ := exists_relMap_of_toRealization_eval x.eval_tuple
  rwa [show symbol x.type _ = p from type_injective hp.symm]

/-- **The extension clauses on the realization**: for a type assignment, a point extends a tuple
to a tuple with a type in `U` in the structure exactly when it does in the realization. -/
theorem IsTypeAssignment.realizesOver_iff (h : IsTypeAssignment M) (t : Fin n ↪ M)
    (U : Set (StageType.{u} ω (n + 1))) :
    RealizesOver ⇑t U ↔ (toRealization M).RealizesOver t U := by
  refine ⟨fun ⟨y, q, hq, hrel⟩ ↦ ?_, fun ⟨u, hu, q, hq, he⟩ ↦ ?_⟩
  · let s : Fin (n + 1) ↪ M := ⟨Fin.snoc t y, h.injective q _ hrel⟩
    exact ⟨s, by ext i; simp [s], type q, hq, (h.toRealization_eval_eq_some_iff s q).mpr hrel⟩
  · have hs : Fin.snoc ⇑t (u (Fin.last n)) = ⇑u := by
      rw [← hu]
      exact Fin.snoc_init_self (α := fun _ ↦ M) u
    refine ⟨u (Fin.last n), symbol q (hasLegalTypes_toRealization u q he), hq, ?_⟩
    rw [hs]
    exact (h.toRealization_eval_eq_some_iff u _).mp he

/-- **The structural conditions on the realization**: a structure satisfies the structural
conditions exactly when it is a type assignment on a nonempty carrier whose realization is exactly
consistent and covering. -/
theorem isStructural_iff : IsStructural M ↔ IsTypeAssignment M ∧ Nonempty M ∧
    (toRealization M).IsConsistent ∧ (toRealization M).IsCovering := by
  refine ⟨fun h ↦ ?_, fun ⟨hT, hne, hcons, hcov⟩ ↦ ⟨hT, hne, fun n p xs hp m f ↦ ?_, ?_⟩⟩
  · have hcons : (toRealization M).IsConsistent := by
      intro m k t p f hp
      have hl := hasLegalTypes_toRealization t p hp
      have hP := (h.toRealization_eval_eq_some_iff t (symbol p hl)).mp hp
      have hface := h.face _ _ hP f
      cases hr : restrictFace f p with
      | none =>
        exact (toRealization_eval_eq_none_iff _).mpr fun q ↦ hface.2 hr q
      | some r =>
        exact (h.toRealization_eval_eq_some_iff _ (symbol r (hl.restrictFace f hr))).mpr
          (hface.1 _ hr)
    refine ⟨h.toIsTypeAssignment, h.nonempty, hcons,
      (Realization.isCovering_iff_exists_castAdd hcons).mpr fun n t ↦ ?_⟩
    obtain ⟨k, p, ys, hp⟩ := h.covering t t.injective
    exact ⟨k, ⟨Fin.append t ys, h.injective p _ hp⟩, by ext i; simp,
      (isSome_toRealization_eval_iff _).mpr ⟨p, hp⟩⟩
  · let t : Fin n ↪ M := ⟨xs, hT.injective p xs hp⟩
    have hc := hcons t (type p) f ((hT.toRealization_eval_eq_some_iff t p).mpr hp)
    refine ⟨fun q hq ↦ (hT.toRealization_eval_eq_some_iff (f.trans t) q).mp (hc.trans hq),
      fun hn q ↦ (toRealization_eval_eq_none_iff (f.trans t)).mp (hc.trans hn) q⟩
  · intro n xs hxs
    obtain ⟨k, u, hu, hs⟩ := hcov.exists_castAdd hcons ⟨xs, hxs⟩
    obtain ⟨p, hp⟩ := (isSome_toRealization_eval_iff u).mp hs
    refine ⟨k, p, fun j ↦ u (Fin.natAdd n j), ?_⟩
    convert hp using 1
    funext i
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i
    · rw [Fin.append_left]
      exact (DFunLike.congr_fun hu i).symm
    · rw [Fin.append_right]

/-- **The four families on the realization**: a structure satisfies the structural conditions and
the four extension families exactly when it is a type assignment whose realization is a model. -/
theorem isFourFamilyModel_iff :
    IsFourFamilyModel M ↔ IsTypeAssignment M ∧ (toRealization M).IsModel := by
  refine ⟨fun h ↦ ?_, fun ⟨hT, hM⟩ ↦ ?_⟩
  · obtain ⟨hT, hne, hcons, hcov⟩ := isStructural_iff.mp h.toIsStructural
    refine ⟨hT, hne, hasLegalTypes_toRealization, hcons, hcov, fun x S hS ↦ ?_,
      fun x S ρ hS ↦ ?_, fun x γ hγ hγω ↦ ?_, fun x γ hγω ↦ ?_⟩ <;>
      refine (hT.realizesOver_iff x.tuple _).mp ?_
    · exact h.saturation _ _ (relMap_occurrence x) S hS
    · exact h.bottomPattern _ _ (relMap_occurrence x) S ρ hS
    · exact h.uniformity _ _ (relMap_occurrence x) γ hγ hγω
    · exact h.dominance _ _ (relMap_occurrence x) γ hγω
  · refine ⟨isStructural_iff.mpr ⟨hT, hM.nonempty, hM.isConsistent, hM.isCovering⟩,
      fun n p xs hp S hS ↦ ?_, fun n p xs hp S ρ hS ↦ ?_, fun n p xs hp γ hγ hγω ↦ ?_,
      fun n p xs hp γ hγω ↦ ?_⟩ <;>
      refine (hT.realizesOver_iff ⟨xs, hT.injective p xs hp⟩ _).mpr ?_
    · exact hM.saturation (hT.occurrence p xs hp) S hS
    · exact hM.bottomPattern (hT.occurrence p xs hp) S ρ hS
    · exact hM.uniformity (hT.occurrence p xs hp) γ hγ hγω
    · exact hM.dominance (hT.occurrence p xs hp) γ hγω

variable (M)

/-- **Satisfaction of the four-family sentence**: it holds in a structure exactly when the
structure is a type assignment whose realization is a model at stage `ω`. -/
theorem realize_fourFamilySentence_iff :
    fourFamilySentence.Realize M ↔ IsTypeAssignment M ∧ (toRealization M).IsModel :=
  (realize_fourFamilySentence_iff_isFourFamilyModel M).trans isFourFamilyModel_iff

/-- **Satisfaction of the structural sentence**: it holds in a structure exactly when the
structure is a type assignment on a nonempty carrier whose realization is exactly consistent and
covering. -/
theorem realize_structuralSentence_iff_toRealization :
    structuralSentence.Realize M ↔ IsTypeAssignment M ∧ Nonempty M ∧
      (toRealization M).IsConsistent ∧ (toRealization M).IsCovering :=
  (realize_structuralSentence_iff M).trans isStructural_iff

variable {M}

/-- For a type assignment, the four-family sentence holds exactly when its realization is a
model at stage `ω`. -/
theorem IsTypeAssignment.realize_fourFamilySentence_iff (h : IsTypeAssignment M) :
    fourFamilySentence.Realize M ↔ (toRealization M).IsModel :=
  (baseLanguage.realize_fourFamilySentence_iff M).trans (and_iff_right h)

/-- A structure satisfying the four-family sentence is a type assignment. -/
theorem isTypeAssignment_of_realize_fourFamilySentence (h : fourFamilySentence.Realize M) :
    IsTypeAssignment M :=
  ((baseLanguage.realize_fourFamilySentence_iff M).mp h).1

/-- **Structures satisfying the four-family sentence are models** [Kni26, Proposition 3.3.5]: the
realization of a structure satisfying the sentence is a model at stage `ω`. -/
theorem isModel_toRealization_of_realize_fourFamilySentence (h : fourFamilySentence.Realize M) :
    (toRealization M).IsModel :=
  ((baseLanguage.realize_fourFamilySentence_iff M).mp h).2

end Structure

/-! ### The clauses on the structure of a realization -/

section Realization

variable {R : Realization.{u, v} ω M}

/-- For a realization with legal types, its structure satisfies the structural sentence exactly
when its carrier is nonempty and it is exactly consistent and covering. -/
theorem realize_toStructure_structuralSentence_iff (hR : R.HasLegalTypes) :
    @Sentenceω.Realize _ structuralSentence M R.toStructure ↔
      Nonempty M ∧ R.IsConsistent ∧ R.IsCovering := by
  rw [@realize_structuralSentence_iff_toRealization M R.toStructure, toRealization_toStructure hR]
  exact and_iff_right (isTypeAssignment_toStructure R)

/-- **Satisfaction by the structure of a realization**: for a realization with legal types, its
structure satisfies the four-family sentence exactly when it is a model at stage `ω`. -/
theorem realize_toStructure_fourFamilySentence_iff (hR : R.HasLegalTypes) :
    @Sentenceω.Realize _ fourFamilySentence M R.toStructure ↔ R.IsModel := by
  rw [@baseLanguage.realize_fourFamilySentence_iff M R.toStructure, toRealization_toStructure hR]
  exact and_iff_right (isTypeAssignment_toStructure R)

/-- **The structure of a model satisfies the four-family sentence** [Kni26, Proposition 3.3.5]. -/
theorem _root_.VaughtConjecture.Realization.IsModel.realize_fourFamilySentence (hR : R.IsModel) :
    @Sentenceω.Realize _ fourFamilySentence M R.toStructure :=
  (realize_toStructure_fourFamilySentence_iff hR.hasLegalTypes).mpr hR

end Realization

/-! ### The correspondence -/

/-- **The structures satisfying the four-family sentence are the structures of models**: a
structure satisfies the sentence exactly when it is the structure of a model at stage `ω` on the
same carrier. -/
theorem realize_fourFamilySentence_iff_exists [baseLanguage.{u}.Structure M] :
    fourFamilySentence.Realize M ↔
      ∃ R : Realization.{u, v} ω M, R.IsModel ∧ R.toStructure = ‹_› := by
  refine ⟨fun h ↦ ⟨_, isModel_toRealization_of_realize_fourFamilySentence h,
    toStructure_toRealization (isTypeAssignment_of_realize_fourFamilySentence h)⟩, ?_⟩
  rintro ⟨R, hR, rfl⟩
  exact hR.realize_fourFamilySentence

variable (M) in
/-- **The correspondence of [Kni26, Proposition 3.3.5] on a fixed carrier**: the models at stage
`ω` on `M` correspond one-to-one to the structures of the base language on `M` satisfying the
four-family sentence, by the structure of a model and the realization of a structure. -/
noncomputable def modelEquiv : {R : Realization.{u, v} ω M // R.IsModel} ≃
    {s : baseLanguage.{u}.Structure M // @Sentenceω.Realize _ fourFamilySentence M s} where
  toFun R := ⟨R.1.toStructure, R.2.realize_fourFamilySentence⟩
  invFun s := ⟨@toRealization M s.1,
    @isModel_toRealization_of_realize_fourFamilySentence M s.1 s.2⟩
  left_inv R := Subtype.ext (toRealization_toStructure R.2.hasLegalTypes)
  right_inv s := Subtype.ext
    (@toStructure_toRealization M s.1 (@isTypeAssignment_of_realize_fourFamilySentence M s.1 s.2))

/-- The structure corresponding to a model is its structure. -/
@[simp] theorem modelEquiv_apply_coe (R : {R : Realization.{u, v} ω M // R.IsModel}) :
    (modelEquiv M R).1 = R.1.toStructure :=
  rfl

/-- The model corresponding to a structure satisfying the sentence is its realization. -/
@[simp] theorem modelEquiv_symm_apply_coe
    (s : {s : baseLanguage.{u}.Structure M // @Sentenceω.Realize _ fourFamilySentence M s}) :
    ((modelEquiv M).symm s).1 = @toRealization M s.1 :=
  rfl

/-- **Isomorphism of models is isomorphism of their structures** [Kni26, Proposition 3.3.5]. -/
theorem _root_.VaughtConjecture.Realization.IsModel.isIso_iff_nonempty_equiv
    {R : Realization.{u, v} ω M} {S : Realization.{u, w} ω N} (hR : R.IsModel) (hS : S.IsModel) :
    R.IsIso S ↔ Nonempty (@Language.Equiv baseLanguage.{u} M N R.toStructure S.toStructure) :=
  Realization.isIso_iff_nonempty_equiv hR.hasLegalTypes hS.hasLegalTypes

/-- **Isomorphism of structures satisfying the sentence is isomorphism of their models**
[Kni26, Proposition 3.3.5]. -/
theorem isIso_toRealization_iff_of_realize [baseLanguage.{u}.Structure M]
    [baseLanguage.{u}.Structure N] (hM : fourFamilySentence.Realize M)
    (hN : fourFamilySentence.Realize N) :
    (toRealization M).IsIso (toRealization N) ↔ Nonempty (M ≃[baseLanguage.{u}] N) :=
  isIso_toRealization_iff (isTypeAssignment_of_realize_fourFamilySentence hM)
    (isTypeAssignment_of_realize_fourFamilySentence hN)

/-! ### No finite models -/

/-- **The four-family sentence has no finite models.** -/
theorem infinite_of_realize_fourFamilySentence [baseLanguage.{u}.Structure M]
    (h : fourFamilySentence.Realize M) : Infinite M :=
  (isModel_toRealization_of_realize_fourFamilySentence h).infinite omega0_pos

/-- No finite structure satisfies the four-family sentence. -/
theorem not_realize_fourFamilySentence_of_finite [baseLanguage.{u}.Structure M] [Finite M] :
    ¬ fourFamilySentence.Realize M :=
  fun h ↦ not_finite_iff_infinite.mpr (infinite_of_realize_fourFamilySentence h) ‹_›

end baseLanguage

end VaughtConjecture
