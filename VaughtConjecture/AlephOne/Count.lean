/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.Family
import VaughtConjecture.Counting.StructureCodes

/-!
# Exactly `2 ^ ℵ₁` isomorphism classes of models of cardinality `ℵ₁`

The carrier is `Carrier = ω₁.ToType`, of cardinality `ℵ₁`.  A **code** (`AlephOne.Code`) is a
structure code of the base language on the carrier: a map from the relation queries (a relation
symbol with a tuple of its arity) to `Bool`.  The base language has no function symbols and no
constants (`baseLanguage.isRelational`), so a structure on the carrier is the decoded structure of
its code.  `Code.Decoded c` is the carrier with the structure decoded from `c`.

The objects counted are **isomorphism classes**.  For a predicate `P` on codes,
`StructureCode.Classes baseLanguage Carrier P` is the quotient of the codes satisfying `P` by
isomorphism of their decoded structures; for a predicate `Q` on structures,
`StructureCode.StructureClasses baseLanguage Q` is the quotient of the sigma type of a carrier in
`Type` and a structure on it satisfying `Q` by isomorphism.

**Statements** (all proved, each by the theorem of the same name in lower camel case).

* `AlephOne.CodeCardLeTarget`: there are at most `2 ^ ℵ₁` codes.  Route: the general bound
  `StructureCode.CardLeTarget` (countably many symbols, `ℵ₁` finite lists from the carrier, so at
  most `ℵ₁` queries) at the carrier.
* `AlephOne.CodeClassesCardEqTarget` (the count): there is a family of codes indexed by
  the maps `ω₁ → Bool` whose decoded structures have the conclusions of
  `AlephOne.existsAlephOneFamilyScottRankTarget` (models of the density sentence, internal Scott
  rank `ω₁`, semantic Scott process of rank `ω₁` beyond `ω₁ + 1`, one common semantic Scott
  process at every positive length, pairwise nonisomorphic), such that **every** predicate on
  codes containing the family has exactly `2 ^ ℵ₁` isomorphism classes.  Route: the family theorem
  transported to the carrier along bijections (`StructureCode.ExistsIsoCodeTarget`); the upper
  bound passes to the quotient (`AlephOne.CodeCardLeTarget`); pairwise nonisomorphism makes the
  map from `ω₁ → Bool` to the classes injective, and `#(ω₁ → Bool) = 2 ^ ℵ₁`
  (`AlephOne.mk_classes_eq_of_family`).  The semantic Scott process passes along isomorphisms
  (`AlephOne.scottProcessOf_eq_of_equiv`).
* `AlephOne.ModelClassesCardEqTarget` (first consequence): the models of the density
  sentence of cardinality `ℵ₁` on carriers in `Type` fall into exactly `2 ^ ℵ₁` isomorphism
  classes.  Route: a class is sent to the class, among all codes, of a code for any of its members
  (`StructureCode.lift_mk_structureClasses_le`), which is injective, so there are at most
  `2 ^ ℵ₁` classes; the decoded members of the coded family give the lower bound
  (`AlephOne.mk_structureClasses_eq_of_family`).
* `AlephOne.ScottClassModelClassesCardEqTarget` (second consequence): there is a model
  `N` of the density sentence of cardinality `ℵ₁` and internal Scott rank `ω₁` such that the
  models of the density sentence of cardinality `ℵ₁` with the semantic Scott process of `N` at
  every positive length already fall into exactly `2 ^ ℵ₁` isomorphism classes.  Route: the same
  count, with `N` the decoded member of the coded family at the constant map `false`
  (`AlephOne.mk_scottClass_eq_of_family`); no second count is made.

The count is about all codes satisfying the predicate, not only about the family: the family enters
only through the lower bound.

## Placement

This file belongs to the `ℵ₁` companion construction over the density sentence, recorded in
`roadmap/COMPANIONS.md` ("The `ℵ₁` companion construction").
-/

namespace VaughtConjecture.AlephOne

universe u v w w'

open Ordinal FirstOrder Language InfinitaryLogic.ScottProcess.Semantic StructureCode

/-- The carrier `ω₁.ToType` is infinite: it has `ℵ₁` points (`AlephOne.mk_carrier`). -/
instance infinite_carrier : Infinite Carrier :=
  Cardinal.infinite_iff.mpr (mk_carrier ▸ Cardinal.aleph0_le_aleph 1)

/-- A **code**: a structure code of the base language on the carrier `ω₁.ToType`, a map from the
relation queries (a relation symbol with a tuple of the carrier of its arity) to `Bool`. -/
abbrev Code : Type 1 :=
  StructureSpaceOn baseLanguage.{0} Carrier

/-- The carrier with the structure decoded from the code `c`: a relation holds of a tuple when `c`
answers `true` to the query. -/
def Code.Decoded (_c : Code) : Type :=
  Carrier

/-- The decoded structure of a code. -/
noncomputable instance (c : Code) : baseLanguage.{0}.Structure c.Decoded :=
  c.toStructure

/-- The decoded structure of a code is on an infinite carrier. -/
instance (c : Code) : Infinite c.Decoded :=
  inferInstanceAs (Infinite Carrier)

/-- **Target: at most `2 ^ ℵ₁` codes** (proved).  The structure codes of the base language on the
carrier `ω₁.ToType` number at most `2 ^ ℵ₁`. -/
def CodeCardLeTarget : Prop :=
  Cardinal.mk Code ≤ 2 ^ Cardinal.aleph 1

/-- **Target: every predicate on codes containing the coded family has exactly `2 ^ ℵ₁`
isomorphism classes** (proved; existence of the family, then a statement about every predicate).
There is a family `F` of codes on the carrier `ω₁.ToType`, indexed by the maps `ω₁ → Bool`, whose
decoded structures satisfy the density sentence, have internal Scott rank `ω₁` and semantic Scott
process of rank `ω₁` at every length beyond `ω₁ + 1`, all have the same semantic Scott process of
every positive length, and are pairwise nonisomorphic; and for every predicate `P` on codes with
`P (F A)` for every `A`, the quotient of the codes satisfying `P` by isomorphism of their decoded
structures has cardinality `2 ^ ℵ₁`. -/
def CodeClassesCardEqTarget : Prop :=
  ∃ F : (Carrier → Bool) → Code,
    (∀ A, Sentenceω.Realize baseLanguage.densitySentence.{0} (F A).Decoded ∧
      internalScottRank (L := baseLanguage.{0}) (F A).Decoded = (ω₁ : Ordinal.{0}) ∧
      ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
        (scottProcessOf baseLanguage.{0} (F A).Decoded δ (zero_le.trans_lt hδ)).IsRank ω₁) ∧
    (∀ A A' ⦃δ : Ordinal.{0}⦄ (hδ : 0 < δ),
      scottProcessOf baseLanguage.{0} (F A).Decoded δ hδ =
        scottProcessOf baseLanguage.{0} (F A').Decoded δ hδ) ∧
    (∀ A A', A ≠ A' → IsEmpty ((F A).Decoded ≃[baseLanguage.{0}] (F A').Decoded)) ∧
    ∀ P : Code → Prop, (∀ A, P (F A)) →
      Cardinal.mk (Classes baseLanguage.{0} Carrier P) = 2 ^ Cardinal.aleph 1

/-- **Target: exactly `2 ^ ℵ₁` isomorphism classes of models of the density sentence of
cardinality `ℵ₁`** (proved).  The quotient of the sigma type of a carrier `M` in `Type` and a
structure of the base language on `M` satisfying the density sentence, with `#M = ℵ₁`, by
isomorphism has cardinality `2 ^ ℵ₁`. -/
def ModelClassesCardEqTarget : Prop :=
  Cardinal.mk (StructureClasses baseLanguage.{0} fun (M : Type) [baseLanguage.{0}.Structure M] ↦
      Sentenceω.Realize baseLanguage.densitySentence.{0} M ∧
        Cardinal.mk M = Cardinal.aleph 1) =
    2 ^ Cardinal.aleph 1

/-- **Target: exactly `2 ^ ℵ₁` isomorphism classes of models of cardinality `ℵ₁` in one Scott
class** (proved; existence of the reference model, then a count).  There is a structure `N` of the
base language on an infinite carrier in `Type`, satisfying the density sentence, of cardinality
`ℵ₁` and internal Scott rank `ω₁`, with semantic Scott process of rank `ω₁` at every length beyond
`ω₁ + 1`, such that the quotient by isomorphism of the sigma type of a carrier `M` in `Type` and a
structure of the base language on `M` satisfying the density sentence, with `#M = ℵ₁`, `M`
infinite and the semantic Scott process of `M` equal to that of `N` at every positive length, has
cardinality `2 ^ ℵ₁`. -/
def ScottClassModelClassesCardEqTarget : Prop :=
  ∃ (N : Type) (_ : baseLanguage.{0}.Structure N) (_ : Infinite N),
    Sentenceω.Realize baseLanguage.densitySentence.{0} N ∧ Cardinal.mk N = Cardinal.aleph 1 ∧
    internalScottRank (L := baseLanguage.{0}) N = (ω₁ : Ordinal.{0}) ∧
    (∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
      (scottProcessOf baseLanguage.{0} N δ (zero_le.trans_lt hδ)).IsRank ω₁) ∧
    Cardinal.mk (StructureClasses baseLanguage.{0} fun (M : Type) [baseLanguage.{0}.Structure M] ↦
        Sentenceω.Realize baseLanguage.densitySentence.{0} M ∧
          Cardinal.mk M = Cardinal.aleph 1 ∧
          ∃ _ : Infinite M, ∀ ⦃δ : Ordinal.{0}⦄ (hδ : 0 < δ),
            scottProcessOf baseLanguage.{0} M δ hδ = scottProcessOf baseLanguage.{0} N δ hδ) =
      2 ^ Cardinal.aleph 1

/-! ### Proofs -/

/-- **Isomorphic structures have the same semantic Scott process** of every positive length, for
a relational language and infinite carriers in any two universes: an isomorphism and its inverse
carry the injective tuples of each structure to injective tuples of the other with the same
semantic entry (`sf_trans_equiv`). -/
theorem scottProcessOf_eq_of_equiv {L : Language.{u, v}} [L.IsRelational] {M : Type w}
    {N : Type w'} [L.Structure M] [L.Structure N] [Infinite M] [Infinite N] (f : M ≃[L] N)
    {δ : Ordinal.{0}} (hδ : 0 < δ) : scottProcessOf L M δ hδ = scottProcessOf L N δ hδ := by
  ext α hα n x
  simp only [scottProcessOf_Φ, Set.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.trans f.toEquiv.toEmbedding, sf_trans_equiv f α a⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b.trans f.symm.toEquiv.toEmbedding, sf_trans_equiv f.symm α b⟩

/-- **At most `2 ^ ℵ₁` codes**, the target form: `StructureCode.cardLeTarget` at the carrier, of
cardinality `ℵ₁` (`AlephOne.mk_carrier`). -/
theorem codeCardLeTarget : CodeCardLeTarget := by
  have h := StructureCode.cardLeTarget (L := baseLanguage.{0}) (α := Carrier)
  have h₁ : Cardinal.lift.{1} (Cardinal.mk Carrier) = Cardinal.aleph 1 := by simp
  rw [h₁] at h
  exact h

/-- **A pairwise nonisomorphic family of codes indexed by `ω₁ → Bool` gives exactly `2 ^ ℵ₁`
classes** to every predicate containing it: at most the number of codes
(`AlephOne.codeCardLeTarget`), and at least the number of indices, since the class of `F A`
determines `A` (`StructureCode.injective_mk_classes`). -/
theorem mk_classes_eq_of_family (F : (Carrier → Bool) → Code)
    (hF : ∀ A A', A ≠ A' → IsEmpty ((F A).Decoded ≃[baseLanguage.{0}] (F A').Decoded))
    (P : Code → Prop) (hP : ∀ A, P (F A)) :
    Cardinal.mk (Classes baseLanguage.{0} Carrier P) = 2 ^ Cardinal.aleph 1 := by
  refine le_antisymm ((mk_classes_le P).trans codeCardLeTarget) ?_
  have h := Cardinal.lift_mk_le_lift_mk_of_injective (injective_mk_classes F hP
    fun A A' ⟨e⟩ ↦ by_contra fun hne ↦ (hF A A' hne).false e)
  have h₁ : Cardinal.lift.{1} (Cardinal.mk (Carrier → Bool)) = 2 ^ Cardinal.aleph 1 := by
    simp
  rw [h₁, Cardinal.lift_uzero] at h
  exact h

/-- **Every predicate on codes containing the coded family has exactly `2 ^ ℵ₁` isomorphism
classes**, the target form.  The family of `AlephOne.existsAlephOneFamilyScottRankTarget` is
transported to the carrier along bijections (`StructureCode.existsIsoCodeTarget`); sentences, the
internal Scott rank (`internalScottRank_map_equiv`) and the semantic Scott process
(`AlephOne.scottProcessOf_eq_of_equiv`) pass along the isomorphisms, and so does
nonisomorphism; the count is `AlephOne.mk_classes_eq_of_family`. -/
theorem codeClassesCardEqTarget : CodeClassesCardEqTarget := by
  obtain ⟨M, _, _, hM, hproc, hne, -⟩ := existsAlephOneFamilyScottRankTarget
  have hiso : ∀ A, ∃ c : Code, Nonempty (M A ≃[baseLanguage.{0}] c.Decoded) := fun A ↦
    StructureCode.existsIsoCodeTarget (L := baseLanguage.{0}) (M := M A) (α := Carrier)
      (by simp [(hM A).2.1])
  choose F e using hiso
  have hF : ∀ A A', A ≠ A' → IsEmpty ((F A).Decoded ≃[baseLanguage.{0}] (F A').Decoded) :=
    fun A A' h ↦ ⟨fun g ↦ (hne A A' h).false (((e A').some.symm.comp g).comp (e A).some)⟩
  refine ⟨F, fun A ↦ ⟨?_, ?_, fun δ hδ ↦ ?_⟩, fun A A' δ hδ ↦ ?_, hF,
    mk_classes_eq_of_family F hF⟩
  · exact (LomegaEquiv.of_equiv (e A).some _).mp (hM A).1
  · exact (internalScottRank_map_equiv (e A).some).trans (hM A).2.2.1
  · rw [← scottProcessOf_eq_of_equiv (e A).some]
    exact (hM A).2.2.2 hδ
  · rw [← scottProcessOf_eq_of_equiv (e A).some, ← scottProcessOf_eq_of_equiv (e A').some]
    exact hproc A A' hδ

/-- **A pairwise nonisomorphic family of codes indexed by `ω₁ → Bool` gives exactly `2 ^ ℵ₁`
classes of structures** to every predicate `Q` on structures on carriers in `Type` of cardinality
`ℵ₁` that holds of the decoded members of the family.  At most: a class is sent to the class,
among all codes, of a code for any of its members (`StructureCode.lift_mk_structureClasses_le`),
and there are at most `2 ^ ℵ₁` codes (`AlephOne.codeCardLeTarget`).  At least: the class of the
decoded structure of `F A` determines `A`. -/
theorem mk_structureClasses_eq_of_family (F : (Carrier → Bool) → Code)
    (hF : ∀ A A', A ≠ A' → IsEmpty ((F A).Decoded ≃[baseLanguage.{0}] (F A').Decoded))
    (Q : ∀ (M : Type) [baseLanguage.{0}.Structure M], Prop)
    (hQ : ∀ (M : Type) [baseLanguage.{0}.Structure M], Q M → Cardinal.mk M = Cardinal.aleph 1)
    (hFQ : ∀ A, Q (F A).Decoded) :
    Cardinal.mk (StructureClasses baseLanguage.{0} Q) = 2 ^ Cardinal.aleph 1 := by
  refine le_antisymm ?_ ?_
  · have h := lift_mk_structureClasses_le (α := Carrier) Q fun M _ hM ↦ by
      simp [hQ M hM]
    simp only [Cardinal.lift_id] at h
    exact h.trans (Cardinal.mk_quotient_le.trans codeCardLeTarget)
  · let g : (Carrier → Bool) → StructureClasses baseLanguage.{0} Q :=
      fun A ↦ Quotient.mk _ ⟨(F A).Decoded, ⟨inferInstance, hFQ A⟩⟩
    have hg : Function.Injective g := fun A A' h ↦ by_contra fun hne ↦ by
      obtain ⟨e⟩ := Quotient.exact h
      exact (hF A A' hne).false e
    have h := Cardinal.lift_mk_le_lift_mk_of_injective hg
    have h₁ : Cardinal.lift.{1} (Cardinal.mk (Carrier → Bool)) = 2 ^ Cardinal.aleph 1 := by
      simp
    rw [h₁, Cardinal.lift_uzero] at h
    exact h

/-- **The Scott class of a member of the coded family has exactly `2 ^ ℵ₁` isomorphism
classes**: for a pairwise nonisomorphic family of codes whose decoded structures satisfy the
density sentence and share their semantic Scott process at every positive length, and any index
`A₀`, the models of the density sentence of cardinality `ℵ₁` with the semantic Scott process of
the decoded structure of `F A₀` at every positive length fall into exactly `2 ^ ℵ₁` isomorphism
classes (`AlephOne.mk_structureClasses_eq_of_family`). -/
theorem mk_scottClass_eq_of_family (F : (Carrier → Bool) → Code)
    (hΦ : ∀ A, Sentenceω.Realize baseLanguage.densitySentence.{0} (F A).Decoded)
    (hproc : ∀ A A' ⦃δ : Ordinal.{0}⦄ (hδ : 0 < δ),
      scottProcessOf baseLanguage.{0} (F A).Decoded δ hδ =
        scottProcessOf baseLanguage.{0} (F A').Decoded δ hδ)
    (hF : ∀ A A', A ≠ A' → IsEmpty ((F A).Decoded ≃[baseLanguage.{0}] (F A').Decoded))
    (A₀ : Carrier → Bool) :
    Cardinal.mk (StructureClasses baseLanguage.{0} fun (M : Type) [baseLanguage.{0}.Structure M] ↦
        Sentenceω.Realize baseLanguage.densitySentence.{0} M ∧
          Cardinal.mk M = Cardinal.aleph 1 ∧
          ∃ _ : Infinite M, ∀ ⦃δ : Ordinal.{0}⦄ (hδ : 0 < δ),
            scottProcessOf baseLanguage.{0} M δ hδ =
              scottProcessOf baseLanguage.{0} (F A₀).Decoded δ hδ) =
      2 ^ Cardinal.aleph 1 :=
  mk_structureClasses_eq_of_family F hF _ (fun _ _ h ↦ h.2.1)
    fun A ↦ ⟨hΦ A, mk_carrier, inferInstance, fun _ hδ ↦ hproc A A₀ hδ⟩

/-- **Exactly `2 ^ ℵ₁` isomorphism classes of models of the density sentence of cardinality
`ℵ₁`**, the target form: `AlephOne.mk_structureClasses_eq_of_family` for the coded family of
`AlephOne.codeClassesCardEqTarget`. -/
theorem modelClassesCardEqTarget : ModelClassesCardEqTarget := by
  obtain ⟨F, hF₁, -, hne, -⟩ := codeClassesCardEqTarget
  exact mk_structureClasses_eq_of_family F hne _ (fun _ _ h ↦ h.2)
    fun A ↦ ⟨(hF₁ A).1, mk_carrier⟩

/-- **Exactly `2 ^ ℵ₁` isomorphism classes of models of cardinality `ℵ₁` in one Scott class**, the
target form: the reference model is the decoded member at the constant map `false` of the coded
family of `AlephOne.codeClassesCardEqTarget`, and the count is
`AlephOne.mk_scottClass_eq_of_family`. -/
theorem scottClassModelClassesCardEqTarget : ScottClassModelClassesCardEqTarget := by
  obtain ⟨F, hF₁, hproc, hne, -⟩ := codeClassesCardEqTarget
  exact ⟨(F fun _ ↦ false).Decoded, inferInstance, inferInstance, (hF₁ _).1, mk_carrier,
    (hF₁ _).2.1, (hF₁ _).2.2,
    mk_scottClass_eq_of_family F (fun A ↦ (hF₁ A).1) hproc hne fun _ ↦ false⟩

end VaughtConjecture.AlephOne
