/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.CodeTransport
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Isomorphism classes of coded structures, and the number of codes on an infinite carrier

For a relational language `L` and a carrier `α`, the infinitary-logic library codes a structure
on `α` by its Boolean answers to the relation queries: a **relation query** is a relation symbol
with a tuple of `α` of its arity (`RelQueryOn L α`), a **structure code** is a map from the
queries to `Bool` (`StructureSpaceOn L α`), and a code decodes to the structure on `α` in which a
relation holds of a tuple when the code answers `true` (`StructureSpaceOn.toStructure`).  Since
`L` has no function symbols, a structure is determined by its answers
(`StructureSpaceOn.toStructure_ofStructure`).

This file counts **isomorphism classes**, not codes.

* `StructureCode.isoSetoid L α`: two codes are related when their decoded structures are
  isomorphic.  `StructureCode.Classes L α P` is the quotient of the codes satisfying a predicate
  `P` by this relation.  `P` need not be invariant under isomorphism.
* `StructureCode.structureIsoSetoid L Q`: on the sigma type of structures on carriers in `Type w`
  satisfying a predicate `Q`, two members are related when they are isomorphic.
  `StructureCode.StructureClasses L Q` is the quotient.

**Statements** (both proved, each by the theorem of the same name in lower camel case).

* `StructureCode.CardLeTarget`: on an infinite carrier `α`, a relational language with countably
  many relation symbols has at most `2 ^ #α` structure codes.  Route: a query is determined by its
  symbol (with its arity) and the list of its tuple entries, so there are at most `ℵ₀ · #α = #α`
  queries, and a code is a map from the queries to `Bool`.
* `StructureCode.ExistsIsoCodeTarget`: a structure on a carrier `M` of the same cardinality as
  `α` is isomorphic to the decoded structure of a code on `α`.  Route: transport the structure
  along a bijection `M ≃ α` and encode it (`StructureSpaceOn.encodeViaEquiv`,
  `StructureSpaceOn.encodeViaEquiv_iso`).

**Counting** (proved).  `StructureCode.injective_mk_classes`: a pairwise nonisomorphic coded
family in `P` injects into the classes of `P`.  `StructureCode.lift_mk_structureClasses_le`: when
every structure satisfying `Q` has the cardinality of `α`, the classes of `Q` inject into the
classes of all codes on `α`, by sending a class to the class of a code for any of its members
(`StructureCode.codeOf`).  Neither predicate is assumed invariant under isomorphism.
-/

universe u v w w'

namespace VaughtConjecture.StructureCode

open Cardinal FirstOrder Language

section Classes

variable (L : Language.{u, v}) [L.IsRelational]

/-- **Isomorphism of decoded structures** on the codes on a carrier `α`: two codes are related
when the structures they decode to are isomorphic. -/
def isoSetoid (α : Type w) : Setoid (StructureSpaceOn L α) where
  r c d := Nonempty (@Language.Equiv L α α c.toStructure d.toStructure)
  iseqv :=
    ⟨fun c ↦ ⟨@Language.Equiv.refl L α c.toStructure⟩,
      fun {c d} ⟨e⟩ ↦ ⟨@Language.Equiv.symm L α α c.toStructure d.toStructure e⟩,
      fun {c d b} ⟨e⟩ ⟨f⟩ ↦
        ⟨@Language.Equiv.comp L α α c.toStructure d.toStructure α b.toStructure f e⟩⟩

/-- **The isomorphism classes of the codes satisfying `P`**: the quotient of the codes on `α`
satisfying `P` by isomorphism of their decoded structures (`StructureCode.isoSetoid`).  The
predicate is not assumed invariant under isomorphism; a class is represented by a code satisfying
`P`. -/
def Classes (α : Type w) (P : StructureSpaceOn L α → Prop) : Type (max v w) :=
  Quotient ((isoSetoid L α).comap (Subtype.val : {c // P c} → StructureSpaceOn L α))

/-- **Isomorphism** on the structures on carriers in `Type w` satisfying a predicate `Q`: two
members of the sigma type are related when they are isomorphic. -/
def structureIsoSetoid (Q : ∀ (M : Type w) [L.Structure M], Prop) :
    Setoid (Σ M : Type w, {inst : L.Structure M // @Q M inst}) where
  r x y := Nonempty (@Language.Equiv L x.1 y.1 x.2.1 y.2.1)
  iseqv :=
    ⟨fun x ↦ ⟨@Language.Equiv.refl L x.1 x.2.1⟩,
      fun {x y} ⟨e⟩ ↦ ⟨@Language.Equiv.symm L x.1 y.1 x.2.1 y.2.1 e⟩,
      fun {x y z} ⟨e⟩ ⟨f⟩ ↦
        ⟨@Language.Equiv.comp L x.1 y.1 x.2.1 y.2.1 z.1 z.2.1 f e⟩⟩

/-- **The isomorphism classes of the structures satisfying `Q`** on carriers in `Type w`: the
quotient of the sigma type of a carrier and a structure on it satisfying `Q` by isomorphism
(`StructureCode.structureIsoSetoid`). -/
def StructureClasses (Q : ∀ (M : Type w) [L.Structure M], Prop) : Type (max u v (w + 1)) :=
  Quotient (structureIsoSetoid L Q)

end Classes

/-- **Target: at most `2 ^ #α` structure codes on an infinite carrier** (proved).  For a
relational language with countably many relation symbols (of all arities together) and an
infinite carrier `α`, the codes on `α` number at most `2 ^ #α`. -/
def CardLeTarget : Prop :=
  ∀ ⦃L : Language.{u, v}⦄ [L.IsRelational] [Countable (Σ n, L.Relations n)] ⦃α : Type w⦄
    [Infinite α], #(StructureSpaceOn L α) ≤ 2 ^ Cardinal.lift.{v} #α

/-- **Target: a structure on a carrier of the cardinality of `α` is isomorphic to a decoded code
on `α`** (proved).  For a relational language `L`, a structure on a carrier `M` and a carrier `α`
with `#M = #α` (lifted to a common universe), some code on `α` decodes to a structure isomorphic
to the given one. -/
def ExistsIsoCodeTarget : Prop :=
  ∀ ⦃L : Language.{u, v}⦄ [L.IsRelational] ⦃M : Type w⦄ [L.Structure M] ⦃α : Type w'⦄,
    Cardinal.lift.{w'} #M = Cardinal.lift.{w} #α →
    ∃ c : StructureSpaceOn L α, Nonempty (@Language.Equiv L M α _ c.toStructure)

/-- **At most `2 ^ #α` structure codes on an infinite carrier**, the target form.  A query is
determined by its symbol (with its arity) and the list of its tuple entries; there are countably
many symbols and `#α` lists, so at most `#α` queries, and a code is a map from the queries to
`Bool`. -/
theorem cardLeTarget : CardLeTarget.{u, v, w} := by
  intro L _ _ α _
  let f : RelQueryOn L α → (Σ n, L.Relations n) × List α := fun q ↦ (q.1, List.ofFn q.2)
  have hf : Function.Injective f := by
    rintro ⟨⟨n, r⟩, a⟩ ⟨⟨m, s⟩, b⟩ h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    cases h₁
    cases List.ofFn_injective h₂
    rfl
  have hα : ℵ₀ ≤ Cardinal.lift.{v} #α := by simp
  have hq : #(RelQueryOn L α) ≤ Cardinal.lift.{v} #α :=
    calc #(RelQueryOn L α) ≤ #((Σ n, L.Relations n) × List α) := Cardinal.mk_le_of_injective hf
      _ = Cardinal.lift.{w} #(Σ n, L.Relations n) * Cardinal.lift.{v} #α := by
        rw [Cardinal.mk_prod, Cardinal.mk_list_eq_mk]
      _ ≤ Cardinal.lift.{v} #α * Cardinal.lift.{v} #α := by
        gcongr
        exact (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0).trans hα
      _ = Cardinal.lift.{v} #α := Cardinal.mul_eq_self hα
  calc #(StructureSpaceOn L α) = 2 ^ #(RelQueryOn L α) := by
        simp [StructureSpaceOn]
    _ ≤ 2 ^ Cardinal.lift.{v} #α := Cardinal.power_le_power_left two_ne_zero hq

/-- **A structure on a carrier of the cardinality of `α` is isomorphic to a decoded code on `α`**,
the target form: the structure transported along a bijection with `α` and encoded
(`StructureSpaceOn.encodeViaEquiv_iso`). -/
theorem existsIsoCodeTarget : ExistsIsoCodeTarget.{u, v, w, w'} := by
  intro L _ M _ α h
  obtain ⟨e⟩ := Cardinal.lift_mk_eq'.mp h
  exact ⟨StructureSpaceOn.encodeViaEquiv e, StructureSpaceOn.encodeViaEquiv_iso e⟩

/-! ### Counting classes -/

section Counting

variable {L : Language.{u, v}} [L.IsRelational]

/-- The classes of the codes satisfying a predicate number at most the codes. -/
theorem mk_classes_le {α : Type w} (P : StructureSpaceOn L α → Prop) :
    #(Classes L α P) ≤ #(StructureSpaceOn L α) :=
  Cardinal.mk_quotient_le.trans (Cardinal.mk_subtype_le P)

/-- **A pairwise nonisomorphic coded family in a predicate injects into its classes**: if the
decoded structures of `F i` and `F j` are isomorphic only for `i = j`, and every `F i` satisfies
`P`, the class of `F i` determines `i`.  The predicate need not be invariant under
isomorphism. -/
theorem injective_mk_classes {α : Type w} {ι : Type*} {P : StructureSpaceOn L α → Prop}
    (F : ι → StructureSpaceOn L α) (hP : ∀ i, P (F i))
    (hF : ∀ i j, Nonempty (@Language.Equiv L α α (F i).toStructure (F j).toStructure) → i = j) :
    Function.Injective fun i ↦
      (Quotient.mk _ ⟨F i, hP i⟩ : Classes L α P) :=
  fun i j h ↦ hF i j (Quotient.exact h)

/-- A code on `α` for a structure on a carrier of the cardinality of `α`: one whose decoded
structure is isomorphic to it (`StructureCode.existsIsoCodeTarget`). -/
noncomputable def codeOf {α : Type w'} (M : Type w) [L.Structure M]
    (h : Cardinal.lift.{w'} #M = Cardinal.lift.{w} #α) : StructureSpaceOn L α :=
  Classical.choose (existsIsoCodeTarget (L := L) (M := M) (α := α) h)

/-- The decoded structure of `StructureCode.codeOf M h` is isomorphic to `M`. -/
theorem nonempty_equiv_codeOf {α : Type w'} (M : Type w) [L.Structure M]
    (h : Cardinal.lift.{w'} #M = Cardinal.lift.{w} #α) :
    Nonempty (@Language.Equiv L M α _ (codeOf (L := L) M h).toStructure) :=
  Classical.choose_spec (existsIsoCodeTarget (L := L) (M := M) (α := α) h)

/-- **The structure classes inject into the classes of all codes** on a carrier `α`, when every
structure satisfying `Q` has the cardinality of `α`: a class is sent to the class of a code for
any of its members (`StructureCode.codeOf`).  Isomorphic structures have isomorphic codes, and
isomorphic codes come from isomorphic structures.  The predicate need not be invariant under
isomorphism. -/
theorem lift_mk_structureClasses_le {α : Type w'} (Q : ∀ (M : Type w) [L.Structure M], Prop)
    (hQ : ∀ (M : Type w) [L.Structure M], Q M →
      Cardinal.lift.{w'} #M = Cardinal.lift.{w} #α) :
    Cardinal.lift.{max v w'} #(StructureClasses L Q) ≤
      Cardinal.lift.{max u v (w + 1)} #(Quotient (isoSetoid L α)) := by
  let code : (Σ M : Type w, {inst : L.Structure M // @Q M inst}) → StructureSpaceOn L α :=
    fun x ↦ @codeOf L _ α x.1 x.2.1 (@hQ x.1 x.2.1 x.2.2)
  have hcode : ∀ x : Σ M : Type w, {inst : L.Structure M // @Q M inst},
      Nonempty (@Language.Equiv L x.1 α x.2.1 (code x).toStructure) :=
    fun x ↦ @nonempty_equiv_codeOf L _ α x.1 x.2.1 (@hQ x.1 x.2.1 x.2.2)
  let g : StructureClasses L Q → Quotient (isoSetoid L α) :=
    Quotient.lift (fun x ↦ Quotient.mk _ (code x)) fun x y ⟨e⟩ ↦ by
      obtain ⟨ex⟩ := hcode x
      obtain ⟨ey⟩ := hcode y
      exact Quotient.sound ⟨@Language.Equiv.comp L α y.1 (code x).toStructure y.2.1 α
        (code y).toStructure ey (@Language.Equiv.comp L α x.1 (code x).toStructure x.2.1 y.1
          y.2.1 e (@Language.Equiv.symm L x.1 α x.2.1 (code x).toStructure ex))⟩
  have hg : Function.Injective g := by
    intro X Y h
    induction X using Quotient.inductionOn with | h x => ?_
    induction Y using Quotient.inductionOn with | h y => ?_
    obtain ⟨e⟩ : Nonempty (@Language.Equiv L α α (code x).toStructure (code y).toStructure) :=
      Quotient.exact h
    obtain ⟨ex⟩ := hcode x
    obtain ⟨ey⟩ := hcode y
    exact Quotient.sound ⟨@Language.Equiv.comp L x.1 α x.2.1 (code y).toStructure y.1 y.2.1
      (@Language.Equiv.symm L y.1 α y.2.1 (code y).toStructure ey)
      (@Language.Equiv.comp L x.1 α x.2.1 (code x).toStructure α (code y).toStructure e ex)⟩
  exact Cardinal.lift_mk_le_lift_mk_of_injective hg

end Counting

end VaughtConjecture.StructureCode
