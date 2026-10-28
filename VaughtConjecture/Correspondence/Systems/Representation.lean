/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.BFClasses

/-!
# The canonical carriers represent the base

Numbering as in the current draft of [AFK26] (the published v1 reads identically).  For a weak
system `W` with carriers in universe `0` and a base sublanguage `E`, the type
`WeakSystem.BaseClasses` collects the isomorphism classes of members of the base on the positive
finite carriers `Fin (n + 1)` and on `ℕ`.  This file shows that it represents the members of the
base on countable nonempty carriers up to isomorphism, finite carriers included:

* `WeakSystem.baseClassesRepresentTarget` (`WeakSystem.BaseClassesRepresentTarget`): every member
  of the base on a countable nonempty carrier `M` is isomorphic to a member of the base on some
  `Fin (n + 1)` or on `ℕ`.  A finite `M` is in bijection with some `Fin k`
  (`Finite.exists_equiv_fin`), and `k ≠ 0` as `M` is nonempty; an infinite `M` is in bijection
  with `ℕ` (`nonempty_denumerable`).  The structure induced along the bijection is isomorphic to
  the given one, and is in the base: a lift is carried along the bijection
  (`WeakSystem.exists_isLiftAt_of_equiv`, from `WeakSystem.isoClosed` and
  `BaseSublanguage.reduct_inducedStructure`).
* The carrier and the representative of a class: `WeakSystem.baseClassCarrier` (`Fin (n + 1)` or
  `ℕ`, countable and nonempty) and `WeakSystem.baseClassRep` (the chosen member of the class),
  which is in the base (`WeakSystem.isInBase_baseClassRep`).
* The cover: `WeakSystem.exists_equiv_baseClassRep`, every member of the base on a countable
  nonempty carrier is isomorphic to the representative of some class; and the separation:
  `WeakSystem.eq_of_equiv_baseClassRep`, classes with isomorphic representatives are equal (a
  bijection between `Fin (n + 1)` and `Fin (m + 1)` forces `n = m`, and none exists between
  `Fin (n + 1)` and `ℕ`).  Together, `BaseClasses` is in bijection with the countable nonempty
  members of the base up to isomorphism.

The finite carriers are treated exactly as `ℕ`; no infiniteness is assumed.
-/

universe w w' wc wc'

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal

variable {L : Language.{w, w'}} {σ : GeometrySignature L}

namespace WeakSystem

variable {D : InvarianceDiagram σ} {S : InvariantSystem.{0} σ} (W : WeakSystem.{w, w', 0} D S)
variable {Lc : Language.{wc, wc'}} (E : σ.BaseSublanguage Lc)

/-! ### Transport to a canonical carrier -/

/-- **The base is closed under isomorphism**, onto countable carriers: an `L_c`-structure
isomorphic to a member of the base is in the base (`exists_isLiftAt_of_equiv`).  Correspondence
with the printed definitions. -/
theorem isInBase_of_equiv {M N : Type} [Countable N] {B : Lc.Structure M} {B' : Lc.Structure N}
    (g : @Language.Equiv Lc M N B B') (hB : W.IsInBase E B) : W.IsInBase E B' := by
  obtain ⟨β, hβ⟩ := hB
  obtain ⟨G', hG'⟩ := W.exists_isLiftAt_of_equiv E g hβ
  exact ⟨β, G', hG'⟩

/-- **The canonical carriers represent the base** (`BaseClassesRepresentTarget`): every member of
the base on a countable nonempty carrier is isomorphic to a member of the base on some
`Fin (n + 1)` or on `ℕ`, namely the structure induced along a bijection
(`Finite.exists_equiv_fin`, `nonempty_denumerable`; `isInBase_of_equiv`).  Correspondence with the
printed definitions. -/
theorem baseClassesRepresentTarget : W.BaseClassesRepresentTarget E := by
  intro M _ _ B hB
  rcases finite_or_infinite M with hM | hM
  · obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin M
    cases k with
    | zero => exact Fin.elim0 (e (Classical.arbitrary M))
    | succ n =>
      let g := @Equiv.inducedStructureEquiv Lc M (Fin (n + 1)) B e
      exact Or.inl ⟨n, _, W.isInBase_of_equiv E g hB, ⟨g⟩⟩
  · obtain ⟨d⟩ := nonempty_denumerable M
    let g := @Equiv.inducedStructureEquiv Lc M ℕ B (@Denumerable.eqv M d)
    exact Or.inr ⟨_, W.isInBase_of_equiv E g hB, ⟨g⟩⟩

/-! ### The carrier and the representative of a class -/

/-- **The carrier of a class of the base on the canonical carriers**: `Fin (n + 1)` for a class on
`Fin (n + 1)`, `ℕ` for a class on `ℕ`.  Correspondence with the printed definitions. -/
def baseClassCarrier : W.BaseClasses E → Type
  | Sum.inl p => Fin (p.1 + 1)
  | Sum.inr _ => ℕ

instance countable_baseClassCarrier (x : W.BaseClasses E) :
    Countable (W.baseClassCarrier E x) := by
  rcases x with p | q
  · exact (inferInstance : Countable (Fin (p.1 + 1)))
  · exact (inferInstance : Countable ℕ)

instance nonempty_baseClassCarrier (x : W.BaseClasses E) : Nonempty (W.baseClassCarrier E x) := by
  rcases x with p | q
  · exact (inferInstance : Nonempty (Fin (p.1 + 1)))
  · exact (inferInstance : Nonempty ℕ)

/-- **The representative of a class**: the chosen member (`Quotient.out`) of the class, a structure
on its carrier.  Correspondence with the printed definitions. -/
@[instance_reducible] noncomputable def baseClassRep :
    (x : W.BaseClasses E) → Lc.Structure (W.baseClassCarrier E x)
  | Sum.inl p => p.2.out.1
  | Sum.inr q => q.out.1

/-- **The representative of a class is in the base.**  Correspondence with the printed
definitions. -/
theorem isInBase_baseClassRep (x : W.BaseClasses E) : W.IsInBase E (W.baseClassRep E x) := by
  rcases x with p | q
  · exact p.2.out.2
  · exact q.out.2

/-! ### The cover and the separation -/

/-- **Every member of the base on a countable nonempty carrier is isomorphic to the representative
of a class** (`baseClassesRepresentTarget`, and the chosen member of the class of the canonical
structure, `Quotient.mk_out`).  Correspondence with the printed definitions. -/
theorem exists_equiv_baseClassRep (M : Type) [Countable M] [Nonempty M] (B : Lc.Structure M)
    (hB : W.IsInBase E B) :
    ∃ x : W.BaseClasses E,
      Nonempty (@Language.Equiv Lc M (W.baseClassCarrier E x) B (W.baseClassRep E x)) := by
  rcases W.baseClassesRepresentTarget E M B hB with ⟨n, B', hB', ⟨g⟩⟩ | ⟨B', hB', ⟨g⟩⟩
  · let q := Quotient.mk (W.baseIsoSetoid E (Fin (n + 1))) ⟨B', hB'⟩
    obtain ⟨g'⟩ : (W.baseIsoSetoid E (Fin (n + 1))).r q.out ⟨B', hB'⟩ := Quotient.mk_out _
    exact ⟨Sum.inl ⟨n, q⟩, ⟨@Language.Equiv.comp Lc M (Fin (n + 1)) B B' (Fin (n + 1)) q.out.1
      (@Language.Equiv.symm Lc _ _ q.out.1 B' g') g⟩⟩
  · let q := Quotient.mk (W.baseIsoSetoid E ℕ) ⟨B', hB'⟩
    obtain ⟨g'⟩ : (W.baseIsoSetoid E ℕ).r q.out ⟨B', hB'⟩ := Quotient.mk_out _
    exact ⟨Sum.inr q, ⟨@Language.Equiv.comp Lc M ℕ B B' ℕ q.out.1
      (@Language.Equiv.symm Lc _ _ q.out.1 B' g') g⟩⟩

/-- **Classes with isomorphic representatives are equal**: a bijection between `Fin (n + 1)` and
`Fin (m + 1)` gives `n = m` (`Fintype.card_congr`), there is none between `Fin (n + 1)` and `ℕ`
(`ℕ` is infinite), and on one carrier isomorphic representatives have one class.  Correspondence
with the printed definitions. -/
theorem eq_of_equiv_baseClassRep {x y : W.BaseClasses E}
    (h : Nonempty (@Language.Equiv Lc (W.baseClassCarrier E x) (W.baseClassCarrier E y)
      (W.baseClassRep E x) (W.baseClassRep E y))) : x = y := by
  obtain ⟨g⟩ := h
  have e := @Language.Equiv.toEquiv Lc _ _ (W.baseClassRep E x) (W.baseClassRep E y) g
  rcases x with ⟨n, q⟩ | q <;> rcases y with ⟨m, q'⟩ | q'
  · have e' : Fin (n + 1) ≃ Fin (m + 1) := e
    obtain rfl : n = m := by simpa using Fintype.card_congr e'
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    exact congrArg
      (fun r : Quotient (W.baseIsoSetoid E (Fin (n + 1))) ↦ (Sum.inl ⟨n, r⟩ : W.BaseClasses E))
      (Quotient.sound (s := W.baseIsoSetoid E (Fin (n + 1))) ⟨g⟩)
  · have e' : Fin (n + 1) ≃ ℕ := e
    exact absurd (Finite.of_equiv (Fin (n + 1)) e') (not_finite_iff_infinite.mpr inferInstance)
  · have e' : ℕ ≃ Fin (m + 1) := e
    exact absurd (Finite.of_equiv (Fin (m + 1)) e'.symm) (not_finite_iff_infinite.mpr inferInstance)
  · rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    exact congrArg Sum.inr (Quotient.sound (s := W.baseIsoSetoid E ℕ) ⟨g⟩)

end WeakSystem

end VaughtConjecture.Correspondence
