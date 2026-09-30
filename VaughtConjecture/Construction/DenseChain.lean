/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.Ideal

/-!
# Chains of conditions meeting countably many dense sets

Roadmap, Layer 0, "Countable construction and comparison".  Conditions form a preorder `C`, and
`c ≤ d` means that `d` extends `c` (stronger conditions are later).  A set `D` of conditions is
dense above `c₀` if every extension of `c₀` has a further extension in `D`.  For countably many
such sets there is an increasing sequence of conditions starting at `c₀` and meeting each of
them (`exists_monotone_forall_exists_mem`): this is the Rasiowa–Sikorski lemma.

Mathlib proves the lemma for a family of globally cofinal sets indexed by an `Encodable` type,
as `Order.sequenceOfCofinals` with `Order.sequenceOfCofinals.monotone` and
`Order.sequenceOfCofinals.encode_mem` (its ideal form is `Order.idealOfCofinals`).  The version
here allows an arbitrary `Countable` index type and requires density only above the starting
condition, which is the form used when every requirement is posed relative to a fixed root.
It is obtained by applying Mathlib's construction in the interval `Set.Ici c₀`.  Globally dense
sets, and a sequence `ℕ → Set C` of dense sets, are the special cases in which the density
hypothesis ignores `c₀ ≤ c`, respectively `ι = ℕ`.
-/

namespace VaughtConjecture.Construction

/-- **Countably many dense sets are met by a chain.**  In a preorder of conditions, for countably
many sets `D i` each dense above `c₀`, there is a monotone sequence of conditions starting at `c₀`
that meets every `D i`. -/
theorem exists_monotone_forall_exists_mem {C ι : Type*} [Preorder C] [Countable ι] (c₀ : C)
    (D : ι → Set C) (hD : ∀ i c, c₀ ≤ c → ∃ d ∈ D i, c ≤ d) :
    ∃ c : ℕ → C, c 0 = c₀ ∧ Monotone c ∧ ∀ i, ∃ n, c n ∈ D i := by
  have := Encodable.ofCountable ι
  let 𝒟 : ι → Order.Cofinal (Set.Ici c₀) := fun i ↦
    ⟨{c | c.1 ∈ D i}, fun c ↦
      let ⟨d, hd, hcd⟩ := hD i c c.2
      ⟨⟨d, c.2.trans hcd⟩, hd, hcd⟩⟩
  exact ⟨fun n ↦ (Order.sequenceOfCofinals ⟨c₀, le_rfl⟩ 𝒟 n).1, rfl,
    (Subtype.mono_coe _).comp (Order.sequenceOfCofinals.monotone _ _),
    fun i ↦ ⟨_, Order.sequenceOfCofinals.encode_mem _ 𝒟 i⟩⟩

end VaughtConjecture.Construction
