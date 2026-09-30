/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.FiniteSupportClosure

/-!
# Transport of finitary closures along maps of finite hulls

InfinitaryLogic's `FiniteSupportClosure.setClosure c` extends a closure operator `c` on the
finite subsets of a type to all subsets by finite character, and `setClosure_unique` shows that
this is the only finite-character extension agreeing with `c` on finite inputs.  This file shows
that equality or equivariance on finite hulls extends to the global closure.

* `image_setClosure`: if a map `f` carries the `h`-hull of every finite subset of `A` onto the
  `k`-hull of its image, then `f` carries the `h`-closure of `A` onto the `k`-closure of `f '' A`.
  The map need not be injective, and the hypothesis is only required below `A`; an equivalence
  `e : M ≃ N` with `(h F).image e = k (F.image e)` for all `F` is the motivating case, and it
  transports closures between different carriers.
* `setClosure_congr`: two finite hull operators agreeing on the finite subsets of `A` have the
  same closure of `A`.  This is the case `f = id` of `image_setClosure`; agreement on all finite
  sets is `ClosureOperator.ext` followed by `congrArg`.

No model theory is involved.  See `roadmap/README.md`, Layer 0, "Finite closure".
-/

namespace VaughtConjecture.Closure

open InfinitaryLogic.FiniteSupportClosure

variable {M N : Type*}

/-- Equivariance of the finitary extension: a map carrying the `h`-hull of each finite subset
of `A` onto the `k`-hull of its image carries the `h`-closure of `A` onto the `k`-closure of the
image of `A`. -/
theorem image_setClosure [DecidableEq N] (h : ClosureOperator (Finset M))
    (k : ClosureOperator (Finset N)) (f : M → N) {A : Set M}
    (hf : ∀ F : Finset M, (↑F : Set M) ⊆ A → (h F).image f = k (F.image f)) :
    f '' setClosure h A = setClosure k (f '' A) := by
  ext y
  simp only [Set.mem_image, mem_setClosure_iff]
  constructor
  · rintro ⟨x, ⟨F, hFA, hx⟩, rfl⟩
    refine ⟨F.image f, ?_, ?_⟩
    · rw [Finset.coe_image]
      exact Set.image_mono hFA
    · rw [← hf F hFA]
      exact Finset.mem_image_of_mem f hx
  · rintro ⟨G, hG, hy⟩
    obtain ⟨F, hFA, rfl⟩ := Finset.subset_set_image_iff.mp hG
    rw [← hf F hFA] at hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨x, ⟨F, hFA, hx⟩, rfl⟩

/-- Two finite hull operators that agree on every finite subset of `A` give the same closure
of `A`: the case `f = id` of `image_setClosure`. -/
theorem setClosure_congr (h k : ClosureOperator (Finset M)) {A : Set M}
    (hhk : ∀ F : Finset M, (↑F : Set M) ⊆ A → h F = k F) :
    setClosure h A = setClosure k A := by
  classical
  simpa using image_setClosure h k id (by simpa using hhk)

end VaughtConjecture.Closure
