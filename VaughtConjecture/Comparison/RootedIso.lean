/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Karp.PotentialIso
import Mathlib.ModelTheory.Order

/-!
# Isomorphisms extending a root of a potential isomorphism

Roadmap, Layer 0, "Countable construction and comparison".  A potential isomorphism `P` between
structures `M` and `N` in a relational language is a family of pairs of finite tuples, preserving
atomic type, containing the empty pair, and closed under extension in both directions
(`FirstOrder.Language.PotentialIso`).  For countable `M` and `N` such a family yields an
isomorphism (`FirstOrder.Language.PotentialIso.countable_toEquiv`), built by back-and-forth from
the empty pair.  Here the construction is started at an arbitrary *root*, a member `⟨k, a, b⟩`
of the family.

* `aboveRoot P h` is the family of tuple pairs that extend the root inside `P`, reindexed by
  their new coordinates.  It is again a potential isomorphism, whose empty pair is the root.
* `exists_equiv_comp_eq`: for countable `M` and `N`, some isomorphism `e : M ≃[L] N` extends the
  root, `e ∘ a = b`.
* `exists_sameAtomicType_forall_comp_ne`: membership of the root in the family cannot be weakened
  to atomic compatibility.  In the two-element order `0 < 1`, the tuples `(0)` and `(1)` have the
  same atomic type, and the diagonal family is a potential isomorphism, but no automorphism sends
  `0` to `1`.

Mathlib's `FirstOrder.Language.FGEquiv.equiv_between_cg` also extends a given finite partial
isomorphism, but assumes that *every* finitely generated partial isomorphism extends in both
directions; the result here needs extension only within the selected family.
-/

namespace VaughtConjecture.Comparison

open FirstOrder Language Structure

universe w

variable {L : Language} [L.IsRelational]

/-- The potential isomorphism above a root `⟨k, a, b⟩` of `P`: it consists of the pairs
`⟨n, c, d⟩` for which `⟨k + n, Fin.append a c, Fin.append b d⟩` belongs to `P`. -/
def aboveRoot {M N : Type*} [L.Structure M] [L.Structure N] {k : ℕ} {a : Fin k → M}
    {b : Fin k → N} (P : PotentialIso L M N) (h : ⟨k, a, b⟩ ∈ P.family) : PotentialIso L M N :=
  PotentialIso.ofExtensionFamily (fun n c d ↦ ⟨k + n, Fin.append a c, Fin.append b d⟩ ∈ P.family)
    (by simpa using h)
    (fun {n c d} hcd ↦ by
      have := (P.compatible _ hcd).relabel (Fin.natAdd k : Fin n → Fin (k + n))
      rwa [show Fin.append a c ∘ Fin.natAdd k = c from funext (Fin.append_right a c),
        show Fin.append b d ∘ Fin.natAdd k = d from funext (Fin.append_right b d)] at this)
    (fun hcd m ↦ by simp only [Fin.append_snoc]; exact P.forth _ hcd m)
    (fun hcd n' ↦ by simp only [Fin.append_snoc]; exact P.back _ hcd n')

/-- **Rooted back-and-forth.**  For countable structures, every member `⟨k, a, b⟩` of a potential
isomorphism is extended by an isomorphism: some `e : M ≃[L] N` satisfies `e ∘ a = b`. -/
theorem exists_equiv_comp_eq {M N : Type w} [L.Structure M] [L.Structure N] [Countable M]
    [Countable N] {k : ℕ} {a : Fin k → M} {b : Fin k → N} (P : PotentialIso L M N)
    (h : ⟨k, a, b⟩ ∈ P.family) : ∃ e : M ≃[L] N, ⇑e ∘ a = b := by
  obtain ⟨e, he⟩ := (aboveRoot P h).countable_toEquiv_graph
  refine ⟨e, funext fun j ↦ ?_⟩
  obtain ⟨⟨n, c, d⟩, hcd, i, hci, hdi⟩ := he (a j)
  have := P.compatible _ hcd (.eq (Fin.castAdd n j) (Fin.natAdd k i))
  simp only [AtomicIdx.holds, Fin.append_left, Fin.append_right] at this
  exact (this.1 hci.symm).trans hdi |>.symm

section Example

attribute [local instance] Language.orderStructure

/-- **Atomic compatibility of a root is not enough.**  In the two-element order `Fin 2`, which is
potentially isomorphic to itself, the one-element tuples `(0)` and `(1)` have the same atomic type,
but no automorphism sends `0` to `1`. -/
theorem exists_sameAtomicType_forall_comp_ne :
    ∃ a b : Fin 1 → Fin 2, SameAtomicType (L := Language.order) a b ∧
      ∀ e : Fin 2 ≃[Language.order] Fin 2, ⇑e ∘ a ≠ b := by
  refine ⟨![0], ![1], fun idx ↦ ?_, fun e he ↦ ?_⟩
  · rcases idx with ⟨i, j⟩ | ⟨⟨⟩, f⟩
    · simp [AtomicIdx.holds, Subsingleton.elim i j]
    · change (![0] ∘ f) 0 ≤ (![0] ∘ f) 1 ↔ (![1] ∘ f) 0 ≤ (![1] ∘ f) 1
      simp
  · have h0 : e 0 = 1 := congrFun he 0
    have h01 : e 0 ≤ e 1 := (e.map_rel (orderRel.le : Language.order.Relations 2) ![0, 1]).2
      (show (0 : Fin 2) ≤ 1 by decide)
    rw [h0] at h01
    exact absurd (e.injective (h0.trans (le_antisymm h01 (Fin.le_last _)))) (by decide)

end Example

end VaughtConjecture.Comparison
