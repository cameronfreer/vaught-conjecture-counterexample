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
* `exists_potentialIso_sameAtomicType_notMem_family`: the two-element order `0 < 1` has a
  potential isomorphism with itself and one-element tuples `a`, `b` of the same atomic type such
  that `⟨1, a, b⟩` is not in its family and no automorphism sends `a` to `b`.  So membership of
  the root in the family cannot be weakened to atomic compatibility.

For `M = N`, `exists_equiv_comp_eq` is InfinitaryLogic's
`FirstOrder.Language.exists_automorphism_of_bfEquiv_all` (`InfinitaryLogic.Scott.OrbitRank`)
composed with `FirstOrder.Language.PotentialIso.family_bfEquiv`, and `aboveRoot` is the
family-based analogue of that module's pointed potential isomorphism `pointedPotentialIso`; the
proof here follows the same pointed back-and-forth argument.  The addition is the two-structure
form, `M` and `N` possibly distinct.

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

@[simp]
theorem mem_aboveRoot_family {M N : Type*} [L.Structure M] [L.Structure N] {k : ℕ}
    {a : Fin k → M} {b : Fin k → N} {P : PotentialIso L M N} {h : ⟨k, a, b⟩ ∈ P.family} {n : ℕ}
    {c : Fin n → M} {d : Fin n → N} :
    (⟨n, c, d⟩ : Σ n, (Fin n → M) × (Fin n → N)) ∈ (aboveRoot P h).family ↔
      (⟨k + n, Fin.append a c, Fin.append b d⟩ : Σ n, (Fin n → M) × (Fin n → N)) ∈ P.family :=
  Iff.rfl

/-- Above the empty pair, `aboveRoot` has the same family as `P`. -/
theorem aboveRoot_empty_mem_family {M N : Type*} [L.Structure M] [L.Structure N]
    (P : PotentialIso L M N) : (aboveRoot P P.empty_mem).family = P.family := by
  ext ⟨n, c, d⟩
  have key : ∀ m (hm : m = n), (⟨m, c ∘ Fin.cast hm, d ∘ Fin.cast hm⟩ :
      Σ n, (Fin n → M) × (Fin n → N)) = ⟨n, c, d⟩ := by rintro _ rfl; rfl
  rw [mem_aboveRoot_family, Fin.elim0_append, Fin.elim0_append, key]

/-- **Rooted back-and-forth.**  For countable structures, every member `⟨k, a, b⟩` of a potential
isomorphism is extended by an isomorphism: some `e : M ≃[L] N` satisfies `e ∘ a = b`.

For `M = N` this is InfinitaryLogic's `FirstOrder.Language.exists_automorphism_of_bfEquiv_all`
composed with `FirstOrder.Language.PotentialIso.family_bfEquiv`; the proof follows the pointed
back-and-forth argument there, with `aboveRoot` in place of the pointed potential isomorphism. -/
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

/-- **Atomic compatibility of a root is not enough.**  The two-element order `Fin 2` has a
potential isomorphism `P` with itself and one-element tuples `a`, `b` of the same atomic type such
that `⟨1, a, b⟩ ∉ P.family` and no automorphism `e` satisfies `e ∘ a = b`. -/
theorem exists_potentialIso_sameAtomicType_notMem_family :
    ∃ (P : PotentialIso Language.order (Fin 2) (Fin 2)) (a b : Fin 1 → Fin 2),
      SameAtomicType (L := Language.order) a b ∧ ⟨1, a, b⟩ ∉ P.family ∧
        ∀ e : Fin 2 ≃[Language.order] Fin 2, ⇑e ∘ a ≠ b := by
  have hne : ∀ e : Fin 2 ≃[Language.order] Fin 2, ⇑e ∘ ![0] ≠ ![1] := fun e he ↦ by
    have h0 : e 0 = 1 := congrFun he 0
    have h01 : e 0 ≤ e 1 := (e.map_rel (orderRel.le : Language.order.Relations 2) ![0, 1]).2
      (show (0 : Fin 2) ≤ 1 by decide)
    rw [h0] at h01
    exact absurd (e.injective (h0.trans (le_antisymm h01 (Fin.le_last _)))) (by decide)
  refine ⟨PotentialIso.refl _, ![0], ![1], fun idx ↦ ?_,
    fun h ↦ (exists_equiv_comp_eq _ h).elim hne, hne⟩
  rcases idx with ⟨i, j⟩ | ⟨⟨⟩, f⟩
  · simp [AtomicIdx.holds, Subsingleton.elim i j]
  · simp [AtomicIdx.holds, Structure.RelMap, Matrix.cons_val_fin_one]

end Example

end VaughtConjecture.Comparison
