/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Interval.Finset.Fin

/-!
# Merging two finite chains along a common subchain

Roadmap, Layer 3 (the coatom extension construction: the literal ordered face-map restrictions of
the amalgam) and Library conventions (the cells of a scheme on `n` points are `Fin card`, in their
order, and a face restriction enumerates the visible cells in increasing order).

The cells of a scheme are a finite chain, and its face restriction along an embedding enumerates
the visible cells in increasing order.  For the restrictions of an amalgam to its two coatoms to
be literally the two given schemes, the cells of the amalgam must be ordered so that both given
orders are retained.  This file constructs such an order: the **merge** of two chains `Fin ca` and
`Fin cb` along common subchains `ea : Fin r ↪o Fin ca` and `eb : Fin r ↪o Fin cb` (the cells of the
common face, in the order of each chain).

* `Merge ea eb` has the points `Merge.inl i` of the first chain and the points `Merge.inr j` of
  the second chain outside its common subchain.  It is linearly ordered by the key `Merge.key`: a
  point is placed after the points of the common subchain below it, points of the first chain
  before points of the second, and otherwise in the given order.
* `Merge.left : Fin ca ↪o Merge ea eb` and `Merge.right : Fin cb ↪o Merge ea eb` are order
  embeddings; `Merge.right` sends `eb t` to `Merge.left (ea t)` (`Merge.right_apply_eb`), so the
  two chains are identified along the common subchain and both orders are retained.
* `Merge.card`: the merge has `ca + (cb - r)` points.

## Placement

Nothing here is about schemes: `Merge` is general order theory on finite chains, and belongs in an
`Order/` folder of the library (and is a candidate for Mathlib).  It is stated here beside its
only application, the amalgam of `VaughtConjecture.Extension.CoatomAmalgam`.
-/

namespace VaughtConjecture

open Finset

variable {ca cb r : ℕ}

/-- The **merge** of two finite chains `Fin ca` and `Fin cb` along common subchains `ea` and `eb`:
the points of the first chain and the points of the second chain outside its common subchain. -/
inductive Merge (ea : Fin r ↪o Fin ca) (eb : Fin r ↪o Fin cb) : Type
  /-- A point of the first chain. -/
  | inl (i : Fin ca)
  /-- A point of the second chain outside its common subchain. -/
  | inr (j : Fin cb) (hj : j ∉ Set.range eb)
  deriving DecidableEq

namespace Merge

variable (ea : Fin r ↪o Fin ca) (eb : Fin r ↪o Fin cb)

/-- The merge as a sum type. -/
def equivSum : Merge ea eb ≃ Fin ca ⊕ {j : Fin cb // j ∉ Set.range eb} where
  toFun
    | inl i => .inl i
    | inr j hj => .inr ⟨j, hj⟩
  invFun
    | .inl i => inl i
    | .inr j => inr j.1 j.2
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with i | ⟨j, hj⟩ <;> rfl

/-- The merge is finite: it is a sum of two finite types. -/
noncomputable instance : Fintype (Merge ea eb) := by
  classical
  exact Fintype.ofEquiv _ (equivSum ea eb).symm

/-- The number of points of the common subchain at most a point of the first chain. -/
def countLeft (i : Fin ca) : ℕ := #{t | ea t ≤ i}

/-- The number of points of the common subchain below a point of the second chain. -/
def countRight (j : Fin cb) : ℕ := #{t | eb t < j}

/-- The key of a point of the merge: the number of common points before it, then the chain it
comes from, then its position in that chain. -/
def key : Merge ea eb → ℕ ×ₗ ℕ ×ₗ ℕ
  | inl i => toLex (countLeft ea i, toLex (0, (i : ℕ)))
  | inr j _ => toLex (countRight eb j, toLex (1, (j : ℕ)))

/-- Distinct points of the merge have distinct keys. -/
theorem key_injective : Function.Injective (key ea eb) := by
  rintro (i | ⟨j, hj⟩) (i' | ⟨j', hj'⟩) h
  · exact congrArg inl (Fin.ext (congrArg (fun x ↦ (ofLex (ofLex x).2).2) h))
  · exact absurd (congrArg (fun x ↦ (ofLex (ofLex x).2).1) h) zero_ne_one
  · exact absurd (congrArg (fun x ↦ (ofLex (ofLex x).2).1) h) one_ne_zero
  · obtain rfl : j = j' := Fin.ext (congrArg (fun x ↦ (ofLex (ofLex x).2).2) h)
    rfl

/-- The merge is ordered by the key. -/
instance : LinearOrder (Merge ea eb) := LinearOrder.lift' (key ea eb) (key_injective ea eb)

variable {ea eb}

/-- The order of the merge is the order of the keys. -/
theorem lt_iff_key {x y : Merge ea eb} : x < y ↔ key ea eb x < key ea eb y := Iff.rfl

/-- Comparison of keys. -/
private theorem key_lt_iff {a b c a' b' c' : ℕ} :
    toLex (a, toLex (b, c)) < toLex (a', toLex (b', c')) ↔
      a < a' ∨ a = a' ∧ (b < b' ∨ b = b' ∧ c < c') := by
  simp only [Prod.Lex.toLex_lt_toLex]

variable (ea eb)

/-- The number of common points at most a point of the common subchain of the first chain. -/
theorem countLeft_ea (t : Fin r) : countLeft ea (ea t) = t + 1 := by
  have : ({t' | ea t' ≤ ea t} : Finset (Fin r)) = Iic t := by
    ext t'
    simp
  rw [countLeft, this, Fin.card_Iic]

/-- The number of common points below a point of the common subchain of the second chain. -/
theorem countRight_eb (t : Fin r) : countRight eb (eb t) = t := by
  have : ({t' | eb t' < eb t} : Finset (Fin r)) = Iio t := by
    ext t'
    simp
  rw [countRight, this, Fin.card_Iio]

/-- The number of common points up to a point of the first chain increases with the point. -/
theorem countLeft_mono : Monotone (countLeft ea) := fun _ _ h ↦
  card_le_card (monotone_filter_right _ fun _ _ h' ↦ h'.trans h)

/-- The number of common points below a point of the second chain increases with the point. -/
theorem countRight_mono : Monotone (countRight eb) := fun _ _ h ↦
  card_le_card (monotone_filter_right _ fun _ _ h' ↦ h'.trans_le h)

/-- The first chain in the merge. -/
def left : Fin ca ↪o Merge ea eb :=
  OrderEmbedding.ofStrictMono inl fun i i' h ↦ by
    rw [lt_iff_key, key, key, key_lt_iff]
    rcases (countLeft_mono ea h.le).lt_or_eq with hc | hc
    · exact Or.inl hc
    · exact Or.inr ⟨hc, Or.inr ⟨rfl, h⟩⟩

/-- The first chain sends a point `i` to `inl i`. -/
@[simp] theorem left_apply (i : Fin ca) : left ea eb i = inl i := rfl

open Classical in
/-- The second chain in the merge: a point of the common subchain is sent to the corresponding
point of the first chain. -/
noncomputable def rightFun (j : Fin cb) : Merge ea eb :=
  if h : j ∈ Set.range eb then inl (ea (Classical.choose (Set.mem_range.mp h))) else inr j h

/-- A point of the common subchain of the second chain is sent to the corresponding point of
the first chain. -/
theorem rightFun_eb (t : Fin r) : rightFun ea eb (eb t) = inl (ea t) := by
  have h : eb t ∈ Set.range eb := ⟨t, rfl⟩
  rw [rightFun, dite_eq_left h, eb.injective (Classical.choose_spec (Set.mem_range.mp h))]

/-- A point of the second chain outside its common subchain is sent to `inr`. -/
theorem rightFun_of_notMem {j : Fin cb} (h : j ∉ Set.range eb) : rightFun ea eb j = inr j h := by
  rw [rightFun, dite_eq_right h]

/-- The second chain is sent into the merge in increasing order. -/
theorem strictMono_rightFun : StrictMono (rightFun ea eb) := by
  intro j j' hjj'
  by_cases hj : j ∈ Set.range eb <;> by_cases hj' : j' ∈ Set.range eb
  · obtain ⟨t, rfl⟩ := hj
    obtain ⟨t', rfl⟩ := hj'
    rw [rightFun_eb, rightFun_eb, lt_iff_key, key, key, key_lt_iff, countLeft_ea, countLeft_ea]
    exact Or.inl (by simpa using eb.lt_iff_lt.mp hjj')
  · obtain ⟨t, rfl⟩ := hj
    rw [rightFun_eb, rightFun_of_notMem ea eb hj', lt_iff_key, key, key, key_lt_iff,
      countLeft_ea]
    -- Every common point up to `t` lies below `j'`.
    have hle : t.1 + 1 ≤ countRight eb j' := by
      rw [← Fin.card_Iic, countRight]
      exact card_le_card fun t'' h ↦
        mem_filter.mpr ⟨mem_univ _, (eb.monotone (mem_Iic.mp h)).trans_lt hjj'⟩
    rcases hle.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, Or.inl zero_lt_one⟩
  · obtain ⟨t', rfl⟩ := hj'
    rw [rightFun_of_notMem ea eb hj, rightFun_eb, lt_iff_key, key, key, key_lt_iff,
      countLeft_ea]
    -- Every common point below `j` lies below `eb t'`.
    have hle : countRight eb j ≤ countRight eb (eb t') := countRight_mono eb hjj'.le
    rw [countRight_eb] at hle
    exact Or.inl (Nat.lt_succ_of_le hle)
  · rw [rightFun_of_notMem ea eb hj, rightFun_of_notMem ea eb hj', lt_iff_key, key, key,
      key_lt_iff]
    rcases (countRight_mono eb hjj'.le).lt_or_eq with hc | hc
    · exact Or.inl hc
    · exact Or.inr ⟨hc, Or.inr ⟨rfl, hjj'⟩⟩

/-- The second chain in the merge, as an order embedding. -/
noncomputable def right : Fin cb ↪o Merge ea eb :=
  OrderEmbedding.ofStrictMono (rightFun ea eb) (strictMono_rightFun ea eb)

/-- `Merge.right` sends a point of the common subchain of the second chain to the
corresponding point of the first chain. -/
theorem right_apply_eb (t : Fin r) : right ea eb (eb t) = inl (ea t) :=
  rightFun_eb ea eb t

/-- `Merge.right` sends a point of the second chain outside its common subchain to `inr`. -/
theorem right_apply_of_notMem {j : Fin cb} (h : j ∉ Set.range eb) : right ea eb j = inr j h :=
  rightFun_of_notMem ea eb h

/-- The points of the merge from the second chain are the images of the common subchain of the
first chain and the points outside it of the second chain. -/
theorem mem_range_right {x : Merge ea eb} :
    x ∈ Set.range (right ea eb) ↔ (∃ t, x = inl (ea t)) ∨ ∃ j hj, x = inr j hj := by
  constructor
  · rintro ⟨j, rfl⟩
    by_cases hj : j ∈ Set.range eb
    · obtain ⟨t, rfl⟩ := hj
      exact Or.inl ⟨t, right_apply_eb ea eb t⟩
    · exact Or.inr ⟨j, hj, right_apply_of_notMem ea eb hj⟩
  · rintro (⟨t, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact ⟨eb t, right_apply_eb ea eb t⟩
    · exact ⟨j, right_apply_of_notMem ea eb hj⟩

/-- The points of the merge from the first chain. -/
theorem mem_range_left {x : Merge ea eb} : x ∈ Set.range (left ea eb) ↔ ∃ i, x = inl i := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩

/-- The merge has `ca + (cb - r)` points. -/
theorem card : Fintype.card (Merge ea eb) = ca + (cb - r) := by
  classical
  have hr : Fintype.card (Set.range eb) = r := by
    rw [Set.card_range_of_injective eb.injective, Fintype.card_fin]
  rw [Fintype.card_congr (equivSum ea eb), Fintype.card_sum, Fintype.card_fin,
    Fintype.card_subtype_compl, Fintype.card_fin, hr]

end Merge

end VaughtConjecture
