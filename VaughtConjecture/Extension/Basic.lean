/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Extending a face by one point

Roadmap, Layer 3 (the coatom extension construction and the exact pinned extension, row 6 of the
table of 3.4: the embeddings of charts along which their faces are taken).

A face of a chart on `n` points is an embedding `f : Fin m ↪ Fin n`.  Adding a point `x` outside
its range is Mathlib's `Fin.Embedding.snoc f hx`, whose range is that of `f` with `x` added
(`Fin.Embedding.univ_map_snoc`).  Adding a new point to the chart as well gives
**`extendByLast f : Fin (m + 1) ↪ Fin (n + 1)`**, the face `f` followed by the new point: it is
`f` on the old points (`castSuccEmb_trans_extendByLast`), sends the last point to the last point,
commutes with composition (`extendByLast_trans`), and extends the identity to the identity
(`extendByLast_refl`).

A proper face, an embedding whose image is not the whole ground set, has a nonempty target
(`pos_of_univ_map_ne`); `Fin.castLEEmb` into a strictly larger `Fin` is a proper face
(`univ_map_castLEEmb_ne`).

## Placement

`Fin.Embedding.univ_map_snoc` belongs in `Mathlib.Data.Fin.Tuple.Embedding`, beside
`Fin.Embedding.snoc`.
-/

open Finset

/-- The range of `Fin.Embedding.snoc f ha` is the range of `f` with `a` added. -/
theorem Fin.Embedding.univ_map_snoc {α : Type*} [DecidableEq α] {m : ℕ} (f : Fin m ↪ α) {a : α}
    (ha : a ∉ Set.range f) : univ.map (Fin.Embedding.snoc f ha) = insert a (univ.map f) := by
  ext y
  simp only [mem_map, mem_univ, true_and, mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | last => exact Or.inl Fin.Embedding.snoc_last
    | cast i => exact Or.inr ⟨i, Fin.Embedding.snoc_castSucc.symm⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨Fin.last m, Fin.Embedding.snoc_last⟩
    · exact ⟨i.castSucc, Fin.Embedding.snoc_castSucc⟩

namespace VaughtConjecture

variable {m n k : ℕ}

/-- The face `f` followed by the new point: the embedding of `Fin (m + 1)` into `Fin (n + 1)`
that is `f` on `Fin m` and sends the last point to the last point. -/
def extendByLast (f : Fin m ↪ Fin n) : Fin (m + 1) ↪ Fin (n + 1) :=
  Fin.Embedding.snoc (f.trans Fin.castSuccEmb) (a := Fin.last n) fun ⟨i, hi⟩ ↦
    (Fin.castSucc_lt_last (f i)).ne hi

/-- `extendByLast f` sends an old point `i` to `f i`, as an old point. -/
@[simp] theorem extendByLast_castSucc (f : Fin m ↪ Fin n) (i : Fin m) :
    extendByLast f i.castSucc = (f i).castSucc :=
  Fin.Embedding.snoc_castSucc

/-- `extendByLast f` sends the last point to the last point. -/
@[simp] theorem extendByLast_last (f : Fin m ↪ Fin n) :
    extendByLast f (Fin.last m) = Fin.last n :=
  Fin.Embedding.snoc_last

/-- The face `f` followed by the new point restricts to `f` on the old points. -/
theorem castSuccEmb_trans_extendByLast (f : Fin m ↪ Fin n) :
    Fin.castSuccEmb.trans (extendByLast f) = f.trans Fin.castSuccEmb :=
  Fin.Embedding.init_snoc _ _

/-- Extending the identity by the new point is the identity. -/
@[simp] theorem extendByLast_refl :
    extendByLast (Function.Embedding.refl (Fin m)) = Function.Embedding.refl (Fin (m + 1)) :=
  Function.Embedding.ext fun i ↦ by
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp

/-- Extending a composite by the new point is composing the extensions. -/
theorem extendByLast_trans (g : Fin k ↪ Fin m) (f : Fin m ↪ Fin n) :
    (extendByLast g).trans (extendByLast f) = extendByLast (g.trans f) :=
  Function.Embedding.ext fun i ↦ by
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp

/-- The range of `extendByLast f` is the range of `f`, moved to the old points, with the new
point added. -/
theorem univ_map_extendByLast (f : Fin m ↪ Fin n) :
    univ.map (extendByLast f) = insert (Fin.last n) ((univ.map f).map Fin.castSuccEmb) := by
  rw [extendByLast, Fin.Embedding.univ_map_snoc, ← map_map]

variable {N : ℕ}

/-- An embedding into `Fin N` whose image is not the whole ground set has `0 < N`: a proper face
rules out the chart on no points. -/
theorem pos_of_univ_map_ne {g : Fin k ↪ Fin N} (hg : univ.map g ≠ univ) : 0 < N :=
  Nat.pos_of_ne_zero fun h ↦ hg (by subst h; exact Subsingleton.elim _ _)

/-- The image of `Fin.castLEEmb` is a proper subset when the target is larger. -/
theorem univ_map_castLEEmb_ne {hkN : k ≤ N} (hlt : k < N) :
    univ.map (Fin.castLEEmb hkN) ≠ univ := fun h ↦ by
  have hmem := mem_univ (⟨k, hlt⟩ : Fin N)
  rw [← h, mem_map] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  have h1 : ((Fin.castLEEmb hkN y : Fin N) : ℕ) = k := Fin.ext_iff.mp hy
  have h2 : ((Fin.castLEEmb hkN y : Fin N) : ℕ) = y := rfl
  omega

/-! ### Extending a permutation by the new point -/

namespace StageType

variable {n k : ℕ}

/-- The **extension of a permutation fixing the new point**. -/
noncomputable def extendPerm (σ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (k + 1)) :=
  Equiv.ofBijective (extendByLast σ.toEmbedding)
    (Finite.injective_iff_bijective.mp (extendByLast σ.toEmbedding).injective)

@[simp] theorem extendPerm_castSucc (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    extendPerm σ i.castSucc = (σ i).castSucc := by
  simp [extendPerm]

@[simp] theorem extendPerm_last (σ : Equiv.Perm (Fin k)) : extendPerm σ (Fin.last k) = Fin.last k :=
  by simp [extendPerm]

theorem extendPerm_symm_castSucc (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    (extendPerm σ).symm i.castSucc = (σ.symm i).castSucc := by
  rw [Equiv.symm_apply_eq, extendPerm_castSucc, Equiv.apply_symm_apply]

/-- The first points followed by the extension are the permutation followed by the first points. -/
theorem castSuccEmb_trans_extendPerm (σ : Equiv.Perm (Fin k)) :
    Fin.castSuccEmb.trans (extendPerm σ).toEmbedding = σ.toEmbedding.trans Fin.castSuccEmb :=
  Function.Embedding.ext fun i ↦ by simp

/-- The first points followed by the inverse extension. -/
theorem castSuccEmb_trans_extendPerm_symm (σ : Equiv.Perm (Fin k)) :
    Fin.castSuccEmb.trans (extendPerm σ).symm.toEmbedding =
      σ.symm.toEmbedding.trans Fin.castSuccEmb :=
  Function.Embedding.ext fun i ↦ by simp [extendPerm_symm_castSucc]

/-- A root followed by the new point, then the extension, is the relabelled root followed by the
new point. -/
theorem extendByLast_trans_extendPerm (σ : Equiv.Perm (Fin k)) (h : Fin n ↪ Fin k) :
    (extendByLast h).trans (extendPerm σ).toEmbedding = extendByLast (h.trans σ.toEmbedding) := by
  refine Function.Embedding.ext fun i ↦ ?_
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

end StageType

end VaughtConjecture
