/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.PinnedExtension
import VaughtConjecture.Realization.Families

/-!
# Every coatom is the first coatom after relabelling

Roadmap, Layer 3 (the coatom steps of (R2), (R3) and (R4) of the table of 3.4).

A one-point coface `d'` of a face `p` of a context `t'` along a closed coatom
`f : Fin m ↪ Fin (m + 1)` is asked to have face `p` along `Fin.castSuccEmb`.  For the permutation
`σ` of `Fin (m + 1)` with `Fin.castSuccEmb.trans σ = f`
(`StageType.exists_perm_castSuccEmb_trans`), the reindexed context `t'.reindex σ` has face `p`
along `Fin.castSuccEmb` (`StageType.reindex_mem_cofaces_of_trans_eq`).  The permutation action is
`StageType.reindex` (`VaughtConjecture.Stage.Basic`).  Each item is compiled in this repository
(theorem named).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset

namespace StageType

/-- A self-embedding of `Fin k` as a permutation. -/
noncomputable def permOfEmbedding {k : ℕ} (e : Fin k ↪ Fin k) : Equiv.Perm (Fin k) :=
  Equiv.ofBijective e (Finite.injective_iff_bijective.mp e.injective)

@[simp] theorem permOfEmbedding_apply {k : ℕ} (e : Fin k ↪ Fin k) (i : Fin k) :
    permOfEmbedding e i = e i :=
  rfl

/-- **Every coatom is the first coatom after relabelling**: for every embedding
`f : Fin m ↪ Fin (m + 1)` some permutation `σ` has `Fin.castSuccEmb.trans σ = f`. -/
theorem exists_perm_castSuccEmb_trans {m : ℕ} (f : Fin m ↪ Fin (m + 1)) :
    ∃ σ : Equiv.Perm (Fin (m + 1)), Fin.castSuccEmb.trans σ.toEmbedding = f := by
  obtain ⟨a, ha⟩ : ∃ a, a ∉ Set.range f := by
    by_contra hall
    push Not at hall
    have h := Fintype.card_le_of_surjective f fun a ↦ hall a
    simp at h
  refine ⟨permOfEmbedding (Fin.Embedding.snoc f ha), Function.Embedding.ext fun i ↦ ?_⟩
  simp [Fin.Embedding.snoc_castSucc]

variable {α : Ordinal.{u}}

/-- **The relabelled context is a donor at the coatom**: if `Fin.castSuccEmb.trans σ = f` and `p`
is the face of a legal `t'` along `f`, then `t'.reindex σ` is a legal one-point coface of `p`. -/
theorem reindex_mem_cofaces_of_trans_eq {m : ℕ} {t' : StageType.{u} α (m + 1)}
    (ht' : t'.IsLegal) {f : Fin m ↪ Fin (m + 1)} {p : StageType.{u} α m}
    (hp : restrictFace f t' = some p) {σ : Equiv.Perm (Fin (m + 1))}
    (hσ : Fin.castSuccEmb.trans σ.toEmbedding = f) : t'.reindex σ ∈ p.cofaces :=
  ⟨ht'.reindex σ, by rw [restrictFace_reindex, hσ, hp]⟩

end StageType

end VaughtConjecture
