/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.PinnedExtension

/-!
# A closed coatom through a closed face

Roadmap, Layer 3, 3.4 (the exact pinned extension), and the coatom steps of (R2), (R3) and (R4).

**A closed coatom through a closed face** (`StageType.exists_coatom_trans_eq`, compiled in this
repository).  In a stage type on `n + 1` points, a closed face `f` of `k ≤ n` points lies in a
closed face `g` of `n` points (a coatom): `f = f'.trans g`.  Points are added one at a time, each
keeping the face closed (the faces form a plan, `Geometry.IsPlan.exists_insert_mem`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset

namespace StageType

/-! ### A closed coatom through a closed face -/

/-- **A closed coatom through a closed face**: in a stage type on `n + 1` points, every closed face
`f` of `k ≤ n` points lies in a closed face of `n` points, `f = f'.trans g` with `univ.map g` a
face.  Points are added one at a time, each keeping the face closed. -/
theorem exists_coatom_trans_eq {α : Ordinal.{u}} {n k : ℕ} (T : StageType.{u} α (n + 1))
    (f : Fin k ↪ Fin (n + 1)) (hf : univ.map f ∈ T.toCellScheme.faces) (hk : k ≤ n) :
    ∃ (g : Fin n ↪ Fin (n + 1)) (f' : Fin k ↪ Fin n),
      univ.map g ∈ T.toCellScheme.faces ∧ f'.trans g = f := by
  induction hd : n - k using Nat.strong_induction_on generalizing k with
  | _ d ih =>
    subst hd
    rcases hk.lt_or_eq with hlt | rfl
    · -- a point outside the face whose addition keeps the face closed
      have hplan := T.isWellFormed.isWellFormed.isPlan
      rw [T.isWellFormed.ground_eq] at hplan
      have hne : univ.map f ≠ univ := fun he ↦ by
        have := congrArg Finset.card he
        rw [card_map, Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
          at this
        omega
      obtain ⟨x, hx, hxP⟩ := hplan.exists_insert_mem hf hne
      have hx' : x ∉ Set.range f := fun ⟨i, hi⟩ ↦ hx (by simp [← hi])
      obtain ⟨g, f₁, hg, hf₁⟩ := ih (n - (k + 1)) (by omega) (Fin.Embedding.snoc f hx')
        (by rwa [Fin.Embedding.univ_map_snoc]) (by omega) rfl
      refine ⟨g, Fin.castSuccEmb.trans f₁, hg, ?_⟩
      rw [Function.Embedding.trans_assoc, hf₁]
      exact Fin.Embedding.init_snoc f hx'
    · exact ⟨f, Function.Embedding.refl _, hf, Function.Embedding.ext fun _ ↦ rfl⟩

end StageType

end VaughtConjecture
