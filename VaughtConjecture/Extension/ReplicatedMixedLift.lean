/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedMixedLiftFromMirror
import VaughtConjecture.Extension.ReplicatedForcing

/-!
# The lift from a mixed face into a larger face at every grade

Roadmap, Layer 3 ((R3) and (R4), the mixed-coatom lift of the replicated carrier).

**The lift** (`Seed.cappedLift_mixed_face`).  For a mixed face `U`, a face `W ⊇ U` and a grade
`j` with `1 ≤ j ≤ m + 1` and `j ≤ |U|`, the replicated scheme lifts capped from `(U, j)` into
`(W, j)`, provided every cell of full scope of grade at most `j` has a cell at `W` with it as
original: the cell itself for `W` the ground set (`Seed.cappedLift_mixed_univ`), its copy at `W`
for `W` mixed (`Seed.cappedLift_mixed_mixed`).  The replicated scheme is the ladder tower over the
attachment mirrored at the mixed faces, and the lift is the lift from a mixed face of a mirrored
scheme (`Seed.cappedLift_mirror_mixed_face`), whose hypotheses the tower meets
(`Seed.cappedLift_mixed_face_of_mirror`).

**Scope.**  Part of the earlier route (the replicated scheme over the height-set tower, or the
ladder tower of the amalgam), whose open inputs the levels re-rendered per grade replace; not used
by the main theorem through the levels (`VaughtConjecture.MainTheorem.GrowthLevelRoute`), and kept
as reusable constructions.

## References

Bountifulness is [Kni26, Definition 2.5.14]; witnesses are [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}
  {U : Finset (Fin (m + 2))}

/-- The replicated scheme. -/
local notation "𝔼" => Seed.replicated I g H Γ A B'

/-- The ladder tower over the attachment. -/
local notation "𝕋" => Seed.attachTower I g H Γ A B'

variable (H Γ A B') in
open Classical in
/-- The copy at `U` of a cell of the tower of full scope and grade at most `|U|`; the cell itself
otherwise. -/
noncomputable def cpy (hU : U ∈ I.mixedFaces g) (v : Fin (𝕋).card) : Fin (𝔼).card :=
  if h : (𝕋).toCellScheme.scope v = univ ∧ (𝕋).toCellScheme.grade v ≤ #U then
    copyAt H Γ A B' hU v h.1 h.2 else Fin.castAdd _ v

theorem gradedIndex_cpy (hU : U ∈ I.mixedFaces g) {v : Fin (𝕋).card} {k : ℕ}
    (hv : (𝕋).toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) (hk : k ≤ #U) :
    (𝔼).toCellScheme.gradedIndex (cpy H Γ A B' hU v) = (U, k) := by
  classical
  unfold cpy
  rw [dite_eq_left ⟨congrArg Prod.fst hv, (congrArg Prod.snd hv).trans_le hk⟩]
  exact (gradedIndex_copyAt hU _ _ _).trans
    (Prod.ext rfl (show (𝕋).toCellScheme.grade v = k from congrArg Prod.snd hv))


/-- **The lift from a mixed face into a larger face** carrying cells of full scope or their copies:
for a mixed face `U ⊆ W` and a grade `j` with `1 ≤ j ≤ m + 1` and `j ≤ |U|`, given a choice `τ` of
a cell at `W` with original `v` for every cell `v` of full scope of the tower of grade at most `j`
(the cell itself when `W` is the ground set, its copy at `W` when `W` is mixed), the replicated
scheme lifts capped from `(U, j)` to `(W, j)`. -/
theorem cappedLift_mixed_face (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (hA0 : ∀ k, A k fun _ ↦ ⊥) (hU : U ∈ I.mixedFaces g) {W : Finset (Fin (m + 2))}
    (hUW : U ⊆ W) (τ : Fin (𝕋).card → Fin (𝔼).card)
    (hτo : ∀ v, (𝕋).mirrorOrig (I.mixedFaces g) (τ v) = v) {j : ℕ}
    (hτg : ∀ v k, (𝕋).toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k) → k ≤ j →
      (𝔼).toCellScheme.gradedIndex (τ v) = (W, k)) (hj1 : 1 ≤ j)
    (hjm : j ≤ m + 1) (hjU : j ≤ #U) :
    (𝔼).rows.CappedLift (X := (U, j)) (Y := (W, j)) ⟨hUW, le_rfl⟩ :=
  cappedLift_mixed_face_of_mirror hH hcard hΓ0 hΓ hA hA0 hU hUW τ hτo hτg hj1 hjm hjU

theorem mirrorOrig_cpy (hU : U ∈ I.mixedFaces g) (v : Fin (𝕋).card) :
    (𝕋).mirrorOrig (I.mixedFaces g) (cpy H Γ A B' hU v) = v := by
  classical
  unfold cpy
  split_ifs with h
  · exact mirrorOrig_copyAt hU _ _ _
  · exact Scheme.mirrorOrig_castAdd _ _ _

/-- **The lift from a mixed face into the full face.**  For a mixed face `U` and a grade `j` with
`1 ≤ j ≤ m + 1` and `j ≤ |U|`, the replicated scheme lifts capped from `(U, j)` to `(univ, j)`. -/
theorem cappedLift_mixed_univ (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (hA0 : ∀ k, A k fun _ ↦ ⊥) (hU : U ∈ I.mixedFaces g) {j : ℕ} (hj1 : 1 ≤ j)
    (hjm : j ≤ m + 1) (hjU : j ≤ #U) :
    (𝔼).rows.CappedLift (X := (U, j)) (Y := ((univ : Finset (Fin (m + 2))), j))
      ⟨subset_univ _, le_rfl⟩ :=
  cappedLift_mixed_face hH hcard hΓ0 hΓ hA hA0 hU (subset_univ _) (Fin.castAdd _)
    (fun v ↦ Scheme.mirrorOrig_castAdd _ _ v)
    (fun v _ hv _ ↦ (Scheme.gradedIndex_mirror_castAdd
      (hmix := I.not_subset_scope_tower g H Γ A B') v).trans hv) hj1 hjm hjU

/-- **The lift between mixed faces at a grade.**  For mixed faces `U ⊆ V` and a grade `j` with
`1 ≤ j ≤ m + 1` and `j ≤ |U|`, the replicated scheme lifts capped from `(U, j)` to `(V, j)`; the
dominating cells are read at their copies at `V`. -/
theorem cappedLift_mixed_mixed (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (hA0 : ∀ k, A k fun _ ↦ ⊥) (hU : U ∈ I.mixedFaces g) {V : Finset (Fin (m + 2))}
    (hV : V ∈ I.mixedFaces g) (hUV : U ⊆ V) {j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m + 1)
    (hjU : j ≤ #U) :
    (𝔼).rows.CappedLift (X := (U, j)) (Y := (V, j)) ⟨hUV, le_rfl⟩ :=
  cappedLift_mixed_face hH hcard hΓ0 hΓ hA hA0 hU hUV (cpy H Γ A B' hV) (mirrorOrig_cpy hV)
    (fun _ _ hv hk ↦ gradedIndex_cpy hV hv (hk.trans (hjU.trans (card_le_card hUV)))) hj1 hjm hjU

end Seed

end VaughtConjecture
