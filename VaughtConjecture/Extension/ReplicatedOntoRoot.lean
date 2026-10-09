/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedAttachedLift

/-!
# The second coatom at an onto root

Roadmap, Layer 3 ((R3) and (R4), the bountifulness of the replicated carrier).

At the seed position the root `g : Fin n ↪ Fin m` may be onto: calibration gives only `n < m + 1`
(`StageType.GrowthRequests.Calibrated.lt`).  When it is onto, the donor face is the second coatom
(`Seed.donorFace_eq_coatom_of_surjective`), so the second coatom is not a mixed face and the lift
from it into the full face is not an instance of `Seed.cappedLift_mixed_univ` (used by
`Seed.hasMixedCoatomLift`, which asks for a root that is not onto).  At the grade one it holds by
the route of the context lift at the grade one (`Seed.cappedLift_coatom_one_of_surjective`: the
attachment lifts from the donor face into `(univ, 1)`, the tower does by gluing of rank members,
the replicated scheme does from the tower).  Above the grade one it is a lift from a face inside
the donor face (`Seed.cappedLift_donor_univ_attachAdmits` in
`VaughtConjecture.MainTheorem.ReplicatedAssembly`).

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

variable (g) in
/-- **For an onto root the donor face is the second coatom** (the points other than `m`). -/
theorem donorFace_eq_coatom_of_surjective (hg : Function.Surjective g) :
    univ.map (extendByLast (g.trans Fin.castSuccEmb)) = univ.erase (Fin.castSucc (Fin.last m)) := by
  rw [← Coatom.univ_map_right, Coatom.right, univ_map_extendByLast, univ_map_extendByLast,
    ← map_map, map_univ_of_surjective hg]

/-- **The lift from the second coatom at the grade one for an onto root**: the second coatom is
then the donor face, the attachment lifts capped from it into `(univ, 1)`
(`Seed.cappedLift_attachment_univ_one`), the tower does so by gluing of rank members
(`Seed.cappedLift_attachTower_one`), and the replicated scheme does so from the tower
(`Seed.cappedLift_replicated_of_tower`). -/
theorem cappedLift_coatom_one_of_surjective (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) (hg : Function.Surjective g)
    (hdF : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)))) :
    (I.replicated g H Γ A B').rows.CappedLift (X := (univ.erase (Fin.castSucc (Fin.last m)), 1))
      (Y := ((univ : Finset (Fin (m + 2))), 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  set D := univ.map (extendByLast (g.trans Fin.castSuccEmb)) with hD
  have hD1 : 1 ≤ #D := by rw [hD, card_map, card_univ, Fintype.card_fin]; omega
  have hXU : ((D, 1) : Finset (Fin (m + 2)) × ℕ) ≤ ((univ : Finset (Fin (m + 2))), 1) :=
    ⟨subset_univ _, le_rfl⟩
  have hX : ¬ (((univ : Finset (Fin (m + 2))), 1) : Finset (Fin (m + 2)) × ℕ) ≤ (D, 1) :=
    fun h ↦ map_extendByLast_ne_univ g (univ_subset_iff.mp h.1)
  have hl : (I.replicated g H Γ A B').rows.CappedLift hXU :=
    cappedLift_replicated_of_tower hXU rfl (.inr subset_rfl)
      (cappedLift_attachTower_one hH hcard hXU hX
        (cappedLift_attachment_univ_one hdF hrF hr1 hdF hD1 (.inr subset_rfl)))
  have key : ∀ (W : Finset (Fin (m + 2)))
      (h : ((W, 1) : Finset (Fin (m + 2)) × ℕ) ≤ ((univ : Finset (Fin (m + 2))), 1)),
      W = D → (I.replicated g H Γ A B').rows.CappedLift h := by
    rintro W h rfl
    exact hl
  exact key _ _ (donorFace_eq_coatom_of_surjective g hg).symm

end Seed

end VaughtConjecture
