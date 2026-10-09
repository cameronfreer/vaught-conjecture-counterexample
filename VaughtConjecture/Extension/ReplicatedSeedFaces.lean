/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedAttachedLift

/-!
# The donor face and the root at a seed

Roadmap, Layer 3 ((R3) and (R4), the bountifulness of the replicated carrier).

The lemmas of the grade one for the replicated scheme (`Seed.cappedLift_attachment_univ_one`,
`Seed.cappedLift_attached_mixed_one_of_faces`, `Seed.cappedLift_context_one`) ask that the donor
face `D` is a face of the amalgam, that its intersection with the context face `C` (the root) is
a face of the amalgam, and that the root is nonempty.  At a seed whose amalgam has the donor `d` as
its face along the root followed by the new point, with the root a face of the first coatom type
`p`, these hold:

* `Seed.mem_faces_donorFace`: the donor face is a face (from the face map along it);
* `Seed.contextFace_inter_donorFace`: the root is the image of the root of the first coatom
  type, `C ∩ D = univ.map ((g.trans castSuccEmb).trans castSuccEmb)`;
* `Seed.mem_faces_root`: the root is a face (the face map along the composite is the face map of
  the first coatom type along its root, `StageType.restrictFace_trans`);
* `Seed.one_le_card_root`: the root has `n` points, so it is nonempty when `0 < n`.

**Onto roots.**  When the root `g` is onto, the donor face is the second coatom
(`Seed.donorFace_eq_coatom_of_surjective`), so the second coatom is not a mixed face and the
lift from it into the full face is not an instance of `Seed.cappedLift_mixed_univ`.  At the grade
one it holds by the same route as the context lift at the grade one
(`Seed.cappedLift_coatom_one_of_surjective`: the attachment lifts from the donor face into
`(univ, 1)`, the tower does by gluing of rank members, the replicated scheme does from the tower).

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- **The donor face is a face of the amalgam** when the face map along it is defined. -/
theorem mem_faces_donorFace {d : StageType.{u} α (n + 1)}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d) :
    univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces :=
  ((restrictFace_eq_some_iff _ _).mp hd).1

variable (g) in
/-- **The root, as the intersection of the context face and the donor face**, is the image of the
root of the first coatom type. -/
theorem contextFace_inter_donorFace :
    univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
        univ.map (extendByLast (g.trans Fin.castSuccEmb)) =
      univ.map ((g.trans Fin.castSuccEmb).trans Fin.castSuccEmb) := by
  rw [univ_map_extendByLast, show univ.map ((g.trans Fin.castSuccEmb).trans Fin.castSuccEmb) =
    (univ.map (g.trans Fin.castSuccEmb)).map Fin.castSuccEmb from (map_map _ _ _).symm]
  ext x
  rw [mem_inter, mem_insert]
  constructor
  · rintro ⟨hC, rfl | hx⟩
    · exact absurd hC Coatom.last_notMem_univ_map_left
    · exact hx
  · intro hx
    obtain ⟨y, -, rfl⟩ := mem_map.mp hx
    exact ⟨mem_map_of_mem _ (mem_univ y), .inr hx⟩

/-- **The root is a face of the amalgam** when it is a face of the first coatom type. -/
theorem mem_faces_root {p : StageType.{u} α n}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) :
    univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces := by
  rw [contextFace_inter_donorFace]
  have h : restrictFace ((g.trans Fin.castSuccEmb).trans Fin.castSuccEmb) I.amalgam = some p :=
    (restrictFace_trans I.amalgam (Coatom.left m) _ I.restrictFace_left).symm.trans hte
  exact ((restrictFace_eq_some_iff _ _).mp h).1

variable (g) in
/-- **The root has `n` points**, so it is nonempty for a positive arity. -/
theorem one_le_card_root (hn : 0 < n) :
    1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb))) := by
  rw [contextFace_inter_donorFace, card_map, card_univ, Fintype.card_fin]
  exact hn

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
