/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderTowerContextLiftRoot
import VaughtConjecture.Extension.ReplicatedWriting
import VaughtConjecture.MainTheorem.ReplicatedInputs
import VaughtConjecture.MainTheorem.SeedJointAdmission

/-!
# The context lift of the replicated scheme: the reduction

Roadmap, Layer 3 ((R3) and (R4), the bountifulness of the replicated carrier).

Let `E` be the replicated scheme of a seed over the attachment (`Seed.replicated`): the ladder
tower over the attachment, with copies of its cells of full scope at the mixed faces.  The context
lift (`Seed.HasContextLift`) asks the capped lifts of `E` from the context coatom
`univ.erase (Fin.last (m + 1))` into the full faces `(univ, j)`, `1 ≤ j ≤ m + 1`.  Below the
context coatom the cells of `E` are cells of the attachment (`Seed.mem_range_attachEmb`); below
`(univ, j)` they are cells of the attachment, cells of full scope of the tower, and copies.

As over the amalgam tower (`VaughtConjecture.Extension.LadderTowerContextLift`), the lift is
reduced to two statements:

* **the state lift** (`Seed.ContextStateLiftR j`): a complete lawful state of the attachment
  satisfying `A (m + 2)`, equal to the prescription on the context cells below the grade, with the
  observation of the ambient at the cap on the cells of the attachment below the grade;
* **the coding of states** (`Seed.StateCodingR j`): such a state is the decoded reading of a state
  of the catalogue below the grade, and the decoded writing in `E`
  (`Seed.replicatedWriting`, every copy reading its original) has the observation of the ambient
  at the cap at every cell below `(univ, j)`, the copies included.  The decoder sends no positive
  label to `⊥` when the cap is `⊥`; at a positive cap it may (`Seed.not_writingLift_univ`: the
  writing is positive at the first rung of its member, where the ambient may be `⊥`), the ambient
  being the lawful companion (`CellScheme.Rows.IsLawfulBelow.map_of_min_eq`).

**The reduction** (`Seed.cappedLift_context_replicated_of_stateLift`,
`Seed.hasContextLift_of_stateLift`).

## References

Bountifulness is [Kni26, Definition 2.5.14]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- The context coatom is the image of the first points. -/
theorem map_castSuccEmb_eq_ctxCoatom :
    univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) = ctxCoatom m :=
  Coatom.univ_map_left

/-- **The cells of the replicated scheme below the context coatom are cells of the attachment.** -/
theorem exists_attachEmb_eq_of_mem_below_ctx {j : ℕ} {z : Fin (I.replicated g H Γ A B').card}
    (hz : z ∈ (I.replicated g H Γ A B').toCellScheme.below (ctxCoatom m, j)) :
    ∃ a, I.attachEmb g H Γ A B' a = z := by
  have h := mem_range_attachEmb (I := I) (g := g) (H := H) (Γ := Γ) (A := A) (B' := B') z
    (.inl (map_castSuccEmb_eq_ctxCoatom ▸ (hz.1 : _ ⊆ ctxCoatom m)))
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha⟩

/-- A cell of the attachment lies below a pair in the replicated scheme exactly when it does in
the attachment. -/
theorem attachEmb_mem_below_iff (a : Fin (I.attachment g).card) (X : Finset (Fin (m + 2)) × ℕ) :
    I.attachEmb g H Γ A B' a ∈ (I.replicated g H Γ A B').toCellScheme.below X ↔
      a ∈ (I.attachment g).toCellScheme.below X := by
  change (I.replicated g H Γ A B').toCellScheme.gradedIndex _ ≤ X ↔
    (I.attachment g).toCellScheme.gradedIndex a ≤ X
  rw [gradedIndex_attachEmb]

variable (I g H Γ A B') in
/-- **The state lift from the context coatom at the grade `j`** over the replicated scheme. -/
def ContextStateLiftR (j : ℕ) : Prop :=
  ∀ c : Label.{u}, IsSelfVisible j c →
    ∀ (p : (I.replicated g H Γ A B').toCellScheme.below (ctxCoatom m, j) → Label.{u})
      (q : (I.replicated g H Γ A B').toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j) → Label.{u}),
      (I.replicated g H Γ A B').rows.IsLawfulBelow (ctxCoatom m, j) p →
      (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q →
      (∀ d, min (q (Set.inclusion (CellScheme.below_mono _ (ctxCoatom_le j)) d)) c =
        min (p d) c) →
      ∃ P : Fin (I.attachment g).card → Label.{u}, (I.attachment g).rows.IsLawful P ∧
        A (m + 2) P ∧
        (∀ (d : (I.replicated g H Γ A B').toCellScheme.below (ctxCoatom m, j)) a,
          I.attachEmb g H Γ A B' a = d.1 → P a = p d) ∧
        ∀ (d : (I.replicated g H Γ A B').toCellScheme.below
          ((univ : Finset (Fin (m + 2))), j)) a,
          I.attachEmb g H Γ A B' a = d.1 → min (P a) c = min (q d) c

variable (I g H Γ A B') in
/-- **The coding of states at the grade `j`** over the replicated scheme: every complete lawful
state of the attachment satisfying `A (m + 2)`, with the observation at a cap `c` of an ambient
`q` on the cells of the attachment below the grade, is the decoded reading below the grade of a
state of the catalogue, by a witness bounded by `j` sending no positive label to `⊥` when `c = ⊥`;
and its decoded writing has the observation of `q` at `c` at every cell below `(univ, j)`, the
cells of full scope and the copies included. -/
def StateCodingR (j : ℕ) : Prop :=
  ∀ c : Label.{u}, IsSelfVisible j c →
    ∀ (q : (I.replicated g H Γ A B').toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j) → Label.{u}),
      (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q →
      ∀ P : Fin (I.attachment g).card → Label.{u}, (I.attachment g).rows.IsLawful P →
      A (m + 2) P →
      (∀ (d : (I.replicated g H Γ A B').toCellScheme.below
          ((univ : Finset (Fin (m + 2))), j)) a,
        I.attachEmb g H Γ A B' a = d.1 → min (P a) c = min (q d) c) →
      ∃ R ∈ (I.attachmentBase g).towerCat Γ A (m + 2), ∃ ν : Label.{u} → Label.{u},
        IsWitness (stepSuppressor j) ν ∧ (c ≠ ⊥ ∨ ∀ x, ν x = ⊥ → x = ⊥) ∧
        (∀ a, (I.attachment g).toCellScheme.grade a ≤ j → ν (R a) = P a) ∧
        ∀ d : (I.replicated g H Γ A B').toCellScheme.below
          ((univ : Finset (Fin (m + 2))), j),
          min (ν (I.replicatedWriting g H Γ A B' R d)) c = min (q d) c

/-- **The context lift at the grade `j` from the state lift and the coding of states**: the
decoded writing of the coded state is lawful below `(univ, j)` (through the ambient at a positive
cap, by bottom reflection at the cap `⊥`), reads the prescription on the context cells, and keeps
the observation of the ambient at the cap. -/
theorem cappedLift_context_replicated_of_stateLift (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hA : ∀ k R, A (k + 3) R → A (k + 2) R) {j : ℕ} (hS : ContextStateLiftR I g H Γ A B' j)
    (hC : StateCodingR I g H Γ A B' j) :
    (I.replicated g H Γ A B').rows.CappedLift (X := (univ.erase (Fin.last (m + 1)), j))
      (Y := ((univ : Finset (Fin (m + 2))), j)) ⟨erase_subset _ _, le_rfl⟩ := by
  refine (Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨P, hPl, hPA, hPp, hPq⟩ := hS c hc p q hp hq hpq
  obtain ⟨R, hR, ν, hν, hbot, hνR, hνq⟩ := hC c hc q hq P hPl hPA hPq
  have hRl : (I.attachment g).rows.IsLawful R :=
    (Scheme.LadderBaseData.mem_towerCat.mp hR).2.1
  have hlaw : (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
      fun d ↦ ν (I.replicatedWriting g H Γ A B' R d) := by
    rcases hbot with hc0 | hbot
    · exact ((isLawful_replicatedWriting hH hcard hΓ hA hR).isLawfulBelow _).map_of_min_eq hq
        (fun d ↦ d.2.2) hν hc0 hνq
    · exact isLawfulBelow_map_replicatedWriting hH hcard hΓ hA hR _ hν hbot
  refine ⟨fun d ↦ ν (I.replicatedWriting g H Γ A B' R d), hlaw, hνq, fun d ↦ ?_⟩
  obtain ⟨a, ha⟩ := exists_attachEmb_eq_of_mem_below_ctx d.2
  have hag : (I.attachment g).toCellScheme.grade a ≤ j :=
    ((attachEmb_mem_below_iff (H := H) (Γ := Γ) (A := A) (B' := B') a (ctxCoatom m, j)).mp
      (ha ▸ d.2)).2
  change ν (I.replicatedWriting g H Γ A B' R d.1) = p d
  rw [← ha, replicatedWriting_attachEmb hcard hRl, hνR a hag]
  exact hPp d a ha

/-- **The context lift from the state lift and the coding of states** at every grade
`1, …, m + 1`. -/
theorem hasContextLift_of_stateLift (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (h : ∀ j, 1 ≤ j → j ≤ m + 1 →
      ContextStateLiftR I g H Γ A B' j ∧ StateCodingR I g H Γ A B' j) :
    I.HasContextLift g H Γ A B' := fun j hj hjm ↦
  cappedLift_context_replicated_of_stateLift hH hcard hΓ hA (h j hj hjm).1 (h j hj hjm).2

end Seed

end VaughtConjecture
