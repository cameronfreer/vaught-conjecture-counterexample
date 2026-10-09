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
  at the cap at every cell below `(univ, j)`, the copies included.  The decoded writing need only
  have the bottom pattern of some section lawful below `(univ, j)` (a lawful companion,
  `CellScheme.Rows.IsLawfulBelow.map_of_bot_iff`): the decoder may send positive labels to `⊥`.

**The reduction** (`Seed.cappedLift_context_replicated_of_stateLift`,
`Seed.hasContextLift_of_stateLift`).

**The bottom-reflecting form is false** (`Seed.not_stateCodingReflecting`, `j ≥ 1`): at the cap
`⊤`, the bottom ambient and the bottom state, the writing of a lawful state is positive at the
first rung of its member, so a decoder sending no positive label to `⊥` cannot match the ambient.
At a positive cap the ambient itself is a lawful companion, and with bottom reflection the writing
is (`Seed.stateCodingR_of_capOrReflect`).

**The copies impose nothing beyond their originals** (`Seed.stateCodingR_of_tower`): every cell
below `(univ, j)` has its original, a cell of the tower, below `(univ, j)` with a scope containing
its own (`Seed.exists_orig_mem_below_univ`); in every lawful section the two carry the same label
(`Scheme.eq_of_mirrorOrig_eq`), and the writing reads the copy at its original.  So the capped
agreement is asked only at the cells of the tower.

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
state of the catalogue, by a witness bounded by `j` whose decoded writing has the bottom pattern of
some section lawful below `(univ, j)` (a lawful companion,
`CellScheme.Rows.IsLawfulBelow.map_of_bot_iff`); and its decoded writing has the observation of `q`
at `c` at every cell below `(univ, j)`, the cells of full scope and the copies included.  The
decoder may send positive labels to `⊥` where the companion is `⊥`. -/
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
        IsWitness (stepSuppressor j) ν ∧
        (∃ r : (I.replicated g H Γ A B').toCellScheme.below
            ((univ : Finset (Fin (m + 2))), j) → Label.{u},
          (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) r ∧
          ∀ d : (I.replicated g H Γ A B').toCellScheme.below
            ((univ : Finset (Fin (m + 2))), j),
            ν (I.replicatedWriting g H Γ A B' R d) = ⊥ ↔ r d = ⊥) ∧
        (∀ a, (I.attachment g).toCellScheme.grade a ≤ j → ν (R a) = P a) ∧
        ∀ d : (I.replicated g H Γ A B').toCellScheme.below
          ((univ : Finset (Fin (m + 2))), j),
          min (ν (I.replicatedWriting g H Γ A B' R d)) c = min (q d) c

variable (I g H Γ A B') in
/-- **The coding of states with a bottom-reflecting decoder** (the form refuted by
`Seed.not_stateCodingReflecting`): as `Seed.StateCodingR`, with a decoder sending no positive
label to `⊥` at every cap. -/
def StateCodingReflecting (j : ℕ) : Prop :=
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
        IsWitness (stepSuppressor j) ν ∧ (∀ x, ν x = ⊥ → x = ⊥) ∧
        (∀ a, (I.attachment g).toCellScheme.grade a ≤ j → ν (R a) = P a) ∧
        ∀ d : (I.replicated g H Γ A B').toCellScheme.below
          ((univ : Finset (Fin (m + 2))), j),
          min (ν (I.replicatedWriting g H Γ A B' R d)) c = min (q d) c

/-- **The coding of states with a bottom-reflecting decoder fails** at every grade `j ≥ 1`, when
the bottom state satisfies the catalogue predicate: at the cap `⊤` with the bottom ambient and the
bottom state, the decoded writing must be `⊥` below `(univ, j)`, but the writing of a lawful state
is positive at the first rung of its member (`Seed.ladderTower_v_rung_ne_bot`) and the decoder
keeps it positive.  The same instance as `Seed.not_writingLift_univ`. -/
theorem not_stateCodingReflecting (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hA0 : A (m + 2) fun _ ↦ ⊥) {j : ℕ} (hj : 1 ≤ j) :
    ¬ StateCodingReflecting I g H Γ A B' j := by
  intro hS
  obtain ⟨R, hR, ν, -, hbot, -, hνq⟩ := hS ⊤ (isSelfVisible_top j) (fun _ ↦ ⊥)
    (Rows.isLawfulBelow_const_bot _) (fun _ ↦ ⊥) Rows.isLawful_const_bot hA0 fun _ _ _ ↦ rfl
  have hRl : (I.attachment g).rows.IsLawful R := (Scheme.LadderBaseData.mem_towerCat.mp hR).2.1
  let t : Fin (I.attachTower g H Γ A B').card := (I.attachmentBase g).towerEmb m
    (Fin.natAdd _ (Scheme.ladderEquiv _ _ H
      (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hRl, Sum.inl ⟨0, hH⟩)))
  have hgt : (I.replicated g H Γ A B').toCellScheme.gradedIndex (Fin.castAdd _ t) =
      ((univ : Finset (Fin (m + 2))), 1) := by
    refine (Scheme.gradedIndex_mirror_castAdd _).trans ?_
    refine (Scheme.gradedIndex_layerTowerEmb (B := (I.attachmentBase g).towerBase H)
      (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ grid k B') _ m).trans ?_
    change ((I.attachmentBase g).S.appendFullCellsScheme 1 _).gradedIndex (Fin.natAdd _ _) = _
    exact Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _
  have hmem : Fin.castAdd _ t ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) := by
    rw [CellScheme.mem_below, hgt]
    exact ⟨subset_rfl, hj⟩
  have h := hνq ⟨_, hmem⟩
  simp only [min_top_right] at h
  apply ladderTower_v_rung_ne_bot (Γ := Γ) (A := A) (B' := B') hcard hH hRl
  apply hbot
  change ν (((I.attachmentBase g).ladderTower H Γ A B' m).v R
    ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (Fin.castAdd _ t))) = ⊥ at h
  rwa [Scheme.mirrorOrig_castAdd] at h

/-- **The coding with a decoder that sends no positive label to `⊥` at the cap `⊥`, and any
decoder at a positive cap, is a coding of states**: at a positive cap the ambient is a lawful
companion with the bottom pattern of the decoded writing; with bottom reflection the writing is. -/
theorem stateCodingR_of_capOrReflect (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R) {j : ℕ}
    (h : ∀ c : Label.{u}, IsSelfVisible j c →
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
            min (ν (I.replicatedWriting g H Γ A B' R d)) c = min (q d) c) :
    StateCodingR I g H Γ A B' j := by
  intro c hc q hq P hP hPA hPq
  obtain ⟨R, hR, ν, hν, hbot, hνR, hνq⟩ := h c hc q hq P hP hPA hPq
  refine ⟨R, hR, ν, hν, ?_, hνR, hνq⟩
  rcases hbot with hc0 | hbot
  · exact ⟨q, hq, fun d ↦ eq_bot_iff_of_min_eq (hνq d) hc0⟩
  · exact ⟨fun d ↦ I.replicatedWriting g H Γ A B' R d,
      (isLawful_replicatedWriting hH hcard hΓ hA hR).isLawfulBelow _,
      fun d ↦ ⟨hbot _, fun h0 ↦ by
        change I.replicatedWriting g H Γ A B' R d.1 = ⊥ at h0
        rw [h0, hν.map_bot]⟩⟩

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
  obtain ⟨R, hR, ν, hν, ⟨r, hr, hbot⟩, hνR, hνq⟩ := hC c hc q hq P hPl hPA hPq
  have hRl : (I.attachment g).rows.IsLawful R :=
    (Scheme.LadderBaseData.mem_towerCat.mp hR).2.1
  have hlaw : (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
      fun d ↦ ν (I.replicatedWriting g H Γ A B' R d) :=
    ((isLawful_replicatedWriting hH hcard hΓ hA hR).isLawfulBelow _).map_of_bot_iff hr
      (fun d ↦ d.2.2) hν hbot
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

/-! ### The copies impose nothing beyond their originals -/

/-- **Every cell below `(univ, j)` has its original below `(univ, j)`**, a cell of the tower whose
scope contains its own. -/
theorem exists_orig_mem_below_univ {j : ℕ} {z : Fin (I.replicated g H Γ A B').card}
    (hz : z ∈ (I.replicated g H Γ A B').toCellScheme.below ((univ : Finset (Fin (m + 2))), j)) :
    Fin.castAdd _ ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) z) ∈
        (I.replicated g H Γ A B').toCellScheme.below ((univ : Finset (Fin (m + 2))), j) ∧
      (I.replicated g H Γ A B').toCellScheme.scope z ⊆ (I.replicated g H Γ A B').toCellScheme.scope
        (Fin.castAdd _ ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) z)) := by
  have horig : (I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) z =
      (I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g)
        (Fin.castAdd _ ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) z)) :=
    (Scheme.mirrorOrig_castAdd _ _ _).symm
  have hg := Scheme.grade_mirror_eq_of_orig (hmix := I.not_subset_scope_tower g H Γ A B') horig
  induction z using Fin.addCases with
  | left c =>
    rw [Scheme.mirrorOrig_castAdd]
    exact ⟨hz, subset_rfl⟩
  | right k =>
    have hsc : (I.replicated g H Γ A B').toCellScheme.scope
        (Fin.castAdd _ ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g)
          (Fin.natAdd _ k))) = univ := by
      refine (congrArg Prod.fst (Scheme.gradedIndex_mirror_castAdd
        (hmix := I.not_subset_scope_tower g H Γ A B') _)).trans ?_
      rw [Scheme.mirrorOrig_natAdd]
      exact (((I.attachTower g H Γ A B').copyEquiv (I.mixedFaces g)).symm k).2.2.1
    refine ⟨⟨subset_univ _, ?_⟩, by rw [hsc]; exact subset_univ _⟩
    exact (hg.symm.trans_le hz.2 :)

/-- **The coding of states at the cells of the tower suffices**: the capped agreement of the
decoded writing with the ambient at the cells of the tower below `(univ, j)` gives it at every cell
below `(univ, j)`, every copy reading its original and carrying its original's label in every
lawful section (`Scheme.eq_of_mirrorOrig_eq`). -/
theorem stateCodingR_of_tower {j : ℕ}
    (h : ∀ c : Label.{u}, IsSelfVisible j c →
      ∀ (q : (I.replicated g H Γ A B').toCellScheme.below
          ((univ : Finset (Fin (m + 2))), j) → Label.{u}),
        (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q →
        ∀ P : Fin (I.attachment g).card → Label.{u}, (I.attachment g).rows.IsLawful P →
        A (m + 2) P →
        (∀ (d : (I.replicated g H Γ A B').toCellScheme.below
            ((univ : Finset (Fin (m + 2))), j)) a,
          I.attachEmb g H Γ A B' a = d.1 → min (P a) c = min (q d) c) →
        ∃ R ∈ (I.attachmentBase g).towerCat Γ A (m + 2), ∃ ν : Label.{u} → Label.{u},
          IsWitness (stepSuppressor j) ν ∧
          (∃ r : (I.replicated g H Γ A B').toCellScheme.below
              ((univ : Finset (Fin (m + 2))), j) → Label.{u},
            (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) r ∧
            ∀ d : (I.replicated g H Γ A B').toCellScheme.below
              ((univ : Finset (Fin (m + 2))), j),
              ν (I.replicatedWriting g H Γ A B' R d) = ⊥ ↔ r d = ⊥) ∧
          (∀ a, (I.attachment g).toCellScheme.grade a ≤ j → ν (R a) = P a) ∧
          ∀ (t : Fin (I.attachTower g H Γ A B').card)
            (ht : Fin.castAdd _ t ∈ (I.replicated g H Γ A B').toCellScheme.below
              ((univ : Finset (Fin (m + 2))), j)),
            min (ν (I.replicatedWriting g H Γ A B' R (Fin.castAdd _ t))) c =
              min (q ⟨_, ht⟩) c) :
    StateCodingR I g H Γ A B' j := by
  classical
  intro c hc q hq P hP hPA hPq
  obtain ⟨R, hR, ν, hν, hr, hνR, hνq⟩ := h c hc q hq P hP hPA hPq
  refine ⟨R, hR, ν, hν, hr, hνR, fun d ↦ ?_⟩
  obtain ⟨hmem, hsc⟩ := exists_orig_mem_below_univ d.2
  have hq' := Rows.isLawfulBelow_iff.mp hq
  have hqd : q d = q ⟨_, hmem⟩ := by
    have hw : (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
        fun e ↦ (fun z ↦ if hz : z ∈ (I.replicated g H Γ A B').toCellScheme.below
          ((univ : Finset (Fin (m + 2))), j) then q ⟨z, hz⟩ else ⊥) e := by
      convert hq using 1
      funext e
      simp only [e.2, dite_true]
    have := Scheme.eq_of_mirrorOrig_eq (w := fun z ↦ if hz : z ∈
      (I.replicated g H Γ A B').toCellScheme.below ((univ : Finset (Fin (m + 2))), j)
        then q ⟨z, hz⟩ else ⊥) hw (d₁ := d.1) (Scheme.mirrorOrig_castAdd _ _ _).symm hsc
      hmem
    simpa only [d.2, hmem, dite_true] using this
  have hwd : I.replicatedWriting g H Γ A B' R d =
      I.replicatedWriting g H Γ A B' R (Fin.castAdd _
        ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) d)) := by
    change ((I.attachmentBase g).ladderTower H Γ A B' m).v R _ =
      ((I.attachmentBase g).ladderTower H Γ A B' m).v R _
    rw [Scheme.mirrorOrig_castAdd]
  rw [hwd, hqd]
  exact hνq _ hmem

end Seed

end VaughtConjecture
