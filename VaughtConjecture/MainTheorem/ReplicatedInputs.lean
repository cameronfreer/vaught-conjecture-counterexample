/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLadderCarrier
import VaughtConjecture.MainTheorem.SeedLadderInputs
import VaughtConjecture.Extension.ReplicatedMixedLift
import VaughtConjecture.Extension.ReplicatedAttachedLift

/-!
# Ladder carriers at the seed position from the inputs of the replicated scheme

Roadmap, Layer 3 ((R3) and (R4), the assembly of the recognizing growth carrier).

The **inputs of the replicated scheme** at a seed for requests `Q` (`Seed.ReplicatedInputs`): a
height, a finite set of values containing `⊥` and a grid bound, and, for the replicated scheme over
the attachment with the admission predicate of `Q`,

* the capped lifts into the mixed faces (`Seed.HasMixedLifts`, open).  They factor through the
  same grade (`Seed.hasMixedLifts_of_sameGrade`); the same-grade lifts between mixed faces hold
  (`Seed.hasMixedSameGradeLifts`), so what remains are the same-grade lifts from the faces inside
  the context face or the donor face (`Seed.HasAttachedMixedLifts`, open above the grade one; at
  the grade one they hold when the donor face and the root are faces of the amalgam,
  `Seed.attachedMixedLifts_one`),
* the capped lifts from the two coatoms into the full faces of the grades `1, …, m + 1`: the
  context lift (`Seed.HasContextLift`, open) and the mixed-coatom lift
  (`Seed.HasMixedCoatomLift`; when the root is not onto the second coatom is a mixed face
  (`Seed.mem_mixedFaces_coatom`) and the lift holds, `Seed.hasMixedCoatomLift`, by the lift from a
  mixed face into the full face `Seed.cappedLift_mixed_univ`),
* a lawful labelling extending the labels of the attachment (`Seed.HasExtendingLabel`): a
  mathematical hypothesis on the replicated scheme, not a step of the assembly; it follows from a
  lawful labelling of the ladder tower extending them (`Seed.hasExtendingLabel_of_tower`, the
  copies reading the labels of their originals), and it holds for the admission predicate of
  requests calibrated on the class with the labels pair admitted, once the values contain the
  compressed labels of the attachment (`Seed.hasExtendingLabel_attachAdmits` in
  `VaughtConjecture.MainTheorem.ReplicatedLabel`: the block expansion of the writing of the
  compressed labels).

The inputs are kept separate: the lifts into the mixed faces, the coatom lifts (the context lift,
whose target below the full face contains the copies, and the mixed-coatom lift), and the extending
lawful labelling.

From them the ladder carrier exists (`Seed.exists_ladderCarrier_of_replicatedInputs`: the
replicated scheme is bountiful by `Seed.isBountiful_replicated_of_lifts`, and
`Seed.exists_replicatedCarrier` assembles the completion).  Below a pair whose face lies in the
context face or the donor face no lift is asked: there the replicated scheme is the amalgam.

**At the seed position** the inputs at some seed of the context
(`StageType.HasReplicatedInputsAtSeed`, open) give ladder carriers
(`StageType.HasReplicatedInputsAtSeed.hasLadderGrowthCarriersStableAtSeed`).  Of the hypotheses
of the contract the implication itself uses exactly: the stage is a limit (`Order.IsSuccLimit α`,
for the completion at a stage that is zero or a limit), and the threshold of the requests is at
least `2`, from `ClassCalibrated.arity` (`n + 1 ≤` the threshold) together with the positive arity
of the root (`0 < n`).  Every other hypothesis is handed to the inputs at the seed.  No exactness,
no root cleanness, no bound on the donor's top grade.

The inputs of the replicated scheme over the height-set tower stay open; the contract itself is
proved by the levels re-rendered per grade (`StageType.hasLadderGrowthCarriersStableAtSeed_levels`,
not yet reviewed).

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m) (H : ℕ)
  (Γ : Finset Label.{u}) (A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop) (B' : ℕ)

/-- **The lifts into the mixed faces** (open): the replicated scheme lifts capped between any two
graded faces whose upper face is mixed. -/
def HasMixedLifts : Prop :=
  ∀ ⦃X Y : Finset (Fin (m + 2)) × ℕ⦄, X ∈ (I.replicated g H Γ A B').toCellScheme.gradedFaces →
    Y ∈ (I.replicated g H Γ A B').toCellScheme.gradedFaces → ∀ h : X ≤ Y,
    Y.1 ∈ I.mixedFaces g → (I.replicated g H Γ A B').rows.CappedLift h

/-- **The same-grade lifts between mixed faces**: the replicated scheme lifts capped from `(V, k)`
to `(U, k)` for mixed faces `V ⊆ U` and `1 ≤ k ≤ |V|` (they hold, `Seed.hasMixedSameGradeLifts`). -/
def HasMixedSameGradeLifts : Prop :=
  ∀ ⦃V U : Finset (Fin (m + 2))⦄ ⦃k : ℕ⦄, V ∈ I.mixedFaces g → U ∈ I.mixedFaces g →
    ∀ h : V ⊆ U, 1 ≤ k → k ≤ #V →
      (I.replicated g H Γ A B').rows.CappedLift (X := (V, k)) (Y := (U, k)) ⟨h, le_rfl⟩

/-- **The same-grade lifts from the faces of the attachment into the mixed faces** (open above
the grade one): the replicated scheme lifts capped from `(V, k)` to `(U, k)` for a face `V`
inside the context face or the donor face, a mixed face `U ⊇ V`, and `1 ≤ k ≤ |V|`.  Below
`(V, k)` lie only cells of the attachment; below `(U, k)` lie also the copies at the mixed faces
inside `U`, whose labels must extend the prescription. -/
def HasAttachedMixedLifts : Prop :=
  ∀ ⦃V U : Finset (Fin (m + 2))⦄ ⦃k : ℕ⦄, V ∈ (I.replicated g H Γ A B').toCellScheme.faces →
    (V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      V ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))) →
    U ∈ I.mixedFaces g → ∀ h : V ⊆ U, 1 ≤ k → k ≤ #V →
      (I.replicated g H Γ A B').rows.CappedLift (X := (V, k)) (Y := (U, k)) ⟨h, le_rfl⟩

/-- **The context lift** (open): the replicated scheme lifts capped from the context coatom (the
points other than the new one) into the full face at every grade `1, …, m + 1`.  Below the context
coatom lie only cells of the context; below the full face lie also the cells of full scope and
their copies at the mixed faces, which the lift must label. -/
def HasContextLift : Prop :=
  ∀ j, 1 ≤ j → j ≤ m + 1 →
    (I.replicated g H Γ A B').rows.CappedLift (X := (univ.erase (Fin.last (m + 1)), j))
      (Y := ((univ : Finset (Fin (m + 2))), j)) ⟨erase_subset _ _, le_rfl⟩

/-- **The mixed-coatom lift** (open): the replicated scheme lifts capped from the second coatom
(the points other than `m`) into the full face at every grade `1, …, m + 1`.  When the root is not
onto, the second coatom is a mixed face, carrying copies of the cells of full scope. -/
def HasMixedCoatomLift : Prop :=
  ∀ j, 1 ≤ j → j ≤ m + 1 →
    (I.replicated g H Γ A B').rows.CappedLift (X := (univ.erase (Fin.castSucc (Fin.last m)), j))
      (Y := ((univ : Finset (Fin (m + 2))), j)) ⟨erase_subset _ _, le_rfl⟩

/-- **The coatom lifts**: the context lift and the mixed-coatom lift. -/
def HasCoatomLifts : Prop :=
  ∀ x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))),
    ∀ j, 1 ≤ j → j ≤ m + 1 →
      (I.replicated g H Γ A B').rows.CappedLift (X := (univ.erase x, j))
        (Y := ((univ : Finset (Fin (m + 2))), j)) ⟨erase_subset _ _, le_rfl⟩

variable {I g H Γ A B'} in
theorem hasCoatomLifts_of_lifts (hc : I.HasContextLift g H Γ A B')
    (hm : I.HasMixedCoatomLift g H Γ A B') : I.HasCoatomLifts g H Γ A B' := by
  intro x hx
  rcases mem_insert.mp hx with rfl | hx
  · exact hc
  · rw [mem_singleton.mp hx]
    exact hm

/-- **A labelling extending the labels of the attachment**: a lawful section of the replicated
scheme that is the labelling of the attachment on its cells.  For the admission predicate of
calibrated requests it holds (`Seed.hasExtendingLabel_attachAdmits`). -/
def HasExtendingLabel : Prop :=
  ∃ q : Fin (I.replicated g H Γ A B').card → Label.{u},
    (I.replicated g H Γ A B').rows.IsLawful q ∧
      ∀ c, q (I.attachEmb g H Γ A B' c) = (I.attachmentType g).label c

variable {I g H Γ A B'}

/-- **A labelling of the replicated scheme from one of the tower**: a lawful labelling of the
ladder tower over the attachment extending the labels of the attachment, read through the
originals, is a lawful labelling of the replicated scheme extending them (the mirroring being
saturated). -/
theorem hasExtendingLabel_of_tower {qT : Fin (I.attachTower g H Γ A B').card → Label.{u}}
    (hqT : (I.attachTower g H Γ A B').rows.IsLawful qT)
    (hqe : ∀ c, qT ((I.attachmentBase g).baseCellEmb m c) = (I.attachmentType g).label c) :
    I.HasExtendingLabel g H Γ A B' :=
  ⟨fun z ↦ qT ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) z),
    (Scheme.mirrorData (I.not_subset_scope_tower g H Γ A B')).isLawful_comp hqT
      (Scheme.saturated_mirrorData _),
    fun c ↦ by
      change qT ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (Fin.castAdd _ _)) = _
      rw [Scheme.mirrorOrig_castAdd]
      exact hqe c⟩

/-- **The mixed-coatom lift holds when the root is not onto** (`Seed.cappedLift_mixed_univ` at the
second coatom, a mixed face of size `m + 1`). -/
theorem hasMixedCoatomLift (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (hA0 : ∀ k, A k fun _ ↦ ⊥) (hg : ¬ Function.Surjective g) :
    I.HasMixedCoatomLift g H Γ A B' := fun j hj1 hjm ↦
  cappedLift_mixed_univ hH hcard hΓ0 hΓ hA hA0 (mem_mixedFaces_coatom hg) hj1 hjm
    (by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega)

/-- **The lifts into the mixed faces factor through the same grade**: a lift from `(V, k)` to
`(U, k')` with `U` mixed is the same-grade lift from `(V, k)` to `(U, k)` followed by the raise of
the grade within `U` (`CellScheme.Rows.cappedLift_of_fst_eq`); the face `V` is mixed or, being a
face other than the ground set and not mixed, lies inside the context face or the donor face. -/
theorem hasMixedLifts_of_sameGrade (hmm : I.HasMixedSameGradeLifts g H Γ A B')
    (hat : I.HasAttachedMixedLifts g H Γ A B') : I.HasMixedLifts g H Γ A B' := by
  rintro ⟨V, k⟩ ⟨U, k'⟩ hX - h hU
  have hsame : (I.replicated g H Γ A B').rows.CappedLift (X := (V, k)) (Y := (U, k))
      ⟨h.1, le_rfl⟩ := by
    by_cases hVm : V ∈ I.mixedFaces g
    · exact hmm hVm hU h.1 hX.2.1 hX.2.2
    · have hVu : V ≠ univ := fun he ↦
        ((I.mem_mixedFaces g).mp hU).2.1 (univ_subset_iff.mp (he ▸ h.1))
      have hc : V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
          V ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb)) := by
        by_contra hc
        push Not at hc
        exact hVm ((I.mem_mixedFaces g).mpr ⟨faces_replicated ▸ hX.1, hVu, hc.1, hc.2⟩)
      exact hat hX.1 hc hU h.1 hX.2.1 hX.2.2
  exact hsame.trans (CellScheme.Rows.cappedLift_of_fst_eq (R := (I.replicated g H Γ A B').rows)
    (X := (U, k)) (Y := (U, k')) ⟨subset_rfl, h.2⟩ rfl)

/-- **The same-grade lifts between mixed faces hold** (`Seed.cappedLift_mixed_mixed`). -/
theorem hasMixedSameGradeLifts (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (hA0 : ∀ k, A k fun _ ↦ ⊥) : I.HasMixedSameGradeLifts g H Γ A B' :=
  fun V _ k hV hU h hk1 hkV ↦ by
    have hVu : #V < m + 2 := by
      have hlt : V ⊂ univ := ssubset_univ_iff.mpr ((I.mem_mixedFaces g).mp hV).2.1
      simpa using card_lt_card hlt
    exact cappedLift_mixed_mixed hH hcard hΓ0 hΓ hA hA0 hV hU h hk1 (by omega) hkV

/-- **The lifts into the mixed faces from the lifts out of the faces of the attachment**: the
same-grade lifts between mixed faces hold, so the lifts into the mixed faces are exactly asked
from the faces inside the context face or the donor face. -/
theorem hasMixedLifts_of_attachedMixedLifts (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hA : ∀ k R, A (k + 3) R → A (k + 2) R) (hA0 : ∀ k, A k fun _ ↦ ⊥)
    (hat : I.HasAttachedMixedLifts g H Γ A B') : I.HasMixedLifts g H Γ A B' :=
  hasMixedLifts_of_sameGrade (hasMixedSameGradeLifts hH hcard hΓ0 hΓ hA hA0) hat

/-- **The same-grade lifts from the faces of the attachment at the grade one**, when the donor
face and the root (its intersection with the context face) are faces of the amalgam and the root
is nonempty (`Seed.cappedLift_attached_mixed_one_of_faces`). -/
theorem attachedMixedLifts_one (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (hdF : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb))))
    {V U : Finset (Fin (m + 2))} (hVF : V ∈ (I.replicated g H Γ A B').toCellScheme.faces)
    (hV : V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      V ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb)))
    (hU : U ∈ I.mixedFaces g) (h : V ⊆ U) (hV1 : 1 ≤ #V) :
    (I.replicated g H Γ A B').rows.CappedLift (X := (V, 1)) (Y := (U, 1)) ⟨h, le_rfl⟩ :=
  cappedLift_attached_mixed_one_of_faces hH hcard hΓ hA hdF hrF hr1 hU
    (faces_replicated ▸ hVF) hV1 h hV

variable (I g) {d : StageType.{u} α (n + 1)}
  (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)

/-- **The inputs of the replicated scheme** at a seed for requests `Q` (open): a height `H`, a
finite set `Γ` of values and a grid bound `B'`, and, for the replicated scheme with the admission
predicate of `Q`, the lifts into the mixed faces, the coatom lifts, and a labelling extending the
labels of the attachment. -/
def ReplicatedInputs (Q : GrowthRequests I.left d.toScheme) : Prop :=
  ∃ (H : ℕ) (Γ : Finset Label.{u}) (B' : ℕ), 0 < H ∧ (I.attachment g).card ≤ H ∧ ⊥ ∈ Γ ∧
    (∀ x ∈ Γ, x ≤ gridPoint 2 B') ∧
    (∀ x ∈ Γ, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})) ∧
    I.HasMixedLifts g H Γ (I.attachAdmits g hd Q) B' ∧
    I.HasContextLift g H Γ (I.attachAdmits g hd Q) B' ∧
    I.HasMixedCoatomLift g H Γ (I.attachAdmits g hd Q) B' ∧
    I.HasExtendingLabel g H Γ (I.attachAdmits g hd Q) B'

variable {I g}

/-- **The ladder carrier from the inputs of the replicated scheme.** -/
theorem exists_ladderCarrier_of_replicatedInputs (hα : Order.IsSuccPrelimit α)
    (Q : GrowthRequests I.left d.toScheme) (hN : 2 ≤ Q.threshold)
    (h : I.ReplicatedInputs g hd Q) :
    ∃ G : GrowthCarrier I.left.toScheme d.toScheme (g.trans Fin.castSuccEmb),
      (∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold)) ∧
      ∃ (Mb : Type) (H : ℕ) (r : Mb → ℕ → Fin G.scheme.card), 0 < H ∧
        (∀ a, ∀ i < H, G.scheme.toCellScheme.gradedIndex (r a i) = (univ, 1)) ∧
        (∀ a, ∀ i < H, G.scheme.rowAt (r a i) (r a i) = Label.ladderSource (i + 1) (i + 1)) ∧
        (∀ a, ∀ i < H, 0 < i →
          G.scheme.rowAt (r a i) (r a (i - 1)) = Label.ladderSource (i + 1) i) ∧
        ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
          ∃ (a : Mb) (F : ℕ → Label.{u}), G.IsLadderController Q (H := H) r u a F := by
  obtain ⟨H, Γ, B', hH, hcard, hΓ0, hΓ, hΓω, hmixed, hctx, hmc, hlab⟩ := h
  exact exists_replicatedCarrier hα hd Q hN hH hcard hΓ0 hΓ hΓω rfl
    (isBountiful_replicated_of_lifts hmixed (hasCoatomLifts_of_lifts hctx hmc)) hlab

end Seed

namespace StageType

/-- **The inputs of the replicated scheme at some seed** (open): for every legal context on
`m + 1` points with a closed first coatom and the root inside it, every legal one-point coface `d`
of the root face (no bound on its top grade), and all requests calibrated on the class with
the labels pair admitted and the relative lift on the exact class, SOME seed with the context as
its first coatom type and the donor as the face of its amalgam along the root followed by the new
point carries the inputs of its replicated scheme. -/
def HasReplicatedInputsAtSeed : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄ (t' : StageType.{u} α (m + 1)) (g : Fin n ↪ Fin m)
    (p' : StageType.{u} α m), Order.IsSuccLimit α → t'.IsLegal →
    restrictFace Fin.castSuccEmb t' = some p' → ∀ (p : StageType.{u} α n)
      (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p) (d : StageType.{u} α (n + 1))
      (hd : d ∈ p.cofaces), 0 < n →
      ∀ Q : GrowthRequests t' d.toScheme,
        (∀ j, Q.CorrectAt t'.label j (d.label j)) → Q.ClassCalibrated hte →
        Q.HasRelativeLiftOnClass hte hd.2 →
        ∃ (I : Seed.{u} α m) (hI : I.left = t')
          (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d),
          I.ReplicatedInputs g hdA (hI ▸ Q)

/-- **Ladder carriers at the seed position from the inputs of the replicated scheme** at some
seed. -/
theorem HasReplicatedInputsAtSeed.hasLadderGrowthCarriersStableAtSeed
    (h : HasReplicatedInputsAtSeed.{u}) : HasLadderGrowthCarriersStableAtSeed.{u} := by
  intro α n m t' g p' hα ht' hp' p hte d hd hn Q hpair hQ hrel
  obtain ⟨I, rfl, hdA, hin⟩ := h t' g p' hα ht' hp' p hte d hd hn Q hpair hQ hrel
  exact Seed.exists_ladderCarrier_of_replicatedInputs hdA hα.isSuccPrelimit Q
    (by have := hQ.arity; omega) hin

end StageType

end VaughtConjecture
