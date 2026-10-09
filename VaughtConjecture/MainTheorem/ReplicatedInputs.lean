/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLadderCarrier
import VaughtConjecture.MainTheorem.SeedLadderInputs

/-!
# Ladder carriers at the seed position from the inputs of the replicated scheme

Roadmap, Layer 3 ((R3) and (R4), the assembly of the recognizing growth carrier).

The **inputs of the replicated scheme** at a seed for requests `Q` (`Seed.ReplicatedInputs`): a
height, a finite set of values containing `⊥` and a grid bound, and, for the replicated scheme over
the attachment with the admission predicate of `Q`,

* the capped lifts into the mixed faces (`Seed.HasMixedLifts`, open),
* the capped lifts from the two coatoms into the full faces of the grades `1, …, m + 1`: the
  context lift (`Seed.HasContextLift`, open) and the mixed-coatom lift
  (`Seed.HasMixedCoatomLift`, open; the second coatom is a mixed face when the root is not onto),
* a lawful labelling extending the labels of the attachment (`Seed.HasExtendingLabel`, open; it
  follows from a lawful labelling of the ladder tower extending them,
  `Seed.hasExtendingLabel_of_tower`, the copies reading the labels of their originals).

From them the ladder carrier exists (`Seed.exists_ladderCarrier_of_replicatedInputs`: the
replicated scheme is bountiful by `Seed.isBountiful_replicated_of_lifts`, and
`Seed.exists_replicatedCarrier` assembles the completion).  Below a pair whose face lies in the
context face or the donor face no lift is asked: there the replicated scheme is the amalgam.

**At the seed position** the inputs at some seed of the context
(`StageType.HasReplicatedInputsAtSeed`, open) give ladder carriers
(`StageType.HasReplicatedInputsAtSeed.hasLadderGrowthCarriersStableAtSeed`).  Only the requests'
threshold `≥ 2` is used; no exactness, no root cleanness.

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

/-- **The context lift** (open): the replicated scheme lifts capped from the context coatom (the
points other than the new one) into the full face at every grade `1, …, m + 1`. -/
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

/-- **A labelling extending the labels of the attachment** (open): a lawful section of the
replicated scheme that is the labelling of the attachment on its cells. -/
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
of the root face of top grade at most the context's, and all requests calibrated on the class with
the labels pair admitted and the relative lift on the exact class, SOME seed with the context as
its first coatom type and the donor as the face of its amalgam along the root followed by the new
point carries the inputs of its replicated scheme. -/
def HasReplicatedInputsAtSeed : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄ (t' : StageType.{u} α (m + 1)) (g : Fin n ↪ Fin m)
    (p' : StageType.{u} α m), Order.IsSuccLimit α → t'.IsLegal →
    restrictFace Fin.castSuccEmb t' = some p' → ∀ (p : StageType.{u} α n)
      (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p) (d : StageType.{u} α (n + 1))
      (hd : d ∈ p.cofaces), d.topGrade ≤ t'.topGrade → 0 < n →
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
  intro α n m t' g p' hα ht' hp' p hte d hd hdK hn Q hpair hQ hrel
  obtain ⟨I, rfl, hdA, hin⟩ := h t' g p' hα ht' hp' p hte d hd hdK hn Q hpair hQ hrel
  exact Seed.exists_ladderCarrier_of_replicatedInputs hdA hα.isSuccPrelimit Q
    (by have := hQ.arity; omega) hin

end StageType

end VaughtConjecture
