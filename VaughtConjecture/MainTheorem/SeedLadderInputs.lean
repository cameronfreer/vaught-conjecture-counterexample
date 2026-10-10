/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.GrowthSeed
import VaughtConjecture.MainTheorem.GrowthStableLadder
import VaughtConjecture.MainTheorem.SeedLadderCarrier

/-!
# Ladder carriers at the seed position from the inputs of the ladder tower

Roadmap, Layer 3 ((R3) and (R4), the assembly of the recognizing growth carrier).

The **inputs of the ladder tower** at a seed for requests `Q` (`Seed.LadderTowerInputs`): a
height, a finite set of values containing `⊥` and a grid bound, the capped lifts of the tower from
the two coatoms into the full faces of the grades `2, …, m + 1`, and a lawful labelling of the tower
extending the glued labels of the amalgam.  These inputs stay open; the contract itself has a
direct proof by the levels re-rendered per grade
(`StageType.hasLadderGrowthCarriersStableAtSeed_levels`, not yet reviewed).  From the inputs the
ladder carrier exists (`Seed.exists_ladderCarrier_of_inputs`: the tower is bountiful by
`Seed.isBountiful_ladderTower_of_coatomLifts`, and `Seed.exists_ladderCarrier` assembles the
completion).

**At the seed position** (`StageType.HasLadderGrowthCarriersStableAtSeed`, the body of
`StageType.HasLadderGrowthCarriersStable` for a context on `m + 1` points with a closed first
coatom and the root inside it; no bound on the donor's top grade): the inputs at some
seed of the context (`StageType.HasLadderTowerInputsAtSeed`, open; the second coatom type is free)
give it
(`StageType.HasLadderTowerInputsAtSeed.hasLadderGrowthCarriersStableAtSeed`).  Of the hypotheses
of the contract the implication itself uses exactly: the stage is a limit (`Order.IsSuccLimit α`,
for the completion at a stage that is zero or a limit), and the threshold of the requests is at
least `2`, from `ClassCalibrated.arity` (`n + 1 ≤` the threshold) together with the positive arity
of the root (`0 < n`).  Every other hypothesis is handed to the inputs at the seed.  No exactness,
no root cleanness, no bound on the donor's top grade.

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) {e₀ : Fin n ↪ Fin m}
  {d : StageType.{u} α (n + 1)}
  (hd : restrictFace (extendByLast (e₀.trans Fin.castSuccEmb)) I.amalgam = some d)

/-- **The inputs of the ladder tower** at a seed for requests `Q` (open): a height `H`, a finite set
`Γ` of values and a grid bound `B'`, the capped lifts of the tower from the two coatoms into the
full faces of the grades `2, …, m + 1`, and a lawful labelling extending the glued labels. -/
def LadderTowerInputs (Q : GrowthRequests I.left d.toScheme) : Prop :=
  ∃ (H : ℕ) (Γ : Finset Label.{u}) (B' : ℕ), 0 < H ∧ I.amalgam.card ≤ H ∧ ⊥ ∈ Γ ∧
    (∀ x ∈ Γ, x ≤ gridPoint 2 B') ∧
    (∀ x ∈ Γ, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})) ∧
    (∀ x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))),
      ∀ j, 2 ≤ j → j ≤ m + 1 →
        (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.rows.CappedLift
          (X := (univ.erase x, j)) (Y := ((univ : Finset (Fin (m + 2))), j))
          ⟨erase_subset _ _, le_rfl⟩) ∧
    ∃ q : Fin (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.card → Label.{u},
      (I.ladderTower H Γ (I.towerAdmits hd Q) B' m).S.rows.IsLawful q ∧
        ∀ c, q (I.towerAmalgamEmb H Γ (I.towerAdmits hd Q) B' c) = I.amalgam.label c

variable {I}

/-- **The ladder carrier from the inputs of the ladder tower.** -/
theorem exists_ladderCarrier_of_inputs (hα : Order.IsSuccPrelimit α)
    (Q : GrowthRequests I.left d.toScheme) (hN : 2 ≤ Q.threshold) (h : I.LadderTowerInputs hd Q) :
    ∃ G : GrowthCarrier I.left.toScheme d.toScheme (e₀.trans Fin.castSuccEmb),
      (∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold)) ∧
      ∃ (Mb : Type) (H : ℕ) (r : Mb → ℕ → Fin G.scheme.card), 0 < H ∧
        (∀ a, ∀ i < H, G.scheme.toCellScheme.gradedIndex (r a i) = (univ, 1)) ∧
        (∀ a, ∀ i < H, G.scheme.rowAt (r a i) (r a i) = Label.ladderSource (i + 1) (i + 1)) ∧
        (∀ a, ∀ i < H, 0 < i →
          G.scheme.rowAt (r a i) (r a (i - 1)) = Label.ladderSource (i + 1) i) ∧
        ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
          ∃ (a : Mb) (F : ℕ → Label.{u}), G.IsLadderController Q (H := H) r u a F := by
  obtain ⟨H, Γ, B', hH, hcard, hΓ0, hΓ, hΓω, hlift, hlab⟩ := h
  exact exists_ladderCarrier hd hα Q hN hH hcard hΓ0 hΓ hΓω
    (isBountiful_ladderTower_of_coatomLifts I H Γ _ B' hH hcard hlift) hlab

end Seed

namespace StageType

/-- **The inputs of the ladder tower at some seed** (open): for every legal context on `m + 1`
points with a closed first coatom and the root inside it, every legal one-point coface `d` of the
root face, and all requests calibrated on the class with the
labels pair admitted and the relative lift on the exact class, SOME seed with the context as its
first coatom type and the donor as the face of its amalgam along the root followed by the new point
carries the inputs of its ladder tower.  The choice of the second coatom type is free: over the
enlarged donor of `StageType.exists_growthSeed` itself the lift from the second coatom can be
obstructed (`GrowthCarrier.not_recognizes_of_bottom`). -/
def HasLadderTowerInputsAtSeed : Prop :=
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
          I.LadderTowerInputs hdA (hI ▸ Q)

/-- **Ladder carriers at the seed position from the inputs of the ladder tower** at some seed. -/
theorem HasLadderTowerInputsAtSeed.hasLadderGrowthCarriersStableAtSeed
    (h : HasLadderTowerInputsAtSeed.{u}) : HasLadderGrowthCarriersStableAtSeed.{u} := by
  intro α n m t' g p' hα ht' hp' p hte d hd hn Q hpair hQ hrel
  obtain ⟨I, rfl, hdA, hin⟩ := h t' g p' hα ht' hp' p hte d hd hn Q hpair hQ hrel
  exact Seed.exists_ladderCarrier_of_inputs hdA hα.isSuccPrelimit Q (by have := hQ.arity; omega)
    hin

end StageType

end VaughtConjecture
