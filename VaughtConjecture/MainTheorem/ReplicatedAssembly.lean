/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLabel
import VaughtConjecture.MainTheorem.GrowthRelabelStable
import VaughtConjecture.Extension.LadderTowerContextLiftOne
import VaughtConjecture.Extension.ReplicatedSeedFaces

/-!
# The inputs of the replicated scheme at the seed position from the remaining lifts

Roadmap, Layer 3 ((R3) and (R4), the assembly of the recognizing growth carrier).

`StageType.HasReplicatedInputsAtSeed` (open) asks, at every seed position, for SOME seed and SOME
height `H`, finite set of values `Γ` and grid bound `B'` with the four inputs of the replicated
scheme.  Here one choice of `H`, `Γ`, `B'` is made for every seed at once (functions of the seed
and the root, quantified once, outside the lift statements), the seed is the one of
`StageType.exists_growthSeed_of_isSuccLimit`, and the inputs are assembled from what is compiled
and from three lift statements at the seed position, each for the same `H`, `Γ`, `B'`:

* `StageType.HasAttachedMixedLiftsAtSeed H Γ B'` (open): the same-grade lifts from the faces
  inside the context face or the donor face into the mixed faces, at the grades `k ≥ 2`;
* `StageType.HasContextLiftAtSeed H Γ B'` (open): the lift from the context coatom into the full
  face, at the grades `2, …, m + 1`; it follows from the extension over the tower at those grades
  (`StageType.hasContextLiftAtSeed_of_towerExtension`, `Seed.TowerExtension` open);
* `StageType.HasOntoRootCoatomLiftAtSeed H Γ B'` (open): for an ONTO root only, the lift from the
  second coatom (then the donor face) into the full face, at the grades `2, …, m + 1`.

What is compiled and used: the grade one of each lift (`Seed.attachedMixedLifts_one`,
`Seed.cappedLift_context_one`, `Seed.cappedLift_coatom_one_of_surjective`), with their face
hypotheses at the seed (`Seed.mem_faces_donorFace`, `Seed.mem_faces_root`,
`Seed.one_le_card_root`); the same-grade lifts between mixed faces
(`Seed.hasMixedLifts_of_attachedMixedLifts`); the mixed-coatom lift for a root that is not onto
(`Seed.hasMixedCoatomLift`); and the lawful labelling extending the labels of the attachment
(`Seed.hasExtendingLabel_attachAdmits`), which asks `Γ` to contain the compressed labels
(`Γ₀ ⊆ Γ`, `Γ₀ = univ.image (I.compressedLabel g)`) and every value of `Γ` to lie below the grid
point `ω * B' + 2` (for `Γ₀` this is `B₀ ≤ B'`, `B₀ = blockCount (I.attachLabels g) + 1`).

**The onto root.**  The seed position allows `n = m`: calibration gives only `n < m + 1`
(`StageType.GrowthRequests.Calibrated.lt`), so the root `g : Fin n ↪ Fin m` may be onto.  Then the
second coatom is the donor face (`Seed.donorFace_eq_coatom_of_surjective`), not a mixed face, and
`Seed.hasMixedCoatomLift` (which needs a root that is not onto) does not apply; the lift from it
above the grade one is the third statement.  It is asked only at onto roots.

**The choice** (`Seed.seedHeight`, `Seed.seedValues`, `Seed.seedGridBound`): `H` the number of
cells of the attachment plus one, `Γ = insert ⊥ Γ₀`, `B' = B₀`.  It meets every side condition
(`StageType.hasReplicatedInputsAtSeed_of_seedLifts`), so the main theorem follows from (R2) and the
three lift statements at this choice
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_seedLifts`, through the transport of the
seed position, `StageType.HasLadderGrowthCarriersStableAtSeed.hasLadderGrowthCarriersStable`).

The lift statements are asked at EVERY seed with the context as its first coatom type and the
donor as the face along the root followed by the new point (the assembly uses one such seed).
These are implications; `StageType.HasReplicatedInputsAtSeed`, the three lift statements and the
main theorem stay conditional.

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m)

/-! ### The choice of the height, the values and the grid bound -/

/-- **The height of the choice**: the number of cells of the attachment plus one. -/
noncomputable def seedHeight : ℕ := (I.attachment g).card + 1

/-- **The values of the choice**: `⊥` and the compressed labels of the attachment. -/
noncomputable def seedValues : Finset Label.{u} := insert ⊥ (univ.image (I.compressedLabel g))

/-- **The grid bound of the choice**: the number of blocks of the labels of the attachment plus
one. -/
noncomputable def seedGridBound : ℕ := blockCount (I.attachLabels g) + 1

theorem seedHeight_pos : 0 < I.seedHeight g := Nat.succ_pos _

theorem card_le_seedHeight : (I.attachment g).card ≤ I.seedHeight g := Nat.le_succ _

theorem bot_mem_seedValues : (⊥ : Label.{u}) ∈ I.seedValues g := mem_insert_self _ _

theorem image_compressedLabel_subset_seedValues :
    univ.image (I.compressedLabel g) ⊆ I.seedValues g := subset_insert _ _

theorem le_gridPoint_of_mem_seedValues {x : Label.{u}} (hx : x ∈ I.seedValues g) :
    x ≤ gridPoint 2 (I.seedGridBound g) := by
  rcases mem_insert.mp hx with rfl | hx
  · exact bot_le
  · obtain ⟨c, -, rfl⟩ := mem_image.mp hx
    exact compressedLabel_le_gridPoint le_rfl c

theorem lt_omega0_sq_of_mem_seedValues {x : Label.{u}} (hx : x ∈ I.seedValues g) :
    x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  rcases mem_insert.mp hx with rfl | hx
  · exact WithBot.bot_lt_coe _
  · obtain ⟨c, -, rfl⟩ := mem_image.mp hx
    exact compressedLabel_lt_omega0_sq c

/-! ### The lifts at a seed from their parts above the grade one -/

variable {I g} {H : ℕ} {Γ : Finset Label.{u}}
  {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- **The lifts from the faces of the attachment into the mixed faces from the grades `k ≥ 2`**:
at the grade one they hold (`Seed.attachedMixedLifts_one`). -/
theorem hasAttachedMixedLifts_of_two (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (hdF : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb))))
    (h2 : ∀ ⦃V U : Finset (Fin (m + 2))⦄ ⦃k : ℕ⦄,
      V ∈ (I.replicated g H Γ A B').toCellScheme.faces →
      (V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
        V ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))) →
      U ∈ I.mixedFaces g → ∀ h : V ⊆ U, 2 ≤ k → k ≤ #V →
        (I.replicated g H Γ A B').rows.CappedLift (X := (V, k)) (Y := (U, k)) ⟨h, le_rfl⟩) :
    I.HasAttachedMixedLifts g H Γ A B' := by
  intro V U k hVF hV hU h hk1 hkV
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by omega
    exact attachedMixedLifts_one hH hcard hΓ hA hdF hrF hr1 hVF hV hU h hkV
  · exact h2 hVF hV hU h hk hkV

/-- **The context lift from the grades `2, …, m + 1`**: at the grade one it holds
(`Seed.cappedLift_context_one`). -/
theorem hasContextLift_of_two (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hdF : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb))))
    (h2 : ∀ j, 2 ≤ j → j ≤ m + 1 →
      (I.replicated g H Γ A B').rows.CappedLift (X := (univ.erase (Fin.last (m + 1)), j))
        (Y := ((univ : Finset (Fin (m + 2))), j)) ⟨erase_subset _ _, le_rfl⟩) :
    I.HasContextLift g H Γ A B' := by
  intro j hj hjm
  rcases Nat.lt_or_ge j 2 with h1 | h1
  · obtain rfl : j = 1 := by omega
    exact cappedLift_context_one hH hcard hdF hrF hr1
  · exact h2 j h1 hjm

/-- **The lift from the second coatom from its grades `2, …, m + 1` at an onto root**: for a
root that is not onto it holds (`Seed.hasMixedCoatomLift`); for an onto root it holds at the grade
one (`Seed.cappedLift_coatom_one_of_surjective`). -/
theorem hasMixedCoatomLift_of_two (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (hA0 : ∀ k, A k fun _ ↦ ⊥)
    (hdF : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb))))
    (h2 : Function.Surjective g → ∀ j, 2 ≤ j → j ≤ m + 1 →
      (I.replicated g H Γ A B').rows.CappedLift
        (X := (univ.erase (Fin.castSucc (Fin.last m)), j))
        (Y := ((univ : Finset (Fin (m + 2))), j)) ⟨erase_subset _ _, le_rfl⟩) :
    I.HasMixedCoatomLift g H Γ A B' := by
  by_cases hg : Function.Surjective g
  · intro j hj hjm
    rcases Nat.lt_or_ge j 2 with h1 | h1
    · obtain rfl : j = 1 := by omega
      exact cappedLift_coatom_one_of_surjective hH hcard hg hdF hrF hr1
    · exact h2 hg j h1 hjm
  · exact hasMixedCoatomLift hH hcard hΓ0 hΓ hA hA0 hg

end Seed

namespace StageType

/-! ### The lift statements at the seed position -/

/-- **The same-grade lifts from the faces of the attachment into the mixed faces at the seed
position, at the grades `k ≥ 2`** (open), for the choice `H`, `Γ`, `B'` of a height, values and a
grid bound at each seed and root: at every seed `I` at a limit stage with a legal first coatom
type, a closed first coatom `p'` in it, a root `g` with face `p` in it, a legal coface `d` of `p`
that is the face of the amalgam along the root followed by the new point, a positive arity, and
all requests `Q` calibrated on the class with the labels pair admitted and the relative lift on the
exact class, the replicated scheme with the admission predicate of `Q` lifts capped from `(V, k)`
to `(U, k)` for every face `V` inside the context face or the donor face, every mixed face
`U ⊇ V`, and `2 ≤ k ≤ |V|`. -/
def HasAttachedMixedLiftsAtSeed
    (H : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ)
    (Γ : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → Finset Label.{u})
    (B' : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄ (I : Seed.{u} α m) (g : Fin n ↪ Fin m)
    (p' : StageType.{u} α m), Order.IsSuccLimit α → I.left.IsLegal →
    restrictFace Fin.castSuccEmb I.left = some p' → ∀ (p : StageType.{u} α n)
      (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (d : StageType.{u} α (n + 1))
      (hd : d ∈ p.cofaces)
      (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d), 0 < n →
      ∀ Q : GrowthRequests I.left d.toScheme,
        (∀ j, Q.CorrectAt I.left.label j (d.label j)) → Q.ClassCalibrated hte →
        Q.HasRelativeLiftOnClass hte hd.2 →
        ∀ ⦃V U : Finset (Fin (m + 2))⦄ ⦃k : ℕ⦄,
          V ∈ (I.replicated g (H I g) (Γ I g) (I.attachAdmits g hdA Q)
            (B' I g)).toCellScheme.faces →
          (V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
            V ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))) →
          U ∈ I.mixedFaces g → ∀ h : V ⊆ U, 2 ≤ k → k ≤ #V →
            (I.replicated g (H I g) (Γ I g) (I.attachAdmits g hdA Q) (B' I g)).rows.CappedLift
              (X := (V, k)) (Y := (U, k)) ⟨h, le_rfl⟩

/-- **The context lift at the seed position, at the grades `2, …, m + 1`** (open), for the choice
`H`, `Γ`, `B'`: at every seed and requests as in `StageType.HasAttachedMixedLiftsAtSeed`, the
replicated scheme with the admission predicate of `Q` lifts capped from the context coatom (the
points other than the new one) into the full face at the grade `j`, for `2 ≤ j ≤ m + 1`. -/
def HasContextLiftAtSeed
    (H : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ)
    (Γ : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → Finset Label.{u})
    (B' : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄ (I : Seed.{u} α m) (g : Fin n ↪ Fin m)
    (p' : StageType.{u} α m), Order.IsSuccLimit α → I.left.IsLegal →
    restrictFace Fin.castSuccEmb I.left = some p' → ∀ (p : StageType.{u} α n)
      (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (d : StageType.{u} α (n + 1))
      (hd : d ∈ p.cofaces)
      (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d), 0 < n →
      ∀ Q : GrowthRequests I.left d.toScheme,
        (∀ j, Q.CorrectAt I.left.label j (d.label j)) → Q.ClassCalibrated hte →
        Q.HasRelativeLiftOnClass hte hd.2 →
        ∀ j, 2 ≤ j → j ≤ m + 1 →
          (I.replicated g (H I g) (Γ I g) (I.attachAdmits g hdA Q) (B' I g)).rows.CappedLift
            (X := (univ.erase (Fin.last (m + 1)), j)) (Y := ((univ : Finset (Fin (m + 2))), j))
            ⟨erase_subset _ _, le_rfl⟩

/-- **The lift from the second coatom at the seed position for an onto root, at the grades
`2, …, m + 1`** (open), for the choice `H`, `Γ`, `B'`: at every seed and requests as in
`StageType.HasAttachedMixedLiftsAtSeed` whose root `g` is onto (so `n = m`, and the second coatom
is the donor face), the replicated scheme with the admission predicate of `Q` lifts capped from the
second coatom (the points other than `m`) into the full face at the grade `j`, for
`2 ≤ j ≤ m + 1`.  For a root that is not onto this lift holds (`Seed.hasMixedCoatomLift`). -/
def HasOntoRootCoatomLiftAtSeed
    (H : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ)
    (Γ : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → Finset Label.{u})
    (B' : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄ (I : Seed.{u} α m) (g : Fin n ↪ Fin m)
    (p' : StageType.{u} α m), Order.IsSuccLimit α → I.left.IsLegal →
    restrictFace Fin.castSuccEmb I.left = some p' → ∀ (p : StageType.{u} α n)
      (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (d : StageType.{u} α (n + 1))
      (hd : d ∈ p.cofaces)
      (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d), 0 < n →
      ∀ Q : GrowthRequests I.left d.toScheme,
        (∀ j, Q.CorrectAt I.left.label j (d.label j)) → Q.ClassCalibrated hte →
        Q.HasRelativeLiftOnClass hte hd.2 → Function.Surjective g →
        ∀ j, 2 ≤ j → j ≤ m + 1 →
          (I.replicated g (H I g) (Γ I g) (I.attachAdmits g hdA Q) (B' I g)).rows.CappedLift
            (X := (univ.erase (Fin.castSucc (Fin.last m)), j))
            (Y := ((univ : Finset (Fin (m + 2))), j)) ⟨erase_subset _ _, le_rfl⟩

/-- **The context lift at the seed position from the extension over the tower** at the grades
`2, …, m + 1` (`Seed.TowerExtension`, open), for a choice with `H` positive and at least the number
of cells of the attachment and `⊥ ∈ Γ`: the state lift holds (`Seed.contextStateLiftR_attachAdmits`,
the ambient being admitted, `Seed.ambientAdmitted`), and with the extension it gives the lift
(`Seed.cappedLift_context_of_towerExtension`). -/
theorem hasContextLiftAtSeed_of_towerExtension
    (H : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ)
    (Γ : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → Finset Label.{u})
    (B' : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ)
    (hH : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m), 0 < H I g)
    (hcard : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m),
      (I.attachment g).card ≤ H I g)
    (hΓ0 : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m), ⊥ ∈ Γ I g)
    (hE : ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄ (I : Seed.{u} α m) (g : Fin n ↪ Fin m)
      (p' : StageType.{u} α m), Order.IsSuccLimit α → I.left.IsLegal →
      restrictFace Fin.castSuccEmb I.left = some p' → ∀ (p : StageType.{u} α n)
        (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p)
        (d : StageType.{u} α (n + 1)) (hd : d ∈ p.cofaces)
        (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d), 0 < n →
        ∀ Q : GrowthRequests I.left d.toScheme,
          (∀ j, Q.CorrectAt I.left.label j (d.label j)) → Q.ClassCalibrated hte →
          Q.HasRelativeLiftOnClass hte hd.2 →
          ∀ j, 2 ≤ j → j ≤ m + 1 →
            Seed.TowerExtension I g (H I g) (Γ I g) (I.attachAdmits g hdA Q) (B' I g) j) :
    HasContextLiftAtSeed.{u} H Γ B' := by
  intro α n m I g p' hα hI hp' p hte d hd hdA hn Q hpair hQ hrel j hj hjm
  exact Seed.cappedLift_context_of_towerExtension
    (Seed.contextStateLiftR_attachAdmits hte hd.2 hd.1 hn hdA hQ hpair hrel (by omega)
      (Seed.ambientAdmitted (hH I g) (hcard I g) (hΓ0 I g) hdA hQ hn j))
    (hE I g p' hα hI hp' p hte d hd hdA hn Q hpair hQ hrel j hj hjm)

/-! ### The assembly -/

/-- **The inputs of the replicated scheme at the seed position from the three lift statements**,
for a choice `H`, `Γ`, `B'` with the side conditions: `H` positive and at least the number of cells
of the attachment, `⊥ ∈ Γ`, every value of `Γ` at most the grid point `ω * B' + 2` and below
`ω ^ 2`, and `Γ` containing the compressed labels of the attachment (`Γ₀ ⊆ Γ`, for the labelling
`Seed.hasExtendingLabel_attachAdmits`).  The seed is that of
`StageType.exists_growthSeed_of_isSuccLimit`. -/
theorem hasReplicatedInputsAtSeed_of_lifts
    (H : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ)
    (Γ : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → Finset Label.{u})
    (B' : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ)
    (hH : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m), 0 < H I g)
    (hcard : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m),
      (I.attachment g).card ≤ H I g)
    (hΓ0 : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m), ⊥ ∈ Γ I g)
    (hΓ : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m),
      ∀ x ∈ Γ I g, x ≤ gridPoint 2 (B' I g))
    (hΓω : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m),
      ∀ x ∈ Γ I g, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hsub : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m),
      univ.image (I.compressedLabel g) ⊆ Γ I g)
    (hatt : HasAttachedMixedLiftsAtSeed.{u} H Γ B') (hctx : HasContextLiftAtSeed.{u} H Γ B')
    (honto : HasOntoRootCoatomLiftAtSeed.{u} H Γ B') : HasReplicatedInputsAtSeed.{u} := by
  intro α n m t' g p' hα ht' hp' p hte d hd hn Q hpair hQ hrel
  obtain ⟨I, rfl, hdA⟩ :=
    exists_growthSeed_of_isSuccLimit hα ht' hp' ((restrictFace_trans t' _ g hp').trans hte) hd
  refine ⟨I, rfl, hdA, ?_⟩
  have hdF := Seed.mem_faces_donorFace hdA
  have hrF := Seed.mem_faces_root hte
  have hr1 := Seed.one_le_card_root (m := m) g hn
  have hA := I.attachAdmits_succ g hdA Q
  have hA0 := I.attachAdmits_bot g hdA Q
  exact Seed.replicatedInputs_of_lifts hdA hpair hQ (hH I g) (hcard I g) (hΓ0 I g) (hΓ I g)
    (hΓω I g) (fun c ↦ hsub I g (mem_image_of_mem _ (mem_univ c)))
    (Seed.hasMixedLifts_of_attachedMixedLifts (hH I g) (hcard I g) (hΓ0 I g) (hΓ I g) hA hA0
      (Seed.hasAttachedMixedLifts_of_two (hH I g) (hcard I g) (hΓ I g) hA hdF hrF hr1
        (hatt I g p' hα ht' hp' p hte d hd hdA hn Q hpair hQ hrel)))
    (Seed.hasContextLift_of_two (hH I g) (hcard I g) hdF hrF hr1
      (hctx I g p' hα ht' hp' p hte d hd hdA hn Q hpair hQ hrel))
    (Seed.hasMixedCoatomLift_of_two (hH I g) (hcard I g) (hΓ0 I g) (hΓ I g) hA hA0 hdF hrF hr1
      (honto I g p' hα ht' hp' p hte d hd hdA hn Q hpair hQ hrel))

/-- **The inputs of the replicated scheme at the seed position from the three lift statements at
the choice** `H = #cells + 1`, `Γ = insert ⊥ Γ₀`, `B' = B₀` (`Seed.seedHeight`, `Seed.seedValues`,
`Seed.seedGridBound`), which meets every side condition of
`StageType.hasReplicatedInputsAtSeed_of_lifts`. -/
theorem hasReplicatedInputsAtSeed_of_seedLifts
    (hatt : HasAttachedMixedLiftsAtSeed.{u} Seed.seedHeight Seed.seedValues Seed.seedGridBound)
    (hctx : HasContextLiftAtSeed.{u} Seed.seedHeight Seed.seedValues Seed.seedGridBound)
    (honto : HasOntoRootCoatomLiftAtSeed.{u} Seed.seedHeight Seed.seedValues
      Seed.seedGridBound) :
    HasReplicatedInputsAtSeed.{u} :=
  hasReplicatedInputsAtSeed_of_lifts _ _ _ Seed.seedHeight_pos Seed.card_le_seedHeight
    Seed.bot_mem_seedValues (fun I g _ hx ↦ I.le_gridPoint_of_mem_seedValues g hx)
    (fun I g _ hx ↦ I.lt_omega0_sq_of_mem_seedValues g hx)
    Seed.image_compressedLabel_subset_seedValues hatt hctx honto

end StageType

namespace MainTheorem

open Ordinal Realization FirstOrder Language Structure baseLanguage Expansion StageType

/-- **The main theorem from (R2) and the three lift statements at the seed position** (all four
hypotheses open): the context lift and the lifts from the faces of the attachment into the mixed
faces above the grade one, and, for an onto root only, the lift from the second coatom above the
grade one, all at the choice `Seed.seedHeight`, `Seed.seedValues`, `Seed.seedGridBound`.  Through
`StageType.HasReplicatedInputsAtSeed.hasLadderGrowthCarriersStableAtSeed` and the transport
`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_stableAtSeed`. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_seedLifts
    (hres : ReceivingResidualReceiving.{0, 0})
    (hatt : HasAttachedMixedLiftsAtSeed.{0} Seed.seedHeight Seed.seedValues Seed.seedGridBound)
    (hctx : HasContextLiftAtSeed.{0} Seed.seedHeight Seed.seedValues Seed.seedGridBound)
    (honto : HasOntoRootCoatomLiftAtSeed.{0} Seed.seedHeight Seed.seedValues
      Seed.seedGridBound) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_stableAtSeed hres
    (hasReplicatedInputsAtSeed_of_seedLifts hatt hctx honto).hasLadderGrowthCarriersStableAtSeed

end MainTheorem

end VaughtConjecture
