/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedAttachedInputs
import VaughtConjecture.Extension.ReplicatedStateCoding
import VaughtConjecture.MainTheorem.GrowthRelabelStable
import VaughtConjecture.Extension.LadderTowerContextLiftOne
import VaughtConjecture.Extension.LadderTowerContextLiftCap
import VaughtConjecture.Extension.ReplicatedOntoRoot
import VaughtConjecture.MainTheorem.LowPaddedRoute

/-!
# The inputs of the replicated scheme at the seed position from the extension over the tower

Roadmap, Layer 3 ((R3) and (R4), the assembly of the recognizing growth carrier).

`StageType.HasReplicatedInputsAtSeed` (open) asks, at every seed position, for SOME seed and SOME
height `H`, finite set of values `Γ` and grid bound `B'` with the four inputs of the replicated
scheme.  Here one choice of `H`, `Γ`, `B'` is made for every seed at once (functions of the seed
and the root, quantified once, outside every statement), the seed is the one of
`StageType.exists_growthSeed_of_isSuccLimit`, and the inputs are assembled from what is compiled
and from ONE open statement at the seed position:

* `StageType.TowerExtensionAtSeed H Γ B'` (open): the extension over the tower
  (`Seed.TowerExtension`) at the grades `2, …, m + 1`, at every seed and requests of the seed
  position, for the replicated scheme with the admission predicate of the requests.

It follows from its case at a positive cap the state exceeds,
`StageType.TowerExtensionPosAtSeed H Γ B'` (`Seed.TowerExtensionPos`: caps `⊥ < c`, some cell of
the attachment of grade at most `j` where the state is not at most `c`), once `Γ` contains the code
set (`StageType.towerExtensionAtSeed_of_pos`, by `Seed.towerExtension_of_pos`: at the cap `⊥` the
decoded writing of the code of the state extends it, and a state at most the cap is extended by the
ambient capped).  Every use of the extension below (the context lift, the lifts into the mixed
faces, the lift from the second coatom at an onto root) goes through
`Seed.TowerExtension`, so the positive case suffices for all of them
(`StageType.hasReplicatedInputsAtSeed_of_towerExtensionPos`,
`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_towerExtensionPos`).

It gives three lift statements at the seed position, each for the same `H`, `Γ`, `B'` (they are
kept as statements of their own, readable separately, so that the assembly
`StageType.hasReplicatedInputsAtSeed_of_lifts` asks only for them):

* `StageType.HasAttachedMixedLiftsAtSeed H Γ B'`: the same-grade lifts from the faces inside the
  context face or the donor face into the mixed faces at the grades `k ≥ 2`
  (`StageType.hasAttachedMixedLiftsAtSeed_of_towerExtension`: through the full face, the context
  lift inside the context face, the state lift inside the donor face);
* `StageType.HasContextLiftAtSeed H Γ B'`: the lift from the context coatom into the full face at
  the grades `2, …, m + 1` (`StageType.hasContextLiftAtSeed_of_towerExtension`);
* `StageType.HasOntoRootCoatomLiftAtSeed H Γ B'`: for an ONTO root only, the lift from the second
  coatom into the full face at the grades `2, …, m + 1`
  (`StageType.hasOntoRootCoatomLiftAtSeed_of_towerExtension`: the second coatom is then the donor
  face, `Seed.cappedLift_donor_univ_attachAdmits`).

**The onto root.**  The seed position allows `n = m`: calibration gives only `n < m + 1`
(`StageType.GrowthRequests.Calibrated.lt`), so the root `g : Fin n ↪ Fin m` may be onto, and the
hypothesis `¬ Function.Surjective g` of `Seed.hasMixedCoatomLift` and
`Seed.replicatedInputs_of_towerExtension` is not available there.  For an onto root the second
coatom is the donor face (`Seed.donorFace_eq_coatom_of_surjective`), and the lift from it is the
lift from a face inside the donor face, which the extension over the tower gives as well.

What is compiled and used besides: the grade one of each lift (`Seed.attachedMixedLifts_one`,
`Seed.cappedLift_context_one`, `Seed.cappedLift_coatom_one_of_surjective`), with the face
hypotheses at the seed (`Seed.donor_mem_faces`, `Seed.root_mem_faces`, `Seed.card_root`); the
same-grade lifts between mixed faces (`Seed.hasMixedLifts_of_attachedMixedLifts`); the
mixed-coatom lift for a root that is not onto (`Seed.hasMixedCoatomLift`); and the lawful
labelling extending the labels of the attachment (`Seed.hasExtendingLabel_attachAdmits`), which
asks `Γ` to contain the compressed labels (`Γ₀ ⊆ Γ`, `Γ₀ = univ.image (I.compressedLabel g)`) and
every value of `Γ` to lie below the grid point `ω * B' + 2` (for `Γ₀` this is `B₀ ≤ B'`,
`B₀ = blockCount (I.attachLabels g) + 1`).

**The code set.**  The extension over the tower is to be proved from the coding of the states of
the attachment (`Seed` lemmas of `VaughtConjecture.Extension.ReplicatedStateCoding`), whose values
lie in the code set `Label.codeSet #cells (m + 2)` (below `ω ^ 2`,
`Label.lt_omega0_sq_of_mem_codeSet`, and below the grid point `ω * B' + 2` once
`#cells + 1 ≤ B'`, `Label.le_gridPoint_of_mem_codeSet`).  So the general assembly
`StageType.hasReplicatedInputsAtSeed_of_towerExtension` also asks `codeSet #cells (m + 2) ⊆ Γ` and
`#cells + 1 ≤ B'`: the assembly itself does not use them; they make `StageType.TowerExtensionAtSeed`
asked only at values containing the code set.

**The choice** (`Seed.seedHeight`, `Seed.seedValues`, `Seed.seedGridBound`): `H` the number of
cells of the attachment plus one, `Γ = insert ⊥ (Γ₀ ∪ codeSet #cells (m + 2))`,
`B' = max B₀ (#cells + 1)`.  It meets every side condition
(`StageType.hasReplicatedInputsAtSeed_of_seedTowerExtension`), so the main theorem follows from
(R2) and the extension over the tower at the seed position at this choice
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_towerExtension`, through the transport of
the seed position, `StageType.HasLadderGrowthCarriersStableAtSeed.hasLadderGrowthCarriersStable`).

The statements at the seed position are asked at EVERY seed with the context as its first coatom
type and the donor as the face along the root followed by the new point (the assembly uses one
such seed).  These are implications; `StageType.HasReplicatedInputsAtSeed`,
`StageType.TowerExtensionAtSeed`, the three lift statements and the main theorem stay
conditional.

**With (R2) for receiving models.**  (R2) for receiving models is compiled
(`Realization.receivingResidualReceiving_of_padded`, in
`VaughtConjecture.MainTheorem.LowPaddedRoute`), so the main theorem follows from ONE statement,
the extension over the tower at a positive cap at the seed position
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_towerExtensionPos'`).  That statement,
`StageType.TowerExtensionPosAtSeed Seed.seedHeight Seed.seedValues Seed.seedGridBound`, is open:
it is not proved in this repository, and the main theorem stays conditional on it.

**The height sets.**  The agreement heights of the ladder tower at the grade `k` are the height
set `Scheme.heightSet Γ B' k`, the grid `grid k B'` together with the values of `Γ` self-visible
at `k` (`VaughtConjecture.Extension.BaseLadderTower`).  For the earlier ladder tower, with
agreement heights in the grid alone, `StageType.TowerExtensionPosAtSeed` at the choice of this
file is refuted (`StageType.not_towerExtensionPosAtSeed_seedChoice`, compiled outside this
library).  A statement compiled for the earlier tower is no evidence for the present one, nor is
that refutation.  For the present tower it is open.

**Dependency record** for the chain from the extension over the tower to the main theorem and its
named inputs, against the change of the height sets: (i) unchanged and recompiled against the
height sets; (ii) re-proved for the height sets with the same statement; (ii') re-proved with one
added hypothesis; (iii) the statement mentions the grid, so its interface is to be re-checked
before reuse.  Every (iii) here mentions only the grid point: the side condition
`∀ x ∈ Γ, x ≤ gridPoint 2 B'` on the values, which also bounds the heights
(`Scheme.le_gridPoint_of_mem_heightSet`), or the top `gridPoint k B'` of the height set
(`Scheme.sup_heightSet`).  No statement below names the set `grid k B'`.

| Declarations | Record |
| --- | --- |
| `MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_towerExtensionPos(')` | (i) |
| `StageType.hasReplicatedInputsAtSeed_of_seedTowerExtension(Pos)` | (i) |
| `StageType.towerExtensionAtSeed_of_pos`, `Seed.towerExtension_of_pos` | (i), (iii) |
| `StageType.hasReplicatedInputsAtSeed_of_towerExtension`, `…_of_lifts` | (i), (iii) |
| `Seed.replicatedInputs_of_lifts` | (i), (iii) |
| `StageType.hasContextLiftAtSeed_of_towerExtension` | (i) |
| `StageType.hasOntoRootCoatomLiftAtSeed_of_towerExtension` | (i) |
| `StageType.hasAttachedMixedLiftsAtSeed_of_towerExtension` | (i), (iii) |
| `StageType.HasReplicatedInputsAtSeed.hasLadderGrowthCarriersStableAtSeed` | (i) |
| `Seed.exists_ladderCarrier_of_replicatedInputs` | (i) |
| `Seed.exists_replicatedCarrier` | (ii), (iii) |
| `StageType.HasLadderGrowthCarriersStableAtSeed.hasLadderGrowthCarriersStable` | (i) |
| `MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_stableAtSeed` | (i) |
| `Seed.hasMixedCoatomLift`, `Seed.hasMixedCoatomLift_of_two` | (i), (iii) |
| `Seed.hasMixedLifts_of_attachedMixedLifts`, `Seed.hasMixedSameGradeLifts` | (i), (iii) |
| `Seed.attachedMixedLifts_one`, `Seed.hasAttachedMixedLifts_of_two` | (i), (iii) |
| `Seed.hasContextLift_of_two`, `Seed.cappedLift_context_one` | (i) |
| `Seed.cappedLift_context_of_towerExtension`, `Seed.hasContextLift_of_towerExtension` | (i) |
| `Seed.cappedLift_coatom_one_of_surjective` | (i) |
| `Seed.hasExtendingLabel_attachAdmits`, `Seed.hasExtendingLabel_of_expansion` | (i), (iii) |
| `Seed.exists_stateCode`, `Seed.exists_stateCode_capped` | (i) |
| `Scheme.LadderBaseData.exists_controller_twin_ladderTower` (adds `hΓ`) | (ii'), (iii) |
| `Scheme.exists_layerTower_controller_twin` (any height sets) | (i) |
| `Scheme.LadderBaseData.exists_controller_agree_ladderTower` | (ii) |
| `Seed.min_decode_eq_decode` | (ii), (iii) |
| `Seed.min_decode_eq_decode_one`, `Seed.decode_copyFull` | (i) |
| `GrowthCarrier.recognizes_of_ladder`, `GrowthCarrier.recovers_of_recognizes` | (i) |
| `Seed.copy_recognition` | (i) |
| `Scheme.LadderBaseData.ladderTower_lawful` | (ii), (iii) |

**The threshold against the arity of the donor.**  Calibration on the class asks only
`n + 1 ≤ Q.threshold` (`StageType.GrowthRequests.ClassCalibrated.arity`), and the chain above
covers both `n + 1 = Q.threshold` and `n + 1 < Q.threshold`: no statement on it asks
`n + 1 < Q.threshold`.  The two places where the cases differ are case splits in compiled proofs.

* The lift from a face inside the donor face (`Seed.cappedLift_donor_univ_attachAdmits`) splits on
  `k < Q.threshold`: below the threshold by the vanishing states (`Seed.attachAdmits_of_vanishing`,
  strict in `k`, any threshold); otherwise `k ≤ n + 1 ≤ Q.threshold` forces
  `k = n + 1 = Q.threshold` and the donor face, by `Seed.attachedStateLift_donor`, which is stated
  only at `Q.threshold = n + 1`.  For `n + 1 < Q.threshold` that branch is empty.
* The onto root (`Seed.hasMixedCoatomLift_of_two` splits on `Function.Surjective g`) occurs only at
  equality: `n = m` and `Q.threshold ≤ m + 1`, the grade of the cap in the context, give
  `Q.threshold = n + 1`.  Its lifts (`Seed.cappedLift_coatom_one_of_surjective`,
  `StageType.hasOntoRootCoatomLiftAtSeed_of_towerExtension`) carry no threshold hypothesis.

The other threshold hypotheses on the chain permit equality: `n + 1 ≤ N`
(`StageType.GrowthRequests.templateImage_isLawful`), `2 ≤ Q.threshold`
(`Seed.exists_replicatedCarrier`, `Seed.exists_ladderCarrier_of_replicatedInputs`, from the arity
and `0 < n`), `1 ≤ Q.threshold` (`GrowthCarrier.recognizes_of_ladder`), and the complete case
splits `Q.threshold ≤ j` (`StageType.exists_donorStep`) and `k ≤ Q.threshold` (the relative lift).

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

/-- **The values of the choice**: `⊥`, the compressed labels of the attachment, and the code set
`codeSet #cells (m + 2)` of the coding of the states of the attachment. -/
noncomputable def seedValues : Finset Label.{u} :=
  insert ⊥ (univ.image (I.compressedLabel g) ∪ codeSet (I.attachment g).card (m + 2))

/-- **The grid bound of the choice**: the larger of the number of blocks of the labels of the
attachment plus one and the number of cells of the attachment plus one. -/
noncomputable def seedGridBound : ℕ :=
  max (blockCount (I.attachLabels g) + 1) ((I.attachment g).card + 1)

theorem seedHeight_pos : 0 < I.seedHeight g := Nat.succ_pos _

theorem card_le_seedHeight : (I.attachment g).card ≤ I.seedHeight g := Nat.le_succ _

theorem bot_mem_seedValues : (⊥ : Label.{u}) ∈ I.seedValues g := mem_insert_self _ _

theorem image_compressedLabel_subset_seedValues :
    univ.image (I.compressedLabel g) ⊆ I.seedValues g :=
  subset_union_left.trans (subset_insert _ _)

theorem codeSet_subset_seedValues :
    codeSet (I.attachment g).card (m + 2) ⊆ I.seedValues g :=
  subset_union_right.trans (subset_insert _ _)

theorem card_add_one_le_seedGridBound : (I.attachment g).card + 1 ≤ I.seedGridBound g :=
  le_max_right _ _

theorem le_gridPoint_of_mem_seedValues {x : Label.{u}} (hx : x ∈ I.seedValues g) :
    x ≤ gridPoint 2 (I.seedGridBound g) := by
  rcases mem_insert.mp hx with rfl | hx
  · exact bot_le
  rcases mem_union.mp hx with hx | hx
  · obtain ⟨c, -, rfl⟩ := mem_image.mp hx
    exact compressedLabel_le_gridPoint (le_max_left _ _) c
  · exact le_gridPoint_of_mem_codeSet (card_add_one_le_seedGridBound I g) hx

theorem lt_omega0_sq_of_mem_seedValues {x : Label.{u}} (hx : x ∈ I.seedValues g) :
    x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  rcases mem_insert.mp hx with rfl | hx
  · exact WithBot.bot_lt_coe _
  rcases mem_union.mp hx with hx | hx
  · obtain ⟨c, -, rfl⟩ := mem_image.mp hx
    exact compressedLabel_lt_omega0_sq c
  · exact lt_omega0_sq_of_mem_codeSet hx

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

/-- **The lift from a face inside the donor face into the full face from the extension over the
tower** at the grade `k`, for requests calibrated on the class over a nonempty root: the state lift
from the face (`Seed.attachedStateLift_of_vanishing` below the threshold, by the vanishing states;
`Seed.attachedStateLift_donor` at the threshold, the donor face at the grade `n + 1`) and the
extension give the lift (`Seed.cappedLift_attached_univ_of_stateLift`).  This is the donor case of
`Seed.hasAttachedMixedLifts_attachAdmits`, for a single grade. -/
theorem cappedLift_donor_univ_attachAdmits {p₀ : StageType.{u} α n}
    {d : StageType.{u} α (n + 1)} (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    {V : Finset (Fin (m + 2))} (hVF : V ∈ I.amalgam.toCellScheme.faces)
    (hVD : V ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))) {k : ℕ} (hk1 : 1 ≤ k)
    (hkV : k ≤ #V) (hE : TowerExtension I g H Γ (I.attachAdmits g hd Q) B' k) :
    (I.replicated g H Γ (I.attachAdmits g hd Q) B').rows.CappedLift (X := (V, k))
      (Y := ((univ : Finset (Fin (m + 2))), k)) ⟨subset_univ _, le_rfl⟩ := by
  have hDc : #(univ.map (extendByLast (g.trans Fin.castSuccEmb))) = n + 1 := by
    rw [card_map, card_univ, Fintype.card_fin]
  have hkD : k ≤ n + 1 := hkV.trans (hDc ▸ card_le_card hVD)
  refine cappedLift_attached_univ_of_stateLift (.inr hVD) ?_ hE
  rcases Nat.lt_or_ge k Q.threshold with hkN | hkN
  · exact attachedStateLift_of_vanishing (donor_mem_faces hd) (root_mem_faces hte)
      (by rw [card_root]; omega) hVF hk1 hkV (.inr hVD)
      fun P _ hP ↦ attachAdmits_of_vanishing hd Q hkN hP _
  · have hN := hQ.arity
    have hkn : k = n + 1 := by omega
    have hVe : V = univ.map (extendByLast (g.trans Fin.castSuccEmb)) :=
      eq_of_subset_of_card_le hVD (by omega)
    subst hVe hkn
    exact attachedStateLift_donor hH hcard hΓ0 hte hn hd hQ (by omega)

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

/-! ### The extension over the tower at the seed position -/

/-- **The extension over the tower at the seed position, at the grades `2, …, m + 1`** (open),
for the choice `H`, `Γ`, `B'`: at every seed and requests as in
`StageType.HasAttachedMixedLiftsAtSeed`, the replicated scheme with the admission predicate of `Q`
has the extension over the tower (`Seed.TowerExtension`) at the grade `j`, for `2 ≤ j ≤ m + 1`:
every complete lawful state of the attachment satisfying the predicate at the grade `m + 2`, with
the observation at a cap `c` self-visible at `j` of an ambient lawful below `(univ, j)` on the
cells of the attachment below the grade, extends to a labelling lawful below `(univ, j)`, equal to
the state on the cells of the attachment and with the observation of the ambient at `c`. -/
def TowerExtensionAtSeed
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
          Seed.TowerExtension I g (H I g) (Γ I g) (I.attachAdmits g hdA Q) (B' I g) j

section TowerExtension

variable (H : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ)
  (Γ : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → Finset Label.{u})
  (B' : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ)
  {H Γ B'}

/-- **The context lift at the seed position from the extension over the tower**, for a choice
with `H` positive and at least the number of cells of the attachment and `⊥ ∈ Γ`: the state lift
holds (`Seed.contextStateLiftR_attachAdmits`, the ambient being admitted, `Seed.ambientAdmitted`),
and with the extension it gives the lift (`Seed.cappedLift_context_of_towerExtension`). -/
theorem hasContextLiftAtSeed_of_towerExtension
    (hH : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m), 0 < H I g)
    (hcard : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m),
      (I.attachment g).card ≤ H I g)
    (hΓ0 : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m), ⊥ ∈ Γ I g)
    (hE : TowerExtensionAtSeed.{u} H Γ B') : HasContextLiftAtSeed.{u} H Γ B' := by
  intro α n m I g p' hα hI hp' p hte d hd hdA hn Q hpair hQ hrel j hj hjm
  exact Seed.cappedLift_context_of_towerExtension
    (Seed.contextStateLiftR_attachAdmits hte hd.2 hd.1 hn hdA hQ hpair hrel (by omega)
      (Seed.ambientAdmitted (hH I g) (hcard I g) (hΓ0 I g) hdA hQ hn j))
    (hE I g p' hα hI hp' p hte d hd hdA hn Q hpair hQ hrel j hj hjm)

/-- **The lifts from the faces of the attachment into the mixed faces at the seed position from
the extension over the tower** (grades `k ≥ 2`), for a choice with `H` positive and at least the
number of cells of the attachment, `⊥ ∈ Γ` and `Γ` below the grid point `ω * B' + 2`: through the
full face (`Seed.cappedLift_attached_mixed_of_univ`), inside the context face by the context lift
(`Seed.hasContextLift_attachAdmits_two`), inside the donor face by the state lift
(`Seed.cappedLift_donor_univ_attachAdmits`). -/
theorem hasAttachedMixedLiftsAtSeed_of_towerExtension
    (hH : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m), 0 < H I g)
    (hcard : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m),
      (I.attachment g).card ≤ H I g)
    (hΓ0 : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m), ⊥ ∈ Γ I g)
    (hΓ : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m),
      ∀ x ∈ Γ I g, x ≤ gridPoint 2 (B' I g))
    (hE : TowerExtensionAtSeed.{u} H Γ B') : HasAttachedMixedLiftsAtSeed.{u} H Γ B' := by
  intro α n m I g p' hα hI hp' p hte d hd hdA hn Q hpair hQ hrel V U k hVF hV hU h hk hkV
  have hE' := hE I g p' hα hI hp' p hte d hd hdA hn Q hpair hQ hrel
  have hVu : #V ≤ m + 1 := by
    have hlt : V ⊂ univ := ssubset_univ_iff.mpr fun he ↦
      ((I.mem_mixedFaces g).mp hU).2.1 (univ_subset_iff.mp (he ▸ h))
    have := card_lt_card hlt
    simp only [card_univ, Fintype.card_fin] at this
    omega
  refine Seed.cappedLift_attached_mixed_of_univ (hH I g) (hcard I g) (hΓ0 I g) (hΓ I g)
    (I.attachAdmits_succ g hdA Q) (I.attachAdmits_bot g hdA Q) hU h (by omega) (hkV.trans hVu)
    (hkV.trans (card_le_card h)) ?_
  by_cases hVC : V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2))
  · exact Seed.cappedLift_attached_univ_of_context
      (Seed.hasContextLift_attachAdmits_two (hH I g) (hcard I g) (hΓ0 I g) hte hd.2 hd.1 hn hdA hQ
        hpair hrel (Seed.root_mem_faces hte) (by rw [Seed.card_root]; omega) hE')
      hVF hVC (by omega) hkV
  · exact Seed.cappedLift_donor_univ_attachAdmits (hH I g) (hcard I g) (hΓ0 I g) hte hn hdA hQ
      (Seed.faces_replicated ▸ hVF) (hV.resolve_left hVC) (by omega) hkV
      (hE' k hk (hkV.trans hVu))

/-- **The lift from the second coatom at an onto root at the seed position from the extension
over the tower**, for a choice with `H` positive and at least the number of cells of the
attachment and `⊥ ∈ Γ`: for an onto root `n = m` and the second coatom is the donor face
(`Seed.donorFace_eq_coatom_of_surjective`), so the lift is the lift from the donor face
(`Seed.cappedLift_donor_univ_attachAdmits`). -/
theorem hasOntoRootCoatomLiftAtSeed_of_towerExtension
    (hH : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m), 0 < H I g)
    (hcard : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m),
      (I.attachment g).card ≤ H I g)
    (hΓ0 : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m), ⊥ ∈ Γ I g)
    (hE : TowerExtensionAtSeed.{u} H Γ B') : HasOntoRootCoatomLiftAtSeed.{u} H Γ B' := by
  intro α n m I g p' hα hI hp' p hte d hd hdA hn Q hpair hQ hrel hg j hj hjm
  have hnm : m ≤ n := by simpa using Fintype.card_le_of_surjective g hg
  have hl := Seed.cappedLift_donor_univ_attachAdmits (hH I g) (hcard I g) (hΓ0 I g) hte hn hdA hQ
    (Seed.donor_mem_faces hdA) subset_rfl (by omega)
    (by rw [card_map, card_univ, Fintype.card_fin]; omega)
    (hE I g p' hα hI hp' p hte d hd hdA hn Q hpair hQ hrel j hj hjm)
  have key : ∀ (W : Finset (Fin (m + 2)))
      (h : ((W, j) : Finset (Fin (m + 2)) × ℕ) ≤ ((univ : Finset (Fin (m + 2))), j)),
      W = univ.map (extendByLast (g.trans Fin.castSuccEmb)) →
        (I.replicated g (H I g) (Γ I g) (I.attachAdmits g hdA Q) (B' I g)).rows.CappedLift h := by
    rintro W h rfl
    exact hl
  exact key _ _ (Seed.donorFace_eq_coatom_of_surjective g hg).symm

end TowerExtension

/-- **The extension over the tower at a positive cap at the seed position, at the grades
`2, …, m + 1`** (open), for the choice `H`, `Γ`, `B'`: as `StageType.TowerExtensionAtSeed`, with
`Seed.TowerExtensionPos` (the extension asked only at caps `c ≠ ⊥` and for states exceeding `c`
at some cell of the attachment of grade at most `j`) in place of `Seed.TowerExtension`.  At the
choice of this file it is refuted for the earlier ladder tower with agreement heights in the grid
alone (`StageType.not_towerExtensionPosAtSeed_seedChoice`, compiled outside this library), and
open for the height sets `Scheme.heightSet`. -/
def TowerExtensionPosAtSeed
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
          Seed.TowerExtensionPos I g (H I g) (Γ I g) (I.attachAdmits g hdA Q) (B' I g) j

/-- **The extension over the tower at the seed position from its case at a positive cap**, for a
choice with `H` positive and at least the number of cells of the attachment, `Γ` below the grid
point `ω * B' + 2` and containing the code set `codeSet #cells (m + 2)`
(`Seed.towerExtension_of_pos`). -/
theorem towerExtensionAtSeed_of_pos
    {H : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ}
    {Γ : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → Finset Label.{u}}
    {B' : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ}
    (hH : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m), 0 < H I g)
    (hcard : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m),
      (I.attachment g).card ≤ H I g)
    (hΓ : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m),
      ∀ x ∈ Γ I g, x ≤ gridPoint 2 (B' I g))
    (hcode : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m),
      codeSet (I.attachment g).card (m + 2) ⊆ Γ I g)
    (hE : TowerExtensionPosAtSeed.{u} H Γ B') : TowerExtensionAtSeed.{u} H Γ B' := by
  intro α n m I g p' hα hI hp' p hte d hd hdA hn Q hpair hQ hrel j hj hjm
  exact Seed.towerExtension_of_pos (hH I g) (hcard I g) (hΓ I g) hdA hQ (hcode I g) (by omega)
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
  have hdF := Seed.donor_mem_faces hdA
  have hrF := Seed.root_mem_faces hte
  have hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb))) := by rw [Seed.card_root]; omega
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
the choice** `Seed.seedHeight`, `Seed.seedValues`, `Seed.seedGridBound`, which meets every side
condition of
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

/-- **The inputs of the replicated scheme at the seed position from the extension over the
tower**, for a choice `H`, `Γ`, `B'` with the side conditions of
`StageType.hasReplicatedInputsAtSeed_of_lifts`: the three lift statements follow from it
(`StageType.hasAttachedMixedLiftsAtSeed_of_towerExtension`,
`StageType.hasContextLiftAtSeed_of_towerExtension`,
`StageType.hasOntoRootCoatomLiftAtSeed_of_towerExtension`).  The two further side conditions,
the code set `codeSet #cells (m + 2)` inside `Γ` and `#cells + 1 ≤ B'`, are not used by the
assembly: they are asked so that the extension over the tower is asked only at values containing
the code set of the coding of the states (`VaughtConjecture.Extension.ReplicatedStateCoding`). -/
theorem hasReplicatedInputsAtSeed_of_towerExtension
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
    (_hcode : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m),
      codeSet (I.attachment g).card (m + 2) ⊆ Γ I g)
    (_hB : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m),
      (I.attachment g).card + 1 ≤ B' I g)
    (hE : TowerExtensionAtSeed.{u} H Γ B') : HasReplicatedInputsAtSeed.{u} :=
  hasReplicatedInputsAtSeed_of_lifts H Γ B' hH hcard hΓ0 hΓ hΓω hsub
    (hasAttachedMixedLiftsAtSeed_of_towerExtension hH hcard hΓ0 hΓ hE)
    (hasContextLiftAtSeed_of_towerExtension hH hcard hΓ0 hE)
    (hasOntoRootCoatomLiftAtSeed_of_towerExtension hH hcard hΓ0 hE)

/-- **The inputs of the replicated scheme at the seed position from the extension over the tower
at the choice** `H = #cells + 1`, `Γ = insert ⊥ (Γ₀ ∪ codeSet #cells (m + 2))`,
`B' = max B₀ (#cells + 1)` (`Seed.seedHeight`, `Seed.seedValues`, `Seed.seedGridBound`), which
meets every side condition, the code set and its grid bound included. -/
theorem hasReplicatedInputsAtSeed_of_seedTowerExtension
    (hE : TowerExtensionAtSeed.{u} Seed.seedHeight Seed.seedValues Seed.seedGridBound) :
    HasReplicatedInputsAtSeed.{u} :=
  hasReplicatedInputsAtSeed_of_towerExtension _ _ _ Seed.seedHeight_pos Seed.card_le_seedHeight
    Seed.bot_mem_seedValues (fun I g _ hx ↦ I.le_gridPoint_of_mem_seedValues g hx)
    (fun I g _ hx ↦ I.lt_omega0_sq_of_mem_seedValues g hx)
    Seed.image_compressedLabel_subset_seedValues Seed.codeSet_subset_seedValues
    Seed.card_add_one_le_seedGridBound hE

/-- **The inputs of the replicated scheme at the seed position from the extension over the tower
at a positive cap**, for a choice with the side conditions of
`StageType.hasReplicatedInputsAtSeed_of_towerExtension`; here the code set inside `Γ` is used
(`StageType.towerExtensionAtSeed_of_pos`). -/
theorem hasReplicatedInputsAtSeed_of_towerExtensionPos
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
    (hcode : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m),
      codeSet (I.attachment g).card (m + 2) ⊆ Γ I g)
    (hB : ∀ {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m),
      (I.attachment g).card + 1 ≤ B' I g)
    (hE : TowerExtensionPosAtSeed.{u} H Γ B') : HasReplicatedInputsAtSeed.{u} :=
  hasReplicatedInputsAtSeed_of_towerExtension H Γ B' hH hcard hΓ0 hΓ hΓω hsub hcode hB
    (towerExtensionAtSeed_of_pos hH hcard hΓ hcode hE)

/-- **The inputs of the replicated scheme at the seed position from the extension over the tower
at a positive cap, at the choice** `Seed.seedHeight`, `Seed.seedValues`, `Seed.seedGridBound`. -/
theorem hasReplicatedInputsAtSeed_of_seedTowerExtensionPos
    (hE : TowerExtensionPosAtSeed.{u} Seed.seedHeight Seed.seedValues Seed.seedGridBound) :
    HasReplicatedInputsAtSeed.{u} :=
  hasReplicatedInputsAtSeed_of_seedTowerExtension
    (towerExtensionAtSeed_of_pos Seed.seedHeight_pos Seed.card_le_seedHeight
      (fun I g _ hx ↦ I.le_gridPoint_of_mem_seedValues g hx) Seed.codeSet_subset_seedValues hE)

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

/-- **The main theorem from (R2) and the extension over the tower at the seed position** (both
hypotheses open): `StageType.TowerExtensionAtSeed` at the grades `2, …, m + 1`, at the choice
`Seed.seedHeight`, `Seed.seedValues`, `Seed.seedGridBound`.  Through
`StageType.hasReplicatedInputsAtSeed_of_seedTowerExtension`,
`StageType.HasReplicatedInputsAtSeed.hasLadderGrowthCarriersStableAtSeed` and the transport
`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_stableAtSeed`. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_towerExtension
    (hres : ReceivingResidualReceiving.{0, 0})
    (hE : TowerExtensionAtSeed.{0} Seed.seedHeight Seed.seedValues Seed.seedGridBound) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_stableAtSeed hres
    (hasReplicatedInputsAtSeed_of_seedTowerExtension hE).hasLadderGrowthCarriersStableAtSeed

/-- **The main theorem from (R2) and the extension over the tower at a positive cap at the seed
position** (both hypotheses open): `StageType.TowerExtensionPosAtSeed` at the grades
`2, …, m + 1`, at the choice `Seed.seedHeight`, `Seed.seedValues`, `Seed.seedGridBound`.  Through
`StageType.hasReplicatedInputsAtSeed_of_seedTowerExtensionPos`. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_towerExtensionPos
    (hres : ReceivingResidualReceiving.{0, 0})
    (hE : TowerExtensionPosAtSeed.{0} Seed.seedHeight Seed.seedValues Seed.seedGridBound) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_stableAtSeed hres
    (hasReplicatedInputsAtSeed_of_seedTowerExtensionPos hE).hasLadderGrowthCarriersStableAtSeed

/-- **The main theorem from the extension over the tower at a positive cap at the seed position**
(one hypothesis, open): `StageType.TowerExtensionPosAtSeed` at the grades `2, …, m + 1`, at the
choice `Seed.seedHeight`, `Seed.seedValues`, `Seed.seedGridBound`.  (R2) for receiving models is
`Realization.receivingResidualReceiving_of_padded`; the rest is
`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_towerExtensionPos`.  The hypothesis is not
proved here, so the thin `ℵ₁` spectrum stays conditional on it.  For the earlier ladder tower,
with agreement heights in the grid alone, the hypothesis is refuted
(`StageType.not_towerExtensionPosAtSeed_seedChoice`, compiled outside this library); for the
height sets `Scheme.heightSet` it is open. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_towerExtensionPos'
    (hE : TowerExtensionPosAtSeed.{0} Seed.seedHeight Seed.seedValues Seed.seedGridBound) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_towerExtensionPos
    receivingResidualReceiving_of_padded hE

end MainTheorem

end VaughtConjecture
