/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.BlockCompress
import VaughtConjecture.MainTheorem.ReplicatedInputs
import VaughtConjecture.Extension.ReplicatedWriting

/-!
# A lawful labelling of the replicated scheme extending the labels of the attachment

Roadmap, Layer 3 ((R3) and (R4), the labelling input of the replicated carrier).

The input `Seed.HasExtendingLabel` of the replicated scheme asks for a lawful section of the
replicated scheme that is the labelling of the attachment on its cells.  The labels of the
attachment may lie above `ω ^ 2`, so they are not themselves a state of the catalogue of the
ladder tower (whose values lie in a finite set below `ω ^ 2`).  They are the **block expansion**
of a state of the catalogue:

* the **compressed labelling** of the attachment (`Seed.compressedLabel`): the block compression
  (`Label.blockCompress`) of the labels of the attachment at the grade `m + 2`.  It is lawful on
  the attachment (`Seed.isLawful_compressedLabel`: the compression is a witness bounded by every
  grade of the attachment, sending no label of the attachment to `⊥` unless it is `⊥`), it lies
  below `ω ^ 2` and below the grid point `ω * B' + 2` once `B'` exceeds the number of blocks of the
  labels (`Seed.compressedLabel_lt_omega0_sq`, `Seed.compressedLabel_le_gridPoint`), and it is
  admitted by the requests at every grade (`Seed.attachAdmits_compressedLabel`), when the labels
  pair is admitted and the requests are calibrated on the class: the relation of the requests is
  carried by the compression (`StageType.GrowthRequests.CorrectAt.map`), and the truncation at the
  threshold changes no read (the cap, references, marker and donor cells have grade at most the
  threshold);
* the expansion of its writing in the replicated scheme is lawful and is the labelling of the
  attachment on its cells (`Seed.hasExtendingLabel_of_expansion`: the expansion is a witness at
  every grade sending only `⊥` to `⊥`, so it keeps the writing of a state of the catalogue lawful,
  and it inverts the compression on the labels).

**Result** (`Seed.hasExtendingLabel_attachAdmits`): for the admission predicate of requests
calibrated on the class with the labels pair admitted, the replicated scheme has a lawful
labelling extending the labels of the attachment, for every height `H > 0` bounding the cells of
the attachment and every finite set `Γ` of values containing the compressed labels with every value
at most the grid point `ω * B' + 2`.  The values to add to `Γ` are explicit and bounded
(`Seed.exists_hasExtendingLabel_attachAdmits`).  With the lifts, this gives the inputs of the
replicated scheme (`Seed.replicatedInputs_of_lifts`); the lifts are separate inputs.

## References

Lawful sections are [Kni26, Definition 2.5.4]; visibility replacement is
[Kni26, Definition 2.2.3]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-! ### A lawful labelling from a state of the catalogue and an expansion -/

/-- **A lawful labelling extending the labels of the attachment from a state of the catalogue**:
if a witness `ν` bounded by the grade `m + 1` and sending only `⊥` to `⊥` reads a state `R` of the
catalogue at the grade `m + 2` as the labels of the attachment, then `ν` applied to the writing of
`R` in the replicated scheme is a lawful labelling extending the labels of the attachment. -/
theorem hasExtendingLabel_of_expansion (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    {R : Fin (I.attachment g).card → Label.{u}}
    (hR : R ∈ (I.attachmentBase g).towerCat Γ A (m + 2)) {ν : Label.{u} → Label.{u}}
    (hν : IsWitness (stepSuppressor (m + 1)) ν) (hbot : ∀ x, ν x = ⊥ → x = ⊥)
    (hRν : ∀ c, ν (R c) = (I.attachmentType g).label c) :
    I.HasExtendingLabel g H Γ A B' :=
  ⟨fun z ↦ ν (I.replicatedWriting g H Γ A B' R z),
    (isLawful_replicatedWriting hH hcard hΓ hA hR).map_of_apply_eq_bot
      (fun d ↦ Nat.lt_succ_iff.mp (grade_lt_replicated d)) hν fun _ h ↦ hbot _ h,
    fun c ↦ by
      change ν (I.replicatedWriting g H Γ A B' R (I.attachEmb g H Γ A B' c)) = _
      rw [replicatedWriting_attachEmb hcard
        (Scheme.LadderBaseData.mem_towerCat.mp hR).2.1 c]
      exact hRν c⟩

/-! ### The compressed labelling of the attachment -/

variable (I g) in
/-- The labels of the attachment. -/
noncomputable def attachLabels : Finset Label.{u} := univ.image (I.attachmentType g).label

theorem label_mem_attachLabels (c : Fin (I.attachment g).card) :
    (I.attachmentType g).label c ∈ I.attachLabels g :=
  mem_image_of_mem _ (mem_univ c)

variable (I g) in
/-- **The compressed labelling of the attachment**: the block compression of its labels at the
grade `m + 2`. -/
noncomputable def compressedLabel (c : Fin (I.attachment g).card) : Label.{u} :=
  blockCompress (I.attachLabels g) (m + 2) ((I.attachmentType g).label c)

/-- **The compressed labelling is lawful on the attachment.** -/
theorem isLawful_compressedLabel : (I.attachment g).rows.IsLawful (I.compressedLabel g) :=
  (I.attachmentType g).isLawful.map_of_bot_iff (I.attachmentType g).isLawful
    (fun d ↦ (I.attachmentType g).grade_le d) (isWitness_blockCompress (m + 2))
    fun d ↦ blockCompress_eq_bot_iff (label_mem_attachLabels d) (m + 2)

/-- **The expansion reads the compressed labelling as the labels of the attachment.** -/
theorem blockExpand_compressedLabel (c : Fin (I.attachment g).card) :
    blockExpand (I.attachLabels g) (I.compressedLabel g c) = (I.attachmentType g).label c :=
  blockExpand_blockCompress (label_mem_attachLabels c) (m + 2)

theorem compressedLabel_lt_omega0_sq (c : Fin (I.attachment g).card) :
    I.compressedLabel g c < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) :=
  blockCompress_lt_omega0_sq (label_mem_attachLabels c) (m + 2)

/-- **The compressed labelling lies below the grid point `ω * B' + 2`** once `B'` exceeds the
number of blocks of the labels of the attachment. -/
theorem compressedLabel_le_gridPoint (hB : blockCount (I.attachLabels g) + 1 ≤ B')
    (c : Fin (I.attachment g).card) : I.compressedLabel g c ≤ gridPoint 2 B' := by
  refine (blockCompress_lt (label_mem_attachLabels c) (m + 2)).le.trans ?_
  rw [gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe]
  exact ((omega0_mul_natCast_le_iff.mpr hB).trans le_self_add)

/-! ### Admission of the compressed labelling -/

variable {d : StageType.{u} α (n + 1)}
  (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)

/-- The cell of the attachment at a cell of the context is its face cell. -/
theorem attachCtxCell_eq (x : Fin I.left.card) :
    I.attachCtxCell g x = (I.attachmentType g).faceCell (I.restrictFace_left_attachmentType g) x :=
  rfl

/-- The cell of the attachment at a cell of the donor is its face cell. -/
theorem attachDonCell_eq (j : Fin d.card) :
    I.attachDonCell g hd j =
      (I.attachmentType g).faceCell (I.restrictFace_donor_attachmentType g hd) j :=
  rfl

/-- **The compressed labelling is admitted** by requests calibrated on the class with the labels
pair admitted, at every grade. -/
theorem attachAdmits_compressedLabel {p : StageType.{u} α n}
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p}
    {Q : GrowthRequests I.left d.toScheme} (hpair : ∀ j, Q.CorrectAt I.left.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (k : ℕ) : I.attachAdmits g hd Q k (I.compressedLabel g) := by
  intro _ _ _ j
  set θ := blockCompress (I.attachLabels g) (m + 2) with hθdef
  have hθ : IsWitness (stepSuppressor (m + 2)) θ := isWitness_blockCompress (m + 2)
  have hthr : Q.threshold ≤ m + 2 := (I.left.grade_le Q.cap).trans (Nat.le_succ _)
  have hθv : ∀ i ≤ Q.threshold, ∀ x, θ (visibilityReplace Q.threshold i x) =
      visibilityReplace Q.threshold i (θ x) := fun i hi x ↦
    hθ.visibilityReplace_comm x _ (by rw [stepSuppressor_of_le hthr]; exact le_top) i hi
  have hmap := (hpair j).map hθ.monotone hθ.map_bot hθv (fun hf ↦ (hQ.ref j hf).2.1)
    hQ.marker.2.1
  have hctx : ∀ x, I.left.toCellScheme.grade x ≤ Q.threshold →
      I.attachHatAt g Q.threshold (I.compressedLabel g) (I.attachCtxCell g x) =
        θ (I.left.label x) := fun x hx ↦ by
    rw [attachHatAt, attachCtxCell_eq]
    change (if (I.attachmentType g).toCellScheme.grade _ ≤ _ then _ else _) = _
    rw [StageType.grade_faceCell, ite_eq_left hx]
    change θ ((I.attachmentType g).label _) = _
    rw [StageType.label_faceCell]
  have hdon : I.attachHatAt g Q.threshold (I.compressedLabel g) (I.attachDonCell g hd j) =
      θ (d.label j) := by
    rw [attachHatAt, attachDonCell_eq]
    change (if (I.attachmentType g).toCellScheme.grade _ ≤ _ then _ else _) = _
    rw [StageType.grade_faceCell, ite_eq_left ((d.grade_le j).trans hQ.arity)]
    change θ ((I.attachmentType g).label _) = _
    rw [StageType.label_faceCell]
  change Q.CorrectAt (fun x ↦ _) j
    (I.attachHatAt g Q.threshold (I.compressedLabel g) (I.attachDonCell g hd j))
  rw [hdon]
  exact hmap.congr (hctx _ le_rfl).symm (fun hf ↦ (hctx _ (hQ.ref j hf).1).symm)
    (hctx _ hQ.marker.1).symm

/-! ### The extending lawful labelling -/

/-- **The replicated scheme has a lawful labelling extending the labels of the attachment**, for
the admission predicate of requests calibrated on the class with the labels pair admitted, every
height `H > 0` bounding the cells of the attachment, and every finite set `Γ` of values at most
the grid point `ω * B' + 2` containing the compressed labelling: the expansion of the writing of
the compressed labelling. -/
theorem hasExtendingLabel_attachAdmits {p : StageType.{u} α n}
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p}
    {Q : GrowthRequests I.left d.toScheme} (hpair : ∀ j, Q.CorrectAt I.left.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hsub : ∀ c, I.compressedLabel g c ∈ Γ) :
    I.HasExtendingLabel g H Γ (I.attachAdmits g hd Q) B' :=
  hasExtendingLabel_of_expansion hH hcard hΓ (I.attachAdmits_succ g hd Q)
    (Scheme.LadderBaseData.mem_towerCat.mpr
      ⟨hsub, isLawful_compressedLabel, attachAdmits_compressedLabel hd hpair hQ _⟩)
    (isWitness_blockExpand (m + 1)) (fun _ h ↦ blockExpand_eq_bot_iff.mp h)
    blockExpand_compressedLabel

/-- **The values to add**: a finite set `Γ₀` of values below `ω ^ 2` and at most a grid point
`ω * B₀ + 2` such that the replicated scheme has a lawful labelling extending the labels of the
attachment for every finite set `Γ ⊇ Γ₀` of values at most a grid point `ω * B' + 2`. -/
theorem exists_hasExtendingLabel_attachAdmits {p : StageType.{u} α n}
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p}
    {Q : GrowthRequests I.left d.toScheme} (hpair : ∀ j, Q.CorrectAt I.left.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) :
    ∃ (Γ₀ : Finset Label.{u}) (B₀ : ℕ),
      (∀ x ∈ Γ₀, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})) ∧
      (∀ x ∈ Γ₀, x ≤ gridPoint 2 B₀) ∧
      ∀ (H : ℕ) (Γ : Finset Label.{u}) (B' : ℕ), 0 < H → (I.attachmentBase g).S.card ≤ H →
        Γ₀ ⊆ Γ → (∀ x ∈ Γ, x ≤ gridPoint 2 B') →
          I.HasExtendingLabel g H Γ (I.attachAdmits g hd Q) B' := by
  classical
  refine ⟨univ.image (I.compressedLabel g), blockCount (I.attachLabels g) + 1,
    fun x hx ↦ ?_, fun x hx ↦ ?_, fun H Γ B' hH hcard hsub hΓ ↦
      hasExtendingLabel_attachAdmits hd hpair hQ hH hcard hΓ fun c ↦
        hsub (mem_image_of_mem _ (mem_univ c))⟩
  · obtain ⟨c, -, rfl⟩ := mem_image.mp hx
    exact compressedLabel_lt_omega0_sq c
  · obtain ⟨c, -, rfl⟩ := mem_image.mp hx
    exact compressedLabel_le_gridPoint le_rfl c

/-- **The inputs of the replicated scheme from the lifts**: for requests calibrated on the class
with the labels pair admitted, a height, a finite set `Γ` of values containing `⊥` and the
compressed labelling, and a grid bound, the three lift inputs give the inputs of the replicated
scheme; the lawful labelling extending the labels is `Seed.hasExtendingLabel_attachAdmits`. -/
theorem replicatedInputs_of_lifts {p : StageType.{u} α n}
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p}
    {Q : GrowthRequests I.left d.toScheme} (hpair : ∀ j, Q.CorrectAt I.left.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hH : 0 < H) (hcard : (I.attachment g).card ≤ H) (hΓ0 : ⊥ ∈ Γ)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hΓω : ∀ x ∈ Γ, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hsub : ∀ c, I.compressedLabel g c ∈ Γ)
    (hmixed : I.HasMixedLifts g H Γ (I.attachAdmits g hd Q) B')
    (hctx : I.HasContextLift g H Γ (I.attachAdmits g hd Q) B')
    (hmc : I.HasMixedCoatomLift g H Γ (I.attachAdmits g hd Q) B') :
    I.ReplicatedInputs g hd Q :=
  ⟨H, Γ, B', hH, hcard, hΓ0, hΓ, hΓω, hmixed, hctx, hmc,
    hasExtendingLabel_attachAdmits hd hpair hQ hH hcard hΓ hsub⟩

end Seed

end VaughtConjecture
