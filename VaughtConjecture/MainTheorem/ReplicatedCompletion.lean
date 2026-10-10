/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AttachmentMirror
import VaughtConjecture.Continuation.GrowthStableRelativeLift

/-!
# The completion of the replicated scheme

Roadmap, Layer 3 ((R3) and (R4), the assembly of the recognizing growth carrier).

The replicated scheme over the attachment (`Seed.replicated`) has cells of proper scope that are
not cells of the amalgam (the copies at the mixed faces), so it is not a completion below the full
grade of the seed; it is completed directly by adding the apex (`StageType.addApex`).

* **The admission predicate through the attachment** (`Seed.attachAdmits`): from the threshold
  on, the truncation of a state of the attachment at the threshold, read on the context and donor
  cells of the attachment (`Seed.attachCtxCell`, `Seed.attachDonCell`), is admitted on the exact
  class.
* **Bountifulness from the lifts** (`Seed.isBountiful_replicated_of_lifts`): below a pair whose
  face lies in the context face or the donor face the replicated scheme is the attachment, hence
  the amalgam (bountiful); the remaining lifts are those into the mixed faces and from the two
  coatoms into the full faces (open inputs).
* **The completion** (`Seed.replicatedCompletion`): the replicated scheme with a lawful labelling
  extending the labels of the attachment, reduced to the stage, with the apex added.  It is legal
  (`Seed.isLegal_replicatedCompletion`), its context face is the first coatom type and its donor
  face the donor, literally, labels included (`Seed.restrictFace_left_replicatedCompletion`,
  `Seed.restrictFace_donor_replicatedCompletion`).

## References

The completion of [Kni26, Definition 4.3.14]; the amalgam is [Kni26, Definition 4.3.1].
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m)
  {d : StageType.{u} α (n + 1)}
  (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)

/-! ### The admission predicate through the attachment -/

/-- The context face of the attachment is the first coatom type, as schemes. -/
theorem comap_left_attachment_scheme :
    (I.attachment g).comap Fin.castSuccEmb = I.left.toScheme :=
  (I.comap_left_attachment g).trans
    (congrArg StageType.toScheme ((restrictFace_eq_some_iff _ _).mp I.restrictFace_left).2)

include hd in
/-- The donor face of the attachment is the donor, as schemes. -/
theorem comap_donor_attachment_scheme :
    (I.attachment g).comap (extendByLast (g.trans Fin.castSuccEmb)) = d.toScheme :=
  (I.comap_donor_attachment g).trans
    (congrArg StageType.toScheme ((restrictFace_eq_some_iff _ _).mp hd).2)

/-- The cell of the attachment at a cell of the context. -/
noncomputable def attachCtxCell (x : Fin I.left.card) : Fin (I.attachment g).card :=
  (I.attachment g).faceCell Fin.castSuccEmb (I.comap_left_attachment_scheme g) x

/-- The cell of the attachment at a cell of the donor. -/
noncomputable def attachDonCell (j : Fin d.card) : Fin (I.attachment g).card :=
  (I.attachment g).faceCell (extendByLast (g.trans Fin.castSuccEmb))
    (I.comap_donor_attachment_scheme g hd) j

/-- The cell of the attachment at a cell of the context is its face cell. -/
theorem attachCtxCell_eq (x : Fin I.left.card) :
    I.attachCtxCell g x = (I.attachmentType g).faceCell (I.restrictFace_left_attachmentType g) x :=
  rfl

/-- The cell of the attachment at a cell of the donor is its face cell. -/
theorem attachDonCell_eq (j : Fin d.card) :
    I.attachDonCell g hd j =
      (I.attachmentType g).faceCell (I.restrictFace_donor_attachmentType g hd) j :=
  rfl

/-- The **truncation at the grade `N`** of a state of the attachment: its values at the cells of
grade at most `N`, `⊥` above. -/
noncomputable def attachHatAt (N : ℕ) (R : Fin (I.attachment g).card → Label.{u})
    (c : Fin (I.attachment g).card) : Label.{u} :=
  if (I.attachment g).toCellScheme.grade c ≤ N then R c else ⊥

/-- The **admission predicate of the ladder tower over the attachment** for requests `Q`: from
the threshold on, the truncation of the state at the threshold, read on the context and donor
cells of the attachment, is admitted on the exact class. -/
def attachAdmits (Q : GrowthRequests I.left d.toScheme) (k : ℕ)
    (R : Fin (I.attachment g).card → Label.{u}) : Prop :=
  Q.threshold ≤ k → Q.AdmitsOnClass (fun x ↦ I.attachHatAt g Q.threshold R (I.attachCtxCell g x))
    (fun j ↦ I.attachHatAt g Q.threshold R (I.attachDonCell g hd j))

theorem attachAdmits_succ (Q : GrowthRequests I.left d.toScheme) (k : ℕ)
    (R : Fin (I.attachment g).card → Label.{u}) (h : I.attachAdmits g hd Q (k + 3) R) :
    I.attachAdmits g hd Q (k + 2) R :=
  fun hk ↦ h (by omega)

/-- The bottom state is admitted: its cap value is `⊥`. -/
theorem attachAdmits_bot (Q : GrowthRequests I.left d.toScheme) (k : ℕ) :
    I.attachAdmits g hd Q k fun _ ↦ ⊥ := fun _ _ hcap ↦
  absurd (by simp only [attachHatAt, ite_self]) hcap

/-! ### Bountifulness from the lifts -/

variable {I g} {H : ℕ} {Γ : Finset Label.{u}}
  {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- **Below a pair whose face lies in the context face or the donor face, the replicated scheme
lifts capped**: there it is the attachment, which is the amalgam. -/
theorem cappedLift_replicated_of_subset {X Y : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ (I.replicated g H Γ A B').toCellScheme.gradedFaces)
    (hY : Y ∈ (I.replicated g H Γ A B').toCellScheme.gradedFaces) (h : X ≤ Y)
    (hYc : Y.1 ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      Y.1 ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))) :
    (I.replicated g H Γ A B').rows.CappedLift h := by
  -- the attachment is a source prefix of the replicated scheme at `Y`
  have hpre : (I.attachment g).toCellScheme.IsSourcePrefix
      (I.replicated g H Γ A B').toCellScheme (I.attachEmb g H Γ A B') Y :=
    ⟨isLowerEmbedding_attachEmb, scope_attachEmb, fun z hz ↦ mem_range_attachEmb z
      (hYc.imp (fun h' ↦ hz.1.trans h') fun h' ↦ hz.1.trans h')⟩
  -- the attachment is a source prefix of the amalgam at `Y`
  have hpreA : (I.attachment g).toCellScheme.IsSourcePrefix I.amalgam.toCellScheme
      (I.amalgam.toScheme.lowerEmb (I.attachmentCells g)) Y :=
    ⟨Scheme.isLowerEmbedding_lowerEmb _ _ (I.attachmentCells_lower g), fun _ ↦ rfl,
      fun c hc ↦ by
        have hcL : c ∈ I.attachmentCells g := (I.mem_attachmentCells g).mpr
          (hYc.imp (fun h' ↦ hc.1.trans h') fun h' ↦ hc.1.trans h')
        have h' := ((I.attachmentCells g).range_orderEmbOfFin rfl).symm ▸ (mem_coe.mpr hcL)
        exact h'⟩
  have hgf {Z : Finset (Fin (m + 2)) × ℕ}
      (hZ : Z ∈ (I.replicated g H Γ A B').toCellScheme.gradedFaces) :
      Z ∈ I.amalgam.toCellScheme.gradedFaces := ⟨faces_replicated ▸ hZ.1, hZ.2⟩
  rw [← hpre.cappedLift_iff h le_rfl, comap_rows_attachEmb]
  exact (hpreA.cappedLift_iff (R := I.amalgam.rows) h le_rfl).mpr
    (I.isBountiful (hgf hX) (hgf hY) h)

/-- **The replicated scheme is bountiful** given the lifts into the mixed faces and the lifts from
the two coatoms into the full faces of the grades `1, …, m + 1`. -/
theorem isBountiful_replicated_of_lifts
    (hmixed : ∀ ⦃X Y : Finset (Fin (m + 2)) × ℕ⦄,
      X ∈ (I.replicated g H Γ A B').toCellScheme.gradedFaces →
      Y ∈ (I.replicated g H Γ A B').toCellScheme.gradedFaces → ∀ h : X ≤ Y,
      Y.1 ∈ I.mixedFaces g → (I.replicated g H Γ A B').rows.CappedLift h)
    (hlift : ∀ x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))),
      ∀ j, 1 ≤ j → j ≤ m + 1 →
        (I.replicated g H Γ A B').rows.CappedLift (X := (univ.erase x, j))
          (Y := ((univ : Finset (Fin (m + 2))), j)) ⟨erase_subset _ _, le_rfl⟩) :
    (I.replicated g H Γ A B').rows.IsBountiful := by
  classical
  have hproper : ∀ ⦃X Y : Finset (Fin (m + 2)) × ℕ⦄,
      X ∈ (I.replicated g H Γ A B').toCellScheme.gradedFaces →
      Y ∈ (I.replicated g H Γ A B').toCellScheme.gradedFaces → ∀ h : X ≤ Y, Y.1 ≠ univ →
      (I.replicated g H Γ A B').rows.CappedLift h := by
    intro X Y hX hY h hYu
    by_cases hYc : Y.1 ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
        Y.1 ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))
    · exact cappedLift_replicated_of_subset hX hY h hYc
    · push Not at hYc
      exact hmixed hX hY h ((I.mem_mixedFaces g).mpr
        ⟨faces_replicated ▸ hY.1, hYu, hYc.1, hYc.2⟩)
  have hfull (x : Fin (m + 2)) (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} :
      Finset (Fin (m + 2)))) :
      ∀ j ≤ #(univ.erase x), (I.replicated g H Γ A B').rows.CappedLift (X := (univ.erase x, j))
        (Y := ((univ : Finset (Fin (m + 2))), j)) ⟨erase_subset _ _, le_rfl⟩ := by
    intro j hj
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at hj
    rcases Nat.lt_or_ge j 1 with hj1 | hj1
    · have hj0 : j = 0 := by omega
      subst hj0
      refine CellScheme.Rows.cappedLift_of_below_eq_empty ?_ _
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hz
      have h1 : (I.replicated g H Γ A B').toCellScheme.grade z ≤ 0 := hz.2
      have h2 := (isWellFormed_replicated (I := I) (g := g) (H := H) (Γ := Γ) (A := A)
        (B' := B')).isWellFormed.grade_pos z
      omega
    · exact hlift x hx j hj1 (by omega)
  have hleftF : univ.erase (Fin.last (m + 1)) ∈ (I.replicated g H Γ A B').toCellScheme.faces := by
    rw [faces_replicated, ← Coatom.univ_map_left]
    exact ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left).1
  have hrightF :
      univ.erase (Fin.castSucc (Fin.last m)) ∈ (I.replicated g H Γ A B').toCellScheme.faces := by
    rw [faces_replicated, ← Coatom.univ_map_right]
    exact ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_right).1
  refine CellScheme.Rows.isBountiful_of_coatoms (A := univ) (mem_univ (Fin.last (m + 1)))
    (mem_univ (Fin.castSucc (Fin.last m))) (fun B hB hBu ↦ ?_) hleftF hrightF hproper
    (hfull _ (by simp)) (hfull _ (by simp))
  exact I.subset_or_subset B (faces_replicated ▸ hB) hBu

/-! ### The completion -/

/-- **The replicated scheme is legal below the full grade**, given its bountifulness. -/
theorem isLegalBelowFullGrade_replicated (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hΓω : ∀ x ∈ Γ, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hA : ∀ k R, A (k + 3) R → A (k + 2) R) (hA0 : ∀ k, A k fun _ ↦ ⊥)
    (hbount : (I.replicated g H Γ A B').rows.IsBountiful) :
    (I.replicated g H Γ A B').IsLegalBelowFullGrade where
  isWellFormed := isWellFormed_replicated
  isCoded := isCoded_replicated hcard hΓω hA
  isConsistent := isConsistent_replicated hH hcard hΓ hA
  isBountiful := hbount
  grade_lt := grade_lt_replicated
  exists_gradedIndex_eq _ hX hX2 := exists_gradedIndex_replicated hH
    (fun _ ↦ ⟨fun _ ↦ ⊥, Scheme.LadderBaseData.mem_towerCat.mpr
      ⟨fun _ ↦ hΓ0, CellScheme.Rows.isLawful_const_bot, hA0 _⟩⟩) hX hX2

variable (hα : Order.IsSuccPrelimit α)

/-- The replicated scheme with a lawful labelling, reduced to the stage, as a stage type. -/
noncomputable def replicatedType (hL : (I.replicated g H Γ A B').IsLegalBelowFullGrade)
    {q : Fin (I.replicated g H Γ A B').card → Label.{u}}
    (hq : (I.replicated g H Γ A B').rows.IsLawful q) : StageType.{u} α (m + 2) where
  toScheme := I.replicated g H Γ A B'
  label z := Label.reduce α (q z)
  isWellFormed := hL.isWellFormed
  isCoded := hL.isCoded
  isLawful := hq.reduce hα
  atStage _ := atStage_reduce α _

theorem isLegalBelowFullGrade_replicatedType
    (hL : (I.replicated g H Γ A B').IsLegalBelowFullGrade)
    {q : Fin (I.replicated g H Γ A B').card → Label.{u}}
    (hq : (I.replicated g H Γ A B').rows.IsLawful q) :
    (replicatedType hα hL hq).IsLegalBelowFullGrade := hL

/-- **The completion of the replicated scheme**: the replicated scheme with a lawful labelling
reduced to the stage, and the apex added. -/
noncomputable def replicatedCompletion (hL : (I.replicated g H Γ A B').IsLegalBelowFullGrade)
    {q : Fin (I.replicated g H Γ A B').card → Label.{u}}
    (hq : (I.replicated g H Γ A B').rows.IsLawful q) : StageType.{u} α (m + 2) :=
  (replicatedType hα hL hq).addApex hL (Nat.succ_pos _)

theorem isLegal_replicatedCompletion (hL : (I.replicated g H Γ A B').IsLegalBelowFullGrade)
    {q : Fin (I.replicated g H Γ A B').card → Label.{u}}
    (hq : (I.replicated g H Γ A B').rows.IsLawful q) :
    (replicatedCompletion hα hL hq).IsLegal :=
  StageType.isLegal_addApex _ _

/-- The faces of the completion along a proper face whose visible cells are cells of the
attachment are those of the attachment, labels included, for a labelling extending the labels of
the attachment. -/
theorem restrictFace_replicatedCompletion (hL : (I.replicated g H Γ A B').IsLegalBelowFullGrade)
    {q : Fin (I.replicated g H Γ A B').card → Label.{u}}
    (hq : (I.replicated g H Γ A B').rows.IsLawful q)
    (hqe : ∀ c, q (I.attachEmb g H Γ A B' c) = (I.attachmentType g).label c) {k : ℕ}
    (f : Fin k ↪ Fin (m + 2)) (hf : univ.map f ≠ univ)
    (hvis : ∀ z : Fin (I.replicated g H Γ A B').card,
      ((I.replicated g H Γ A B').toCellScheme.scope z : Set (Fin (m + 2))) ⊆ Set.range f →
        z ∈ Set.range (I.attachEmb g H Γ A B')) :
    restrictFace f (replicatedCompletion hα hL hq) = restrictFace f (I.attachmentType g) :=
  (StageType.restrictFace_addApex _ _ _ hf).trans
    (StageType.restrictFace_eq_of_strictMono (t := replicatedType hα hL hq)
      (s := I.attachmentType g) f strictMono_attachEmb isLowerEmbedding_attachEmb
      scope_attachEmb comap_rows_attachEmb ground_replicated faces_replicated
      (fun c ↦ by
        change Label.reduce α (q _) = _
        rw [hqe c]
        exact ((I.attachmentType g).atStage c).reduce_eq) hvis)

/-- **The context face of the completion is the first coatom type**, literally. -/
theorem restrictFace_left_replicatedCompletion
    (hL : (I.replicated g H Γ A B').IsLegalBelowFullGrade)
    {q : Fin (I.replicated g H Γ A B').card → Label.{u}}
    (hq : (I.replicated g H Γ A B').rows.IsLawful q)
    (hqe : ∀ c, q (I.attachEmb g H Γ A B' c) = (I.attachmentType g).label c) :
    restrictFace Fin.castSuccEmb (replicatedCompletion hα hL hq) = some I.left :=
  (restrictFace_replicatedCompletion hα hL hq hqe _ Coatom.univ_map_left_ne
    mem_range_attachEmb_left).trans (I.restrictFace_left_attachmentType g)

include hd in
/-- **The donor face of the completion is the donor**, literally. -/
theorem restrictFace_donor_replicatedCompletion
    (hL : (I.replicated g H Γ A B').IsLegalBelowFullGrade)
    {q : Fin (I.replicated g H Γ A B').card → Label.{u}}
    (hq : (I.replicated g H Γ A B').rows.IsLawful q)
    (hqe : ∀ c, q (I.attachEmb g H Γ A B' c) = (I.attachmentType g).label c) :
    restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (replicatedCompletion hα hL hq) =
      some d :=
  (restrictFace_replicatedCompletion hα hL hq hqe _ (map_extendByLast_ne_univ g)
    mem_range_attachEmb_donor).trans (I.restrictFace_donor_attachmentType g hd)

end Seed

namespace Seed

open Finset Label StageType
variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m}
variable {d : StageType.{u} α (n + 1)}
  (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)

/-- The truncation at the threshold of a mapped state is the mapped truncation. -/
theorem attachHatAt_comp {ν : Label.{u} → Label.{u}} (hν : ν ⊥ = ⊥) (N : ℕ)
    (P : Fin (I.attachment g).card → Label.{u}) (a : Fin (I.attachment g).card) :
    I.attachHatAt g N (ν ∘ P) a = ν (I.attachHatAt g N P a) := by
  unfold attachHatAt
  split_ifs
  · rfl
  · exact hν.symm

end Seed

namespace Seed

open Finset Label CellScheme StageType
variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- All cells of the attachment lie below the full face at the grade `m + 2`. -/
theorem attachment_mem_below_top (a : Fin (I.attachment g).card) :
    a ∈ (I.attachment g).toCellScheme.below ((univ : Finset (Fin (m + 2))), m + 2) :=
  ⟨subset_univ _, ((I.isWellFormed_attachment g).isWellFormed.grade_le_card a).trans
    ((card_le_univ _).trans (by simp))⟩

end Seed

namespace Seed

open Finset Label CellScheme StageType
variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

theorem grade_attachCtxCell (x : Fin I.left.card) :
    (I.attachment g).toCellScheme.grade (I.attachCtxCell g x) = I.left.toCellScheme.grade x :=
  Scheme.grade_faceCell (I.comap_left_attachment_scheme g) x

end Seed

namespace Seed

open Finset Label CellScheme StageType
variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- The cell of the attachment at a context cell lies in the context coatom. -/
theorem scope_attachCtxCell_subset (x : Fin I.left.card) :
    (I.attachment g).toCellScheme.scope (I.attachCtxCell g x) ⊆ ctxCoatom m := by
  rw [← map_castSuccEmb_eq_ctxCoatom, attachCtxCell, Scheme.scope_faceCell]
  exact map_subset_map.mpr (subset_univ _)

end Seed

namespace Seed

open Finset Label CellScheme StageType
variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}
variable {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-- **The truncation at the threshold of a state admitted on its context and donor cells is
admitted**: the requests read the context only at cells of grade at most the threshold (the cap,
the references, the marker, the cells below the cap), and the donor cells have grade at most the
threshold. -/
theorem attachAdmits_of_admitsOnClass
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) (k : ℕ)
    {R : Fin (I.attachment g).card → Label.{u}}
    (hadm : Q.AdmitsOnClass (fun x ↦ R (I.attachCtxCell g x)) fun y ↦ R (I.attachDonCell g hd y)) :
    I.attachAdmits g hd Q k R := by
  intro _ hcls hcap y
  have hctx (x : Fin I.left.card) (hx : I.left.toCellScheme.grade x ≤ Q.threshold) :
      I.attachHatAt g Q.threshold R (I.attachCtxCell g x) = R (I.attachCtxCell g x) := by
    unfold attachHatAt
    rw [grade_attachCtxCell, ite_eq_left hx]
  have hdon (y : Fin d.card) :
      I.attachHatAt g Q.threshold R (I.attachDonCell g hd y) = R (I.attachDonCell g hd y) := by
    unfold attachHatAt
    have hg : (I.attachment g).toCellScheme.grade (I.attachDonCell g hd y) =
        d.toCellScheme.grade y :=
      Scheme.grade_faceCell (comap_toScheme_of_restrictFace
        (I.restrictFace_donor_attachmentType g hd)) y
    rw [hg, ite_eq_left ((d.grade_le y).trans hQ.arity)]
  have hbelow (x : Fin I.left.card)
      (hx : x ∈ I.left.toCellScheme.below (I.left.toCellScheme.gradedIndex Q.cap)) :
      I.left.toCellScheme.grade x ≤ Q.threshold := hx.2
  have hcls' : ∀ x ∈ I.left.toCellScheme.below (I.left.toCellScheme.gradedIndex Q.cap),
      R (I.attachCtxCell g x) = ⊥ ↔ I.left.label x = ⊥ := fun x hx ↦ by
    rw [← hctx x (hbelow x hx)]
    exact hcls x hx
  have hcap' : R (I.attachCtxCell g Q.cap) ≠ ⊥ := by
    rw [← hctx Q.cap le_rfl]
    exact hcap
  have h := hadm hcls' hcap' y
  change Q.CorrectAt _ y (I.attachHatAt g Q.threshold R (I.attachDonCell g hd y))
  rw [hdon]
  refine h.congr (hctx Q.cap le_rfl).symm (fun hy ↦ (hctx _ (hQ.ref y hy).1).symm)
    (hctx _ hQ.marker.1).symm

end Seed

namespace Seed

open Finset Label CellScheme StageType
variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}
variable {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-- **The donor step**: from a lawful context section `u'` vanishing above the grade `j`, agreeing
capped at `c` (self-visible at `j`) with a lawful ambient context section `u` on the cells of grade
at most `j`, and an ambient donor section `v` reading `u` on the root, some lawful donor section
reads `u'` on the root, has the observation of `v` at `c` at the donor cells of grade at most `j`,
and is admitted with `u'`.  Below the threshold: the root lift of the donor at the grade
(`StageType.IsLegal.exists_rootLift_le`), admission being vacuous since the cap value of `u'` is
`⊥`; from the threshold on: the relative lift on the exact class at `c`, from the ambient pair at a
positive cap (admitted by hypothesis) and from the labels pair at the cap `⊥`. -/
theorem _root_.VaughtConjecture.StageType.exists_donorStep {k : ℕ} {t' : StageType.{u} α k}
    {e : Fin n ↪ Fin k} {p₀ : StageType.{u} α n} (hte : restrictFace e t' = some p₀)
    {d : StageType.{u} α (n + 1)} (hdp : restrictFace Fin.castSuccEmb d = some p₀)
    (hdL : d.IsLegal) (hn : 0 < n) {Q : GrowthRequests t' d.toScheme}
    (hpair : ∀ y, Q.CorrectAt t'.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    {j : ℕ} (hj : 1 ≤ j) {c : Label.{u}} (hc : IsSelfVisible j c)
    {u' u : Fin t'.card → Label.{u}} {v : Fin d.card → Label.{u}} (hu' : t'.rows.IsLawful u')
    (hu : t'.rows.IsLawful u) (hv : d.rows.IsLawful v)
    (huv : ∀ i, v (d.faceCell hdp i) = u (t'.faceCell hte i))
    (hpu : ∀ x, t'.toCellScheme.grade x ≤ j → min (u' x) c = min (u x) c)
    (hu'0 : ∀ x, j < t'.toCellScheme.grade x → u' x = ⊥)
    (hu0 : ∀ x, j < t'.toCellScheme.grade x → u x = ⊥)
    (hamb : Q.threshold ≤ j → c ≠ ⊥ → Q.AdmitsOnClass u v) :
    ∃ w : Fin d.card → Label.{u}, d.rows.IsLawful w ∧
      (∀ i, w (d.faceCell hdp i) = u' (t'.faceCell hte i)) ∧
      (∀ y, d.toCellScheme.grade y ≤ j → min (w y) c = min (v y) c) ∧ Q.AdmitsOnClass u' w := by
  by_cases hN : Q.threshold ≤ j
  · have hcN : IsSelfVisible Q.threshold c := hc.mono hN
    by_cases hc0 : c = ⊥
    · subst hc0
      have hlab : Q.AllowedOnClass hte hdp t'.label d.label :=
        ⟨t'.isLawful, d.isLawful,
          fun i ↦ by rw [StageType.label_faceCell, StageType.label_faceCell],
          fun _ _ y ↦ hpair y⟩
      obtain ⟨v', ⟨-, hv', hroot', hadm'⟩, -⟩ := hrel t'.label u' d.label ⊥ hlab hu'
        (isSelfVisible_bot _) fun x ↦ by rw [min_bot_right, min_bot_right]
      exact ⟨v', hv', hroot', fun y _ ↦ by rw [min_bot_right, min_bot_right], hadm'⟩
    · have hall : Q.AllowedOnClass hte hdp u v := ⟨hu, hv, huv, hamb hN hc0⟩
      have hagree (x : Fin t'.card) : min (u' x) c = min (u x) c := by
        by_cases hx : t'.toCellScheme.grade x ≤ j
        · exact hpu x hx
        · rw [hu'0 x (not_le.mp hx), hu0 x (not_le.mp hx)]
      obtain ⟨v', ⟨-, hv', hroot', hadm'⟩, hcap⟩ := hrel u u' v c hall hu' hcN hagree
      exact ⟨v', hv', hroot', fun y _ ↦ hcap y, hadm'⟩
  · have hjN : j < Q.threshold := not_le.mp hN
    have hgr (i : Fin p₀.card) :
        t'.toCellScheme.grade (t'.faceCell hte i) = p₀.toCellScheme.grade i :=
      Scheme.grade_faceCell (comap_toScheme_of_restrictFace hte) i
    have hρ : p₀.rows.IsLawful fun i ↦ u' (t'.faceCell hte i) := isLawful_comp_faceCell hte hu'
    obtain ⟨w, hw, hwr, -, hwc⟩ := hdL.exists_rootLift_le hn hdp hv hρ
      (K := min j (n + 1)) (le_min hj (by omega)) (min_le_right _ _)
      (fun i hi ↦ by
        have h1 := p₀.grade_le i
        have h2 : min j (n + 1) = j := by
          rcases le_total j (n + 1) with h | h
          · exact min_eq_left h
          · exfalso; rw [min_eq_right h] at hi; omega
        rw [h2] at hi
        exact hu'0 _ ((hgr i).symm ▸ hi))
      (hc.mono (min_le_left _ _))
      (fun i hi ↦ by
        rw [huv]
        exact hpu _ ((hgr i).symm ▸ (hi.trans (min_le_left _ _))))
    refine ⟨w, hw, hwr, fun y hy ↦ hwc y (le_min hy (d.grade_le y)), fun _ hcap ↦ ?_⟩
    exact absurd (hu'0 Q.cap hjN) hcap

end Seed

end VaughtConjecture
