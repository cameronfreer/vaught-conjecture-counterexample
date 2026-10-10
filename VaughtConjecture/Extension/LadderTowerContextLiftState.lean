/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderTowerContextLiftReplicated
import VaughtConjecture.MainTheorem.ReplicatedCompletion

/-!
# The state lift from the context coatom over the attachment

Roadmap, Layer 3 ((R3) and (R4), the bountifulness of the replicated carrier).

For the admission predicate of the ladder tower over the attachment (`Seed.attachAdmits`) and
requests calibrated on the class with the labels pair admitted and the relative lift on the exact
class, **the state lift from the context coatom holds at every grade `1 ≤ j ≤ m + 1`**
(`Seed.contextStateLiftR_attachAdmits`), given, from the threshold on, the admission of the
ambient's state (`Seed.ambientState`: the ambient read on the attachment, `⊥` above the grade).

* The prescription, read on the context cells and extended by `⊥` above the grade, is a lawful
  context section (`Seed.isLawful_ctxSection`); the ambient, read on the attachment and extended
  by `⊥`, is a lawful state of the attachment (`Seed.isLawful_ambientState`).
* **The donor** (`Seed.exists_donorStep`): below the threshold, the root lift of the legal donor at
  the grade (`StageType.IsLegal.exists_rootLift_le`); from the threshold on, the relative lift on
  the exact class at the cap, from the ambient pair (admitted by hypothesis) at a positive cap and
  from the labels pair at the cap `⊥`.  In both cases the donor section reads the context section
  on the root, has the observation of the ambient at the cap below the grade, and is admitted with
  the context section (vacuously below the threshold: the cap value is `⊥`).
* **The gluing** (`StageType.exists_joint_extension`, the attachment being covered by its two
  faces) gives the state; its truncation at the threshold is admitted
  (`Seed.attachAdmits_of_admitsOnClass`: the requests read the context only at cells of grade at
  most the threshold, and the donor cells have grade at most the threshold).

The ambient's admission from the threshold on (`Seed.AmbientAdmitted`) is the recognition of the
sections of the replicated scheme below `(univ, j)` (the controllers at `(univ, N)` are available
above the cap and read admitted states); it is a hypothesis here, not proved.

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-! ### The prescription and the ambient on the attachment -/

/-- The cells of the attachment below the full face at the grade `j` lie below it in the
replicated scheme. -/
theorem attachEmb_mem_below_univ {j : ℕ} (a : Fin (I.attachment g).card)
    (h : (I.attachment g).toCellScheme.grade a ≤ j) :
    I.attachEmb g H Γ A B' a ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) :=
  (attachEmb_mem_below_iff a _).mpr ⟨subset_univ _, h⟩

variable (H Γ A B') in
/-- **The ambient's state**: the ambient read on the cells of the attachment below the grade, `⊥`
above. -/
noncomputable def ambientState {j : ℕ}
    (q : (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) → Label.{u}) :
    Fin (I.attachment g).card → Label.{u} := fun a ↦
  if h : (I.attachment g).toCellScheme.grade a ≤ j then
    q ⟨I.attachEmb g H Γ A B' a, attachEmb_mem_below_univ a h⟩ else ⊥

variable (H Γ A B') in
open Classical in
/-- **The prescription's state**: the prescription read on the cells of the attachment below the
context coatom at the grade, `⊥` elsewhere. -/
noncomputable def prescriptionState {j : ℕ}
    (p : (I.replicated g H Γ A B').toCellScheme.below (ctxCoatom m, j) → Label.{u}) :
    Fin (I.attachment g).card → Label.{u} := fun a ↦
  if h : a ∈ (I.attachment g).toCellScheme.below (ctxCoatom m, j) then
    p ⟨I.attachEmb g H Γ A B' a, (attachEmb_mem_below_iff a _).mpr h⟩ else ⊥

theorem ambientState_of_le {j : ℕ}
    {q : (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) → Label.{u}}
    (a : Fin (I.attachment g).card) (h : (I.attachment g).toCellScheme.grade a ≤ j) :
    ambientState H Γ A B' q a = q ⟨I.attachEmb g H Γ A B' a, attachEmb_mem_below_univ a h⟩ := by
  simp only [ambientState, h, dite_true]

theorem ambientState_of_lt {j : ℕ}
    {q : (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) → Label.{u}}
    (a : Fin (I.attachment g).card) (h : j < (I.attachment g).toCellScheme.grade a) :
    ambientState H Γ A B' q a = ⊥ := by
  simp only [ambientState, not_le.mpr h, dite_false]

theorem prescriptionState_of_mem {j : ℕ}
    {p : (I.replicated g H Γ A B').toCellScheme.below (ctxCoatom m, j) → Label.{u}}
    (a : Fin (I.attachment g).card) (h : a ∈ (I.attachment g).toCellScheme.below (ctxCoatom m, j)) :
    prescriptionState H Γ A B' p a =
      p ⟨I.attachEmb g H Γ A B' a, (attachEmb_mem_below_iff a _).mpr h⟩ := by
  simp only [prescriptionState, h, dite_true]

theorem prescriptionState_of_notMem {j : ℕ}
    {p : (I.replicated g H Γ A B').toCellScheme.below (ctxCoatom m, j) → Label.{u}}
    (a : Fin (I.attachment g).card)
    (h : a ∉ (I.attachment g).toCellScheme.below (ctxCoatom m, j)) :
    prescriptionState H Γ A B' p a = ⊥ := by
  simp only [prescriptionState, h, dite_false]

/-- **The ambient's state is a lawful state of the attachment.** -/
theorem isLawful_ambientState {j : ℕ}
    {q : (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) → Label.{u}}
    (hq : (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q) :
    (I.attachment g).rows.IsLawful (ambientState H Γ A B' q) := by
  have hq' := Rows.IsLawfulBelow.comap_of_scope_eq isLowerEmbedding_attachEmb scope_attachEmb hq
  rw [comap_rows_attachEmb] at hq'
  have h1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
      fun t ↦ ambientState H Γ A B' q t := by
    refine (Rows.isLawfulBelow_congr (w := fun a ↦ ambientState H Γ A B' q a)
      (w' := fun a ↦ ambientState H Γ A B' q a) fun _ _ ↦ rfl).mp ?_
    convert hq' using 1
    funext t
    exact ambientState_of_le t.1 t.2.2
  have h2 := Rows.isLawfulBelow_extendAbove (K := m + 2) h1
  refine Rows.isLawful_of_isLawfulBelow attachment_mem_below_top
    ((Rows.isLawfulBelow_congr (w := fun a ↦ if (I.attachment g).toCellScheme.grade a ≤ j
      then ambientState H Γ A B' q a else ⊥) fun a _ ↦ ?_).mp h2)
  by_cases h : (I.attachment g).toCellScheme.grade a ≤ j
  · exact ite_eq_left h
  · rw [ite_eq_right h, ambientState_of_lt a (not_le.mp h)]

/-- **The prescription's state is lawful below the context coatom** at every grade. -/
theorem isLawfulBelow_prescriptionState {j : ℕ}
    {p : (I.replicated g H Γ A B').toCellScheme.below (ctxCoatom m, j) → Label.{u}}
    (hp : (I.replicated g H Γ A B').rows.IsLawfulBelow (ctxCoatom m, j) p) :
    (I.attachment g).rows.IsLawfulBelow (ctxCoatom m, m + 2)
      fun t ↦ prescriptionState H Γ A B' p t := by
  have hp' := Rows.IsLawfulBelow.comap_of_scope_eq isLowerEmbedding_attachEmb scope_attachEmb hp
  rw [comap_rows_attachEmb] at hp'
  have h1 : (I.attachment g).rows.IsLawfulBelow (ctxCoatom m, j)
      fun t ↦ prescriptionState H Γ A B' p t := by
    convert hp' using 1
    funext t
    exact prescriptionState_of_mem t.1 t.2
  have h2 := Rows.isLawfulBelow_extendAbove (K := m + 2) h1
  refine (Rows.isLawfulBelow_congr (w := fun a ↦ if (I.attachment g).toCellScheme.grade a ≤ j
    then prescriptionState H Γ A B' p a else ⊥) fun a _ ↦ ?_).mp h2
  by_cases h : (I.attachment g).toCellScheme.grade a ≤ j
  · exact ite_eq_left h
  · rw [ite_eq_right h, prescriptionState_of_notMem a fun hm ↦ h hm.2]

/-! ### The context section -/

variable (H Γ A B') in
/-- **The context section of a prescription**: the prescription's state at the context cells. -/
noncomputable def ctxSection {j : ℕ}
    (p : (I.replicated g H Γ A B').toCellScheme.below (ctxCoatom m, j) → Label.{u}) :
    Fin I.left.card → Label.{u} := fun x ↦ prescriptionState H Γ A B' p (I.attachCtxCell g x)

/-- **The context section of a lawful prescription is a lawful context section.** -/
theorem isLawful_ctxSection {j : ℕ}
    {p : (I.replicated g H Γ A B').toCellScheme.below (ctxCoatom m, j) → Label.{u}}
    (hp : (I.replicated g H Γ A B').rows.IsLawfulBelow (ctxCoatom m, j) p) :
    I.left.rows.IsLawful (ctxSection H Γ A B' p) := by
  have h0 := isLawfulBelow_prescriptionState hp
  have hX : Prod.map (Finset.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2))) id
      ((univ : Finset (Fin (m + 1))), m + 2) = (ctxCoatom m, m + 2) := by
    simp only [Prod.map, id, map_castSuccEmb_eq_ctxCoatom]
  have h1 := ((I.attachment g).isLawfulBelow_comap_cellMap_iff Fin.castSuccEmb
    ((univ : Finset (Fin (m + 1))), m + 2) (prescriptionState H Γ A B' p)).mpr (hX ▸ h0)
  have h2 : ((I.attachment g).comap Fin.castSuccEmb).rows.IsLawful
      fun i ↦ prescriptionState H Γ A B' p ((I.attachment g).cellMap Fin.castSuccEmb i) :=
    Rows.isLawful_of_isLawfulBelow (fun i ↦ by
      refine ⟨subset_univ _, ?_⟩
      exact (attachment_mem_below_top ((I.attachment g).cellMap Fin.castSuccEmb i)).2) h1
  exact Scheme.isLawful_of_eq
    (comap_toScheme_of_restrictFace (I.restrictFace_left_attachmentType g)).symm h2

/-! ### The truncation is admitted -/

variable {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-! ### The donor step -/

/-! ### The state lift -/

variable (I g H Γ B') in
/-- **The ambient's admission at the grade `j`**: from the threshold on, the state of every
ambient lawful below `(univ, j)` is admitted on its context and donor cells.  It is the recognition
of the sections of the replicated scheme below the full face. -/
def AmbientAdmitted (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    (Q : GrowthRequests I.left d.toScheme) (j : ℕ) : Prop :=
  Q.threshold ≤ j →
    ∀ q : (I.replicated g H Γ (I.attachAdmits g hd Q) B').toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j) → Label.{u},
      (I.replicated g H Γ (I.attachAdmits g hd Q) B').rows.IsLawfulBelow
        ((univ : Finset (Fin (m + 2))), j) q →
      Q.AdmitsOnClass (fun x ↦ ambientState H Γ (I.attachAdmits g hd Q) B' q (I.attachCtxCell g x))
        fun y ↦ ambientState H Γ (I.attachAdmits g hd Q) B' q (I.attachDonCell g hd y)

/-- **The state lift from the context coatom over the attachment** at every grade `1 ≤ j ≤ m + 1`,
for requests calibrated on the class with the labels pair admitted and the relative lift on the
exact class, given the ambient's admission from the threshold on.  The context section of the
prescription and the donor step (`StageType.exists_donorStep`) glue over the attachment
(`StageType.exists_joint_extension`); the glued state's truncation is admitted
(`Seed.attachAdmits_of_admitsOnClass`). -/
theorem contextStateLiftR_attachAdmits
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    {j : ℕ} (hj : 1 ≤ j) (hamb : AmbientAdmitted I g H Γ B' hd Q j) :
    ContextStateLiftR I g H Γ (I.attachAdmits g hd Q) B' j := by
  intro c hc p q hp hq hpq
  have h₁ := I.restrictFace_left_attachmentType g
  have h₂ := I.restrictFace_donor_attachmentType g hd
  have hu' := isLawful_ctxSection hp
  have hqA := isLawful_ambientState hq
  have hu : I.left.rows.IsLawful
      fun x ↦ ambientState H Γ (I.attachAdmits g hd Q) B' q (I.attachCtxCell g x) :=
    isLawful_comp_faceCell h₁ hqA
  have hv : d.rows.IsLawful
      fun y ↦ ambientState H Γ (I.attachAdmits g hd Q) B' q (I.attachDonCell g hd y) :=
    isLawful_comp_faceCell h₂ hqA
  have hctxmem (x : Fin I.left.card) (hx : I.left.toCellScheme.grade x ≤ j) :
      I.attachCtxCell g x ∈ (I.attachment g).toCellScheme.below (ctxCoatom m, j) :=
    ⟨scope_attachCtxCell_subset x, (grade_attachCtxCell x).trans_le hx⟩
  obtain ⟨w, hw, hwr, hwc, hadm⟩ := StageType.exists_donorStep hte hdp hdL hn hpair hrel hj hc
    hu' hu hv
    (fun i ↦ by
      change ambientState H Γ _ B' q ((I.attachmentType g).faceCell h₂ (d.faceCell hdp i)) =
        ambientState H Γ _ B' q ((I.attachmentType g).faceCell h₁ (I.left.faceCell hte i))
      rw [StageType.faceCell_faceCell h₁ h₂ hte hdp i])
    (fun x hx ↦ by
      have e1 := prescriptionState_of_mem (H := H) (Γ := Γ) (A := I.attachAdmits g hd Q)
        (B' := B') (p := p) _ (hctxmem x hx)
      have e2 := ambientState_of_le (H := H) (Γ := Γ) (A := I.attachAdmits g hd Q) (B' := B')
        (q := q) _ ((grade_attachCtxCell x).trans_le hx)
      exact ((congrArg (fun z ↦ min z c) e1).trans
        (hpq ⟨_, (attachEmb_mem_below_iff _ _).mpr (hctxmem x hx)⟩).symm).trans
        (congrArg (fun z ↦ min z c) e2).symm)
    (fun x hx ↦ prescriptionState_of_notMem _ fun hm ↦
      absurd ((grade_attachCtxCell x).symm.trans_le hm.2) (not_le.mpr hx))
    (fun x hx ↦ ambientState_of_lt _ ((grade_attachCtxCell x).symm ▸ hx))
    (fun hN _ ↦ hamb hN q hq)
  obtain ⟨R, hR, hR₁, hR₂⟩ := StageType.exists_joint_extension h₁ h₂ hte hdp
    (I.attachment_cover g) hu' hw hwr
  have e1 : (fun x ↦ R (I.attachCtxCell g x)) = ctxSection H Γ (I.attachAdmits g hd Q) B' p :=
    funext hR₁
  have e2 : (fun y ↦ R (I.attachDonCell g hd y)) = w := funext hR₂
  refine ⟨R, hR, attachAdmits_of_admitsOnClass hd hQ _ (by rw [e1, e2]; exact hadm), ?_, ?_⟩
  · intro d' a ha
    have hab : a ∈ (I.attachment g).toCellScheme.below (ctxCoatom m, j) :=
      (attachEmb_mem_below_iff a _).mp (ha ▸ d'.2)
    have hvis : a ∈ (I.attachment g).visibleCells Fin.castSuccEmb := by
      rw [Scheme.mem_visibleCells]
      intro z hz
      have hz' : z ∈ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) := by
        rw [map_castSuccEmb_eq_ctxCoatom]
        exact hab.1 (mem_coe.mp hz)
      obtain ⟨y, -, rfl⟩ := mem_map.mp hz'
      exact ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := StageType.exists_faceCell_eq h₁ hvis
    have e1 := prescriptionState_of_mem (H := H) (Γ := Γ) (A := I.attachAdmits g hd Q)
      (B' := B') (p := p) _ hab
    exact (hR₁ x).trans (e1.trans (congrArg p (Subtype.ext ha)))
  · intro d' a ha
    have hab : (I.attachment g).toCellScheme.grade a ≤ j :=
      ((attachEmb_mem_below_iff a ((univ : Finset (Fin (m + 2))), j)).mp (ha ▸ d'.2)).2
    have hqa : q d' = q ⟨I.attachEmb g H Γ _ B' a, attachEmb_mem_below_univ a hab⟩ :=
      congrArg q (Subtype.ext ha.symm)
    rcases I.attachment_cover g a with hvis | hvis
    · obtain ⟨x, rfl⟩ := StageType.exists_faceCell_eq h₁ hvis
      have hxj : I.left.toCellScheme.grade x ≤ j := (grade_attachCtxCell x).symm.trans_le hab
      have e1 := prescriptionState_of_mem (H := H) (Γ := Γ) (A := I.attachAdmits g hd Q)
        (B' := B') (p := p) _ (hctxmem x hxj)
      rw [hR₁ x, hqa]
      exact (congrArg (fun z ↦ min z c) e1).trans
        (hpq ⟨_, (attachEmb_mem_below_iff _ _).mpr (hctxmem x hxj)⟩).symm
    · obtain ⟨y, rfl⟩ := StageType.exists_faceCell_eq h₂ hvis
      have hgy : d.toCellScheme.grade y ≤ j :=
        (Scheme.grade_faceCell (comap_toScheme_of_restrictFace h₂) y).symm.trans_le hab
      have e2 := ambientState_of_le (H := H) (Γ := Γ) (A := I.attachAdmits g hd Q) (B' := B')
        (q := q) _ hab
      rw [hR₂ y, hwc y hgy, hqa]
      exact congrArg (fun z ↦ min z c) e2

/-- **The context lift of the replicated scheme from the ambient's admission and the coding of
states**: for requests calibrated on the class with the labels pair admitted and the relative lift
on the exact class over a legal donor with a nonempty root, the state lift holds at every grade
(`Seed.contextStateLiftR_attachAdmits`), so the context lift follows from the ambient's admission
from the threshold on and the coding of states at every grade (`Seed.hasContextLift_of_stateLift`).
-/
theorem hasContextLift_attachAdmits (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hamb : ∀ j, 1 ≤ j → j ≤ m + 1 → AmbientAdmitted I g H Γ B' hd Q j)
    (hC : ∀ j, 1 ≤ j → j ≤ m + 1 → StateCodingR I g H Γ (I.attachAdmits g hd Q) B' j) :
    I.HasContextLift g H Γ (I.attachAdmits g hd Q) B' :=
  hasContextLift_of_stateLift hH hcard hΓ (fun k R h ↦ I.attachAdmits_succ g hd Q k R h)
    fun j hj hjm ↦ ⟨contextStateLiftR_attachAdmits hte hdp hdL hn hd hQ hpair hrel hj
      (hamb j hj hjm), hC j hj hjm⟩

end Seed

end VaughtConjecture
