/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthFaceAdmission
import VaughtConjecture.Extension.FaceGluing
import VaughtConjecture.Extension.SeedAttachment
import VaughtConjecture.MainTheorem.SeedLadderCarrier

/-!
# Admitted completions over the amalgam of a seed

Roadmap, Layer 3 ((R3) and (R4), the lift from the context coatom of the recognizing carrier).

At a seed whose amalgam has the context `I.left` and the donor `d` as faces, a context section
`u'` has an **admitted completion** when some lawful section of the amalgam extends it with donor
values admitted on the exact class (`Seed.HasAdmittedCompletions`).

* **Necessity** (`Seed.hasAdmittedCompletions_of_recognizes`): a recognizing growth carrier that
  contains the amalgam (a lower embedding keeping rows, through which the context and donor cells
  pass) has admitted completions: the admitted extension of the context section
  (`GrowthCarrier.exists_admitted_extension`) restricts to the amalgam.  This holds for every
  carrier built over the amalgam, whatever cells of full scope or copies are added.
* **Sufficiency from a joint extension** (`Seed.hasAdmittedCompletions_of_jointExtension`): if
  lawful sections of the context and of the donor agreeing on the root extend jointly to the
  amalgam (`Seed.HasJointExtension`: the second coatom type is a free amalgam of its two faces),
  then the relative lift on the exact class at the cap `⊥` (from the labels, whose pair is admitted)
  gives admitted donor values, and the joint extension the completion.

So the lift from the context coatom asks, at the amalgam, exactly for admitted completions; they
follow from the relative lift on the exact class and a joint extension through the second coatom
type.

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) {g : Fin n ↪ Fin m}
  {p : StageType.{u} α n} (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p)
  {d : StageType.{u} α (n + 1)} (hdp : restrictFace Fin.castSuccEmb d = some p)
  (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)

/-- **Admitted completions** for requests `Q`: every lawful context section extends to a lawful
section of the amalgam whose donor values are admitted on the exact class. -/
def HasAdmittedCompletions (Q : GrowthRequests I.left d.toScheme) : Prop :=
  ∀ u' : Fin I.left.card → Label.{u}, I.left.rows.IsLawful u' →
    ∃ R : Fin I.amalgam.card → Label.{u}, I.amalgam.rows.IsLawful R ∧
      (∀ x, R (I.ctxCell x) = u' x) ∧
      Q.AdmitsOnClass (fun x ↦ R (I.ctxCell x)) (fun j ↦ R (I.donorFaceCell hd j))

/-- **The joint extension through the amalgam**: lawful sections of the context and of the donor
agreeing on the root extend jointly to a lawful section of the amalgam. -/
def HasJointExtension : Prop :=
  ∀ (u : Fin I.left.card → Label.{u}) (w : Fin d.card → Label.{u}), I.left.rows.IsLawful u →
    d.rows.IsLawful w → (∀ i, w (d.faceCell hdp i) = u (I.left.faceCell hte i)) →
    ∃ R : Fin I.amalgam.card → Label.{u}, I.amalgam.rows.IsLawful R ∧
      (∀ x, R (I.ctxCell x) = u x) ∧ ∀ j, R (I.donorFaceCell hd j) = w j

variable {I}

/-- **Admitted completions from a joint extension and the relative lift on the exact class**: the
labels pair is admitted, the relative lift at the cap `⊥` gives admitted donor values for any
context section, and the joint extension completes them. -/
theorem hasAdmittedCompletions_of_jointExtension {Q : GrowthRequests I.left d.toScheme}
    (hpair : ∀ j, Q.CorrectAt I.left.label j (d.label j))
    (hrel : Q.HasRelativeLiftOnClass hte hdp) (hJ : I.HasJointExtension hte hdp hd) :
    I.HasAdmittedCompletions hd Q := by
  intro u' hu'
  have hlab : Q.AllowedOnClass hte hdp I.left.label d.label :=
    ⟨I.left.isLawful, d.isLawful,
      fun i ↦ by rw [StageType.label_faceCell, StageType.label_faceCell],
      fun _ _ j ↦ hpair j⟩
  obtain ⟨v', ⟨-, hv', hroot, hadm⟩, -⟩ := hrel I.left.label u' d.label ⊥ hlab hu'
    (isSelfVisible_bot _) fun x ↦ by rw [min_bot_right, min_bot_right]
  obtain ⟨R, hR, hRc, hRd⟩ := hJ u' v' hu' hv' hroot
  refine ⟨R, hR, hRc, ?_⟩
  have e1 : (fun x ↦ R (I.ctxCell x)) = u' := funext hRc
  have e2 : (fun j ↦ R (I.donorFaceCell hd j)) = v' := funext hRd
  rw [e1, e2]
  exact hadm

/-- **Admitted completions are necessary for recognition**: a recognizing growth carrier containing
the amalgam (a lower embedding `φ` keeping rows, through which the context and donor cells pass)
has admitted completions. -/
theorem hasAdmittedCompletions_of_recognizes {Q : GrowthRequests I.left d.toScheme}
    (G : GrowthCarrier I.left.toScheme d.toScheme (g.trans Fin.castSuccEmb))
    {φ : Fin I.amalgam.card → Fin G.scheme.card}
    (hφ : I.amalgam.toCellScheme.IsLowerEmbedding G.scheme.toCellScheme φ)
    (hrows : G.scheme.rows.comap hφ = I.amalgam.rows)
    (hctx : ∀ x, G.contextCell x = φ (I.ctxCell x))
    (hdon : ∀ j, G.donorCell j = φ (I.donorFaceCell hd j)) (hrec : G.Recognizes Q)
    (href : ∀ j ∈ Q.exacts,
      Q.ref j ∈ I.left.toCellScheme.below (I.left.toCellScheme.gradedIndex Q.cap) ∧
        Q.offset j ≤ Q.threshold)
    (hmk : Q.marker ∈ I.left.toCellScheme.below (I.left.toCellScheme.gradedIndex Q.cap) ∧
      Q.markerOffset ≤ Q.threshold) :
    I.HasAdmittedCompletions hd Q := by
  intro u' hu'
  obtain ⟨r, hr, hrℓ, hadm⟩ := G.exists_admitted_extension Q hrec href hmk G.context_mem
    (Scheme.isLawful_of_eq G.comap_context hu')
  have hR := hr.comap hφ
  rw [hrows] at hR
  have hrc (x : Fin I.left.card) : r (G.contextCell x) = u' x := by
    have h := hrℓ (Fin.cast (congrArg Scheme.card G.comap_context).symm x)
    rw [GrowthCarrier.contextCell, Scheme.faceCell]
    simpa using h
  refine ⟨r ∘ φ, hR, fun x ↦ ?_, ?_⟩
  · simp only [Function.comp_apply]
    rw [← hctx]
    exact hrc x
  · have e1 : (fun x ↦ (r ∘ φ) (I.ctxCell x)) = fun x ↦ r (G.contextCell x) :=
      funext fun x ↦ by simp only [Function.comp_apply]; rw [hctx]
    have e2 : (fun j ↦ (r ∘ φ) (I.donorFaceCell hd j)) = fun j ↦ r (G.donorCell j) :=
      funext fun j ↦ by simp only [Function.comp_apply]; rw [hdon]
    rw [e1, e2]
    exact hadm

end Seed

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ} {D : StageType.{u} α (k + 1)} {t' : StageType.{u} α k}
  {e : Fin n ↪ Fin k} {p : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-- **Admitted completions over a one-point extension covered by its two faces**: with the labels
pair admitted and the relative lift on the exact class, every lawful context section extends to a
lawful section of `D` whose donor values are admitted on the exact class.  The relative lift at the
cap `⊥` from the labels gives admitted donor values agreeing with the section on the root, and the
two sections glue (`StageType.exists_joint_extension`). -/
theorem exists_admitted_completion (h₁ : restrictFace Fin.castSuccEmb D = some t')
    (h₂ : restrictFace (extendByLast e) D = some d) (ht : restrictFace e t' = some p)
    (hd : restrictFace Fin.castSuccEmb d = some p)
    (hcover : ∀ c, c ∈ D.toScheme.visibleCells Fin.castSuccEmb ∨
      c ∈ D.toScheme.visibleCells (extendByLast e))
    {Q : GrowthRequests t' d.toScheme} (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j))
    (hrel : Q.HasRelativeLiftOnClass ht hd) {u' : Fin t'.card → Label.{u}}
    (hu' : t'.rows.IsLawful u') :
    ∃ R : Fin D.card → Label.{u}, D.rows.IsLawful R ∧ (∀ x, R (D.faceCell h₁ x) = u' x) ∧
      Q.AdmitsOnClass u' fun j ↦ R (D.faceCell h₂ j) := by
  have hlab : Q.AllowedOnClass ht hd t'.label d.label :=
    ⟨t'.isLawful, d.isLawful,
      fun i ↦ by rw [StageType.label_faceCell, StageType.label_faceCell],
      fun _ _ j ↦ hpair j⟩
  obtain ⟨v', ⟨-, hv', hroot, hadm⟩, -⟩ := hrel t'.label u' d.label ⊥ hlab hu'
    (isSelfVisible_bot _) fun x ↦ by rw [min_bot_right, min_bot_right]
  obtain ⟨R, hR, hR₁, hR₂⟩ := exists_joint_extension h₁ h₂ ht hd hcover hu' hv' hroot
  refine ⟨R, hR, hR₁, ?_⟩
  have e2 : (fun j ↦ R (D.faceCell h₂ j)) = v' := funext hR₂
  rw [e2]
  exact hadm

end StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) {g : Fin n ↪ Fin m}
  {p : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-- **Admitted completions over the attachment are a theorem**: at a seed whose amalgam has the
donor as its face along the root followed by the new point, with the labels pair admitted and the
relative lift on the exact class, every lawful context section extends to a lawful section of the
attachment with admitted donor values.  The attachment is covered by its context and donor faces
(no cell on a mixed face), so the joint extension holds outright. -/
theorem exists_admitted_completion_attachment
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p)
    (hdp : restrictFace Fin.castSuccEmb d = some p)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hpair : ∀ j, Q.CorrectAt I.left.label j (d.label j))
    (hrel : Q.HasRelativeLiftOnClass hte hdp) {u' : Fin I.left.card → Label.{u}}
    (hu' : I.left.rows.IsLawful u') :
    ∃ R : Fin (I.attachmentType g).card → Label.{u}, (I.attachmentType g).rows.IsLawful R ∧
      (∀ x, R ((I.attachmentType g).faceCell (I.restrictFace_left_attachmentType g) x) = u' x) ∧
      Q.AdmitsOnClass u' fun j ↦
        R ((I.attachmentType g).faceCell (I.restrictFace_donor_attachmentType g hd) j) :=
  StageType.exists_admitted_completion (I.restrictFace_left_attachmentType g)
    (I.restrictFace_donor_attachmentType g hd) hte hdp (I.attachment_cover g) hpair hrel hu'

end Seed

end VaughtConjecture
