/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowLayer
import VaughtConjecture.MainTheorem.BoundedCoatomDetermination

/-!
# (R2) for receiving models from LOW displays at source-gap contexts

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3) and Layer 6 ("Status:
the hypotheses of the main theorem"); semantic contract, items 4, 5 and 8.

**LOW displays at source-gap contexts** (`StageType.HasLowDisplays`, a statement about stage
types; open).  At a limit stage, every LOW family (`StageType.IsLowFamily`: a legal source-gap
context `t'` of grade `K` on `k + 1` points with the lost point last, along `Fin.castSuccEmb` at
`Fin.last k`, with coatom face `p` along `Fin.castSuccEmb`, and a legal coface `tb` of `p` of top
grade at most `K`) has a LOW display (`StageType.IsLowDisplay`) at a
threshold occurring at the stage: a legal `D` on `k + 2` points with faces `t'` and `tb`, such
that every lawful section of the rows of `D` with the private face literal and the observation of
`D` at a cutoff above the threshold has the donor face literal.  The separated form
(`StageType.HasSeparatedLowDisplays`, the separator and its reading, [Kni26, §3.3]) implies it
(`StageType.HasSeparatedLowDisplays.hasLowDisplays`, compiled in this repository), and the
controller form (`StageType.HasControlledLowDisplays`: the separator reading through the rows of
the cells of graded index `(univ, K)`, `StageType.IsControllerReading`) implies the separated form
(`StageType.HasControlledLowDisplays.hasSeparatedLowDisplays`, compiled in this repository).  In
the controller form no lawful section of the display enters: a lawful section `q` with the
private tops literal is `σ` of the row of some controller up to grade `K`
(`StageType.exists_controller`, from completeness, availability and locality).  LOW layers
(`StageType.HasLowLayers`: every controller of grade `K` carries a LOW profile, read by its row
at the other cells and at agreement heights at the controllers, `StageType.IsLowLayer`) give the
controller form (`StageType.HasLowLayers.hasControlledLowDisplays`, compiled in this repository).

**The bounded coatom form from LOW displays**
(`Realization.BoundedCoatomCutoffDetermination.of_hasLowDisplays`, compiled in this repository).
For the input of the bounded coatom form at a source-gap context with the lost point last (the
context `t'`, its root `g.trans Fin.castSuccEmb`, its coatom face `p`, a coface `tb` of `p` of top
grade at most `K`, and the face `d` of `tb` along `extendByLast g`), the LOW display `D'` of
`(t', tb)` is the coface, with face `tb`, and a permitted cutoff above its threshold
(`StageType.IsLowDisplay.exists_cutoff`) determines `d`: every member of the receiving family of
`D'` at that cutoff with face `t'` has face `tb` (`StageType.IsLowDisplay.isDeterminedWithin`),
hence face `d` along `extendByLast g` followed by the root.

**(R2) for receiving models** (`Realization.receivingResidualReceiving_of_hasLowDisplays`,
compiled in this repository): through the bounded coatom form, the compiled acquisition with the
first coatom closed, and the bounded pinned extension
(`Realization.receivingResidualReceiving_of_boundedCoatom_sourceGapLast`).  The model application
is the finite-cut receiving of the given model and its exact consistency: the display is received
over the cover of the context at the cutoff, the private labels stay literal by consistency,
recovery gives the donor, and restriction gives the original donor over the original tuple.
**The main theorem** with (R2) replaced by LOW displays
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_lowDisplays`), conditional on (R4),
`StageType.HasLowDisplays` at universe `0`, and (R3) for receiving models.

**The instance without new tops** (`StageType.exists_isLowDisplay_of_forall_top_root`, compiled in
this repository): at a limit stage, if every top of `tb` avoids the new point, the exact pinned
extension of `t'` through `tb` is a LOW display (`StageType.IsLowDisplay.of_forall_top_root`).  No
source-gap clause is used; the separator reading is needed only for the donor tops through the
new point.

**Not claimed.**  `StageType.HasLowDisplays` is not proved; the bounded receiving hypothesis
remains open.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n k K : ℕ}

/-- The source-gap clauses at the last point do not depend on the root, as long as the root avoids
the last point: they hold along `Fin.castSuccEmb`. -/
theorem IsSourceGapContextAt.castSuccEmb {t' : StageType.{u} α (k + 1)}
    {h : Fin n ↪ Fin (k + 1)} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt K h (Fin.last k) o r) :
    t'.IsSourceGapContextAt K Fin.castSuccEmb (Fin.last k) o r where
  notMem_range := fun ⟨i, hi⟩ ↦ (Fin.castSucc_lt_last i).ne hi
  topGrade_eq := hs.topGrade_eq
  scope_owner := hs.scope_owner
  grade_owner := hs.grade_owner
  label_owner := hs.label_owner
  label_lost := hs.label_lost
  mem_scope_lost := hs.mem_scope_lost
  gap_owner := hs.gap_owner
  gap_retained := hs.gap_retained

/-- **LOW displays at source-gap contexts** (open): at every limit stage, every LOW family
(`IsLowFamily`: a legal source-gap context `t'` of grade `K` on `k + 1` points with the lost point
last, and a legal donor `tb` of top grade at most `K` with the same face `p` along
`Fin.castSuccEmb`) has a LOW display at a threshold occurring at the stage.

Not proved.  The legality of a display carrying a LOW layer reduces, at the grade `K` of the
controllers over a good level of the profile tower, to the LOW step on the amalgam
(`ProfileTower.Lvl.LowStep`, `ProfileTower.Lvl.Good.cappedLift_lowS_of_lowStep`), a named
hypothesis that is open; the layers above `K`, the separator and the reading are not assembled. -/
def HasLowDisplays : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K k : ℕ⦄ (t' tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (o r : Fin t'.card), Order.IsSuccLimit α → IsLowFamily K t' tb p o r →
      ∃ (D : StageType.{u} α (k + 2)) (a : Label.{u}), AtStage α a ∧ IsLowDisplay t' tb D a

/-- **Separated LOW displays at source-gap contexts** (open): the statement of `HasLowDisplays`
with a separated display (`IsSeparatedLowDisplay`). -/
def HasSeparatedLowDisplays : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K k : ℕ⦄ (t' tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (o r : Fin t'.card), Order.IsSuccLimit α → IsLowFamily K t' tb p o r →
      ∃ (D : StageType.{u} α (k + 2)) (lo hi : Fin D.card), IsSeparatedLowDisplay t' tb D lo hi

/-- **Controlled LOW displays at source-gap contexts** (open): the statement of
`HasSeparatedLowDisplays` with the separator reading given by the controller reading
(`IsControllerReading`) at grade `K`: every LOW family `(t', tb)` with owner `o` and lost top `r`
has a legal display `D` with separator cells `lo`, `hi` of grade at most `K`, labelled by a proper
label and by `⊤`, whose controllers of grade `K` read the private copies of `o` and `r`, the
separator, and the donor tops as required.  A statement about the rows of the controllers of `D`;
no lawful section of `D` other than its labels enters. -/
def HasControlledLowDisplays : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K k : ℕ⦄ (t' tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (o r : Fin t'.card), Order.IsSuccLimit α → IsLowFamily K t' tb p o r →
      ∃ (D : StageType.{u} α (k + 2)) (h₁ : restrictFace Fin.castSuccEmb D = some t')
        (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some tb) (lo hi : Fin D.card),
        D.IsLegal ∧ D.label lo ≠ ⊤ ∧ D.label hi = ⊤ ∧ D.toCellScheme.grade lo ≤ K ∧
          D.toCellScheme.grade hi ≤ K ∧
          IsControllerReading D K (faceCell h₁ o) (faceCell h₁ r) lo hi
            {i | ∃ x, tb.label x = ⊤ ∧ faceCell h₂ x = i}

/-- **The controller reading gives separated displays**
(`StageType.IsSeparatedLowDisplay.of_controllerReading`). -/
theorem HasControlledLowDisplays.hasSeparatedLowDisplays (h : HasControlledLowDisplays.{u}) :
    HasSeparatedLowDisplays.{u} := by
  intro α K k t' tb p o r hα hF
  obtain ⟨D, h₁, h₂, lo, hi, hD, hlo, hhi, hlog, hhig, hX⟩ := h t' tb p o r hα hF
  exact ⟨D, lo, hi, IsSeparatedLowDisplay.of_controllerReading hF.isSourceGapContextAt
    hF.topGrade_donor hD h₁ h₂ hlo hhi hlog hhig hX⟩

/-- **LOW layers at source-gap contexts** (open): every LOW family `(t', tb)` with owner `o` and
lost top `r` has a legal display `D` with a LOW layer at grade `K` (`IsLowLayer`) whose separator
`lo`, `hi` is labelled by a proper label and by `⊤`. -/
def HasLowLayers : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K k : ℕ⦄ (t' tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (o r : Fin t'.card), Order.IsSuccLimit α → IsLowFamily K t' tb p o r →
      ∃ (D : StageType.{u} α (k + 2)) (h₁ : restrictFace Fin.castSuccEmb D = some t')
        (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some tb) (G : Finset Label.{u})
        (entry : Fin D.card → LowField D → Label.{u}) (s : LowField D → Label.{u})
        (lo hi : Fin D.card), D.IsLegal ∧ D.label lo ≠ ⊤ ∧ D.label hi = ⊤ ∧
          IsLowLayer K h₁ h₂ o r G entry s lo hi

/-- **LOW layers give controlled LOW displays** (`StageType.IsLowLayer.isControllerReading`). -/
theorem HasLowLayers.hasControlledLowDisplays (h : HasLowLayers.{u}) :
    HasControlledLowDisplays.{u} := by
  intro α K k t' tb p o r hα hF
  obtain ⟨D, h₁, h₂, G, entry, s, lo, hi, hD, hlo, hhi, hL⟩ := h t' tb p o r hα hF
  have hs := hF.isSourceGapContextAt
  have hr : t'.toCellScheme.grade r ≤ K := hs.topGrade_eq ▸ grade_le_topGrade hs.label_lost
  exact ⟨D, h₁, h₂, lo, hi, hD, hlo, hhi, (congrArg Prod.snd hL.gradedIndex_lo).le,
    (congrArg Prod.snd hL.gradedIndex_hi).le,
    hL.isControllerReading hs.grade_owner.le hr hF.topGrade_donor⟩

/-- **Separated displays give LOW displays** (`StageType.exists_isLowDisplay_of_separated`). -/
theorem HasSeparatedLowDisplays.hasLowDisplays (h : HasSeparatedLowDisplays.{u}) :
    HasLowDisplays.{u} := by
  intro α K k t' tb p o r hα hF
  obtain ⟨D, lo, hi, hD⟩ := h t' tb p o r hα hF
  obtain ⟨a, ha, hDa⟩ := exists_isLowDisplay_of_separated hα hD
  exact ⟨D, a, ha, hDa⟩

/-- **The instance without new tops**: at a limit stage, for a legal `t'` on `k + 1` points with
face `p` along `Fin.castSuccEmb` and a legal coface `tb` of `p` whose tops all avoid the new
point, the exact pinned extension of `t'` through `tb` is a LOW display at a threshold occurring
at the stage. -/
theorem exists_isLowDisplay_of_forall_top_root (hα : Order.IsSuccLimit α)
    {t' : StageType.{u} α (k + 1)} (ht' : t'.IsLegal) {p : StageType.{u} α k}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α (k + 1)}
    (htb : tb ∈ p.cofaces) (htop : ∀ x, tb.label x = ⊤ → Fin.last k ∉ tb.toCellScheme.scope x) :
    ∃ (D : StageType.{u} α (k + 2)) (a : Label.{u}), AtStage α a ∧ IsLowDisplay t' tb D a := by
  obtain ⟨D, hD, h₁, h₂⟩ :=
    exists_pinned_extension_of_isSuccPrelimit hα.isSuccPrelimit ht' hp htb.1 htb.2
  obtain ⟨o, hoα, ho⟩ := D.exists_lt_forall_label_lt hα
  have hoα' : (o : Label.{u}) < α := by exact_mod_cast hoα
  exact ⟨D, o, .inl hoα', IsLowDisplay.of_forall_top_root hD h₁ h₂ htop (ne_top_of_lt hoα')
    fun i hi ↦ (ho i hi).le⟩

end StageType

namespace Realization

open StageType

/-- **The bounded coatom form from LOW displays**: LOW displays at source-gap contexts give
bounded coatom cutoff determination for the source-gap contexts with the lost point last.  The
coface is the LOW display of `(t', tb)`, and the cutoff is a permitted cutoff above its
threshold. -/
theorem BoundedCoatomCutoffDetermination.of_hasLowDisplays (hlow : HasLowDisplays.{u}) :
    BoundedCoatomCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextLast K h where
  exists_coface α K n k t' g p hα ht' hP hp tb htb hK d hd := by
    obtain ⟨l, o, r, hl, hs⟩ := hP
    obtain rfl : l = Fin.last k := Fin.ext (by simp only [Fin.val_last]; omega)
    obtain ⟨D, a, ha, hD⟩ :=
      hlow t' tb p o r hα ⟨ht', htb.1, hp, htb.2, hs.castSuccEmb, hK⟩
    obtain ⟨δ, hδ, hdet⟩ := hD.exists_cutoff hα ha hd
    exact ⟨D, hD.mem_cofaces, hD.face_donor, δ, hδ, hdet⟩

/-- **(R2) for receiving models from LOW displays at source-gap contexts**: the bounded coatom
form (`BoundedCoatomCutoffDetermination.of_hasLowDisplays`) through the compiled acquisition with
the first coatom closed and the bounded pinned extension
(`receivingResidualReceiving_of_boundedCoatom_sourceGapLast`). -/
theorem receivingResidualReceiving_of_hasLowDisplays (hlow : HasLowDisplays.{u}) :
    ReceivingResidualReceiving.{u, w} :=
  receivingResidualReceiving_of_boundedCoatom_sourceGapLast
    (BoundedCoatomCutoffDetermination.of_hasLowDisplays hlow)

end Realization

namespace MainTheorem

open FirstOrder Language baseLanguage Realization StageType Expansion

/-- **The thin `ℵ₁` spectrum with (R2) from LOW displays**: the three-hypothesis receiving form
(`densitySentence_hasThinAlephOneSpectrum_of_receivingModels'`) with (R2) for receiving models
given by LOW displays at source-gap contexts
(`Realization.receivingResidualReceiving_of_hasLowDisplays`).  Conditional on (R4) for receiving
models (`hR4`), LOW displays at source-gap contexts (`hlow`), and (R3) for receiving models
(`hhol`); none of the three is proved here. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_lowDisplays
    (hR4 : ReceivingStableCappedReceiving.{0}) (hlow : HasLowDisplays.{0})
    (hhol : HollowReceiving.{0, 0} IsReceivingCoverHollowAtBlock) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_receivingModels' hR4
    (receivingResidualReceiving_of_hasLowDisplays hlow) hhol

end MainTheorem

end VaughtConjecture
