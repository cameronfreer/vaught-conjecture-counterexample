/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowDisplay
import VaughtConjecture.MainTheorem.BoundedCoatomDetermination

/-!
# (R2) for receiving models from LOW displays at source-gap contexts

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3) and Layer 6 ("Status:
the hypotheses of the main theorem"); semantic contract, items 4, 5 and 8.

**LOW displays at source-gap contexts** (`StageType.HasLowDisplays`, a statement about stage
types; open).  At a limit stage, for every legal source-gap context `t'` of grade `K` on `k + 1`
points with the lost point last (`StageType.IsSourceGapContextAt` along `Fin.castSuccEmb` at
`Fin.last k`), with coatom face `p` along `Fin.castSuccEmb`, and every legal coface `tb` of `p` of
top grade at most `K`, the pair `(t', tb)` has a LOW display (`StageType.IsLowDisplay`) at a
threshold occurring at the stage: a legal `D` on `k + 2` points with faces `t'` and `tb`, such
that every lawful section of the rows of `D` with the private face literal and the observation of
`D` at a cutoff above the threshold has the donor face literal.  The separated form
(`StageType.HasSeparatedLowDisplays`, the separator and its reading, [Kni26, §3.3]) implies it
(`StageType.HasSeparatedLowDisplays.hasLowDisplays`, compiled in this repository).

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

/-- **LOW displays at source-gap contexts** (open): at every limit stage, for every legal
source-gap context `t'` of grade `K` on `k + 1` points with the lost point last, with coatom face
`p`, and every legal coface `tb` of `p` of top grade at most `K`, the pair `(t', tb)` has a LOW
display at a threshold occurring at the stage. -/
def HasLowDisplays : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K k : ℕ⦄ (t' : StageType.{u} α (k + 1)) (o r : Fin t'.card)
    (p : StageType.{u} α k), Order.IsSuccLimit α → t'.IsLegal →
      t'.IsSourceGapContextAt K Fin.castSuccEmb (Fin.last k) o r →
      restrictFace Fin.castSuccEmb t' = some p → ∀ tb ∈ p.cofaces, tb.topGrade ≤ K →
        ∃ (D : StageType.{u} α (k + 2)) (a : Label.{u}), AtStage α a ∧ IsLowDisplay t' tb D a

/-- **Separated LOW displays at source-gap contexts** (open): the statement of `HasLowDisplays`
with a separated display (`IsSeparatedLowDisplay`). -/
def HasSeparatedLowDisplays : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K k : ℕ⦄ (t' : StageType.{u} α (k + 1)) (o r : Fin t'.card)
    (p : StageType.{u} α k), Order.IsSuccLimit α → t'.IsLegal →
      t'.IsSourceGapContextAt K Fin.castSuccEmb (Fin.last k) o r →
      restrictFace Fin.castSuccEmb t' = some p → ∀ tb ∈ p.cofaces, tb.topGrade ≤ K →
        ∃ (D : StageType.{u} α (k + 2)) (lo hi : Fin D.card), IsSeparatedLowDisplay t' tb D lo hi

/-- **Separated displays give LOW displays** (`StageType.exists_isLowDisplay_of_separated`). -/
theorem HasSeparatedLowDisplays.hasLowDisplays (h : HasSeparatedLowDisplays.{u}) :
    HasLowDisplays.{u} := by
  intro α K k t' o r p hα ht' hs hp tb htb hK
  obtain ⟨D, lo, hi, hD⟩ := h t' o r p hα ht' hs hp tb htb hK
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
  exists_coface α K n k t' g p hα ht' hP hp tb htb hK d hd _ := by
    obtain ⟨l, o, r, hl, hs⟩ := hP
    obtain rfl : l = Fin.last k := Fin.ext (by simp only [Fin.val_last]; omega)
    obtain ⟨D, a, ha, hD⟩ := hlow t' o r p hα ht' hs.castSuccEmb hp tb htb hK
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
