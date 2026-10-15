/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.CodedLadderStable
import VaughtConjecture.MainTheorem.LowPaddedRoute
import VaughtConjecture.MainTheorem.StronglyCodedTerminalProperty

/-!
# The strongly coded LOW donor: the contracts of restricted (R2)

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3) and Layer 4 (the residual
comparison), in the strongly coded receiving class (`Realization.IsStronglyCodedReceiving`);
Correspondence, item 1 (the strongly coded legal stage types).

Restricted (R2), `Realization.StronglyCodedResidualReceiving ξ M`, is the premise of the residual
comparison in the class: a realization in the class at `λ_ξ` with the residual property `K` has
exact one-point receiving of the strongly coded cofaces of top grade at most `K`.  Its
unrestricted form, (R2) for receiving models (`Realization.ReceivingResidualReceiving`), is proved
by the bounded LOW determination (`Realization.receivingResidualReceiving_of_padded`).  This file
states what that construction has to keep for the restricted form, proves the steps other than the
construction of the LOW layer, and proves the acquisition in the class.  The construction of
the LOW layer with a strongly coded display is in
`VaughtConjecture.MainTheorem.StronglyCodedLowDisplay`, where restricted (R2) is proved
(`Realization.stronglyCodedResidualReceiving`): it is closed only with both the construction and
the acquisition closed, and both are.  Everything here is a native construction of this
repository; no correspondence with [AFK26] is claimed.

**Why the coface must be strongly coded.**  In the unrestricted route the determining coface `D'`
of the acquired context is realized by the finite-cut receiving of the model
(`Realization.HasFiniteCutReceiving.realizesOver_receivingFamily`).  In the class, receiving is
asked only for cofaces with strongly coded rows (the `receiving` field,
`Realization.HasFiniteCutReceivingIn`).  So `D'` must be strongly coded.  A forcing donor at one
cell (`ForcingDonorsIn`) is not a determination: threshold forcing at one cell does not determine
the whole donor face, and it is not used here.

**The existing determination contract** (unchanged): bounded coatom cutoff determination,
`Realization.BoundedCoatomCutoffDetermination`, at the source-gap contexts with the lost point last
(`StageType.IsSourceGapContextLast`); compiled from LOW displays
(`Realization.BoundedCoatomCutoffDetermination.of_hasLowDisplays`, with
`StageType.hasLowDisplays_of_padded`).

**1. The strongly coded LOW-donor contract**
(`Realization.StronglyCodedBoundedCoatomCutoffDetermination`, and at the source-gap contexts with
the lost point last `Realization.StronglyCodedLowDonorTarget`).  The statement of
`Realization.BoundedCoatomCutoffDetermination` with two premises added (the context `t'` and the
intermediate pinned extension `tb` are strongly coded) and one conclusion added (the determining
coface `D'`, the LOW determination donor, is strongly coded).  Its first-coatom form
(`Realization.StronglyCodedFirstCoatomCutoffDetermination`) and its general form
(`Realization.StronglyCodedCutoffDetermination`) add the premises that `t'` and the donor `d` are
strongly coded and the conclusion that the resulting coface is.

**2. The steps of the construction and their preservation of strong coding.**  The construction of
`Realization.receivingResidualReceiving_of_padded`, step by step:

* (S1) acquisition, `Realization.residualAcquisition_isSourceGapContextOff`
  (`Realization.exists_covers_isSourceGapContextAt`): the context is the type of a cover, hence
  strongly coded by the class field `isStronglyCoded`; nothing to keep.
* (S2) relabelling,
  `Realization.FirstCoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff`
  (`Realization.FirstCoatomCutoffDetermination.exists_coface_reindex`,
  `StageType.reindex_extendPerm_symm_mem_cofaces`): the relabelled context `t'.reindex σ` and the
  relabelled coface `D''.reindex (extendPerm σ).symm` are strongly coded when `t'` and `D''` are
  (`StageType.isStronglyCoded_reindex`, proved).  The strongly coded form of the step,
  `Realization.StronglyCodedRelabelTarget`, is proved (`Realization.stronglyCodedRelabelTarget`):
  the existing argument with strong coding carried, no new construction.
* (S3) the first coatom, `Realization.BoundedCoatomCutoffDetermination.firstCoatom`
  (`Realization.exists_mem_cofaces_restrictFace_eq_topGrade_le`,
  `StageType.exists_pinned_extension_topGrade_le`): the intermediate pinned extension `tb` is
  replaced by the bounded strongly coded one,
  `StageType.exists_stronglyCoded_pinned_extension_topGrade_le` (strongly coded, top grade at most
  `K`, both faces kept).  Proved:
  `Realization.StronglyCodedBoundedCoatomCutoffDetermination.firstCoatom`.
* (S4) the bounded coatom form, `Realization.BoundedCoatomCutoffDetermination.of_hasLowDisplays`
  (`StageType.IsLowDisplay.exists_cutoff`, `StageType.IsLowDisplay.mem_cofaces`,
  `StageType.IsLowDisplay.face_donor`): the coface is the LOW display itself, so it is strongly
  coded when the display is.  Proved, from strongly coded LOW displays
  (`StageType.HasStronglyCodedLowDisplays`):
  `Realization.stronglyCodedLowDonorTarget_of_hasStronglyCodedLowDisplays`.
* (S5) displays from layers, `StageType.hasLowDisplays_of_padded` =
  `StageType.HasSeparatedLowDisplays.hasLowDisplays` ∘
  `StageType.HasControlledLowDisplays.hasSeparatedLowDisplays` ∘
  `StageType.HasLowLayers.hasControlledLowDisplays`: the display `D` is the same at every stage,
  so it keeps strong coding.  Proved:
  `StageType.HasStronglyCodedLowLayersOn.hasStronglyCodedLowDisplays`.
* (S6) the cases, `StageType.hasLowLayers_of_padded` (`K < k`, `K = k`, `K = k + 1`): proved for
  the strongly coded form, `StageType.hasStronglyCodedLowLayersOn_of_targets`, from the three
  constructions below.
* (S7) the three constructions of the LOW layer, each a preservation target:
  `K < k`, `ProfileTower.exists_isLowLayer_pTower` (`StageType.hasLowLayersOn_lt`):
  `StageType.StronglyCodedPaddedLowLayersTarget`; `K = k`, `StageType.hasLowLayersOn_lowBotAll`
  (`ProfileTower.LowReading.exists_isLowLayer`): `StageType.StronglyCodedLowBotLowLayersTarget`;
  `K = k + 1`, `StageType.hasLowLayersOn_fullGradeAll` (`ProfileTower.exists_isLowLayer_top`):
  `StageType.StronglyCodedFullGradeLowLayersTarget`.  Proved in
  `VaughtConjecture.MainTheorem.StronglyCodedLowDisplay`
  (`StageType.stronglyCodedPaddedLowLayersTarget`, `StageType.stronglyCodedLowBotLowLayersTarget`,
  `StageType.stronglyCodedFullGradeLowLayersTarget`), with the strongly coded display (below).
* (S8) receiving and recovery, `Realization.receivingResidualReceiving_of_cutoffDetermination`
  (`Realization.exists_covers_snoc_of_isDeterminedWithin`): the coface is received by the class
  field `receiving`, given its strong coding; recovery uses exact consistency only.  Proved:
  `Realization.stronglyCodedResidualReceiving_of_cutoffDetermination`.

**The strongly coded LOW display** (closed in
`VaughtConjecture.MainTheorem.StronglyCodedLowDisplay`).  In all three cases of (S7) the display of
the existing construction is `CompletionBelowFullGrade.display`, the completed scheme over a level
of the profile tower of the seed of the family (`Seed.ofCoatoms`), labelled, with the apex added by
`StageType.addApex`.  Its apex row is the block coding of the labels (`StageType.apexRow`,
`Label.blockEncode`), which keeps the finite part of every label; labels are bounded in finite part
from below by self-visibility, not from above, so that row is not strongly coded in general.  The
strongly coded display (`CompletionBelowFullGrade.strongDisplay`) adds the strongly coded apex
(`StageType.addStrongApex`) instead; the LOW layer is read through the grade prefix below the full
grade, where the two displays agree.  Every operation creating rows has its own strong-coding result
there.

**3. The derivation** (`Realization.StronglyCodedResidualDerivationTarget`, proved:
`Realization.stronglyCodedResidualDerivationTarget`).  From the strongly coded LOW-donor contract
(`Realization.StronglyCodedLowDonorTarget`), the strongly coded relabelling
(`Realization.StronglyCodedRelabelTarget`) and the acquisition of source-gap contexts in the class
(`Realization.StronglyCodedSourceGapAcquisitionTarget`), restricted (R2) holds for every carrier.
The premises of the unrestricted route are mirrored: modelhood by the class
(`Realization.IsStronglyCodedReceiving`), the finite-cut receiving of the model by the class field
`receiving`, and `Realization.ResidualAcquisition` by
`Realization.StronglyCodedResidualAcquisition`.
The calibrated contexts of the class (`Realization.calibratedContextAcquisitionTarget`) are not a
premise: they are acquired at top-grade supremum `⊤` for (R4), while (R2) concerns a natural
top-grade supremum, where the acquired contexts are the source-gap contexts.  With the three LOW
layer targets in place of the contract: `Realization.stronglyCodedResidualReceiving_of_lowLayers`.
All three premises are proved (the acquisition and the relabelling here, the contract in
`VaughtConjecture.MainTheorem.StronglyCodedLowDisplay`), so restricted (R2) is proved there
(`Realization.stronglyCodedResidualReceiving`).

**4. The modelhood audit of the context acquisition** used by the unrestricted route for (R2),
`Realization.exists_covers_isSourceGapContextAt` (through
`Realization.residualAcquisition_isSourceGapContextOff`).  Each entry: the model-level use; where;
its status in the class.

* `IsModel.exists_covers_zero` and `IsModel.isGloballyRigidCore_empty_iff`; the positivity
  `K > 0`; **replaced** by `Realization.exists_covers_zero_of_isCovering` and
  `Realization.isGloballyRigidCore_empty_iff_of_hasLegalTypes` (in
  `VaughtConjecture.MainTheorem.StronglyCodedTerminalProperty`; at the block stage the same as
  `Realization.IsStronglyCodedReceiving.ne_zero_of_residual`).
* `IsModel.isConsistent`; the tail (`Realization.exists_forall_le_topGrade_eq`), the face of the
  cover above the tail, the type of the acquired cover; **class field** `isConsistent`.
* `IsModel.isCovering`; the tail, and the occurrence above it containing the cover
  (`Realization.IsCovering.exists_subset_support`); **class field** `isCovering`.
* `IsModel.isLegal`; the legality of the type above the tail, an input of
  `StageType.exists_isSourceGapContextAt_comap`; **class field** `hasLegalTypes`.
* no model; first loss, the owner and the gaps (`StageType.exists_isSourceGapContextAt_comap`);
  stage types only.
* no model; the strong coding of the acquired context; **class field** `isStronglyCoded` (the
  context is an actual type).

Saturation, the bottom pattern, uniformity and dominance are not used by the acquisition.  The
acquisition in the class is closed:
`Realization.IsStronglyCodedReceiving.exists_covers_isSourceGapContextAt` and
`Realization.stronglyCodedSourceGapAcquisitionTarget`, the existing argument with these
replacements.  Downstream of the acquisition the unrestricted route uses `IsModel.isLegal` (the
legality of the context: class field `hasLegalTypes`), `IsModel.isConsistent` (class field) and the
finite-cut receiving of the model (class field `receiving`, for the strongly coded coface).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label

/-! ### Strong coding under relabelling -/

namespace StageType

variable {α : Ordinal.{u}} {m n : ℕ}

/-- **Reindexing keeps strong coding**: the rows of `t.reindex e` are those of `t` restricted along
the bijection `e`. -/
theorem isStronglyCoded_reindex {t : StageType.{u} α n} (ht : t.rows.IsStronglyCoded)
    (e : Fin m ≃ Fin n) : (t.reindex e).rows.IsStronglyCoded :=
  Scheme.isStronglyCoded_comap ht e.toEmbedding

/-! ### Strongly coded LOW layers and LOW displays -/

section LowLayers

variable (S : ∀ (α : Ordinal.{u}) (_ k : ℕ) (t' _ : StageType.{u} α (k + 1)),
  StageType.{u} α k → Fin t'.card → Fin t'.card → Prop)

/-- **Strongly coded LOW layers on a class `S` of LOW families**: the statement of
`StageType.HasLowLayersOn S` for the families whose private context `t'` and donor `tb` are
strongly coded, with the display strongly coded. -/
def HasStronglyCodedLowLayersOn : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K k : ℕ⦄ (t' tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (o r : Fin t'.card), Order.IsSuccLimit α → IsLowFamily K t' tb p o r → S α K k t' tb p o r →
      t'.rows.IsStronglyCoded → tb.rows.IsStronglyCoded →
      ∃ (D : StageType.{u} α (k + 2)) (h₁ : restrictFace Fin.castSuccEmb D = some t')
        (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some tb) (G : Finset Label.{u})
        (entry : Fin D.card → LowField D → Label.{u}) (s : LowField D → Label.{u})
        (lo hi : Fin D.card), D.IsLegal ∧ D.rows.IsStronglyCoded ∧ D.label lo ≠ ⊤ ∧
          D.label hi = ⊤ ∧ IsLowLayer K h₁ h₂ o r G entry s lo hi

end LowLayers

/-- **Strongly coded LOW displays**: the statement of `StageType.HasLowDisplays` for the LOW
families whose private context `t'` and donor `tb` are strongly coded, with the display strongly
coded. -/
def HasStronglyCodedLowDisplays : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K k : ℕ⦄ (t' tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (o r : Fin t'.card), Order.IsSuccLimit α → IsLowFamily K t' tb p o r →
      t'.rows.IsStronglyCoded → tb.rows.IsStronglyCoded →
      ∃ (D : StageType.{u} α (k + 2)) (a : Label.{u}), AtStage α a ∧ IsLowDisplay t' tb D a ∧
        D.rows.IsStronglyCoded

/-- **Target: strong coding of the padded LOW layer** (`K < k`), the construction
`ProfileTower.exists_isLowLayer_pTower` of `StageType.hasLowLayersOn_lt`.  Proved with the strongly
coded display: `StageType.stronglyCodedPaddedLowLayersTarget`. -/
def StronglyCodedPaddedLowLayersTarget : Prop :=
  HasStronglyCodedLowLayersOn.{u} fun _ K k _ _ _ _ _ ↦ K < k

/-- **Target: strong coding of the LOW layer with the faces `⊥` above `K`** (used at `K = k`), the
construction of `StageType.hasLowLayersOn_lowBotAll`.  Proved with the strongly coded display:
`StageType.stronglyCodedLowBotLowLayersTarget`. -/
def StronglyCodedLowBotLowLayersTarget : Prop :=
  HasStronglyCodedLowLayersOn.{u} LowBotAllClass

/-- **Target: strong coding of the LOW layer at the full grade** (`K = k + 1`), the construction
of `StageType.hasLowLayersOn_fullGradeAll`.  Proved with the strongly coded display:
`StageType.stronglyCodedFullGradeLowLayersTarget`. -/
def StronglyCodedFullGradeLowLayersTarget : Prop :=
  HasStronglyCodedLowLayersOn.{u} LowFullGradeAllClass

/-- **Target: strong-coding preservation by the three constructions of the LOW layer**, the three
targets together. -/
def StronglyCodedLowLayersPreservationTarget : Prop :=
  StronglyCodedPaddedLowLayersTarget.{u} ∧ StronglyCodedLowBotLowLayersTarget.{u} ∧
    StronglyCodedFullGradeLowLayersTarget.{u}

/-- **Strongly coded LOW layers for every LOW family from the three constructions**: the case
analysis of `StageType.hasLowLayers_of_padded` (`K < k`, `K = k` with no grade in `(K, k]`,
`K = k + 1`). -/
theorem hasStronglyCodedLowLayersOn_of_targets (h : StronglyCodedLowLayersPreservationTarget.{u}) :
    HasStronglyCodedLowLayersOn.{u} fun _ _ _ _ _ _ _ _ ↦ True := by
  obtain ⟨hlt, heq, hfull⟩ := h
  intro α K k t' tb p o r hα hF _ ht' htb
  rcases lt_trichotomy K k with hKk | hKk | hKk
  · exact hlt t' tb p o r hα hF hKk ht' htb
  · subst hKk
    exact heq t' tb p o r hα hF
      ⟨le_rfl, fun _ h1 h2 ↦ absurd (h1.trans_le h2) (lt_irrefl _),
        fun _ h1 h2 ↦ absurd (h1.trans_le h2) (lt_irrefl _)⟩ ht' htb
  · exact hfull t' tb p o r hα hF (show K = k + 1 by have := hF.grade_le_succ; omega) ht' htb

/-- **Strongly coded LOW layers give strongly coded LOW displays**: the chain of
`StageType.HasLowLayersOn.hasLowDisplaysOn` (the controller reading, the separated display, a
threshold at the stage) keeps the display. -/
theorem HasStronglyCodedLowLayersOn.hasStronglyCodedLowDisplays
    (h : HasStronglyCodedLowLayersOn.{u} fun _ _ _ _ _ _ _ _ ↦ True) :
    HasStronglyCodedLowDisplays.{u} := by
  intro α K k t' tb p o r hα hF ht' htb
  obtain ⟨D, h₁, h₂, G, entry, s, lo, hi, hD, hDs, hlo, hhi, hL⟩ :=
    h t' tb p o r hα hF trivial ht' htb
  have hs := hF.isSourceGapContextAt
  have hr : t'.toCellScheme.grade r ≤ K := hs.topGrade_eq ▸ grade_le_topGrade hs.label_lost
  obtain ⟨a, ha, hDa⟩ := exists_isLowDisplay_of_separated hα
    (IsSeparatedLowDisplay.of_controllerReading hs hF.topGrade_donor hD h₁ h₂ hlo hhi
      (congrArg Prod.snd hL.gradedIndex_lo).le (congrArg Prod.snd hL.gradedIndex_hi).le
      (hL.isControllerReading hs.grade_owner.le hr hF.topGrade_donor))
  exact ⟨D, a, ha, hDa, hDs⟩

end StageType

/-! ### The strongly coded determination contracts -/

namespace Realization

open StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **Strongly coded bounded coatom cutoff determination** for `P`, the strongly coded LOW-donor
contract: the statement of `Realization.BoundedCoatomCutoffDetermination` (unchanged otherwise)
for a strongly coded context `t'` and a strongly coded intermediate pinned extension `tb`, with
the determining coface `D'` (the LOW determination donor) strongly coded. -/
structure StronglyCodedBoundedCoatomCutoffDetermination
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop) :
    Prop where
  /-- Every donor through a strongly coded coface of top grade at most `K` of the coatom face is
  determined at a cutoff, by a strongly coded coface. -/
  exists_coface ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α (k + 1))
    (g : Fin n ↪ Fin k) (p : StageType.{u} α k) :
    Order.IsSuccLimit α → t'.IsLegal → t'.rows.IsStronglyCoded →
      P K t' (g.trans Fin.castSuccEmb) → restrictFace Fin.castSuccEmb t' = some p →
        ∀ tb ∈ p.cofaces, tb.rows.IsStronglyCoded → tb.topGrade ≤ K →
          ∀ d : StageType.{u} α (n + 1), restrictFace (extendByLast g) tb = some d →
            ∃ D' ∈ t'.cofaces, D'.rows.IsStronglyCoded ∧
              restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
              ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
                IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d

/-- **Target: the strongly coded LOW-donor contract** at the source-gap contexts with the lost
point last, the contexts of `Realization.BoundedCoatomCutoffDetermination.of_hasLowDisplays`.  It
follows from strongly coded LOW displays
(`Realization.stronglyCodedLowDonorTarget_of_hasStronglyCodedLowDisplays`); proved:
`Realization.stronglyCodedLowDonorTarget`. -/
def StronglyCodedLowDonorTarget : Prop :=
  StronglyCodedBoundedCoatomCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextLast K h

/-- **Strongly coded cutoff determination at the first coatom** for `P`: the statement of
`Realization.FirstCoatomCutoffDetermination` for a strongly coded context and a strongly coded
donor `d`, with the resulting coface strongly coded. -/
structure StronglyCodedFirstCoatomCutoffDetermination
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop) :
    Prop where
  /-- Every strongly coded donor over the root in the first coatom is determined at a cutoff, by a
  strongly coded coface. -/
  exists_coface ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α (k + 1))
    (g : Fin n ↪ Fin k) (p : StageType.{u} α k) :
    Order.IsSuccLimit α → t'.IsLegal → t'.rows.IsStronglyCoded →
      P K t' (g.trans Fin.castSuccEmb) → restrictFace Fin.castSuccEmb t' = some p →
        ∀ t : StageType.{u} α n, restrictFace (g.trans Fin.castSuccEmb) t' = some t →
          ∀ d ∈ t.cofaces, d.rows.IsStronglyCoded → d.topGrade ≤ K →
            ∃ D' ∈ t'.cofaces, D'.rows.IsStronglyCoded ∧ ∃ δ : Label.{u},
              IsPermittedCutoff α δ ∧
                IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d

/-- **Strongly coded cutoff determination** for `P`: the statement of
`Realization.CutoffDetermination` for a strongly coded context and a strongly coded donor `d`, with
the resulting coface strongly coded. -/
structure StronglyCodedCutoffDetermination
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop) :
    Prop where
  /-- Every strongly coded coface of the face is determined at a cutoff, by a strongly coded
  coface. -/
  exists_coface ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) :
    Order.IsSuccLimit α → t'.IsLegal → t'.rows.IsStronglyCoded → P K t' h →
      ∀ t : StageType.{u} α n, restrictFace h t' = some t →
        ∀ d ∈ t.cofaces, d.rows.IsStronglyCoded → d.topGrade ≤ K →
          ∃ D' ∈ t'.cofaces, D'.rows.IsStronglyCoded ∧ ∃ δ : Label.{u},
            IsPermittedCutoff α δ ∧ IsDeterminedWithin (receivingFamily D' δ) t' h d

/-- **Target: the strongly coded relabelling**, the statement of
`Realization.FirstCoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff` for the
strongly coded forms.  Proved: `Realization.stronglyCodedRelabelTarget` (the relabelled context and
coface are strongly coded, `StageType.isStronglyCoded_reindex`). -/
def StronglyCodedRelabelTarget : Prop :=
  StronglyCodedFirstCoatomCutoffDetermination.{u} (fun K t' h ↦ t'.IsSourceGapContextLast K h) →
    StronglyCodedCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextOff K h

variable {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop}

/-- **The strongly coded first coatom from the strongly coded bounded coatom form**, for a
predicate `P` whose contexts of grade `K` have top grade at most `K` (`hK`): the argument of
`Realization.BoundedCoatomCutoffDetermination.firstCoatom`, with the intermediate pinned extension
`tb` from the bounded strongly coded pinned extension
(`StageType.exists_stronglyCoded_pinned_extension_topGrade_le`).  The coatom face is strongly coded
as a face of `t'` (`StageType.isStronglyCoded_of_restrictFace`). -/
theorem StronglyCodedBoundedCoatomCutoffDetermination.firstCoatom
    (hdet : StronglyCodedBoundedCoatomCutoffDetermination.{u} P)
    (hK : ∀ ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
      P K t' h → t'.topGrade ≤ K) :
    StronglyCodedFirstCoatomCutoffDetermination.{u} P where
  exists_coface _ _ _ _ t' g p hα ht' hts hP hp t ht d hd hds hdK := by
    have hpt : restrictFace g p = some t := (restrictFace_trans t' _ g hp).trans ht
    obtain ⟨tb, htb, htbK, htbp, htbd⟩ := exists_stronglyCoded_pinned_extension_topGrade_le hα
      ⟨ht'.restrictFace _ hp, isStronglyCoded_of_restrictFace hp hts⟩ hpt ⟨hd.1, hds⟩ hd.2
      ((topGrade_le_of_restrictFace hp).trans (hK _ _ hP)) hdK
    obtain ⟨D', hD', hD's, -, hrest⟩ :=
      hdet.exists_coface t' g p hα ht' hts hP hp tb ⟨htb.1, htbp⟩ htb.2 htbK d htbd
    exact ⟨D', hD', hD's, hrest⟩

/-- **The strongly coded LOW-donor contract from strongly coded LOW displays**: the argument of
`Realization.BoundedCoatomCutoffDetermination.of_hasLowDisplays`; the coface is the display, so it
is strongly coded. -/
theorem stronglyCodedLowDonorTarget_of_hasStronglyCodedLowDisplays
    (hlow : HasStronglyCodedLowDisplays.{u}) : StronglyCodedLowDonorTarget.{u} where
  exists_coface α K n k t' g p hα ht' hts hP hp tb htb htbs hK d hd := by
    obtain ⟨l, o, r, hl, hs⟩ := hP
    obtain rfl : l = Fin.last k := Fin.ext (by simp only [Fin.val_last]; omega)
    obtain ⟨D, a, ha, hD, hDs⟩ :=
      hlow t' tb p o r hα ⟨ht', htb.1, hp, htb.2, hs.castSuccEmb, hK⟩ hts htbs
    obtain ⟨δ, hδ, hdet⟩ := hD.exists_cutoff hα ha hd
    exact ⟨D, hD.mem_cofaces, hDs, hD.face_donor, δ, hδ, hdet⟩

/-- **The strongly coded first coatom at the source-gap contexts with the lost point last**, from
the strongly coded LOW-donor contract: the contexts have top grade `K`. -/
theorem StronglyCodedLowDonorTarget.firstCoatom (hdet : StronglyCodedLowDonorTarget.{u}) :
    StronglyCodedFirstCoatomCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextLast K h :=
  StronglyCodedBoundedCoatomCutoffDetermination.firstCoatom hdet
    fun _ _ _ _ _ _ hs ↦ hs.topGrade_eq.le

/-- **The strongly coded first coatom after a relabelling**: the argument of
`Realization.FirstCoatomCutoffDetermination.exists_coface_reindex`; the relabelled context and the
relabelled coface are strongly coded (`StageType.isStronglyCoded_reindex`). -/
theorem StronglyCodedFirstCoatomCutoffDetermination.exists_coface_reindex
    (hdet : StronglyCodedFirstCoatomCutoffDetermination.{u} P) {K : ℕ} (hα : Order.IsSuccLimit α)
    {t' : StageType.{u} α (k + 1)} (ht' : t'.IsLegal) (hts : t'.rows.IsStronglyCoded)
    (σ : Equiv.Perm (Fin (k + 1))) {g : Fin n ↪ Fin k}
    (hP : P K (t'.reindex σ) (g.trans Fin.castSuccEmb)) {p : StageType.{u} α k}
    (hp : restrictFace Fin.castSuccEmb (t'.reindex σ) = some p) {t : StageType.{u} α n}
    (ht : restrictFace ((g.trans Fin.castSuccEmb).trans σ.toEmbedding) t' = some t)
    {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces) (hds : d.rows.IsStronglyCoded)
    (hdK : d.topGrade ≤ K) :
    ∃ D' ∈ t'.cofaces, D'.rows.IsStronglyCoded ∧ ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
      IsDeterminedWithin (receivingFamily D' δ) t'
        ((g.trans Fin.castSuccEmb).trans σ.toEmbedding) d := by
  obtain ⟨D'', hD'', hD''s, δ, hδ, hdet''⟩ := hdet.exists_coface (t'.reindex σ) g p hα
    (ht'.reindex σ) (isStronglyCoded_reindex hts σ) hP hp t (by rwa [restrictFace_reindex]) d hd
    hds hdK
  exact ⟨_, reindex_extendPerm_symm_mem_cofaces hD'', isStronglyCoded_reindex hD''s _, δ, hδ,
    hdet''.reindex_extendPerm⟩

/-- **Strongly coded cutoff determination with the coatom off the lost point closed, from the
strongly coded first coatom with the lost point last**: the argument of
`Realization.FirstCoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff` (the
transposition of the lost point with the last point), with strong coding carried. -/
theorem StronglyCodedFirstCoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff
    (hdet : StronglyCodedFirstCoatomCutoffDetermination.{u}
      fun K t' h ↦ t'.IsSourceGapContextLast K h) :
    StronglyCodedCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextOff K h where
  exists_coface α K n k t' h hα ht' hts hP t ht d hd hds hdK := by
    obtain ⟨l, o, r, hs, hface⟩ := hP
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := l.2; omega⟩
    set σ : Equiv.Perm (Fin (j + 1)) := Equiv.swap l (Fin.last j) with hσ
    have hsurj := t'.toScheme.surjective_cellMap_equiv σ
    obtain ⟨o', rfl⟩ := hsurj o
    obtain ⟨r', rfl⟩ := hsurj r
    have hs' := hs.reindex (σ := σ)
    rw [show σ.symm l = Fin.last j by simp [hσ]] at hs'
    have hne (i : Fin n) : (h.trans σ.symm.toEmbedding) i ≠ Fin.last j :=
      fun hi ↦ hs'.notMem_range ⟨i, hi⟩
    let g : Fin n ↪ Fin j :=
      ⟨fun i ↦ ((h.trans σ.symm.toEmbedding) i).castPred (hne i), fun a b hab ↦
        (h.trans σ.symm.toEmbedding).injective (by simpa using congrArg Fin.castSucc hab)⟩
    have hg : g.trans Fin.castSuccEmb = h.trans σ.symm.toEmbedding :=
      Function.Embedding.ext fun i ↦ by simp [g]
    have hroot : (g.trans Fin.castSuccEmb).trans σ.toEmbedding = h := by
      rw [hg]
      exact Function.Embedding.ext fun i ↦ by simp
    have hcoatom : univ.map (Fin.castSuccEmb.trans σ.toEmbedding) = univ.erase l := by
      rw [← Finset.map_map, ← erase_cons (s := univ.map Fin.castSuccEmb) (a := Fin.last j)
        (by simp [Fin.castSucc_ne_last]), ← Fin.univ_castSuccEmb, map_erase, map_univ_equiv]
      simp [hσ]
    have hp : StageType.restrictFace Fin.castSuccEmb (t'.reindex σ) =
        some (t'.comap (Fin.castSuccEmb.trans σ.toEmbedding) (hcoatom ▸ hface)) := by
      rw [StageType.restrictFace_reindex]
      exact StageType.restrictFace_of_mem t' _ _
    have := hdet.exists_coface_reindex hα ht' hts σ ⟨Fin.last j, o', r', by simp, hg ▸ hs'⟩ hp
      (hroot ▸ ht) hd hds hdK
    rwa [hroot] at this

/-- **The strongly coded relabelling** (proved):
`Realization.StronglyCodedFirstCoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff`.
-/
theorem stronglyCodedRelabelTarget : StronglyCodedRelabelTarget.{u} :=
  fun hdet ↦ hdet.cutoffDetermination_isSourceGapContextOff

/-! ### Acquisition in the class, and the derivation of restricted (R2) -/

/-- **Residual acquisition in the strongly coded receiving class** for `P`: the statement of
`Realization.ResidualAcquisition` with the model replaced by a realization in the class. -/
structure StronglyCodedResidualAcquisition
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop) :
    Prop where
  /-- Every cover extends to a cover of an acquired context. -/
  exists_context ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄ ⦃K : ℕ⦄ :
    Order.IsSuccLimit α → R.IsStronglyCodedReceiving →
      (¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
        R.IsGloballyRigidCore c) →
      R.topGradeSup = K → ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
        ∃ (k : ℕ) (t' : StageType.{u} α k) (c' : Fin k → M) (h : Fin n ↪ Fin k),
          R.Covers t' c' ∧ c' ∘ h = c ∧ P K t' h

/-- **Target: acquisition of source-gap contexts in the strongly coded receiving class**, with the
coatom off the lost point closed: the statement of
`Realization.residualAcquisition_isSourceGapContextOff` in the class.  The existing proof uses
modelhood only through exact consistency, covering, legal types and the positivity of the residual
grade, each replaced in the class (the list of the module docstring); proved:
`Realization.stronglyCodedSourceGapAcquisitionTarget`. -/
def StronglyCodedSourceGapAcquisitionTarget : Prop :=
  StronglyCodedResidualAcquisition.{u, w} fun K t' h ↦ t'.IsSourceGapContextOff K h

/-- A tuple whose values are among the values of `φ` factors through `φ` along an embedding. -/
private theorem exists_embedding_comp_eq' {β : Type*} {c : Fin n → β}
    (hc : Function.Injective c) {φ : Fin k → β} (h : ∀ i, ∃ j, φ j = c i) :
    ∃ e : Fin n ↪ Fin k, φ ∘ e = c := by
  choose j hj using h
  exact ⟨⟨j, fun a b hab ↦ hc (by rw [← hj a, ← hj b, hab])⟩, funext hj⟩

/-- **Residual acquisition of a source-gap context in the strongly coded receiving class**, in the
form with the lost point last: the argument of `Realization.exists_covers_isSourceGapContextAt`,
with modelhood replaced by the class.  The positivity `K > 0` uses
`Realization.exists_covers_zero_of_isCovering` and
`Realization.isGloballyRigidCore_empty_iff_of_hasLegalTypes`; the tail, the occurrence above it and
the type of the acquired cover use the fields `isConsistent` and `isCovering`; the legality of the
type above the tail uses the field `hasLegalTypes`; the rest is
`StageType.exists_isSourceGapContextAt_comap`, about stage types only. -/
theorem IsStronglyCodedReceiving.exists_covers_isSourceGapContextAt {M : Type w}
    {R : Realization.{u, w} α M} (hα : Order.IsSuccLimit α) (hR : R.IsStronglyCodedReceiving)
    (hcore : ¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
      R.IsGloballyRigidCore c)
    {K : ℕ} (hK : R.topGradeSup = K) {t : StageType.{u} α n} {c : Fin n → M}
    (hc : R.Covers t c) :
    ∃ (k : ℕ) (t' : StageType.{u} α (k + 1)) (c' : Fin (k + 1) → M) (e : Fin n ↪ Fin k),
      R.Covers t' c' ∧ c' ∘ (e.trans Fin.castSuccEmb) = c ∧
        univ.map Fin.castSuccEmb ∈ t'.toCellScheme.faces ∧
        ∃ o r, t'.IsSourceGapContextAt K (e.trans Fin.castSuccEmb) (Fin.last k) o r := by
  classical
  -- the eventual top grade is positive: otherwise the empty tuple is a globally rigid core
  have hKpos : 0 < K := by
    refine Nat.pos_of_ne_zero fun hK0 ↦ hcore ?_
    obtain ⟨p, hp⟩ := exists_covers_zero_of_isCovering hR.isConsistent hR.isCovering
    exact ⟨0, p, ![], hp, (isGloballyRigidCore_empty_iff_of_hasLegalTypes hR.hasLegalTypes
      hα).mpr (by rw [hK, hK0]; rfl)⟩
  -- the tail, and an occurrence `z` above it containing the points of `c`
  obtain ⟨x₀, hx₀⟩ := exists_forall_le_topGrade_eq hR.isConsistent hR.isCovering hK
  obtain ⟨z, hz⟩ := hR.isCovering.exists_subset_support (univ.image c ∪ x₀.support)
  have hzK : z.type.topGrade = K := hx₀ z (subset_union_right.trans hz)
  -- `z` is not a globally rigid core
  have hnr : ¬ R.IsGloballyRigidCore z.tuple :=
    fun h ↦ hcore ⟨_, _, _, covers_of_eval _ z.eval_tuple, h⟩
  simp only [IsGloballyRigidCore, StageType.IsRigidCoreIn] at hnr
  push Not at hnr
  obtain ⟨m, Q, x, e₀, hx, hxe, H, hH, hcoreH, d₀, hd₀, hd₀H⟩ := hnr
  -- the occurrence of `x` lies above `z`, so `Q` has top grade `K`
  let y : R.Occurrence := ⟨m, ⟨x, hx.injective⟩, Q, hx.eval_eq⟩
  have hzy : z ≤ y := by
    intro a ha
    obtain ⟨j, rfl⟩ := (Occurrence.mem_support _).mp ha
    exact (Occurrence.mem_support _).mpr ⟨e₀ j, congrFun hxe j⟩
  have hQK : Q.topGrade = K := hx₀ y ((subset_union_right.trans hz).trans hzy)
  -- the face of `Q` along `e₀` is the type of `z`
  have hface : StageType.restrictFace e₀ Q = some z.type := by
    have he : e₀.trans ⟨x, hx.injective⟩ = z.tuple := Function.Embedding.ext fun j ↦ congrFun hxe j
    rw [← hR.isConsistent _ Q e₀ hx.eval_eq, he, z.eval_tuple]
  have hG : univ.map e₀ ∈ Q.toCellScheme.faces := ((StageType.restrictFace_eq_some_iff _ _).mp
    hface).1
  have hfull (d : Fin Q.card) (hd : Q.toCellScheme.scope d ⊆ univ.map e₀) (hdt : Q.label d = ⊤) :
      d ∈ H :=
    hcoreH d (mem_filter.mpr ⟨mem_univ _, hd⟩) hdt
  -- a top cell `s` of grade `K` of the type of `z`, visible through `e₀` in `Q`
  obtain ⟨s, hs, hsK⟩ := StageType.exists_grade_eq_topGrade (t := z.type) (hzK ▸ hKpos)
  have hsG : Q.toCellScheme.scope (StageType.faceCell hface s) ⊆ univ.map e₀ := by
    rw [StageType.scope_faceCell]
    exact map_subset_map.mpr (subset_univ _)
  -- the positions `g` of `c` in `x`, inside the range of `e₀`
  have hpos (i : Fin n) : ∃ j₀, x (e₀ j₀) = c i := by
    obtain ⟨j₀, hj₀⟩ := (Occurrence.mem_support _).mp
      (hz (mem_union_left _ (mem_image_of_mem c (mem_univ i))))
    exact ⟨j₀, (congrFun hxe j₀).trans hj₀⟩
  obtain ⟨g, hg⟩ := exists_embedding_comp_eq' hc.injective (φ := x) fun i ↦
    let ⟨j₀, hj₀⟩ := hpos i
    ⟨e₀ j₀, hj₀⟩
  have hgG (i : Fin n) : g i ∈ univ.map e₀ := by
    obtain ⟨j₀, hj₀⟩ := hpos i
    exact mem_map.mpr ⟨j₀, mem_univ _, hx.injective (hj₀.trans (congrFun hg i).symm)⟩
  obtain ⟨k, ι, hι, e, he, hcf, o, r, hsg⟩ := StageType.exists_isSourceGapContextAt_comap
    (hR.hasLegalTypes _ _ hx.eval_eq) hQK hH hG hfull ⟨d₀, hd₀, hd₀H⟩
    ((StageType.label_faceCell hface s).trans hs)
    ((StageType.grade_faceCell hface s).trans (hsK.trans hzK)) hsG g.injective hgG
  refine ⟨k, Q.comap ι hι, x ∘ ι, e, ⟨hx.injective.comp ι.injective, ?_⟩, ?_,
    (StageType.map_univ_mem_comap_faces_iff Q ι Fin.castSuccEmb hι).mpr hcf, o, r, hsg⟩
  · have hxι : (⟨x ∘ ι, hx.injective.comp ι.injective⟩ : Fin (k + 1) ↪ M) =
        ι.trans ⟨x, hx.injective⟩ := Function.Embedding.ext fun _ ↦ rfl
    rw [hxι, hR.isConsistent _ Q ι hx.eval_eq, StageType.restrictFace_of_mem _ _ hι]
  · funext i
    simp only [Function.comp_apply, Function.Embedding.trans_apply, Fin.coe_castSuccEmb, he]
    exact congrFun hg i

/-- **Acquisition of source-gap contexts in the strongly coded receiving class** (proved): the
acquired context of `Realization.IsStronglyCodedReceiving.exists_covers_isSourceGapContextAt`,
whose first coatom, the complement of the last point, is closed. -/
theorem stronglyCodedSourceGapAcquisitionTarget :
    StronglyCodedSourceGapAcquisitionTarget.{u, w} where
  exists_context _ _ _ _ hα hR hcore hK _ _ _ hc := by
    obtain ⟨k, t', c', e, hc', hcc', hcf, o, r, hs⟩ :=
      hR.exists_covers_isSourceGapContextAt hα hcore hK hc
    refine ⟨k + 1, t', c', _, hc', hcc', Fin.last k, o, r, hs, ?_⟩
    rwa [Fin.univ_castSuccEmb, erase_cons]

/-- **Restricted (R2) from acquisition and strongly coded cutoff determination** in the class, for
any predicate `P` on acquired contexts: the argument of
`Realization.receivingResidualReceiving_of_cutoffDetermination`.  The acquired context is the type
of a cover, so it is legal and strongly coded by the class fields; the strongly coded coface is
received by the class field `receiving`. -/
theorem stronglyCodedResidualReceiving_of_cutoffDetermination {ξ : Ordinal.{0}} {M : Type w}
    {P : ∀ {α : Ordinal.{0}} {n k : ℕ}, ℕ → StageType.{0} α k → (Fin n ↪ Fin k) → Prop}
    (hacq : StronglyCodedResidualAcquisition.{0, w} P)
    (hdet : StronglyCodedCutoffDetermination.{0} P) : StronglyCodedResidualReceiving ξ M := by
  intro R K hR hres n t c hc d hd hds hdK
  have hα := isSuccLimit_blockStage ξ
  obtain ⟨k, t', c', h, hc', hcc', hP⟩ := hacq.exists_context hα hR hres.1 hres.2 t c hc
  obtain ⟨D', hD', hD's, δ, hδ, hdet'⟩ := hdet.exists_coface t' h hα
    (hR.hasLegalTypes _ _ hc'.eval_eq) (hR.isStronglyCoded _ _ hc'.eval_eq) hP t
    (restrictFace_of_covers hR.isConsistent hc hc' hcc') d hd hds (by exact_mod_cast hdK)
  rw [← hcc']
  exact exists_covers_snoc_of_isDeterminedWithin hR.isConsistent hc'
    (hR.receiving ⟨k, ⟨c', hc'.injective⟩, t', hc'.eval_eq⟩ D' hD' hD's δ hδ) hdet'

section Derivation

variable (ξ : Ordinal.{0}) (M : Type w)

/-- **Target: the derivation of restricted (R2)** from the strongly coded LOW-donor contract, with
the remaining premises of the unrestricted route in their class forms: the acquisition of
source-gap contexts in the class and the strongly coded relabelling. -/
def StronglyCodedResidualDerivationTarget : Prop :=
  StronglyCodedSourceGapAcquisitionTarget.{0, w} → StronglyCodedRelabelTarget.{0} →
    StronglyCodedLowDonorTarget.{0} → StronglyCodedResidualReceiving ξ M

/-- **The derivation of restricted (R2)** (direct composition): the strongly coded first coatom
(`Realization.StronglyCodedLowDonorTarget.firstCoatom`), the relabelling, and
`Realization.stronglyCodedResidualReceiving_of_cutoffDetermination`. -/
theorem stronglyCodedResidualDerivationTarget : StronglyCodedResidualDerivationTarget ξ M :=
  fun hacq hrel hdet ↦ stronglyCodedResidualReceiving_of_cutoffDetermination hacq
    (hrel hdet.firstCoatom)

/-- **Restricted (R2) from the three LOW-layer targets**, with the acquisition and the relabelling:
`Realization.stronglyCodedResidualDerivationTarget` with the contract from strongly coded LOW
layers (`StageType.hasStronglyCodedLowLayersOn_of_targets`). -/
theorem stronglyCodedResidualReceiving_of_lowLayers
    (hacq : StronglyCodedSourceGapAcquisitionTarget.{0, w}) (hrel : StronglyCodedRelabelTarget.{0})
    (hlayers : StronglyCodedLowLayersPreservationTarget.{0}) :
    StronglyCodedResidualReceiving ξ M :=
  stronglyCodedResidualDerivationTarget ξ M hacq hrel
    (stronglyCodedLowDonorTarget_of_hasStronglyCodedLowDisplays
      (hasStronglyCodedLowLayersOn_of_targets hlayers).hasStronglyCodedLowDisplays)

end Derivation

end Realization

end VaughtConjecture
