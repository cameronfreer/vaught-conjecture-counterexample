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
states what that construction has to keep for the restricted form, and composes the steps that are
direct.  Everything here is a native construction of this repository; no correspondence with
[AFK26] is claimed.

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
  (`StageType.isStronglyCoded_reindex`, proved).  The strongly coded form of the step is stated,
  `Realization.StronglyCodedRelabelTarget`; its proof is the existing one with strong coding
  carried, no new construction.
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
* (S7) the three constructions of the LOW layer, each stated as a preservation target:
  `K < k`, `ProfileTower.exists_isLowLayer_pTower` (`StageType.hasLowLayersOn_lt`):
  `StageType.StronglyCodedPaddedLowLayersTarget`; `K = k`, `StageType.hasLowLayersOn_lowBotAll`
  (`ProfileTower.LowReading.exists_isLowLayer`): `StageType.StronglyCodedLowBotLowLayersTarget`;
  `K = k + 1`, `StageType.hasLowLayersOn_fullGradeAll` (`ProfileTower.exists_isLowLayer_top`):
  `StageType.StronglyCodedFullGradeLowLayersTarget`.  **Not proved; a construction is missing**
  (below).
* (S8) receiving and recovery, `Realization.receivingResidualReceiving_of_cutoffDetermination`
  (`Realization.exists_covers_snoc_of_isDeterminedWithin`): the coface is received by the class
  field `receiving`, given its strong coding; recovery uses exact consistency only.  Proved:
  `Realization.stronglyCodedResidualReceiving_of_cutoffDetermination`.

**The missing construction: a strongly coded LOW display.**  In all three cases of (S7) the display
is `CompletionBelowFullGrade.display`, the completed scheme over a level of the profile tower of the
seed of the family (`Seed.ofCoatoms`), labelled, with the apex added by `StageType.addApex`.  Of its
parts:

* the amalgam of the seed is strongly coded when `t'` and `tb` are (`Seed.isStronglyCoded_amalgam`,
  compiled);
* the unpadded levels are strongly coded (`ProfileTower.isStronglyCoded_lvl`,
  `ProfileTower.Lvl.Good.isStronglyCoded_next`, compiled), and so is the field layer of a
  completion over a strongly coded scheme (`Scheme.isStronglyCoded_fieldLayer`, compiled); the
  levels used by the three constructions (the catalogue layers, the state levels and the padded
  levels `ProfileTower.pTower`, whose new rows carry agreement heights of states) have no strong
  coding result in the repository;
* the apex row of `StageType.addApex` is the block coding of the labels (`StageType.apexRow`,
  `Label.blockEncode`), which keeps the finite part of every label; labels are bounded in finite
  part from below by self-visibility, not from above, so that row is not strongly coded in
  general.  The strongly coded apex `StageType.addStrongApex` exists (legal, strongly coded over a
  strongly coded scheme, keeping the proper faces), but a LOW display with it in place of
  `StageType.addApex` (legality, the two faces, the LOW layer at `K` and the separator labels) is
  not constructed.

So the first missing construction is the strongly coded display, and with it strong coding of the
levels below it.  It is not built here.

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

**4. The modelhood audit of the context acquisition** used by the unrestricted route for (R2),
`Realization.exists_covers_isSourceGapContextAt` (through
`Realization.residualAcquisition_isSourceGapContextOff`).  Each entry: the model-level use; where;
its status in the class.

* `IsModel.exists_covers_zero` and `IsModel.isGloballyRigidCore_empty_iff`; the positivity
  `K > 0`; **replaced** by `Realization.IsStronglyCodedReceiving.ne_zero_of_residual` (through
  `Realization.exists_covers_zero_of_isCovering` and
  `Realization.isGloballyRigidCore_empty_iff_of_hasLegalTypes`, in
  `VaughtConjecture.MainTheorem.StronglyCodedTerminalProperty`).
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

Saturation, the bottom pattern, uniformity and dominance are not used by the acquisition.  Nothing
in the acquisition is missing; its form in the class is stated
(`Realization.StronglyCodedSourceGapAcquisitionTarget`), its proof being the existing one with these
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
`ProfileTower.exists_isLowLayer_pTower` of `StageType.hasLowLayersOn_lt`.  Not proved: the
display of the construction carries the apex of `StageType.addApex`. -/
def StronglyCodedPaddedLowLayersTarget : Prop :=
  HasStronglyCodedLowLayersOn.{u} fun _ K k _ _ _ _ _ ↦ K < k

/-- **Target: strong coding of the LOW layer with the faces `⊥` above `K`** (used at `K = k`), the
construction of `StageType.hasLowLayersOn_lowBotAll`.  Not proved: the display of the construction
carries the apex of `StageType.addApex`. -/
def StronglyCodedLowBotLowLayersTarget : Prop :=
  HasStronglyCodedLowLayersOn.{u} LowBotAllClass

/-- **Target: strong coding of the LOW layer at the full grade** (`K = k + 1`), the construction
of `StageType.hasLowLayersOn_fullGradeAll`.  Not proved: the display of the construction carries
the apex of `StageType.addApex`. -/
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
point last, the contexts of `Realization.BoundedCoatomCutoffDetermination.of_hasLowDisplays`.  Not
proved: it follows from strongly coded LOW displays
(`Realization.stronglyCodedLowDonorTarget_of_hasStronglyCodedLowDisplays`). -/
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
strongly coded forms.  Not proved here; the relabelled context and coface are strongly coded
(`StageType.isStronglyCoded_reindex`), and no new construction enters. -/
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
`Realization.residualAcquisition_isSourceGapContextOff` in the class.  Not proved here: the
existing proof uses modelhood only through exact consistency, covering, legal types and the
positivity of the residual grade, each replaced in the class (the table of the module
docstring). -/
def StronglyCodedSourceGapAcquisitionTarget : Prop :=
  StronglyCodedResidualAcquisition.{u, w} fun K t' h ↦ t'.IsSourceGapContextOff K h

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
