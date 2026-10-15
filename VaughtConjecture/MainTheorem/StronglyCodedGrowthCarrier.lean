/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.StronglyCodedBotKeeping
import VaughtConjecture.MainTheorem.CodedLadderStable
import VaughtConjecture.MainTheorem.GrowthAdmittedCarrier
import VaughtConjecture.MainTheorem.StronglyCodedTerminalProperty
import VaughtConjecture.Realization.CapToModel

/-!
# Restricted (R3) in the strongly coded receiving class through coded exact-growth carriers

Roadmap, Layer 3 ((R3), the growth carrier and its evaluation) and Layer 4 (the hollow
comparison), Correspondence, item 1 (the strongly coded legal stage types).

The restricted (R3) premise of the hollow comparison is `Realization.StronglyCodedHollowReceiving`
(`VaughtConjecture.MainTheorem.StronglyCodedTerminalProperty`): a realization in the strongly coded
receiving class (`Realization.IsStronglyCodedReceiving`) at `λ_ξ` with the restricted hollow
property receives every strongly coded one-point coface exactly.  For models, (R3) is
`Realization.hollowReceiving_levels`, through exact growth carriers, an acquisition of calibrated
contexts and padding (`Realization.hollowReceiving_of_hasExactGrowthCarriers_pos`,
`Realization.hollowGrowthAcquisition_reference'`, `Realization.HollowReceiving.of_pos`).

Status: restricted (R3) is **closed** for the native construction:
`Realization.stronglyCodedHollowReceiving : StronglyCodedHollowReceiving ξ M` for every `ξ` and `M`,
with no premise.  It composes the construction (strongly coded exact growth carriers), the
realization (the carrier received by strongly coded receiving), the acquisition of calibrated
contexts in the class, and padding of the empty cover.  No correspondence with [AFK26] is claimed.

## 1. Construction: strongly coded exact growth carriers

* `StageType.HasExactStronglyCodedGrowthCarriers C`: `StageType.HasExactGrowthCarriers C` with a
  strongly coded context and donor as inputs and a strongly coded carrier as output.
* `StageType.hasExactStronglyCodedGrowthCarriers_codedLadder` (proved): for the hollow reference
  calibration with a nonempty root, from the coded contract
  `StageType.hasCodedLadderGrowthCarriers_levels`, recognition
  `GrowthCarrier.recognizes_of_codedLadder`, recovery
  `StageType.GrowthRequests.recovers_eq_of_recognizes`, and the field
  `GrowthCarrier.CodedLadder.stronglyCoded`, which
  `StageType.HasCodedLadderGrowthCarriers.exists_recognizes` forgets.

The strong coding of the output is proved by the construction, not assumed from the inputs: each
step that creates rows has its own preservation lemma.  The second coatom type is the strongly coded
pinned extension (`StageType.exists_stronglyCoded_pinned_extension`, in
`StageType.exists_stronglyCodedGrowthSeed_of_isSuccLimit`); the amalgam
(`Seed.isStronglyCoded_amalgam`) and the attachment, a restriction of it
(`Seed.isStronglyCoded_attachment`); the coded levels, initial and next
(`Seed.codedLvLevel_codedGood`); their replicated copies (`Seed.ALvl.CodedGood.isStronglyCoded_rep`,
`Seed.codedLvRep_isStronglyCoded`); the strongly coded apex
(`StageType.isStronglyCoded_addStrongApex`, `Seed.isStronglyCoded_codedLvRepCompletion`), which
gives the field `GrowthCarrier.CodedLadder.stronglyCoded` in
`Seed.exists_codedLadder_codedLvRepCompletion`; and the relabelling to every context
(`Scheme.isStronglyCoded_comap`, in `StageType.CodedLadderCarrierBody.relabel`).

## 2. Realization: the saturation use and its replacement

`GrowthCarrier.exists_eval_eq_of_recovers_eq` takes `hR : R.IsModel` and uses two of its clauses,
both through `GrowthCarrier.exists_recovered`:

* `IsModel.saturation` (generalized saturation, [Kni26, Definition 3.2.1, clause 4(a)i]), applied
  as `hR.saturation x G.scheme hsat`: it realizes over the occurrence `x` a tuple `w` whose type
  `r` is **some** stage type on the carrier scheme `G.scheme`, with labels not prescribed;
* `IsModel.isConsistent`, in `GrowthCarrier.exists_recovered_of_eval`, which reads the type of
  the face of `w` along the donor face from `r`.

Exactness is not a property of the realization: it comes from the recovery
`G.Recovers x.type.label (· = D.label ·)`, a statement about every lawful section of the carrier
rows agreeing with the labels of `x` on the context face.  So the replacement needs only some
tuple over `x` with a type on the carrier scheme.  In the class this is the field
`Realization.IsStronglyCodedReceiving.receiving` (finite-cut receiving for the cofaces with
strongly coded rows) at a coface `d ∈ x.type.cofaces` on `G.scheme` and the cutoff `0` (permitted
at a positive stage).  The cutoff-stable recovery of the coded ladder
(`StageType.hasStronglyCodedCutoffStableRecovery`) is not used: it concerns the stable labels of
(R4), not the actual labels.

* `GrowthCarrier.exists_eval_eq_of_recovers_eq_of_mem_cofaces` (proved): the coface `d` given to
  receiving is explicit, with the premise `d.rows.IsStronglyCoded`; (a) the received type `r` is in
  the receiving family of `d` at `0`, a coface of the type of `x`, with strongly coded rows; (b)
  the face of the received tuple along the root followed by the new point has type `D` literally
  (`R.eval … = some D`), the formal top included.
* `GrowthCarrier.exists_eval_eq_of_recovers_eq_of_isStronglyCoded` (proved): the same from a
  strongly coded carrier and a nonempty saturation instance, the instance being given to receiving.
* `GrowthCarrier.exists_eval_eq_of_recovers_eq_of_hasFiniteCutReceivingIn` (proved): the conclusion
  of `GrowthCarrier.exists_eval_eq_of_recovers_eq` clause by clause (`Fin.castSuccEmb.trans u =
  e.trans x.tuple`, `u (Fin.last n) ∉ Set.range x.tuple`, `R.eval u = some D`), with `hR` replaced
  by exact consistency, the receiving field and a positive stage, the carrier strongly coded.
* `Realization.StronglyCodedCarrierEvaluationTarget`, proved
  (`Realization.stronglyCodedCarrierEvaluationTarget`): the evaluation for `R` in the class.
* `Realization.IsStronglyCodedReceiving.exists_covers_of_calibratedContext` (proved): exact
  receiving of a strongly coded coface `D` over `c' ∘ h`, at an explicit calibrated context: a
  cover `c'` of `t'` with `C t' h D` is a hypothesis, with strongly coded exact growth carriers for
  `C`.

## 3. Acquisition and the empty root

* `Realization.StronglyCodedHollowGrowthAcquisition ξ M C`: the acquisition of calibrated contexts
  in the class, an explicit premise: over every cover of **positive** arity, for every strongly
  coded one-point coface, a cover of a context calibrated by `C`.  The acquisition of
  `VaughtConjecture.MainTheorem.StronglyCodedCalibratedContexts`
  (`Realization.CalibratedContextAcquisitionTarget`) is for the non-hollow case and the margin
  calibration of (R4); it does not apply here.  Only its reference-cell step carries over
  (`Realization.stronglyCodedReferenceCellsTarget`, the premise `huni` of
  `Realization.acquiresCalibratedContexts_gradedCapMargin_of_exists_extend_uniformity`).
* `Realization.StronglyCodedHollowAcquisitionTarget ξ M`, proved
  (`Realization.stronglyCodedHollowAcquisitionTarget`): the acquisition for
  `StageType.HollowReferenceCalibration'`, from
  - synchronization with forcing from consistency and covering
    (`Realization.exists_forcing_floor_of_isCovering`; cover-hollowness and unbounded growth are
    hypotheses);
  - occurrences of every size from unbounded growth
    (`Realization.exists_le_arity_of_topGradeSup_eq_top`: for every `N`, an occurrence with at
    least `N` points; the acquisition takes `N` the largest donor offset bound);
  - the acquisition of marked-cap contexts in the class
    (`Realization.IsStronglyCodedReceiving.exists_markedCapContextBelow'`, the class form of
    `Realization.rootBottomAcquisition_of_botKeeping`, over every cover, the empty one included);
  - reference cells (`Realization.stronglyCodedReferenceCellsTarget`) and covering.
* **The empty root.**  The calibration of the coded carriers has a nonempty root
  (`StageType.HollowReferenceCalibrationPos`: the relative lift reads the donor through its root
  face), so covers of arity zero are not acquired: they are padded.
  `Realization.StronglyCodedHollowPadding ξ M`, proved (`Realization.stronglyCodedHollowPadding`),
  from an occurrence of positive arity (`Realization.positiveOccurrenceStep`, from unbounded
  growth) and the strongly coded pinned extension over the empty face
  (`Realization.stronglyCodedPaddingExtensionStep`).
* `Realization.stronglyCodedHollowReceivingPos_of_hasExactStronglyCodedGrowthCarriers` (proved):
  restricted (R3) over positive covers from acquisition and strongly coded exact growth carriers.
* `Realization.StronglyCodedHollowDerivationTarget`, proved, and
  `Realization.stronglyCodedHollowReceiving_of_acquisition` (proved): restricted (R3)
  (`Realization.StronglyCodedHollowReceiving ξ M`) from the acquisition alone; with the acquisition,
  `Realization.stronglyCodedHollowReceiving` (proved).

## Modelhood audit of the unrestricted (R3) route

The route of `Realization.hollowReceiving_levels`, step by step.  Each entry: step; the clause of a
model it uses; status in the strongly coded receiving class.

* Padding, an occurrence of positive arity; `IsModel.exists_le_arity`; proved from unbounded growth
  (`Realization.positiveOccurrenceStep`).
* Padding, the pinned extension; none (`StageType.exists_pinned_extension_of_isSuccPrelimit`);
  proved strongly coded (`Realization.stronglyCodedPaddingExtensionStep`).
* Acquisition, reference cells; `IsModel.exists_extend_uniformity`; proved:
  `Realization.stronglyCodedReferenceCellsTarget`.
* Acquisition, an occurrence with more points than the donor offsets; `IsModel.exists_le_arity`;
  proved from unbounded growth: `Realization.exists_le_arity_of_topGradeSup_eq_top`.
* Acquisition, one occurrence containing both; `IsModel.isCovering`; class field.
* Synchronization with forcing (`Realization.IsModel.exists_forcing_floor`); covering and
  consistency only; proved: `Realization.exists_forcing_floor_of_isCovering`.
* A top cap of the floor; `IsModel.isLegal`; class field.
* One point more; `IsModel.dominance` at `0`; proved:
  `Realization.IsStronglyCodedReceiving.realizesOver_dominanceFamily`.
* The bot-keeping completion of the seed; none (`Seed.exists_botKeeping`); proved strongly coded:
  `StageType.stronglyCodedBotKeepingCofaceTarget`
  (`VaughtConjecture.Extension.StronglyCodedBotKeeping`).
* The bottom-pattern realization; `IsModel.bottomPattern`; proved for strongly coded cofaces:
  `Realization.IsStronglyCodedReceiving.realizesOver_bottomPatternFamily`.  Receiving at a cutoff
  other than `⊥` keeps exactly the information the clause asks for (which cells are `⊥`).
* The marked-cap context; none (`StageType.markedCapContextBelow'_of_botKeeping`); unchanged, and
  composed in `Realization.IsStronglyCodedReceiving.exists_markedCapContextBelow'`.
* Exact growth carriers; none; proved: `StageType.hasExactStronglyCodedGrowthCarriers_codedLadder`.
* Legality and strong coding of the acquired context; `IsModel.isLegal`; class fields.
* Realization of the carrier; `IsModel.saturation`; proved:
  `GrowthCarrier.exists_eval_eq_of_recovers_eq_of_mem_cofaces`.
* The evaluation; `IsModel.isConsistent`; class field.

Every step above is compiled, and the composition is compiled:
`Realization.stronglyCodedHollowAcquisitionTarget` composes the class forms of
`Realization.IsModel.exists_forcing_floor`, `Realization.rootBottomAcquisition_of_botKeeping` and
`Realization.hollowGrowthAcquisition_reference'`, and `Realization.stronglyCodedHollowReceiving`
composes it with padding, the coded carriers and their realization.  No premise beyond the class
and the restricted hollow property is used: no countability, nonemptiness, bound on `ξ`,
unrestricted receiving, saturation or modelhood.

All results here are native constructions of this repository; no correspondence with [AFK26] is
claimed.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Finset Label StageType
open scoped Ordinal

/-! ### The realization of a strongly coded carrier by restricted receiving -/

namespace GrowthCarrier

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M} {n : ℕ}

/-- **The realization of a carrier through a given strongly coded coface** (native
construction): the coface `d` of the type of `x` on the carrier scheme, with strongly coded rows,
is given to finite-cut receiving for the cofaces with strongly coded rows at the cutoff `0`
(permitted at a positive stage).  The received tuple `w` has a type `r` in the receiving family of
`d` at `0`, hence on the carrier scheme; `r` is a coface of the type of `x` with strongly coded
rows.  The face of `w` along the root `e` followed by the new point has type `D` literally, by the
recovery of the labels of `D` from the actual labels of `x`
(`GrowthCarrier.exists_recovered_of_eval`, which uses exact consistency only). -/
theorem exists_eval_eq_of_recovers_eq_of_mem_cofaces (hR : R.IsConsistent)
    (hrec : R.HasFiniteCutReceivingIn fun t ↦ t.rows.IsStronglyCoded) (hα : 0 < α)
    (x : R.Occurrence) {e : Fin n ↪ Fin x.arity} {D : StageType.{u} α (n + 1)}
    (G : GrowthCarrier x.type.toScheme D.toScheme e) {d : StageType.{u} α (x.arity + 1)}
    (hd : d ∈ x.type.cofaces) (hdE : d.toScheme = G.scheme) (hds : d.rows.IsStronglyCoded)
    (hrecov : G.Recovers x.type.label fun j ℓ ↦ ℓ = D.label j) :
    ∃ (w : Fin (x.arity + 1) ↪ M) (r : StageType.{u} α (x.arity + 1)),
      Fin.castSuccEmb.trans w = x.tuple ∧ R.eval w = some r ∧ r ∈ receivingFamily d 0 ∧
        r ∈ x.type.cofaces ∧ r.rows.IsStronglyCoded ∧
        Fin.castSuccEmb.trans ((extendByLast e).trans w) = e.trans x.tuple ∧
        ((extendByLast e).trans w) (Fin.last n) ∉ Set.range x.tuple ∧
        R.eval ((extendByLast e).trans w) = some D := by
  obtain ⟨w, hw, r, hr, hev⟩ := hrec x d hd hds 0 (isPermittedCutoff_zero.mpr hα)
  have hrE : r.toScheme = G.scheme := hr.1.trans hdE
  obtain ⟨s, hs, hsD, hl⟩ :=
    G.exists_recovered_of_eval hR (Realization.typeLabelling R) hrecov hw hev hrE
  have hrl : r.IsLegal := by
    change Scheme.IsLegal r.toScheme
    rw [hrE]
    exact G.isLegal
  have hrf : restrictFace Fin.castSuccEmb r = some x.type := by
    rw [← hR w r _ hev, hw]
    exact x.eval_tuple
  exact ⟨w, r, hw, hev, hr, ⟨hrl, hrf⟩, StageType.schemeInvariant_isStronglyCoded hr.1 hds,
    castSuccEmb_trans_extendByLast_trans hw, last_notMem_range hw,
    hs.trans (congrArg some (StageType.ext hsD hl))⟩

/-- **Exact receiving from exact recovery, by strongly coded receiving** (native construction):
`GrowthCarrier.exists_eval_eq_of_recovers_eq` with generalized saturation replaced by finite-cut
receiving for the cofaces with strongly coded rows, for a carrier with strongly coded rows, at a
positive stage.  The saturation instance `d` on the carrier scheme is strongly coded (its rows are
those of the carrier) and is given to receiving
(`GrowthCarrier.exists_eval_eq_of_recovers_eq_of_mem_cofaces`); the received tuple `w` has a type
`r` on the carrier scheme, a coface of the type of `x` with strongly coded rows, and its face along
the root `e` followed by the new point has type `D`. -/
theorem exists_eval_eq_of_recovers_eq_of_isStronglyCoded (hR : R.IsConsistent)
    (hrec : R.HasFiniteCutReceivingIn fun t ↦ t.rows.IsStronglyCoded) (hα : 0 < α)
    (x : R.Occurrence) {e : Fin n ↪ Fin x.arity} {D : StageType.{u} α (n + 1)}
    (G : GrowthCarrier x.type.toScheme D.toScheme e) (hG : G.scheme.rows.IsStronglyCoded)
    (hsat : (x.type.cofaces ∩ saturationFamily G.scheme).Nonempty)
    (hrecov : G.Recovers x.type.label fun j ℓ ↦ ℓ = D.label j) :
    ∃ (w : Fin (x.arity + 1) ↪ M) (r : StageType.{u} α (x.arity + 1)),
      Fin.castSuccEmb.trans w = x.tuple ∧ R.eval w = some r ∧ r ∈ x.type.cofaces ∧
        r.toScheme = G.scheme ∧ r.rows.IsStronglyCoded ∧
        Fin.castSuccEmb.trans ((extendByLast e).trans w) = e.trans x.tuple ∧
        ((extendByLast e).trans w) (Fin.last n) ∉ Set.range x.tuple ∧
        R.eval ((extendByLast e).trans w) = some D := by
  obtain ⟨d, hd, hdE⟩ := hsat
  have hdE' : d.toScheme = G.scheme := hdE
  have hds : d.rows.IsStronglyCoded := by
    rw [hdE']
    exact hG
  obtain ⟨w, r, hw, hev, hr, hcof, hrs, h₁, h₂, h₃⟩ :=
    G.exists_eval_eq_of_recovers_eq_of_mem_cofaces hR hrec hα x hd hdE' hds hrecov
  exact ⟨w, r, hw, hev, hcof, hr.1.trans hdE', hrs, h₁, h₂, h₃⟩

/-- **Exact receiving from exact recovery, in the form of the original** (native construction):
the conclusion of `GrowthCarrier.exists_eval_eq_of_recovers_eq` clause by clause (a tuple `u`
extending the root `e` of `x`, its new point fresh over `x`, and `R.eval u = some D`), with
`hR : R.IsModel` replaced by exact consistency, finite-cut receiving for the cofaces with strongly
coded rows and a positive stage, and the carrier strongly coded. -/
theorem exists_eval_eq_of_recovers_eq_of_hasFiniteCutReceivingIn (hR : R.IsConsistent)
    (hrec : R.HasFiniteCutReceivingIn fun t ↦ t.rows.IsStronglyCoded) (hα : 0 < α)
    (x : R.Occurrence) {e : Fin n ↪ Fin x.arity} {D : StageType.{u} α (n + 1)}
    (G : GrowthCarrier x.type.toScheme D.toScheme e) (hG : G.scheme.rows.IsStronglyCoded)
    (hsat : (x.type.cofaces ∩ saturationFamily G.scheme).Nonempty)
    (hrecov : G.Recovers x.type.label fun j ℓ ↦ ℓ = D.label j) :
    ∃ u : Fin (n + 1) ↪ M, Fin.castSuccEmb.trans u = e.trans x.tuple ∧
      u (Fin.last n) ∉ Set.range x.tuple ∧ R.eval u = some D := by
  obtain ⟨w, r, -, -, -, -, -, h₁, h₂, h₃⟩ :=
    G.exists_eval_eq_of_recovers_eq_of_isStronglyCoded hR hrec hα x hG hsat hrecov
  exact ⟨_, h₁, h₂, h₃⟩

end GrowthCarrier

namespace Realization

section Evaluation

variable (α : Ordinal.{u}) (M : Type v)

/-- **Target: the evaluation of a strongly coded carrier in the strongly coded receiving class**.
At a positive stage, for `R` in the class, an occurrence `x`, and a growth carrier `G` over `x`
with root `e` and donor `D`, with strongly coded rows, a nonempty saturation instance over `x`,
and recovering the labels of `D` exactly from the actual labels of `x`: some tuple `w` over `x`
has as type a coface `r` of the type of `x` on the carrier scheme, with strongly coded rows (the
coface actually received), and the face of `w` along `e` followed by the new point is fresh over
`x`, extends the root, and has type `D`, the formal top included. -/
def StronglyCodedCarrierEvaluationTarget : Prop :=
  0 < α → ∀ R : Realization.{u, v} α M, R.IsStronglyCodedReceiving →
    ∀ (x : R.Occurrence) ⦃n : ℕ⦄ (e : Fin n ↪ Fin x.arity) (D : StageType.{u} α (n + 1))
      (G : GrowthCarrier x.type.toScheme D.toScheme e), G.scheme.rows.IsStronglyCoded →
      (x.type.cofaces ∩ saturationFamily G.scheme).Nonempty →
      G.Recovers x.type.label (fun j ℓ ↦ ℓ = D.label j) →
      ∃ (w : Fin (x.arity + 1) ↪ M) (r : StageType.{u} α (x.arity + 1)),
        Fin.castSuccEmb.trans w = x.tuple ∧ R.eval w = some r ∧ r ∈ x.type.cofaces ∧
          r.toScheme = G.scheme ∧ r.rows.IsStronglyCoded ∧
          Fin.castSuccEmb.trans ((extendByLast e).trans w) = e.trans x.tuple ∧
          ((extendByLast e).trans w) (Fin.last n) ∉ Set.range x.tuple ∧
          R.eval ((extendByLast e).trans w) = some D

/-- **The evaluation of a strongly coded carrier in the class** (native construction):
`GrowthCarrier.exists_eval_eq_of_recovers_eq_of_isStronglyCoded` with the fields
`Realization.IsStronglyCodedReceiving.isConsistent` and
`Realization.IsStronglyCodedReceiving.receiving`; no other field is used. -/
theorem stronglyCodedCarrierEvaluationTarget : StronglyCodedCarrierEvaluationTarget α M :=
  fun hα _ hR x _ _ _ G hG hsat hrecov ↦
    G.exists_eval_eq_of_recovers_eq_of_isStronglyCoded hR.isConsistent hR.receiving hα x hG hsat
      hrecov

end Evaluation

end Realization

/-! ### Strongly coded exact growth carriers -/

namespace StageType

/-- **Strongly coded exact growth carriers** for a calibration `C`: as
`StageType.HasExactGrowthCarriers C`, over a legal context `t'` with strongly coded rows and for
a one-point coface `d` with strongly coded rows, some growth carrier with strongly coded rows
recovers the labels of `d` exactly, the formal top included, from the labels of `t'`. -/
def HasExactStronglyCodedGrowthCarriers
    (C : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
    Order.IsSuccLimit α → t'.IsLegal → t'.rows.IsStronglyCoded →
    ∀ t : StageType.{u} α n, restrictFace h t' = some t →
      ∀ d ∈ t.cofaces, d.rows.IsStronglyCoded → C t' h d →
        ∃ G : GrowthCarrier t'.toScheme d.toScheme h, G.scheme.rows.IsStronglyCoded ∧
          G.Recovers t'.label fun j ℓ ↦ ℓ = d.label j

/-- **Target: strongly coded exact growth carriers from the coded ladder**, for the hollow
reference calibration with a nonempty root. -/
def StronglyCodedExactGrowthCarriersTarget : Prop :=
  HasExactStronglyCodedGrowthCarriers.{u} HollowReferenceCalibrationPos

/-- **Strongly coded exact growth carriers from the coded ladder** (native construction): the
requests of `StageType.HollowReferenceCalibration'.exists_relativeLift`, with the relative lift on
the exact class (`StageType.GrowthRequests.hasRelativeLiftOnClass_of_hasRelativeLift`), have a coded
ladder carrier (`StageType.hasCodedLadderGrowthCarriers_levels`, at the strongly coded context and
donor); it recognizes admitted states (`GrowthCarrier.recognizes_of_codedLadder`), hence recovers
the donor exactly (`StageType.GrowthRequests.recovers_eq_of_recognizes`), and its rows are
strongly coded (`GrowthCarrier.CodedLadder.stronglyCoded`). -/
theorem hasExactStronglyCodedGrowthCarriers_codedLadder :
    StronglyCodedExactGrowthCarriersTarget.{u} := by
  intro α n k t' e hα ht' hsc p hte d hd hdsc hC
  obtain ⟨hC, hn⟩ := hC
  obtain ⟨Q, hex, hQ, hrel⟩ := hC.exists_relativeLift ht' hte hd.2 hd.1 hn
  obtain ⟨G, Mb, H, r, hL⟩ := hasCodedLadderGrowthCarriers_levels t' e hα ht' hsc p hte d hd hdsc
    hn Q hex hQ (GrowthRequests.hasRelativeLiftOnClass_of_hasRelativeLift hte hd.2 hex hQ hd.1 hn
      hrel)
  refine ⟨G, hL.stronglyCoded, GrowthRequests.recovers_eq_of_recognizes hex hQ G ?_⟩
  refine G.recognizes_of_codedLadder Q (by have := hQ.arity; omega) (fun j ↦ ?_) hL
  rw [GrowthCarrier.donorCell, Scheme.grade_faceCell]
  exact (d.grade_le j).trans hQ.arity

end StageType

/-! ### The realization step at an explicit calibrated context, and the acquisition steps -/

namespace Realization

section Steps

/-- **Exact receiving at an explicit calibrated context** (native construction): for `R` in the
strongly coded receiving class at `λ_ξ`, a cover `c'` of a context `t'` calibrated by `C` along
`h` for a strongly coded one-point coface `D` of the face `t` of `t'` along `h` (the calibration
`hC` is a hypothesis), and strongly coded exact growth carriers for `C`: the cover `c' ∘ h` of `t`
extends by one point to a cover of `D`.  The context is an actual type, so legal and strongly coded
by the class fields; the carrier is strongly coded; it is realized over the context by strongly
coded receiving (`GrowthCarrier.exists_eval_eq_of_recovers_eq_of_hasFiniteCutReceivingIn`). -/
theorem IsStronglyCodedReceiving.exists_covers_of_calibratedContext {M : Type v} {ξ : Ordinal.{u}}
    {R : Realization.{u, v} (blockStage ξ) M} (hR : R.IsStronglyCodedReceiving)
    {C : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop}
    (hcar : StageType.HasExactStronglyCodedGrowthCarriers.{u} C) {k n : ℕ}
    {t' : StageType.{u} (blockStage ξ) k} {c' : Fin k → M} (hc' : R.Covers t' c')
    {h : Fin n ↪ Fin k} {t : StageType.{u} (blockStage ξ) n} (ht : restrictFace h t' = some t)
    {D : StageType.{u} (blockStage ξ) (n + 1)} (hD : D ∈ t.cofaces)
    (hDs : D.rows.IsStronglyCoded) (hC : C t' h D) :
    ∃ y : M, R.Covers D (Fin.snoc (c' ∘ h) y) := by
  let x : R.Occurrence := ⟨k, ⟨c', hc'.injective⟩, t', hc'.eval_eq⟩
  obtain ⟨G, hGs, hrec⟩ := hcar t' h (isSuccLimit_blockStage ξ)
    (hR.hasLegalTypes _ _ hc'.eval_eq) (hR.isStronglyCoded _ _ hc'.eval_eq) t ht D hD hDs hC
  have hpos : (0 : Ordinal.{u}) < blockStage ξ :=
    Ordinal.omega0_pos.trans_le (omega0_le_blockStage ξ)
  obtain ⟨u, hu, -, hev⟩ :=
    GrowthCarrier.exists_eval_eq_of_recovers_eq_of_hasFiniteCutReceivingIn hR.isConsistent
      hR.receiving hpos x G hGs
      (G.nonempty_cofaces_inter_saturationFamily_of_isSuccPrelimit
        (isSuccPrelimit_blockStage ξ) rfl) hrec
  refine ⟨u (Fin.last n), ?_⟩
  have hfun : Fin.snoc (c' ∘ h) (u (Fin.last n)) = ⇑u := by
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i =>
      rw [Fin.snoc_castSucc]
      exact (DFunLike.congr_fun hu i).symm
  rw [hfun]
  exact covers_of_eval u hev

/-- **The bottom-pattern step in the class** (native construction): the clause
`IsModel.bottomPattern` used by `Realization.rootBottomAcquisition_of_botKeeping`, for a coface
with strongly coded rows, from the receiving field of the class at the cutoff `0`: the receiving
family of a stage type at a cutoff other than `⊥` lies in its bottom-pattern family
(`StageType.receivingFamily_subset_bottomPatternFamily`).  The coface used there is given
strongly coded by `StageType.stronglyCodedBotKeepingCofaceTarget`. -/
theorem IsStronglyCodedReceiving.realizesOver_bottomPatternFamily {M : Type v} {α : Ordinal.{u}}
    {R : Realization.{u, v} α M} (hR : R.IsStronglyCodedReceiving) (hα : 0 < α)
    (x : R.Occurrence) {qs : StageType.{u} α (x.arity + 1)} (hqs : qs ∈ x.type.cofaces)
    (hsc : qs.rows.IsStronglyCoded) :
    R.RealizesOver x.tuple (bottomPatternFamily qs.toScheme qs.label) :=
  (hR.receiving x qs hqs hsc 0 (isPermittedCutoff_zero.mpr hα)).mono
    (receivingFamily_subset_bottomPatternFamily
      ⟨rfl, fun i j hij _ ↦ by obtain rfl : i = j := Fin.ext hij; rfl⟩ (by simp))

/-- **The step of one point more in the class** (native construction): the clause
`IsModel.dominance` used by `Realization.rootBottomAcquisition_of_botKeeping`, from the receiving
field of the class and the strongly coded coface instances
(`Realization.HasFiniteCutReceivingIn.dominance_of_hasStronglyCodedCofaceInstances`). -/
theorem IsStronglyCodedReceiving.realizesOver_dominanceFamily {M : Type v} {α : Ordinal.{u}}
    {R : Realization.{u, v} α M} (hR : R.IsStronglyCodedReceiving) (hα : Order.IsSuccPrelimit α)
    (x : R.Occurrence) {γ : Ordinal.{u}} (hγα : γ < α) :
    R.RealizesOver x.tuple (dominanceFamily γ) :=
  hR.receiving.dominance_of_hasStronglyCodedCofaceInstances
    (StageType.HasStronglyCodedCofaceInstances.of_isSuccPrelimit hα) hα
    (fun _ t p h ↦ ⟨hR.hasLegalTypes t p h, hR.isStronglyCoded t p h⟩) x hγα

/-- **Occurrences of every top grade from unbounded growth** (native construction): if the
top-grade supremum is `⊤`, then for every `N` some occurrence has top grade above `N`. -/
theorem exists_lt_topGrade_of_topGradeSup_eq_top {M : Type v} {α : Ordinal.{u}}
    {R : Realization.{u, v} α M}
    (htop : R.topGradeSup = ⊤) (N : ℕ) : ∃ w : R.Occurrence, N < w.type.topGrade := by
  have hlt : ((N : ℕ) : ℕ∞) < R.topGradeSup := htop ▸ ENat.natCast_lt_top _
  obtain ⟨w, hw⟩ := lt_iSup_iff.mp hlt
  exact ⟨w, by exact_mod_cast hw⟩

/-- **Occurrences of every size from unbounded growth** (native construction): if the top-grade
supremum is `⊤`, then for every `N` some occurrence has at least `N` points; the top grade is the
grade of a cell, at most the arity.  This is the form consumed by the acquisition, where `N` bounds
every donor offset (`IsModel.exists_le_arity` in `Realization.hollowGrowthAcquisition_reference'`).
-/
theorem exists_le_arity_of_topGradeSup_eq_top {M : Type v} {α : Ordinal.{u}}
    {R : Realization.{u, v} α M}
    (htop : R.topGradeSup = ⊤) (N : ℕ) : ∃ x : R.Occurrence, N ≤ x.arity := by
  obtain ⟨x, hx⟩ := exists_lt_topGrade_of_topGradeSup_eq_top htop N
  exact ⟨x, (hx.trans_le (topGrade_le_iff.mpr fun d _ ↦ x.type.grade_le d)).le⟩

/-- **Synchronization with forcing from consistency and covering** (native construction):
`Realization.IsModel.exists_forcing_floor` with modelhood replaced by its two uses, exact
consistency (`hR`) and covering (`hc`); cover-hollowness and unbounded growth are hypotheses, as
there.  Every occurrence `x` is a literal face, along some `g`, of an occurrence `Z` of top grade
above `x.arity + 1` and above `K`, at which `x.arity + 1` is forced at every cell of `x` labelled
`⊤`. -/
theorem exists_forcing_floor_of_isCovering {M : Type v} {ξ : Ordinal.{u}}
    {R : Realization.{u, v} (blockStage ξ) M} (hR : R.IsConsistent) (hc : R.IsCovering)
    (hhol : R.IsCoverHollow) (htop : R.topGradeSup = ⊤) (K : ℕ) (x : R.Occurrence) :
    ∃ (Z : R.Occurrence) (g : Fin x.arity ↪ Fin Z.arity), g.trans Z.tuple = x.tuple ∧
      x.arity + 1 < Z.type.topGrade ∧ K < Z.type.topGrade ∧ ∀ a, x.type.label a = ⊤ →
        StageType.ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) Z.type g
          x.type a (x.arity + 1) := by
  classical
  have hO (a : Fin x.type.card) : ∃ O : R.Occurrence, x.type.label a = ⊤ →
      ∃ g : Fin x.arity ↪ Fin O.arity, g.trans O.tuple = x.tuple ∧
        StageType.ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) O.type g
          x.type a (x.arity + 1) := by
    by_cases ha : x.type.label a = ⊤
    · have hno : ¬ R.IsTopAnchor x a (x.arity + 1) := fun hA ↦ hhol ⟨x, a, x.arity + 1, hA⟩
      simp only [IsTopAnchor, not_and, not_forall, not_not] at hno
      obtain ⟨⟨m, q, g⟩, ⟨s, hs, hsq⟩, hforce⟩ := hno ha
      refine ⟨⟨m, ⟨s, hsq.injective⟩, q, hsq.eval_eq⟩, fun _ ↦ ⟨g, ?_, hforce⟩⟩
      exact Function.Embedding.ext fun i ↦ congrFun hs i
    · exact ⟨x, fun h ↦ absurd h ha⟩
  choose O hO using hO
  obtain ⟨w₁, hw₁⟩ := exists_lt_topGrade_of_topGradeSup_eq_top htop (x.arity + 1)
  obtain ⟨w₂, hw₂⟩ := exists_lt_topGrade_of_topGradeSup_eq_top htop K
  obtain ⟨Z, hZ⟩ := hc.exists_subset_support
    (x.support ∪ w₁.support ∪ w₂.support ∪ univ.biUnion fun a ↦ (O a).support)
  have hxZ : x ≤ Z := subset_union_left.trans (subset_union_left.trans
    (subset_union_left.trans hZ))
  have hw₁Z : w₁ ≤ Z := subset_union_right.trans (subset_union_left.trans
    (subset_union_left.trans hZ))
  have hw₂Z : w₂ ≤ Z := subset_union_right.trans (subset_union_left.trans hZ)
  have hOZ (a : Fin x.type.card) : O a ≤ Z :=
    (subset_biUnion_of_mem (fun a ↦ (O a).support) (mem_univ a)).trans
      (subset_union_right.trans hZ)
  obtain ⟨g, hg, -⟩ := (Occurrence.le_iff_exists_restrictFace hR).mp hxZ
  refine ⟨Z, g, hg, hw₁.trans_le (Occurrence.topGrade_mono hR hw₁Z),
    hw₂.trans_le (Occurrence.topGrade_mono hR hw₂Z), fun a ha ↦ ?_⟩
  obtain ⟨g', hg', hfa⟩ := hO a ha
  obtain ⟨ga, hga, hgar⟩ := (Occurrence.le_iff_exists_restrictFace hR).mp (hOZ a)
  have heq : g'.trans ga = g := by
    refine Function.Embedding.ext fun i ↦ Z.tuple.injective ?_
    have h₁ := DFunLike.congr_fun (congrArg (fun e ↦ g'.trans e) hga) i
    have h₂ := DFunLike.congr_fun hg' i
    have h₃ := DFunLike.congr_fun hg i
    simp only [Function.Embedding.trans_apply] at h₁ h₂ h₃ ⊢
    rw [h₁, h₂, h₃]
  exact heq ▸ hfa.trans_face hgar

/-- **Acquisition of marked-cap contexts respecting the root bottoms in the class** (native
construction): the argument of `Realization.rootBottomAcquisition_of_botKeeping` for `R` in the
strongly coded receiving class at `λ_ξ`, cover-hollow with unbounded growth, every model clause
replaced: synchronization with forcing by `Realization.exists_forcing_floor_of_isCovering`, the top
cap by legal types, one point more by
`Realization.IsStronglyCodedReceiving.realizesOver_dominanceFamily`, the bot-keeping coface by the
strongly coded one (`StageType.stronglyCodedBotKeepingCofaceTarget`, at the type of an occurrence,
strongly coded by the class field), and its bottom pattern by
`Realization.IsStronglyCodedReceiving.realizesOver_bottomPatternFamily`.  Every cover `c` of `t`,
the empty cover included, extends to a cover of a marked-cap context with root offsets below the cap
that respects the root bottoms (`TiedRootCapRelabel.MarkedCapContextBelow'`). -/
theorem IsStronglyCodedReceiving.exists_markedCapContextBelow' {M : Type v} {ξ : Ordinal.{u}}
    {R : Realization.{u, v} (blockStage ξ) M} (hR : R.IsStronglyCodedReceiving)
    (hhol : R.IsCoverHollow) (htop : R.topGradeSup = ⊤) {n : ℕ}
    (t : StageType.{u} (blockStage ξ) n) (c : Fin n → M) (hc : R.Covers t c) :
    ∃ (k : ℕ) (t' : StageType.{u} (blockStage ξ) k) (c' : Fin k → M) (h : Fin n ↪ Fin k),
      R.Covers t' c' ∧ c' ∘ h = c ∧ TiedRootCapRelabel.MarkedCapContextBelow' t' h := by
  have hβ := isSuccLimit_blockStage ξ
  have hα' : blockStage ξ + ω ≤ blockStage (ξ + 1) := (blockStage_add_one ξ).ge
  set x : R.Occurrence := ⟨n, ⟨c, hc.injective⟩, t, hc.eval_eq⟩
  obtain ⟨K, hK⟩ := StageType.exists_offset_bound t
  obtain ⟨Z, g, hg, hNZ, hKZ, hforce⟩ :=
    exists_forcing_floor_of_isCovering hR.isConsistent hR.isCovering hhol htop K x
  have htZ : StageType.restrictFace g Z.type = some t :=
    Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent hg
  -- a top cap of the type of `Z`
  have hnt : ¬ Z.type.IsTopFree := fun htf ↦ by
    rw [← StageType.topGrade_eq_zero_iff] at htf
    omega
  obtain ⟨cc, hcc⟩ := StageType.exists_isTopCap (hR.hasLegalTypes _ _ Z.eval_tuple) hnt
  -- one point more, by strongly coded receiving of a dominance instance at `0`
  obtain ⟨u, hu, q₀, ⟨⟨hq₀l, hq₀f⟩, -⟩, he₀⟩ :=
    (hR.realizesOver_dominanceFamily hβ.isSuccPrelimit Z (γ := 0) hβ.bot_lt).inter_cofaces
      hR.isConsistent hR.hasLegalTypes
  set Z₁ : R.Occurrence := ⟨Z.arity + 1, u, q₀, he₀⟩
  -- the strongly coded bot-keeping coface of `q₀`, and its bottom pattern over `Z₁`
  obtain ⟨qs, hqs, hqsc, hclean⟩ := StageType.stronglyCodedBotKeepingCofaceTarget q₀ Z.type
    hβ.isSuccPrelimit hq₀l (hR.isStronglyCoded _ _ he₀) hq₀f
  obtain ⟨v, hv, q, hq, hev⟩ :=
    (hR.realizesOver_bottomPatternFamily hβ.bot_lt Z₁ hqs hqsc).inter_cofaces hR.isConsistent
      hR.hasLegalTypes
  -- the root along `g` followed by the first points
  have hp : StageType.restrictFace (g.trans Fin.castSuccEmb) q₀ = some t := by
    rw [← StageType.restrictFace_trans _ _ _ hq₀f]
    exact htZ
  refine ⟨Z.arity + 2, q, v, (g.trans Fin.castSuccEmb).trans Fin.castSuccEmb,
    covers_of_eval _ hev, ?_, ?_⟩
  · funext i
    have h₁ := DFunLike.congr_fun hv (Fin.castSucc (g i))
    have h₂ := DFunLike.congr_fun hu (g i)
    have h₃ := DFunLike.congr_fun hg i
    simp only [Function.Embedding.trans_apply, Fin.coe_castSuccEmb] at h₁ h₂ h₃ ⊢
    change v (Fin.castSucc (Fin.castSucc (g i))) = c i
    rw [h₁, h₂, h₃]
    rfl
  · exact StageType.markedCapContextBelow'_of_botKeeping hβ hα' hqs hclean hq hp hK
      (fun d hd ↦ (hforce d hd).trans_face hq₀f) (e := StageType.faceCell hq₀f cc)
      ((StageType.label_faceCell hq₀f cc).trans hcc.2.1)
      (by rw [StageType.grade_faceCell, hcc.grade_eq_topGrade]; exact hNZ)
      (by rw [StageType.grade_faceCell, hcc.grade_eq_topGrade]; exact hKZ)

variable (α : Ordinal.{u}) (M : Type v)

/-- **Target: an occurrence of positive arity from unbounded growth**, the replacement of
`IsModel.exists_le_arity` at `1` in `Realization.HollowReceiving.of_pos`. -/
def PositiveOccurrenceStep : Prop :=
  ∀ R : Realization.{u, v} α M, R.topGradeSup = ⊤ → ∃ x : R.Occurrence, 0 < x.arity

/-- **An occurrence of positive arity from unbounded growth** (native construction): some
occurrence has a cell labelled `⊤` of positive grade, and grades are at most the arity. -/
theorem positiveOccurrenceStep : PositiveOccurrenceStep α M := by
  intro R h
  obtain ⟨x, hx⟩ : ∃ x : R.Occurrence, 0 < x.type.topGrade := by
    by_contra! h'
    have hle : R.topGradeSup ≤ 0 := iSup_le fun x ↦ by exact_mod_cast h' x
    simp [h] at hle
  obtain ⟨d, -, hd⟩ : ∃ d, x.type.label d = ⊤ ∧ 0 < x.type.toCellScheme.grade d := by
    by_contra! h'
    exact hx.not_ge (topGrade_le_iff.mpr h')
  exact ⟨x, hd.trans_le (x.type.grade_le d)⟩

/-- **Target: the strongly coded pinned extension over the empty face**, the replacement of
`StageType.exists_pinned_extension_of_isSuccPrelimit` in `Realization.HollowReceiving.of_pos`: at a
stage that is zero or a limit, a legal, strongly coded `P` on `k` points with empty face `p₀` and a
strongly coded one-point coface `D` of `p₀` are the faces, along the first points and along the new
point, of a legal, strongly coded `Q`. -/
def StronglyCodedPaddingExtensionStep : Prop :=
  Order.IsSuccPrelimit α → ∀ ⦃k : ℕ⦄ (P : StageType.{u} α k) (p₀ : StageType.{u} α 0)
    (D : StageType.{u} α 1), P.IsLegal → P.rows.IsStronglyCoded →
    restrictFace (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin k) P = some p₀ → D ∈ p₀.cofaces →
    D.rows.IsStronglyCoded →
    ∃ Q : StageType.{u} α (k + 1), Q.IsStronglyCodedLegal ∧
      restrictFace Fin.castSuccEmb Q = some P ∧
      restrictFace (extendByLast (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin k)) Q = some D

/-- **The strongly coded pinned extension over the empty face** (native construction):
`StageType.exists_stronglyCoded_pinned_extension` with
`StageType.hasStronglyCodedApexCoatomExtensions`. -/
theorem stronglyCodedPaddingExtensionStep : StronglyCodedPaddingExtensionStep α :=
  fun hα _ _ _ _ hl hsc hp hD hDs ↦ exists_stronglyCoded_pinned_extension
    (hasStronglyCodedApexCoatomExtensions hα) ⟨hl, hsc⟩ hp ⟨hD.1, hDs⟩ hD.2

end Steps

end Realization

/-! ### The derivation of restricted (R3) -/

namespace Realization

section Derivation

variable (ξ : Ordinal.{0}) (M : Type w)

/-- **Hollow growth acquisition in the strongly coded receiving class** for a calibration `C`, an
explicit premise: for `R` in the class at `λ_ξ` with the restricted hollow property, every cover
`c` of positive arity of a stage type `t` extends, for each one-point coface `d` of `t` with
strongly coded rows, to a cover `c'` of some `t'` along some `h` (`c' ∘ h = c`) with `C t' h d`.
The counterpart of `Realization.HollowGrowthAcquisition`, over positive covers and strongly coded
cofaces. -/
def StronglyCodedHollowGrowthAcquisition
    (C : ∀ {α : Ordinal.{0}} {n k : ℕ}, StageType.{0} α k → (Fin n ↪ Fin k) →
      StageType.{0} α (n + 1) → Prop) : Prop :=
  ∀ R : Realization.{0, w} (blockStage ξ) M, R.IsStronglyCodedReceiving →
    R.HasRestrictedTerminalProperty (.inr (.inr ())) →
    ∀ ⦃n : ℕ⦄, 0 < n → ∀ (t : StageType.{0} (blockStage ξ) n) (c : Fin n → M), R.Covers t c →
      ∀ d ∈ t.cofaces, d.rows.IsStronglyCoded →
        ∃ (k : ℕ) (t' : StageType.{0} (blockStage ξ) k) (c' : Fin k → M) (h : Fin n ↪ Fin k),
          R.Covers t' c' ∧ c' ∘ h = c ∧ C t' h d

/-- **Target: hollow growth acquisition in the class for the hollow reference calibration with
bounded donor offsets**: the counterpart of `Realization.hollowGrowthAcquisition_reference'`.
Proved: `Realization.stronglyCodedHollowAcquisitionTarget`. -/
def StronglyCodedHollowAcquisitionTarget : Prop :=
  StronglyCodedHollowGrowthAcquisition ξ M StageType.HollowReferenceCalibration'

/-- **Restricted (R3) over covers of positive arity**: `Realization.StronglyCodedHollowReceiving`
asked only over covers of positive arity. -/
def StronglyCodedHollowReceivingPos : Prop :=
  ∀ R : Realization.{0, w} (blockStage ξ) M, R.IsStronglyCodedReceiving →
    R.HasRestrictedTerminalProperty (.inr (.inr ())) →
    ∀ ⦃n : ℕ⦄, 0 < n → ∀ (t : StageType.{0} (blockStage ξ) n) (c : Fin n → M), R.Covers t c →
      ∀ D ∈ t.cofaces, D.rows.IsStronglyCoded → ∃ y : M, R.Covers D (Fin.snoc c y)

/-- **Target: padding of the empty cover in the class**: restricted (R3) over positive covers gives
restricted (R3).  The counterpart of `Realization.HollowReceiving.of_pos`,
whose two uses beyond exact consistency and legality have strongly coded replacements: an
occurrence of positive arity (from unbounded growth instead of `IsModel.exists_le_arity`) and the
strongly coded pinned extension (`StageType.exists_stronglyCoded_pinned_extension` instead of
`StageType.exists_pinned_extension_of_isSuccPrelimit`).  Proved:
`Realization.stronglyCodedHollowPadding`. -/
def StronglyCodedHollowPadding : Prop :=
  StronglyCodedHollowReceivingPos ξ M → StronglyCodedHollowReceiving ξ M

variable {ξ M}

/-- **Restricted (R3) over positive covers from acquisition and strongly coded exact growth
carriers** (native construction), for one calibration `C`: as
`Realization.hollowReceiving_of_hasExactGrowthCarriers_pos`.  The acquired context is an actual
type, legal and strongly coded by the class fields; the carrier is strongly coded; it is realized
over the context by strongly coded receiving and read with the actual labels
(`GrowthCarrier.exists_eval_eq_of_recovers_eq_of_isStronglyCoded`). -/
theorem stronglyCodedHollowReceivingPos_of_hasExactStronglyCodedGrowthCarriers
    {C : ∀ {α : Ordinal.{0}} {n k : ℕ}, StageType.{0} α k → (Fin n ↪ Fin k) →
      StageType.{0} α (n + 1) → Prop}
    (hacq : StronglyCodedHollowGrowthAcquisition ξ M C)
    (hcar : StageType.HasExactStronglyCodedGrowthCarriers.{0}
      fun {_ n _} t' h d ↦ C t' h d ∧ 0 < n) :
    StronglyCodedHollowReceivingPos ξ M := by
  intro R hR hP n hn t c hc D hD hDs
  obtain ⟨k, t', c', h, hc', hcc', hC⟩ := hacq R hR hP hn t c hc D hD hDs
  subst hcc'
  exact hR.exists_covers_of_calibratedContext hcar hc'
    (restrictFace_of_covers hR.isConsistent hc hc' rfl) hD hDs ⟨hC, hn⟩

/-- **Restricted (R3) over positive covers from acquisition alone** (native construction): the
strongly coded exact growth carriers for the hollow reference calibration with a nonempty root are
`StageType.hasExactStronglyCodedGrowthCarriers_codedLadder`. -/
theorem stronglyCodedHollowReceivingPos_of_acquisition
    (hacq : StronglyCodedHollowAcquisitionTarget ξ M) : StronglyCodedHollowReceivingPos ξ M :=
  stronglyCodedHollowReceivingPos_of_hasExactStronglyCodedGrowthCarriers hacq
    StageType.hasExactStronglyCodedGrowthCarriers_codedLadder

variable (ξ M)

/-- **Target: restricted (R3) from acquisition and padding**: the strongly coded exact growth
carriers of the coded ladder and the realization of strongly coded carriers by restricted receiving
reduce `Realization.StronglyCodedHollowReceiving ξ M` to the two named premises: acquisition in the
class (`Realization.StronglyCodedHollowAcquisitionTarget ξ M`) and padding
(`Realization.StronglyCodedHollowPadding ξ M`). -/
def StronglyCodedHollowDerivationTarget : Prop :=
  StronglyCodedHollowAcquisitionTarget ξ M → StronglyCodedHollowPadding ξ M →
    StronglyCodedHollowReceiving ξ M

/-- **Restricted (R3) from acquisition and padding** (native construction):
`Realization.stronglyCodedHollowReceivingPos_of_acquisition`, then padding. -/
theorem stronglyCodedHollowDerivationTarget : StronglyCodedHollowDerivationTarget ξ M :=
  fun hacq hpad ↦ hpad (stronglyCodedHollowReceivingPos_of_acquisition hacq)

/-- **Padding of the empty cover in the class** (native construction): as
`Realization.HollowReceiving.of_pos`, with an occurrence of positive arity from unbounded growth
(`Realization.positiveOccurrenceStep`) and the strongly coded pinned extension over the empty face
(`Realization.stronglyCodedPaddingExtensionStep`); the arity-zero cover is received through that
occurrence and restricted to the new point by exact consistency. -/
theorem stronglyCodedHollowPadding : StronglyCodedHollowPadding ξ M := by
  intro hpos R hR hP n t c hc D hD hDs _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  swap
  · exact hpos R hR hP hn t c hc D hD hDs
  obtain ⟨hhol, htop⟩ := hP
  obtain ⟨x, hxpos⟩ := positiveOccurrenceStep _ M R htop
  let f : Fin 0 ↪ Fin x.arity := Function.Embedding.ofIsEmpty
  obtain ⟨p₀, hp₀⟩ := Option.isSome_iff_exists.mp (x.type.isSome_restrictFace_of_zero f)
  have htp : t = p₀ := by
    have h1 := Realization.eval_face hR.isConsistent x f
    rw [hp₀] at h1
    have h2 : R.eval (f.trans x.tuple) = R.eval ⟨c, hc.injective⟩ := by
      congr 1
      ext i
      exact i.elim0
    rw [h2, hc.eval_eq] at h1
    exact Option.some_injective _ h1
  subst htp
  obtain ⟨Q, hQ, hQx, hQD⟩ := stronglyCodedPaddingExtensionStep _ (isSuccPrelimit_blockStage ξ)
    x.type t D (hR.hasLegalTypes _ _ x.eval_tuple) (hR.isStronglyCoded _ _ x.eval_tuple) hp₀ hD
    hDs
  obtain ⟨y, hy⟩ := hpos R hR ⟨hhol, htop⟩ hxpos x.type x.tuple (covers_of_eval _ x.eval_tuple) Q
    ⟨hQ.1, hQx⟩ hQ.2
  refine ⟨y, ?_⟩
  have hres := hR.isConsistent _ Q (extendByLast f) hy.eval_eq
  rw [hQD] at hres
  refine ⟨?_, ?_⟩
  · intro i j _
    exact Fin.ext (by omega)
  · rw [← hres]
    congr 1
    ext i
    obtain rfl : i = Fin.last 0 := Fin.ext (by omega)
    simp only [Function.Embedding.coeFn_mk, Function.Embedding.trans_apply, extendByLast_last]
    change Fin.snoc (α := fun _ ↦ M) c y (Fin.last 0) =
      Fin.snoc (α := fun _ ↦ M) (⇑x.tuple) y (Fin.last x.arity)
    rw [Fin.snoc_last, Fin.snoc_last]

/-- **Acquisition of the hollow reference calibration in the class** (native construction): the
argument of `Realization.hollowGrowthAcquisition_reference'` for `R` in the strongly coded receiving
class with the restricted hollow property.  Reference cells for the blocks of the labels of the
donor come from strongly coded receiving (`Realization.stronglyCodedReferenceCellsTarget`), an
occurrence with more points than every donor offset from unbounded growth
(`Realization.exists_le_arity_of_topGradeSup_eq_top`), one occurrence `w` containing both from
covering, and the marked-cap context over `w` from
`Realization.IsStronglyCodedReceiving.exists_markedCapContextBelow'`.  The donor's strong coding
and the positivity of the cover are not used. -/
theorem stronglyCodedHollowAcquisitionTarget : StronglyCodedHollowAcquisitionTarget ξ M := by
  classical
  intro R hR hP n _ t c hc d _ _
  obtain ⟨⟨hhol, -⟩, htop⟩ := hP
  have hα := isSuccLimit_blockStage ξ
  choose ν hν B hB using StageType.exists_block_bound hα d
  let x : R.Occurrence := ⟨n, ⟨c, hc.injective⟩, t, hc.eval_eq⟩
  obtain ⟨y, fy, K, B₁, hfy, -, -, href⟩ :=
    stronglyCodedReferenceCellsTarget (blockStage ξ) M (isSuccPrelimit_blockStage ξ) R
      hR.isConsistent (fun _ t p h ↦ ⟨hR.hasLegalTypes t p h, hR.isStronglyCoded t p h⟩)
      hR.receiving x hα.bot_lt (List.ofFn ν) fun μ hμ ↦ by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hμ
        exact hν i
  obtain ⟨z, hz⟩ := exists_le_arity_of_topGradeSup_eq_top htop (univ.sup B)
  obtain ⟨w, hw⟩ := hR.isCovering.exists_subset_support (univ.map y.tuple ∪ univ.map z.tuple)
  obtain ⟨gy, hgy⟩ := w.exists_trans_eq (subset_union_left.trans hw)
  obtain ⟨gz, -⟩ := w.exists_trans_eq (subset_union_right.trans hw)
  have hzw : z.arity ≤ w.arity := by simpa using Fintype.card_le_of_embedding gz
  obtain ⟨k, t', c', g, hc', hcg, ⟨cc, rr, hmc, hoff, hbot⟩⟩ :=
    hR.exists_markedCapContextBelow' hhol htop w.type w.tuple (covers_of_eval _ w.eval_tuple)
  have hface : restrictFace g t' = some w.type :=
    restrictFace_of_covers hR.isConsistent (covers_of_eval _ w.eval_tuple) hc' hcg
  have hgrade : w.arity + 1 < t'.toCellScheme.grade cc := hmc.2.2.1
  refine ⟨k, t', c', (fy.trans gy).trans g, hc', ?_, w.arity, g, fy.trans gy, cc, rr, rfl,
    hmc, hoff, hbot, fun i o ho ↦ ?_⟩
  · funext i
    change (c' ∘ g) (gy (fy i)) = c i
    rw [hcg]
    change (gy.trans w.tuple) (fy i) = c i
    rw [hgy]
    exact DFunLike.congr_fun hfy i
  · obtain ⟨m, hmB, hm⟩ := hB i o ho
    obtain ⟨zc, r', -, hzc, -⟩ := href (ν i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
    obtain ⟨zw, hzw', -⟩ := Occurrence.exists_label_grade_eq_of_trans_eq hR.isConsistent hgy zc
    obtain ⟨z', -, hz'l, -⟩ := exists_cellMap_of_restrictFace_eq hface zw
    have hmN : m < t'.toCellScheme.grade cc := by
      have := le_sup (f := B) (mem_univ i)
      omega
    exact ⟨ν i, m, r', t'.cellMap g z', (hν i).1, hm, hmN, t'.cellMap_mem g z',
      hz'l.trans (hzw'.trans hzc)⟩

/-- **Restricted (R3) from acquisition in the class** (native construction): the derivation
(`Realization.stronglyCodedHollowDerivationTarget`) with padding
(`Realization.stronglyCodedHollowPadding`); the acquisition
`Realization.StronglyCodedHollowAcquisitionTarget ξ M` is proved
(`Realization.stronglyCodedHollowAcquisitionTarget`), which gives
`Realization.stronglyCodedHollowReceiving`. -/
theorem stronglyCodedHollowReceiving_of_acquisition
    (hacq : StronglyCodedHollowAcquisitionTarget ξ M) : StronglyCodedHollowReceiving ξ M :=
  stronglyCodedHollowDerivationTarget ξ M hacq (stronglyCodedHollowPadding ξ M)

/-- **Restricted (R3), exact hollow-growth receiving in the strongly coded receiving class**
(native construction): `Realization.StronglyCodedHollowReceiving ξ M` for every `ξ` and `M`, from
the acquisition in the class (`Realization.stronglyCodedHollowAcquisitionTarget`), padding, strongly
coded exact growth carriers from the coded ladder, and their realization by strongly coded
receiving. -/
theorem stronglyCodedHollowReceiving : StronglyCodedHollowReceiving ξ M :=
  stronglyCodedHollowReceiving_of_acquisition ξ M (stronglyCodedHollowAcquisitionTarget ξ M)

end Derivation

end Realization

end VaughtConjecture
