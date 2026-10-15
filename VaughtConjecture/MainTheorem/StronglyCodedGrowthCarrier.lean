/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.CodedLadderStable
import VaughtConjecture.MainTheorem.GrowthAdmittedCarrier
import VaughtConjecture.MainTheorem.StronglyCodedTerminalProperty

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

## The saturation use, and its replacement

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
strongly coded rows) applied to the saturation instance `d ∈ x.type.cofaces` on `G.scheme` at any
permitted cutoff (here `0`, permitted at a positive stage): the received type has the scheme of
`d`, which is `G.scheme`.  The instance `d` is strongly coded exactly when the carrier scheme is
(strong coding is a property of the rows), so the carrier must be **strongly coded**; it is the
received coface, the actual type of `w`, that is then strongly coded and a coface of `x.type`.
The cutoff-stable recovery of the coded ladder
(`StageType.hasStronglyCodedCutoffStableRecovery`) is not used: it concerns the stable labels of
(R4), not the actual labels.

* `GrowthCarrier.exists_eval_eq_of_recovers_eq_of_isStronglyCoded` (proved, native construction):
  the replacement, from exact consistency, strongly coded receiving and a positive stage.
* `Realization.StronglyCodedCarrierEvaluationTarget` and its proof
  `Realization.stronglyCodedCarrierEvaluationTarget`: the same for `R` in the class.

## Strongly coded exact growth carriers

* `StageType.HasExactStronglyCodedGrowthCarriers C`: `StageType.HasExactGrowthCarriers C` with a
  strongly coded context and donor as inputs and a strongly coded carrier as output.
* `StageType.hasExactStronglyCodedGrowthCarriers_codedLadder` (proved, native construction): for the
  hollow reference calibration with a nonempty root, from the coded contract
  `StageType.hasCodedLadderGrowthCarriers_levels`, recognition
  `GrowthCarrier.recognizes_of_codedLadder`, recovery
  `StageType.GrowthRequests.recovers_eq_of_recognizes`, and the field
  `GrowthCarrier.CodedLadder.stronglyCoded`, which the unrestricted route
  (`StageType.HasCodedLadderGrowthCarriers.exists_recognizes`) forgets.

## The derivation of restricted (R3)

* `Realization.StronglyCodedHollowGrowthAcquisition ξ M C`: the acquisition of calibrated contexts
  in the class, an explicit premise: over every cover of positive arity, for every strongly coded
  one-point coface, a cover of a context calibrated by `C`.  The acquisition of
  `VaughtConjecture.MainTheorem.StronglyCodedCalibratedContexts`
  (`Realization.CalibratedContextAcquisitionTarget`) is for the non-hollow case and the margin
  calibration of (R4); it does not apply here.  Only its reference-cell step carries over
  (`Realization.stronglyCodedReferenceCellsTarget`, the premise `huni` of
  `Realization.acquiresCalibratedContexts_gradedCapMargin_of_exists_extend_uniformity`).
* `Realization.StronglyCodedHollowReceivingPos ξ M`: restricted (R3) over covers of positive arity.
* `Realization.StronglyCodedHollowPadding ξ M` (stated, not proved): padding of the empty cover in
  the class, the counterpart of `Realization.HollowReceiving.of_pos`.
* `Realization.stronglyCodedHollowReceivingPos_of_hasExactStronglyCodedGrowthCarriers` (proved):
  restricted (R3) over positive covers from acquisition and strongly coded exact growth carriers for
  one calibration, as `Realization.hollowReceiving_of_hasExactGrowthCarriers_pos`.
* `Realization.StronglyCodedHollowDerivationTarget ξ M` and its proof
  `Realization.stronglyCodedHollowDerivationTarget`: `Realization.StronglyCodedHollowReceiving ξ M`
  from the two named premises `Realization.StronglyCodedHollowAcquisitionTarget ξ M` (acquisition
  for `StageType.HollowReferenceCalibration'`) and `Realization.StronglyCodedHollowPadding ξ M`.

## Modelhood audit of the unrestricted (R3) route

The route of `Realization.hollowReceiving_levels`, step by step, with the clause of a model it
uses and its status in the strongly coded receiving class ("replaced": a compiled strongly coded
result; "class field": a clause of `Realization.IsStronglyCodedReceiving`; "replaceable": a
replacement named, not composed here; "MISSING": no strongly coded construction).

Each entry: step; the clause of a model it uses; status in the class.

* Padding, an occurrence of positive arity; `IsModel.exists_le_arity`; replaceable by unbounded
  growth (`topGradeSup = ⊤` and `StageType.grade_le`).
* Padding, the pinned extension; none (`StageType.exists_pinned_extension_of_isSuccPrelimit`);
  replaceable by `StageType.exists_stronglyCoded_pinned_extension`.
* Acquisition, reference cells; `IsModel.exists_extend_uniformity`; replaced by
  `Realization.stronglyCodedReferenceCellsTarget`.
* Acquisition, an occurrence with more points than the donor offsets; `IsModel.exists_le_arity`;
  replaceable by unbounded growth.
* Acquisition, one occurrence containing both; `IsModel.isCovering`; class field.
* Synchronization with forcing (`Realization.IsModel.exists_forcing_floor`); covering and
  consistency only; class fields.
* A top cap of the floor; `IsModel.isLegal`; class field.
* One point more; `IsModel.dominance` at `0`; replaced by
  `Realization.HasFiniteCutReceivingIn.dominance_of_hasStronglyCodedCofaceInstances`.
* The bot-keeping completion of the seed; none (`Seed.exists_botKeeping`); **MISSING** in the
  strongly coded form, `StageType.StronglyCodedBotKeepingCofaceTarget`.
* The bottom-pattern realization; `IsModel.bottomPattern`; replaceable once the previous step
  holds: class receiving and `StageType.receivingFamily_subset_bottomPatternFamily`.
* The marked-cap context; none (`StageType.markedCapContextBelow'_of_botKeeping`); unchanged.
* Exact growth carriers; none; replaced by
  `StageType.hasExactStronglyCodedGrowthCarriers_codedLadder`.
* Legality and strong coding of the acquired context; `IsModel.isLegal`; class fields.
* Realization of the carrier; `IsModel.saturation`; replaced by
  `GrowthCarrier.exists_eval_eq_of_recovers_eq_of_isStronglyCoded`.
* The evaluation; `IsModel.isConsistent`; class field.

The first missing construction is in the acquisition, at the bottom-pattern step of
`Realization.rootBottomAcquisition`: the coface realized there is the completion of a bot-keeping
completion below the full grade of the seed of a coatom type with itself, whose apex row is the
block coding of the labels (`StageType.addApex`).  To receive it in the class it must be strongly
coded.  Strongly coded completions exist (`Seed.exists_completionBelowFullGrade_isStronglyCoded`,
completed by `CompletionBelowFullGrade.strongCompletion`), and bot-keeping ones exist
(`Seed.exists_botKeeping`), but no compiled completion is both, with the strongly coded apex
reading the cells labelled `⊥` as `⊥`.  `StageType.StronglyCodedBotKeepingCofaceTarget` states what
is needed; its unrestricted form is proved (`StageType.exists_botKeepingCoface`).  It is not built
here.

All results here are native constructions of this repository; no correspondence with [AFK26] is
claimed.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Finset Label StageType

/-! ### The realization of a strongly coded carrier by restricted receiving -/

namespace GrowthCarrier

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M} {n : ℕ}

/-- **Exact receiving from exact recovery, by strongly coded receiving** (native construction):
`GrowthCarrier.exists_eval_eq_of_recovers_eq` with generalized saturation replaced by finite-cut
receiving for the cofaces with strongly coded rows, for a carrier with strongly coded rows, at a
positive stage.  The saturation instance `d` on the carrier scheme is strongly coded and is
received over `x` at the cutoff `0`; the received tuple `w` has a type `r` on the carrier scheme,
a coface of the type of `x` with strongly coded rows, and its face along the root `e` followed by
the new point has type `D` by the recovery (`GrowthCarrier.exists_recovered_of_eval`). -/
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
  obtain ⟨w, hw, r, hr, hev⟩ := hrec x d hd hds 0 (isPermittedCutoff_zero.mpr hα)
  have hrE : r.toScheme = G.scheme := hr.1.trans hdE'
  obtain ⟨s, hs, hsD, hl⟩ :=
    G.exists_recovered_of_eval hR (Realization.typeLabelling R) hrecov hw hev hrE
  have hrl : r.IsLegal := by
    change Scheme.IsLegal r.toScheme
    rw [hrE]
    exact G.isLegal
  have hrf : restrictFace Fin.castSuccEmb r = some x.type := by
    rw [← hR w r _ hev, hw]
    exact x.eval_tuple
  have hrs : r.rows.IsStronglyCoded := by
    rw [hrE]
    exact hG
  exact ⟨w, r, hw, hev, ⟨hrl, hrf⟩, hrE, hrs, castSuccEmb_trans_extendByLast_trans hw,
    last_notMem_range hw, hs.trans (congrArg some (StageType.ext hsD hl))⟩

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

/-! ### The first missing construction: a strongly coded bot-keeping coface -/

/-- **A bot-keeping coface** (native construction): over a legal stage type `q₀` on `m + 1` points
with a face along the first `m` points, at a stage that is zero or a limit, some coface `qs` of
`q₀` has every cell of full scope that is its apex (grade `m + 2`) or not labelled `⊥` reading
every cell of proper scope labelled `⊥` as `⊥`.  It is the completion of a bot-keeping completion
below the full grade of the seed of `q₀` with itself (`Seed.exists_botKeeping`,
`CompletionBelowFullGrade.BotKeeping.rowAt_completion_eq_bot`), the coface used in
`Realization.rootBottomAcquisition_of_botKeeping`.  Its apex row is the block coding of the labels,
which need not be strongly coded. -/
theorem exists_botKeepingCoface {α : Ordinal.{u}} {m : ℕ} (hα : Order.IsSuccPrelimit α)
    {q₀ : StageType.{u} α (m + 1)} (hl : q₀.IsLegal) {p : StageType.{u} α m}
    (hp : restrictFace Fin.castSuccEmb q₀ = some p) :
    ∃ qs ∈ q₀.cofaces, ∀ u y, qs.toCellScheme.scope u = univ →
      (qs.toCellScheme.grade u = m + 2 ∨ qs.label u ≠ ⊥) → qs.toCellScheme.scope y ≠ univ →
        qs.label y = ⊥ → qs.rowAt u y = ⊥ := by
  obtain ⟨F, hF⟩ := (Seed.ofCoatoms hl hl hp hp).exists_botKeeping
  exact ⟨F.completion hα, ⟨F.isLegal_completion _, F.restrictFace_left_completion hα⟩,
    fun u y hsu hu hys hyb ↦ hF.rowAt_completion_eq_bot hα u y hsu hu hys hyb⟩

/-- **Target: a strongly coded bot-keeping coface**, still to be proved:
`StageType.exists_botKeepingCoface` for a strongly coded `q₀`, with a coface `qs` whose rows are
strongly coded.  This is what the bottom-pattern step of `Realization.rootBottomAcquisition` needs
in the strongly coded receiving class, where only cofaces with strongly coded rows are received;
with it, receiving `qs` at a permitted cutoff realizes its bottom pattern
(`StageType.receivingFamily_subset_bottomPatternFamily`). -/
def StronglyCodedBotKeepingCofaceTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃m : ℕ⦄ (q₀ : StageType.{u} α (m + 1)) (p : StageType.{u} α m),
    Order.IsSuccPrelimit α → q₀.IsLegal → q₀.rows.IsStronglyCoded →
    restrictFace Fin.castSuccEmb q₀ = some p →
    ∃ qs ∈ q₀.cofaces, qs.rows.IsStronglyCoded ∧ ∀ u y, qs.toCellScheme.scope u = univ →
      (qs.toCellScheme.grade u = m + 2 ∨ qs.label u ≠ ⊥) → qs.toCellScheme.scope y ≠ univ →
        qs.label y = ⊥ → qs.rowAt u y = ⊥

end StageType

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
bounded donor offsets**, still to be proved: the counterpart of
`Realization.hollowGrowthAcquisition_reference'`.  Its bottom-pattern step needs
`StageType.StronglyCodedBotKeepingCofaceTarget` (missing); its other steps have strongly coded
replacements (see the audit in the module documentation). -/
def StronglyCodedHollowAcquisitionTarget : Prop :=
  StronglyCodedHollowGrowthAcquisition ξ M StageType.HollowReferenceCalibration'

/-- **Restricted (R3) over covers of positive arity**: `Realization.StronglyCodedHollowReceiving`
asked only over covers of positive arity. -/
def StronglyCodedHollowReceivingPos : Prop :=
  ∀ R : Realization.{0, w} (blockStage ξ) M, R.IsStronglyCodedReceiving →
    R.HasRestrictedTerminalProperty (.inr (.inr ())) →
    ∀ ⦃n : ℕ⦄, 0 < n → ∀ (t : StageType.{0} (blockStage ξ) n) (c : Fin n → M), R.Covers t c →
      ∀ D ∈ t.cofaces, D.rows.IsStronglyCoded → ∃ y : M, R.Covers D (Fin.snoc c y)

/-- **Target: padding of the empty cover in the class**, still to be proved: restricted (R3) over
positive covers gives restricted (R3).  The counterpart of `Realization.HollowReceiving.of_pos`,
whose two uses beyond exact consistency and legality have strongly coded replacements: an
occurrence of positive arity (from unbounded growth instead of `IsModel.exists_le_arity`) and the
strongly coded pinned extension (`StageType.exists_stronglyCoded_pinned_extension` instead of
`StageType.exists_pinned_extension_of_isSuccPrelimit`). -/
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
  let x : R.Occurrence := ⟨k, ⟨c', hc'.injective⟩, t', hc'.eval_eq⟩
  obtain ⟨G, hGs, hrec⟩ := hcar t' h (isSuccLimit_blockStage ξ)
    (hR.hasLegalTypes _ _ hc'.eval_eq) (hR.isStronglyCoded _ _ hc'.eval_eq) t
    (restrictFace_of_covers hR.isConsistent hc hc' hcc') D hD hDs ⟨hC, hn⟩
  have hpos : (0 : Ordinal.{0}) < blockStage ξ :=
    Ordinal.omega0_pos.trans_le (omega0_le_blockStage ξ)
  obtain ⟨w, r, -, -, -, -, -, hu, -, hev⟩ :=
    GrowthCarrier.exists_eval_eq_of_recovers_eq_of_isStronglyCoded hR.isConsistent hR.receiving
      hpos x G hGs
      (G.nonempty_cofaces_inter_saturationFamily_of_isSuccPrelimit
        (isSuccPrelimit_blockStage ξ) rfl) hrec
  set u := (extendByLast h).trans w
  refine ⟨u (Fin.last n), ?_⟩
  have hfun : Fin.snoc c (u (Fin.last n)) = ⇑u := by
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i =>
      rw [Fin.snoc_castSucc, ← hcc']
      exact (DFunLike.congr_fun hu i).symm
  rw [hfun]
  exact covers_of_eval u hev

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

end Derivation

end Realization

end VaughtConjecture
