/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapRelabel
import VaughtConjecture.Continuation.TiedRootCapEngine

/-!
# The engine's coatom provision at an acquired context: root cells labelled `⊥`

Roadmap, Layer 3 ((R3) of the table of 3.4).

The engine's admission of correct states (on the engine's branch: `Adm` the correct states,
`InClass` everything, `CapBot` the states with private cap `⊥`) asks, through its coatom provision
from the grade of the cap, that every state lawful below the private coatom and `⊤` at the cap
extend to a correct state lawful on the cut.  This file tests it at an **acquired** marked-cap
context, one whose root offsets lie below the grade of its cap
(`TiedRootCapRelabel.MarkedCapContextBelow`).

* **The forbidden-extension lemma** (`TiedRootCapEngine.not_coatomProvision_of_forbidden`,
  compiled in this repository (theorem named)): a state lawful below a coatom, `⊤` at a cell of the
  grade `N` below it, whose cut-lawful extensions all violate a consequence of admission at cap
  `⊤`, refutes the coatom provision from the grade `N`.
* **The coded cap over a type labelled `⊥`** (`StageType.isLawful_apexLabel_codedScheme_of_bot`,
  with `Label.keepTopShifter`, compiled).
* **The instance** (`BottomRootCounterexample`, compiled): the root of
  `TiedRootCapCounterexample` (rows `(1, 2)`) labelled `⊥`; its donor (the completion of two
  copies), whose apex reads both root cells at `⊥`; the context (the coded cap, over the completion
  below the full grade labelled `⊥`, of a labelling reading the root as `(1, 2)` and capped at
  `3`).  The context is an acquired marked-cap context
  (`BottomRootCounterexample.markedCapContextBelow_context`: the root labels are `⊥`, so the
  offset bound holds vacuously).
* **The provision fails** (`BottomRootCounterexample.not_coatomProvision`, compiled): over the
  seed of the context and a three-point carrier of the donor, for every set `T` of cells read
  from below containing the donor's apex, `¬ CoatomProvision seedFour 3 (capRequestsT T).IsCorrect`.
  The separating labelling, `⊤` at the cap, separates two root cells labelled `⊥` that the donor's
  apex ties.  It is outside the bottom class of the context
  (`BottomRootCounterexample.separating_not_inClass`).

**What fails.**  The root offset bound keeps ordinal root ties (`StageType.le_of_rootOffsetsBelow`)
and the row inequality keeps ties at `⊤` at labellings `⊤` at the marker; ties at `⊥` are kept only
by the bottom class.  The engine's admission of correct states has no bottom class, so its coatom
provision asks the raise at labellings separating root cells labelled `⊥`, and fails there.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### The provision fails at a forbidden extension -/

namespace TiedRootCapEngine

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The coatom provision fails at a state whose extensions are all forbidden.**  Let `W` be
lawful below the coatom `univ.erase x` at the grade `N`, `⊤` at a cell `capA` of the grade `N`
below that coatom, and let every admitted state `⊤` at `capA` have a property `Q`.  If no state
lawful on the grade-`N` cut and agreeing with `W` below the coatom has its splice with `Q`, the
coatom provision from the grade `N` fails. -/
theorem not_coatomProvision_of_forbidden {N : ℕ} (hN0 : 0 < N) (hNm : N ≤ m + 1)
    {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) {Adm Q : Prof I → Prop}
    {W : Prof I} (hW : I.amalgam.rows.IsLawfulBelow (univ.erase x, N) (fun d ↦ W d))
    {capA : Fin I.amalgam.card} (hcapg : I.amalgam.toCellScheme.grade capA = N)
    (hcapb : capA ∈ I.amalgam.toCellScheme.below (univ.erase x, N)) (hcap : W capA = ⊤)
    (hAdm : ∀ s, Adm s → s capA = ⊤ → Q s)
    (hforbid : ∀ W', IsCutLawful I N W' →
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, N), W' d = W d) → ¬ Q (hat I N W')) :
    ¬ CoatomProvision I N Adm := by
  intro hprov
  obtain ⟨W', hW', hW'W, hpr⟩ := hprov le_rfl hN0 hNm hx hW
  have hcap' : W' capA = ⊤ := (hW'W _ hcapb).trans hcap
  have hadm := (provisionAt_iff_of_eq_top hcapg hcap').mp hpr
  exact hforbid W' hW' hW'W (hAdm _ hadm (by rw [hat_of_le hcapg.le]; exact hcap'))

end TiedRootCapEngine

/-! ### A shifter keeping only the formal top -/

namespace Label

open Classical in
/-- The shifter sending the formal top to itself and every other label to `⊥`. -/
noncomputable def keepTopShifter (x : Label.{u}) : Label.{u} := if x = ⊤ then ⊤ else ⊥

theorem keepTopShifter_top : keepTopShifter (⊤ : Label.{u}) = ⊤ := by simp [keepTopShifter]

theorem keepTopShifter_of_ne {x : Label.{u}} (h : x ≠ ⊤) : keepTopShifter x = ⊥ := by
  simp [keepTopShifter, h]

theorem monotone_keepTopShifter : Monotone (keepTopShifter : Label.{u} → Label.{u}) :=
    fun a b hab ↦ by
  by_cases hb : b = ⊤
  · rw [hb, keepTopShifter_top]; exact le_top
  · have ha : a ≠ ⊤ := fun h ↦ hb (top_le_iff.mp (h ▸ hab))
    rw [keepTopShifter_of_ne ha]; exact bot_le

theorem keepTopShifter_visibilityReplace (k i : ℕ) (x : Label.{u}) :
    keepTopShifter (visibilityReplace k i x) = visibilityReplace k i (keepTopShifter x) := by
  induction x using recBotCoeTop with
  | bot => rw [visibilityReplace_bot, keepTopShifter_of_ne bot_ne_top, visibilityReplace_bot]
  | top => rw [visibilityReplace_top, keepTopShifter_top, visibilityReplace_top]
  | coe o =>
    rw [visibilityReplace_coe, keepTopShifter_of_ne (by simp), keepTopShifter_of_ne (by simp),
      visibilityReplace_bot]

end Label

/-! ### The coded cap over a type labelled `⊥` -/

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ} {t : StageType.{u} α n} (ht : t.IsLegalBelowFullGrade)
  {V : Finset Label.{u}} {ℓ : Fin t.card → Label.{u}}

/-- **Over a type labelled `⊥`, the labels with `⊤` at the coded cap are lawful** when `ℓ` is
never the formal top: the block decoding followed by the shifter keeping only `⊤`. -/
theorem isLawful_apexLabel_codedScheme_of_bot (hbot : ∀ d, t.label d = ⊥)
    (hℓ : ∀ d, ℓ d ≠ ⊤) (hV : ∀ d, ℓ d ∈ V) :
    (codedScheme ht V ℓ).rows.IsLawful (apexLabel (t := t)) := by
  refine Scheme.isLawful_appendFullCell ?_ ?_ ?_ fun d hd ↦ absurd hd (ht.grade_lt d).ne
  · convert t.isLawful using 1
    funext d
    exact apexLabel_castSucc d
  · rw [apexLabel_last]
    exact isSelfVisible_top n
  · have hw : IsWitness (fun _ ↦ (⊤ : Label.{u})) (keepTopShifter ∘ blockDecode V) :=
      ⟨antitone_const, fun _ ↦ isSelfVisible_top _, by
        simp [blockDecode_bot, keepTopShifter_of_ne bot_ne_top],
        monotone_keepTopShifter.comp isWitness_blockDecode.monotone, fun x k _ i hi ↦ by
          simp only [Function.comp_apply]
          rw [isWitness_blockDecode.visibilityReplace_comm x k le_top i hi,
            keepTopShifter_visibilityReplace]⟩
    refine ⟨fun _ ↦ ⊤, keepTopShifter ∘ blockDecode V, hw, fun d ↦ ?_⟩
    beta_reduce
    rw [min_top_right, apexLabel_last, min_top_right]
    induction d using Fin.lastCases with
    | last =>
      rw [apexLabel_last, Function.comp_apply, codedRow_last, blockDecode_blockEncode_top,
        keepTopShifter_top]
    | cast d =>
      rw [apexLabel_castSucc, Function.comp_apply, codedRow_castSucc,
        blockDecode_blockEncode (hV d), keepTopShifter_of_ne (hℓ d), hbot]

end StageType

end VaughtConjecture
