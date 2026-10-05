/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.GatedExtensionCounterexample

/-!
# Examples for gated extensions

Special cases of `VaughtConjecture.Extension.GatedExtension` and
`VaughtConjecture.Extension.GatedExtensionCounterexample`:

* **bottom and top donors**: a donor whose new cells are all labelled `⊥`, or all `⊤`, is
  anchored below every cell of every private type; the refutation uses a donor of the first kind,
  so its failure is in the legality of the display, not in the readings of the gate;
* **the stage `ω`** and **the stage `0`**: the gated pinned extension property fails there, as at
  every stage;
* **the refuting private type**: legal, with two cells of graded index `(univ, 2)` labelled `⊤`;
  it has no gated extension over the empty root, with any donor;
* **the inhabited gated extension** at private arity `2` over the empty root, with the cap
  labelled `⊤`: every hypothesis of the gated pinned extension property holds, and the gate has no
  twins.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.StageType

open Finset Label
open GatedExtensionExample (emptyRoot)

variable {α : Ordinal.{u}}

/-! ### Bottom and top donors -/

/-- **A donor whose new cells are all labelled `⊥` is anchored** below every cell of every
private type. -/
example {n m : ℕ} (P : StageType.{u} α n) (C : Fin P.card) {d : StageType.{u} α (m + 1)}
    (hd : ∀ j, Fin.last m ∈ d.toCellScheme.scope j → d.label j = ⊥) : IsAnchored P C d :=
  isAnchored_of_forall_label_eq_bot_or_top P C fun j hj ↦ Or.inl (hd j hj)

/-- **A donor whose new cells are all labelled `⊤` is anchored** below every cell of every
private type. -/
example {n m : ℕ} (P : StageType.{u} α n) (C : Fin P.card) {d : StageType.{u} α (m + 1)}
    (hd : ∀ j, Fin.last m ∈ d.toCellScheme.scope j → d.label j = ⊤) : IsAnchored P C d :=
  isAnchored_of_forall_label_eq_bot_or_top P C fun j hj ↦ Or.inr (hd j hj)

/-! ### The stages `ω` and `0` -/

/-- **The gated pinned extension property fails at the stage `ω`.** -/
example : ¬ HasGatedPinnedExtensions.{u} Ordinal.omega0 :=
  GatedExtensionCounterexample.not_hasGatedPinnedExtensions _

/-- **The gated pinned extension property fails at the stage `0`.** -/
example : ¬ HasGatedPinnedExtensions.{u} 0 :=
  GatedExtensionCounterexample.not_hasGatedPinnedExtensions _

/-! ### The refuting private type -/

/-- **The refuting private type** is legal and has two distinct cells of graded index
`(univ, 2)`, both labelled `⊤`. -/
example : (GatedExtensionCounterexample.P α).IsLegal ∧
    ∃ C₁ C₂ : Fin (GatedExtensionCounterexample.P α).card, C₁ ≠ C₂ ∧
      (GatedExtensionCounterexample.P α).toCellScheme.gradedIndex C₁ = (univ, 2) ∧
      (GatedExtensionCounterexample.P α).toCellScheme.gradedIndex C₂ = (univ, 2) ∧
      (GatedExtensionCounterexample.P α).label C₁ = ⊤ ∧
      (GatedExtensionCounterexample.P α).label C₂ = ⊤ :=
  ⟨GatedExtensionCounterexample.isLegal_P α, (3 : Fin 5), (4 : Fin 5),
    (by decide : (3 : Fin 5) ≠ 4), rfl, rfl, rfl, rfl⟩

/-- **The refuting private type has no gated extension over the empty root**, whatever the
donor. -/
example (f : Fin 0 ↪ Fin 2) (d : StageType.{u} α 1) :
    IsEmpty (GatedExtension (GatedExtensionCounterexample.P α) f d) :=
  GatedExtensionCounterexample.isEmpty_gatedExtension f d

/-! ### The inhabited gated extension -/

/-- **A gated extension with the cap labelled `⊤`**, at every stage: the input satisfies every
hypothesis of the gated pinned extension property, and the gate has no twins. -/
example : ∃ (P : StageType.{u} α 2) (p : StageType.{u} α 0) (d : StageType.{u} α 1)
    (C : Fin P.card), P.IsLegal ∧ restrictFace emptyRoot P = some p ∧ d.IsLegal ∧
      restrictFace Fin.castSuccEmb d = some p ∧ P.toCellScheme.gradedIndex C = (univ, 2) ∧
      P.label C ≠ ⊥ ∧ P.IsAnchored C d ∧
      ∃ E : GatedExtension P emptyRoot d, E.display.label E.cap = P.label C ∧
        ∀ t, E.display.toCellScheme.gradedIndex t = (univ, 2) → t = E.gate :=
  GatedExtension.instance_two_zero (isSelfVisible_top 2) atStage_top top_ne_bot

end VaughtConjecture.StageType
