/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Amalgamation

/-!
# Examples: amalgamation and joint embedding of top-free charts, and their special cases

Roadmap, the section "The top-free witnesses: the finite age and its classical limit", step 2
(amalgamation and joint embedding), with its special cases.

* **Capping.**  A stage type whose labels are at most the cap is its own capped stage type; a cell
  labelled `⊤` carries the cap after capping; the one-point chart is unchanged by every cap.
* **The cap needs a nonzero stage.**  At stage `0` there is no ordinal below the stage to serve as a
  cap.
* **The empty chart.**  The embedding of the empty chart into a top-free chart is unique, so the
  square over the empty chart commutes for any two embeddings.
* **Two one-point charts over the empty chart.**  Their amalgam over the empty chart, which is their
  joint embedding, is a top-free chart with at least one point.
* **The base stage `ω`.**  At `ω` the hypotheses on the stage hold, and the coatom extension
  property alone makes the age a Fraïssé class with a Fraïssé limit; the countability of the
  function symbols is an instance there.
-/

universe u

namespace VaughtConjecture

open FirstOrder Language Structure Finset Label CategoryTheory
open scoped Ordinal

variable {α : Ordinal.{u}}

/-! ### Capping -/

/-- A stage type whose labels are at most the cap is its own capped stage type. -/
private example {n : ℕ} (t : StageType.{u} α n) {c : Ordinal.{u}}
    (hc : IsSelfVisible n (c : Label)) (hcα : c < α) (htc : ∀ d, t.label d ≤ c) :
    t.cap c hc hcα = t :=
  Option.some_injective _ ((StageType.restrictFace_refl _).symm.trans
    (StageType.restrictFace_cap (StageType.restrictFace_refl t) htc))

/-- A cell labelled `⊤` carries the cap after capping. -/
private example {n : ℕ} (t : StageType.{u} α n) {c : Ordinal.{u}}
    (hc : IsSelfVisible n (c : Label)) (hcα : c < α) (d : Fin t.card) (hd : t.label d = ⊤) :
    (t.cap c hc hcα).label d = c := by
  change min (t.label d) c = c
  rw [hd, min_eq_right le_top]

/-- The one-point chart is unchanged by every cap: its label is `⊥`. -/
private example {c : Ordinal.{u}} (hc : IsSelfVisible 1 (c : Label)) (hcα : c < α) :
    StageType.restrictFace (Function.Embedding.refl (Fin 1))
      ((TopFreeIndex.point α).2.1.cap c hc hcα) = some (TopFreeIndex.point α).2.1 :=
  StageType.restrictFace_cap (StageType.restrictFace_refl _) fun _ ↦ bot_le

/-- At stage `0` there is no cap: no ordinal is below the stage. -/
private example (c : Ordinal.{u}) : ¬ c < 0 :=
  not_lt.mpr zero_le

/-! ### The empty chart -/

/-- The embedding of the empty chart into a top-free chart is unique, so the square over the empty
chart commutes for any two embeddings. -/
private example (i j : TopFreeIndex.{u} α)
    (f g : topFreeChart α (TopFreeIndex.empty α) ↪[hullLanguage.{u} α] topFreeChart α j) :
    f = g ∧ Nonempty (topFreeChart α (TopFreeIndex.empty α) ↪[hullLanguage.{u} α]
      topFreeChart α i) :=
  ⟨Embedding.ext fun x ↦ Fin.elim0 x,
    ⟨StageType.chartEmbedding (i.restrictFace_empty Function.Embedding.ofIsEmpty)⟩⟩

/-! ### Two one-point charts over the empty chart -/

/-- The embedding of the empty chart into the one-point chart. -/
private noncomputable def emptyPoint :
    topFreeChart α (TopFreeIndex.empty α) ↪[hullLanguage.{u} α]
      topFreeChart α (TopFreeIndex.point α) :=
  StageType.chartEmbedding ((TopFreeIndex.point α).restrictFace_empty Function.Embedding.ofIsEmpty)

/-- **Amalgamation over the empty chart of two one-point charts**: under the coatom extension
property, the two copies of the one-point chart are amalgamated over the empty chart, in a top-free
chart with at least one point. -/
private example (hext : StageType.HasCoatomExtensions.{u} α) (hα : Order.IsSuccPrelimit α)
    (h0 : 0 < α) :
    ∃ (l : TopFreeIndex.{u} α)
      (a b : topFreeChart α (TopFreeIndex.point α) ↪[hullLanguage.{u} α] topFreeChart α l),
        a.comp emptyPoint = b.comp emptyPoint ∧ 1 ≤ l.1 := by
  obtain ⟨l, a, b, hab⟩ := exists_amalgam_topFreeChart hext hα h0 _ _ _ emptyPoint emptyPoint
  refine ⟨l, a, b, hab, ?_⟩
  let e : Fin 1 ↪ Fin l.1 := ⟨fun x ↦ a x, a.injective⟩
  simpa using Fintype.card_le_of_embedding e

/-- **Joint embedding of the one-point chart with itself**, under the coatom extension property. -/
private example (hext : StageType.HasCoatomExtensions.{u} α) (hα : Order.IsSuccPrelimit α)
    (h0 : 0 < α) :
    ∃ l : TopFreeIndex.{u} α,
      Nonempty (topFreeChart α (TopFreeIndex.point α) ↪[hullLanguage.{u} α] topFreeChart α l) :=
  (exists_jointEmbedding_topFreeChart hext hα h0 _ (TopFreeIndex.point α)).imp fun _ h ↦ h.1

/-! ### The base stage -/

/-- At `ω` the hypotheses on the stage hold: it is a nonzero limit with countably many ordinals
below it. -/
private example : Order.IsSuccPrelimit ω ∧ 0 < ω ∧ (Set.Iio (ω : Ordinal.{u})).Countable :=
  ⟨Ordinal.isSuccLimit_omega0.isSuccPrelimit, Ordinal.omega0_pos,
    Set.countable_coe_iff.mp countable_Iio_omega0_coe⟩

/-- At `ω` the coatom extension property alone makes the age of top-free charts a Fraïssé class,
with the amalgamation and joint embedding properties. -/
private example (hext : StageType.HasCoatomExtensions.{u} ω) :
    IsFraisse (topFreeAge.{u} ω) ∧ Amalgamation (topFreeAge.{u} ω) ∧
      JointEmbedding (topFreeAge.{u} ω) :=
  ⟨isFraisse_topFreeAge_omega hext,
    amalgamation_topFreeAge hext Ordinal.isSuccLimit_omega0.isSuccPrelimit Ordinal.omega0_pos,
    jointEmbedding_topFreeAge hext Ordinal.isSuccLimit_omega0.isSuccPrelimit Ordinal.omega0_pos⟩

/-- At `ω` the age of top-free charts has a countable Fraïssé limit, under the coatom extension
property; the countability of the function symbols is an instance. -/
private example (hext : StageType.HasCoatomExtensions.{u} ω) :
    ∃ (M : Bundled.{0} (hullLanguage.{u} ω).Structure) (_ : Countable M),
      IsFraisseLimit (topFreeAge.{u} ω) M :=
  exists_topFreeLimit hext Ordinal.isSuccLimit_omega0.isSuccPrelimit Ordinal.omega0_pos
    (Set.countable_coe_iff.mp countable_Iio_omega0_coe)

end VaughtConjecture
