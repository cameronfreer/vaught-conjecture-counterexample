/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Cardinal.Aleph
import VaughtConjecture.Correspondence.Visibility

/-!
# Correspondence with the legal templates of [AFK26]: visibility maps and self-visibility

Roadmap, "Manuscript concordance", row 41.  [AFK26, Definition 4.24] defines, for `k ∈ ℕ`, the
visibility map `visible<k>[i]` of the labels `{-∞} ∪ ω₁ ∪ {∞}` to themselves, and calls a label
`x` *self-visible at `k`* when `visible<k>[k](x) = x`.  The clauses are compared with
`Label.visibilityReplace` and `Label.IsSelfVisible`.

The printed labels are those at stage `ω₁`.  The clauses are stated here at a stage `θ`, for the
ordinals `ω · α + n < θ` (`Label.PrintedVisibilityMap θ k i f`); at `ω₁` these are the pairs
`(α, n)` with `α < ω₁` and `n ∈ ℕ`, as printed (`Label.omega0_mul_add_natCast_lt_omega_one_iff`).
Here `ω · α` is Mathlib's ordinal product `ω * α`, the sum of `α` copies of `ω`.

| Printed clause | `PrintedVisibilityMap` | `CorrectedVisibilityMap` |
| --- | --- | --- |
| 1. `visible<k>[i](-∞) = -∞`, `visible<k>[i](∞) = ∞` | `bot`, `top` | `bot`, `top` |
| 2. `ω · α + n ↦ i` if `n < k`, `n` otherwise | `ordinal` | `ordinal`: `ω · α + i`, `ω · α + n` |

**Correction** (status C).  As printed, clause 2 sends the ordinal `ω · α + n` to the natural
number `i` or `n`, forgetting its block `[ω · α, ω · α + ω)`.  Read literally, the image of every
ordinal is a natural number (`Label.PrintedVisibilityMap.apply_coe_lt_omega0`), no ordinal `≥ ω`
is self-visible at any threshold (`Label.PrintedVisibilityMap.apply_ne_self`), and the map is not
visibility replacement (`Label.PrintedVisibilityMap.ne_visibilityReplace`).  Every label `ω · n + i`
of the range clause of [AFK26, Definition 4.27] with `n ≥ 1` would then fail the orderliness clause
of [AFK26, Definition 4.26].  The corrected clause keeps the block: `ω · α + n` is sent to
`ω · α + i` if `n < k`, and kept otherwise, which is the operation of
[Kni26, Definition 2.2.3] (row 2).

**The corrected clauses.**  `Label.correctedVisibilityMap_iff`: a map satisfies the corrected
clauses at stage `θ` exactly when it agrees with `Label.visibilityReplace k i` on the labels at
stage `θ`; at `ω₁` this is `Label.correctedVisibilityMap_omega_one_iff`.  Self-visibility in the
sense of Definition 4.24 is then `Label.IsSelfVisible`
(`Label.CorrectedVisibilityMap.apply_eq_self_iff`).

**The two printed definitions.**  [Kni26, Definition 2.2.3] (`Label.PrintedVisibilityReplace`)
decomposes an ordinal as `μ + j` with `μ` zero or a limit, and is stated for all ordinals; the
corrected clause of [AFK26] decomposes it as `ω · α + n`, at a stage.  A map satisfies the clauses
of [Kni26] exactly when it satisfies the corrected clauses of [AFK26] at every stage
(`Label.printedVisibilityReplace_iff_forall_correctedVisibilityMap`).  [Kni26] takes values
`m ≤ K` and [AFK26] every value `i`; the identifications hold for every value.

## Placement

The concordance and its notes are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".
-/

universe u

namespace VaughtConjecture.Label

open Ordinal

variable {θ : Ordinal.{u}} {k i : ℕ} {f : Label.{u} → Label.{u}} {x : Label.{u}}

/-- The ordinals `ω · α + n` below `ω₁` are those with `α < ω₁`: at `ω₁` the clauses below range
over the pairs `α ∈ ω₁`, `n ∈ ℕ` of [AFK26, Definition 4.24]. -/
theorem omega0_mul_add_natCast_lt_omega_one_iff (α : Ordinal.{u}) (n : ℕ) :
    ω * α + n < ω₁ ↔ α < ω₁ := by
  have key (o : Ordinal.{u}) : o < ω₁ ↔ o.card ≤ Cardinal.aleph0 := by
    rw [← Cardinal.ord_aleph, Cardinal.lt_ord]
    exact Cardinal.lt_aleph_one_iff
  refine ⟨fun h ↦ ((le_mul_right α omega0_pos).trans le_self_add).trans_lt h, fun h ↦ ?_⟩
  rw [key] at h ⊢
  simp only [card_add, card_mul, card_omega0, card_nat]
  calc Cardinal.aleph0 * α.card + n ≤ Cardinal.aleph0 * Cardinal.aleph0 + Cardinal.aleph0 := by
        gcongr
        exact Cardinal.natCast_le_aleph0
    _ = Cardinal.aleph0 := by rw [Cardinal.aleph0_mul_aleph0, Cardinal.aleph0_add_aleph0]

/-- Every ordinal is `ω · α + n` with `n` finite. -/
theorem exists_eq_omega0_mul_add_natCast (o : Ordinal.{u}) :
    ∃ (α : Ordinal.{u}) (n : ℕ), o = ω * α + n := by
  obtain ⟨n, hn⟩ := lt_omega0.mp (mod_lt o omega0_ne_zero)
  exact ⟨o / ω, n, by rw [← hn, div_add_mod]⟩

/-- Visibility replacement in the form `ω · α + n`: replacement at threshold `k` with value `i`
sends `ω · α + n` to `ω · α + i` if `n < k`, and fixes it otherwise. -/
theorem visibilityReplace_omega0_mul_add (k i : ℕ) (α : Ordinal.{u}) (n : ℕ) :
    visibilityReplace k i ((ω * α + n : Ordinal.{u}) : Label.{u}) =
      if n < k then ((ω * α + i : Ordinal.{u}) : Label.{u})
      else ((ω * α + n : Ordinal.{u}) : Label.{u}) :=
  visibilityReplace_coe_add (isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _)) k i n

/-! ### The printed clauses -/

/-- **The clauses of [AFK26, Definition 4.24] as printed**, for a map `f` of labels at threshold
`k` with value `i`, on the labels at stage `θ` ([AFK26] takes `θ = ω₁`).  Clause 2 sends
`ω · α + n` to a natural number; the corrected clauses are `CorrectedVisibilityMap`. -/
structure PrintedVisibilityMap (θ : Ordinal.{u}) (k i : ℕ) (f : Label.{u} → Label.{u}) :
    Prop where
  /-- Clause 1 of [AFK26, Definition 4.24]: `visible<k>[i](-∞) = -∞`. -/
  bot : f ⊥ = ⊥
  /-- Clause 1 of [AFK26, Definition 4.24]: `visible<k>[i](∞) = ∞`. -/
  top : f ⊤ = ⊤
  /-- Clause 2 of [AFK26, Definition 4.24], as printed: for `ω · α + n` at stage `θ`,
  `visible<k>[i](ω · α + n)` is `i` if `n < k`, and `n` otherwise. -/
  ordinal : ∀ (α : Ordinal.{u}) (n : ℕ), ω * α + n < θ →
    f ((ω * α + n : Ordinal.{u}) : Label.{u}) = if n < k then (i : Label.{u}) else (n : Label.{u})

/-- **The corrected clauses of [AFK26, Definition 4.24]**, for a map `f` of labels at threshold
`k` with value `i`, on the labels at stage `θ`: clause 2 keeps the block
`[ω · α, ω · α + ω)`. -/
structure CorrectedVisibilityMap (θ : Ordinal.{u}) (k i : ℕ) (f : Label.{u} → Label.{u}) :
    Prop where
  /-- Clause 1 of [AFK26, Definition 4.24]: `visible<k>[i](-∞) = -∞`. -/
  bot : f ⊥ = ⊥
  /-- Clause 1 of [AFK26, Definition 4.24]: `visible<k>[i](∞) = ∞`. -/
  top : f ⊤ = ⊤
  /-- Clause 2 of [AFK26, Definition 4.24], corrected: for `ω · α + n` at stage `θ`,
  `visible<k>[i](ω · α + n)` is `ω · α + i` if `n < k`, and `ω · α + n` otherwise. -/
  ordinal : ∀ (α : Ordinal.{u}) (n : ℕ), ω * α + n < θ →
    f ((ω * α + n : Ordinal.{u}) : Label.{u}) =
      if n < k then ((ω * α + i : Ordinal.{u}) : Label.{u})
      else ((ω * α + n : Ordinal.{u}) : Label.{u})

/-! ### The printed clause forgets the block -/

/-- **Under the printed clauses, every ordinal goes to a natural number**: the image of an
ordinal at stage `θ` is below `ω`. -/
theorem PrintedVisibilityMap.apply_coe_lt_omega0 (hf : PrintedVisibilityMap θ k i f)
    {o : Ordinal.{u}} (ho : o < θ) : f o < ((ω : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨α, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
  have hlt (m : ℕ) : (m : Label.{u}) < ((ω : Ordinal.{u}) : Label.{u}) := by
    rw [← WithBot.coe_natCast, ← WithTop.coe_natCast]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (natCast_lt_omega0 m))
  rw [hf.ordinal α n ho]
  split_ifs
  · exact hlt i
  · exact hlt n

/-- **Under the printed clauses, no ordinal `≥ ω` is self-visible**: a map satisfying the printed
clauses at threshold `k` with value `k` fixes no ordinal `o` with `ω ≤ o < θ`. -/
theorem PrintedVisibilityMap.apply_ne_self (hf : PrintedVisibilityMap θ k k f) {o : Ordinal.{u}}
    (hωo : ω ≤ o) (ho : o < θ) : f o ≠ o := fun h ↦ by
  have := hf.apply_coe_lt_omega0 ho
  rw [h] at this
  exact (not_lt.mpr hωo) (WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp this))

/-- **The printed map is not visibility replacement**: at an ordinal `o` with `ω ≤ o < θ`, a map
satisfying the printed clauses differs from `Label.visibilityReplace k i`. -/
theorem PrintedVisibilityMap.apply_ne_visibilityReplace (hf : PrintedVisibilityMap θ k i f)
    {o : Ordinal.{u}} (hωo : ω ≤ o) (ho : o < θ) : f o ≠ visibilityReplace k i o := fun h ↦ by
  have := hf.apply_coe_lt_omega0 ho
  rw [h, visibilityReplace_lt_iff isSuccLimit_omega0.isSuccPrelimit] at this
  exact (not_lt.mpr hωo) (WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp this))

/-- **The printed clauses do not define visibility replacement**: at a stage above `ω`, no map
satisfying the printed clauses of [AFK26, Definition 4.24] is `Label.visibilityReplace k i`. -/
theorem PrintedVisibilityMap.ne_visibilityReplace (hf : PrintedVisibilityMap θ k i f)
    (hθ : ω < θ) : f ≠ visibilityReplace k i := fun h ↦
  hf.apply_ne_visibilityReplace le_rfl hθ (congrFun h _)

/-! ### The corrected clauses -/

/-- **The corrected visibility map is visibility replacement** [AFK26, Definition 4.24]: a map
satisfies the corrected clauses at stage `θ` exactly when it agrees with
`Label.visibilityReplace k i` on the labels at stage `θ`. -/
theorem correctedVisibilityMap_iff :
    CorrectedVisibilityMap θ k i f ↔ ∀ x, AtStage θ x → f x = visibilityReplace k i x := by
  refine ⟨fun hf x hx ↦ ?_, fun h ↦ ⟨by simpa using h ⊥ atStage_bot,
    by simpa using h ⊤ atStage_top, fun α n hαn ↦ by
      rw [h _ (atStage_coe.mpr hαn), visibilityReplace_omega0_mul_add]⟩⟩
  induction x using recBotCoeTop with
  | bot => rw [hf.bot, visibilityReplace_bot]
  | top => rw [hf.top, visibilityReplace_top]
  | coe o =>
    obtain ⟨α, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
    rw [hf.ordinal α n (atStage_coe.mp hx), visibilityReplace_omega0_mul_add]

/-- Visibility replacement satisfies the corrected clauses of [AFK26, Definition 4.24] at every
stage. -/
theorem correctedVisibilityMap_visibilityReplace (θ : Ordinal.{u}) (k i : ℕ) :
    CorrectedVisibilityMap θ k i (visibilityReplace.{u} k i) :=
  correctedVisibilityMap_iff.mpr fun _ _ ↦ rfl

/-- **The corrected visibility map of [AFK26, Definition 4.24]** on the printed labels
`{-∞} ∪ ω₁ ∪ {∞}`: a map satisfies the corrected clauses at `ω₁` exactly when it agrees with
`Label.visibilityReplace k i` there. -/
theorem correctedVisibilityMap_omega_one_iff :
    CorrectedVisibilityMap ω₁ k i f ↔ ∀ x, AtStage ω₁ x → f x = visibilityReplace k i x :=
  correctedVisibilityMap_iff

/-- **Self-visibility** [AFK26, Definition 4.24]: for a map satisfying the corrected clauses at
threshold `k` with value `k`, a label `x` at stage `θ` has `visible<k>[k](x) = x` exactly when it
is self-visible at `k`. -/
theorem CorrectedVisibilityMap.apply_eq_self_iff (hf : CorrectedVisibilityMap θ k k f)
    (hx : AtStage θ x) : f x = x ↔ IsSelfVisible k x := by
  rw [correctedVisibilityMap_iff.mp hf x hx]
  rfl

/-- **The two printed definitions of visibility replacement**: a map satisfies the clauses of
[Kni26, Definition 2.2.3] exactly when it satisfies the corrected clauses of
[AFK26, Definition 4.24] at every stage. -/
theorem printedVisibilityReplace_iff_forall_correctedVisibilityMap :
    PrintedVisibilityReplace k i f ↔ ∀ θ : Ordinal.{u}, CorrectedVisibilityMap θ k i f := by
  rw [printedVisibilityReplace_iff]
  refine ⟨fun h θ ↦ h ▸ correctedVisibilityMap_visibilityReplace θ k i, fun h ↦ funext fun x ↦ ?_⟩
  obtain ⟨θ, -, hθ⟩ := exists_isSuccPrelimit_forall_atStage (Set.finite_singleton x)
  exact correctedVisibilityMap_iff.mp (h θ) x (hθ x rfl)

end VaughtConjecture.Label
