/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Visibility

/-!
# Correspondence: labels and visibility replacement

Roadmap, "Manuscript concordance", row 2.  The printed definitions of the labels
[Kni26, Definition 2.2.1] and of visibility replacement [Kni26, Definition 2.2.3] are compared
clause by clause with `VaughtConjecture.Label` and `Label.visibilityReplace`.

## The labels, [Kni26, Definition 2.2.1]

| Printed clause | Here |
| --- | --- |
| `-∞ < α < ∞` for every ordinal `α` | `⊥ < (o : Label)` and `(o : Label) < ⊤` |
| the ordinals keep their order | `(a : Label) ≤ b ↔ a ≤ b` |
| `-∞ + α = -∞` | `⊥ + (o : Label) = ⊥` |
| `α + ∞ = ∞ + α = ∞ + ∞ = ∞` | the same three equations in `Label` |

All of them are the single theorem `Label.printed_order_add` about Mathlib's order and addition on
`WithBot (WithTop Ordinal)`.  The printed text leaves `∞ + -∞` and `-∞ + ∞` undefined; Mathlib's
addition gives both the value `⊥`, and nothing here uses them.

## Visibility replacement, [Kni26, Definition 2.2.3]

The printed operation `α ⌊+⌋_K m` is a map of labels for each threshold `K` and value `m ≤ K`.
`Label.PrintedVisibilityReplace K m f` states that a map `f` of labels satisfies the three printed
clauses, one field each:

| Printed clause | Field | Here |
| --- | --- | --- |
| `μ + j ↦ μ + m` if `j < K`, else kept (`μ` limit or 0) | `ordinal` | `visibilityReplace_coe_add` |
| `-∞ ⌊+⌋_K m = -∞` | `bot` | `visibilityReplace_bot` |
| `∞ ⌊+⌋_K m = ∞` | `top` | `visibilityReplace_top` |

The identification is `Label.printedVisibilityReplace_iff`: a map satisfies the printed clauses
exactly when it is `Label.visibilityReplace K m`.

**Departures.**
1. *Normal form.*  The printed clause decomposes `α = μ + j` with `μ` zero or a limit and `j`
   finite; `Ordinal.visibilityReplace` uses the division `α = ω * (α / ω) + α % ω`.  The two agree
   by `Label.visibilityReplace_coe_add` (the printed clause for `Label.visibilityReplace`), and
   every label is bottom, top, or of the printed form (`Label.printedVisibilityReplace_iff`).
2. *Domain of the value.*  The printed operation is defined for `m ≤ K` only;
   `Label.visibilityReplace K m` is defined for every `m`, and the identification holds for every
   `m`, so on the printed domain the two coincide.  The laws used in this development carry the
   hypothesis `i ≤ k` where they need it (for instance `monotone_visibilityReplace`).

The clauses of Definition 2.2.3 use no notion beyond ordinal addition and the two symbols `-∞`,
`∞`.  [Kni26, Definition 2.2.2] (the operation `α ⌊+⌋ m` without a threshold) is motivation only;
Definition 2.2.3 restates the decomposition and does not refer to it.

## Placement

The concordance and its notes are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".
-/

universe u

namespace VaughtConjecture.Label

open Ordinal

/-! ### The labels -/

/-- **The labels of [Kni26, Definition 2.2.1]**: bottom lies below every ordinal and every ordinal
below the formal top, the ordinals keep their order, and Mathlib's addition of labels satisfies
the printed equations `-∞ + α = -∞` and `α + ∞ = ∞ + α = ∞ + ∞ = ∞`. -/
theorem printed_order_add :
    (∀ o : Ordinal.{u}, (⊥ : Label.{u}) < o ∧ (o : Label.{u}) < ⊤) ∧
      (∀ a b : Ordinal.{u}, (a : Label.{u}) ≤ b ↔ a ≤ b) ∧
      (∀ o : Ordinal.{u}, (⊥ : Label.{u}) + o = ⊥) ∧
      (∀ o : Ordinal.{u}, (o : Label.{u}) + ⊤ = ⊤ ∧ (⊤ : Label.{u}) + o = ⊤) ∧
      (⊤ : Label.{u}) + ⊤ = ⊤ := by
  refine ⟨fun o ↦ ⟨WithBot.bot_lt_coe _, WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top o)⟩,
    fun a b ↦ by simp, fun o ↦ WithBot.bot_add _, fun o ↦ ⟨?_, ?_⟩, ?_⟩
  · exact congrArg WithBot.some (WithTop.add_top _)
  · exact congrArg WithBot.some (WithTop.top_add _)
  · exact congrArg WithBot.some (WithTop.top_add _)

/-! ### Visibility replacement -/

/-- **The clauses of [Kni26, Definition 2.2.3]** for a map `f` of labels, at threshold `K` with
value `m`: `f` is the printed operation `x ↦ x ⌊+⌋_K m`.  The printed definition takes `m ≤ K`;
the clauses make sense for every `m`. -/
structure PrintedVisibilityReplace (K m : ℕ) (f : Label.{u} → Label.{u}) : Prop where
  /-- First clause of [Kni26, Definition 2.2.3]: for `α = μ + j` with `μ` zero or a limit and `j`
  finite, `α ⌊+⌋_K m` is `μ + m` if `j < K`, and `α` otherwise. -/
  ordinal : ∀ μ : Ordinal.{u}, Order.IsSuccPrelimit μ → ∀ j : ℕ,
    f ((μ + j : Ordinal.{u}) : Label.{u}) =
      if j < K then ((μ + m : Ordinal.{u}) : Label.{u}) else ((μ + j : Ordinal.{u}) : Label.{u})
  /-- Second clause of [Kni26, Definition 2.2.3]: `-∞ ⌊+⌋_K m = -∞`. -/
  bot : f ⊥ = ⊥
  /-- Third clause of [Kni26, Definition 2.2.3]: `∞ ⌊+⌋_K m = ∞`. -/
  top : f ⊤ = ⊤

/-- **The printed normal form for visibility replacement**: for `μ` zero or a limit and `j`
finite, replacement at threshold `K` with value `m` sends `μ + j` to `μ + m` if `j < K`, and
fixes it otherwise. -/
theorem visibilityReplace_coe_add {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) (K m j : ℕ) :
    visibilityReplace K m ((μ + j : Ordinal.{u}) : Label.{u}) =
      if j < K then ((μ + m : Ordinal.{u}) : Label.{u})
      else ((μ + j : Ordinal.{u}) : Label.{u}) := by
  split_ifs with hj
  · exact visibilityReplace_coe_add_natCast hμ hj m
  · exact (isSelfVisible_coe_add hμ (not_lt.mp hj)).visibilityReplace_eq m

/-- `Label.visibilityReplace K m` satisfies the clauses of [Kni26, Definition 2.2.3]. -/
theorem printedVisibilityReplace_visibilityReplace (K m : ℕ) :
    PrintedVisibilityReplace K m (visibilityReplace.{u} K m) :=
  ⟨fun _ hμ j ↦ visibilityReplace_coe_add hμ K m j, visibilityReplace_bot K m,
    visibilityReplace_top K m⟩

/-- Every ordinal is `μ + j` with `μ` zero or a limit and `j` finite: `μ = ω * (o / ω)` and
`j = o % ω`. -/
theorem exists_eq_add_natCast_isSuccPrelimit (o : Ordinal.{u}) :
    ∃ μ : Ordinal.{u}, Order.IsSuccPrelimit μ ∧ ∃ j : ℕ, o = μ + j := by
  obtain ⟨j, hj⟩ := lt_omega0.mp (mod_lt o omega0_ne_zero)
  exact ⟨ω * (o / ω), isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _), j, by
    rw [← hj, div_add_mod]⟩

/-- **Visibility replacement is the printed operation** [Kni26, Definition 2.2.3]: a map of
labels satisfies the printed clauses at threshold `K` with value `m` exactly when it is
`Label.visibilityReplace K m`.  The printed definition takes `m ≤ K`; the identification holds
for every `m`. -/
theorem printedVisibilityReplace_iff {K m : ℕ} {f : Label.{u} → Label.{u}} :
    PrintedVisibilityReplace K m f ↔ f = visibilityReplace K m := by
  refine ⟨fun hf ↦ funext fun x ↦ ?_, fun h ↦ h ▸ printedVisibilityReplace_visibilityReplace K m⟩
  induction x using recBotCoeTop with
  | bot => rw [hf.bot, visibilityReplace_bot]
  | top => rw [hf.top, visibilityReplace_top]
  | coe o =>
    obtain ⟨μ, hμ, j, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o
    rw [hf.ordinal μ hμ j, visibilityReplace_coe_add hμ]

end VaughtConjecture.Label
