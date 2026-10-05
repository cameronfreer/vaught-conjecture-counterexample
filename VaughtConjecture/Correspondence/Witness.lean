/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Cardinal.Aleph
import VaughtConjecture.Correspondence.Visibility
import VaughtConjecture.Label.Transform

/-!
# Correspondence: witnesses and the transformation relation

Roadmap, "Manuscript concordance", row 3.  The printed definition of the relation `p ⇒ q`
[Kni26, Definition 2.3.9] is compared clause by clause with `Label.IsWitness` and
`Label.TransformsTo`.

The printed labels are `{-∞} ∪ ω₁ ∪ {∞}`: in the vocabulary of `VaughtConjecture.Label.Basic`,
the labels at stage `ω₁`.  The printed definition is stated here at an arbitrary stage `α`
(`Label.PrintedWitness α g σ`, `Label.PrintedTransformsTo α a p q`), and [Kni26] is the case
`α = ω₁`.  A printed witness is a pair `(g, σ)` with `g : ω → {-∞} ∪ α ∪ {∞}` and
`σ : {-∞} ∪ α ∪ {∞} → {-∞} ∪ α ∪ {∞}`; here `σ` is a map of all labels, of which only the values
at the labels at stage `α` matter, and the typing of `g` and `σ` is recorded by two fields.

| Printed clause | Field of `PrintedWitness` | Law of `IsWitness` |
| --- | --- | --- |
| `g : ω → {-∞} ∪ α ∪ {∞}` | `suppressor_atStage` | none (labels are not bounded here) |
| `σ` maps `{-∞} ∪ α ∪ {∞}` to itself | `shifter_atStage` | none |
| `q(d) = min (σ (p d), g (a d))` | the equation of `PrintedTransformsTo` | that of `TransformsTo` |
| 1. `n < m → g m ≤ g n` | `antitone` | `antitone` |
| 2. `g n = g n ⌊+⌋_n n` | `visibility` | `isSelfVisible` |
| 3. `σ (-∞) = -∞` | `map_bot` | `map_bot` |
| 4. `α ≤ β → σ α ≤ σ β` | `monotone` | `monotone` |
| 5. `σ α ≤ g k`, `i ≤ k` give `σ (α ⌊+⌋_k i) = σ α ⌊+⌋_k i` | `comm` | `visibilityReplace_comm` |

The identification is `Label.printedTransformsTo_iff`: at a stage `α` that is zero or a limit, for
labellings `p` and `q` with values at stage `α`, `p ⇒ q` as printed exactly when
`TransformsTo a p q`; at `ω₁` this is `Label.printedTransformsTo_omega_one_iff`.

**Departures**, each proved harmless:
1. *Strict and non-strict antitonicity* (clause 1): Mathlib's `antitone_iff_forall_lt`.
2. *The orientation of clause 2*: `IsSelfVisible n x` is `visibilityReplace n n x = x`; the
   printed clause is its symmetric form (`eq_comm`).  Visibility replacement is the printed
   operation by `Label.printedVisibilityReplace_iff` (row 2).
3. *The range of the labels*: the laws of `IsWitness` quantify over all labels, the printed
   clauses 4 and 5 over the labels at stage `α`, and the printed `g` and `σ` take values there.
   A printed witness gives a witness with the shifter `σ ∘ Label.reduce α`
   (`Label.PrintedWitness.isWitness_comp_reduce`), and a witness gives a printed witness by stage
   reduction of both maps (`Label.IsWitness.printedWitness_reduce`); both use that stage reduction
   to a stage that is zero or a limit commutes with visibility replacement.
4. *Finiteness of the domain*: the printed `D` is finite; no clause uses it, and the relation is
   stated here for any type of cells.

The clauses use visibility replacement (row 2, Definition 2.2.3) and the order of the labels
(Definition 2.2.1, `Label.printed_order_add`).  The relation is not transitive
(`Label.TransformsTo.not_transitive`), contrary to [Kni26, Lemma 2.3.14]: that is a statement
about the relation, and the definition is unaffected.

## Placement

The concordance and its notes are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".
-/

universe u

namespace VaughtConjecture.Label

open Ordinal

variable {D : Type*} {α : Ordinal.{u}} {a : D → ℕ} {p q : D → Label.{u}}
  {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}

/-- **The clauses of a printed witness** [Kni26, Definition 2.3.9] at stage `α`: a suppressor `g`
and a shifter `σ` with values among the labels at stage `α`, subject to clauses 1–5.  [Kni26]
takes `α = ω₁`. -/
structure PrintedWitness (α : Ordinal.{u}) (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}) :
    Prop where
  /-- The typing of `g` in [Kni26, Definition 2.3.9]: `g : ω → {-∞} ∪ α ∪ {∞}`. -/
  suppressor_atStage : ∀ n, AtStage α (g n)
  /-- The typing of `σ` in [Kni26, Definition 2.3.9]: `σ` maps `{-∞} ∪ α ∪ {∞}` to itself. -/
  shifter_atStage : ∀ x, AtStage α x → AtStage α (σ x)
  /-- Clause 1 of [Kni26, Definition 2.3.9]: if `n < m`, then `g m ≤ g n`. -/
  antitone : ∀ n m : ℕ, n < m → g m ≤ g n
  /-- Clause 2 of [Kni26, Definition 2.3.9]: `g n = g n ⌊+⌋_n n`. -/
  visibility : ∀ n, g n = visibilityReplace n n (g n)
  /-- Clause 3 of [Kni26, Definition 2.3.9]: `σ (-∞) = -∞`. -/
  map_bot : σ ⊥ = ⊥
  /-- Clause 4 of [Kni26, Definition 2.3.9]: `σ` is monotone on the labels at stage `α`. -/
  monotone : ∀ x y, AtStage α x → AtStage α y → x ≤ y → σ x ≤ σ y
  /-- Clause 5 of [Kni26, Definition 2.3.9]: for a label `x` at stage `α` and `k` with
  `σ x ≤ g k`, `σ (x ⌊+⌋_k i) = σ x ⌊+⌋_k i` for every `i ≤ k`. -/
  comm : ∀ x, AtStage α x → ∀ k, σ x ≤ g k → ∀ i ≤ k,
    σ (visibilityReplace k i x) = visibilityReplace k i (σ x)

/-- **The printed transformation relation** [Kni26, Definition 2.3.9] at stage `α`, over the
arities `a`: some printed witness `(g, σ)` has `q d = min (σ (p d)) (g (a d))` for every `d`. -/
def PrintedTransformsTo (α : Ordinal.{u}) (a : D → ℕ) (p q : D → Label.{u}) : Prop :=
  ∃ g σ, PrintedWitness α g σ ∧ ∀ d, q d = min (σ (p d)) (g (a d))

/-- The minimum of two labels at a stage is at that stage. -/
theorem AtStage.min {x y : Label.{u}} (hx : AtStage α x) (hy : AtStage α y) :
    AtStage α (min x y) := by
  rcases min_choice x y with h | h <;> rwa [h]

/-- **A printed witness is a witness after stage reduction of the argument**: at a stage `α` that
is zero or a limit, the clauses of [Kni26, Definition 2.3.9] for `(g, σ)` give the laws of
`IsWitness` for `(g, σ ∘ Label.reduce α)`. -/
theorem PrintedWitness.isWitness_comp_reduce (hα : Order.IsSuccPrelimit α)
    (h : PrintedWitness α g σ) : IsWitness g (σ ∘ Label.reduce α) where
  antitone := antitone_iff_forall_lt.mpr fun n m hnm ↦ h.antitone n m hnm
  isSelfVisible n := (h.visibility n).symm
  map_bot := by simp [h.map_bot]
  monotone x y hxy := h.monotone _ _ (atStage_reduce α x) (atStage_reduce α y)
    (monotone_reduce α hxy)
  visibilityReplace_comm x k hx i hi := by
    simp only [Function.comp_apply] at hx ⊢
    rw [reduce_visibilityReplace hα, h.comm _ (atStage_reduce α x) k hx i hi]

/-- **A witness gives a printed witness by stage reduction**: at a stage `α` that is zero or a
limit, the stage reductions of the suppressor and the shifter of a witness satisfy the clauses of
[Kni26, Definition 2.3.9] at stage `α`. -/
theorem IsWitness.printedWitness_reduce (hα : Order.IsSuccPrelimit α) (hw : IsWitness g σ) :
    PrintedWitness α (Label.reduce α ∘ g) (Label.reduce α ∘ σ) :=
  have hr := hw.reduce hα
  { suppressor_atStage := fun n ↦ atStage_reduce α (g n)
    shifter_atStage := fun x _ ↦ atStage_reduce α (σ x)
    antitone := fun _ _ hnm ↦ hr.antitone hnm.le
    visibility := fun n ↦ (hr.isSelfVisible n).symm
    map_bot := hr.map_bot
    monotone := fun _ _ _ _ hxy ↦ hr.monotone hxy
    comm := fun x _ k hx i hi ↦ hr.visibilityReplace_comm x k hx i hi }

/-- **The transformation relation is the printed one** [Kni26, Definition 2.3.9]: at a stage `α`
that is zero or a limit, for labellings `p` and `q` with values at stage `α`, `p` transforms to
`q` as printed exactly when `TransformsTo a p q`. -/
theorem printedTransformsTo_iff (hα : Order.IsSuccPrelimit α) (hp : ∀ d, AtStage α (p d))
    (hq : ∀ d, AtStage α (q d)) : PrintedTransformsTo α a p q ↔ TransformsTo a p q := by
  refine ⟨fun ⟨g, σ, hw, heq⟩ ↦
    ⟨g, σ ∘ Label.reduce α, hw.isWitness_comp_reduce hα, fun d ↦ ?_⟩,
    fun ⟨g, σ, hw, heq⟩ ↦ ⟨_, _, hw.printedWitness_reduce hα, fun d ↦ ?_⟩⟩
  · rw [heq, Function.comp_apply, (hp d).reduce_eq]
  · rw [← (hq d).reduce_eq, heq, (monotone_reduce α).map_min]
    rfl

/-- **The transformation relation of [Kni26, Definition 2.3.9]**, on the printed labels
`{-∞} ∪ ω₁ ∪ {∞}`: for labellings with values at stage `ω₁`, `p ⇒ q` as printed exactly when
`TransformsTo a p q`. -/
theorem printedTransformsTo_omega_one_iff (hp : ∀ d, AtStage ω₁ (p d))
    (hq : ∀ d, AtStage ω₁ (q d)) : PrintedTransformsTo ω₁ a p q ↔ TransformsTo a p q :=
  printedTransformsTo_iff (Cardinal.isSuccLimit_omega 1).isSuccPrelimit hp hq

end VaughtConjecture.Label
