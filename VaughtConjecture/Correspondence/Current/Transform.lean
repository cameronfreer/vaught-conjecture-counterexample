/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Current.Visibility
import VaughtConjecture.Correspondence.Witness

/-!
# Correspondence with the legal templates of [AFK26]: the relation `u ⇒ v`

Roadmap, "Manuscript concordance", row 42.  [AFK26, Definition 4.25] defines, for labellings `u`
and `v` of a frame with cells `D` and grades `g`, the relation `u ⇒ v`: there are `f : ℕ → L` and
`h : L → L`, `L = {-∞} ∪ ω₁ ∪ {∞}` the labels, with

1. `f` antitone, and `f(k)` visible at `k` for every `k`;
2. `h(-∞) = -∞`, and `h(visible<k>[i](x)) = visible<k>[i](h(x))` for all `i ≤ k` and `x` with
   `h(x) ≤ f(k)`;

such that `v(d) = min (h(u(d)), f(g(d)))` for every `d ∈ D`.  It is compared with the relation of
[Kni26, Definition 2.3.9] (`Label.PrintedTransformsTo`, row 3), which is `Label.TransformsTo`.

As in row 3, the printed labels are those at stage `ω₁`; the clauses are stated at a stage `θ`
(`Label.PrintedFrameWitness θ f h`, `Label.PrintedFrameTransformsTo θ g u v`), with the typing of
`f` and `h` as two fields, and `visible<k>[i]` is the corrected visibility map of row 41, that is
`Label.visibilityReplace k i` (`Label.correctedVisibilityMap_iff`).

| Printed clause | Field of `PrintedFrameWitness` | Field of `PrintedWitness` ([Kni26]) |
| --- | --- | --- |
| `f : ℕ → {-∞} ∪ θ ∪ {∞}` | `suppressor_atStage` | `suppressor_atStage` |
| `h` maps `{-∞} ∪ θ ∪ {∞}` to itself | `shifter_atStage` | `shifter_atStage` |
| 1. `f` antitone: `a ≤ b → f(b) ≤ f(a)` | `antitone` | `antitone` (strict form) |
| 1. `f(k)` visible at `k` | `isSelfVisible` | `visibility` |
| 2. `h(-∞) = -∞` | `map_bot` | `map_bot` |
| (none) | (none) | `monotone`: `h` monotone |
| 2. `h(x) ≤ f(k)`, `i ≤ k` give `h(visible<k>[i](x)) = visible<k>[i](h(x))` | `comm` | `comm` |
| `v(d) = min (h(u(d)), f(g(d)))` | the equation of `PrintedFrameTransformsTo` | the same |

**The two printed definitions.**  They differ by the monotonicity of the shifter, clause 4 of
[Kni26, Definition 2.3.9], which [AFK26, Definition 4.25] does not state: a pair is a witness of
[Kni26] exactly when it is a witness of [AFK26] with a shifter monotone on the labels at the stage
(`Label.printedWitness_iff_printedFrameWitness`).  So `p ⇒ q` in the sense of [Kni26] gives `p ⇒ q`
in the sense of [AFK26] (`Label.PrintedTransformsTo.printedFrameTransformsTo`), and so does
`Label.TransformsTo` (`Label.TransformsTo.printedFrameTransformsTo`), but not conversely: on two
cells of grade `1` labelled `1` and `2`, the relation of [AFK26] reaches the labelling `2`, `1`,
which no monotone shifter reaches (`Label.exists_printedFrameTransformsTo_not_transformsTo`, at
`ω₁`).

**Corrections** (status C).
1. *Monotonicity of the shifter*: restored, as in [Kni26, Definition 2.3.9], clause 4.  The
   corrected relation is `Label.PrintedTransformsTo θ` of row 3, which is `Label.TransformsTo` for
   labellings with values at a stage that is zero or a limit (`Label.printedTransformsTo_iff`).
   Without it the relation reaches labellings that reverse the order of the source labels at
   cells of equal grade (above), while the relation of [Kni26] and of this development is
   monotone in the source label (`Label.TransformsTo.le_of_le`).
2. *"Visible at `k`"*: [AFK26] defines only self-visibility at `k` (Definition 4.24, row 41); the
   clause is read as self-visibility, which is clause 2 of [Kni26, Definition 2.3.9].
3. *The visibility map* in clause 2 is the corrected map of row 41.
The printed equation `v(d) = min {h(u(d)), f(g(d))` lacks a closing brace; it is read as the
minimum of the two labels.

## Placement

The concordance and its notes are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".
-/

universe u

namespace VaughtConjecture.Label

open Ordinal

variable {D : Type*} {θ : Ordinal.{u}} {g : D → ℕ} {u v : D → Label.{u}}
  {f : ℕ → Label.{u}} {h : Label.{u} → Label.{u}}

/-- **The clauses of a witness of `u ⇒ v`** in [AFK26, Definition 4.25], at stage `θ`: a
suppressor `f` and a shifter `h` with values among the labels at stage `θ`, subject to the printed
clauses, the visibility map being visibility replacement (the corrected map of
[AFK26, Definition 4.24]).  [AFK26] takes `θ = ω₁`.  It has no monotonicity clause. -/
structure PrintedFrameWitness (θ : Ordinal.{u}) (f : ℕ → Label.{u}) (h : Label.{u} → Label.{u}) :
    Prop where
  /-- The typing of `f` in [AFK26, Definition 4.25]: `f : ℕ → {-∞} ∪ θ ∪ {∞}`. -/
  suppressor_atStage : ∀ n, AtStage θ (f n)
  /-- The typing of `h` in [AFK26, Definition 4.25]: `h` maps `{-∞} ∪ θ ∪ {∞}` to itself. -/
  shifter_atStage : ∀ x, AtStage θ x → AtStage θ (h x)
  /-- First clause of [AFK26, Definition 4.25]: `f` is antitone, `a ≤ b → f(b) ≤ f(a)`. -/
  antitone : ∀ a b : ℕ, a ≤ b → f b ≤ f a
  /-- First clause of [AFK26, Definition 4.25]: `f(k)` is (self-)visible at `k`. -/
  isSelfVisible : ∀ k, IsSelfVisible k (f k)
  /-- Second clause of [AFK26, Definition 4.25]: `h(-∞) = -∞`. -/
  map_bot : h ⊥ = ⊥
  /-- Second clause of [AFK26, Definition 4.25]: for all `i ≤ k` and every label `x` at stage `θ`
  with `h(x) ≤ f(k)`, `h(visible<k>[i](x)) = visible<k>[i](h(x))`. -/
  comm : ∀ i k : ℕ, i ≤ k → ∀ x, AtStage θ x → h x ≤ f k →
    h (visibilityReplace k i x) = visibilityReplace k i (h x)

/-- **The relation `u ⇒ v` of [AFK26, Definition 4.25]** at stage `θ`, for labellings `u`, `v` of
cells with grades `g`: some printed witness `(f, h)` has `v d = min (h (u d)) (f (g d))` for every
cell `d`. -/
def PrintedFrameTransformsTo (θ : Ordinal.{u}) (g : D → ℕ) (u v : D → Label.{u}) : Prop :=
  ∃ f h, PrintedFrameWitness θ f h ∧ ∀ d, v d = min (h (u d)) (f (g d))

/-- **The two printed witnesses**: a pair is a witness of [Kni26, Definition 2.3.9] at stage `θ`
exactly when it is a witness of [AFK26, Definition 4.25] at stage `θ` whose shifter is monotone on
the labels at stage `θ` (clause 4 of [Kni26, Definition 2.3.9]). -/
theorem printedWitness_iff_printedFrameWitness :
    PrintedWitness θ f h ↔
      PrintedFrameWitness θ f h ∧ ∀ x y, AtStage θ x → AtStage θ y → x ≤ y → h x ≤ h y := by
  refine ⟨fun hw ↦ ⟨⟨hw.suppressor_atStage, hw.shifter_atStage,
    fun a b hab ↦ (eq_or_lt_of_le hab).elim (fun e ↦ e ▸ le_rfl) (hw.antitone a b),
    fun k ↦ (hw.visibility k).symm, hw.map_bot,
    fun i k hik x hx hk ↦ hw.comm x hx k hk i hik⟩, hw.monotone⟩,
    fun ⟨hw, hm⟩ ↦ ⟨hw.suppressor_atStage, hw.shifter_atStage,
      fun a b hab ↦ hw.antitone a b hab.le, fun k ↦ (hw.isSelfVisible k).symm, hw.map_bot, hm,
      fun x hx k hk i hik ↦ hw.comm i k hik x hx hk⟩⟩

/-- **The relation of [Kni26] gives that of [AFK26]**: `p ⇒ q` in the sense of
[Kni26, Definition 2.3.9] at stage `θ` gives `p ⇒ q` in the sense of [AFK26, Definition 4.25]. -/
theorem PrintedTransformsTo.printedFrameTransformsTo (hpq : PrintedTransformsTo θ g u v) :
    PrintedFrameTransformsTo θ g u v :=
  let ⟨f, h, hw, heq⟩ := hpq
  ⟨f, h, (printedWitness_iff_printedFrameWitness.mp hw).1, heq⟩

/-- **The transformation relation gives that of [AFK26, Definition 4.25]**: at a stage `θ` that is
zero or a limit, for labellings with values at stage `θ`, `TransformsTo g u v` gives `u ⇒ v` in the
sense of [AFK26]. -/
theorem TransformsTo.printedFrameTransformsTo (hθ : Order.IsSuccPrelimit θ)
    (hu : ∀ d, AtStage θ (u d)) (hv : ∀ d, AtStage θ (v d)) (huv : TransformsTo g u v) :
    PrintedFrameTransformsTo θ g u v :=
  ((printedTransformsTo_iff hθ hu hv).mpr huv).printedFrameTransformsTo

/-! ### The relation of [AFK26] reverses an order -/

/-- The label `2` is below the formal top. -/
private theorem two_lt_top : (2 : Label.{u}) < ⊤ := by
  simpa using (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top (2 : Ordinal.{u})) :
    ((2 : Ordinal.{u}) : Label.{u}) < ⊤)

/-- A label at most `2` other than `0` is self-visible at `1`. -/
private theorem isSelfVisible_one_of_le_two {x : Label.{u}} (hx : x ≤ 2) (h0 : x ≠ 0) :
    IsSelfVisible 1 x := by
  induction x using recBotCoeTop with
  | bot => exact isSelfVisible_bot 1
  | top => exact absurd hx (not_le.mpr two_lt_top)
  | coe o =>
    have h2 : o ≤ 2 := by
      have : (o : Label.{u}) ≤ ((2 : Ordinal.{u}) : Label.{u}) := by simpa using hx
      exact WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp this)
    obtain ⟨n, rfl⟩ := lt_omega0.mp (h2.trans_lt ((natCast_lt_omega0 2).trans_eq' (by simp)))
    have hn : n ≠ 0 := by rintro rfl; exact h0 (by simp)
    rw [isSelfVisible_coe, natCast_mod_omega0]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn

/-- The suppressor of the example: `2` at the grades `≤ 1`, bottom above. -/
private def exampleSuppressor (k : ℕ) : Label.{u} := if k ≤ 1 then 2 else ⊥

open Classical in
/-- The shifter of the example: `0 ↦ ∞`, `1 ↦ 2`, `2 ↦ 1`, and every other label fixed. -/
private noncomputable def exampleShifter (x : Label.{u}) : Label.{u} :=
  if x = 0 then ⊤ else if x = 1 then 2 else if x = 2 then 1 else x

private theorem exampleShifter_of_ne {x : Label.{u}} (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ 2) :
    exampleShifter x = x := by
  simp [exampleShifter, h0, h1, h2]

private theorem exampleShifter_eq_bot_iff {x : Label.{u}} : exampleShifter x = ⊥ ↔ x = ⊥ := by
  unfold exampleShifter
  split_ifs with h0 h1 h2 <;> simp_all

private theorem printedFrameWitness_example (hθ : (2 : Ordinal.{u}) < θ) :
    PrintedFrameWitness θ exampleSuppressor.{u} exampleShifter.{u} := by
  have h2 : AtStage θ (2 : Label.{u}) := (atStage_ofNat 2).mpr hθ
  have h1 : AtStage θ (1 : Label.{u}) :=
    atStage_one.mpr (lt_trans (by exact_mod_cast (show (1 : ℕ) < 2 by omega)) hθ)
  have sv1 : IsSelfVisible 1 (1 : Label.{u}) := isSelfVisible_one.mpr le_rfl
  have sv2 : IsSelfVisible 1 (2 : Label.{u}) := (isSelfVisible_ofNat 2).mpr (by simp)
  refine ⟨fun k ↦ ?_, fun x hx ↦ ?_, fun a b hab ↦ ?_, fun k ↦ ?_, ?_, ?_⟩
  · unfold exampleSuppressor
    split_ifs
    · exact h2
    · exact atStage_bot
  · unfold exampleShifter
    split_ifs
    · exact atStage_top
    · exact h2
    · exact h1
    · exact hx
  · unfold exampleSuppressor
    split_ifs <;> first | exact le_rfl | exact bot_le | omega
  · unfold exampleSuppressor
    split_ifs with hk
    · exact (isSelfVisible_ofNat 2).mpr (by simpa using (show k ≤ 2 by omega))
    · exact isSelfVisible_bot k
  · simp [exampleShifter]
  · intro i k hik x _ hk
    by_cases hk1 : k ≤ 1
    · rcases Nat.lt_or_ge k 1 with hk0 | hk1'
      · -- At threshold `0` visibility replacement is the identity.
        obtain rfl : k = 0 := by omega
        have hv (y : Label.{u}) : visibilityReplace 0 i y = y :=
          (show IsSelfVisible 0 y by
            induction y using recBotCoeTop <;> simp).visibilityReplace_eq i
        rw [hv, hv]
      · obtain rfl : k = 1 := by omega
        have hk' : exampleShifter x ≤ 2 := by simpa [exampleSuppressor] using hk
        by_cases hx0 : x = 0
        · subst hx0
          rw [show exampleShifter (0 : Label.{u}) = ⊤ by simp [exampleShifter]] at hk'
          exact absurd hk' (not_le.mpr two_lt_top)
        by_cases hx1 : x = 1
        · subst hx1
          rw [sv1.visibilityReplace_eq i]
          simp [exampleShifter]
        by_cases hx2 : x = 2
        · subst hx2
          rw [sv2.visibilityReplace_eq i]
          simp [exampleShifter]
        rw [exampleShifter_of_ne hx0 hx1 hx2] at hk' ⊢
        rw [(isSelfVisible_one_of_le_two hk' hx0).visibilityReplace_eq i,
          exampleShifter_of_ne hx0 hx1 hx2]
    · have hb : exampleShifter x = ⊥ :=
        le_bot_iff.mp (by simpa [exampleSuppressor, hk1] using hk)
      obtain rfl := exampleShifter_eq_bot_iff.mp hb
      simp [exampleShifter]

/-- **The relation of [AFK26, Definition 4.25] is not the transformation relation**: on two cells
of grade `1` labelled `1` and `2`, `u ⇒ v` holds at `ω₁` for the labelling `2`, `1` that reverses
their order, while neither `Label.TransformsTo` nor the relation of [Kni26, Definition 2.3.9]
relates them. -/
theorem exists_printedFrameTransformsTo_not_transformsTo :
    ∃ u v : Bool → Label.{u}, (∀ d, AtStage ω₁ (u d)) ∧ (∀ d, AtStage ω₁ (v d)) ∧
      PrintedFrameTransformsTo ω₁ (fun _ ↦ 1) u v ∧ ¬ TransformsTo (fun _ ↦ 1) u v ∧
        ¬ PrintedTransformsTo ω₁ (fun _ ↦ 1) u v := by
  have hθ : (2 : Ordinal.{u}) < ω₁ :=
    ((natCast_lt_omega0 2).trans_eq' (by simp)).trans omega0_lt_omega_one
  have h2 : AtStage ω₁ (2 : Label.{u}) := (atStage_ofNat 2).mpr hθ
  have h1 : AtStage ω₁ (1 : Label.{u}) :=
    atStage_one.mpr (lt_trans (by exact_mod_cast (show (1 : ℕ) < 2 by omega)) hθ)
  let u : Bool → Label.{u} := fun b ↦ if b then 2 else 1
  let v : Bool → Label.{u} := fun b ↦ if b then 1 else 2
  have hu : ∀ d, AtStage ω₁ (u d) := fun d ↦ by cases d; exacts [h1, h2]
  have hv : ∀ d, AtStage ω₁ (v d) := fun d ↦ by cases d; exacts [h2, h1]
  have hnot : ¬ TransformsTo (fun _ : Bool ↦ 1) u v := by
    rintro ⟨g, σ, hw, heq⟩
    have e0 : (2 : Label.{u}) = min (σ 1) (g 1) := by simpa [u, v] using heq false
    have e1 : (1 : Label.{u}) = min (σ 2) (g 1) := by simpa [u, v] using heq true
    have hle : min (σ 1) (g 1) ≤ min (σ 2) (g 1) :=
      min_le_min_right _ (hw.monotone (by simp))
    rw [← e0, ← e1] at hle
    exact absurd hle (by simp)
  refine ⟨u, v, hu, hv, ⟨exampleSuppressor, exampleShifter,
    printedFrameWitness_example hθ, fun d ↦ ?_⟩, hnot, fun h ↦ hnot
      ((printedTransformsTo_omega_one_iff hu hv).mp h)⟩
  cases d <;> simp [u, v, exampleShifter, exampleSuppressor]

end VaughtConjecture.Label
