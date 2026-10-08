/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapTransport

/-!
# Transport of lawfulness through a transformation with any suppressor

Roadmap, Layer 3, 3.1, (R6); the transport of `VaughtConjecture.Extension.CapTransport` for a
witness `(g, σ)` with an arbitrary suppressor `g`.

The transport there (`CellScheme.Rows.IsLawful.map_of_bot_iff`) sends a lawful section `r` to
`ν ∘ r` for a witness `ν` bounded by a grade `K` above every grade
(`IsWitness (stepSuppressor K) ν`).  A locality of a lawful section at a cell gives a witness
`(g, σ)` whose suppressor `g` is a general antitone map, and the transformed labelling is
`d ↦ min (σ (r d)) (g (grade d))`.  Compiled in this repository (theorem named):

* **The capped shifter** (`Label.IsWitness.min_apply`): for a witness `(g, σ)` and a grade `n`, the
  shifter `x ↦ min (σ x) (g n)` is a witness bounded by `n`.  The cap `g n` is self-visible at `n`
  and below `g k` for every `k ≤ n`, so the guard of `σ` holds wherever the capped shifter is not
  the cap (`Label.IsWitness.le_apply_visibilityReplace`).
* **Transport through any suppressor** (`CellScheme.Rows.IsLawful.transform_of_bot_iff`,
  `CellScheme.Rows.IsLawfulBelow.transform_of_bot_iff`): if `r` is lawful and the transformed
  labelling `r' d = min (σ (r d)) (g (grade d))` is bottom exactly where some lawful section `q` is
  bottom, then `r'` is lawful.  No bound on the grades is needed.  At a cell `s` of grade `n`, the
  locality target `min (r' d) (r' s)` is `min (ν (r d)) (ν (r s))` for the capped shifter `ν` at
  `n` (the suppressor is antitone, so `g n` is below `g (grade d)` for `d` below `s`), and the
  mapped locality with a lawful companion applies (`Label.TransformsTo.map_of_bot_iff`); when
  `g n = ⊥` the target is constantly `⊥`.
* **Without a companion** (`CellScheme.Rows.IsLawful.transform_of_apply_eq_bot`): when the
  transformed labelling is bottom only where `r` is, `r` is its own companion.

## Placement

Layer 3, 3.1, under "(R6)" of `roadmap/README.md`: the transport used by the fills of the cap
requests (`VaughtConjecture.Extension.CapRequestsFill`).
-/

universe u

namespace VaughtConjecture

open Label

namespace Label

variable {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}

/-- **The capped shifter**: for a witness `(g, σ)` and a grade `n`, the shifter
`x ↦ min (σ x) (g n)` is a witness bounded by the grade `n`. -/
theorem IsWitness.min_apply (hw : IsWitness g σ) (n : ℕ) :
    IsWitness (stepSuppressor.{u} n) fun x ↦ min (σ x) (g n) := by
  have hvis : IsSelfVisible n (g n) := hw.isSelfVisible n
  refine ⟨(IsWitness.id_step n).antitone, (IsWitness.id_step n).isSelfVisible,
    by simp [hw.map_bot], fun _ _ h ↦ min_le_min_right _ (hw.monotone h), fun x k hx i hi ↦ ?_⟩
  by_cases hk : k ≤ n
  · have hck : IsSelfVisible k (g n) := hvis.mono hk
    have hcg : g n ≤ g k := hw.antitone hk
    rcases le_or_gt (σ x) (g n) with hle | hlt
    · rw [min_eq_left hle, hw.visibilityReplace_comm x k (hle.trans hcg) i hi,
        min_eq_left (visibilityReplace_le_of_le hi hck hle)]
    · rw [min_eq_right hlt.le, hck.visibilityReplace_eq,
        min_eq_right (hw.le_apply_visibilityReplace hck hcg hlt hi)]
  · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff, min_eq_bot] at hx
    rcases hx with hσ | hg
    · rw [hw.visibilityReplace_comm x k (hσ ▸ bot_le) i hi, hσ]
      simp
    · simp [hg]

end Label

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {g : ℕ → Label.{u}}
  {σ : Label.{u} → Label.{u}}

namespace IsLawful

variable {r q : ι → Label.{u}}

/-- **Transport of lawfulness through a transformation with any suppressor.**  Let `r` and `q` be
lawful and `(g, σ)` a witness such that the transformed labelling
`d ↦ min (σ (r d)) (g (grade d))` is bottom exactly where `q` is.  Then the transformed labelling is
lawful. -/
theorem transform_of_bot_iff (hr : R.IsLawful r) (hq : R.IsLawful q) (hw : IsWitness g σ)
    (hbot : ∀ d, min (σ (r d)) (g (D.grade d)) = ⊥ ↔ q d = ⊥) :
    R.IsLawful fun d ↦ min (σ (r d)) (g (D.grade d)) where
  orderly d := by
    rcases le_or_gt (σ (r d)) (g (D.grade d)) with hle | hlt
    · rw [min_eq_left hle]
      exact hw.isSelfVisible_apply (hr.orderly d) hle
    · rw [min_eq_right hlt.le]
      exact hw.isSelfVisible _
  locality s := by
    set n := D.grade s
    -- below `s`, the suppressor at the grade of a cell is at least the suppressor at `n`
    have hgd (d : D.below (D.gradedIndex s)) : g n ≤ g (D.grade d) := hw.antitone d.2.2
    have htarget (d : D.below (D.gradedIndex s)) :
        min (min (σ (r d)) (g (D.grade d))) (min (σ (r s)) (g n)) =
          min (min (σ (r d)) (g n)) (min (σ (r s)) (g n)) := by
      rw [min_min_min_comm, min_eq_right (hgd d), min_min_min_comm, min_self]
    by_cases hb : g n = ⊥
    · refine ⟨fun _ ↦ ⊤, fun _ ↦ ⊥, IsWitness.bot_top, fun d ↦ ?_⟩
      simp only [hb, min_bot_right]
      simp
    have hloc := Label.TransformsTo.map_of_bot_iff
      (grade := fun d : D.below (D.gradedIndex s) ↦ D.grade d) (E := R.row s)
      (p := fun d ↦ r d) (q := fun d ↦ q d) (c := ⟨s, D.mem_below_gradedIndex s⟩)
      (K := n) (fun d ↦ d.2.2) le_rfl (hr.orderly s) (hr.locality s) (hq.orderly s)
      (hq.locality s) (hw.min_apply n) fun d ↦ by
        rw [← hbot d, min_eq_bot, min_eq_bot, or_iff_left hb,
          or_iff_left (ne_bot_of_le_ne_bot hb (hgd d))]
    obtain ⟨g', σ', hw', heq⟩ := hloc
    exact ⟨g', σ', hw', fun d ↦ (htarget d).trans (heq d)⟩
  availability s t hst hg := by
    obtain ⟨u, hu, hle⟩ := hr.availability s t hst hg
    refine ⟨u, hu, ?_⟩
    have hgu : D.grade u = D.grade s := (congrArg Prod.snd hu).trans hg.symm
    rw [hgu]
    exact min_le_min_right _ (hw.monotone hle)

/-- **Transport through any suppressor without a companion**: when the transformed labelling is
bottom only where `r` is, it is lawful (`r` is its own companion). -/
theorem transform_of_apply_eq_bot (hr : R.IsLawful r) (hw : IsWitness g σ)
    (hbot : ∀ d, min (σ (r d)) (g (D.grade d)) = ⊥ → r d = ⊥) :
    R.IsLawful fun d ↦ min (σ (r d)) (g (D.grade d)) :=
  hr.transform_of_bot_iff hr hw fun d ↦ ⟨hbot d, fun h ↦ by rw [h, hw.map_bot, min_bot_left]⟩

end IsLawful

namespace IsLawfulBelow

variable {X : Finset α × ℕ} {r q : D.below X → Label.{u}}

/-- **Transport of lawfulness through a transformation with any suppressor**, below a pair `X`
(`CellScheme.Rows.IsLawful.transform_of_bot_iff`). -/
theorem transform_of_bot_iff (hr : R.IsLawfulBelow X r) (hq : R.IsLawfulBelow X q)
    (hw : IsWitness g σ) (hbot : ∀ d, min (σ (r d)) (g (D.grade d)) = ⊥ ↔ q d = ⊥) :
    R.IsLawfulBelow X fun d ↦ min (σ (r d)) (g (D.grade d)) :=
  isLawfulBelow_iff.mpr ((isLawfulBelow_iff.mp hr).transform_of_bot_iff
    (isLawfulBelow_iff.mp hq) hw hbot)

/-- **Transport through any suppressor without a companion**, below a pair `X`. -/
theorem transform_of_apply_eq_bot (hr : R.IsLawfulBelow X r) (hw : IsWitness g σ)
    (hbot : ∀ d, min (σ (r d)) (g (D.grade d)) = ⊥ → r d = ⊥) :
    R.IsLawfulBelow X fun d ↦ min (σ (r d)) (g (D.grade d)) :=
  isLawfulBelow_iff.mpr ((isLawfulBelow_iff.mp hr).transform_of_apply_eq_bot hw hbot)

end IsLawfulBelow

end CellScheme.Rows

end VaughtConjecture
