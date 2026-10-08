/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Transform

/-!
# Transformations at the grade one by order interpolation

Roadmap, Layer 3 ((R3) and (R4), the grade-one base of the recognizing growth carrier).

At the constant grade `1`, the targets of a transformation from a labelling `p` of a finite family
are described by order alone.

* **The order of a target** (`Label.TransformsTo.le_of_le_visibilityReplace`): if `p` transforms to
  `q` over the grade `1` and `q` is self-visible at `1`, then `q e ≤ q d` whenever
  `p e ≤ visibilityReplace 1 1 (p d)`.
* **Order interpolation** (`Label.transformsTo_one_of_order`): conversely, a labelling `r`
  self-visible at `1`, monotone in this sense along `p`, and with the zero set of a target `q` of
  `p`, is a target of `p`.  The witness is the step suppressor at `1` and the shifter that is `⊥`
  on the zero region of the witness of `q` (a down-set closed under every visibility replacement)
  and above it the largest value of `r` at the cells whose source lies below the replacement at
  `1` of the argument, at least the least positive value of `r`.

Consequently every monotone image of a target, with the same zero set and self-visible at `1`, is
a target (`Label.TransformsTo.comp_one`).

## References

Witnesses and visibility replacement are [Kni26, Definitions 2.2.3 and 2.3.9].
-/

universe u

namespace VaughtConjecture.Label

open Finset

/-- Every label is self-visible at the threshold `0`. -/
theorem isSelfVisible_threshold_zero (x : Label.{u}) : IsSelfVisible 0 x := by
  induction x using recBotCoeTop with
  | bot => rfl
  | coe o => exact isSelfVisible_coe.mpr (by simp)
  | top => rfl

/-- **The order of a target at the grade one**: if `p` transforms to `q` over the grade `1` and `q`
is self-visible at `1`, then `q e ≤ q d` whenever `p e ≤ visibilityReplace 1 1 (p d)`. -/
theorem TransformsTo.le_of_le_visibilityReplace {D : Type*} {p q : D → Label.{u}}
    (h : TransformsTo (fun _ ↦ 1) p q) (hq : ∀ d, IsSelfVisible 1 (q d)) {d e : D}
    (hed : p e ≤ visibilityReplace 1 1 (p d)) : q e ≤ q d := by
  obtain ⟨g, σ, hw, heq⟩ := h
  rw [heq e, heq d]
  rcases le_total (σ (p d)) (g 1) with hle | hle
  · have hc := hw.visibilityReplace_comm (p d) 1 hle 1 le_rfl
    have h1 : min (σ (p e)) (g 1) ≤ min (visibilityReplace 1 1 (σ (p d))) (g 1) :=
      min_le_min_right _ (hc ▸ hw.monotone hed)
    rw [← visibilityReplace_min_of_isSelfVisible le_rfl (hw.isSelfVisible 1), ← heq d,
      (hq d).visibilityReplace_eq, heq d] at h1
    exact h1
  · rw [min_eq_right hle]
    exact min_le_right _ _

/-- The zero region of a witness at the grade one is closed under every visibility
replacement. -/
theorem IsWitness.min_visibilityReplace_eq_bot {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}
    (hw : IsWitness g σ) {x : Label.{u}} (hx : min (σ x) (g 1) = ⊥) {k i : ℕ} (hi : i ≤ k) :
    min (σ (visibilityReplace k i x)) (g 1) = ⊥ := by
  rcases min_eq_bot.mp hx with h | h
  · rw [hw.visibilityReplace_comm x k (h ▸ bot_le) i hi, h, visibilityReplace_bot,
      min_eq_left bot_le]
  · rw [h, min_bot_right]

/-- **Order interpolation at the grade one.**  Let `p` transform to `q` over the grade `1`.  A
labelling `r` of the finite family, self-visible at `1`, with `r e ≤ r d` whenever
`p e ≤ visibilityReplace 1 1 (p d)`, and `⊥` exactly where `q` is, is a target of `p`. -/
theorem transformsTo_one_of_order {D : Type*} [Finite D] {p q r : D → Label.{u}}
    (hq : TransformsTo (fun _ ↦ 1) p q) (hr : ∀ d, IsSelfVisible 1 (r d))
    (hord : ∀ d e, p e ≤ visibilityReplace 1 1 (p d) → r e ≤ r d)
    (hbot : ∀ d, r d = ⊥ ↔ q d = ⊥) : TransformsTo (fun _ ↦ 1) p r := by
  classical
  have := Fintype.ofFinite D
  obtain ⟨g, σ, hw, heq⟩ := hq
  -- the zero region, the least positive value, and the interpolating shifter
  set Z : Label.{u} → Prop := fun x ↦ min (σ x) (g 1) = ⊥ with hZ
  set m : Label.{u} := (univ.filter fun e ↦ r e ≠ ⊥).inf r with hm
  set τ : Label.{u} → Label.{u} := fun x ↦ if Z x then ⊥ else
    max ((univ.filter fun e ↦ p e ≤ visibilityReplace 1 1 x).sup r) m with hτ
  have hZdown {x y : Label.{u}} (hxy : x ≤ y) (hy : Z y) : Z x :=
    le_bot_iff.mp (hy ▸ min_le_min_right _ (hw.monotone hxy))
  have hm0 : m ≠ ⊥ := by
    refine Finset.inf_induction (p := fun y ↦ y ≠ ⊥) (by simp) (fun a ha b hb ↦ ?_) ?_
    · rcases min_choice a b with h | h <;> rw [h] <;> assumption
    · intro e he; exact (mem_filter.mp he).2
  have hmv : IsSelfVisible 1 m :=
    Finset.inf_induction (p := IsSelfVisible 1) (isSelfVisible_top _)
      (fun _ ha _ hb ↦ ha.min hb) fun e _ ↦ hr e
  have hτv (x : Label.{u}) : IsSelfVisible 1 (τ x) := by
    simp only [hτ]
    split_ifs
    · exact isSelfVisible_bot _
    · refine IsSelfVisible.max ?_ hmv
      exact Finset.sup_induction (p := IsSelfVisible 1) (isSelfVisible_bot _)
        (fun _ ha _ hb ↦ ha.max hb) fun e _ ↦ hr e
  have hτ0 (x : Label.{u}) (hx : ¬ Z x) : τ x ≠ ⊥ := by
    simp only [hτ, hx, ↓reduceIte]
    exact fun h ↦ hm0 (le_bot_iff.mp (h ▸ le_max_right _ _))
  -- the replacements at thresholds `k ≤ 1` keep the zero region and the replacement at `1`
  have hZiff {k i : ℕ} (hk : k ≤ 1) (hi : i ≤ k) (x : Label.{u}) :
      Z (visibilityReplace k i x) ↔ Z x :=
    ⟨hZdown (le_visibilityReplace (by omega) x), fun h ↦ hw.min_visibilityReplace_eq_bot h hi⟩
  have hvv {k i : ℕ} (hk : k ≤ 1) (hi : i ≤ k) (x : Label.{u}) :
      visibilityReplace 1 1 (visibilityReplace k i x) = visibilityReplace 1 1 x := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
    · rw [(isSelfVisible_threshold_zero x).visibilityReplace_eq]
    · exact visibilityReplace_self_visibilityReplace hi x
  refine ⟨stepSuppressor 1, τ, ⟨(IsWitness.id_step 1).antitone,
    (IsWitness.id_step 1).isSelfVisible, ?_, fun x y hxy ↦ ?_, fun x k hg i hi ↦ ?_⟩, fun d ↦ ?_⟩
  · -- `⊥` lies in the zero region
    simp only [hτ, hZ, hw.map_bot, min_eq_left bot_le, ↓reduceIte]
  · -- monotone
    by_cases hx : Z x
    · simp only [hτ, hx, ↓reduceIte]; exact bot_le
    have hy : ¬ Z y := fun hy ↦ hx (hZdown hxy hy)
    simp only [hτ, hx, hy, ↓reduceIte]
    refine max_le_max_right _ (Finset.sup_mono fun e he ↦ ?_)
    simp only [mem_filter, mem_univ, true_and] at he ⊢
    exact he.trans (monotone_visibilityReplace le_rfl hxy)
  · -- commutation with visibility replacement
    by_cases hk : k ≤ 1
    · rw [((hτv x).mono hk).visibilityReplace_eq]
      simp only [hτ, hZiff hk hi, hvv hk hi]
    · rw [stepSuppressor_of_lt (by omega), le_bot_iff] at hg
      have hx : Z x := by_contra fun hx ↦ hτ0 x hx hg
      have hx' : Z (visibilityReplace k i x) := hw.min_visibilityReplace_eq_bot hx hi
      rw [hg, visibilityReplace_bot]
      simp only [hτ, hx', ↓reduceIte]
  · -- the values at the cells
    rw [stepSuppressor_of_le le_rfl, min_top_right]
    by_cases hd : r d = ⊥
    · have hz : Z (p d) := by rw [hZ]; simp only; rw [← heq d]; exact (hbot d).mp hd
      simp only [hτ, hz, ↓reduceIte, hd]
    · have hz : ¬ Z (p d) := by rw [hZ]; simp only; rw [← heq d]; exact fun h ↦ hd ((hbot d).mpr h)
      simp only [hτ, hz, ↓reduceIte]
      refine le_antisymm (le_max_of_le_left ?_) (max_le (Finset.sup_le fun e he ↦ ?_) ?_)
      · exact Finset.le_sup (f := r) (mem_filter.mpr ⟨mem_univ _,
          le_visibilityReplace (by omega) _⟩)
      · exact hord d e (mem_filter.mp he).2
      · exact Finset.inf_le (mem_filter.mpr ⟨mem_univ _, hd⟩)

/-- **Monotone images of a target at the grade one**: if `p` transforms to `q` over the grade `1`,
`q` is self-visible at `1`, and `θ` is monotone, self-visible at `1` on the values of `q`, and `⊥`
exactly at `⊥` there, then `p` transforms to `θ ∘ q`. -/
theorem TransformsTo.comp_one {D : Type*} [Finite D] {p q : D → Label.{u}}
    (h : TransformsTo (fun _ ↦ 1) p q) (hq : ∀ d, IsSelfVisible 1 (q d))
    {θ : Label.{u} → Label.{u}} (hθ : Monotone θ) (hθv : ∀ d, IsSelfVisible 1 (θ (q d)))
    (hθb : ∀ d, θ (q d) = ⊥ ↔ q d = ⊥) : TransformsTo (fun _ ↦ 1) p (fun d ↦ θ (q d)) :=
  transformsTo_one_of_order h hθv (fun _ _ hed ↦ hθ (h.le_of_le_visibilityReplace hq hed)) hθb

end VaughtConjecture.Label
