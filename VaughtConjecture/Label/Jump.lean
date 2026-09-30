/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Transform

/-!
# The jump rule: stage reduction at a successor stage

Roadmap, Layer 1 (the bounded transformations used by the construction: the jump rule; guarded
composition retains its guards); semantic contract, item 3.

Let `α` be zero or a limit ordinal and `K` a natural number.  The *jump* at `α + K` keeps the
labels `≤ α + K` and sends every other label to the formal top.  It is stage reduction to the
successor stage `α + K + 1` (`reduce_add_one_of_le`, `reduce_add_one_of_lt`), and no separate
operation is introduced.  Unlike stage reduction to a stage that is zero or a limit
(`TransformsTo.reduce`), it does not commute with visibility replacement: replacing a finite part
below the threshold can move a label of the band of `α` across `α + K`.  Post-composition with it
nevertheless preserves the transformation relation under two guards.

* `IsWitness.le_coe_add_of_visibilityReplace`: at a threshold `k ≤ K` where the suppressor is at
  least `α + K`, a shifter that sends the visibility replacement of `x` to at most `α + K` sends
  `x` itself to at most `α + K`.  The label `x` is recovered from its replacement by a second
  replacement (`exists_visibilityReplace_visibilityReplace`), with which the shifter commutes.
* `IsWitness.reduce_add_one`: if the suppressor is below `α` at every grade above `K`, reducing
  the suppressor and the shifter of a witness to stage `α + K + 1` gives a witness.
* **The jump rule** (`TransformsTo.reduce_add_one`): on a finite family of cells whose targets are
  below `α` at every grade above `K`, a transformation to `q` gives a transformation to the
  reduction of `q` to stage `α + K + 1`.  Finiteness provides a label below `α`, self-visible at
  the largest grade, that bounds the targets (`exists_isSelfVisible_bound`); the suppressor is
  lowered to it above `K` (`IsWitness.sup`).
* The guard on the targets cannot be dropped (`TransformsTo.not_forall_reduce_one`).

## References

The jump rule is the post-composition used in the case of the formal top of the proof of
[Kni26, Lemma 5.3.10]; the transformation relation is [Kni26, Definition 2.3.9].
-/

universe u

open Order

namespace VaughtConjecture.Label


variable {D : Type*} {grade : D → ℕ} {p q : D → Label.{u}} {g : ℕ → Label.{u}}
  {σ : Label.{u} → Label.{u}} {α : Ordinal.{u}} {K k i : ℕ} {x : Label.{u}}

/-! ### The jump rule -/

/-- **The band mate controls the shifter.**  Let `α` be zero or a limit, `k ≤ K`, and `i ≤ k`.
If the suppressor at `k` is at least `α + K` and the shifter sends the visibility replacement of
`x` at threshold `k` with value `i` to at most `α + K`, then it sends `x` to at most `α + K`. -/
theorem IsWitness.le_coe_add_of_visibilityReplace (hw : IsWitness g σ) (hα : IsSuccPrelimit α)
    (hk : k ≤ K) (hi : i ≤ k) (hg : ((α + K : Ordinal.{u}) : Label.{u}) ≤ g k)
    (h : σ (visibilityReplace k i x) ≤ ((α + K : Ordinal.{u}) : Label.{u})) :
    σ x ≤ ((α + K : Ordinal.{u}) : Label.{u}) := by
  rcases hi.lt_or_eq with hi | rfl
  · obtain ⟨j, hj, hx⟩ := exists_visibilityReplace_visibilityReplace hi x
    calc σ x = σ (visibilityReplace k j (visibilityReplace k i x)) := by rw [hx]
      _ = visibilityReplace k j (σ (visibilityReplace k i x)) :=
        hw.visibilityReplace_comm _ k (h.trans hg) j hj.le
      _ ≤ _ := visibilityReplace_le_coe_add hα h (hj.le.trans hk) k
  · exact (hw.monotone (le_visibilityReplace (by omega) x)).trans h

/-- Let `α` be zero or a limit.  If the suppressor of a witness is below `α` at every grade above
`K`, then reducing the suppressor and the shifter to the successor stage `α + K + 1` gives a
witness. -/
theorem IsWitness.reduce_add_one (hw : IsWitness g σ) (hα : IsSuccPrelimit α)
    (hg : ∀ k, K < k → g k < α) :
    IsWitness (Label.reduce (α + (K : Ordinal.{u}) + 1) ∘ g)
      (Label.reduce (α + (K : Ordinal.{u}) + 1) ∘ σ) where
  antitone := (monotone_reduce _).comp_antitone hw.antitone
  isSelfVisible n := (hw.isSelfVisible n).reduce _
  map_bot := by simp [hw.map_bot, reduce_bot]
  monotone := (monotone_reduce _).comp hw.monotone
  visibilityReplace_comm x k hx i hi := by
    have hατ : (α : Label.{u}) ≤ ((α + K : Ordinal.{u}) : Label.{u}) :=
      WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)
    simp only [Function.comp_apply] at hx ⊢
    rcases le_or_gt k K with hk | hk
    · rcases le_or_gt (σ x) ((α + K : Ordinal.{u}) : Label.{u}) with hσ | hσ
      · rw [reduce_add_one_of_le hσ] at hx ⊢
        rw [hw.visibilityReplace_comm x k (le_of_le_reduce_add_one hσ hx) i hi,
          reduce_add_one_of_le (visibilityReplace_le_coe_add hα hσ (hi.trans hk) k)]
      · rw [reduce_add_one_of_lt hσ, top_le_iff, reduce_eq_top_iff] at hx
        have hg' : ((α + K : Ordinal.{u}) : Label.{u}) < g k :=
          not_le.mp fun h ↦ (not_lt.mpr hx) (lt_coe_add_one_iff.mpr h)
        rw [reduce_add_one_of_lt hσ, visibilityReplace_top, reduce_add_one_of_lt (not_le.mp
          fun h ↦ (not_le.mpr hσ) (hw.le_coe_add_of_visibilityReplace hα hk hi hg'.le h))]
    · rw [reduce_add_one_of_le ((hg k hk).le.trans hατ)] at hx
      have hσx : σ x < α := ((le_reduce _ _).trans hx).trans_lt (hg k hk)
      rw [reduce_add_one_of_le (hσx.le.trans hατ)] at hx ⊢
      rw [hw.visibilityReplace_comm x k hx i hi,
        reduce_add_one_of_le (((visibilityReplace_lt_iff hα).mpr hσx).le.trans hατ)]

/-- **The jump rule.**  Let `α` be zero or a limit, and let the family of cells be finite.  If
every cell of grade above `K` has its target below `α`, then a transformation to `q` gives a
transformation to the reduction of `q` to the successor stage `α + K + 1`, which keeps the
target labels `≤ α + K` and sends the others to the formal top.  This is the post-composition
used in the case of the formal top of the proof of [Kni26, Lemma 5.3.10]. -/
theorem TransformsTo.reduce_add_one [Finite D] (hα : IsSuccPrelimit α)
    (h : TransformsTo grade p q) (hq : ∀ d, K < grade d → q d < α) :
    TransformsTo grade p (Label.reduce (α + (K : Ordinal.{u}) + 1) ∘ q) := by
  obtain ⟨g, σ, hw, heq⟩ := h
  have := Fintype.ofFinite D
  have hn (d : D) : grade d ≤ Finset.univ.sup grade := Finset.le_sup (Finset.mem_univ d)
  obtain ⟨c, -, hcα, hc, hqc⟩ := exists_isSelfVisible_bound hα (Finset.univ.sup grade)
    (WithBot.bot_lt_coe _) fun d ↦ if K < grade d then q d else ⊥
  have hw₁ := (hw.cap hc).sup (hw.truncate K)
  refine ⟨_, _, hw₁.reduce_add_one (K := K) hα fun m hm ↦ ?_, fun d ↦ ?_⟩
  · simp only [Pi.sup_apply, ite_eq_right (not_le.mpr hm), max_bot_right]
    split_ifs
    exacts [(min_le_right _ _).trans_lt hcα, WithBot.bot_lt_coe _]
  · simp only [Function.comp_apply, ← (monotone_reduce _).map_min]
    congr 1
    by_cases hd : grade d ≤ K
    · rw [Pi.sup_apply, ite_eq_left hd, max_eq_right, heq d]
      split_ifs
      exacts [min_le_left _ _, bot_le]
    · have hd' : K < grade d := not_le.mp hd
      have hqd : q d ≤ c := by simpa [hd'] using hqc d (by simpa [hd'] using hq d hd')
      rw [Pi.sup_apply, ite_eq_right hd, ite_eq_left (hn d), max_bot_right, ← min_assoc,
        ← heq d, min_eq_left hqd]

/-! ### The guard cannot be dropped -/

/-- At grade one, the labelling `(0, 1)` does not transform to `(0, ⊤)`, its stage reduction to
`1 = 0 + 0 + 1`: a shifter fixing `0` commutes with visibility replacement at threshold one and
must send `1` to `1`.  Here `α = K = 0`, and the target `1` at grade `1 > K` is not below `α`. -/
private theorem TransformsTo.not_zero_one_reduce_one :
    ¬ TransformsTo (fun _ : Bool ↦ 1)
      (fun b ↦ ((if b then 1 else 0 : Ordinal.{u}) : Label.{u}))
      (Label.reduce 1 ∘ fun b ↦ ((if b then 1 else 0 : Ordinal.{u}) : Label.{u})) := by
  rintro ⟨g, τ, hw, heq⟩
  have h₁ := heq false
  have h₂ := heq true
  simp only [Function.comp_apply, Bool.false_eq_true, ↓reduceIte] at h₁ h₂
  rw [reduce_of_lt (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr zero_lt_one))] at h₁
  rw [reduce_of_le le_rfl] at h₂
  have hg : g 1 = ⊤ := top_le_iff.mp (h₂.le.trans (min_le_right _ _))
  rw [hg, min_top_right] at h₁ h₂
  have h := hw.visibilityReplace_comm ((0 : Ordinal.{u}) : Label.{u}) 1 (hg ▸ le_top) 1 le_rfl
  have h01 : Ordinal.visibilityReplace 1 1 (0 : Ordinal.{u}) = 1 := by simp
  rw [← h₁, visibilityReplace_coe, h01, ← h₂] at h
  exact (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top 1)).ne' h

/-- **The guard of the jump rule cannot be dropped**, already for two cells of grade one with
`α = K = 0`: a labelling that transforms to itself need not transform to its stage reduction to
`1 = 0 + 0 + 1`. -/
theorem TransformsTo.not_forall_reduce_one :
    ¬ ∀ (grade : Bool → ℕ) (p q : Bool → Label.{u}), TransformsTo grade p q →
      TransformsTo grade p (Label.reduce 1 ∘ q) :=
  fun h ↦ not_zero_one_reduce_one (h _ _ _ (TransformsTo.refl _ _))

end VaughtConjecture.Label
