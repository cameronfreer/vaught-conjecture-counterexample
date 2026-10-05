/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Visibility

/-!
# The transformation relation between labellings

Roadmap, Layer 1 (the bounded transformations used by the construction; guarded composition
retains its guards, and no transitivity is declared); semantic contract, item 3.

Let `D` be a family of cells with grades `grade : D → ℕ`, and let `p q : D → Label` be
labellings.  A *witness* consists of a *suppressor* `g : ℕ → Label` and a *shifter*
`σ : Label → Label` subject to five laws (`IsWitness g σ`, [Kni26, Definition 2.3.9]):

1. `g` is antitone;
2. each `g n` is self-visible at `n`;
3. `σ ⊥ = ⊥`;
4. `σ` is monotone;
5. `σ` commutes with visibility replacement at threshold `k` and every value `i ≤ k` at each
   label `x` with `σ x ≤ g k` (the *guard*).

The labelling `p` *transforms to* `q` (`TransformsTo grade p q`) if some witness satisfies
`q d = min (σ (p d)) (g (grade d))` for every cell `d`.  The raw data `(g, σ)` and their laws
are kept apart: `IsWitness` is a proposition about given functions.

The *step suppressor* `stepSuppressor K` is the formal top at the grades `≤ K` and bottom above.
A value map `σ` is a *witness bounded by grade `K`* when `(stepSuppressor K, σ)` is a witness
(`IsWitness (stepSuppressor K) σ`); the bound is on the grades of the suppressor, not on the values
of `σ`.

## Rules proved here

* reflexivity (`TransformsTo.refl`), pullback along a map of cell families
  (`TransformsTo.reindex`), and the bottom cases (`TransformsTo.bot`, `TransformsTo.eq_bot`);
* every witness reads `a` at most as `b` exactly when `a ≤ b` (`le_iff_forall_isWitness`);
* monotonicity in the source and antitonicity in the grade (`TransformsTo.le_of_le`), and
  preservation of self-visibility at the grade (`TransformsTo.isSelfVisible`);
* lowering the suppressor (`IsWitness.of_le`, `IsWitness.of_le_stepSuppressor`), the pointwise
  maximum of two suppressors (`IsWitness.sup`), truncation of the suppressor above a grade
  (`IsWitness.truncate`), capping the suppressor by a self-visible label (`IsWitness.cap`), and
  the cap rule for the target (`TransformsTo.min_const`, a related target-capping variant of
  [Kni26, Lemma 2.3.12]);
* guarded composition (`IsWitness.comp_of_bot_reflecting`): a witness bounded by grade `m` may be
  followed by a second witness bounded by grade `m` that reflects bottom on the values of the
  first;
* stage reduction at a stage that is zero or a limit, of the target and of the witness
  (`TransformsTo.reduce_self`, `IsWitness.reduce`, and the reduction rule
  `TransformsTo.reduce`, [Kni26, Lemma 3.1.3]);
* pointwise minima: the pointwise minimum of two witnesses is a witness (`IsWitness.inf`), so two
  transformations from a common source give one to the pointwise minimum of their targets
  (`TransformsTo.inf`).  The guard is handled by the fact that a shifter exceeding the suppressor
  at `k` still exceeds it after visibility replacement at `k`
  (`IsWitness.lt_apply_visibilityReplace`, the argument of `IsWitness.reduce`);
* collapse above a threshold: `collapse β N` is stage reduction to `β + N` (`reduce (β + N)`),
  sending every label at least `β + N` to the formal top and keeping the others; for `β` zero or a
  limit and all grades at most `K < N`, a transformation to `q` gives one to the collapse of `q`
  (`TransformsTo.collapse`), since the collapse commutes with visibility replacement at thresholds
  `k < N` (`collapse_visibilityReplace`), although `β + N` is a successor stage for `N ≠ 0`.

Pointwise minima and collapse prove locality of the stable labelling at the next block stage
(roadmap, Layer 4, output 1), written as a pointwise minimum of finitely many lawful labellings,
collapsed above a threshold (`Realization.locality_stableSection`, in
`VaughtConjecture.Continuation.Candidate`).

## Nontransitivity

The relation is **not transitive**, even on labellings that are self-visible at the grade:
at grade one, `(1, 2) ⇒ (1, ⊤)` and `(1, ⊤) ⇒ (⊥, ⊤)`, but not `(1, 2) ⇒ (⊥, ⊤)`
(`TransformsTo.not_transitive`).  No `Trans` or `IsTrans` instance is declared, and composition
is available only in the guarded form above.

## References

The transformation relation is [Kni26, Definition 2.3.9], the cap rule `TransformsTo.min_const`
is a related target-capping variant of [Kni26, Lemma 2.3.12] (which caps the source at a selected
source value and the target at the corresponding target value), and the reduction rule is
[Kni26, Lemma 3.1.3].  Nontransitivity contradicts [Kni26, Lemma 2.3.14] as printed.
-/

universe u

namespace VaughtConjecture.Label

variable {D D' : Type*} {grade : D → ℕ} {p q : D → Label.{u}}
  {g g' : ℕ → Label.{u}} {σ τ ν : Label.{u} → Label.{u}}

/-- The laws of a transformation witness: a suppressor `g` and a shifter `σ`
[Kni26, Definition 2.3.9]. -/
structure IsWitness (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}) : Prop where
  /-- The suppressor is antitone. -/
  antitone : Antitone g
  /-- Each value of the suppressor is self-visible at its grade. -/
  isSelfVisible : ∀ n, IsSelfVisible n (g n)
  /-- The shifter fixes bottom. -/
  map_bot : σ ⊥ = ⊥
  /-- The shifter is monotone. -/
  monotone : Monotone σ
  /-- Under the guard `σ x ≤ g k`, the shifter commutes with visibility replacement at
  threshold `k` for every value `i ≤ k`. -/
  visibilityReplace_comm : ∀ x k, σ x ≤ g k → ∀ i ≤ k,
    σ (visibilityReplace k i x) = visibilityReplace k i (σ x)

/-- The labelling `p` *transforms to* `q` over the grades `grade`: for some witness `(g, σ)`,
`q d = min (σ (p d)) (g (grade d))` for every cell `d`. -/
def TransformsTo (grade : D → ℕ) (p q : D → Label.{u}) : Prop :=
  ∃ g σ, IsWitness g σ ∧ ∀ d, q d = min (σ (p d)) (g (grade d))

/-- The step suppressor at grade `K`: the formal top at grades `≤ K` and bottom above. -/
def stepSuppressor (K : ℕ) (n : ℕ) : Label.{u} := if n ≤ K then ⊤ else ⊥

/-- The step suppressor is the formal top at grades `≤ K`. -/
@[simp] theorem stepSuppressor_of_le {K n : ℕ} (h : n ≤ K) :
    stepSuppressor.{u} K n = ⊤ := ite_eq_left h

/-- The step suppressor is bottom at grades `> K`. -/
@[simp] theorem stepSuppressor_of_lt {K n : ℕ} (h : K < n) :
    stepSuppressor.{u} K n = ⊥ := ite_eq_right h.not_ge

/-! ### Basic witnesses and rules -/

/-- The identity shifter with the constant suppressor `⊤` is a witness. -/
theorem IsWitness.id_top : IsWitness (fun _ ↦ (⊤ : Label.{u})) id :=
  ⟨antitone_const, fun _ ↦ isSelfVisible_top _, rfl, monotone_id, fun _ _ _ _ _ ↦ rfl⟩

/-- The constant shifter `⊥` with the constant suppressor `⊤` is a witness. -/
theorem IsWitness.bot_top : IsWitness (fun _ ↦ (⊤ : Label.{u})) (fun _ ↦ ⊥) :=
  ⟨antitone_const, fun _ ↦ isSelfVisible_top _, rfl, monotone_const,
    fun _ _ _ _ _ ↦ (visibilityReplace_bot _ _).symm⟩

/-- **Every witness reads `a` at most as `b` exactly when `a ≤ b`**: shifters are monotone, and
the identity is a witness. -/
theorem le_iff_forall_isWitness {a b : Label.{u}} :
    (∀ (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}), IsWitness g σ → σ a ≤ σ b) ↔ a ≤ b :=
  ⟨fun h ↦ h _ id IsWitness.id_top, fun h _ _ hw ↦ hw.monotone h⟩

/-- Every labelling transforms to itself. -/
theorem TransformsTo.refl (grade : D → ℕ) (p : D → Label.{u}) : TransformsTo grade p p :=
  ⟨_, _, IsWitness.id_top, fun _ ↦ (min_top_right _).symm⟩

/-- Every labelling transforms to the constant bottom labelling. -/
theorem TransformsTo.bot (grade : D → ℕ) (p : D → Label.{u}) :
    TransformsTo grade p (fun _ ↦ ⊥) :=
  ⟨_, _, IsWitness.bot_top, fun _ ↦ (min_eq_left bot_le).symm⟩

/-- A transformation pulls back along any map of cell families. -/
theorem TransformsTo.reindex (h : TransformsTo grade p q) (φ : D' → D) :
    TransformsTo (grade ∘ φ) (p ∘ φ) (q ∘ φ) :=
  let ⟨g, σ, hw, heq⟩ := h
  ⟨g, σ, hw, fun d ↦ heq (φ d)⟩

/-- A transformation sends a bottom source label to bottom. -/
theorem TransformsTo.eq_bot (h : TransformsTo grade p q) {d : D} (hd : p d = ⊥) : q d = ⊥ := by
  obtain ⟨g, σ, hw, heq⟩ := h
  rw [heq, hd, hw.map_bot, min_eq_left bot_le]

/-- A transformation is monotone in the source label and antitone in the grade. -/
theorem TransformsTo.le_of_le (h : TransformsTo grade p q) {d d' : D} (hp : p d ≤ p d')
    (hg : grade d' ≤ grade d) : q d ≤ q d' := by
  obtain ⟨g, σ, hw, heq⟩ := h
  rw [heq, heq]
  exact min_le_min (hw.monotone hp) (hw.antitone hg)

/-- Under the guard, a shifter preserves self-visibility at the threshold. -/
theorem IsWitness.isSelfVisible_apply (hw : IsWitness g σ) {k : ℕ} {x : Label.{u}}
    (hx : IsSelfVisible k x) (hg : σ x ≤ g k) : IsSelfVisible k (σ x) := by
  have := hw.visibilityReplace_comm x k hg k le_rfl
  rwa [hx, eq_comm] at this

/-- A transformation preserves self-visibility of a label at the grade of its cell. -/
theorem TransformsTo.isSelfVisible (h : TransformsTo grade p q) {d : D}
    (hp : IsSelfVisible (grade d) (p d)) : IsSelfVisible (grade d) (q d) := by
  obtain ⟨g, σ, hw, heq⟩ := h
  rw [heq]
  rcases le_total (σ (p d)) (g (grade d)) with hle | hle
  · rw [min_eq_left hle]; exact hw.isSelfVisible_apply hp hle
  · rw [min_eq_right hle]; exact hw.isSelfVisible _

/-! ### Lowering, truncating, and capping the suppressor -/

/-- A witness remains a witness for any lower antitone suppressor that is self-visible at each
grade. -/
theorem IsWitness.of_le (hw : IsWitness g σ) (hle : g' ≤ g) (anti : Antitone g')
    (vis : ∀ n, IsSelfVisible n (g' n)) : IsWitness g' σ :=
  ⟨anti, vis, hw.map_bot, hw.monotone,
    fun x k hx i hi ↦ hw.visibilityReplace_comm x k (hx.trans (hle k)) i hi⟩

/-- **Capping the suppressor.**  For a label `c` self-visible at `K`, capping the suppressor by
`c` at grades `≤ K` and replacing it by bottom above `K` gives a witness. -/
theorem IsWitness.cap (hw : IsWitness g σ) {K : ℕ} {c : Label.{u}} (hc : IsSelfVisible K c) :
    IsWitness (fun n ↦ if n ≤ K then min (g n) c else ⊥) σ := by
  refine hw.of_le (fun n ↦ ?_) (fun n m hnm ↦ ?_) (fun n ↦ ?_)
  · split_ifs
    · exact min_le_left _ _
    · exact bot_le
  · split_ifs with hm hn
    · exact min_le_min_right _ (hw.antitone hnm)
    · exact absurd (hnm.trans hm) hn
    · exact bot_le
    · exact le_rfl
  · split_ifs with hn
    · exact (hw.isSelfVisible n).min (hc.mono hn)
    · exact isSelfVisible_bot n

/-- **Truncating the suppressor.**  Replacing the suppressor by bottom above a grade `K` gives
a witness. -/
theorem IsWitness.truncate (hw : IsWitness g σ) (K : ℕ) :
    IsWitness (fun n ↦ if n ≤ K then g n else ⊥) σ := by
  simpa only [min_top_right] using hw.cap (isSelfVisible_top K)

/-- The identity is a witness bounded by grade `K`. -/
theorem IsWitness.id_step (K : ℕ) : IsWitness (stepSuppressor.{u} K) id :=
  IsWitness.id_top.truncate K

/-- **The cap rule**, a related target-capping variant of [Kni26, Lemma 2.3.12] (the source `p`
is retained and only the target is capped).  If every grade is at most `K` and `c` is
self-visible at `K`, then a transformation to `q` gives a transformation to `q` capped at `c`. -/
theorem TransformsTo.min_const (h : TransformsTo grade p q) {K : ℕ} (hK : ∀ d, grade d ≤ K)
    {c : Label.{u}} (hc : IsSelfVisible K c) : TransformsTo grade p (fun d ↦ min (q d) c) := by
  obtain ⟨g, σ, hw, heq⟩ := h
  exact ⟨_, σ, hw.cap hc, fun d ↦ by simp only [ite_eq_left (hK d), heq, min_assoc]⟩

/-- The pointwise maximum of two suppressors of a shifter is a suppressor of it. -/
theorem IsWitness.sup (hg : IsWitness g σ) (hg' : IsWitness g' σ) : IsWitness (g ⊔ g') σ where
  antitone := hg.antitone.sup hg'.antitone
  isSelfVisible n := (hg.isSelfVisible n).max (hg'.isSelfVisible n)
  map_bot := hg.map_bot
  monotone := hg.monotone
  visibilityReplace_comm x k hx i hi := (le_sup_iff.mp hx).elim
    (hg.visibilityReplace_comm x k · i hi) (hg'.visibilityReplace_comm x k · i hi)

/-! ### Guarded composition -/

/-- The step suppressor is monotone in its grade. -/
theorem monotone_stepSuppressor : Monotone (stepSuppressor.{u} : ℕ → ℕ → Label.{u}) :=
  fun _ _ hmK n ↦ by unfold stepSuppressor; split_ifs <;> simp_all; omega

/-- A witness bounded by grade `K` is a witness bounded by every grade `m ≤ K`. -/
theorem IsWitness.of_le_stepSuppressor {m K : ℕ} (hν : IsWitness (stepSuppressor K) ν)
    (hmK : m ≤ K) : IsWitness (stepSuppressor.{u} m) ν :=
  hν.of_le (monotone_stepSuppressor hmK) (IsWitness.id_step m).antitone
    (IsWitness.id_step m).isSelfVisible

/-- **Guarded composition.**  If `τ` and `ν` are witnesses bounded by grade `m`, then `ν ∘ τ` is a
witness bounded by grade `m`, provided `ν` sends a value of `τ` to bottom only when that value is
bottom.  A witness bounded by a grade `K ≥ m` is bounded by `m`
(`IsWitness.of_le_stepSuppressor`). -/
theorem IsWitness.comp_of_bot_reflecting {m : ℕ} (hτ : IsWitness (stepSuppressor m) τ)
    (hν : IsWitness (stepSuppressor m) ν) (hbot : ∀ x, ν (τ x) = ⊥ → τ x = ⊥) :
    IsWitness (stepSuppressor.{u} m) (ν ∘ τ) where
  antitone := hτ.antitone
  isSelfVisible := hτ.isSelfVisible
  map_bot := by simp [hτ.map_bot, hν.map_bot]
  monotone := hν.monotone.comp hτ.monotone
  visibilityReplace_comm x k hx i hi := by
    simp only [Function.comp_apply] at hx ⊢
    by_cases hk : k ≤ m
    · rw [hτ.visibilityReplace_comm x k (by simp [hk]) i hi,
        hν.visibilityReplace_comm _ k (by simp [hk]) i hi]
    -- Above `m` the guard forces `ν (τ x) = ⊥`; bottom reflection recovers `τ x = ⊥`, which is
    -- the guard of the first shifter.
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
      have hτx : τ x = ⊥ := hbot x hx
      rw [hτ.visibilityReplace_comm x k (by simp [hτx]) i hi, hτx, visibilityReplace_bot,
        hν.map_bot, visibilityReplace_bot]

/-! ### Stage reduction -/

/-- At a stage `α` that is zero or a limit, every labelling transforms to its stage reduction. -/
theorem TransformsTo.reduce_self {α : Ordinal.{u}} (hα : Order.IsSuccPrelimit α)
    (grade : D → ℕ) (p : D → Label.{u}) : TransformsTo grade p (reduce α ∘ p) :=
  ⟨fun _ ↦ ⊤, reduce α,
    ⟨antitone_const, fun _ ↦ isSelfVisible_top _, reduce_bot, monotone_reduce α,
      fun x k _ i _ ↦ reduce_visibilityReplace hα k i x⟩,
    fun _ ↦ (min_top_right _).symm⟩

/-- At a stage `α` that is zero or a limit, reducing both the suppressor and the shifter of a
witness gives a witness. -/
theorem IsWitness.reduce {α : Ordinal.{u}} (hα : Order.IsSuccPrelimit α) (hw : IsWitness g σ) :
    IsWitness (reduce α ∘ g) (reduce α ∘ σ) where
  antitone := (monotone_reduce α).comp_antitone hw.antitone
  isSelfVisible n := (hw.isSelfVisible n).reduce α
  map_bot := by simp [hw.map_bot]
  monotone := (monotone_reduce α).comp hw.monotone
  visibilityReplace_comm x k hx i hi := by
    simp only [Function.comp_apply] at hx ⊢
    rw [← reduce_visibilityReplace hα]
    by_cases hxk : σ x ≤ g k
    · rw [hw.visibilityReplace_comm x k hxk i hi]
    have hαg : (α : Label.{u}) ≤ g k := by
      by_contra hg
      have hg : g k < α := not_le.mp hg
      rw [reduce_of_lt hg] at hx
      exact hxk (by rwa [reduce_of_lt (reduce_lt_iff.mp (hx.trans_lt hg))] at hx)
    have hασ : (α : Label.{u}) ≤ σ x := hαg.trans (not_le.mp hxk).le
    rw [reduce_of_le (not_lt.mp (mt (visibilityReplace_lt_iff hα).mp (not_lt.mpr hασ))),
      reduce_of_le]
    by_contra hy
    have hy : σ (visibilityReplace k i x) < α := not_le.mp hy
    have h5 := hw.visibilityReplace_comm _ k (hy.le.trans hαg) k le_rfl
    rw [visibilityReplace_self_visibilityReplace hi] at h5
    have hle : σ x ≤ σ (visibilityReplace k k x) := hw.monotone (le_visibilityReplace (by omega) x)
    exact (not_lt.mpr hασ) (hle.trans_lt (h5 ▸ (visibilityReplace_lt_iff hα).mpr hy))

/-- **The reduction rule** [Kni26, Lemma 3.1.3].  At a stage `α` that is zero or a limit, a
transformation to `q` gives a transformation to the stage reduction of `q`. -/
theorem TransformsTo.reduce {α : Ordinal.{u}} (hα : Order.IsSuccPrelimit α)
    (h : TransformsTo grade p q) : TransformsTo grade p (reduce α ∘ q) := by
  obtain ⟨g, σ, hw, heq⟩ := h
  exact ⟨_, _, hw.reduce hα, fun d ↦ by simp [heq, (monotone_reduce α).map_min]⟩

/-! ### Pointwise minima -/

/-- **The guard fails along visibility replacement**: if the shifter exceeds the suppressor at `k`
at `x`, it exceeds it at every visibility replacement of `x` at threshold `k` with a value
`i ≤ k`.  Otherwise the guard would hold there, and replacing again with value `k` would bound the
shifter at `x` by the suppressor at `k`. -/
theorem IsWitness.lt_apply_visibilityReplace (hw : IsWitness g σ) {x : Label.{u}} {k i : ℕ}
    (hx : g k < σ x) (hi : i ≤ k) : g k < σ (visibilityReplace k i x) := by
  by_contra hy
  have hy : σ (visibilityReplace k i x) ≤ g k := not_lt.mp hy
  have h5 := hw.visibilityReplace_comm _ k hy k le_rfl
  rw [visibilityReplace_self_visibilityReplace hi] at h5
  have hle : σ x ≤ σ (visibilityReplace k k x) := hw.monotone (le_visibilityReplace (by omega) x)
  exact hx.not_ge (hle.trans (h5.trans_le
    (visibilityReplace_le_of_le le_rfl (hw.isSelfVisible k) hy)))

/-- The guard law of `IsWitness.inf` when the first shifter is the smaller one at `x`. -/
private theorem IsWitness.inf_comm_of_le {g₁ g₂ : ℕ → Label.{u}} {σ₁ σ₂ : Label.{u} → Label.{u}}
    (h₁ : IsWitness g₁ σ₁) (h₂ : IsWitness g₂ σ₂) {x : Label.{u}} {k i : ℕ} (hle : σ₁ x ≤ σ₂ x)
    (hx₁ : σ₁ x ≤ g₁ k) (hx₂ : σ₁ x ≤ g₂ k) (hi : i ≤ k) :
    min (σ₁ (visibilityReplace k i x)) (σ₂ (visibilityReplace k i x)) =
      visibilityReplace k i (min (σ₁ x) (σ₂ x)) := by
  rw [visibilityReplace_min hi, h₁.visibilityReplace_comm x k hx₁ i hi]
  by_cases h₂x : σ₂ x ≤ g₂ k
  · rw [h₂.visibilityReplace_comm x k h₂x i hi]
  · have hlt := h₂.lt_apply_visibilityReplace (not_le.mp h₂x) hi
    have hb : visibilityReplace k i (σ₁ x) ≤ g₂ k :=
      visibilityReplace_le_of_le hi (h₂.isSelfVisible k) hx₂
    rw [min_eq_left (hb.trans hlt.le), min_eq_left (monotone_visibilityReplace hi hle)]

/-- **Pointwise minima of witnesses**: the pointwise minimum of two suppressors, with the pointwise
minimum of their shifters, is a witness. -/
theorem IsWitness.inf {g₁ g₂ : ℕ → Label.{u}} {σ₁ σ₂ : Label.{u} → Label.{u}}
    (h₁ : IsWitness g₁ σ₁) (h₂ : IsWitness g₂ σ₂) : IsWitness (g₁ ⊓ g₂) (σ₁ ⊓ σ₂) where
  antitone := h₁.antitone.inf h₂.antitone
  isSelfVisible n := (h₁.isSelfVisible n).min (h₂.isSelfVisible n)
  map_bot := by simp [h₁.map_bot, h₂.map_bot]
  monotone := h₁.monotone.inf h₂.monotone
  visibilityReplace_comm x k hx i hi := by
    simp only [Pi.inf_apply] at hx ⊢
    rcases le_total (σ₁ x) (σ₂ x) with hle | hle
    · rw [inf_eq_left.mpr hle] at hx
      exact h₁.inf_comm_of_le h₂ hle (hx.trans inf_le_left) (hx.trans inf_le_right) hi
    · rw [inf_eq_right.mpr hle] at hx
      rw [inf_comm, inf_comm (σ₁ x)]
      exact h₂.inf_comm_of_le h₁ hle (hx.trans inf_le_right) (hx.trans inf_le_left) hi

/-- **Pointwise minima of transformations**: if `p` transforms to `q₁` and to `q₂`, it transforms
to their pointwise minimum. -/
theorem TransformsTo.inf {q₁ q₂ : D → Label.{u}} (h₁ : TransformsTo grade p q₁)
    (h₂ : TransformsTo grade p q₂) : TransformsTo grade p (q₁ ⊓ q₂) := by
  obtain ⟨g₁, σ₁, hw₁, he₁⟩ := h₁
  obtain ⟨g₂, σ₂, hw₂, he₂⟩ := h₂
  exact ⟨_, _, hw₁.inf hw₂, fun d ↦ by
    simp only [Pi.inf_apply, he₁, he₂]
    exact inf_inf_inf_comm _ _ _ _⟩

/-! ### Collapse above a threshold -/

section Collapse

variable {β : Ordinal.{u}} {N : ℕ} {x y : Label.{u}}

/-- The **collapse** above `β + N` is stage reduction to `β + N` (`Label.reduce (β + N)`): a label
at least `β + N` is sent to the formal top, and every other label is kept.  Its elementary
properties are those of stage reduction: `reduce_of_le`, `reduce_of_lt`, `le_reduce`,
`monotone_reduce`, `reduce_eq_bot_iff` and `IsSelfVisible.reduce`.  For `N ≠ 0` the stage `β + N`
is a successor, so `reduce_visibilityReplace` does not apply; the collapse commutes with visibility
replacement only at thresholds `k < N` (`collapse_visibilityReplace`). -/
noncomputable abbrev collapse (β : Ordinal.{u}) (N : ℕ) (x : Label.{u}) : Label.{u} :=
  reduce (β + N) x

/-- Visibility replacement at a threshold `k < N` with a value `i ≤ k` does not move a label across
`β + N`, for `β` zero or a limit. -/
private theorem coe_add_le_visibilityReplace_iff (hβ : Order.IsSuccPrelimit β) {k i : ℕ}
    (hi : i ≤ k) (hkN : k < N) :
    ((β + N : Ordinal.{u}) : Label.{u}) ≤ visibilityReplace k i x ↔
      ((β + N : Ordinal.{u}) : Label.{u}) ≤ x := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hM : ((β + (M + 1 : ℕ) : Ordinal.{u}) : Label.{u}) = ((β + M + 1 : Ordinal.{u}) : Label.{u})
    := by rw [Nat.cast_add_one, add_assoc]
  rw [hM, ← not_lt, ← not_lt, lt_coe_add_one_iff, lt_coe_add_one_iff, not_iff_not]
  refine ⟨fun h ↦ ?_, fun h ↦ visibilityReplace_le_coe_add hβ h (by omega) k⟩
  calc x ≤ visibilityReplace k k x := le_visibilityReplace (by omega) x
    _ = visibilityReplace k k (visibilityReplace k i x) :=
      (visibilityReplace_self_visibilityReplace hi x).symm
    _ ≤ _ := visibilityReplace_le_of_le le_rfl (isSelfVisible_coe_add hβ (by omega)) h

/-- **The collapse commutes with visibility replacement** at a threshold `k < N` with a value
`i ≤ k`, for `β` zero or a limit. -/
theorem collapse_visibilityReplace (hβ : Order.IsSuccPrelimit β) {k i : ℕ} (hi : i ≤ k)
    (hkN : k < N) (x : Label.{u}) :
    collapse β N (visibilityReplace k i x) = visibilityReplace k i (collapse β N x) := by
  unfold collapse
  by_cases hx : ((β + N : Ordinal.{u}) : Label.{u}) ≤ x
  · rw [reduce_of_le hx, visibilityReplace_top,
      reduce_of_le ((coe_add_le_visibilityReplace_iff hβ hi hkN).mpr hx)]
  · rw [reduce_of_lt (not_le.mp hx),
      reduce_of_lt (not_le.mp (mt (coe_add_le_visibilityReplace_iff hβ hi hkN).mp hx))]

/-- **Collapse of a transformation**: if every grade is at most `K < N` and `β` is zero or a limit,
a transformation to `q` gives a transformation to the collapse of `q` above `β + N`.  The witness
is the collapse of the suppressor, truncated above `K`, with the collapse of the shifter. -/
theorem TransformsTo.collapse (hβ : Order.IsSuccPrelimit β) {K : ℕ} (hK : ∀ d, grade d ≤ K)
    (hKN : K < N) (h : TransformsTo grade p q) : TransformsTo grade p (collapse β N ∘ q) := by
  obtain ⟨g, σ, hw, heq⟩ := h
  refine ⟨fun n ↦ if n ≤ K then Label.collapse β N (g n) else ⊥, Label.collapse β N ∘ σ,
    ⟨fun n m hnm ↦ ?_, fun n ↦ ?_, by simp [hw.map_bot], (monotone_reduce _).comp hw.monotone,
      fun x k hx i hi ↦ ?_⟩, fun d ↦ ?_⟩
  · split_ifs with hm hn
    · exact monotone_reduce _ (hw.antitone hnm)
    · exact absurd (hnm.trans hm) hn
    · exact bot_le
    · exact le_rfl
  · split_ifs
    exacts [(hw.isSelfVisible n).reduce _, isSelfVisible_bot n]
  · simp only [Function.comp_apply] at hx ⊢
    split_ifs at hx with hk
    · by_cases hxk : σ x ≤ g k
      · rw [hw.visibilityReplace_comm x k hxk i hi,
          collapse_visibilityReplace hβ hi (hk.trans_lt hKN)]
      unfold Label.collapse at hx ⊢
      have hgk : ((β + N : Ordinal.{u}) : Label.{u}) ≤ g k := by
        by_contra hg
        rw [reduce_of_lt (not_le.mp hg)] at hx
        exact hxk ((le_reduce _ _).trans hx)
      have hlt : g k < σ x := not_le.mp hxk
      rw [reduce_of_le (hgk.trans (hw.lt_apply_visibilityReplace hlt hi).le),
        reduce_of_le (hgk.trans hlt.le), visibilityReplace_top]
    · have hσ : σ x = ⊥ := reduce_eq_bot_iff.mp (le_bot_iff.mp hx)
      rw [hw.visibilityReplace_comm x k (hσ.trans_le bot_le) i hi, hσ, visibilityReplace_bot,
        Label.collapse, reduce_bot, visibilityReplace_bot]
  · simp only [Function.comp_apply, hK d, ↓reduceIte, heq]
    exact (monotone_reduce _).map_min

end Collapse

/-! ### Nontransitivity -/

section Nontransitive

open Ordinal

/-- The sources `(1, 2)`, at grade one, transform to `(1, ⊤)`. -/
private theorem TransformsTo.one_two_one_top :
    TransformsTo (fun _ : Bool ↦ 1)
      (fun b ↦ ((if b then 2 else 1 : Ordinal.{u}) : Label.{u}))
      (fun b ↦ if b then ⊤ else ((1 : Ordinal.{u}) : Label.{u})) := by
  refine ⟨stepSuppressor 1, Label.reduce 2, ⟨(IsWitness.id_step 1).antitone,
    (IsWitness.id_step 1).isSelfVisible, reduce_bot, monotone_reduce 2, ?_⟩, ?_⟩
  · intro x k hx i hi
    rcases le_or_gt k 1 with hk | hk
    · by_cases h2 : ((2 : Ordinal.{u}) : Label.{u}) ≤ x
      · rw [reduce_of_le h2, visibilityReplace_top,
          reduce_of_le (h2.trans (le_visibilityReplace (by omega) x))]
      rw [not_le] at h2
      rw [reduce_of_lt h2]
      refine reduce_of_lt ?_
      induction x using recBotCoeTop with
      | bot => exact h2
      | coe o =>
        have ho : o < 2 := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h2)
        have hω : o < ω := ho.trans (by exact_mod_cast natCast_lt_omega0 2)
        have hi2 : (i : Ordinal.{u}) < 2 := by exact_mod_cast (hi.trans hk).trans_lt one_lt_two
        simp only [visibilityReplace_coe, Ordinal.visibilityReplace_of_lt_omega0 hω,
          WithBot.coe_lt_coe, WithTop.coe_lt_coe]
        split_ifs <;> assumption
      | top => simp at h2
    · rw [stepSuppressor_of_lt hk, le_bot_iff, reduce_eq_bot_iff] at hx
      simp [hx, reduce_bot]
  · have h12 : ((1 : Ordinal.{u}) : Label.{u}) < ((2 : Ordinal.{u}) : Label.{u}) :=
      WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr one_lt_two)
    intro b
    cases b
    · rw [stepSuppressor_of_le le_rfl, min_top_right]
      exact (reduce_of_lt h12).symm
    · rw [stepSuppressor_of_le le_rfl, min_top_right]
      exact (reduce_of_le le_rfl).symm

/-- The labels `(1, ⊤)`, at grade one, transform to `(⊥, ⊤)`. -/
private theorem TransformsTo.one_top_bot_top :
    TransformsTo (fun _ : Bool ↦ 1)
      (fun b ↦ if b then ⊤ else ((1 : Ordinal.{u}) : Label.{u}))
      (fun b ↦ if b then ⊤ else ⊥) := by
  classical
  refine ⟨fun _ ↦ ⊤, fun x ↦ if x = ⊤ then ⊤ else ⊥, ⟨antitone_const,
    fun _ ↦ isSelfVisible_top _, by simp, fun x y hxy ↦ ?_, fun x k _ i _ ↦ ?_⟩, ?_⟩
  · split_ifs with hx hy <;> simp_all
  · by_cases hx : x = ⊤ <;> simp [hx]
  · intro b
    cases b
    · have h1 : ((1 : Ordinal.{u}) : Label.{u}) ≠ ⊤ :=
        (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top (1 : Ordinal.{u}))).ne
      simp only [Bool.false_eq_true, ↓reduceIte, h1, min_top_right]
    · simp

/-- The sources `(1, 2)`, at grade one, do not transform to `(⊥, ⊤)`: a shifter sending `1` to
`⊥` must send the visibility replacement `2` of `1` to `⊥` as well. -/
private theorem TransformsTo.not_one_two_bot_top :
    ¬ TransformsTo (fun _ : Bool ↦ 1)
      (fun b ↦ ((if b then 2 else 1 : Ordinal.{u}) : Label.{u}))
      (fun b ↦ if b then ⊤ else ⊥) := by
  rintro ⟨g, τ, hw, heq⟩
  have h₁ := heq false
  have h₂ := heq true
  simp only [Bool.false_eq_true, ↓reduceIte] at h₁ h₂
  have hg : g 1 = ⊤ := top_le_iff.mp (h₂.le.trans (min_le_right _ _))
  rw [hg, min_top_right] at h₁ h₂
  have h := hw.visibilityReplace_comm _ 2 (h₁ ▸ bot_le) 2 le_rfl
  have h12 : Ordinal.visibilityReplace 2 2 (1 : Ordinal.{u}) = 2 := by simp
  rw [visibilityReplace_coe, h12, ← h₁, visibilityReplace_bot, ← h₂] at h
  exact top_ne_bot h

/-- The three labellings of the nontransitivity example are self-visible at grade one. -/
private theorem isSelfVisible_one_two_one_top_bot_top (b : Bool) :
    IsSelfVisible 1 ((if b then 2 else 1 : Ordinal.{u}) : Label.{u}) ∧
      IsSelfVisible 1 (if b then ⊤ else ((1 : Ordinal.{u}) : Label.{u})) ∧
      IsSelfVisible 1 (if b then (⊤ : Label.{u}) else ⊥) := by
  cases b <;> simp

/-- **The transformation relation is not transitive**, even on labellings that are self-visible
at the grade, and already for two cells of grade one.  This contradicts [Kni26, Lemma 2.3.14] as
printed; the library proves only the guarded composition `IsWitness.comp_of_bot_reflecting`. -/
theorem TransformsTo.not_transitive :
    ¬ ∀ (grade : Bool → ℕ) (p q r : Bool → Label.{u}), (∀ d, IsSelfVisible (grade d) (p d)) →
      (∀ d, IsSelfVisible (grade d) (q d)) → (∀ d, IsSelfVisible (grade d) (r d)) →
      TransformsTo grade p q → TransformsTo grade q r → TransformsTo grade p r :=
  fun h ↦ not_one_two_bot_top (h _ _ _ _ (fun b ↦ (isSelfVisible_one_two_one_top_bot_top b).1)
    (fun b ↦ (isSelfVisible_one_two_one_top_bot_top b).2.1)
    (fun b ↦ (isSelfVisible_one_two_one_top_bot_top b).2.2) one_two_one_top one_top_bot_top)

end Nontransitive

end VaughtConjecture.Label
