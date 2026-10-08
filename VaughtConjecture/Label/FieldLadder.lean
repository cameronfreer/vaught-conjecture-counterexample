/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.BlockReading
import VaughtConjecture.Label.StepWitness

/-!
# The grade-one field ladder and reflection of the bottom label

Roadmap, Layer 3 ((R3) and (R4), the recognition of admitted states in a growth carrier).

A **field ladder** of height `H` is a table of grade-one rows on rungs `0, …, H - 1` and on
shadows (one per stored field).  The row of the rung `i` reads the codes
`Label.ladderSource (i + 1) j` of the ranks `j`; its **diagonal** `ladderSource t t` (`t ≥ 2`) lies
in the same block as the code `ladderSource t (t - 1)` of the preceding rank, one finite step
above it (`Label.ladderSource_diag`).  Every code is self-visible at the grade `1`
(`Label.isSelfVisible_ladderSource`), and the code of the rank `0` is `⊥`.

**Reflection of the bottom label.**  The zero set of a witness is closed under visibility
replacement, so locality at the rung `i` carries `⊥` from the rung `i - 1` to the rung `i`
(`Label.eq_bot_of_ladder_predecessor`).  Hence in every labelling local at the rungs, a positive top
rung makes every rung positive (`Label.ladder_ne_bot`), and the chart of the top rung (its witness)
is positive at every positive rank (`Label.ladder_chart_ne_bot`): it reflects `⊥` on the codes, so
a shadow read below the top rung is `⊥` exactly when its rank is `0`
(`Label.ladder_shadow_eq_bot_iff`).  A stored field of rank `0` is a field labelled `⊥`; so the
chart of the top rung reflects `⊥` on the stored fields.

**The table** (`Label.ladderRow`, `Label.LadderLawful`): the row of a cell reads the codes, at its
ceiling, of the ceilings of all cells.  Its rows are lawful on it (`Label.ladderLawful_row`), every
positive table read at the ceilings is lawful on it (`Label.ladderLawful_image`, through the chart
`Label.ladderChart` of `Label.transformsTo_ladderSource`), and every lawful labelling with a
positive top rung is read by the chart of its top rung with `⊥` exactly at the ceiling `0`
(`Label.LadderLawful.reflects`).  With several members (the cut `Label.rankCut` of their rank
vectors caps the indices, `Label.ladderIndex`), every lawful labelling is `⊥` or the chart image of
the table of the member with the largest top rung, `⊥` exactly at its index `0`
(`Label.LadderLawful.exists_shape`).

## References

The witnesses and visibility replacement are [Kni26, Definitions 2.2.3 and 2.3.9].
-/

universe u

namespace VaughtConjecture.Label

open Ordinal

/-- The **code of the rank `i`** in the row of a rung of ceiling `t`: `⊥` at the rank `0`; at the
diagonal `i ≥ t ≥ 2` the block `t - 1` at the finite part `3`; otherwise the block `min i t` at the
finite part `2`. -/
noncomputable def ladderSource (t i : ℕ) : Label.{u} :=
  if min i t = 0 then ⊥
  else if 2 ≤ t ∧ t ≤ i then ((ω * ((t - 1 : ℕ) : Ordinal.{u}) + ((3 : ℕ) : Ordinal.{u}) :
    Ordinal.{u}) : Label.{u})
  else ((ω * ((min i t : ℕ) : Ordinal.{u}) + ((2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})

theorem isSuccPrelimit_omega0_mul' (b : Ordinal.{u}) : Order.IsSuccPrelimit (ω * b) :=
  isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right ω b)

@[simp] theorem ladderSource_zero (t : ℕ) : ladderSource.{u} t 0 = ⊥ := by
  simp [ladderSource]

theorem ladderSource_eq_bot_iff (t i : ℕ) : ladderSource.{u} t i = ⊥ ↔ min i t = 0 := by
  unfold ladderSource
  split_ifs with h0 h1
  · simp [h0]
  · simp only [h0, iff_false]; exact WithBot.coe_ne_bot
  · simp only [h0, iff_false]; exact WithBot.coe_ne_bot

/-- Every code is self-visible at the grade `1`. -/
theorem isSelfVisible_ladderSource (t i : ℕ) : IsSelfVisible 1 (ladderSource.{u} t i) := by
  unfold ladderSource
  split_ifs
  · exact isSelfVisible_bot _
  · exact (isSelfVisible_coe_add_natCast_iff (isSuccPrelimit_omega0_mul' _)).mpr (by omega)
  · exact (isSelfVisible_coe_add_natCast_iff (isSuccPrelimit_omega0_mul' _)).mpr (by omega)

/-- **The diagonal lies one finite step above the preceding rank, in its block.** -/
theorem ladderSource_diag {t : ℕ} (ht : 2 ≤ t) :
    ladderSource.{u} t t = visibilityReplace 3 3 (ladderSource t (t - 1)) := by
  have h1 : min (t - 1) t = t - 1 := min_eq_left (Nat.sub_le t 1)
  have h2 : ¬ min (t - 1) t = 0 := by omega
  have h3 : ¬ (2 ≤ t ∧ t ≤ t - 1) := by omega
  have h4 : ¬ min t t = 0 := by omega
  have h5 : 2 ≤ t ∧ t ≤ t := ⟨ht, le_rfl⟩
  unfold ladderSource
  rw [ite_eq_right h4, ite_eq_left h5, ite_eq_right h2, ite_eq_right h3, h1,
    visibilityReplace_coe_add_natCast (isSuccPrelimit_omega0_mul' _) (by omega : 2 < 3)]

/-- The zero set of a witness is closed under visibility replacement. -/
theorem IsWitness.eq_bot_visibilityReplace {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}
    (hw : IsWitness g σ) {x : Label.{u}} (hx : σ x = ⊥) {k i : ℕ} (hi : i ≤ k) :
    σ (visibilityReplace k i x) = ⊥ := by
  rw [hw.visibilityReplace_comm x k (hx ▸ bot_le) i hi, hx, visibilityReplace_bot]

/-- **The predecessor step**: under locality at a rung `c` of ceiling `t ≥ 2`, whose row reads the
diagonal at `c` and the preceding rank at `d`, if `d` is `⊥` then so is `c`. -/
theorem eq_bot_of_ladder_predecessor {D : Type*} {row q : D → Label.{u}} {c d : D} {t : ℕ}
    (ht : 2 ≤ t) (hloc : TransformsTo (fun _ ↦ 1) row (fun v ↦ min (q v) (q c)))
    (hrc : row c = ladderSource t t) (hrd : row d = ladderSource t (t - 1)) (hd : q d = ⊥) :
    q c = ⊥ := by
  obtain ⟨g, σ, hw, hq⟩ := hloc
  have hqd := hq d
  have hqc := hq c
  simp only [hd, min_eq_left bot_le, min_self] at hqd hqc
  rw [hrd] at hqd
  rw [hqc, hrc]
  rcases min_eq_bot.mp hqd.symm with h | h
  · rw [ladderSource_diag ht, hw.eq_bot_visibilityReplace h (le_refl 3)]
    exact min_eq_left bot_le
  · rw [h, min_eq_right bot_le]

/-- **A positive top rung makes every rung positive**: in a labelling local at every rung `r i`
(`i < H`), whose row reads the diagonal at `r i` and the preceding rank at `r (i - 1)`. -/
theorem ladder_ne_bot {D : Type*} (row : D → D → Label.{u}) (q : D → Label.{u}) (r : ℕ → D)
    {H : ℕ} (hloc : ∀ i < H, TransformsTo (fun _ ↦ 1) (row (r i)) (fun v ↦ min (q v) (q (r i))))
    (hdiag : ∀ i < H, row (r i) (r i) = ladderSource (i + 1) (i + 1))
    (hpred : ∀ i < H, 0 < i → row (r i) (r (i - 1)) = ladderSource (i + 1) i)
    (htop : q (r (H - 1)) ≠ ⊥) : ∀ i < H, q (r i) ≠ ⊥ := by
  intro i hi h0
  have key : ∀ m, i + m < H → q (r (i + m)) = ⊥ := by
    intro m
    induction m with
    | zero => intro _; simpa using h0
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      have h1 := hdiag (i + (m + 1)) hm
      have h2 := hpred (i + (m + 1)) hm (by omega)
      have hsub : i + (m + 1) - 1 = i + m := by omega
      rw [hsub] at h2
      have h3 : ladderSource (i + (m + 1) + 1) (i + (m + 1)) =
          ladderSource (i + (m + 1) + 1) (i + (m + 1) + 1 - 1) := by
        congr 1
      exact eq_bot_of_ladder_predecessor (t := i + (m + 1) + 1) (by omega)
        (hloc _ hm) h1 (h2.trans h3) hprev
  apply htop
  have := key (H - 1 - i) (by omega)
  rwa [show i + (H - 1 - i) = H - 1 by omega] at this

/-- **The chart of the top rung reflects `⊥` on the codes of the positive ranks**: if the top rung
`r (H - 1)` is positive and its chart `(g, σ)` reads every rung `r j` (below the top rung) through
the codes `ladderSource H (j + 1)`, then `σ` is positive at each of them. -/
theorem ladder_chart_ne_bot {D : Type*} (row : D → D → Label.{u}) (q : D → Label.{u})
    (r : ℕ → D) {H : ℕ}
    (hloc : ∀ i < H, TransformsTo (fun _ ↦ 1) (row (r i)) (fun v ↦ min (q v) (q (r i))))
    (hdiag : ∀ i < H, row (r i) (r i) = ladderSource (i + 1) (i + 1))
    (hpred : ∀ i < H, 0 < i → row (r i) (r (i - 1)) = ladderSource (i + 1) i)
    (htop : q (r (H - 1)) ≠ ⊥) {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}
    (hchart : ∀ v, min (q v) (q (r (H - 1))) = min (σ (row (r (H - 1)) v)) (g 1))
    (hleaf : ∀ j < H, row (r (H - 1)) (r j) = ladderSource H (j + 1)) :
    ∀ j < H, σ (ladderSource H (j + 1)) ≠ ⊥ ∧ g 1 ≠ ⊥ := by
  intro j hj
  have hpos := ladder_ne_bot row q r hloc hdiag hpred htop j hj
  have h := hchart (r j)
  rw [hleaf j hj] at h
  have hne : min (q (r j)) (q (r (H - 1))) ≠ ⊥ := by
    intro h0
    rcases min_eq_bot.mp h0 with h' | h'
    · exact hpos h'
    · exact htop h'
  rw [h] at hne
  exact ⟨fun h0 ↦ hne (by rw [h0, min_eq_left bot_le]),
    fun h0 ↦ hne (by rw [h0, min_eq_right bot_le])⟩

/-- **Reflection of `⊥` on the stored fields**: with a positive top rung, a shadow `s` read by the
chart of the top rung through the code of its rank `k ≤ H` is `⊥` below the top rung exactly when
its rank is `0`. -/
theorem ladder_shadow_eq_bot_iff {D : Type*} (row : D → D → Label.{u}) (q : D → Label.{u})
    (r : ℕ → D) {H : ℕ}
    (hloc : ∀ i < H, TransformsTo (fun _ ↦ 1) (row (r i)) (fun v ↦ min (q v) (q (r i))))
    (hdiag : ∀ i < H, row (r i) (r i) = ladderSource (i + 1) (i + 1))
    (hpred : ∀ i < H, 0 < i → row (r i) (r (i - 1)) = ladderSource (i + 1) i)
    (htop : q (r (H - 1)) ≠ ⊥) {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}
    (hw : IsWitness g σ)
    (hchart : ∀ v, min (q v) (q (r (H - 1))) = min (σ (row (r (H - 1)) v)) (g 1))
    (hleaf : ∀ j < H, row (r (H - 1)) (r j) = ladderSource H (j + 1))
    {s : D} {k : ℕ} (hk : k ≤ H) (hs : row (r (H - 1)) s = ladderSource H k) :
    min (q s) (q (r (H - 1))) = ⊥ ↔ k = 0 := by
  rw [hchart, hs]
  constructor
  · intro h0
    by_contra hk0
    obtain ⟨h1, h2⟩ := ladder_chart_ne_bot row q r hloc hdiag hpred htop hchart hleaf (k - 1)
      (by omega)
    rw [show k - 1 + 1 = k by omega] at h1
    rcases min_eq_bot.mp h0 with h | h
    · exact h1 h
    · exact h2 h
  · rintro rfl
    rw [ladderSource_zero, hw.map_bot, min_eq_left bot_le]

/-! ### The order of the codes -/

theorem ladderSource_block_lt {a b : ℕ} (h : a < b) (r s : ℕ) :
    ω * (a : Ordinal.{u}) + (r : Ordinal.{u}) < ω * (b : Ordinal.{u}) + (s : Ordinal.{u}) := by
  calc ω * (a : Ordinal.{u}) + (r : Ordinal.{u}) < ω * (a : Ordinal.{u}) + ω :=
        (add_lt_add_iff_left _).mpr (natCast_lt_omega0 r)
    _ = ω * ((a : Ordinal.{u}) + 1) := by rw [mul_add, mul_one]
    _ ≤ ω * (b : Ordinal.{u}) := mul_le_mul_right (by exact_mod_cast Nat.succ_le_of_lt h) _
    _ ≤ ω * (b : Ordinal.{u}) + (s : Ordinal.{u}) := le_self_add

/-- The codes depend on the rank only up to the ceiling. -/
theorem ladderSource_min (t i : ℕ) : ladderSource.{u} t (min i t) = ladderSource t i := by
  simp only [ladderSource, min_assoc, min_self, le_min_iff, le_refl, and_true]

/-- **The codes of the positive ranks up to the ceiling increase strictly.** -/
theorem ladderSource_lt {t m m' : ℕ} (h1 : 1 ≤ m) (hmm : m < m') (hm' : m' ≤ t) :
    ladderSource.{u} t m < ladderSource t m' := by
  have hm0 : ¬ min m t = 0 := by omega
  have hm'0 : ¬ min m' t = 0 := by omega
  have hnd : ¬ (2 ≤ t ∧ t ≤ m) := by omega
  have hmin : min m t = m := min_eq_left (by omega)
  have hmin' : min m' t = m' := min_eq_left hm'
  unfold ladderSource
  rw [ite_eq_right hm0, ite_eq_right hm'0, ite_eq_right hnd, hmin, hmin']
  split_ifs with hd
  · rw [Label.coe_lt_coe_iff]
    rcases Nat.lt_or_ge m (t - 1) with hlt | hge
    · exact ladderSource_block_lt hlt 2 3
    · have : m = t - 1 := by omega
      subst this
      exact (add_lt_add_iff_left _).mpr (by exact_mod_cast (by omega : 2 < 3))
  · rw [Label.coe_lt_coe_iff]
    exact ladderSource_block_lt hmm 2 2

/-- **The order of the codes**: for a positive rank `m ≤ t`, the code of `m` is at most the code
of `i` exactly when `m ≤ min i t`. -/
theorem ladderSource_le_iff {t m : ℕ} (h1 : 1 ≤ m) (hmt : m ≤ t) (i : ℕ) :
    ladderSource.{u} t m ≤ ladderSource t i ↔ m ≤ min i t := by
  rw [← ladderSource_min t i]
  set i' := min i t with hi'
  have hi't : i' ≤ t := min_le_right _ _
  rcases Nat.lt_trichotomy m i' with h | h | h
  · exact ⟨fun _ ↦ h.le, fun _ ↦ (ladderSource_lt h1 h hi't).le⟩
  · subst h; exact ⟨fun _ ↦ le_rfl, fun _ ↦ le_rfl⟩
  · refine ⟨fun hle ↦ ?_, fun hle ↦ absurd hle (not_le.mpr h)⟩
    rcases Nat.eq_zero_or_pos i' with h0 | hpos
    · rw [h0, ladderSource_zero, le_bot_iff, ladderSource_eq_bot_iff] at hle
      omega
    · exact absurd hle (not_le.mpr (ladderSource_lt hpos h hmt))

/-- The codes are monotone in the rank. -/
theorem monotone_ladderSource (t : ℕ) : Monotone (ladderSource.{u} t) := by
  intro i j hij
  rcases Nat.eq_zero_or_pos (min i t) with h0 | hpos
  · rw [(ladderSource_eq_bot_iff t i).mpr h0]; exact bot_le
  · rw [← ladderSource_min t i]
    exact (ladderSource_le_iff hpos (min_le_right _ _) j).mpr (min_le_min_right _ hij)

/-- Every code is self-visible at the grade `2`. -/
theorem isSelfVisible_two_ladderSource (t i : ℕ) : IsSelfVisible 2 (ladderSource.{u} t i) := by
  unfold ladderSource
  split_ifs
  · exact isSelfVisible_bot _
  · exact (isSelfVisible_coe_add_natCast_iff (isSuccPrelimit_omega0_mul' _)).mpr (by omega)
  · exact (isSelfVisible_coe_add_natCast_iff (isSuccPrelimit_omega0_mul' _)).mpr (by omega)

/-- A positive code is at least `ω`. -/
theorem omega0_le_ladderSource {t i : ℕ} (h : min i t ≠ 0) :
    ((ω : Ordinal.{u}) : Label.{u}) ≤ ladderSource t i := by
  unfold ladderSource
  rw [ite_eq_right h]
  split_ifs with hd
  · rw [Label.coe_le_coe_iff]
    calc (ω : Ordinal.{u}) = ω * ((1 : ℕ) : Ordinal.{u}) := by simp
      _ ≤ ω * ((t - 1 : ℕ) : Ordinal.{u}) := mul_le_mul_right (by exact_mod_cast (by omega)) _
      _ ≤ _ := le_self_add
  · rw [Label.coe_le_coe_iff]
    calc (ω : Ordinal.{u}) = ω * ((1 : ℕ) : Ordinal.{u}) := by simp
      _ ≤ ω * ((min i t : ℕ) : Ordinal.{u}) :=
          mul_le_mul_right (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h) _
      _ ≤ _ := le_self_add

/-! ### The chart of a positive table -/

/-- The number of positive ranks up to `t` whose code is at most `x`. -/
noncomputable def ladderCount (t : ℕ) (x : Label.{u}) : ℕ :=
  ((Finset.range t).filter fun m ↦ ladderSource.{u} t (m + 1) ≤ x).card

theorem ladderCount_le (t : ℕ) (x : Label.{u}) : ladderCount t x ≤ t :=
  (Finset.card_filter_le _ _).trans (by simp)

theorem monotone_ladderCount (t : ℕ) : Monotone (ladderCount.{u} t) := fun _ _ hxy ↦
  Finset.card_le_card fun m hm ↦ by
    simp only [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, hm.2.trans hxy⟩

/-- The count at a code is its rank up to the ceiling. -/
theorem ladderCount_ladderSource (t i : ℕ) : ladderCount t (ladderSource.{u} t i) = min i t := by
  have h : ((Finset.range t).filter fun m ↦ ladderSource.{u} t (m + 1) ≤ ladderSource t i) =
      Finset.range (min i t) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hmt, hle⟩
      have := (ladderSource_le_iff (by omega) (by omega) i).mp hle
      omega
    · intro hm
      refine ⟨by omega, (ladderSource_le_iff (by omega) (by omega) i).mpr (by omega)⟩
  rw [ladderCount, h, Finset.card_range]

/-- The count is unchanged by visibility replacement at a threshold at most `1`. -/
theorem ladderCount_visibilityReplace {k i : ℕ} (hk : k ≤ 1) (hi : i ≤ k) (t : ℕ)
    (x : Label.{u}) : ladderCount t (visibilityReplace k i x) = ladderCount t x := by
  unfold ladderCount
  congr 1
  exact Finset.filter_congr fun m _ ↦
    (isSelfVisible_two_ladderSource t (m + 1)).le_visibilityReplace_iff hk hi x

/-- Visibility replacement keeps a label below `ω` exactly when it was below. -/
theorem visibilityReplace_lt_omega0_iff (k i : ℕ) (x : Label.{u}) :
    visibilityReplace k i x < ((ω : Ordinal.{u}) : Label.{u}) ↔
      x < ((ω : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => simp
  | top => simp
  | coe o =>
    rw [visibilityReplace_coe, coe_lt_coe_iff, coe_lt_coe_iff]
    exact Ordinal.visibilityReplace_lt_iff isSuccLimit_omega0.isSuccPrelimit k i

/-- **The chart of a positive table** `f` at the ceiling `t`: `⊥` below `ω`, and above it `f` at
the number of codes below, at least `1`. -/
noncomputable def ladderChart (t : ℕ) (f : ℕ → Label.{u}) (x : Label.{u}) : Label.{u} :=
  if x < ((ω : Ordinal.{u}) : Label.{u}) then ⊥ else f (max 1 (ladderCount t x))

/-- **A positive table is the image of the codes under a witness** at the grade `1`: for `f`
monotone, `⊥` at `0`, self-visible at `1` and positive at the ranks `1, …, t`, the codes of any
ranks `a` transform to the table `f` at those ranks capped at `t`. -/
theorem transformsTo_ladderSource {D : Type*} (a : D → ℕ) {t : ℕ} (ht : 1 ≤ t)
    {f : ℕ → Label.{u}} (hf : Monotone f) (h0 : f 0 = ⊥) (hv : ∀ i, IsSelfVisible 1 (f i))
    (hp : ∀ i, 0 < i → i ≤ t → f i ≠ ⊥) :
    TransformsTo (fun _ ↦ 1) (fun d ↦ ladderSource t (a d)) (fun d ↦ f (min (a d) t)) := by
  have hpos (x : Label.{u}) : f (max 1 (ladderCount t x)) ≠ ⊥ :=
    hp _ (by omega) (max_le ht (ladderCount_le t x))
  have hzero (x : Label.{u}) : ladderChart t f x = ⊥ ↔ x < ((ω : Ordinal.{u}) : Label.{u}) := by
    unfold ladderChart
    split_ifs with hx
    · exact ⟨fun _ ↦ hx, fun _ ↦ rfl⟩
    · exact ⟨fun h ↦ absurd h (hpos x), fun h ↦ absurd h hx⟩
  refine ⟨stepSuppressor 1, ladderChart t f, ⟨(IsWitness.id_step 1).antitone,
    (IsWitness.id_step 1).isSelfVisible, by simp [ladderChart], fun x y hxy ↦ ?_,
    fun x k hg i hi ↦ ?_⟩, fun d ↦ ?_⟩
  · unfold ladderChart
    by_cases hx : x < ((ω : Ordinal.{u}) : Label.{u})
    · rw [ite_eq_left hx]; exact bot_le
    · have hy : ¬ y < ((ω : Ordinal.{u}) : Label.{u}) := fun hy ↦ hx (lt_of_le_of_lt hxy hy)
      rw [ite_eq_right hx, ite_eq_right hy]
      exact hf (max_le_max le_rfl (monotone_ladderCount t hxy))
  · by_cases hk : k ≤ 1
    · have hlt := visibilityReplace_lt_omega0_iff k i x
      unfold ladderChart
      by_cases hx : x < ((ω : Ordinal.{u}) : Label.{u})
      · rw [ite_eq_left (hlt.mpr hx), ite_eq_left hx, visibilityReplace_bot]
      · rw [ite_eq_right (mt hlt.mp hx), ite_eq_right hx, ladderCount_visibilityReplace hk hi,
          ((hv _).mono hk).visibilityReplace_eq]
    · rw [stepSuppressor_of_lt (by omega), le_bot_iff] at hg
      have hx := (hzero x).mp hg
      rw [hg, visibilityReplace_bot, hzero]
      exact (visibilityReplace_lt_omega0_iff k i x).mpr hx
  · simp only [stepSuppressor_of_le le_rfl, min_top_right]
    by_cases h : min (a d) t = 0
    · rw [h, h0, (ladderSource_eq_bot_iff t (a d)).mpr h]
      exact ((hzero ⊥).mpr (WithBot.bot_lt_coe _)).symm
    · unfold ladderChart
      rw [ite_eq_right (not_lt.mpr (omega0_le_ladderSource h)), ladderCount_ladderSource,
        max_eq_right (Nat.one_le_iff_ne_zero.mpr h)]

/-! ### Agreement of rank vectors -/

section Cut

variable {X : Type*}

/-- Two rank vectors **agree up to `k`**: equal at every field capped at `k`. -/
def RankAgree (a b : X → ℕ) (k : ℕ) : Prop := ∀ d, min (a d) k = min (b d) k

theorem RankAgree.mono {a b : X → ℕ} {k l : ℕ} (h : RankAgree a b k) (hl : l ≤ k) :
    RankAgree a b l := fun d ↦ by
  have hh := congrArg (fun z ↦ min z l) (h d)
  simpa only [min_assoc, min_eq_right hl] using hh

open Classical in
/-- The **cut** of two rank vectors at the height `H`: the largest `k ≤ H` up to which they
agree. -/
noncomputable def rankCut (H : ℕ) (a b : X → ℕ) : ℕ :=
  ((Finset.range (H + 1)).filter (RankAgree a b)).sup id

theorem rankCut_le (H : ℕ) (a b : X → ℕ) : rankCut H a b ≤ H := by
  classical
  refine Finset.sup_le fun k hk ↦ ?_
  exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)

theorem le_rankCut {H k : ℕ} {a b : X → ℕ} (hk : k ≤ H) (h : RankAgree a b k) :
    k ≤ rankCut H a b := by
  classical
  exact Finset.le_sup (f := id)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hk), h⟩)

theorem rankAgree_rankCut (H : ℕ) (a b : X → ℕ) : RankAgree a b (rankCut H a b) := by
  classical
  have hn : ((Finset.range (H + 1)).filter (RankAgree a b)).Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨by simp, fun _ ↦ by simp⟩⟩
  obtain ⟨k, hk, he⟩ := Finset.sup_mem_of_nonempty (f := id) hn
  have ha := (Finset.mem_filter.mp hk).2
  change k = rankCut H a b at he
  exact he ▸ ha

theorem rankCut_symm (H : ℕ) (a b : X → ℕ) : rankCut H a b = rankCut H b a :=
  le_antisymm (le_rankCut (rankCut_le H a b) fun d ↦ (rankAgree_rankCut H a b d).symm)
    (le_rankCut (rankCut_le H b a) fun d ↦ (rankAgree_rankCut H b a d).symm)

theorem rankCut_self (H : ℕ) (a : X → ℕ) : rankCut H a a = H :=
  le_antisymm (rankCut_le H a a) (le_rankCut le_rfl fun _ ↦ rfl)

theorem rankCut_triangle (H : ℕ) (a b c : X → ℕ) :
    min (rankCut H a b) (rankCut H b c) ≤ rankCut H a c :=
  le_rankCut ((min_le_left _ _).trans (rankCut_le H a b)) fun d ↦
    ((rankAgree_rankCut H a b).mono (min_le_left _ _) d).trans
      ((rankAgree_rankCut H b c).mono (min_le_right _ _) d)

/-- The cut seen from two vectors agrees capped at their own cut. -/
theorem rankCut_cross (H : ℕ) (a b c : X → ℕ) :
    min (rankCut H a c) (rankCut H a b) = min (rankCut H b c) (rankCut H a b) := by
  have h1 := rankCut_triangle H a b c
  have h2 := rankCut_triangle H b a c
  rw [rankCut_symm H b a] at h2
  omega

end Cut

/-! ### The ladder table -/

section Table

variable {Q X D : Type*} (H : ℕ) (prof : Q → X → ℕ) (parent : D → Q) (ceil : D → ℕ)

/-- The **index** of a cell `v` for the member `a`: its ceiling, capped at the cut of the rank
vectors of `a` and of the parent of `v`. -/
noncomputable def ladderIndex (a : Q) (v : D) : ℕ :=
  min (rankCut H (prof a) (prof (parent v))) (ceil v)

/-- The **row** of a cell `c` of the ladder table: the codes, at the ceiling of `c`, of the
indices of the cells for the parent of `c`.  A rung `i` has ceiling `i + 1`; a shadow of a field
has the rank of the field in its parent. -/
noncomputable def ladderRow (c v : D) : Label.{u} :=
  ladderSource (ceil c) (ladderIndex H prof parent ceil (parent c) v)

/-- A labelling of the ladder table **lawful at the grade `1`**: self-visible at `1`, and local at
every cell with respect to its row. -/
def LadderLawful (q : D → Label.{u}) : Prop :=
  (∀ v, IsSelfVisible 1 (q v)) ∧
    ∀ c, TransformsTo (fun _ ↦ 1) (ladderRow.{u} H prof parent ceil c) fun v ↦ min (q v) (q c)

variable {H prof parent ceil}

theorem ladderIndex_le (a : Q) (v : D) : ladderIndex H prof parent ceil a v ≤ H :=
  (min_le_left _ _).trans (rankCut_le _ _ _)

/-- The indices for two members agree capped at the cut of their rank vectors. -/
theorem ladderIndex_agree (a b : Q) (v : D) :
    min (ladderIndex H prof parent ceil a v) (rankCut H (prof a) (prof b)) =
      min (ladderIndex H prof parent ceil b v) (rankCut H (prof a) (prof b)) := by
  unfold ladderIndex
  have h := rankCut_cross H (prof a) (prof b) (prof (parent v))
  calc min (min (rankCut H (prof a) (prof (parent v))) (ceil v)) (rankCut H (prof a) (prof b))
      = min (min (rankCut H (prof a) (prof (parent v))) (rankCut H (prof a) (prof b)))
          (ceil v) := by ac_rfl
    _ = min (min (rankCut H (prof b) (prof (parent v))) (rankCut H (prof a) (prof b)))
          (ceil v) := by rw [h]
    _ = _ := by ac_rfl

/-- At its own parent a cell's index is its ceiling. -/
theorem ladderIndex_parent (hceil : ∀ v, ceil v ≤ H) (v : D) :
    ladderIndex H prof parent ceil (parent v) v = ceil v := by
  rw [ladderIndex, rankCut_self, min_eq_right (hceil v)]

/-- **Rendering**: a positive table `f` read at the indices of a member `a` is lawful on the
ladder table. -/
theorem ladderLawful_image (a : Q) {f : ℕ → Label.{u}}
    (hf : Monotone f) (h0 : f 0 = ⊥) (hv : ∀ i, IsSelfVisible 1 (f i))
    (hp : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥) :
    LadderLawful H prof parent ceil fun v ↦ f (ladderIndex H prof parent ceil a v) := by
  refine ⟨fun v ↦ hv _, fun c ↦ ?_⟩
  set e := ladderIndex H prof parent ceil a c with he
  have hec : e ≤ ceil c := min_le_right _ _
  have hecut : e ≤ rankCut H (prof a) (prof (parent c)) := min_le_left _ _
  have hmin (v : D) : min (ladderIndex H prof parent ceil a v) e =
      min (ladderIndex H prof parent ceil (parent c) v) e := by
    rw [← min_eq_right hecut, ← min_assoc, ladderIndex_agree a (parent c) v, min_assoc]
  have hfun : (fun v ↦ min (f (ladderIndex H prof parent ceil a v)) (f e)) =
      fun v ↦ f (min (min (ladderIndex H prof parent ceil (parent c) v) (ceil c)) e) := by
    funext v
    rw [← hf.map_min, hmin, min_assoc, min_eq_right hec]
  rw [hfun]
  by_cases he0 : e = 0
  · have hz : (fun v ↦ f (min (min (ladderIndex H prof parent ceil (parent c) v) (ceil c)) e)) =
        fun _ ↦ (⊥ : Label.{u}) := by funext v; rw [he0, Nat.min_zero, h0]
    rw [hz]
    exact TransformsTo.bot _ _
  · exact transformsTo_ladderSource (ladderIndex H prof parent ceil (parent c)) (t := ceil c)
      (by omega) (f := fun i ↦ f (min i e)) (fun _ _ h ↦ hf (min_le_min_right _ h)) (by simp [h0])
      (fun _ ↦ hv _) fun i hi _ ↦ hp _ (by omega) ((min_le_right _ _).trans (ladderIndex_le a c))

/-- **Every row of the ladder table is lawful on the table**: the rows are consistent. -/
theorem ladderLawful_row (c : D) :
    LadderLawful.{u} H prof parent ceil (ladderRow H prof parent ceil c) := by
  by_cases hc : ceil c = 0
  · have he : ladderRow.{u} H prof parent ceil c = fun _ ↦ ⊥ := by
      funext v
      rw [ladderRow, (ladderSource_eq_bot_iff _ _).mpr (by rw [hc]; exact Nat.min_zero _)]
    rw [he]
    refine ⟨fun _ ↦ isSelfVisible_bot _, fun _ ↦ ?_⟩
    simp only [min_self]
    exact TransformsTo.bot _ _
  · exact ladderLawful_image (parent c) (monotone_ladderSource _) (ladderSource_zero _)
      (isSelfVisible_ladderSource _) fun i hi _ h0 ↦ by
        rw [ladderSource_eq_bot_iff] at h0
        omega

/-- **Reflection of `⊥` by the chart of a top rung.**  Let a member `a` have rungs `r i`
(`i < H`, `H ≥ 1`) of ceiling `i + 1`.  In every labelling lawful on the ladder table with a
positive top rung `r (H - 1)`, the chart `(g, σ)` of the top rung reads every cell `v` (below the
top rung) through the code of its index for `a`, and `v` is `⊥` below the top rung exactly when
that index is `0`. -/
theorem LadderLawful.reflects (hH : 0 < H) (hceil : ∀ v, ceil v ≤ H) (a : Q) (r : ℕ → D)
    (hpr : ∀ i < H, parent (r i) = a) (hr : ∀ i < H, ceil (r i) = i + 1) {q : D → Label.{u}}
    (hq : LadderLawful H prof parent ceil q) (htop : q (r (H - 1)) ≠ ⊥) :
    ∃ (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}), IsWitness g σ ∧
      (∀ v, min (q v) (q (r (H - 1))) =
        min (σ (ladderSource H (ladderIndex H prof parent ceil a v))) (g 1)) ∧
      ∀ v, min (q v) (q (r (H - 1))) = ⊥ ↔ ladderIndex H prof parent ceil a v = 0 := by
  obtain ⟨g, σ, hw, hch⟩ := hq.2 (r (H - 1))
  have htopc : ceil (r (H - 1)) = H := by rw [hr _ (by omega)]; omega
  have hidx (i : ℕ) (hi : i < H) : ladderIndex H prof parent ceil a (r i) = i + 1 := by
    rw [← hpr i hi, ladderIndex_parent hceil, hr i hi]
  have hrow (v : D) : ladderRow.{u} H prof parent ceil (r (H - 1)) v =
      ladderSource H (ladderIndex H prof parent ceil a v) := by
    rw [ladderRow, htopc, hpr _ (by omega)]
  have hchart (v : D) : min (q v) (q (r (H - 1))) =
      min (σ (ladderRow H prof parent ceil (r (H - 1)) v)) (g 1) := hch v
  refine ⟨g, σ, hw, fun v ↦ (hchart v).trans (by rw [hrow]), fun v ↦ ?_⟩
  exact ladder_shadow_eq_bot_iff (ladderRow H prof parent ceil) q r (fun i _ ↦ hq.2 (r i))
    (fun i hi ↦ by rw [ladderRow, hr i hi, hpr i hi, hidx i hi])
    (fun i hi hi0 ↦ by
      rw [ladderRow, hr i hi, hpr i hi, hidx (i - 1) (by omega)]
      congr 1; omega)
    htop hw hchart (fun j hj ↦ by rw [hrow, hidx j hj]) (ladderIndex_le a v) (hrow v)

/-- **Every cell lies below the top rung of its parent** in a lawful labelling: the row of a cell
reads the top rung of its parent as itself. -/
theorem LadderLawful.le_top (hceil : ∀ v, ceil v ≤ H) (top : Q → D)
    (hpt : ∀ a, parent (top a) = a) (htc : ∀ a, ceil (top a) = H) {q : D → Label.{u}}
    (hq : LadderLawful H prof parent ceil q) (c : D) : q c ≤ q (top (parent c)) := by
  obtain ⟨g, σ, -, hr⟩ := hq.2 c
  have he : ladderRow.{u} H prof parent ceil c (top (parent c)) =
      ladderRow H prof parent ceil c c := by
    rw [ladderRow, ladderRow, ladderIndex_parent hceil, ladderIndex, hpt, rankCut_self, htc,
      min_self, ← ladderSource_min (ceil c) H, min_eq_right (hceil c)]
  have h1 := hr (top (parent c))
  have h2 := hr c
  simp only [min_self] at h2
  rw [he, ← h2] at h1
  exact min_eq_right_iff.mp h1

/-- **Recognition on the ladder table**: every labelling lawful on the table is `⊥`, or for the
member `a` with the largest top rung it is the image, under the chart `(g, σ)` of that top rung, of
the codes of the indices for `a`, with `⊥` exactly at the index `0`.  The members have rungs
`r a i` of ceiling `i + 1` (`i < H`, `H ≥ 1`). -/
theorem LadderLawful.exists_shape [Finite Q] [Nonempty Q] (hH : 0 < H)
    (hceil : ∀ v, ceil v ≤ H) (r : Q → ℕ → D) (hpr : ∀ a, ∀ i < H, parent (r a i) = a)
    (hr : ∀ a, ∀ i < H, ceil (r a i) = i + 1) {q : D → Label.{u}}
    (hq : LadderLawful H prof parent ceil q) :
    (∀ v, q v = ⊥) ∨ ∃ (a : Q) (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}),
      IsWitness g σ ∧
      (∀ v, q v = min (σ (ladderSource H (ladderIndex H prof parent ceil a v))) (g 1)) ∧
      ∀ v, q v = ⊥ ↔ ladderIndex H prof parent ceil a v = 0 := by
  have := Fintype.ofFinite Q
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ (fun a : Q ↦ q (r a (H - 1)))
    Finset.univ_nonempty
  have hdom (v : D) : q v ≤ q (r a (H - 1)) :=
    (hq.le_top hceil (fun b ↦ r b (H - 1)) (fun b ↦ hpr b _ (by omega))
      (fun b ↦ by rw [hr b _ (by omega)]; omega) v).trans (ha (parent v) (Finset.mem_univ _))
  by_cases htop : q (r a (H - 1)) = ⊥
  · exact Or.inl fun v ↦ le_bot_iff.mp (htop ▸ hdom v)
  obtain ⟨g, σ, hw, hch, hbot⟩ := hq.reflects hH hceil a (r a) (hpr a) (hr a) htop
  refine Or.inr ⟨a, g, σ, hw, fun v ↦ ?_, fun v ↦ ?_⟩
  · rw [← hch v, min_eq_left (hdom v)]
  · rw [← hbot v, min_eq_left (hdom v)]

end Table

end VaughtConjecture.Label
