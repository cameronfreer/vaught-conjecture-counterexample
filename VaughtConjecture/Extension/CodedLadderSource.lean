/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Coding
import VaughtConjecture.Label.FieldLadder
import VaughtConjecture.Label.GradeOneInterpolation

/-!
# The strongly coded field ladder

Roadmap, Layer 3 ((R3) and (R4), the grade-one base of the recognizing growth carrier) and
Correspondence, item 1 (the strongly coded legal stage types).  All results here are native
constructions of this repository.

The codes of the field ladder (`Label.ladderSource`) use the finite parts `2` and `3`; the
diagonal `ladderSource t t = ω · (t - 1) + 3` of a rung of ceiling `t ≥ 2` is not strongly coded
at grade one (`Label.not_isStronglyCoded_ladderSource_diag`).  The **coded ladder source**
(`Label.codedLadderSource`) uses the finite parts `1` and `2` instead: at the ceiling `t` the rank
`0` reads `⊥`, a rank `1 ≤ i < t` reads `ω · i + 1`, and a rank `i ≥ t` reads the **diagonal**
`ω · (t - 1) + 2` when `t ≥ 2` (`ω + 1` when `t = 1`).  The diagonal lies in the block of the
preceding rank, one finite step above it.

* `Label.isStronglyCoded_codedLadderSource`: every code is strongly coded at every grade `k ≥ 1`
  (finite part at most `2 ≤ k + 1`, `Label.isStronglyCoded_coe_omega0_mul_add`).
* `Label.codedLadderSource_eq_bot_iff`, `Label.codedLadderSource_lt`,
  `Label.codedLadderSource_le_iff`, `Label.codedLadderSource_min`,
  `Label.codedLadderSource_diag`: the zero characterization, the strict order of the positive
  ranks up to the ceiling, truncation at the ceiling, and the shared block of the diagonal and the
  preceding rank (the diagonal is the replacement at the threshold `2` of the preceding code).
* `Label.transformsTo_codedLadderSource`: **rendering**.  The codes are self-visible at `1` only
  (not at `2`), so the chart of `Label.transformsTo_ladderSource` (which counts codes below its
  argument and needs that count to be invariant under replacement at the threshold `1`) does not
  apply.  The witness is order interpolation at the grade one
  (`Label.transformsTo_one_of_order`) on the finite family of the ranks up to the ceiling, pulled
  back along the capped rank.
* `Label.codedLadder_ne_bot`, `Label.codedLadder_shadow_eq_bot_iff`: **reflection of the bottom
  label** along the rungs, through the shared block of the diagonal.
* The coded ladder table (`Label.codedLadderRow`, `Label.CodedLadderLawful`), its rendering
  (`Label.codedLadderLawful_image`), consistency (`Label.codedLadderLawful_row`) and recognition
  (`Label.CodedLadderLawful.exists_shape`), with the indices `Label.ladderIndex` of the existing
  ladder table.

## References

Strong coding is the range of [Kni26, Lemma 2.5.13]; witnesses and visibility replacement are
[Kni26, Definitions 2.2.3 and 2.3.9].

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Label

open Ordinal

/-- The **coded ladder source** (native construction): the code of the rank `i` in the row of a
rung of ceiling `t`.  It is `⊥` at the rank `0`; at the diagonal `i ≥ t ≥ 2` the block `t - 1` at
the finite part `2`; otherwise the block `min i t` at the finite part `1`. -/
noncomputable def codedLadderSource (t i : ℕ) : Label.{u} :=
  if min i t = 0 then ⊥
  else if 2 ≤ t ∧ t ≤ i then ((ω * ((t - 1 : ℕ) : Ordinal.{u}) + ((2 : ℕ) : Ordinal.{u}) :
    Ordinal.{u}) : Label.{u})
  else ((ω * ((min i t : ℕ) : Ordinal.{u}) + ((1 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})

@[simp] theorem codedLadderSource_zero (t : ℕ) : codedLadderSource.{u} t 0 = ⊥ := by
  simp [codedLadderSource]

/-- **Zero characterization**: a code is `⊥` exactly when its rank, capped at the ceiling, is
`0`. -/
theorem codedLadderSource_eq_bot_iff (t i : ℕ) : codedLadderSource.{u} t i = ⊥ ↔ min i t = 0 := by
  unfold codedLadderSource
  split_ifs with h0 h1
  · simp [h0]
  · simp only [h0, iff_false]; exact WithBot.coe_ne_bot
  · simp only [h0, iff_false]; exact WithBot.coe_ne_bot

/-- A rank below the ceiling has the code `ω · i + 1`. -/
theorem codedLadderSource_of_lt {t i : ℕ} (hi : 1 ≤ i) (hit : i < t) :
    codedLadderSource.{u} t i = ((ω * (i : Ordinal.{u}) + 1 : Ordinal.{u}) : Label.{u}) := by
  have h0 : ¬ min i t = 0 := by omega
  have h1 : ¬ (2 ≤ t ∧ t ≤ i) := by omega
  unfold codedLadderSource
  rw [ite_eq_right h0, ite_eq_right h1, min_eq_left hit.le, Nat.cast_one]

/-- At a ceiling `t ≥ 2` the diagonal has the code `ω · (t - 1) + 2`. -/
theorem codedLadderSource_self {t : ℕ} (ht : 2 ≤ t) :
    codedLadderSource.{u} t t =
      ((ω * ((t - 1 : ℕ) : Ordinal.{u}) + 2 : Ordinal.{u}) : Label.{u}) := by
  have h0 : ¬ min t t = 0 := by omega
  unfold codedLadderSource
  rw [ite_eq_right h0, ite_eq_left ⟨ht, le_rfl⟩]
  rfl

/-- Every code is self-visible at the grade `1`. -/
theorem isSelfVisible_codedLadderSource (t i : ℕ) :
    IsSelfVisible 1 (codedLadderSource.{u} t i) := by
  unfold codedLadderSource
  split_ifs
  · exact isSelfVisible_bot _
  · exact (isSelfVisible_coe_add_natCast_iff (isSuccPrelimit_omega0_mul' _)).mpr (by omega)
  · exact (isSelfVisible_coe_add_natCast_iff (isSuccPrelimit_omega0_mul' _)).mpr (by omega)

/-- **Strong coding** (native construction): every code is strongly coded at every grade
`k ≥ 1`; its finite part is at most `2 ≤ k + 1`.  At the grade one this is the bound of
`CellScheme.Rows.IsStronglyCoded` for a row of grade one. -/
theorem isStronglyCoded_codedLadderSource {k : ℕ} (hk : 1 ≤ k) (t i : ℕ) :
    IsStronglyCoded k (codedLadderSource.{u} t i) := by
  unfold codedLadderSource
  split_ifs
  · exact isStronglyCoded_bot _
  · exact (isStronglyCoded_coe_omega0_mul_add k _ 2).mpr (by omega)
  · exact (isStronglyCoded_coe_omega0_mul_add k _ 1).mpr (by omega)

/-- The codes lie below `ω ^ 2`. -/
theorem codedLadderSource_lt_omega0_sq (t i : ℕ) :
    codedLadderSource.{u} t i < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) :=
  (isStronglyCoded_codedLadderSource le_rfl t i).lt_omega0_sq

/-- **The diagonal shares the block of the preceding rank**: it is the replacement at the
threshold `2` of the code of the preceding rank. -/
theorem codedLadderSource_diag {t : ℕ} (ht : 2 ≤ t) :
    codedLadderSource.{u} t t = visibilityReplace 2 2 (codedLadderSource t (t - 1)) := by
  rw [codedLadderSource_self ht, codedLadderSource_of_lt (by omega) (by omega)]
  have h := visibilityReplace_coe_add_natCast (n := 2) (k := 1)
    (isSuccPrelimit_omega0_mul' ((t - 1 : ℕ) : Ordinal.{u})) (by omega) 2
  simp only [Nat.cast_one, Nat.cast_ofNat] at h
  exact h.symm

/-- **The predecessor step**: under locality at a rung `c` of ceiling `t ≥ 2`, whose row reads the
diagonal at `c` and the preceding rank at `d`, if `d` is `⊥` then so is `c`. -/
theorem eq_bot_of_codedLadder_predecessor {D : Type*} {row q : D → Label.{u}} {c d : D} {t : ℕ}
    (ht : 2 ≤ t) (hloc : TransformsTo (fun _ ↦ 1) row (fun v ↦ min (q v) (q c)))
    (hrc : row c = codedLadderSource t t) (hrd : row d = codedLadderSource t (t - 1))
    (hd : q d = ⊥) : q c = ⊥ := by
  obtain ⟨g, σ, hw, hq⟩ := hloc
  have hqd := hq d
  have hqc := hq c
  simp only [hd, min_eq_left bot_le, min_self] at hqd hqc
  rw [hrd] at hqd
  rw [hqc, hrc]
  rcases min_eq_bot.mp hqd.symm with h | h
  · rw [codedLadderSource_diag ht, hw.eq_bot_visibilityReplace h (le_refl 2)]
    exact min_eq_left bot_le
  · rw [h, min_eq_right bot_le]

/-- **A positive top rung makes every rung positive**: in a labelling local at every rung `r i`
(`i < H`), whose row reads the diagonal at `r i` and the preceding rank at `r (i - 1)`. -/
theorem codedLadder_ne_bot {D : Type*} (row : D → D → Label.{u}) (q : D → Label.{u})
    (r : ℕ → D) {H : ℕ}
    (hloc : ∀ i < H, TransformsTo (fun _ ↦ 1) (row (r i)) (fun v ↦ min (q v) (q (r i))))
    (hdiag : ∀ i < H, row (r i) (r i) = codedLadderSource (i + 1) (i + 1))
    (hpred : ∀ i < H, 0 < i → row (r i) (r (i - 1)) = codedLadderSource (i + 1) i)
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
      have h3 : codedLadderSource (i + (m + 1) + 1) (i + (m + 1)) =
          codedLadderSource (i + (m + 1) + 1) (i + (m + 1) + 1 - 1) := by
        congr 1
      exact eq_bot_of_codedLadder_predecessor (t := i + (m + 1) + 1) (by omega)
        (hloc _ hm) h1 (h2.trans h3) hprev
  apply htop
  have := key (H - 1 - i) (by omega)
  rwa [show i + (H - 1 - i) = H - 1 by omega] at this

/-- **The chart of the top rung reflects `⊥` on the codes of the positive ranks**: if the top rung
`r (H - 1)` is positive and its chart `(g, σ)` reads every rung `r j` (below the top rung) through
the codes `codedLadderSource H (j + 1)`, then `σ` is positive at each of them. -/
theorem codedLadder_chart_ne_bot {D : Type*} (row : D → D → Label.{u}) (q : D → Label.{u})
    (r : ℕ → D) {H : ℕ}
    (hloc : ∀ i < H, TransformsTo (fun _ ↦ 1) (row (r i)) (fun v ↦ min (q v) (q (r i))))
    (hdiag : ∀ i < H, row (r i) (r i) = codedLadderSource (i + 1) (i + 1))
    (hpred : ∀ i < H, 0 < i → row (r i) (r (i - 1)) = codedLadderSource (i + 1) i)
    (htop : q (r (H - 1)) ≠ ⊥) {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}
    (hchart : ∀ v, min (q v) (q (r (H - 1))) = min (σ (row (r (H - 1)) v)) (g 1))
    (hleaf : ∀ j < H, row (r (H - 1)) (r j) = codedLadderSource H (j + 1)) :
    ∀ j < H, σ (codedLadderSource H (j + 1)) ≠ ⊥ ∧ g 1 ≠ ⊥ := by
  intro j hj
  have hpos := codedLadder_ne_bot row q r hloc hdiag hpred htop j hj
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
theorem codedLadder_shadow_eq_bot_iff {D : Type*} (row : D → D → Label.{u}) (q : D → Label.{u})
    (r : ℕ → D) {H : ℕ}
    (hloc : ∀ i < H, TransformsTo (fun _ ↦ 1) (row (r i)) (fun v ↦ min (q v) (q (r i))))
    (hdiag : ∀ i < H, row (r i) (r i) = codedLadderSource (i + 1) (i + 1))
    (hpred : ∀ i < H, 0 < i → row (r i) (r (i - 1)) = codedLadderSource (i + 1) i)
    (htop : q (r (H - 1)) ≠ ⊥) {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}
    (hw : IsWitness g σ)
    (hchart : ∀ v, min (q v) (q (r (H - 1))) = min (σ (row (r (H - 1)) v)) (g 1))
    (hleaf : ∀ j < H, row (r (H - 1)) (r j) = codedLadderSource H (j + 1))
    {s : D} {k : ℕ} (hk : k ≤ H) (hs : row (r (H - 1)) s = codedLadderSource H k) :
    min (q s) (q (r (H - 1))) = ⊥ ↔ k = 0 := by
  rw [hchart, hs]
  constructor
  · intro h0
    by_contra hk0
    obtain ⟨h1, h2⟩ := codedLadder_chart_ne_bot row q r hloc hdiag hpred htop hchart hleaf (k - 1)
      (by omega)
    rw [show k - 1 + 1 = k by omega] at h1
    rcases min_eq_bot.mp h0 with h | h
    · exact h1 h
    · exact h2 h
  · rintro rfl
    rw [codedLadderSource_zero, hw.map_bot, min_eq_left bot_le]

/-! ### The order of the codes -/

/-- **Ceiling truncation**: the codes depend on the rank only up to the ceiling. -/
theorem codedLadderSource_min (t i : ℕ) :
    codedLadderSource.{u} t (min i t) = codedLadderSource t i := by
  simp only [codedLadderSource, min_assoc, min_self, le_min_iff, le_refl, and_true]

/-- **The codes of the positive ranks up to the ceiling increase strictly.** -/
theorem codedLadderSource_lt {t m m' : ℕ} (h1 : 1 ≤ m) (hmm : m < m') (hm' : m' ≤ t) :
    codedLadderSource.{u} t m < codedLadderSource t m' := by
  rw [codedLadderSource_of_lt h1 (by omega)]
  rcases Nat.lt_or_ge m' t with hlt | hge
  · rw [codedLadderSource_of_lt (by omega) hlt, Label.coe_lt_coe_iff]
    exact_mod_cast ladderSource_block_lt hmm 1 1
  · obtain rfl : m' = t := le_antisymm hm' hge
    rw [codedLadderSource_self (by omega), Label.coe_lt_coe_iff]
    rcases Nat.lt_or_ge m (m' - 1) with hlt | hge'
    · exact_mod_cast ladderSource_block_lt hlt 1 2
    · obtain rfl : m = m' - 1 := by omega
      exact (add_lt_add_iff_left _).mpr (by exact_mod_cast (by omega : 1 < 2))

/-- **The order of the codes**: for a positive rank `m ≤ t`, the code of `m` is at most the code
of `i` exactly when `m ≤ min i t`. -/
theorem codedLadderSource_le_iff {t m : ℕ} (h1 : 1 ≤ m) (hmt : m ≤ t) (i : ℕ) :
    codedLadderSource.{u} t m ≤ codedLadderSource t i ↔ m ≤ min i t := by
  rw [← codedLadderSource_min t i]
  set i' := min i t with hi'
  have hi't : i' ≤ t := min_le_right _ _
  rcases Nat.lt_trichotomy m i' with h | h | h
  · exact ⟨fun _ ↦ h.le, fun _ ↦ (codedLadderSource_lt h1 h hi't).le⟩
  · subst h; exact ⟨fun _ ↦ le_rfl, fun _ ↦ le_rfl⟩
  · refine ⟨fun hle ↦ ?_, fun hle ↦ absurd hle (not_le.mpr h)⟩
    rcases Nat.eq_zero_or_pos i' with h0 | hpos
    · rw [h0, codedLadderSource_zero, le_bot_iff, codedLadderSource_eq_bot_iff] at hle
      omega
    · exact absurd hle (not_le.mpr (codedLadderSource_lt hpos h hmt))

/-- The codes are monotone in the rank. -/
theorem monotone_codedLadderSource (t : ℕ) : Monotone (codedLadderSource.{u} t) := by
  intro i j hij
  rcases Nat.eq_zero_or_pos (min i t) with h0 | hpos
  · rw [(codedLadderSource_eq_bot_iff t i).mpr h0]; exact bot_le
  · rw [← codedLadderSource_min t i]
    exact (codedLadderSource_le_iff hpos (min_le_right _ _) j).mpr (min_le_min_right _ hij)

/-- The codes reflect the order of the ranks up to the ceiling. -/
theorem codedLadderSource_le_codedLadderSource_iff {H i j : ℕ} (hi : i ≤ H) (hj : j ≤ H) :
    codedLadderSource.{u} H i ≤ codedLadderSource H j ↔ i ≤ j := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · rw [codedLadderSource_le_iff hpos hi, min_eq_left hj]

/-! ### Rendering by order interpolation -/

/-- **A positive table is the image of the codes under a witness** at the grade `1` (native
construction): for `f` monotone, `⊥` at `0`, self-visible at `1` and positive at the ranks
`1, …, t`, the codes of any ranks `a` transform to the table `f` at those ranks capped at `t`.
The witness is order interpolation (`Label.transformsTo_one_of_order`) on the ranks `0, …, t`,
pulled back along the capped rank. -/
theorem transformsTo_codedLadderSource {D : Type*} (a : D → ℕ) {t : ℕ}
    {f : ℕ → Label.{u}} (hf : Monotone f) (h0 : f 0 = ⊥) (hv : ∀ i, IsSelfVisible 1 (f i))
    (hp : ∀ i, 0 < i → i ≤ t → f i ≠ ⊥) :
    TransformsTo (fun _ ↦ 1) (fun d ↦ codedLadderSource t (a d)) (fun d ↦ f (min (a d) t)) := by
  have hfin : TransformsTo (fun _ : Fin (t + 1) ↦ 1) (fun j ↦ codedLadderSource.{u} t j)
      (fun j ↦ f (min (j : ℕ) t)) := by
    refine transformsTo_one_of_order (TransformsTo.refl _ _) (fun _ ↦ hv _) (fun j j' hle ↦ ?_)
      fun j ↦ ?_
    · rw [(isSelfVisible_codedLadderSource t j).visibilityReplace_eq] at hle
      rcases Nat.eq_zero_or_pos (min (j' : ℕ) t) with h | h
      · rw [h, h0]; exact bot_le
      · rw [← codedLadderSource_min t j', codedLadderSource_le_iff h (min_le_right _ _)] at hle
        exact hf hle
    · rw [codedLadderSource_eq_bot_iff]
      refine ⟨fun h ↦ by_contra fun hne ↦ hp _ (by omega) (min_le_right _ _) h, fun h ↦ ?_⟩
      rw [h, h0]
  have h := hfin.reindex fun d ↦ (⟨min (a d) t, by omega⟩ : Fin (t + 1))
  simp only [Function.comp_def, min_assoc, min_self, codedLadderSource_min] at h
  exact h

/-! ### The coded ladder table -/

section Table

variable {Q X D : Type*} (H : ℕ) (prof : Q → X → ℕ) (parent : D → Q) (ceil : D → ℕ)

/-- The **row** of a cell `c` of the coded ladder table (native construction): the coded ladder
sources, at the ceiling of `c`, of the indices (`Label.ladderIndex`) of the cells for the parent
of `c`. -/
noncomputable def codedLadderRow (c v : D) : Label.{u} :=
  codedLadderSource (ceil c) (ladderIndex H prof parent ceil (parent c) v)

/-- A labelling of the coded ladder table **lawful at the grade `1`**: self-visible at `1`, and
local at every cell with respect to its row. -/
def CodedLadderLawful (q : D → Label.{u}) : Prop :=
  (∀ v, IsSelfVisible 1 (q v)) ∧
    ∀ c, TransformsTo (fun _ ↦ 1) (codedLadderRow.{u} H prof parent ceil c) fun v ↦
      min (q v) (q c)

variable {H prof parent ceil}

/-- **Rendering**: a positive table `f` read at the indices of a member `a` is lawful on the
coded ladder table. -/
theorem codedLadderLawful_image (a : Q) {f : ℕ → Label.{u}}
    (hf : Monotone f) (h0 : f 0 = ⊥) (hv : ∀ i, IsSelfVisible 1 (f i))
    (hp : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥) :
    CodedLadderLawful H prof parent ceil fun v ↦ f (ladderIndex H prof parent ceil a v) := by
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
  · exact transformsTo_codedLadderSource (ladderIndex H prof parent ceil (parent c))
      (t := ceil c) (f := fun i ↦ f (min i e)) (fun _ _ h ↦ hf (min_le_min_right _ h))
      (by simp [h0]) (fun _ ↦ hv _) fun i hi _ ↦ hp _ (by omega)
        ((min_le_right _ _).trans (ladderIndex_le a c))

/-- **Every row of the coded ladder table is lawful on the table**: the rows are consistent. -/
theorem codedLadderLawful_row (c : D) :
    CodedLadderLawful.{u} H prof parent ceil (codedLadderRow H prof parent ceil c) := by
  by_cases hc : ceil c = 0
  · have he : codedLadderRow.{u} H prof parent ceil c = fun _ ↦ ⊥ := by
      funext v
      rw [codedLadderRow, (codedLadderSource_eq_bot_iff _ _).mpr (by rw [hc]; exact Nat.min_zero _)]
    rw [he]
    refine ⟨fun _ ↦ isSelfVisible_bot _, fun _ ↦ ?_⟩
    simp only [min_self]
    exact TransformsTo.bot _ _
  · exact codedLadderLawful_image (parent c) (monotone_codedLadderSource _)
      (codedLadderSource_zero _) (isSelfVisible_codedLadderSource _) fun i hi _ h0 ↦ by
        rw [codedLadderSource_eq_bot_iff] at h0
        omega

/-- **Reflection of `⊥` by the chart of a top rung.**  Let a member `a` have rungs `r i`
(`i < H`, `H ≥ 1`) of ceiling `i + 1`.  In every labelling lawful on the coded ladder table with a
positive top rung `r (H - 1)`, the chart `(g, σ)` of the top rung reads every cell `v` (below the
top rung) through the code of its index for `a`, and `v` is `⊥` below the top rung exactly when
that index is `0`. -/
theorem CodedLadderLawful.reflects (hH : 0 < H) (hceil : ∀ v, ceil v ≤ H) (a : Q) (r : ℕ → D)
    (hpr : ∀ i < H, parent (r i) = a) (hr : ∀ i < H, ceil (r i) = i + 1) {q : D → Label.{u}}
    (hq : CodedLadderLawful H prof parent ceil q) (htop : q (r (H - 1)) ≠ ⊥) :
    ∃ (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}), IsWitness g σ ∧
      (∀ v, min (q v) (q (r (H - 1))) =
        min (σ (codedLadderSource H (ladderIndex H prof parent ceil a v))) (g 1)) ∧
      ∀ v, min (q v) (q (r (H - 1))) = ⊥ ↔ ladderIndex H prof parent ceil a v = 0 := by
  obtain ⟨g, σ, hw, hch⟩ := hq.2 (r (H - 1))
  have htopc : ceil (r (H - 1)) = H := by rw [hr _ (by omega)]; omega
  have hidx (i : ℕ) (hi : i < H) : ladderIndex H prof parent ceil a (r i) = i + 1 := by
    rw [← hpr i hi, ladderIndex_parent hceil, hr i hi]
  have hrow (v : D) : codedLadderRow.{u} H prof parent ceil (r (H - 1)) v =
      codedLadderSource H (ladderIndex H prof parent ceil a v) := by
    rw [codedLadderRow, htopc, hpr _ (by omega)]
  have hchart (v : D) : min (q v) (q (r (H - 1))) =
      min (σ (codedLadderRow H prof parent ceil (r (H - 1)) v)) (g 1) := hch v
  refine ⟨g, σ, hw, fun v ↦ (hchart v).trans (by rw [hrow]), fun v ↦ ?_⟩
  exact codedLadder_shadow_eq_bot_iff (codedLadderRow H prof parent ceil) q r
    (fun i _ ↦ hq.2 (r i))
    (fun i hi ↦ by rw [codedLadderRow, hr i hi, hpr i hi, hidx i hi])
    (fun i hi hi0 ↦ by
      rw [codedLadderRow, hr i hi, hpr i hi, hidx (i - 1) (by omega)]
      congr 1; omega)
    htop hw hchart (fun j hj ↦ by rw [hrow, hidx j hj]) (ladderIndex_le a v) (hrow v)

/-- **Every cell lies below the top rung of its parent** in a lawful labelling: the row of a cell
reads the top rung of its parent as itself. -/
theorem CodedLadderLawful.le_top (hceil : ∀ v, ceil v ≤ H) (top : Q → D)
    (hpt : ∀ a, parent (top a) = a) (htc : ∀ a, ceil (top a) = H) {q : D → Label.{u}}
    (hq : CodedLadderLawful H prof parent ceil q) (c : D) : q c ≤ q (top (parent c)) := by
  obtain ⟨g, σ, -, hr⟩ := hq.2 c
  have he : codedLadderRow.{u} H prof parent ceil c (top (parent c)) =
      codedLadderRow H prof parent ceil c c := by
    rw [codedLadderRow, codedLadderRow, ladderIndex_parent hceil, ladderIndex, hpt, rankCut_self,
      htc, min_self, ← codedLadderSource_min (ceil c) H, min_eq_right (hceil c)]
  have h1 := hr (top (parent c))
  have h2 := hr c
  simp only [min_self] at h2
  rw [he, ← h2] at h1
  exact min_eq_right_iff.mp h1

/-- **Recognition on the coded ladder table** (native construction): every labelling lawful on the
table is `⊥`, or for the member `a` with the largest top rung it is the image, under the chart
`(g, σ)` of that top rung, of the codes of the indices for `a`, with `⊥` exactly at the index `0`.
The members have rungs `r a i` of ceiling `i + 1` (`i < H`, `H ≥ 1`). -/
theorem CodedLadderLawful.exists_shape [Finite Q] [Nonempty Q] (hH : 0 < H)
    (hceil : ∀ v, ceil v ≤ H) (r : Q → ℕ → D) (hpr : ∀ a, ∀ i < H, parent (r a i) = a)
    (hr : ∀ a, ∀ i < H, ceil (r a i) = i + 1) {q : D → Label.{u}}
    (hq : CodedLadderLawful H prof parent ceil q) :
    (∀ v, q v = ⊥) ∨ ∃ (a : Q) (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}),
      IsWitness g σ ∧
      (∀ v, q v = min (σ (codedLadderSource H (ladderIndex H prof parent ceil a v))) (g 1)) ∧
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
