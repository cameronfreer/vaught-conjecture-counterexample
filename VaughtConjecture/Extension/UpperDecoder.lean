/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OrbitCode

/-!
# The upper decoder: an orbit decoder that reads the gaps between codes upward

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`; here
the label map behind a selected section through the lower layers of the tower, with capped
agreement at the caps self-visible and short at `3`).

The extension at the cap `⊥` through a canonical field layer at a grade `k`
(`Scheme.exists_isLawfulBelow_fieldLayer`) reads the field row of the orbit code `c` of a
labelling `w` by the orbit decoder at the least grid point (`Label.orbitDecoder`).  That decoder
reads a label strictly between the codes of two keys of `w` as the lower key: at an agreement
height that falls in such a gap, the decoded label lies below the next value of `w`, however far
above it that value is.  Two labellings that agree capped at a cap `h` self-visible and short at
`3`, but not short at `k`, can then decode one agreement height below `h` and the other above it.

**The upper decoder** (`Label.upperDecoder k B w`) is the larger of the orbit decoder and the
*gap value* (`Label.gapValue`): at a label `x` other than bottom, the least, over the cells `d`
whose code has key at least the key of `x`, of the largest member of the code grid
`Label.codeGrid 3 B` that is self-visible at `k` and at most `w d` (`Label.admissibleBelow`), and
at most the grid point `ω * B + 3`.

* It is a witness bounded by the grade `k`, for `k ≤ 3` (`Label.isWitness_upperDecoder`): the gap
  value depends on the key of the label only and is self-visible at `k`; it sends only bottom to
  bottom (`Label.eq_bot_of_upperDecoder_eq_bot`); and it reads the orbit code literally
  (`Label.upperDecoder_orbitCode`).
* On the agreement heights in the grid of grade `k` it takes values in `Label.codeGrid 3 B` when
  `w` does (`Label.upperDecoder_mem_codeGrid`).
* **Capped agreement** (`Label.min_upperDecoder_agreementHeight_eq`): for `k < 3`, if `w` has
  values at most `ω * B + 3` and `w'` agrees with it capped at a cap `h` self-visible and short
  at `3`, then for every labelling `e` the decoded agreement heights of their orbit codes with `e`
  agree capped at `h`.  With `R` the number of keys of `w` below `h` (the same for `w'`), the
  grid point `Γ = ω * (2 R + 1) + k` separates the codes of the values below `h` (keys below `Γ`)
  from those of the values at least `h` (at least `Γ`), so the two orbit codes agree capped at
  `Γ` and so do the agreement heights; below `Γ` the two decoders read the same cells; at or above
  `Γ` the gap value reads only values at least `h`, whose admissible labels are at least `h`.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.Label

open Finset
open Ordinal hiding univ

variable {ι : Type*} [Fintype ι] {k B : ℕ} {w w' : ι → Label.{u}} {x y h v : Label.{u}}

/-! ### Admissible labels -/

open Classical in
/-- The **admissible label below `v`**: the largest member of the code grid `codeGrid 3 B` that is
self-visible at `k` and at most `v` (bottom if there is none). -/
noncomputable def admissibleBelow (k B : ℕ) (v : Label.{u}) : Label.{u} :=
  ({y ∈ codeGrid 3 B | IsSelfVisible k y ∧ y ≤ v} : Finset Label.{u}).sup id

/-- The admissible label below `v` is at most `v`. -/
theorem admissibleBelow_le (k B : ℕ) (v : Label.{u}) : admissibleBelow k B v ≤ v := by
  classical
  unfold admissibleBelow
  exact Finset.sup_le fun y hy ↦ (mem_filter.mp hy).2.2

/-- The admissible label below `v` is self-visible at `k`. -/
theorem isSelfVisible_admissibleBelow (k B : ℕ) (v : Label.{u}) :
    IsSelfVisible k (admissibleBelow k B v) := by
  classical
  unfold admissibleBelow
  exact Finset.sup_induction (isSelfVisible_bot k) (fun a ha b hb ↦ ha.max hb)
    fun y hy ↦ (mem_filter.mp hy).2.1

/-- The admissible label below `v` is a member of the code grid. -/
theorem admissibleBelow_mem_codeGrid (k B : ℕ) (v : Label.{u}) :
    admissibleBelow k B v ∈ codeGrid 3 B := by
  classical
  unfold admissibleBelow
  refine Finset.sup_induction (p := fun z ↦ z ∈ codeGrid 3 B) (mem_insert_self _ _)
    (fun a ha b hb ↦ ?_) fun y hy ↦ (mem_filter.mp hy).1
  rcases le_total a b with hab | hab
  · rwa [show a ⊔ b = b from max_eq_right hab]
  · rwa [show a ⊔ b = a from max_eq_left hab]

/-- A member of the code grid self-visible at `k` and at most `v` is at most the admissible label
below `v`. -/
theorem le_admissibleBelow (hy : y ∈ codeGrid 3 B) (hv : IsSelfVisible k y) (hyv : y ≤ v) :
    y ≤ admissibleBelow k B v := by
  classical
  unfold admissibleBelow
  exact le_sup (f := id) (mem_filter.mpr ⟨hy, hv, hyv⟩)

/-! ### The gap value and the upper decoder -/

open Classical in
/-- The **gap value** of `w` at `x`: bottom at bottom; otherwise the least admissible label below
the values of `w` at the cells whose orbit code has key at least the key of `x`, at most
`ω * B + 3`. -/
noncomputable def gapValue (k B : ℕ) (w : ι → Label.{u}) (x : Label.{u}) : Label.{u} :=
  if x = ⊥ then ⊥ else min (gridPoint 3 B)
    (({d | visibilityReplace k k x ≤ visibilityReplace k k (orbitCode k w d)} : Finset ι).inf
      fun d ↦ admissibleBelow k B (w d))

/-- The **upper decoder** of `w` at grade `k` with block bound `B`: the larger of the orbit
decoder at the least grid point and the gap value. -/
noncomputable def upperDecoder (k B : ℕ) (w : ι → Label.{u}) (x : Label.{u}) : Label.{u} :=
  max (orbitDecoder k w (gridPoint k 0) x) (gapValue k B w x)

/-- The gap value at bottom. -/
@[simp] theorem gapValue_bot : gapValue k B w ⊥ = ⊥ := by
  unfold gapValue
  exact ite_eq_left rfl

/-- The gap value off bottom. -/
theorem gapValue_of_ne_bot (hx : x ≠ ⊥) : gapValue k B w x = min (gridPoint 3 B)
    (({d | visibilityReplace k k x ≤ visibilityReplace k k (orbitCode k w d)} : Finset ι).inf
      fun d ↦ admissibleBelow k B (w d)) := by
  unfold gapValue
  exact ite_eq_right hx

/-- The gap value is self-visible at `k`, for `k ≤ 3`. -/
theorem isSelfVisible_gapValue (hk : k ≤ 3) (x : Label.{u}) :
    IsSelfVisible k (gapValue k B w x) := by
  by_cases hx : x = ⊥
  · rw [hx, gapValue_bot]
    exact isSelfVisible_bot k
  rw [gapValue_of_ne_bot hx]
  exact ((isSelfVisible_gridPoint 3 B).mono hk).min (Finset.inf_induction (isSelfVisible_top k)
    (fun a ha b hb ↦ ha.min hb) fun d _ ↦ isSelfVisible_admissibleBelow k B (w d))

/-- The gap value is at most `ω * B + 3`. -/
theorem gapValue_le_gridPoint (x : Label.{u}) : gapValue k B w x ≤ gridPoint 3 B := by
  by_cases hx : x = ⊥
  · rw [hx, gapValue_bot]
    exact bot_le
  rw [gapValue_of_ne_bot hx]
  exact min_le_left _ _

/-- The gap value depends on the key of the label only. -/
theorem gapValue_visibilityReplace {j i : ℕ} (hi : i ≤ j) (hj : j ≤ k) (x : Label.{u}) :
    gapValue k B w (visibilityReplace j i x) = gapValue k B w x := by
  by_cases hx : x = ⊥
  · rw [hx, visibilityReplace_bot]
  have hx' : visibilityReplace j i x ≠ ⊥ := by rwa [Ne, visibilityReplace_eq_bot_iff]
  rw [gapValue_of_ne_bot hx, gapValue_of_ne_bot hx',
    visibilityReplace_self_visibilityReplace_of_le hi hj]

/-- The gap value is monotone. -/
theorem monotone_gapValue : Monotone (gapValue k B w) := by
  classical
  intro x y hxy
  by_cases hx : x = ⊥
  · rw [hx, gapValue_bot]
    exact bot_le
  have hy : y ≠ ⊥ := ne_bot_of_le_ne_bot hx hxy
  rw [gapValue_of_ne_bot hx, gapValue_of_ne_bot hy]
  refine min_le_min_left _ (Finset.inf_mono fun d hd ↦ ?_)
  rw [mem_filter] at hd ⊢
  exact ⟨mem_univ d, (monotone_visibilityReplace le_rfl hxy).trans hd.2⟩

/-- At the code of a cell, the gap value is at most the value there. -/
theorem gapValue_orbitCode_le (d : ι) : gapValue k B w (orbitCode k w d) ≤ w d := by
  classical
  by_cases hd : w d = ⊥
  · rw [orbitCode_eq_bot_iff.mpr hd, gapValue_bot]
    exact bot_le
  rw [gapValue_of_ne_bot (by rwa [Ne, orbitCode_eq_bot_iff])]
  have hmem : d ∈ ({e | visibilityReplace k k (orbitCode k w d) ≤
      visibilityReplace k k (orbitCode k w e)} : Finset ι) := mem_filter.mpr ⟨mem_univ d, le_rfl⟩
  exact (min_le_right _ _).trans ((Finset.inf_le hmem).trans (admissibleBelow_le k B (w d)))

/-- The orbit decoder at the least grid point is a witness bounded by the grade `k`. -/
private theorem isWitness_orbitDecoder_zero :
    IsWitness (stepSuppressor.{u} k) (orbitDecoder k w (gridPoint k 0)) :=
  isWitness_orbitDecoder (isSelfVisible_gridPoint k 0) (gridPoint_ne_bot k 0)

/-- The upper decoder sends only bottom to bottom. -/
theorem eq_bot_of_upperDecoder_eq_bot (hx : upperDecoder k B w x = ⊥) : x = ⊥ :=
  eq_bot_of_orbitDecoder_eq_bot (gridPoint_ne_bot k 0)
    (le_bot_iff.mp ((le_max_left _ _).trans hx.le))

/-- The upper decoder fixes bottom. -/
@[simp] theorem upperDecoder_bot : upperDecoder k B w ⊥ = ⊥ := by
  rw [upperDecoder, orbitDecoder_bot, gapValue_bot, max_self]

/-- **The upper decoder is a witness bounded by the grade `k`**, for `k ≤ 3`. -/
theorem isWitness_upperDecoder (hk : k ≤ 3) :
    IsWitness (stepSuppressor.{u} k) (upperDecoder k B w) where
  antitone := (IsWitness.id_step k).antitone
  isSelfVisible := (IsWitness.id_step k).isSelfVisible
  map_bot := upperDecoder_bot
  monotone _ _ hxy := max_le_max (isWitness_orbitDecoder_zero.monotone hxy) (monotone_gapValue hxy)
  visibilityReplace_comm x j hx i hi := by
    by_cases hj : j ≤ k
    · rw [upperDecoder, upperDecoder, visibilityReplace_max hi,
        isWitness_orbitDecoder_zero.visibilityReplace_comm x j
          (by rw [stepSuppressor_of_le hj]; exact le_top) i hi,
        gapValue_visibilityReplace hi hj,
        ((isSelfVisible_gapValue hk x).mono hj).visibilityReplace_eq]
    · rw [stepSuppressor_of_lt (not_le.mp hj), le_bot_iff] at hx
      rw [eq_bot_of_upperDecoder_eq_bot hx, visibilityReplace_bot, upperDecoder_bot,
        visibilityReplace_bot]

/-- **The upper decoder reads the orbit code literally.** -/
theorem upperDecoder_orbitCode (d : ι) : upperDecoder k B w (orbitCode k w d) = w d := by
  rw [upperDecoder, orbitDecoder_orbitCode (fun e ↦ min_orbitCode_gridPoint_zero e)]
  exact max_eq_left (gapValue_orbitCode_le d)

/-! ### Values in the code grid -/

/-- The larger of two members of a finite set of labels is a member. -/
private theorem max_mem {S : Finset Label.{u}} (hx : x ∈ S) (hy : y ∈ S) : max x y ∈ S := by
  rcases le_total x y with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

/-- A block point with finite part at most `3` and block at most `B` is in the code grid. -/
private theorem block_mem_codeGrid {b f : ℕ} (hb : b ≤ B) (hf : f ≤ 3) :
    ((ω * (b : Ordinal.{u}) + (f : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) ∈ codeGrid 3 B :=
  mem_codeGrid.mpr (.inr ⟨b, hb, f, hf, rfl⟩)

omit [Fintype ι] in
/-- A least admissible label over a set of cells is the formal top or in the code grid. -/
private theorem inf_admissibleBelow_cases (w : ι → Label.{u}) (S : Finset ι) :
    S.inf (fun d ↦ admissibleBelow k B (w d)) = ⊤ ∨
      S.inf (fun d ↦ admissibleBelow k B (w d)) ∈ codeGrid 3 B := by
  refine Finset.inf_induction (p := fun z ↦ z = ⊤ ∨ z ∈ codeGrid 3 B) (.inl rfl)
    (fun a ha b hb ↦ ?_) fun d _ ↦ .inr (admissibleBelow_mem_codeGrid k B (w d))
  rcases ha with rfl | ha
  · rw [show (⊤ : Label.{u}) ⊓ b = b from top_inf_eq b]; exact hb
  rcases hb with rfl | hb
  · rw [show a ⊓ (⊤ : Label.{u}) = a from inf_top_eq a]; exact .inr ha
  rcases le_total a b with h | h
  · rw [show a ⊓ b = a from min_eq_left h]; exact .inr ha
  · rw [show a ⊓ b = b from min_eq_right h]; exact .inr hb

/-- **On the grid of grade `k`, the upper decoder takes values in the code grid** when `w` does,
for `k ≤ 3`. -/
theorem upperDecoder_mem_codeGrid (hk : k ≤ 3) (hw : ∀ d, w d ∈ codeGrid 3 B) {B' : ℕ}
    (hx : x ∈ grid k B') : upperDecoder k B w x ∈ codeGrid 3 B := by
  have hbot : (⊥ : Label.{u}) ∈ codeGrid 3 B := mem_insert_self _ _
  refine max_mem (max_mem ?_ ?_) ?_
  · -- The capped label: bottom or the least grid point.
    rcases mem_grid.mp hx with rfl | ⟨b, -, rfl⟩
    · rwa [min_eq_left bot_le]
    · rw [min_eq_right (gridPoint_le_gridPoint.mpr (Nat.zero_le b))]
      exact block_mem_codeGrid (Nat.zero_le B) hk
  · refine Finset.sup_induction (p := fun z ↦ z ∈ codeGrid 3 B) hbot
      (fun a ha b hb ↦ max_mem ha hb) fun d _ ↦ ?_
    unfold cellReading
    split_ifs with h1 h2
    · exact hbot
    · rcases mem_codeGrid.mp (hw d) with h0 | ⟨b, hb, f, -, he⟩
      · exact absurd h0 h2.2.isKey.ne_bot
      rcases mem_grid.mp hx with rfl | ⟨b', -, rfl⟩
      · rw [moveToBlock_bot]; exact hbot
      · rw [he, gridPoint, moveToBlock_omega0_mul_add]
        exact block_mem_codeGrid hb hk
    · rcases mem_codeGrid.mp (hw d) with h0 | ⟨b, hb, f, hf, he⟩
      · rw [h0, visibilityReplace_bot]; exact hbot
      · rw [he, visibilityReplace_block]
        exact block_mem_codeGrid hb (by split_ifs <;> omega)
  · by_cases hx0 : x = ⊥
    · rw [hx0, gapValue_bot]; exact hbot
    rw [gapValue_of_ne_bot hx0]
    have hT : gridPoint.{u} 3 B ∈ codeGrid 3 B := block_mem_codeGrid le_rfl le_rfl
    rcases inf_admissibleBelow_cases (k := k) (B := B) w (({d | visibilityReplace k k x ≤
      visibilityReplace k k (orbitCode k w d)} : Finset ι)) with htop | hmem
    · rw [htop, min_eq_left le_top]; exact hT
    · rcases le_total (gridPoint.{u} 3 B) _ with h | h
      · rw [min_eq_left h]; exact hT
      · rw [min_eq_right h]; exact hmem

/-! ### Keys below a cap self-visible and short at `3` -/

/-- A label self-visible and short at `3`, other than bottom and the formal top, is
`ω * γ + 3`. -/
private theorem exists_eq_block_three (hh : IsSelfVisible 3 h) (hs : IsShort 3 h) (h0 : h ≠ ⊥)
    (ht : h ≠ ⊤) : ∃ γ : Ordinal.{u}, h = ((ω * γ + ((3 : ℕ) : Ordinal.{u}) : Ordinal.{u}) :
      Label.{u}) := by
  obtain ⟨q, n, rfl⟩ := exists_block h0 ht
  have h1 := isSelfVisible_block.mp hh
  rw [isShort_coe, mul_add_mod_self, mod_eq_of_lt (natCast_lt_omega0 n)] at hs
  have h2 : n ≤ 3 := by exact_mod_cast hs
  exact ⟨q, by rw [show n = 3 by omega]⟩

/-- Block points compare strictly, lexicographically. -/
private theorem block_lt_block_iff {q γ : Ordinal.{u}} {n m : ℕ} :
    ((ω * q + n : Ordinal.{u}) : Label.{u}) < ((ω * γ + m : Ordinal.{u}) : Label.{u}) ↔
      q < γ ∨ q = γ ∧ n < m := by
  rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe, lt_iff_not_ge, omega0_mul_add_natCast_le_iff]
  rcases lt_trichotomy q γ with hlt | rfl | hgt
  · exact ⟨fun _ ↦ .inl hlt, fun _ ↦ by
      rintro (h | ⟨h, -⟩)
      exacts [lt_asymm hlt h, hlt.ne h.symm]⟩
  · exact ⟨fun h ↦ .inr ⟨rfl, by
      by_contra hc
      exact h (.inr ⟨rfl, by omega⟩)⟩, by
      rintro (h | ⟨-, h⟩) (h' | ⟨-, h'⟩)
      · exact lt_irrefl _ h
      · exact lt_irrefl _ h
      · exact lt_irrefl _ h'
      · omega⟩
  · exact ⟨fun h ↦ absurd (.inl hgt) h, by
      rintro (h | ⟨h, -⟩)
      exacts [absurd (lt_asymm hgt) (not_not.mpr h), absurd h hgt.ne']⟩

/-- **Below a cap `ω * γ + 3`, keys at a grade `k < 3` stay below the cap.** -/
private theorem visibilityReplace_lt (hk : k < 3) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((3 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) (hy : y < h) :
    visibilityReplace k k y < h := by
  by_cases hy0 : y = ⊥
  · rw [hy0, visibilityReplace_bot]; exact hy0 ▸ hy
  have hyt : y ≠ ⊤ := ne_top_of_lt hy
  obtain ⟨q, n, rfl⟩ := exists_block hy0 hyt
  rw [hγ] at hy ⊢
  rw [visibilityReplace_block]
  rcases block_lt_block_iff.mp hy with h | ⟨rfl, h⟩
  · exact block_lt_block_iff.mpr (.inl h)
  · exact block_lt_block_iff.mpr (.inr ⟨rfl, by split_ifs <;> omega⟩)

open Classical in
/-- The **keys of `w` below `h`** at grade `k`. -/
private noncomputable def keysBelow (k : ℕ) (w : ι → Label.{u}) (h : Label.{u}) :
    Finset Label.{u} :=
  {y ∈ univ.image fun e ↦ visibilityReplace k k (w e) | y ≠ ⊥ ∧ y < h}

/-- There are at most as many keys below `h` as cells. -/
private theorem card_keysBelow_le (k : ℕ) (w : ι → Label.{u}) (h : Label.{u}) :
    #(keysBelow k w h) ≤ Fintype.card ι := by
  unfold keysBelow
  exact (card_filter_le _ _).trans (card_image_le.trans_eq card_univ)

/-- Labellings that agree capped at `h` have the same keys below `h`. -/
private theorem keysBelow_congr (hag : ∀ d, min (w d) h = min (w' d) h) :
    keysBelow k w h = keysBelow k w' h := by
  classical
  have key {v v' : ι → Label.{u}} (hvv : ∀ d, min (v d) h = min (v' d) h) {y : Label.{u}}
      (hy : y ∈ keysBelow k v h) : y ∈ keysBelow k v' h := by
    unfold keysBelow at hy ⊢
    obtain ⟨hyi, hy0, hyh⟩ := mem_filter.mp hy
    obtain ⟨e, -, rfl⟩ := mem_image.mp hyi
    have hve : v e < h := (le_visibilityReplace (Nat.le_succ k) _).trans_lt hyh
    refine mem_filter.mpr ⟨mem_image.mpr ⟨e, mem_univ e, ?_⟩, hy0, hyh⟩
    rw [eq_of_min_eq_of_lt (hvv e) hve]
  ext y
  exact ⟨key hag, key fun d ↦ (hag d).symm⟩

/-- A value below a cap `ω * γ + 3` has key rank at most the number of keys below the cap. -/
private theorem keyRank_le_card_keysBelow (hk : k < 3) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((3 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) {d : ι}
    (hd : w d < h) : keyRank k w (w d) ≤ #(keysBelow k w h) := by
  classical
  unfold keyRank valueRank keysBelow
  refine card_le_card fun y hy ↦ ?_
  obtain ⟨hyi, hy0, hyle⟩ := mem_filter.mp hy
  exact mem_filter.mpr ⟨hyi, hy0, hyle.trans_lt (visibilityReplace_lt hk hγ hd)⟩

/-- A value at least `h` has key rank above the number of keys below `h`. -/
private theorem card_lt_keyRank (h0 : h ≠ ⊥) {d : ι} (hd : h ≤ w d) :
    #(keysBelow k w h) + 1 ≤ keyRank k w (w d) := by
  classical
  have hxh : h ≤ visibilityReplace k k (w d) := hd.trans (le_visibilityReplace (Nat.le_succ k) _)
  have hnot : visibilityReplace k k (w d) ∉ keysBelow k w h := by
    unfold keysBelow
    exact fun hm ↦ not_lt.mpr hxh (mem_filter.mp hm).2.2
  have hsub : insert (visibilityReplace k k (w d)) (keysBelow k w h) ⊆
      {y ∈ univ.image fun e ↦ visibilityReplace k k (w e) |
        y ≠ ⊥ ∧ y ≤ visibilityReplace k k (w d)} := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ d),
        ne_bot_of_le_ne_bot h0 hxh, le_rfl⟩
    · unfold keysBelow at hy
      obtain ⟨hyimg, hy0, hylt⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨hyimg, hy0, (hylt.trans_le hxh).le⟩
  calc #(keysBelow k w h) + 1 = #(insert (visibilityReplace k k (w d)) (keysBelow k w h)) :=
        (card_insert_of_notMem hnot).symm
    _ ≤ keyRank k w (w d) := card_le_card hsub

/-- The least grid point lies below a cap `ω * γ + 3`, at a grade `k < 3`. -/
private theorem gridPoint_zero_lt (hk : k < 3) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((3 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) :
    gridPoint.{u} k 0 < h := by
  rw [hγ, gridPoint, Nat.cast_zero]
  rcases eq_or_ne γ 0 with rfl | hγ0
  · exact block_lt_block_iff.mpr (.inr ⟨rfl, hk⟩)
  · exact block_lt_block_iff.mpr (.inl (pos_iff_ne_zero.mpr hγ0))

/-- **The code blocks of the values at least `h` are at least `2 R + 1`**, `R` the number of keys
below `h`. -/
private theorem le_codeBlock_of_le (h0 : h ≠ ⊥) (hk : k < 3) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((3 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) {d : ι}
    (hd : h ≤ w d) : 2 * #(keysBelow k w h) + 1 ≤ codeBlock k w (w d) ∧
      ¬ (IsOrbitKey k w (w d) ∧ visibilityReplace k k (w d) = gridPoint k 0) := by
  have hn : ¬ (IsOrbitKey k w (w d) ∧ visibilityReplace k k (w d) = gridPoint k 0) := by
    rintro ⟨-, he⟩
    have := hd.trans ((le_visibilityReplace (Nat.le_succ k) _).trans_eq he)
    exact absurd (gridPoint_zero_lt hk hγ) (not_lt.mpr this)
  have h1 := le_codeBlock hn
  have h2 := card_lt_keyRank (k := k) h0 hd
  exact ⟨by omega, hn⟩

/-- (F1) The codes of the values below `h` have keys below `ω * (2 R + 1) + k`. -/
private theorem visibilityReplace_orbitCode_lt (hk : k < 3) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((3 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) {d : ι}
    (hd : w d < h) :
    visibilityReplace k k (orbitCode k w d) < gridPoint k (2 * #(keysBelow k w h) + 1) := by
  by_cases hd0 : w d = ⊥
  · rw [orbitCode_eq_bot_iff.mpr hd0, visibilityReplace_bot]
    exact bot_lt_iff_ne_bot.mpr (gridPoint_ne_bot _ _)
  rw [orbitCode_apply, visibilityReplace_orbitMap hd0, gridPoint_lt_gridPoint]
  have := codeBlock_le k w (w d)
  have := keyRank_le_card_keysBelow hk hγ hd
  omega

/-- (F2) The codes of the values at least `h` have keys at least `ω * (2 R + 1) + k`. -/
private theorem le_visibilityReplace_orbitCode (h0 : h ≠ ⊥) (hk : k < 3) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((3 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) {d : ι}
    (hd : h ≤ w d) :
    gridPoint k (2 * #(keysBelow k w h) + 1) ≤ visibilityReplace k k (orbitCode k w d) := by
  rw [orbitCode_apply, visibilityReplace_orbitMap (ne_bot_of_le_ne_bot h0 hd),
    gridPoint_le_gridPoint]
  exact (le_codeBlock_of_le h0 hk hγ hd).1

/-- (F3) The codes of the values at least `h` are at least `ω * (2 R + 1) + k`. -/
private theorem le_orbitCode (h0 : h ≠ ⊥) (hk : k < 3) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((3 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) {d : ι}
    (hd : h ≤ w d) : gridPoint k (2 * #(keysBelow k w h) + 1) ≤ orbitCode k w d := by
  have hd0 : w d ≠ ⊥ := ne_bot_of_le_ne_bot h0 hd
  obtain ⟨hcb, hn⟩ := le_codeBlock_of_le h0 hk hγ hd
  rcases hcb.lt_or_eq with hlt | heq
  · -- A code block above `2 R + 1`: the code lies in that block.
    have hkey := visibilityReplace_orbitMap (w := w) (k := k) hd0
    have hz0 : orbitMap k w (w d) ≠ ⊥ := by rwa [Ne, orbitMap_eq_bot_iff]
    obtain ⟨q, n, hz⟩ := exists_block hz0 (orbitMap_ne_top _)
    rw [hz, visibilityReplace_block, gridPoint, WithBot.coe_inj, WithTop.coe_inj] at hkey
    have hq : q = (codeBlock k w (w d) : Ordinal.{u}) := by
      have h1 := (omega0_mul_add_natCast_le_iff (a := q)).mp hkey.le
      have h2 := (omega0_mul_add_natCast_le_iff (b := q)).mp hkey.ge
      rcases h1 with h1 | ⟨h1, -⟩
      · rcases h2 with h2 | ⟨h2, -⟩
        · exact absurd (h1.trans h2) (lt_irrefl _)
        · exact absurd (h2 ▸ h1) (lt_irrefl _)
      · exact h1
    rw [orbitCode_apply, hz, hq, gridPoint]
    exact (block_lt_block_iff.mpr (.inl (by exact_mod_cast hlt))).le
  · -- The code block `2 R + 1` is odd: not an orbit key, so the code is the grid point.
    have ho : ¬ IsOrbitKey k w (w d) := fun ho ↦ by
      have := codeBlock_of_isOrbitKey ho fun he ↦ hn ⟨ho, he⟩
      omega
    rw [orbitCode_apply, orbitMap_of_not_isOrbitKey hd0 ho, ← heq]

omit [Fintype ι] in
/-- Below a cap self-visible at `k`, the values with an orbit key are the same. -/
private theorem isOrbitKey_iff_of_lt (hh : IsSelfVisible k h)
    (hag : ∀ d, min (w d) h = min (w' d) h) {d : ι} (hd : w d < h) :
    IsOrbitKey k w (w d) ↔ IsOrbitKey k w' (w d) := by
  have hdh : visibilityReplace k k (w d) ≤ h :=
    (monotone_visibilityReplace le_rfl hd.le).trans_eq hh
  have hlow {v v' : ι → Label.{u}} (hvv : ∀ e, min (v e) h = min (v' e) h) {e : ι}
      (hek : visibilityReplace k k (v e) = visibilityReplace k k (w d))
      (hesv : ¬ IsSelfVisible k (v e)) : v' e = v e :=
    eq_of_min_eq_of_lt (hvv e) (lt_of_le_of_ne
      ((le_visibilityReplace (Nat.le_succ k) _).trans (hek.trans_le hdh)) fun h' ↦ hesv (h' ▸ hh))
  constructor
  · rintro ⟨e, hek, hesv⟩
    exact ⟨e, by rw [hlow hag hek hesv, hek], by rwa [hlow hag hek hesv]⟩
  · rintro ⟨e, hek, hesv⟩
    exact ⟨e, by rw [hlow (fun d ↦ (hag d).symm) hek hesv, hek],
      by rwa [hlow (fun d ↦ (hag d).symm) hek hesv]⟩

/-- Below a cap self-visible at `k`, the readings of a cell with a value below the cap agree. -/
private theorem cellReading_eq_of_lt (hh : IsSelfVisible k h)
    (hag : ∀ d, min (w d) h = min (w' d) h) {d : ι} (hd : w d < h) (x : Label.{u}) :
    cellReading k w d x = cellReading k w' d x := by
  have hwd : w' d = w d := eq_of_min_eq_of_lt (hag d) hd
  unfold cellReading
  rw [orbitCode_eq_of_min_eq hh hag hd, propext (isOrbitKey_iff_of_lt hh hag hd), hwd]

/-- **The orbit decoders agree below the separating grid point.** -/
private theorem orbitDecoder_le_of_lt (h0 : h ≠ ⊥) (hk : k < 3) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((3 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}))
    (hag : ∀ d, min (w d) h = min (w' d) h)
    (hx : visibilityReplace k k x < gridPoint k (2 * #(keysBelow k w h) + 1)) :
    orbitDecoder k w (gridPoint k 0) x ≤ orbitDecoder k w' (gridPoint k 0) x := by
  classical
  have hh : IsSelfVisible k h := by
    rw [hγ]; exact isSelfVisible_block.mpr (by omega)
  unfold orbitDecoder
  refine max_le_max le_rfl (Finset.sup_le fun d hd ↦ ?_)
  rcases lt_or_ge (w d) h with hdh | hdh
  · rw [cellReading_eq_of_lt hh hag hdh x]
    refine le_sup (f := fun e ↦ cellReading k w' e x) (mem_filter.mpr ⟨mem_univ d, ?_⟩)
    rw [← orbitCode_eq_of_min_eq hh hag hdh]
    exact (mem_filter.mp hd).2
  · have hlt : visibilityReplace k k x < visibilityReplace k k (orbitCode k w d) :=
      hx.trans_le (le_visibilityReplace_orbitCode h0 hk hγ hdh)
    unfold cellReading
    rw [ite_eq_left hlt]
    exact bot_le

/-- **The gap values agree capped at `h`**, when `h` is a member of the code grid self-visible at
`k`. -/
private theorem min_gapValue_le (hhB : h ∈ codeGrid 3 B) (hhk : IsSelfVisible k h)
    (hag : ∀ d, min (w d) h = min (w' d) h) (x : Label.{u}) :
    min (gapValue k B w x) h ≤ min (gapValue k B w' x) h := by
  classical
  by_cases hx0 : x = ⊥
  · rw [hx0, gapValue_bot, gapValue_bot]
  rw [gapValue_of_ne_bot hx0, gapValue_of_ne_bot hx0]
  refine le_min (le_min ((min_le_left _ _).trans (min_le_left _ _)) (Finset.le_inf fun d hd ↦ ?_))
    (min_le_right _ _)
  rcases lt_or_ge (w d) h with hdh | hdh
  · have hmem : d ∈ ({e | visibilityReplace k k x ≤ visibilityReplace k k (orbitCode k w e)} :
        Finset ι) := by
      refine mem_filter.mpr ⟨mem_univ d, ?_⟩
      rw [orbitCode_eq_of_min_eq (hhk) hag hdh]
      exact (mem_filter.mp hd).2
    rw [eq_of_min_eq_of_lt (hag d) hdh]
    exact (min_le_left _ _).trans ((min_le_right _ _).trans (Finset.inf_le hmem))
  · exact (min_le_right _ _).trans
      (le_admissibleBelow hhB hhk (le_of_min_eq_of_le (hag d) hdh))

/-- At or above the separating grid point the gap value is at least `h`. -/
private theorem le_gapValue (hk : k < 3) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((3 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}))
    (hhB : h ∈ codeGrid 3 B) (hhT : h ≤ gridPoint 3 B)
    (hx : gridPoint k (2 * #(keysBelow k w h) + 1) ≤ visibilityReplace k k x) :
    h ≤ gapValue k B w x := by
  classical
  have hhk : IsSelfVisible k h := by
    rw [hγ]; exact isSelfVisible_block.mpr (by omega)
  have hx0 : x ≠ ⊥ := fun h' ↦ by
    rw [h', visibilityReplace_bot, le_bot_iff] at hx
    exact gridPoint_ne_bot _ _ hx
  rw [gapValue_of_ne_bot hx0]
  refine le_min hhT (Finset.le_inf fun d hd ↦ ?_)
  rcases lt_or_ge (w d) h with hdh | hdh
  · exact absurd ((mem_filter.mp hd).2.trans_lt ((visibilityReplace_orbitCode_lt hk hγ hdh)))
      (not_lt.mpr hx)
  · exact le_admissibleBelow hhB hhk hdh

/-- **Capped agreement of the decoded agreement heights.**  For a grade `k < 3`, let `w` have
values at most `ω * B + 3`, and let `w'` agree with `w` capped at a cap `h` self-visible and short
at `3`.  Then, for every labelling `e`, the upper decoders of `w` and `w'` at the agreement
heights of their orbit codes with `e`, in the grid of grade `k` with a block bound at least
`2 N + 1` for `N` cells, agree capped at `h`. -/
theorem min_upperDecoder_agreementHeight_eq (hk : k < 3) {B' : ℕ}
    (hB' : 2 * Fintype.card ι + 1 ≤ B') (hh : IsSelfVisible 3 h) (hs : IsShort 3 h)
    (hw : ∀ d, w d ≤ gridPoint 3 B) (hag : ∀ d, min (w d) h = min (w' d) h) (e : ι → Label.{u}) :
    min (upperDecoder k B w (agreementHeight (grid k B') (orbitCode k w) e)) h =
      min (upperDecoder k B w' (agreementHeight (grid k B') (orbitCode k w') e)) h := by
  classical
  by_cases h0 : h = ⊥
  · rw [h0, min_bot_right, min_bot_right]
  by_cases hT : h ≤ gridPoint 3 B
  swap
  · -- Above every value the two labellings are equal.
    have : w' = w := funext fun d ↦ eq_of_min_eq_of_lt (hag d) ((hw d).trans_lt (not_le.mp hT))
    rw [this]
  have htop : h ≠ ⊤ := ne_top_of_le_ne_top (gridPoint_ne_top 3 B) hT
  obtain ⟨γ, hγ⟩ := exists_eq_block_three hh hs h0 htop
  have hhk : IsSelfVisible k h := by
    rw [hγ]; exact isSelfVisible_block.mpr (by omega)
  have hhB : h ∈ codeGrid 3 B := by
    have hle := hT
    rw [hγ, gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe,
      omega0_mul_add_natCast_le_iff] at hle
    have hγB : γ ≤ (B : Ordinal.{u}) := by
      rcases hle with hle | ⟨hle, -⟩
      exacts [hle.le, hle.le]
    obtain ⟨g, rfl⟩ : ∃ g : ℕ, γ = g :=
      Ordinal.lt_omega0.mp (hγB.trans_lt (Ordinal.natCast_lt_omega0 _))
    rw [hγ]
    exact mem_codeGrid.mpr (.inr ⟨g, by exact_mod_cast hγB, 3, le_rfl, rfl⟩)
  have hag' : ∀ d, min (w' d) h = min (w d) h := fun d ↦ (hag d).symm
  have hL : keysBelow k w' h = keysBelow k w h := (keysBelow_congr hag).symm
  set Γ : Label.{u} := gridPoint k (2 * #(keysBelow k w h) + 1) with hΓ
  have hΓg : Γ ∈ grid k B' :=
    gridPoint_mem_grid (by have := card_keysBelow_le k w h; omega)
  -- The two orbit codes agree capped at `Γ`.
  have hcc (d : ι) : min (orbitCode k w d) Γ = min (orbitCode k w' d) Γ := by
    rcases lt_or_ge (w d) h with hdh | hdh
    · rw [orbitCode_eq_of_min_eq hhk hag hdh]
    · have h1 := le_orbitCode (k := k) h0 hk hγ hdh
      have h2 := le_orbitCode (k := k) h0 hk hγ (le_of_min_eq_of_le (hag d) hdh)
      rw [hL] at h2
      rw [min_eq_right h1, min_eq_right h2]
  set κ := agreementHeight (grid k B') (orbitCode k w) e with hκ
  set κ' := agreementHeight (grid k B') (orbitCode k w') e with hκ'
  have hG : (⊥ : Label.{u}) ∈ grid k B' := bot_mem_grid k B'
  have hle : Γ ≤ agreementHeight (grid k B') (orbitCode k w) (orbitCode k w') :=
    le_agreementHeight hΓg hcc
  have hκκ : min κ Γ = min κ' Γ := by
    set A := agreementHeight (grid k B') (orbitCode k w) (orbitCode k w') with hA
    calc min κ Γ = min (min κ A) Γ := by rw [min_assoc, min_eq_right hle]
      _ = min (min κ' A) Γ := by rw [hκ, hκ', hA, agreementHeight_tri hG]
      _ = min κ' Γ := by rw [min_assoc, min_eq_right hle]
  have hsv (z : Label.{u}) (hz : z ∈ grid k B') : visibilityReplace k k z = z :=
    isSelfVisible_of_mem_grid hz
  have hκg : κ ∈ grid k B' := (agreementHeight_spec hG _ _).1
  have hκg' : κ' ∈ grid k B' := (agreementHeight_spec hG _ _).1
  rcases lt_or_ge κ Γ with hlt | hge
  · -- Below `Γ`: one agreement height, read alike.
    have hκeq : κ' = κ := by
      rw [min_eq_left hlt.le] at hκκ
      rcases lt_or_ge κ' Γ with hlt' | hge'
      · rw [min_eq_left hlt'.le] at hκκ; exact hκκ.symm
      · rw [min_eq_right hge'] at hκκ; exact absurd hκκ hlt.ne
    rw [hκeq, upperDecoder, upperDecoder, min_max_distrib_right, min_max_distrib_right]
    have hx : visibilityReplace k k κ < Γ := by rw [hsv κ hκg]; exact hlt
    have hx' : visibilityReplace k k κ < gridPoint k (2 * #(keysBelow k w' h) + 1) := by
      rw [hL]; exact hx
    congr 1
    · rw [le_antisymm (orbitDecoder_le_of_lt h0 hk hγ hag hx)
        (orbitDecoder_le_of_lt h0 hk hγ hag' hx')]
    · exact le_antisymm (min_gapValue_le hhB hhk hag κ) (min_gapValue_le hhB hhk hag' κ)
  · -- At or above `Γ`: both decoded labels are at least `h`.
    have hge' : Γ ≤ κ' := by
      rw [min_eq_right hge] at hκκ
      exact min_eq_right_iff.mp hκκ.symm
    have hx : Γ ≤ visibilityReplace k k κ := by rw [hsv κ hκg]; exact hge
    have hx' : gridPoint k (2 * #(keysBelow k w' h) + 1) ≤ visibilityReplace k k κ' := by
      rw [hL, hsv κ' hκg']; exact hge'
    have h1 : h ≤ upperDecoder k B w κ := (le_gapValue hk hγ hhB hT hx).trans (le_max_right _ _)
    have h2 : h ≤ upperDecoder k B w' κ' :=
      (le_gapValue hk hγ hhB hT hx').trans (le_max_right _ _)
    rw [min_eq_right h1, min_eq_right h2]

end VaughtConjecture.Label
