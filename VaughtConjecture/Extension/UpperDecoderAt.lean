/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OrbitCode

/-!
# The upper decoder: an orbit decoder that reads the gaps between codes upward

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at every arity;
here the label map behind the section operator of each level, with capped agreement at the caps
self-visible and short at a cap grade `K`).

The extension at the cap `⊥` through a canonical field layer at a grade `k` (the layer of one cell
of full scope and grade `k` for each catalogue entry, `Scheme.fieldLayer`;
`Scheme.exists_isLawfulBelow_fieldLayer`) reads the field row of the orbit code of a labelling `w`
by the orbit decoder at the least grid point (`Label.orbitDecoder`).  That decoder reads a label
strictly between the codes of two keys of `w` as the lower key: at an agreement height in such a
gap the decoded label lies below the next value of `w`, however far above it that value is.  Two
labellings that agree capped at a cap `h` self-visible and short at `K > k`, but not short at `k`,
can then decode one agreement height below `h` and the other above it.

**The upper decoder** (`Label.upperDecoderAt k K B w`) is the larger of the orbit decoder and the
*gap value* (`Label.gapValueAt`): at a label `x` other than bottom, the least, over the cells `d`
whose code has key at least the key of `x`, of the largest member of the code grid
`Label.codeGrid K B` self-visible at `K` and at most `w d` (`Label.admissibleBelowAt`), and at most
the grid point `ω * B + K`.  Compiled in this repository (theorem named):

* for `k ≤ K` it is a witness bounded by the grade `k` (`Label.isWitness_upperDecoderAt`), sends
  only bottom to bottom (`Label.eq_bot_of_upperDecoderAt_eq_bot`), and reads the orbit code
  literally (`Label.upperDecoderAt_orbitCode`); it takes values in the code grid
  (`Label.upperDecoderAt_mem_codeGrid`, `Label.upperDecoderAt_mem_codeGrid_of_mem`);
* **capped agreement**, for `k < K`, at every cap `h` self-visible and short at `K`
  (`Label.min_upperDecoderAt_agreementHeight_eq`, and `Label.min_upperDecoderAt_comp_eq` for any
  construction on the orbit codes keeping capped agreement at the caps self-visible and short at
  `k`): with `R` the number of keys of `w` below `h`, the grid point `Γ = ω * (2 R + 1) + k`
  separates the codes of the values below `h` from those of the values at least `h`, so below `Γ`
  the two decoders read the same cells, and at or above `Γ` the gap values are at least `h`;
* **readable labels** (`Label.IsReadableAt K`): a label is readable for `Q` when it is bottom,
  self-visible at `K`, or its key at `K` is an orbit key of `Q` or not a key of `Q`.  The orbit
  decoder at the grade `K` reads a readable label literally below its cap
  (`Label.min_orbitDecoder_eq_of_isReadableAt`), and the upper decoder keeps readability for an
  orbit-canonical `Q` (`Label.isReadableAt_upperDecoderAt`,
  `Label.isReadableAt_upperDecoderAt_of_mem`).

At the cap grade `3` it is the decoder of the tower section (`Seed.towerSection`); at the grade
`g + 2` it is the decoder of the level at the grade `g + 1` (`ProfileTower.Lvl.next`).

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.Label

open Finset
open Ordinal hiding univ

variable {ι : Type*} [Fintype ι] {k K B : ℕ} {w w' : ι → Label.{u}} {x y h v : Label.{u}}

/-! ### Admissible labels -/

open Classical in
/-- The **admissible label below `v`** at the grade `K`: the largest member of the code grid
`codeGrid K B` that is self-visible at `K` and at most `v` (bottom if there is none). -/
noncomputable def admissibleBelowAt (K B : ℕ) (v : Label.{u}) : Label.{u} :=
  ({y ∈ codeGrid K B | IsSelfVisible K y ∧ y ≤ v} : Finset Label.{u}).sup id

/-- The admissible label below `v` is at most `v`. -/
theorem admissibleBelowAt_le (K B : ℕ) (v : Label.{u}) : admissibleBelowAt K B v ≤ v := by
  classical
  unfold admissibleBelowAt
  exact Finset.sup_le fun y hy ↦ (mem_filter.mp hy).2.2

/-- The admissible label below `v` is self-visible at `K`. -/
theorem isSelfVisible_admissibleBelowAt (K B : ℕ) (v : Label.{u}) :
    IsSelfVisible K (admissibleBelowAt K B v) := by
  classical
  unfold admissibleBelowAt
  exact Finset.sup_induction (isSelfVisible_bot K) (fun a ha b hb ↦ ha.max hb)
    fun y hy ↦ (mem_filter.mp hy).2.1

/-- The admissible label below `v` is a member of the code grid. -/
theorem admissibleBelowAt_mem_codeGrid (K B : ℕ) (v : Label.{u}) :
    admissibleBelowAt K B v ∈ codeGrid K B := by
  classical
  unfold admissibleBelowAt
  refine Finset.sup_induction (p := fun z ↦ z ∈ codeGrid K B) (mem_insert_self _ _)
    (fun a ha b hb ↦ ?_) fun y hy ↦ (mem_filter.mp hy).1
  rcases le_total a b with hab | hab
  · rwa [show a ⊔ b = b from max_eq_right hab]
  · rwa [show a ⊔ b = a from max_eq_left hab]

/-- A member of the code grid self-visible at `K` and at most `v` is at most the admissible label
below `v`. -/
theorem le_admissibleBelowAt (hy : y ∈ codeGrid K B) (hv : IsSelfVisible K y) (hyv : y ≤ v) :
    y ≤ admissibleBelowAt K B v := by
  classical
  unfold admissibleBelowAt
  exact le_sup (f := id) (mem_filter.mpr ⟨hy, hv, hyv⟩)

/-! ### The gap value and the upper decoder -/

open Classical in
/-- The **gap value** of `w` at `x`: bottom at bottom; otherwise the least admissible label below
the values of `w` at the cells whose orbit code has key at least the key of `x`, at most
`ω * B + K`. -/
noncomputable def gapValueAt (k K B : ℕ) (w : ι → Label.{u}) (x : Label.{u}) : Label.{u} :=
  if x = ⊥ then ⊥ else min (gridPoint K B)
    (({d | visibilityReplace k k x ≤ visibilityReplace k k (orbitCode k w d)} : Finset ι).inf
      fun d ↦ admissibleBelowAt K B (w d))

/-- The **upper decoder** of `w` at grade `k` with block bound `B`: the larger of the orbit
decoder at the least grid point and the gap value. -/
noncomputable def upperDecoderAt (k K B : ℕ) (w : ι → Label.{u}) (x : Label.{u}) : Label.{u} :=
  max (orbitDecoder k w (gridPoint k 0) x) (gapValueAt k K B w x)

/-- The gap value at bottom. -/
@[simp] theorem gapValueAt_bot : gapValueAt k K B w ⊥ = ⊥ := by
  unfold gapValueAt
  exact ite_eq_left rfl

/-- The gap value off bottom. -/
theorem gapValueAt_of_ne_bot (hx : x ≠ ⊥) : gapValueAt k K B w x = min (gridPoint K B)
    (({d | visibilityReplace k k x ≤ visibilityReplace k k (orbitCode k w d)} : Finset ι).inf
      fun d ↦ admissibleBelowAt K B (w d)) := by
  unfold gapValueAt
  exact ite_eq_right hx

/-- The gap value is self-visible at `k`, for `k ≤ K`. -/
theorem isSelfVisible_gapValueAt (hk : k ≤ K) (x : Label.{u}) :
    IsSelfVisible k (gapValueAt k K B w x) := by
  by_cases hx : x = ⊥
  · rw [hx, gapValueAt_bot]
    exact isSelfVisible_bot k
  rw [gapValueAt_of_ne_bot hx]
  exact ((isSelfVisible_gridPoint K B).mono hk).min (Finset.inf_induction (isSelfVisible_top k)
    (fun a ha b hb ↦ ha.min hb) fun d _ ↦ (isSelfVisible_admissibleBelowAt K B (w d)).mono hk)

/-- The gap value is at most `ω * B + K`. -/
theorem gapValueAt_le_gridPoint (x : Label.{u}) : gapValueAt k K B w x ≤ gridPoint K B := by
  by_cases hx : x = ⊥
  · rw [hx, gapValueAt_bot]
    exact bot_le
  rw [gapValueAt_of_ne_bot hx]
  exact min_le_left _ _

/-- The gap value depends on the key of the label only. -/
theorem gapValueAt_visibilityReplace {j i : ℕ} (hi : i ≤ j) (hj : j ≤ k) (x : Label.{u}) :
    gapValueAt k K B w (visibilityReplace j i x) = gapValueAt k K B w x := by
  by_cases hx : x = ⊥
  · rw [hx, visibilityReplace_bot]
  have hx' : visibilityReplace j i x ≠ ⊥ := by rwa [Ne, visibilityReplace_eq_bot_iff]
  rw [gapValueAt_of_ne_bot hx, gapValueAt_of_ne_bot hx',
    visibilityReplace_self_visibilityReplace_of_le hi hj]

/-- The gap value is monotone. -/
theorem monotone_gapValueAt : Monotone (gapValueAt k K B w) := by
  classical
  intro x y hxy
  by_cases hx : x = ⊥
  · rw [hx, gapValueAt_bot]
    exact bot_le
  have hy : y ≠ ⊥ := ne_bot_of_le_ne_bot hx hxy
  rw [gapValueAt_of_ne_bot hx, gapValueAt_of_ne_bot hy]
  refine min_le_min_left _ (Finset.inf_mono fun d hd ↦ ?_)
  rw [mem_filter] at hd ⊢
  exact ⟨mem_univ d, (monotone_visibilityReplace le_rfl hxy).trans hd.2⟩

/-- At the code of a cell, the gap value is at most the value there. -/
theorem gapValueAt_orbitCode_le (d : ι) : gapValueAt k K B w (orbitCode k w d) ≤ w d := by
  classical
  by_cases hd : w d = ⊥
  · rw [orbitCode_eq_bot_iff.mpr hd, gapValueAt_bot]
    exact bot_le
  rw [gapValueAt_of_ne_bot (by rwa [Ne, orbitCode_eq_bot_iff])]
  have hmem : d ∈ ({e | visibilityReplace k k (orbitCode k w d) ≤
      visibilityReplace k k (orbitCode k w e)} : Finset ι) := mem_filter.mpr ⟨mem_univ d, le_rfl⟩
  exact (min_le_right _ _).trans ((Finset.inf_le hmem).trans (admissibleBelowAt_le K B (w d)))

/-- The orbit decoder at the least grid point is a witness bounded by the grade `k`. -/
private theorem isWitness_orbitDecoder_zero :
    IsWitness (stepSuppressor.{u} k) (orbitDecoder k w (gridPoint k 0)) :=
  isWitness_orbitDecoder (isSelfVisible_gridPoint k 0) (gridPoint_ne_bot k 0)

/-- The upper decoder sends only bottom to bottom. -/
theorem eq_bot_of_upperDecoderAt_eq_bot (hx : upperDecoderAt k K B w x = ⊥) : x = ⊥ :=
  eq_bot_of_orbitDecoder_eq_bot (gridPoint_ne_bot k 0)
    (le_bot_iff.mp ((le_max_left _ _).trans hx.le))

/-- The upper decoder fixes bottom. -/
@[simp] theorem upperDecoderAt_bot : upperDecoderAt k K B w ⊥ = ⊥ := by
  rw [upperDecoderAt, orbitDecoder_bot, gapValueAt_bot, max_self]

/-- **The upper decoder is a witness bounded by the grade `k`**, for `k ≤ K`. -/
theorem isWitness_upperDecoderAt (hk : k ≤ K) :
    IsWitness (stepSuppressor.{u} k) (upperDecoderAt k K B w) where
  antitone := (IsWitness.id_step k).antitone
  isSelfVisible := (IsWitness.id_step k).isSelfVisible
  map_bot := upperDecoderAt_bot
  monotone _ _ hxy :=
    max_le_max (isWitness_orbitDecoder_zero.monotone hxy) (monotone_gapValueAt hxy)
  visibilityReplace_comm x j hx i hi := by
    by_cases hj : j ≤ k
    · rw [upperDecoderAt, upperDecoderAt, visibilityReplace_max hi,
        isWitness_orbitDecoder_zero.visibilityReplace_comm x j
          (by rw [stepSuppressor_of_le hj]; exact le_top) i hi,
        gapValueAt_visibilityReplace hi hj,
        ((isSelfVisible_gapValueAt hk x).mono hj).visibilityReplace_eq]
    · rw [stepSuppressor_of_lt (not_le.mp hj), le_bot_iff] at hx
      rw [eq_bot_of_upperDecoderAt_eq_bot hx, visibilityReplace_bot, upperDecoderAt_bot,
        visibilityReplace_bot]

/-- **The upper decoder reads the orbit code literally.** -/
theorem upperDecoderAt_orbitCode (d : ι) : upperDecoderAt k K B w (orbitCode k w d) = w d := by
  rw [upperDecoderAt, orbitDecoder_orbitCode (fun e ↦ min_orbitCode_gridPoint_zero e)]
  exact max_eq_left (gapValueAt_orbitCode_le d)

/-! ### Values in the code grid -/

/-- The larger of two members of a finite set of labels is a member. -/
private theorem max_mem {S : Finset Label.{u}} (hx : x ∈ S) (hy : y ∈ S) : max x y ∈ S := by
  rcases le_total x y with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

/-- A block point with finite part at most `K` and block at most `B` is in the code grid. -/
private theorem block_mem_codeGrid {b f : ℕ} (hb : b ≤ B) (hf : f ≤ K) :
    ((ω * (b : Ordinal.{u}) + (f : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) ∈ codeGrid K B :=
  mem_codeGrid.mpr (.inr ⟨b, hb, f, hf, rfl⟩)

omit [Fintype ι] in
/-- A least admissible label over a set of cells is the formal top or in the code grid. -/
private theorem inf_admissibleBelowAt_cases (w : ι → Label.{u}) (S : Finset ι) :
    S.inf (fun d ↦ admissibleBelowAt K B (w d)) = ⊤ ∨
      S.inf (fun d ↦ admissibleBelowAt K B (w d)) ∈ codeGrid K B := by
  refine Finset.inf_induction (p := fun z ↦ z = ⊤ ∨ z ∈ codeGrid K B) (.inl rfl)
    (fun a ha b hb ↦ ?_) fun d _ ↦ .inr (admissibleBelowAt_mem_codeGrid K B (w d))
  rcases ha with rfl | ha
  · rw [show (⊤ : Label.{u}) ⊓ b = b from top_inf_eq b]; exact hb
  rcases hb with rfl | hb
  · rw [show a ⊓ (⊤ : Label.{u}) = a from inf_top_eq a]; exact .inr ha
  rcases le_total a b with h | h
  · rw [show a ⊓ b = a from min_eq_left h]; exact .inr ha
  · rw [show a ⊓ b = b from min_eq_right h]; exact .inr hb

/-- **On the grid of grade `k`, the upper decoder takes values in the code grid** when `w` does,
for `k ≤ K`. -/
theorem upperDecoderAt_mem_codeGrid (hk : k ≤ K) (hw : ∀ d, w d ∈ codeGrid K B) {B' : ℕ}
    (hx : x ∈ grid k B') : upperDecoderAt k K B w x ∈ codeGrid K B := by
  have hbot : (⊥ : Label.{u}) ∈ codeGrid K B := mem_insert_self _ _
  refine max_mem (max_mem ?_ ?_) ?_
  · -- The capped label: bottom or the least grid point.
    rcases mem_grid.mp hx with rfl | ⟨b, -, rfl⟩
    · rwa [min_eq_left bot_le]
    · rw [min_eq_right (gridPoint_le_gridPoint.mpr (Nat.zero_le b))]
      exact block_mem_codeGrid (Nat.zero_le B) hk
  · refine Finset.sup_induction (p := fun z ↦ z ∈ codeGrid K B) hbot
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
    · rw [hx0, gapValueAt_bot]; exact hbot
    rw [gapValueAt_of_ne_bot hx0]
    have hT : gridPoint.{u} K B ∈ codeGrid K B := block_mem_codeGrid le_rfl le_rfl
    rcases inf_admissibleBelowAt_cases (K := K) (B := B) w (({d | visibilityReplace k k x ≤
      visibilityReplace k k (orbitCode k w d)} : Finset ι)) with htop | hmem
    · rw [htop, min_eq_left le_top]; exact hT
    · rcases le_total (gridPoint.{u} K B) _ with h | h
      · rw [min_eq_left h]; exact hT
      · rw [min_eq_right h]; exact hmem

/-! ### Keys below a cap self-visible and short at `K` -/

/-- A label self-visible and short at `K`, other than bottom and the formal top, is
`ω * γ + K`. -/
private theorem exists_eq_block_of_isShort (hh : IsSelfVisible K h) (hs : IsShort K h) (h0 : h ≠ ⊥)
    (ht : h ≠ ⊤) : ∃ γ : Ordinal.{u}, h = ((ω * γ + ((K : ℕ) : Ordinal.{u}) : Ordinal.{u}) :
      Label.{u}) := by
  obtain ⟨q, n, rfl⟩ := exists_block h0 ht
  have h1 := isSelfVisible_block.mp hh
  rw [isShort_coe, mul_add_mod_self, mod_eq_of_lt (natCast_lt_omega0 n)] at hs
  have h2 : n ≤ K := by exact_mod_cast hs
  exact ⟨q, by rw [show n = K by omega]⟩

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

/-- **Below a cap `ω * γ + K`, keys at a grade `k < K` stay below the cap.** -/
private theorem visibilityReplace_lt (hk : k < K) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((K : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) (hy : y < h) :
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

/-- A value below a cap `ω * γ + K` has key rank at most the number of keys below the cap. -/
private theorem keyRank_le_card_keysBelow (hk : k < K) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((K : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) {d : ι}
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

/-- The least grid point lies below a cap `ω * γ + K`, at a grade `k < K`. -/
private theorem gridPoint_zero_lt (hk : k < K) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((K : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) :
    gridPoint.{u} k 0 < h := by
  rw [hγ, gridPoint, Nat.cast_zero]
  rcases eq_or_ne γ 0 with rfl | hγ0
  · exact block_lt_block_iff.mpr (.inr ⟨rfl, hk⟩)
  · exact block_lt_block_iff.mpr (.inl (pos_iff_ne_zero.mpr hγ0))

/-- **The code blocks of the values at least `h` are at least `2 R + 1`**, `R` the number of keys
below `h`. -/
private theorem le_codeBlock_of_le (h0 : h ≠ ⊥) (hk : k < K) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((K : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) {d : ι}
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
private theorem visibilityReplace_orbitCode_lt (hk : k < K) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((K : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) {d : ι}
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
private theorem le_visibilityReplace_orbitCode (h0 : h ≠ ⊥) (hk : k < K) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((K : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) {d : ι}
    (hd : h ≤ w d) :
    gridPoint k (2 * #(keysBelow k w h) + 1) ≤ visibilityReplace k k (orbitCode k w d) := by
  rw [orbitCode_apply, visibilityReplace_orbitMap (ne_bot_of_le_ne_bot h0 hd),
    gridPoint_le_gridPoint]
  exact (le_codeBlock_of_le h0 hk hγ hd).1

/-- (F3) The codes of the values at least `h` are at least `ω * (2 R + 1) + k`. -/
private theorem le_orbitCode (h0 : h ≠ ⊥) (hk : k < K) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((K : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) {d : ι}
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
private theorem orbitDecoder_le_of_lt (h0 : h ≠ ⊥) (hk : k < K) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((K : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}))
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
`K` and at `k`. -/
private theorem min_gapValueAt_le (hhB : h ∈ codeGrid K B) (hh3 : IsSelfVisible K h)
    (hhk : IsSelfVisible k h) (hag : ∀ d, min (w d) h = min (w' d) h) (x : Label.{u}) :
    min (gapValueAt k K B w x) h ≤ min (gapValueAt k K B w' x) h := by
  classical
  by_cases hx0 : x = ⊥
  · rw [hx0, gapValueAt_bot, gapValueAt_bot]
  rw [gapValueAt_of_ne_bot hx0, gapValueAt_of_ne_bot hx0]
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
      (le_admissibleBelowAt hhB hh3 (le_of_min_eq_of_le (hag d) hdh))

/-- At or above the separating grid point the gap value is at least `h`. -/
private theorem le_gapValueAt (hk : k < K) {γ : Ordinal.{u}}
    (hγ : h = ((ω * γ + ((K : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}))
    (hhB : h ∈ codeGrid K B) (hhT : h ≤ gridPoint K B)
    (hx : gridPoint k (2 * #(keysBelow k w h) + 1) ≤ visibilityReplace k k x) :
    h ≤ gapValueAt k K B w x := by
  classical
  have hx0 : x ≠ ⊥ := fun h' ↦ by
    rw [h', visibilityReplace_bot, le_bot_iff] at hx
    exact gridPoint_ne_bot _ _ hx
  rw [gapValueAt_of_ne_bot hx0]
  refine le_min hhT (Finset.le_inf fun d hd ↦ ?_)
  rcases lt_or_ge (w d) h with hdh | hdh
  · exact absurd ((mem_filter.mp hd).2.trans_lt ((visibilityReplace_orbitCode_lt hk hγ hdh)))
      (not_lt.mpr hx)
  · exact le_admissibleBelowAt hhB (by rw [hγ]; exact isSelfVisible_block.mpr le_rfl) hdh

/-- **Capped agreement of the decoded agreement heights.**  For a grade `k < K`, let `w` have
values at most `ω * B + K`, and let `w'` agree with `w` capped at a cap `h` self-visible and short
at `K`.  Then, for every labelling `e`, the upper decoders of `w` and `w'` at the agreement
heights of their orbit codes with `e`, in the grid of grade `k` with a block bound at least
`2 N + 1` for `N` cells, agree capped at `h`. -/
theorem min_upperDecoderAt_agreementHeight_eq (hk : k < K) {B' : ℕ}
    (hB' : 2 * Fintype.card ι + 1 ≤ B') (hh : IsSelfVisible K h) (hs : IsShort K h)
    (hw : ∀ d, w d ≤ gridPoint K B) (hag : ∀ d, min (w d) h = min (w' d) h) (e : ι → Label.{u}) :
    min (upperDecoderAt k K B w (agreementHeight (grid k B') (orbitCode k w) e)) h =
      min (upperDecoderAt k K B w' (agreementHeight (grid k B') (orbitCode k w') e)) h := by
  classical
  by_cases h0 : h = ⊥
  · rw [h0, min_bot_right, min_bot_right]
  by_cases hT : h ≤ gridPoint K B
  swap
  · -- Above every value the two labellings are equal.
    have : w' = w := funext fun d ↦ eq_of_min_eq_of_lt (hag d) ((hw d).trans_lt (not_le.mp hT))
    rw [this]
  have htop : h ≠ ⊤ := ne_top_of_le_ne_top (gridPoint_ne_top K B) hT
  obtain ⟨γ, hγ⟩ := exists_eq_block_of_isShort hh hs h0 htop
  have hhk : IsSelfVisible k h := by
    rw [hγ]; exact isSelfVisible_block.mpr (by omega)
  have hhB : h ∈ codeGrid K B := by
    have hle := hT
    rw [hγ, gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe,
      omega0_mul_add_natCast_le_iff] at hle
    have hγB : γ ≤ (B : Ordinal.{u}) := by
      rcases hle with hle | ⟨hle, -⟩
      exacts [hle.le, hle.le]
    obtain ⟨g, rfl⟩ : ∃ g : ℕ, γ = g :=
      Ordinal.lt_omega0.mp (hγB.trans_lt (Ordinal.natCast_lt_omega0 _))
    rw [hγ]
    exact mem_codeGrid.mpr (.inr ⟨g, by exact_mod_cast hγB, K, le_rfl, rfl⟩)
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
    rw [hκeq, upperDecoderAt, upperDecoderAt, min_max_distrib_right, min_max_distrib_right]
    have hx : visibilityReplace k k κ < Γ := by rw [hsv κ hκg]; exact hlt
    have hx' : visibilityReplace k k κ < gridPoint k (2 * #(keysBelow k w' h) + 1) := by
      rw [hL]; exact hx
    congr 1
    · rw [le_antisymm (orbitDecoder_le_of_lt h0 hk hγ hag hx)
        (orbitDecoder_le_of_lt h0 hk hγ hag' hx')]
    · exact le_antisymm (min_gapValueAt_le hhB hh hhk hag κ) (min_gapValueAt_le hhB hh hhk hag' κ)
  · -- At or above `Γ`: both decoded labels are at least `h`.
    have hge' : Γ ≤ κ' := by
      rw [min_eq_right hge] at hκκ
      exact min_eq_right_iff.mp hκκ.symm
    have hx : Γ ≤ visibilityReplace k k κ := by rw [hsv κ hκg]; exact hge
    have hx' : gridPoint k (2 * #(keysBelow k w' h) + 1) ≤ visibilityReplace k k κ' := by
      rw [hL, hsv κ' hκg']; exact hge'
    have h1 : h ≤ upperDecoderAt k K B w κ :=
      (le_gapValueAt hk hγ hhB hT hx).trans (le_max_right _ _)
    have h2 : h ≤ upperDecoderAt k K B w' κ' :=
      (le_gapValueAt hk hγ hhB hT hx').trans (le_max_right _ _)
    rw [min_eq_right h1, min_eq_right h2]

/-! ### Labels read literally by the orbit decoder at the grade `K` -/

/-- A label `x` is **readable** for `Q` when it is bottom, self-visible at `K`, or its key at `K`
is an orbit key of `Q` or not a key of `Q`: the orbit decoders at the grade `K` of the labellings
coded by `Q` read it literally below their cap (`Label.min_orbitDecoder_eq_of_isReadableAt`). -/
def IsReadableAt (K : ℕ) {κ : Type*} (Q : κ → Label.{u}) (x : Label.{u}) : Prop :=
  x = ⊥ ∨ IsSelfVisible K x ∨ IsOrbitKey K Q x ∨ ¬ IsKey K Q x

omit [Fintype ι] in
/-- Readability off the self-visible labels depends only on the key at `K`. -/
private theorem isReadableAt_of_key {κ : Type*} {Q : κ → Label.{u}} (hy : IsReadableAt K Q y)
    (hy3 : ¬ IsSelfVisible K y)
    (hxy : visibilityReplace K K x = visibilityReplace K K y) : IsReadableAt K Q x := by
  rcases hy with rfl | h | h | h
  · exact absurd (isSelfVisible_bot K) hy3
  · exact absurd h hy3
  · exact .inr (.inr (.inl ((isOrbitKey_congr hxy).mpr h)))
  · exact .inr (.inr (.inr fun h' ↦ h ((isKey_congr hxy).mp h')))

omit [Fintype ι] in
/-- The larger of two readable labels is readable. -/
private theorem IsReadableAt.max {κ : Type*} {Q : κ → Label.{u}} (hx : IsReadableAt K Q x)
    (hy : IsReadableAt K Q y) : IsReadableAt K Q (max x y) := by
  rcases le_total x y with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

omit [Fintype ι] in
/-- The values of `Q` are readable for `Q`. -/
theorem isReadableAt_apply (Q : ι → Label.{u}) (d : ι) : IsReadableAt K Q (Q d) := by
  by_cases h3 : IsSelfVisible K (Q d)
  · exact .inr (.inl h3)
  · exact .inr (.inr (.inl (isOrbitKey_of_not_isSelfVisible h3)))

/-- In an orbit-canonical labelling, a value with the key `K` of the natural strip has an orbit
key: a key that is not an orbit key has a code block at least `1`. -/
private theorem isOrbitKey_of_key_natural {κ : Type*} [Fintype κ] {Q : κ → Label.{u}}
    (hQ : orbitCode K Q = Q) {d : κ}
    (hd : Q d ≠ ⊥) (hk : visibilityReplace K K (Q d) = gridPoint K 0) : IsOrbitKey K Q (Q d) := by
  by_contra ho
  have hcb := codeBlock_of_not_isOrbitKey (isKey_apply_iff.mpr hd) ho
  have h1 := one_le_keyRank (k := K) (isKey_apply_iff.mpr hd)
  have hkey := visibilityReplace_orbitMap (w := Q) (k := K) hd
  rw [← orbitCode_apply, hQ, hk, hcb] at hkey
  have := gridPoint_le_gridPoint.mp hkey.ge
  omega

/-- Block points are equal exactly when their blocks and finite parts are. -/
private theorem block_eq_block_iff {q γ : Ordinal.{u}} {n m : ℕ} :
    ((ω * q + n : Ordinal.{u}) : Label.{u}) = ((ω * γ + m : Ordinal.{u}) : Label.{u}) ↔
      q = γ ∧ n = m := by
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2⟩ ↦ by rw [h1, h2]⟩
  rcases lt_trichotomy q γ with hlt | rfl | hgt
  · exact absurd h (block_lt_block_iff.mpr (.inl hlt)).ne
  · refine ⟨rfl, ?_⟩
    rcases lt_trichotomy n m with hlt | rfl | hgt
    · exact absurd h (block_lt_block_iff.mpr (.inr ⟨rfl, hlt⟩)).ne
    · rfl
    · exact absurd h.symm (block_lt_block_iff.mpr (.inr ⟨rfl, hgt⟩)).ne
  · exact absurd h.symm (block_lt_block_iff.mpr (.inl hgt)).ne

omit [Fintype ι] in
/-- A value of finite part `K` in the code grid has an orbit key at no grade `k < K`: its strip at
`k` is itself. -/
private theorem not_isOrbitKey_of_isSelfVisible_of_lt (hk : k < K)
    (hwB : ∀ d, w d ∈ codeGrid K B) {d : ι} (h3 : IsSelfVisible K (w d)) :
    ¬ IsOrbitKey k w (w d) := by
  rintro ⟨e, hek, hesv⟩
  rw [(h3.mono hk.le).visibilityReplace_eq k] at hek
  rcases mem_codeGrid.mp (hwB e) with he0 | ⟨b, -, f, -, he⟩
  · exact hesv (he0 ▸ isSelfVisible_bot k)
  rcases mem_codeGrid.mp (hwB d) with hd0 | ⟨b', -, f', hf', hd⟩
  · rw [hd0] at h3 hek
    rw [visibilityReplace_eq_bot_iff] at hek
    exact hesv (hek ▸ isSelfVisible_bot k)
  rw [hd] at h3 hek
  rw [he] at hek hesv
  have hf3 : K ≤ f' := isSelfVisible_block.mp h3
  rw [visibilityReplace_block, block_eq_block_iff] at hek
  exact hesv (isSelfVisible_block.mpr (by split_ifs at hek <;> omega))

/-- **The upper decoder keeps readability**: for `k < K`, if the values of `w` lie in the code grid
and are readable for an orbit-canonical `Q`, so is the upper decoder at every point of the grid of
grade `k`. -/
theorem isReadableAt_upperDecoderAt {κ : Type*} [Fintype κ] {Q : κ → Label.{u}}
    (hQ : orbitCode K Q = Q) (hk : k < K)
    (hwB : ∀ d, w d ∈ codeGrid K B) (hw : ∀ d, IsReadableAt K Q (w d)) {B' : ℕ}
    (hx : x ∈ grid k B') : IsReadableAt K Q (upperDecoderAt k K B w x) := by
  refine IsReadableAt.max (IsReadableAt.max ?_ ?_) ?_
  · -- The capped label: bottom or the least grid point `k`, of key `K`.
    rcases mem_grid.mp hx with rfl | ⟨b, -, rfl⟩
    · rw [min_eq_left bot_le]; exact .inl rfl
    rw [min_eq_right (gridPoint_le_gridPoint.mpr (Nat.zero_le b))]
    refine .inr (.inr (by_cases (fun hkey ↦ .inl ?_) fun hkey ↦ .inr hkey))
    obtain ⟨d, hd0, hdk⟩ := hkey
    have hk3 : visibilityReplace K K (gridPoint.{u} k 0) = gridPoint K 0 := by
      rw [gridPoint, gridPoint, visibilityReplace_block, ite_eq_left (by omega)]
    exact (isOrbitKey_congr hdk).mp (isOrbitKey_of_key_natural hQ hd0 (hdk.trans hk3))
  · refine Finset.sup_induction (p := IsReadableAt K Q) (.inl rfl) (fun a ha b hb ↦ ha.max hb)
      fun d _ ↦ ?_
    unfold cellReading
    split_ifs with h1 h2
    · exact .inl rfl
    · -- The block move keeps the key at `K` of the value, which is not self-visible at `K`.
      have h3 : ¬ IsSelfVisible K (w d) := fun h3 ↦
        not_isOrbitKey_of_isSelfVisible_of_lt (by omega) hwB h3 h2.2
      rcases mem_grid.mp hx with rfl | ⟨b', -, rfl⟩
      · rw [moveToBlock_bot]; exact .inl rfl
      rcases mem_codeGrid.mp (hwB d) with hd0 | ⟨b, -, f, hf, he⟩
      · exact absurd hd0 h2.2.isKey.ne_bot
      have hf3 : f < K := by
        rw [he] at h3; exact not_le.mp fun h ↦ h3 (isSelfVisible_block.mpr h)
      refine isReadableAt_of_key (hw d) h3 ?_
      rw [he, gridPoint, moveToBlock_omega0_mul_add, visibilityReplace_block,
        visibilityReplace_block, ite_eq_left (by omega), ite_eq_left hf3]
    · by_cases h3 : IsSelfVisible K (w d)
      · rw [(h3.mono (by omega)).visibilityReplace_eq k]; exact .inr (.inl h3)
      · exact isReadableAt_of_key (hw d) h3 (visibilityReplace_self_visibilityReplace_of_le le_rfl
          (by omega) _)
  · -- The gap value is self-visible at `K`.
    by_cases hx0 : x = ⊥
    · rw [hx0, gapValueAt_bot]; exact .inl rfl
    rw [gapValueAt_of_ne_bot hx0]
    exact .inr (.inl ((isSelfVisible_gridPoint K B).min (Finset.inf_induction
      (isSelfVisible_top K) (fun a ha b hb ↦ ha.min hb)
      fun d _ ↦ isSelfVisible_admissibleBelowAt K B (w d))))

/-- **The orbit decoder at the grade `K` reads a readable label literally below its cap.**  Let
the orbit code of `W` at `K` agree with `W` capped at `h`, self-visible at `K`.  Then at every
label readable for that code the orbit decoder at `h` agrees with the identity capped at `h`. -/
theorem min_orbitDecoder_eq_of_isReadableAt {W : ι → Label.{u}} (hh : IsSelfVisible K h)
    (hag : ∀ d, min (orbitCode K W d) h = min (W d) h) (hx : IsReadableAt K (orbitCode K W) x) :
    min (orbitDecoder K W h x) h = min x h := by
  rcases le_or_gt h x with hhx | hxh
  · rw [min_eq_right hhx]
    exact min_eq_right ((min_eq_right hhx).ge.trans
      (show min x h ≤ orbitDecoder K W h x from le_max_left _ _))
  rcases hx with rfl | h3 | hrest
  · rw [orbitDecoder_bot]
  · exact min_orbitDecoder_eq h3
  have hh0 : h ≠ ⊥ := ne_bot_of_gt hxh
  have hxk : visibilityReplace K K x ≤ h := (monotone_visibilityReplace le_rfl hxh.le).trans_eq hh
  -- At a cell read at `x`, the key of the code is the key of `x`, and the value has that key.
  have key (d : ι) (hd : h ≤ visibilityReplace K K (orbitCode K W d))
      (h1 : ¬ visibilityReplace K K x < visibilityReplace K K (orbitCode K W d)) :
      visibilityReplace K K (orbitCode K W d) = visibilityReplace K K x ∧
        IsOrbitKey K W (W d) ∧ visibilityReplace K K (W d) = visibilityReplace K K x := by
    have hkd : visibilityReplace K K (orbitCode K W d) = visibilityReplace K K x :=
      le_antisymm (not_lt.mp h1) (hxk.trans hd)
    have hd0 : W d ≠ ⊥ := fun h0 ↦ by
      rw [orbitCode_eq_bot_iff.mpr h0, visibilityReplace_bot] at hd
      exact hh0 (le_bot_iff.mp hd)
    rcases hrest with ⟨e, hek, hesv⟩ | hnk
    · have hQe : orbitCode K W e < h := lt_of_le_of_ne
        ((le_visibilityReplace (Nat.le_succ K) _).trans (hek.trans_le hxk)) fun h' ↦ hesv (h' ▸ hh)
      have hWe : W e = orbitCode K W e := eq_of_min_eq_of_lt (hag e) hQe
      have he0 : W e ≠ ⊥ := fun h0 ↦ hesv (by rw [← hWe, h0]; exact isSelfVisible_bot K)
      have hWk : visibilityReplace K K (W e) = visibilityReplace K K (W d) := le_antisymm
        ((visibilityReplace_orbitCode_le_iff hd0 he0).mp (by rw [hkd, hek]))
        ((visibilityReplace_orbitCode_le_iff he0 hd0).mp (by rw [hkd, hek]))
      refine ⟨hkd, ⟨e, hWk, by rwa [hWe]⟩, ?_⟩
      rw [← hWk, hWe, hek]
    · exact absurd ⟨d, by rwa [Ne, orbitCode_eq_bot_iff], hkd⟩ hnk
  have hsup : (({d | h ≤ visibilityReplace K K (orbitCode K W d)} : Finset ι).sup
      fun d ↦ cellReading K W d x) ≤ x := by
    classical
    refine Finset.sup_le fun d hd ↦ ?_
    have hd' := (mem_filter.mp hd).2
    unfold cellReading
    split_ifs with h1 h2
    · exact bot_le
    · exact (moveToBlock_eq_self (key d hd' h1).2.2).le
    · obtain ⟨hkd, ho, -⟩ := key d hd' h1
      exact absurd ⟨hkd.symm, ho⟩ h2
  rw [orbitDecoder, min_eq_left hxh.le, max_eq_left hsup]
  exact min_eq_left hxh.le

/-! ### Capped agreement through a construction on the codes -/

/-- **Capped agreement of a construction on the orbit codes, decoded.**  For a grade `k < K`, let
`w` have values at most `ω * B + K` and `w'` agree with `w` capped at a cap `h` self-visible and
short at `K`.  Let `F` be any construction on labellings that keeps capped agreement at every cap
self-visible and short at `k`, for a first argument in the code grid.  Then the upper decoders of
`w` and `w'` applied to `F` of their orbit codes at `k` agree capped at `h`, at every point.  With
`R` the number of keys below `h` and `Γ = ω * (2 R + 1) + k` the separating grid point, the two
orbit codes agree capped at `Γ`, hence so do the two values of `F`; below the key `Γ` the two
decoders read the same cells, and from the key `Γ` on the gap values are at least `h`. -/
theorem min_upperDecoderAt_comp_eq (hk : k < K) (hh : IsSelfVisible K h) (hs : IsShort K h)
    (hw : ∀ d, w d ≤ gridPoint K B) (hag : ∀ d, min (w d) h = min (w' d) h) {ι' : Type*}
    (F : (ι → Label.{u}) → ι' → Label.{u})
    (hF : ∀ c c' : ι → Label.{u}, (∀ d, c d ∈ codeGrid k (2 * Fintype.card ι)) →
      (∀ d, c' d ∈ codeGrid k (2 * Fintype.card ι)) →
      ∀ Γ, IsSelfVisible k Γ → IsShort k Γ → (∀ d, min (c d) Γ = min (c' d) Γ) →
      ∀ z, min (F c z) Γ = min (F c' z) Γ) (z : ι') :
    min (upperDecoderAt k K B w (F (orbitCode k w) z)) h =
      min (upperDecoderAt k K B w' (F (orbitCode k w') z)) h := by
  classical
  by_cases h0 : h = ⊥
  · rw [h0, min_bot_right, min_bot_right]
  by_cases hT : h ≤ gridPoint K B
  swap
  · have : w' = w := funext fun d ↦ eq_of_min_eq_of_lt (hag d) ((hw d).trans_lt (not_le.mp hT))
    rw [this]
  have htop : h ≠ ⊤ := ne_top_of_le_ne_top (gridPoint_ne_top K B) hT
  obtain ⟨γ, hγ⟩ := exists_eq_block_of_isShort hh hs h0 htop
  have hhk : IsSelfVisible k h := by
    rw [hγ]; exact isSelfVisible_block.mpr (by omega)
  have hhB : h ∈ codeGrid K B := by
    have hle := hT
    rw [hγ, gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe,
      omega0_mul_add_natCast_le_iff] at hle
    have hγB : γ ≤ (B : Ordinal.{u}) := by
      rcases hle with hle | ⟨hle, -⟩
      exacts [hle.le, hle.le]
    obtain ⟨g, rfl⟩ : ∃ g : ℕ, γ = g :=
      Ordinal.lt_omega0.mp (hγB.trans_lt (Ordinal.natCast_lt_omega0 _))
    rw [hγ]
    exact mem_codeGrid.mpr (.inr ⟨g, by exact_mod_cast hγB, K, le_rfl, rfl⟩)
  have hag' : ∀ d, min (w' d) h = min (w d) h := fun d ↦ (hag d).symm
  have hL : keysBelow k w' h = keysBelow k w h := (keysBelow_congr hag).symm
  set Γ : Label.{u} := gridPoint k (2 * #(keysBelow k w h) + 1) with hΓ
  have hcc (d : ι) : min (orbitCode k w d) Γ = min (orbitCode k w' d) Γ := by
    rcases lt_or_ge (w d) h with hdh | hdh
    · rw [orbitCode_eq_of_min_eq hhk hag hdh]
    · have h1 := le_orbitCode (k := k) h0 hk hγ hdh
      have h2 := le_orbitCode (k := k) h0 hk hγ (le_of_min_eq_of_le (hag d) hdh)
      rw [hL] at h2
      rw [min_eq_right h1, min_eq_right h2]
  have hFz : min (F (orbitCode k w) z) Γ = min (F (orbitCode k w') z) Γ :=
    hF (orbitCode k w) (orbitCode k w') (fun d ↦ orbitMap_mem_codeGrid le_rfl _)
      (fun d ↦ orbitMap_mem_codeGrid le_rfl _) Γ
      (isSelfVisible_gridPoint k _) (isShort_gridPoint k _) hcc z
  generalize F (orbitCode k w) z = x at hFz ⊢
  generalize F (orbitCode k w') z = x' at hFz ⊢
  rcases lt_or_ge (visibilityReplace k k x) Γ with hlt | hge
  · -- Below the key `Γ`: one label, read alike.
    have hxΓ : x < Γ := (le_visibilityReplace (Nat.le_succ k) x).trans_lt hlt
    have hxx : x' = x := by
      rw [min_eq_left hxΓ.le] at hFz
      rcases lt_or_ge x' Γ with h' | h'
      · rw [min_eq_left h'.le] at hFz; exact hFz.symm
      · rw [min_eq_right h'] at hFz; exact absurd hFz hxΓ.ne
    have hlt' : visibilityReplace k k x' < gridPoint k (2 * #(keysBelow k w' h) + 1) := by
      rw [hxx, hL]; exact hlt
    rw [hxx, upperDecoderAt, upperDecoderAt, min_max_distrib_right, min_max_distrib_right]
    congr 1
    · rw [le_antisymm (orbitDecoder_le_of_lt h0 hk hγ hag hlt)
        (orbitDecoder_le_of_lt h0 hk hγ hag' (hxx ▸ hlt'))]
    · exact le_antisymm (min_gapValueAt_le hhB hh hhk hag x) (min_gapValueAt_le hhB hh hhk hag' x)
  · -- From the key `Γ` on: both decoded labels are at least `h`.
    have hge' : gridPoint k (2 * #(keysBelow k w' h) + 1) ≤ visibilityReplace k k x' := by
      rw [hL]
      rcases lt_or_ge x' Γ with h' | h'
      · have hxx : x = x' := by
          rw [min_eq_left h'.le] at hFz
          rcases lt_or_ge x Γ with h'' | h''
          · rwa [min_eq_left h''.le] at hFz
          · rw [min_eq_right h''] at hFz; exact absurd hFz.symm h'.ne
        rw [← hxx]; exact hge
      · exact h'.trans (le_visibilityReplace (Nat.le_succ k) x')
    have h1 : h ≤ upperDecoderAt k K B w x :=
      (le_gapValueAt hk hγ hhB hT hge).trans (le_max_right _ _)
    have h2 : h ≤ upperDecoderAt k K B w' x' :=
      (le_gapValueAt hk hγ hhB hT hge').trans (le_max_right _ _)
    rw [min_eq_right h1, min_eq_right h2]

/-- **Capped agreement of a construction on the two orbit codes, decoded**: as
`Label.min_upperDecoderAt_comp_eq`, with the construction asked to keep capped agreement only
between the orbit codes of `w` and `w'` at the caps self-visible and short at `k` (the proof uses
the construction there only). -/
theorem min_upperDecoderAt_comp_eq_of_codes (hk : k < K) (hh : IsSelfVisible K h)
    (hs : IsShort K h)
    (hw : ∀ d, w d ≤ gridPoint K B) (hag : ∀ d, min (w d) h = min (w' d) h) {ι' : Type*}
    (F : (ι → Label.{u}) → ι' → Label.{u})
    (hF : ∀ Γ, IsSelfVisible k Γ → IsShort k Γ →
      (∀ d, min (orbitCode k w d) Γ = min (orbitCode k w' d) Γ) →
      ∀ z, min (F (orbitCode k w) z) Γ = min (F (orbitCode k w') z) Γ) (z : ι') :
    min (upperDecoderAt k K B w (F (orbitCode k w) z)) h =
      min (upperDecoderAt k K B w' (F (orbitCode k w') z)) h := by
  classical
  by_cases h0 : h = ⊥
  · rw [h0, min_bot_right, min_bot_right]
  by_cases hT : h ≤ gridPoint K B
  swap
  · have : w' = w := funext fun d ↦ eq_of_min_eq_of_lt (hag d) ((hw d).trans_lt (not_le.mp hT))
    rw [this]
  have htop : h ≠ ⊤ := ne_top_of_le_ne_top (gridPoint_ne_top K B) hT
  obtain ⟨γ, hγ⟩ := exists_eq_block_of_isShort hh hs h0 htop
  have hhk : IsSelfVisible k h := by
    rw [hγ]; exact isSelfVisible_block.mpr (by omega)
  have hhB : h ∈ codeGrid K B := by
    have hle := hT
    rw [hγ, gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe,
      omega0_mul_add_natCast_le_iff] at hle
    have hγB : γ ≤ (B : Ordinal.{u}) := by
      rcases hle with hle | ⟨hle, -⟩
      exacts [hle.le, hle.le]
    obtain ⟨g, rfl⟩ : ∃ g : ℕ, γ = g :=
      Ordinal.lt_omega0.mp (hγB.trans_lt (Ordinal.natCast_lt_omega0 _))
    rw [hγ]
    exact mem_codeGrid.mpr (.inr ⟨g, by exact_mod_cast hγB, K, le_rfl, rfl⟩)
  have hag' : ∀ d, min (w' d) h = min (w d) h := fun d ↦ (hag d).symm
  have hL : keysBelow k w' h = keysBelow k w h := (keysBelow_congr hag).symm
  set Γ : Label.{u} := gridPoint k (2 * #(keysBelow k w h) + 1) with hΓ
  have hcc (d : ι) : min (orbitCode k w d) Γ = min (orbitCode k w' d) Γ := by
    rcases lt_or_ge (w d) h with hdh | hdh
    · rw [orbitCode_eq_of_min_eq hhk hag hdh]
    · have h1 := le_orbitCode (k := k) h0 hk hγ hdh
      have h2 := le_orbitCode (k := k) h0 hk hγ (le_of_min_eq_of_le (hag d) hdh)
      rw [hL] at h2
      rw [min_eq_right h1, min_eq_right h2]
  have hFz : min (F (orbitCode k w) z) Γ = min (F (orbitCode k w') z) Γ :=
    hF Γ (isSelfVisible_gridPoint k _) (isShort_gridPoint k _) hcc z
  generalize F (orbitCode k w) z = x at hFz ⊢
  generalize F (orbitCode k w') z = x' at hFz ⊢
  rcases lt_or_ge (visibilityReplace k k x) Γ with hlt | hge
  · -- Below the key `Γ`: one label, read alike.
    have hxΓ : x < Γ := (le_visibilityReplace (Nat.le_succ k) x).trans_lt hlt
    have hxx : x' = x := by
      rw [min_eq_left hxΓ.le] at hFz
      rcases lt_or_ge x' Γ with h' | h'
      · rw [min_eq_left h'.le] at hFz; exact hFz.symm
      · rw [min_eq_right h'] at hFz; exact absurd hFz hxΓ.ne
    have hlt' : visibilityReplace k k x' < gridPoint k (2 * #(keysBelow k w' h) + 1) := by
      rw [hxx, hL]; exact hlt
    rw [hxx, upperDecoderAt, upperDecoderAt, min_max_distrib_right, min_max_distrib_right]
    congr 1
    · rw [le_antisymm (orbitDecoder_le_of_lt h0 hk hγ hag hlt)
        (orbitDecoder_le_of_lt h0 hk hγ hag' (hxx ▸ hlt'))]
    · exact le_antisymm (min_gapValueAt_le hhB hh hhk hag x) (min_gapValueAt_le hhB hh hhk hag' x)
  · -- From the key `Γ` on: both decoded labels are at least `h`.
    have hge' : gridPoint k (2 * #(keysBelow k w' h) + 1) ≤ visibilityReplace k k x' := by
      rw [hL]
      rcases lt_or_ge x' Γ with h' | h'
      · have hxx : x = x' := by
          rw [min_eq_left h'.le] at hFz
          rcases lt_or_ge x Γ with h'' | h''
          · rwa [min_eq_left h''.le] at hFz
          · rw [min_eq_right h''] at hFz; exact absurd hFz.symm h'.ne
        rw [← hxx]; exact hge
      · exact h'.trans (le_visibilityReplace (Nat.le_succ k) x')
    have h1 : h ≤ upperDecoderAt k K B w x :=
      (le_gapValueAt hk hγ hhB hT hge).trans (le_max_right _ _)
    have h2 : h ≤ upperDecoderAt k K B w' x' :=
      (le_gapValueAt hk hγ hhB hT hge').trans (le_max_right _ _)
    rw [min_eq_right h1, min_eq_right h2]

/-! ### Values and readability at every point of the code grid of grade `k` -/

/-- A point of the code grid of grade `k` at most the least grid point lies in the block `0`. -/
private theorem eq_block_zero_of_le {B' : ℕ} (hx : x ∈ codeGrid k B') (hx0 : x ≠ ⊥)
    (hle : x ≤ gridPoint k 0) : ∃ f ≤ k, x = ((ω * ((0 : ℕ) : Ordinal.{u}) + (f : Ordinal.{u}) :
      Ordinal.{u}) : Label.{u}) := by
  rcases mem_codeGrid.mp hx with h0 | ⟨b, -, f, hf, rfl⟩
  · exact absurd h0 hx0
  rw [gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe, omega0_mul_add_natCast_le_iff] at hle
  rcases hle with hb | ⟨hb, -⟩
  · exact absurd hb (by exact_mod_cast Nat.not_lt_zero b)
  · exact ⟨f, hf, by rw [hb]⟩

/-- **The upper decoder takes values in the code grid** at every point of the code grid of grade
`k`, when `w` does, for `k ≤ K`. -/
theorem upperDecoderAt_mem_codeGrid_of_mem (hk : k ≤ K) (hw : ∀ d, w d ∈ codeGrid K B)
    {B' : ℕ} (hx : x ∈ codeGrid k B') : upperDecoderAt k K B w x ∈ codeGrid K B := by
  have hbot : (⊥ : Label.{u}) ∈ codeGrid K B := mem_insert_self _ _
  refine max_mem (max_mem ?_ ?_) ?_
  · rcases le_total x (gridPoint k 0) with hle | hle
    · rw [min_eq_left hle]
      by_cases hx0 : x = ⊥
      · rw [hx0]; exact hbot
      obtain ⟨f, hf, rfl⟩ := eq_block_zero_of_le hx hx0 hle
      exact block_mem_codeGrid (Nat.zero_le B) (hf.trans hk)
    · rw [min_eq_right hle]
      exact block_mem_codeGrid (Nat.zero_le B) hk
  · refine Finset.sup_induction (p := fun z ↦ z ∈ codeGrid K B) hbot
      (fun a ha b hb ↦ max_mem ha hb) fun d _ ↦ ?_
    unfold cellReading
    split_ifs with h1 h2
    · exact hbot
    · rcases mem_codeGrid.mp (hw d) with h0 | ⟨b, hb, f, -, he⟩
      · exact absurd h0 h2.2.isKey.ne_bot
      rcases mem_codeGrid.mp hx with rfl | ⟨b', -, f', hf', rfl⟩
      · rw [moveToBlock_bot]; exact hbot
      · rw [he, moveToBlock_omega0_mul_add]
        exact block_mem_codeGrid hb (hf'.trans hk)
    · rcases mem_codeGrid.mp (hw d) with h0 | ⟨b, hb, f, hf, he⟩
      · rw [h0, visibilityReplace_bot]; exact hbot
      · rw [he, visibilityReplace_block]
        exact block_mem_codeGrid hb (by split_ifs <;> omega)
  · by_cases hx0 : x = ⊥
    · rw [hx0, gapValueAt_bot]; exact hbot
    rw [gapValueAt_of_ne_bot hx0]
    have hT : gridPoint.{u} K B ∈ codeGrid K B := block_mem_codeGrid le_rfl le_rfl
    rcases inf_admissibleBelowAt_cases (K := K) (B := B) w (({d | visibilityReplace k k x ≤
      visibilityReplace k k (orbitCode k w d)} : Finset ι)) with htop | hmem
    · rw [htop, min_eq_left le_top]; exact hT
    · rcases le_total (gridPoint.{u} K B) _ with h | h
      · rw [min_eq_left h]; exact hT
      · rw [min_eq_right h]; exact hmem

/-- **The upper decoder keeps readability** at every point of the code grid of grade `k < K`. -/
theorem isReadableAt_upperDecoderAt_of_mem {κ : Type*} [Fintype κ] {Q : κ → Label.{u}}
    (hQ : orbitCode K Q = Q) (hk : k < K)
    (hwB : ∀ d, w d ∈ codeGrid K B) (hw : ∀ d, IsReadableAt K Q (w d)) {B' : ℕ}
    (hx : x ∈ codeGrid k B') : IsReadableAt K Q (upperDecoderAt k K B w x) := by
  -- A label of the block `0` with finite part at most `k` has the key `K` of the natural strip.
  have hnat {y : Label.{u}} (hy : visibilityReplace K K y = gridPoint K 0) :
      IsReadableAt K Q y := by
    refine .inr (.inr (by_cases (fun hkey ↦ .inl ?_) fun hkey ↦ .inr hkey))
    obtain ⟨d, hd0, hdk⟩ := hkey
    exact (isOrbitKey_congr hdk).mp (isOrbitKey_of_key_natural hQ hd0 (hdk.trans hy))
  refine IsReadableAt.max (IsReadableAt.max ?_ ?_) ?_
  · rcases le_total x (gridPoint k 0) with hle | hle
    · rw [min_eq_left hle]
      by_cases hx0 : x = ⊥
      · rw [hx0]; exact .inl rfl
      obtain ⟨f, hf, rfl⟩ := eq_block_zero_of_le hx hx0 hle
      refine hnat ?_
      rw [gridPoint, visibilityReplace_block, ite_eq_left (by omega)]
    · rw [min_eq_right hle]
      refine hnat ?_
      rw [gridPoint, gridPoint, visibilityReplace_block, ite_eq_left (by omega)]
  · refine Finset.sup_induction (p := IsReadableAt K Q) (.inl rfl) (fun a ha b hb ↦ ha.max hb)
      fun d _ ↦ ?_
    unfold cellReading
    split_ifs with h1 h2
    · exact .inl rfl
    · have h3 : ¬ IsSelfVisible K (w d) := fun h3 ↦
        not_isOrbitKey_of_isSelfVisible_of_lt hk hwB h3 h2.2
      rcases mem_codeGrid.mp hx with rfl | ⟨b', -, f', hf', rfl⟩
      · rw [moveToBlock_bot]; exact .inl rfl
      rcases mem_codeGrid.mp (hwB d) with hd0 | ⟨b, -, f, hf, he⟩
      · exact absurd hd0 h2.2.isKey.ne_bot
      have hf3 : f < K := by
        rw [he] at h3; exact not_le.mp fun h ↦ h3 (isSelfVisible_block.mpr h)
      refine isReadableAt_of_key (hw d) h3 ?_
      rw [he, moveToBlock_omega0_mul_add, visibilityReplace_block,
        visibilityReplace_block, ite_eq_left (by omega), ite_eq_left hf3]
    · by_cases h3 : IsSelfVisible K (w d)
      · rw [(h3.mono hk.le).visibilityReplace_eq k]; exact .inr (.inl h3)
      · exact isReadableAt_of_key (hw d) h3 (visibilityReplace_self_visibilityReplace_of_le le_rfl
          hk.le _)
  · by_cases hx0 : x = ⊥
    · rw [hx0, gapValueAt_bot]; exact .inl rfl
    rw [gapValueAt_of_ne_bot hx0]
    exact .inr (.inl ((isSelfVisible_gridPoint K B).min (Finset.inf_induction
      (isSelfVisible_top K) (fun a ha b hb ↦ ha.min hb)
      fun d _ ↦ isSelfVisible_admissibleBelowAt K B (w d))))

end VaughtConjecture.Label
