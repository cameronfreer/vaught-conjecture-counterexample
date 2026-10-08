/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapTransport
import VaughtConjecture.Extension.Coding
import VaughtConjecture.Extension.Restoration
import VaughtConjecture.Extension.SectionTheorem

/-!
# The canonical code, the grid, and agreement heights

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.5 (the two small arities: the catalogue of the field
layer); semantic contract, item 3.

The scalar part of the field layer (`VaughtConjecture.Extension.FieldLayer`): the canonical code of
a labelling whose values are self-visible at a grade `k`, its literal-reading decoder, the grid of
the field layer, and agreement heights.  The orbit code of
`VaughtConjecture.Extension.OrbitCode`, which also handles values that are not self-visible at
`k`, agrees with the canonical code on labellings whose values are self-visible at `k`.

**The canonical code** (`Label.canonicalCode k w`).  The **canonical point** of rank `r` at grade
`k` is the grid point `ω * (2 r - 1) + k` (`Label.canonicalPoint`, `Label.gridPoint`); the
**value rank** of a label `x` for a labelling `w` is the number of distinct values of `w` other
than bottom that are at most `x` (`Label.valueRank`).  The canonical code sends bottom to bottom
and every other value of `w` to the canonical point of its value rank, so the values of rank
`1, 2, 3, …` occupy the blocks `1, 3, 5, …`; a labelling is **canonical** when it is its own
canonical code.  On values self-visible at `k`:

* it is lawful when `w` is (`CellScheme.Rows.IsLawful.canonicalCode`: the canonical map is a
  witness bounded by grade `k` that sends only bottom to bottom), short at `k`, never the formal
  top, bottom exactly where `w` is, and keeps the order of the values;
* **N1, idempotence** (`Label.canonicalCode_canonicalCode`);
* **N2, prefix stability** (`Label.canonicalCode_eq_of_min_eq`): labellings that agree capped at a
  label `h` have the same code at the cells below `h`;
* **N3, relative room** (`Label.min_canonicalCode_eq`): if `w` agrees with a canonical `a` capped
  at `h`, so does the canonical code of `w`.  The values of `w` below `h` are those of `a`, with
  the same ranks; a value of `w` at least `h` has a larger rank than all of them, so its code is at
  least the least value of `a` at least `h`, which is canonical of that rank.  This is what a
  catalogue of all short coded labellings lacks
  (`VaughtConjecture.Extension.SmallArityExamples`, R1).

The flattened source `Label.flattenedSource (univ.image w) k w` of
`VaughtConjecture.Extension.FlattenedSource` is short, lawful and read literally, but its ranks
count the successor blocks of the block coding, which coincide with value blocks when two values
of `w` lie in consecutive spread blocks, so it is not idempotent: at grade `1` the values `ω + 2`
and `ω + 3` have the codes `ω + 1` and `ω * 2 + 1`, whose codes are `ω + 1` and `ω * 3 + 1`.  It
is not used as the canonical code.

**The literal-reading decoder** (`Label.literalDecoder k w h`): a label `x` goes to the larger of
`min x h` and the largest value of `w` at a cell whose canonical code lies between `h` and
`vr k k x`.  For a cap `h` self-visible at `k` other than bottom it is a witness bounded by grade
`k` (`Label.isWitness_literalDecoder`); it reads the canonical code of `w` literally as `w`, the
formal top included, whenever the code agrees with `w` capped at `h` (N4, the literal reading,
`Label.literalDecoder_canonicalCode`); and it keeps the cap at every label self-visible at `k`
(`Label.min_literalDecoder_eq`).  It need not be the identity below `h`: visibility
replacement at `k` sends the start `ω * c` of the block of a cap `h = ω * c + k` to `h`, so a
decoder fixing `ω * c` reads `h` as `h`, while the least code at least `h` may be `h` itself and
must be read as a value above `h` (`VaughtConjecture.Extension.SmallArityExamples`, R4).

**The grid and agreement heights.**  The **grid** at grade `k` with block bound `B`
(`Label.grid k B`) is bottom together with the grid points `ω * b + k`, `b ≤ B`.  The
**agreement height** of two labellings in a finite set `G` of labels (`Label.agreementHeight`) is
the largest member of `G` at which they agree capped.  Agreement heights satisfy the ultrametric
inequality (`Label.min_agreementHeight_le`, `Label.agreementHeight_tri`), and two labellings with
values in `G` that agree capped at `h` are equal or have agreement height at least `h`, so their
agreement heights with any third labelling agree capped at `h`
(`Label.min_agreementHeight_eq`).

## Placement

Checkpoint 2.5 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

Witnesses are [Kni26, Definition 2.3.9] and lawful sections [Kni26, Definition 2.5.4].
-/

universe u

namespace VaughtConjecture.Label

open Finset Ordinal

variable {k : ℕ} {x y h : Label.{u}}

/-! ### Grid points -/

/-- The **grid point** `ω * b + k` of the block `b` at grade `k`. -/
noncomputable def gridPoint (k b : ℕ) : Label.{u} :=
  ((ω * (b : Ordinal.{u}) + (k : Ordinal.{u}) : Ordinal.{u}) : Label.{u})

/-- Grid points of one grade compare as their blocks. -/
theorem gridPoint_le_gridPoint {a b : ℕ} : gridPoint.{u} k a ≤ gridPoint k b ↔ a ≤ b := by
  rw [gridPoint, gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe,
    omega0_mul_add_natCast_le_iff]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact_mod_cast h.le
    · exact (Nat.cast_inj.mp h).le
  · intro h
    rcases h.lt_or_eq with h | rfl
    · exact .inl (by exact_mod_cast h)
    · exact .inr ⟨rfl, le_rfl⟩

/-- Grid points of one grade compare strictly as their blocks. -/
theorem gridPoint_lt_gridPoint {a b : ℕ} : gridPoint.{u} k a < gridPoint k b ↔ a < b := by
  rw [lt_iff_not_ge, gridPoint_le_gridPoint, not_le]

/-- A grid point is not bottom. -/
theorem gridPoint_ne_bot (k b : ℕ) : gridPoint.{u} k b ≠ ⊥ := WithBot.coe_ne_bot

/-- A grid point is not the formal top. -/
theorem gridPoint_ne_top (k b : ℕ) : gridPoint.{u} k b ≠ ⊤ := fun h ↦
  WithTop.coe_ne_top (WithBot.coe_injective h)

/-- Grid points of any grades compare lexicographically in block and grade. -/
theorem gridPoint_le_gridPoint_iff_lex {k k' a b : ℕ} :
    gridPoint.{u} k a ≤ gridPoint k' b ↔ a < b ∨ a = b ∧ k ≤ k' := by
  rw [gridPoint, gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe,
    omega0_mul_add_natCast_le_iff]
  simp only [Nat.cast_lt, Nat.cast_inj]

/-- Grid points of any grades compare strictly lexicographically in block and grade. -/
theorem gridPoint_lt_gridPoint_iff_lex {k k' a b : ℕ} :
    gridPoint.{u} k a < gridPoint k' b ↔ a < b ∨ a = b ∧ k < k' := by
  rw [lt_iff_not_ge, gridPoint_le_gridPoint_iff_lex]
  omega

/-- A grid point of grade `1` is fixed by the visibility replacement at the threshold `3` with
value `1`: its finite part is `1`. -/
theorem visibilityReplace_three_one_gridPoint_one (b : ℕ) :
    visibilityReplace 3 1 (gridPoint.{u} 1 b) = gridPoint 1 b := by
  rw [gridPoint, visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast]
  simp

/-- A grid point at grade `k` is self-visible at `k`: its finite part is `k`. -/
theorem isSelfVisible_gridPoint (k b : ℕ) : IsSelfVisible k (gridPoint.{u} k b) :=
  isSelfVisible_coe.mpr (by rw [omega0_mul_add_natCast_mod])

/-- A grid point at grade `k` is short at `k`. -/
theorem isShort_gridPoint (k b : ℕ) : IsShort k (gridPoint.{u} k b) :=
  isShort_coe.mpr (by rw [omega0_mul_add_natCast_mod])

/-- Grid points lie below `ω ^ 2`. -/
theorem gridPoint_lt_omega0_sq (k b : ℕ) :
    gridPoint.{u} k b < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) :=
  lt_omega0_sq_iff.mpr (.inr ⟨b, k, rfl⟩)

/-- A label below `h` that agrees with `y` capped at `h` is `y`. -/
theorem eq_of_min_eq_of_lt (hxy : min x h = min y h) (hx : x < h) : y = x := by
  rw [min_eq_left hx.le] at hxy
  rcases le_total y h with hy | hy
  · rw [min_eq_left hy] at hxy
    exact hxy.symm
  · rw [min_eq_right hy] at hxy
    exact absurd hxy hx.ne

/-- A label at least `h` that agrees with `y` capped at `h` has `h ≤ y`. -/
theorem le_of_min_eq_of_le (hxy : min x h = min y h) (hx : h ≤ x) : h ≤ y := by
  rw [min_eq_right hx] at hxy
  exact min_eq_right_iff.mp hxy.symm

/-! ### The canonical code -/

/-- The **canonical point** of rank `r` at grade `k`: the grid point `ω * (2 * r - 1) + k`.  The
canonical points of the ranks `1, 2, 3, …` occupy the blocks `1, 3, 5, …`, so that between two of
them a whole block is free. -/
noncomputable def canonicalPoint (k r : ℕ) : Label.{u} := gridPoint k (2 * r - 1)

/-- Canonical points compare as their ranks. -/
theorem canonicalPoint_le_canonicalPoint {r r' : ℕ} :
    canonicalPoint.{u} k r ≤ canonicalPoint k r' ↔ r ≤ r' := by
  rw [canonicalPoint, canonicalPoint, gridPoint_le_gridPoint]
  omega

variable {ι : Type*} [Fintype ι] {w w' a : ι → Label.{u}}

/-- The **value rank** of a label `x` for a labelling `w`: the number of distinct values of `w`,
other than bottom, that are at most `x`. -/
noncomputable def valueRank (w : ι → Label.{u}) (x : Label.{u}) : ℕ :=
  #{y ∈ univ.image w | y ≠ ⊥ ∧ y ≤ x}

/-- The value rank is monotone in the label. -/
theorem monotone_valueRank (w : ι → Label.{u}) : Monotone (valueRank w) := fun _ _ hxy ↦
  card_le_card fun _ hy ↦ by
    rw [mem_filter] at hy ⊢
    exact ⟨hy.1, hy.2.1, hy.2.2.trans hxy⟩

/-- A value of `w` other than bottom has a larger rank than every label below it. -/
theorem valueRank_lt_valueRank {d : ι} (hd : w d ≠ ⊥) (hx : x < w d) :
    valueRank w x < valueRank w (w d) := by
  refine card_lt_card ⟨fun y hy ↦ ?_, fun hsub ↦ ?_⟩
  · rw [mem_filter] at hy ⊢
    exact ⟨hy.1, hy.2.1, hy.2.2.trans hx.le⟩
  · have hmem : w d ∈ {y ∈ univ.image w | y ≠ ⊥ ∧ y ≤ w d} :=
      mem_filter.mpr ⟨mem_image_of_mem w (mem_univ d), hd, le_rfl⟩
    exact absurd (mem_filter.mp (hsub hmem)).2.2 (not_le.mpr hx)

/-- The value rank is at most the number of cells. -/
theorem valueRank_le_card (w : ι → Label.{u}) (x : Label.{u}) :
    valueRank w x ≤ Fintype.card ι :=
  (card_filter_le _ _).trans (card_image_le.trans_eq card_univ)

/-- The **canonical map** of a labelling `w` at grade `k`: bottom is fixed, and every other label
`x` goes to the canonical point whose rank is the value rank of its replacement `vr k k x`. -/
noncomputable def canonicalMap (k : ℕ) (w : ι → Label.{u}) (x : Label.{u}) : Label.{u} :=
  if x = ⊥ then ⊥ else canonicalPoint k (valueRank w (visibilityReplace k k x))

/-- The **canonical code** of a labelling `w` at grade `k`: the canonical map applied to its
values.  For values self-visible at `k`, the value of rank `r` goes to the canonical point of rank
`r`, and bottom is kept.  A value not self-visible at `k` is ranked by its replacement `vr k k x`:
at grade `1` the labelling `(ω, ω + 1)` has `ω` of rank `1` but code of rank `2`. -/
noncomputable def canonicalCode (k : ℕ) (w : ι → Label.{u}) : ι → Label.{u} :=
  canonicalMap k w ∘ w

/-- The canonical map fixes bottom. -/
theorem canonicalMap_bot : canonicalMap k w ⊥ = ⊥ := ite_eq_left rfl

/-- The canonical map at a label other than bottom. -/
theorem canonicalMap_of_ne_bot (hx : x ≠ ⊥) :
    canonicalMap k w x = canonicalPoint k (valueRank w (visibilityReplace k k x)) := ite_eq_right hx

/-- The canonical map sends a label to bottom exactly when it is bottom. -/
@[simp] theorem canonicalMap_eq_bot_iff : canonicalMap k w x = ⊥ ↔ x = ⊥ := by
  by_cases hx : x = ⊥
  · simp [hx, canonicalMap_bot]
  · rw [canonicalMap_of_ne_bot hx]
    exact ⟨fun h ↦ absurd h (gridPoint_ne_bot _ _), fun h ↦ absurd h hx⟩

/-- The canonical code at a cell whose value is self-visible at `k` and not bottom. -/
theorem canonicalCode_of_ne_bot {d : ι} (hv : IsSelfVisible k (w d)) (hd : w d ≠ ⊥) :
    canonicalCode k w d = canonicalPoint k (valueRank w (w d)) := by
  rw [canonicalCode, Function.comp_apply, canonicalMap_of_ne_bot hd, hv]

/-- **The canonical code is bottom exactly where the labelling is.** -/
@[simp] theorem canonicalCode_eq_bot_iff {d : ι} : canonicalCode k w d = ⊥ ↔ w d = ⊥ :=
  canonicalMap_eq_bot_iff

/-- Every value of the canonical code is bottom or a canonical point. -/
theorem canonicalMap_eq_bot_or (k : ℕ) (w : ι → Label.{u}) (x : Label.{u}) :
    canonicalMap k w x = ⊥ ∨ ∃ r ≤ Fintype.card ι, canonicalMap k w x = canonicalPoint k r := by
  by_cases hx : x = ⊥
  · exact .inl (by rw [hx, canonicalMap_bot])
  · exact .inr ⟨_, valueRank_le_card w _, canonicalMap_of_ne_bot hx⟩

/-- **The canonical code is never the formal top.** -/
theorem canonicalCode_ne_top (d : ι) : canonicalCode k w d ≠ ⊤ := by
  rcases canonicalMap_eq_bot_or k w (w d) with h | ⟨r, -, h⟩ <;>
    simp only [canonicalCode, Function.comp_apply, h]
  exacts [bot_ne_top, gridPoint_ne_top _ _]

/-- **The canonical code is self-visible at `k`.** -/
theorem isSelfVisible_canonicalMap (x : Label.{u}) : IsSelfVisible k (canonicalMap k w x) := by
  rcases canonicalMap_eq_bot_or k w x with h | ⟨r, -, h⟩ <;> rw [h]
  exacts [isSelfVisible_bot k, isSelfVisible_gridPoint k _]

/-- **The canonical code is short at `k`.** -/
theorem isShort_canonicalMap (x : Label.{u}) : IsShort k (canonicalMap k w x) := by
  rcases canonicalMap_eq_bot_or k w x with h | ⟨r, -, h⟩ <;> rw [h]
  exacts [isShort_bot k, isShort_gridPoint k _]

/-- **The canonical code keeps the order of the values** self-visible at `k`. -/
theorem canonicalCode_le_canonicalCode_iff (hv : ∀ d, IsSelfVisible k (w d)) {d d' : ι} :
    canonicalCode k w d ≤ canonicalCode k w d' ↔ w d ≤ w d' := by
  by_cases hd : w d = ⊥
  · simp [hd, canonicalCode_eq_bot_iff.mpr hd]
  by_cases hd' : w d' = ⊥
  · rw [canonicalCode_eq_bot_iff.mpr hd', hd', le_bot_iff, le_bot_iff, canonicalCode_eq_bot_iff]
  rw [canonicalCode_of_ne_bot (hv d) hd, canonicalCode_of_ne_bot (hv d') hd',
    canonicalPoint_le_canonicalPoint]
  refine ⟨fun h ↦ not_lt.mp fun hlt ↦ ?_, fun h ↦ monotone_valueRank w h⟩
  exact (valueRank_lt_valueRank hd hlt).not_ge h

/-- **The canonical map is a witness bounded by grade `k`**: it is monotone, constant on the
labels with one replacement at `k`, and takes values self-visible at `k`. -/
theorem isWitness_canonicalMap (k : ℕ) (w : ι → Label.{u}) :
    IsWitness (stepSuppressor.{u} k) (canonicalMap k w) where
  antitone := (IsWitness.id_step k).antitone
  isSelfVisible := (IsWitness.id_step k).isSelfVisible
  map_bot := canonicalMap_bot
  monotone x y hxy := by
    by_cases hx : x = ⊥
    · rw [hx, canonicalMap_bot]
      exact bot_le
    have hy : y ≠ ⊥ := fun hy ↦ hx (le_bot_iff.mp (hy ▸ hxy))
    rw [canonicalMap_of_ne_bot hx, canonicalMap_of_ne_bot hy, canonicalPoint_le_canonicalPoint]
    exact monotone_valueRank w (monotone_visibilityReplace le_rfl hxy)
  visibilityReplace_comm x j hx i hi := by
    by_cases hj : j ≤ k
    · by_cases hx0 : x = ⊥
      · simp [hx0, canonicalMap_bot]
      have hx' : visibilityReplace j i x ≠ ⊥ := by simpa using hx0
      rw [canonicalMap_of_ne_bot hx', canonicalMap_of_ne_bot hx0,
        visibilityReplace_self_visibilityReplace_of_le hi hj]
      exact (((isSelfVisible_gridPoint k _).mono hj).visibilityReplace_eq i).symm
    · rw [stepSuppressor_of_lt (not_le.mp hj), le_bot_iff, canonicalMap_eq_bot_iff] at hx
      simp [hx, canonicalMap_bot]

/-- **N1, idempotence**: the canonical code of a canonical code is itself, for a labelling whose
values are self-visible at `k`. -/
theorem canonicalCode_canonicalCode (hv : ∀ d, IsSelfVisible k (w d)) :
    canonicalCode k (canonicalCode k w) = canonicalCode k w := by
  funext d
  by_cases hd : w d = ⊥
  · rw [canonicalCode_eq_bot_iff.mpr (canonicalCode_eq_bot_iff.mpr hd),
      canonicalCode_eq_bot_iff.mpr hd]
  have hd' : canonicalCode k w d ≠ ⊥ := by rwa [Ne, canonicalCode_eq_bot_iff]
  rw [canonicalCode_of_ne_bot (w := canonicalCode k w) (d := d) (isSelfVisible_canonicalMap _) hd']
  conv_rhs => rw [canonicalCode_of_ne_bot (hv d) hd]
  congr 1
  -- The values of the canonical code are the images of the values of `w`.
  have himage : (univ : Finset ι).image (canonicalCode k w) =
      ((univ : Finset ι).image w).image (canonicalMap k w) := by
    rw [image_image]
    rfl
  rw [valueRank, valueRank, himage, filter_image, card_image_of_injOn]
  · refine congrArg Finset.card (filter_congr fun z hz ↦ ?_)
    obtain ⟨e, -, rfl⟩ := mem_image.mp hz
    -- The canonical map at a value of `w` is the canonical code at its cell.
    change canonicalCode k w e ≠ ⊥ ∧ canonicalCode k w e ≤ canonicalCode k w d ↔ _
    rw [Ne, canonicalCode_eq_bot_iff, canonicalCode_le_canonicalCode_iff hv]
  · intro y hy z hz hyz
    obtain ⟨e, -, rfl⟩ := mem_image.mp (mem_filter.mp hy).1
    obtain ⟨e', -, rfl⟩ := mem_image.mp (mem_filter.mp hz).1
    -- The canonical map at values of `w` is the canonical code at their cells.
    change canonicalCode k w e = canonicalCode k w e' at hyz
    exact le_antisymm ((canonicalCode_le_canonicalCode_iff hv).mp hyz.le)
      ((canonicalCode_le_canonicalCode_iff hv).mp hyz.ge)

/-- **N2, prefix stability**: two labellings that agree capped at `h` have the same canonical code
at every cell whose value lies below `h`: the values below `h`, and so their ranks, are the same. -/
theorem canonicalCode_eq_of_min_eq (hv : ∀ d, IsSelfVisible k (w d))
    (hv' : ∀ d, IsSelfVisible k (w' d)) (hag : ∀ d, min (w d) h = min (w' d) h) {d : ι}
    (hd : w d < h) : canonicalCode k w d = canonicalCode k w' d := by
  have hwd : w' d = w d := eq_of_min_eq_of_lt (hag d) hd
  by_cases h0 : w d = ⊥
  · rw [canonicalCode_eq_bot_iff.mpr h0, canonicalCode_eq_bot_iff.mpr (hwd.trans h0)]
  rw [canonicalCode_of_ne_bot (hv d) h0, canonicalCode_of_ne_bot (hv' d) (hwd ▸ h0), hwd]
  simp only [valueRank]
  congr 2
  ext y
  simp only [mem_filter, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨⟨e, rfl⟩, hy0, hyd⟩
    exact ⟨⟨e, eq_of_min_eq_of_lt (hag e) (hyd.trans_lt hd)⟩, hy0, hyd⟩
  · rintro ⟨⟨e, rfl⟩, hy0, hyd⟩
    exact ⟨⟨e, eq_of_min_eq_of_lt (hag e).symm (hyd.trans_lt hd)⟩, hy0, hyd⟩

/-- A canonical labelling (a fixed point of the canonical code) has values self-visible at `k`. -/
theorem isSelfVisible_of_canonicalCode_eq (ha : canonicalCode k a = a) (d : ι) :
    IsSelfVisible k (a d) := by
  rw [← congrFun ha d]
  exact isSelfVisible_canonicalMap _

/-- **N3, relative room.**  Let `a` be canonical and let `w`, with values self-visible at `k`,
agree with `a` capped at `h`.  Then the canonical code of `w` agrees with `a` capped at `h`.  Below
`h` this is prefix stability; at a cell where `w` is at least `h`, the rank of its value exceeds
the number of values below `h`, so its code is at least the least value of `a` at least `h`, which
is canonical of that rank. -/
theorem min_canonicalCode_eq (hv : ∀ d, IsSelfVisible k (w d)) (ha : canonicalCode k a = a)
    (hag : ∀ d, min (w d) h = min (a d) h) (d : ι) :
    min (canonicalCode k w d) h = min (a d) h := by
  have hva := isSelfVisible_of_canonicalCode_eq ha
  rcases lt_or_ge (w d) h with hd | hd
  · rw [canonicalCode_eq_of_min_eq hv hva hag hd, ha]
  by_cases hbot : h = ⊥
  · simp [hbot]
  have had : h ≤ a d := le_of_min_eq_of_le (hag d) hd
  -- The least value of `a` at least `h`.
  obtain ⟨d₀, hd₀, hmin⟩ := exists_min_image ({e | h ≤ a e} : Finset ι) a
    ⟨d, mem_filter.mpr ⟨mem_univ d, had⟩⟩
  have hd₀' : h ≤ a d₀ := (mem_filter.mp hd₀).2
  have hne : a d₀ ≠ ⊥ := ne_bot_of_le_ne_bot hbot hd₀'
  have hwne : w d ≠ ⊥ := ne_bot_of_le_ne_bot hbot hd
  have hrank : valueRank a (a d₀) ≤ valueRank w (w d) := by
    set T : Finset Label.{u} := {y ∈ univ.image a | y ≠ ⊥ ∧ y < h}
    have h1 : {y ∈ univ.image a | y ≠ ⊥ ∧ y ≤ a d₀} ⊆ insert (a d₀) T := by
      intro y hy
      obtain ⟨hyimg, hy0, hyle⟩ := mem_filter.mp hy
      obtain ⟨e, -, rfl⟩ := mem_image.mp hyimg
      rcases lt_or_ge (a e) h with he | he
      · exact mem_insert_of_mem (mem_filter.mpr ⟨hyimg, hy0, he⟩)
      · exact mem_insert.mpr (.inl (le_antisymm hyle (hmin e (mem_filter.mpr ⟨mem_univ e, he⟩))))
    have h2 : insert (w d) T ⊆ {y ∈ univ.image w | y ≠ ⊥ ∧ y ≤ w d} := by
      intro y hy
      rcases mem_insert.mp hy with rfl | hy
      · exact mem_filter.mpr ⟨mem_image_of_mem w (mem_univ d), hwne, le_rfl⟩
      · obtain ⟨hyimg, hy0, hylt⟩ := mem_filter.mp hy
        obtain ⟨e, -, rfl⟩ := mem_image.mp hyimg
        exact mem_filter.mpr ⟨mem_image.mpr ⟨e, mem_univ e, eq_of_min_eq_of_lt (hag e).symm hylt⟩,
          hy0, (hylt.trans_le hd).le⟩
    have h3 : w d ∉ T := fun hmem ↦ (not_lt.mpr hd) (mem_filter.mp hmem).2.2
    calc valueRank a (a d₀) ≤ #(insert (a d₀) T) := card_le_card h1
      _ ≤ #T + 1 := card_insert_le _ _
      _ = #(insert (w d) T) := (card_insert_of_notMem h3).symm
      _ ≤ valueRank w (w d) := card_le_card h2
  have hle : h ≤ canonicalCode k w d :=
    calc h ≤ a d₀ := hd₀'
      _ = canonicalPoint k (valueRank a (a d₀)) := by
        rw [← canonicalCode_of_ne_bot (hva d₀) hne, ha]
      _ ≤ canonicalPoint k (valueRank w (w d)) := canonicalPoint_le_canonicalPoint.mpr hrank
      _ = canonicalCode k w d := (canonicalCode_of_ne_bot (hv d) hwne).symm
  rw [min_eq_right hle, min_eq_right had]

/-! ### The literal-reading decoder -/

omit [Fintype ι] in
/-- The supremum of labels self-visible at `k` is self-visible at `k`. -/
theorem isSelfVisible_sup (s : Finset ι) (hv : ∀ d, IsSelfVisible k (w d)) :
    IsSelfVisible k (s.sup w) :=
  Finset.sup_induction (isSelfVisible_bot k) (fun _ ha _ hb ↦ ha.max hb) fun d _ ↦ hv d

/-- The **literal-reading decoder** of a labelling `w` at grade `k` and cap `h`: a label `x` goes
to the larger of `min x h` and the largest value of `w` at a cell whose canonical code lies between
`h` and `vr k k x`.  It is the identity on the labels `x` with `vr k k x < h`, but it need not be
the identity on the labels `[ω * c, h)` of the strip of a cap `h = ω * c + k`, where
`vr k k x = h` (`VaughtConjecture.Extension.SmallArityExamples`, R4); at and above `h` it is at
least `h`; and it reads the canonical code of `w` literally when the code agrees with `w` capped
at `h`. -/
noncomputable def literalDecoder (k : ℕ) (w : ι → Label.{u}) (h x : Label.{u}) : Label.{u} :=
  max (min x h)
    (({d | h ≤ canonicalCode k w d ∧ canonicalCode k w d ≤ visibilityReplace k k x} :
      Finset ι).sup w)

/-- Below `h` (after the replacement at `k`), the literal-reading decoder caps at `h`. -/
theorem literalDecoder_of_lt (hx : visibilityReplace k k x < h) :
    literalDecoder k w h x = min x h := by
  rw [literalDecoder, (Finset.sup_eq_bot_iff _ _).mpr fun d hd ↦
    absurd ((mem_filter.mp hd).2.1.trans (mem_filter.mp hd).2.2) (not_le.mpr hx)]
  exact max_eq_left bot_le

/-- The literal-reading decoder fixes bottom, at a cap other than bottom. -/
theorem literalDecoder_bot (hbot : h ≠ ⊥) : literalDecoder k w h ⊥ = ⊥ := by
  rw [literalDecoder_of_lt (by rw [visibilityReplace_bot]; exact bot_lt_iff_ne_bot.mpr hbot)]
  exact min_eq_left bot_le

/-- **The literal-reading decoder is a witness bounded by grade `k`**, for a cap `h` self-visible
at `k` other than bottom and a labelling with values self-visible at `k`. -/
theorem isWitness_literalDecoder (hv : ∀ d, IsSelfVisible k (w d)) (hh : IsSelfVisible k h)
    (hbot : h ≠ ⊥) : IsWitness (stepSuppressor.{u} k) (literalDecoder k w h) where
  antitone := (IsWitness.id_step k).antitone
  isSelfVisible := (IsWitness.id_step k).isSelfVisible
  map_bot := literalDecoder_bot hbot
  monotone x y hxy := max_le_max (min_le_min_right _ hxy) (sup_mono fun d hd ↦ by
    simp only [mem_filter] at hd ⊢
    exact ⟨hd.1, hd.2.1, hd.2.2.trans (monotone_visibilityReplace le_rfl hxy)⟩)
  visibilityReplace_comm x j hx i hi := by
    by_cases hj : j ≤ k
    · rw [literalDecoder, literalDecoder, visibilityReplace_self_visibilityReplace_of_le hi hj,
        visibilityReplace_max hi, visibilityReplace_min_of_isSelfVisible hi (hh.mono hj),
        ((isSelfVisible_sup _ hv).mono hj).visibilityReplace_eq i]
    · rw [stepSuppressor_of_lt (not_le.mp hj), le_bot_iff] at hx
      have hx0 : x = ⊥ := by
        have := le_bot_iff.mp ((le_max_left _ _).trans hx.le)
        rwa [min_eq_bot, or_iff_left hbot] at this
      rw [hx0, visibilityReplace_bot, literalDecoder_bot hbot, visibilityReplace_bot]

/-- **N4, the literal reading**: when the canonical code of `w` agrees with `w` capped at `h`, the
literal-reading decoder reads it literally as `w`, the formal top included. -/
theorem literalDecoder_canonicalCode (hv : ∀ d, IsSelfVisible k (w d))
    (hag : ∀ d, min (canonicalCode k w d) h = min (w d) h) (d : ι) :
    literalDecoder k w h (canonicalCode k w d) = w d := by
  have hvis : visibilityReplace k k (canonicalCode k w d) = canonicalCode k w d :=
    isSelfVisible_canonicalMap _
  rcases lt_or_ge (canonicalCode k w d) h with hd | hd
  · rw [literalDecoder_of_lt (by rwa [hvis]), min_eq_left hd.le]
    exact (eq_of_min_eq_of_lt (hag d) hd).symm
  have hwd : h ≤ w d := le_of_min_eq_of_le (hag d) hd
  have hsup : ({e | h ≤ canonicalCode k w e ∧
      canonicalCode k w e ≤ visibilityReplace k k (canonicalCode k w d)} : Finset ι).sup w =
      w d := by
    rw [hvis]
    refine le_antisymm (Finset.sup_le fun e he ↦ ?_)
      (le_sup (mem_filter.mpr ⟨mem_univ d, hd, le_rfl⟩))
    exact (canonicalCode_le_canonicalCode_iff hv).mp (mem_filter.mp he).2.2
  rw [literalDecoder, hsup, min_eq_right hd, max_eq_right hwd]

/-- **The cap is kept**: at a label self-visible at `k` the literal-reading decoder agrees with the
identity capped at `h`. -/
theorem min_literalDecoder_eq (hx : IsSelfVisible k x) :
    min (literalDecoder k w h x) h = min x h := by
  rcases lt_or_ge x h with hxh | hxh
  · rw [literalDecoder_of_lt (by rwa [hx]), min_assoc, min_self]
  · rw [min_eq_right hxh]
    exact min_eq_right ((min_eq_right hxh).ge.trans (le_max_left _ _))

/-! ### The grid and agreement heights -/

/-- The **grid** at grade `k` with block bound `B`: bottom and the grid points of the blocks
`b ≤ B`.  Its largest member, `ω * B + k`, is its ceiling. -/
noncomputable def grid (k B : ℕ) : Finset Label.{u} :=
  insert ⊥ ((range (B + 1)).image (gridPoint k))

/-- Membership in the grid. -/
theorem mem_grid {B : ℕ} : x ∈ grid k B ↔ x = ⊥ ∨ ∃ b ≤ B, x = gridPoint k b := by
  simp only [grid, mem_insert, mem_image, mem_range, Nat.lt_succ_iff]
  exact or_congr Iff.rfl ⟨fun ⟨b, hb, he⟩ ↦ ⟨b, hb, he.symm⟩, fun ⟨b, hb, he⟩ ↦ ⟨b, hb, he.symm⟩⟩

/-- Bottom lies in the grid. -/
theorem bot_mem_grid (k B : ℕ) : (⊥ : Label.{u}) ∈ grid k B := mem_insert_self _ _

/-- The grid points of the blocks `b ≤ B` lie in the grid. -/
theorem gridPoint_mem_grid {b B : ℕ} (hb : b ≤ B) : gridPoint.{u} k b ∈ grid k B :=
  mem_grid.mpr (.inr ⟨b, hb, rfl⟩)

/-- The members of the grid at grade `k` are self-visible at `k`. -/
theorem isSelfVisible_of_mem_grid {B : ℕ} (hx : x ∈ grid k B) : IsSelfVisible k x := by
  rcases mem_grid.mp hx with rfl | ⟨b, -, rfl⟩
  exacts [isSelfVisible_bot k, isSelfVisible_gridPoint k b]

/-- The members of the grid at grade `k` are short at `k`. -/
theorem isShort_of_mem_grid {B : ℕ} (hx : x ∈ grid k B) : IsShort k x := by
  rcases mem_grid.mp hx with rfl | ⟨b, -, rfl⟩
  exacts [isShort_bot k, isShort_gridPoint k b]

/-- The members of the grid are not the formal top. -/
theorem ne_top_of_mem_grid {B : ℕ} (hx : x ∈ grid k B) : x ≠ ⊤ := by
  rcases mem_grid.mp hx with rfl | ⟨b, -, rfl⟩
  exacts [bot_ne_top, gridPoint_ne_top k b]

/-- The members of the grid lie below `ω ^ 2`. -/
theorem lt_omega0_sq_of_mem_grid {B : ℕ} (hx : x ∈ grid k B) :
    x < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := by
  rcases mem_grid.mp hx with rfl | ⟨b, -, rfl⟩
  exacts [lt_omega0_sq_iff.mpr (.inl rfl), gridPoint_lt_omega0_sq k b]

/-- The members of the grid with block bound `B` are at most its ceiling `ω * B + k`. -/
theorem le_gridPoint_of_mem_grid {B : ℕ} (hx : x ∈ grid k B) : x ≤ gridPoint k B := by
  rcases mem_grid.mp hx with rfl | ⟨b, hb, rfl⟩
  exacts [bot_le, gridPoint_le_gridPoint.mpr hb]

/-- The canonical code lies in every grid whose block bound is at least `2 N - 1`, for `N` cells. -/
theorem canonicalMap_mem_grid {B : ℕ} (hB : 2 * Fintype.card ι - 1 ≤ B) (x : Label.{u}) :
    canonicalMap k w x ∈ grid k B := by
  rcases canonicalMap_eq_bot_or k w x with h | ⟨r, hr, h⟩ <;> rw [h]
  · exact bot_mem_grid k B
  · exact gridPoint_mem_grid (by omega)

/-- The **agreement height** of two labellings in a finite set `G` of labels: the largest member
`x` of `G` at which they agree capped, `min (a d) x = min (b d) x` at every cell. -/
noncomputable def agreementHeight (G : Finset Label.{u}) (a b : ι → Label.{u}) : Label.{u} :=
  {x ∈ G | ∀ d, min (a d) x = min (b d) x}.sup id

variable {G : Finset Label.{u}} {b c : ι → Label.{u}}

/-- The agreement height lies in `G` and the two labellings agree capped at it. -/
theorem agreementHeight_spec (hG : ⊥ ∈ G) (a b : ι → Label.{u}) :
    agreementHeight G a b ∈ G ∧ ∀ d, min (a d) (agreementHeight G a b) =
      min (b d) (agreementHeight G a b) := by
  have hne : ({x ∈ G | ∀ d, min (a d) x = min (b d) x}).Nonempty :=
    ⟨⊥, mem_filter.mpr ⟨hG, fun d ↦ by simp⟩⟩
  obtain ⟨x, hx, hsup⟩ := exists_mem_eq_sup _ hne id
  rw [agreementHeight, hsup]
  exact mem_filter.mp hx

/-- **An agreement height other than `⊥` keeps the bottoms**: where `a` is `⊥`, so is `b`. -/
theorem eq_bot_of_agreementHeight_ne_bot {G : Finset Label.{u}} {a b : ι → Label.{u}}
    (hG : ⊥ ∈ G) (h : agreementHeight G a b ≠ ⊥) {d : ι} (hd : a d = ⊥) : b d = ⊥ := by
  have hspec := (agreementHeight_spec hG a b).2 d
  rw [hd, min_eq_left bot_le] at hspec
  rcases min_eq_bot.mp hspec.symm with h' | h'
  · exact h'
  · exact absurd h' h

/-- Every member of `G` at which two labellings agree capped is at most their agreement height. -/
theorem le_agreementHeight (hx : x ∈ G) (hag : ∀ d, min (a d) x = min (b d) x) :
    x ≤ agreementHeight G a b :=
  le_sup (f := id) (mem_filter.mpr ⟨hx, hag⟩)

/-- An upper bound of `G` bounds every agreement height in `G`. -/
theorem agreementHeight_le (hc : ∀ x ∈ G, x ≤ y) : agreementHeight G a b ≤ y :=
  Finset.sup_le fun x hx ↦ hc x (mem_filter.mp hx).1

/-- The agreement height is symmetric. -/
theorem agreementHeight_comm (a b : ι → Label.{u}) :
    agreementHeight G a b = agreementHeight G b a := by
  unfold agreementHeight
  congr 1
  exact filter_congr fun _ _ ↦ ⟨fun h d ↦ (h d).symm, fun h d ↦ (h d).symm⟩

/-- A labelling has agreement height the largest member of `G` with itself. -/
theorem agreementHeight_self (hy : y ∈ G) (hmax : ∀ x ∈ G, x ≤ y) (a : ι → Label.{u}) :
    agreementHeight G a a = y :=
  le_antisymm (agreementHeight_le hmax) (le_agreementHeight hy fun _ ↦ rfl)

/-- **The ultrametric inequality** of agreement heights. -/
theorem min_agreementHeight_le (hG : ⊥ ∈ G) (a b c : ι → Label.{u}) :
    min (agreementHeight G a b) (agreementHeight G b c) ≤ agreementHeight G a c := by
  obtain ⟨hab, hab'⟩ := agreementHeight_spec hG a b
  obtain ⟨hbc, hbc'⟩ := agreementHeight_spec hG b c
  refine le_agreementHeight ?_ fun d ↦ ?_
  · rcases min_choice (agreementHeight G a b) (agreementHeight G b c) with h | h <;> rw [h]
    exacts [hab, hbc]
  · exact (min_eq_min_of_le (hab' d) (min_le_left _ _)).trans
      (min_eq_min_of_le (hbc' d) (min_le_right _ _))

/-- The two smallest of three agreement heights are equal, in the form used for locality. -/
theorem agreementHeight_tri (hG : ⊥ ∈ G) (a b c : ι → Label.{u}) :
    min (agreementHeight G a c) (agreementHeight G a b) =
      min (agreementHeight G b c) (agreementHeight G a b) := by
  apply le_antisymm
  · refine le_min ?_ (min_le_right _ _)
    calc min (agreementHeight G a c) (agreementHeight G a b)
        = min (agreementHeight G b a) (agreementHeight G a c) := by
          rw [agreementHeight_comm b a, min_comm]
      _ ≤ agreementHeight G b c := min_agreementHeight_le hG b a c
  · refine le_min ?_ (min_le_right _ _)
    calc min (agreementHeight G b c) (agreementHeight G a b)
        = min (agreementHeight G a b) (agreementHeight G b c) := min_comm _ _
      _ ≤ agreementHeight G a c := min_agreementHeight_le hG a b c

/-- Two labellings with values in `G` that agree capped at `h` are equal, or have agreement height
at least `h`: the least value at a cell where they differ is a member of `G` at least `h` at
which they agree capped. -/
theorem eq_or_le_agreementHeight (hval : ∀ d, a d ∈ G ∧ b d ∈ G)
    (hag : ∀ d, min (a d) h = min (b d) h) : a = b ∨ h ≤ agreementHeight G a b := by
  by_cases hab : a = b
  · exact .inl hab
  right
  obtain ⟨d₁, hd₁⟩ := Function.ne_iff.mp hab
  have hs : ({d | a d ≠ b d} : Finset ι).Nonempty := ⟨d₁, mem_filter.mpr ⟨mem_univ _, hd₁⟩⟩
  -- At a cell where they differ, both values are at least `h`.
  have hge (d : ι) (hd : a d ≠ b d) : h ≤ min (a d) (b d) := by
    refine le_min (not_lt.mp fun hlt ↦ hd ?_) (not_lt.mp fun hlt ↦ hd ?_)
    · exact (eq_of_min_eq_of_lt (hag d) hlt).symm
    · exact eq_of_min_eq_of_lt (hag d).symm hlt
  obtain ⟨d₂, hd₂, hg⟩ := exists_mem_eq_inf' hs fun d ↦ min (a d) (b d)
  have hgG : ({d | a d ≠ b d} : Finset ι).inf' hs (fun d ↦ min (a d) (b d)) ∈ G := by
    rw [hg]
    rcases min_choice (a d₂) (b d₂) with h | h <;> rw [h]
    exacts [(hval d₂).1, (hval d₂).2]
  refine (le_inf' hs _ fun d hd ↦ hge d (mem_filter.mp hd).2).trans (le_agreementHeight hgG ?_)
  intro d
  by_cases hd : a d = b d
  · rw [hd]
  have hle : ({d | a d ≠ b d} : Finset ι).inf' hs (fun d ↦ min (a d) (b d)) ≤ min (a d) (b d) :=
    inf'_le _ (mem_filter.mpr ⟨mem_univ d, hd⟩)
  rw [min_eq_right ((hle.trans (min_le_left _ _))), min_eq_right (hle.trans (min_le_right _ _))]

/-- **Agreement heights keep a capped agreement**: if `a` and `b`, with values in `G`, agree capped
at `h`, then so do their agreement heights with every labelling `c`. -/
theorem min_agreementHeight_eq (hG : ⊥ ∈ G) (hval : ∀ d, a d ∈ G ∧ b d ∈ G)
    (hag : ∀ d, min (a d) h = min (b d) h) (c : ι → Label.{u}) :
    min (agreementHeight G a c) h = min (agreementHeight G b c) h := by
  rcases eq_or_le_agreementHeight hval hag with rfl | hle
  · rfl
  calc min (agreementHeight G a c) h
      = min (min (agreementHeight G a c) (agreementHeight G a b)) h := by
        rw [min_assoc, min_eq_right hle]
    _ = min (min (agreementHeight G b c) (agreementHeight G a b)) h := by
        rw [agreementHeight_tri hG]
    _ = min (agreementHeight G b c) h := by rw [min_assoc, min_eq_right hle]

/-- The literal-reading decoder sends only bottom to bottom. -/
theorem eq_bot_of_literalDecoder_eq_bot (hbot : h ≠ ⊥) (hx : literalDecoder k w h x = ⊥) :
    x = ⊥ := by
  have := le_bot_iff.mp ((le_max_left _ _).trans hx.le)
  rwa [min_eq_bot, or_iff_left hbot] at this

/-- A label other than bottom, self-visible at `k`, is at least the grid point `ω * 0 + k`. -/
theorem gridPoint_zero_le (hx : IsSelfVisible k x) (hx0 : x ≠ ⊥) : gridPoint.{u} k 0 ≤ x := by
  have h0 : gridPoint.{u} k 0 = ((k : Ordinal.{u}) : Label.{u}) := by simp [gridPoint]
  rw [h0]
  exact natCast_le_of_isSelfVisible hx hx0

/-- The canonical code agrees with the labelling capped at the least grid point `ω * 0 + k`:
both are bottom at the same cells and at least that point elsewhere.  It gives the literal
reading at the cap `⊥`. -/
theorem min_canonicalCode_gridPoint_zero (hv : ∀ d, IsSelfVisible k (w d)) (d : ι) :
    min (canonicalCode k w d) (gridPoint k 0) = min (w d) (gridPoint k 0) := by
  by_cases hd : w d = ⊥
  · rw [canonicalCode_eq_bot_iff.mpr hd, hd]
  rw [min_eq_right (gridPoint_zero_le (hv d) hd), canonicalCode_of_ne_bot (hv d) hd,
    canonicalPoint, min_eq_right (gridPoint_le_gridPoint.mpr (Nat.zero_le _))]

end VaughtConjecture.Label

namespace VaughtConjecture.CellScheme.Rows

open Label

variable {ι α : Type*} [Fintype ι] {D : CellScheme ι α} {R : D.Rows.{u}} {k : ℕ}
  {w : ι → Label.{u}}

/-- **The canonical code of a lawful section is lawful** on cells of grade at most `k`: the
canonical map is a witness bounded by grade `k` that sends only bottom to bottom. -/
theorem IsLawful.canonicalCode (hw : R.IsLawful w) (hk : ∀ d, D.grade d ≤ k) :
    R.IsLawful (Label.canonicalCode k w) :=
  hw.map_of_bot_reflecting hk (isWitness_canonicalMap k w) fun _ ↦ canonicalMap_eq_bot_iff.mp

end VaughtConjecture.CellScheme.Rows
