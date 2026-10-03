/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OwnerCappedLift

/-!
# The canonical field layer

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.5 (the two small arities: one layer of cells of full
scope over the amalgam, with the cap preserved on every auxiliary cell); semantic contract,
item 3.

Let `S` be a scheme on `n` points whose cells all have grade `k` and none of which lies above
`(univ, k)`.  The **field layer** of `S` at grade `k` appends to `S` one cell of scope `univ` and
grade `k` for each entry of a finite catalogue of labellings of the cells of `S`; the row of a new
cell reads its catalogue entry on the old cells and, on the new cells, an agreement height of two
catalogue entries.  This file builds the **canonical field layer** (`Scheme.fieldLayer`), whose
catalogue consists of canonical labellings, and proves the laws and the extension properties that
the one-grade lift (`CellScheme.Rows.cappedLift_of_boundary`) asks of the new rows.

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
`k` (`Label.isWitness_literalDecoder`); it reads the canonical code of `w` back as `w`, the formal
top included, whenever the code agrees with `w` capped at `h` (N4 (i),
`Label.literalDecoder_canonicalCode`); and it keeps the cap at every label self-visible at `k`
(N4 (ii)–(iii), `Label.min_literalDecoder_eq`).  It is not the identity below `h`: visibility
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

**Appending cells of full scope** (`Scheme.appendFullCells S k M r h`, an `abbrev`, for the reason
recorded at `Scheme.appendFullCell`): the cells of `S` along `Fin.castAdd`, then `M` cells of scope
`univ` and grade `k` along `Fin.natAdd`, the `i`-th with row `r i`.  The old cells form a lower
embedding along which the rows pull back to those of `S`; below a pair not above `(univ, k)`
lawfulness is lawfulness in `S`; a labelling is lawful when it is lawful on the old cells and its
locality and availability hold at the new cells; consistency, well-formedness and coding pass to
the appended scheme.

**The canonical field layer** (`Scheme.fieldLayer S k hS`).  The **canonical catalogue**
(`Scheme.catalogue S k`) is the set of lawful canonical labellings of the cells of `S`; they take
values in the grid with block bound `2 N + 2` for `N` cells, so it is finite.  The row of the new
cell of an entry `a` is its **field row** (`Scheme.fieldRow`): `a` on the old cells, the agreement
height of `a` and `b` at the cell of `b`, and the ceiling `ω * (2 N + 2) + k` of the grid at its
own cell.

* The field row of every entry is a lawful section of the layer (`Scheme.isLawful_fieldRow`): on
  the old cells it is the entry; at a new cell its locality is the identity capped at the agreement
  height, by the ultrametric inequality; availability holds at its own cell.  So the layer is
  consistent (`Scheme.isConsistent_fieldLayer`); it is well formed, coded, and its new rows are
  short at `k` and never the formal top.
* **Extension at the cap `⊥`** (`Scheme.exists_isLawful_fieldLayer`): every lawful section `p` of
  `S` extends to the layer, by the field row of its canonical code read by the literal-reading
  decoder at the least grid point.
* **Extension from the boundary** (`Scheme.extendsFromBoundary_bot_fieldLayer`,
  `Scheme.extendsFromBoundary_fieldLayer`): for pairs `U`, `V` below one of which lies every old
  cell, a labelling lawful below `U` and `V` that agrees with the row of a new cell (entry `a`)
  capped at a cap `h` self-visible at `k`, `⊥ < h`, on the old cells extends, unchanged there, to a
  labelling lawful below `(univ, k)` agreeing with that row capped at `h` everywhere.  The extension
  is the field row of the canonical code `b` of the labelling, read by its literal-reading decoder
  at `h`: relative room gives the agreement of `b` with `a` capped at `h`, the agreement heights
  follow, and the field row of `a` is the lawful companion of the positive-cap transport
  (`CellScheme.Rows.IsLawfulBelow.map_of_min_eq`).  This holds at every positive cap, not only at
  the source cap of the owner alignment, so the hypotheses of the one-grade lift hold as stated.

## Placement

Checkpoint 2.5 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

The completion of [Kni26, Definition 4.3.14] has the same shape (cells of full scope indexed by
patterns of the cells below, rows between them given by meet heights); its catalogue of efficient
stacks is not the canonical catalogue here.  Witnesses are [Kni26, Definition 2.3.9], lawful
sections [Kni26, Definition 2.5.4], and bountifulness [Kni26, Definition 2.5.14].
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
values.  The value of rank `r` goes to the canonical point of rank `r`, and bottom is kept. -/
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
    change canonicalCode k w e ≠ ⊥ ∧ canonicalCode k w e ≤ canonicalCode k w d ↔ _
    rw [Ne, canonicalCode_eq_bot_iff, canonicalCode_le_canonicalCode_iff hv]
  · intro y hy z hz hyz
    obtain ⟨e, -, rfl⟩ := mem_image.mp (mem_filter.mp hy).1
    obtain ⟨e', -, rfl⟩ := mem_image.mp (mem_filter.mp hz).1
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
`h` and `vr k k x`.  Below `h` it is the identity, at and above `h` it is at least `h`, and it reads
the canonical code of `w` literally when the code agrees with `w` capped at `h`. -/
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

/-- **N4 (i), literal reading**: when the canonical code of `w` agrees with `w` capped at `h`, the
literal-reading decoder reads it back as `w`, the formal top included. -/
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

/-- **N4 (ii)–(iii), the cap is kept**: at a label self-visible at `k` the literal-reading decoder
agrees with the identity capped at `h`. -/
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

/-- The members of the grid at grade `k` are self-visible and short at `k`, never the formal top,
below `ω ^ 2`, and at most the ceiling. -/
theorem properties_of_mem_grid {B : ℕ} (hx : x ∈ grid k B) :
    IsSelfVisible k x ∧ IsShort k x ∧ x ≠ ⊤ ∧ x < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) ∧
      x ≤ gridPoint k B := by
  rcases mem_grid.mp hx with rfl | ⟨b, hb, rfl⟩
  · exact ⟨isSelfVisible_bot k, isShort_bot k, bot_ne_top, lt_omega0_sq_iff.mpr (.inl rfl),
      bot_le⟩
  · exact ⟨isSelfVisible_gridPoint k b, isShort_gridPoint k b, gridPoint_ne_top k b,
      gridPoint_lt_omega0_sq k b, gridPoint_le_gridPoint.mpr hb⟩

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

omit [Fintype ι] in
/-- A labelling lawful below a pair that lies above every cell is lawful. -/
theorem isLawful_of_isLawfulBelow {X : Finset α × ℕ} (hall : ∀ d, d ∈ D.below X)
    (hw : R.IsLawfulBelow X (fun d ↦ w d)) : R.IsLawful w := by
  obtain ⟨ho, hl, ha⟩ := isLawfulBelow_iff_forall.mp hw
  exact ⟨fun d ↦ ho d (hall d), fun s ↦ hl s (hall s), fun s t hst hg ↦ ha s t (hall t) hst hg⟩

/-- **The canonical code of a lawful section is lawful** on cells of grade at most `k`: the
canonical map is a witness bounded by grade `k` that sends only bottom to bottom. -/
theorem IsLawful.canonicalCode (hw : R.IsLawful w) (hk : ∀ d, D.grade d ≤ k) :
    R.IsLawful (Label.canonicalCode k w) :=
  hw.map_of_bot_reflecting hk (isWitness_canonicalMap k w) fun _ ↦ canonicalMap_eq_bot_iff.mp

end VaughtConjecture.CellScheme.Rows

/-! ### Appending cells of full scope -/

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} (S : Scheme.{u} n) (k M : ℕ)

/-- The cell scheme of `S` with `M` more cells, last, of scope `univ` and grade `k`. -/
def appendFullCellsScheme : CellScheme (Fin (S.card + M)) (Fin n) where
  ground := S.toCellScheme.ground
  faces := S.toCellScheme.faces
  scope := Fin.append S.toCellScheme.scope fun _ ↦ univ
  grade := Fin.append S.toCellScheme.grade fun _ ↦ k

/-- An old cell keeps its scope. -/
@[simp] theorem appendFullCellsScheme_scope_castAdd (d : Fin S.card) :
    (S.appendFullCellsScheme k M).scope (Fin.castAdd M d) = S.toCellScheme.scope d :=
  Fin.append_left (u := S.toCellScheme.scope) (v := fun _ ↦ univ) d

/-- A new cell has full scope. -/
@[simp] theorem appendFullCellsScheme_scope_natAdd (i : Fin M) :
    (S.appendFullCellsScheme k M).scope (Fin.natAdd S.card i) = univ :=
  Fin.append_right (u := S.toCellScheme.scope) (v := fun _ ↦ univ) i

/-- An old cell keeps its grade. -/
@[simp] theorem appendFullCellsScheme_grade_castAdd (d : Fin S.card) :
    (S.appendFullCellsScheme k M).grade (Fin.castAdd M d) = S.toCellScheme.grade d :=
  Fin.append_left (u := S.toCellScheme.grade) (v := fun _ ↦ k) d

/-- A new cell has grade `k`. -/
@[simp] theorem appendFullCellsScheme_grade_natAdd (i : Fin M) :
    (S.appendFullCellsScheme k M).grade (Fin.natAdd S.card i) = k :=
  Fin.append_right (u := S.toCellScheme.grade) (v := fun _ ↦ k) i

/-- An old cell keeps its graded index. -/
@[simp] theorem appendFullCellsScheme_gradedIndex_castAdd (d : Fin S.card) :
    (S.appendFullCellsScheme k M).gradedIndex (Fin.castAdd M d) = S.toCellScheme.gradedIndex d := by
  simp [CellScheme.gradedIndex]

/-- A new cell has graded index `(univ, k)`. -/
@[simp] theorem appendFullCellsScheme_gradedIndex_natAdd (i : Fin M) :
    (S.appendFullCellsScheme k M).gradedIndex (Fin.natAdd S.card i) = (univ, k) := by
  simp [CellScheme.gradedIndex]

variable {S k M}

/-- The graded index of a cell of index below the number of old cells, read in `S`. -/
theorem appendFullCellsScheme_gradedIndex_of_lt {s : Fin (S.card + M)} (hs : (s : ℕ) < S.card) :
    (S.appendFullCellsScheme k M).gradedIndex s = S.toCellScheme.gradedIndex ⟨s, hs⟩ :=
  appendFullCellsScheme_gradedIndex_castAdd S k M ⟨s, hs⟩

/-- Below a pair that is not above `(univ, k)`, every cell is old. -/
theorem lt_card_of_mem_below {X : Finset (Fin n) × ℕ} (hX : ¬ ((univ : Finset (Fin n)), k) ≤ X)
    {d : Fin (S.card + M)} (hd : d ∈ (S.appendFullCellsScheme k M).below X) :
    (d : ℕ) < S.card := by
  by_contra hlt
  have hd' : d = Fin.natAdd S.card ⟨d - S.card, by omega⟩ := Fin.ext (by simp; omega)
  rw [hd', CellScheme.mem_below, appendFullCellsScheme_gradedIndex_natAdd] at hd
  exact hX hd

/-- An old cell lies below no new cell, when no cell of `S` lies above `(univ, k)`. -/
theorem not_le_gradedIndex_of_lt
    (h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d)
    {s : Fin (S.card + M)} (hs : (s : ℕ) < S.card) :
    ¬ ((univ : Finset (Fin n)), k) ≤ (S.appendFullCellsScheme k M).gradedIndex s := by
  rw [appendFullCellsScheme_gradedIndex_of_lt hs]
  exact h _

/-- The cells below an old cell are old, and lie below it in `S`. -/
theorem mem_below_of_lt
    (h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d)
    {s : Fin (S.card + M)} (hs : (s : ℕ) < S.card)
    (t : (S.appendFullCellsScheme k M).below ((S.appendFullCellsScheme k M).gradedIndex s)) :
    (⟨t.1, lt_card_of_mem_below (not_le_gradedIndex_of_lt h hs) t.2⟩ : Fin S.card) ∈
      S.toCellScheme.below (S.toCellScheme.gradedIndex ⟨s, hs⟩) := by
  rw [CellScheme.mem_below, ← appendFullCellsScheme_gradedIndex_of_lt (M := M) (k := k),
    ← appendFullCellsScheme_gradedIndex_of_lt hs]
  exact t.2

variable (S k M) in
/-- **Appending cells of full scope**: the scheme with the cells of `S`, in their order, followed
by `M` cells of scope `univ` and grade `k`, the `i`-th with row `r i` (a labelling of all cells,
read on those below `(univ, k)`).  The hypothesis says that no cell of `S` lies above `(univ, k)`,
so that the old rows, which are those of `S`, see only old cells.

It is an `abbrev`, not a `def`, for the reason recorded at `Scheme.appendFullCell`: its number of
cells must unfold reducibly to `S.card + M`, so that `Fin.castAdd` and `Fin.natAdd` apply to its
cells in rewriting and in `simp`. -/
abbrev appendFullCells (r : Fin M → Fin (S.card + M) → Label.{u})
    (h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d) : Scheme.{u} n where
  card := S.card + M
  toCellScheme := S.appendFullCellsScheme k M
  rows := ⟨fun s t ↦ if hs : (s : ℕ) < S.card then
      S.rows.row ⟨s, hs⟩ ⟨⟨t.1, lt_card_of_mem_below (not_le_gradedIndex_of_lt h hs) t.2⟩,
        mem_below_of_lt h hs t⟩
    else r ⟨s - S.card, by omega⟩ t.1⟩

variable {r : Fin M → Fin (S.card + M) → Label.{u}}
  {h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- The row of the new cell `i` is `r i`. -/
theorem appendFullCells_row_natAdd (i : Fin M)
    (t : (S.appendFullCellsScheme k M).below
      ((S.appendFullCellsScheme k M).gradedIndex (Fin.natAdd S.card i))) :
    (S.appendFullCells k M r h).rows.row (Fin.natAdd S.card i) t = r i t.1 := by
  refine (dite_eq_right (by simp)).trans (congrArg (r · t.1) (Fin.ext ?_))
  simp

/-- The row of the new cell `i` is `r i`, as a function. -/
theorem appendFullCells_row_natAdd_eq (i : Fin M) :
    (S.appendFullCells k M r h).rows.row (Fin.natAdd S.card i) = fun t ↦ r i t.1 :=
  funext (appendFullCells_row_natAdd i)

variable (k M r h) in
/-- **The old cells form a lower embedding** along `Fin.castAdd`. -/
theorem isLowerEmbedding_castAdd :
    S.toCellScheme.IsLowerEmbedding (S.appendFullCells k M r h).toCellScheme (Fin.castAdd M) where
  injective := Fin.castAdd_injective _ _
  grade_eq d := appendFullCellsScheme_grade_castAdd S k M d
  le_iff s t := by simp only [appendFullCellsScheme_gradedIndex_castAdd]
  mem_range t d hd := ⟨⟨d, lt_card_of_mem_below
    (by rw [appendFullCellsScheme_gradedIndex_castAdd]; exact h t) hd⟩, rfl⟩

/-- **The rows pull back to those of `S`** along the old cells. -/
theorem comap_rows_castAdd :
    (S.appendFullCells k M r h).rows.comap (isLowerEmbedding_castAdd k M r h) = S.rows := by
  ext s t
  rw [CellScheme.Rows.comap_row]
  exact (dite_eq_left s.2).trans (S.rows.row_congr rfl rfl)

/-- The old cells below a pair that is not above `(univ, k)` are all its cells. -/
theorem image_castAdd_below {X : Finset (Fin n) × ℕ} (hX : ¬ ((univ : Finset (Fin n)), k) ≤ X) :
    Fin.castAdd M '' S.toCellScheme.below X = (S.appendFullCells k M r h).toCellScheme.below X := by
  ext d
  constructor
  · rintro ⟨d, hd, rfl⟩
    rwa [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_castAdd]
  · intro hd
    refine ⟨⟨d, lt_card_of_mem_below hX hd⟩, ?_, rfl⟩
    rw [CellScheme.mem_below, ← appendFullCellsScheme_gradedIndex_of_lt]
    exact hd

/-- **Lawfulness below a pair that is not above `(univ, k)`** is lawfulness in `S`. -/
theorem isLawfulBelow_appendFullCells_iff {X : Finset (Fin n) × ℕ}
    (hX : ¬ ((univ : Finset (Fin n)), k) ≤ X) {v : Fin (S.card + M) → Label.{u}} :
    (S.appendFullCells k M r h).rows.IsLawfulBelow X (fun d ↦ v d) ↔
      S.rows.IsLawfulBelow X (fun d ↦ v (Fin.castAdd M d)) := by
  have := CellScheme.Rows.isLawfulBelow_comap_iff (R := (S.appendFullCells k M r h).rows)
    (isLowerEmbedding_castAdd k M r h) (image_castAdd_below hX) (r := fun d ↦ v d)
  rw [comap_rows_castAdd] at this
  exact this.symm

/-- **Lawful labellings after appending cells.**  A labelling `v` is lawful when it is lawful on
the old cells, its values at the new cells are self-visible at `k`, the row of every new cell
transforms to `v` capped at its value, and every cell of grade `k` has a value at most that of
some new cell. -/
theorem isLawful_appendFullCells {v : Fin (S.card + M) → Label.{u}}
    (hv : S.rows.IsLawful (v ∘ Fin.castAdd M))
    (hvis : ∀ i, IsSelfVisible k (v (Fin.natAdd S.card i)))
    (hloc : ∀ i, TransformsTo (fun t : (S.appendFullCellsScheme k M).below
        ((S.appendFullCellsScheme k M).gradedIndex (Fin.natAdd S.card i)) ↦
          (S.appendFullCellsScheme k M).grade t) (fun t ↦ r i t.1)
        fun t ↦ min (v t) (v (Fin.natAdd S.card i)))
    (havail : ∀ s, (S.appendFullCellsScheme k M).grade s = k →
      ∃ i, v s ≤ v (Fin.natAdd S.card i)) :
    (S.appendFullCells k M r h).rows.IsLawful v where
  orderly d := by
    induction d using Fin.addCases with
    | left d => rw [appendFullCellsScheme_grade_castAdd]; exact hv.orderly d
    | right i => rw [appendFullCellsScheme_grade_natAdd]; exact hvis i
  locality s := by
    induction s using Fin.addCases with
    | right i =>
      rw [appendFullCells_row_natAdd_eq]
      exact hloc i
    | left s =>
      have hX : ¬ ((univ : Finset (Fin n)), k) ≤
          (S.appendFullCellsScheme k M).gradedIndex (Fin.castAdd M s) := by
        rw [appendFullCellsScheme_gradedIndex_castAdd]
        exact h s
      have hb := (isLawfulBelow_appendFullCells_iff (r := r) (h := h) hX).mpr (hv.isLawfulBelow _)
      exact (CellScheme.Rows.isLawfulBelow_iff_forall.mp hb).2.1 _
        (CellScheme.mem_below_gradedIndex _ _)
  availability s t hst hg := by
    induction t using Fin.addCases with
    | right i =>
      obtain ⟨j, hj⟩ := havail s (hg.trans (appendFullCellsScheme_grade_natAdd S k M i))
      exact ⟨Fin.natAdd S.card j, by simp, hj⟩
    | left t =>
      induction s using Fin.addCases with
      | right i =>
        refine absurd ?_ (h t)
        simp only [appendFullCellsScheme_scope_natAdd, appendFullCellsScheme_scope_castAdd,
          appendFullCellsScheme_grade_natAdd, appendFullCellsScheme_grade_castAdd] at hst hg
        exact ⟨hst, hg.le⟩
      | left s =>
        simp only [appendFullCellsScheme_scope_castAdd,
          appendFullCellsScheme_grade_castAdd] at hst hg
        obtain ⟨u, hu, hle⟩ := hv.availability s t hst hg
        exact ⟨Fin.castAdd M u, by simpa using hu, hle⟩

/-- **Consistency after appending cells**: the old rows are those of `S`, and the new rows are
lawful. -/
theorem isConsistent_appendFullCells (hS : S.rows.IsConsistent)
    (hr : ∀ i, (S.appendFullCells k M r h).rows.IsLawful (r i)) :
    (S.appendFullCells k M r h).rows.IsConsistent := by
  intro s
  induction s using Fin.addCases with
  | right i =>
    rw [appendFullCells_row_natAdd_eq]
    exact (hr i).isLawfulBelow _
  | left s =>
    have hφ := isLowerEmbedding_castAdd k M r h
    refine (CellScheme.Rows.isLawfulBelow_comap_iff hφ (hφ.image_below_gradedIndex s)).mp ?_
    rw [comap_rows_castAdd]
    convert hS s using 1
    funext t
    exact congrArg (fun R : S.toCellScheme.Rows ↦ R.row s t) comap_rows_castAdd

/-- **Appending cells keeps well-formedness** when `(univ, k)` is a graded face. -/
theorem isWellFormed_appendFullCells (hS : S.IsWellFormed) (hk : 0 < k) (hkn : k ≤ n) :
    (S.appendFullCells k M r h).IsWellFormed where
  ground_eq := hS.ground_eq
  isWellFormed := by
    refine ⟨inferInstance, hS.isWellFormed.isPlan, fun d ↦ ?_⟩
    induction d using Fin.addCases with
    | right i =>
      rw [appendFullCellsScheme_gradedIndex_natAdd]
      exact ⟨hS.univ_mem_faces, hk, by simpa using hkn⟩
    | left d =>
      rw [appendFullCellsScheme_gradedIndex_castAdd]
      exact hS.isWellFormed.gradedIndex_mem d

/-- **Appending cells keeps coding** when the new rows are coded. -/
theorem isCoded_appendFullCells (hS : S.IsCoded)
    (hr : ∀ i d, r i d < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})) :
    (S.appendFullCells k M r h).IsCoded := by
  intro s t
  induction s using Fin.addCases with
  | right i => exact (appendFullCells_row_natAdd i t).trans_lt (hr i _)
  | left s => exact (dite_eq_left s.2).trans_lt (hS _ _)

end VaughtConjecture.Scheme

/-! ### The canonical field layer -/

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} (S : Scheme.{u} n) (k : ℕ)

/-- The grid of the field layer at grade `k`: block bound `2 N + 2` for `N` old cells. -/
noncomputable abbrev fieldGrid : Finset Label.{u} := grid k (2 * S.card + 2)

open Classical in
/-- The **canonical catalogue** at grade `k`: the lawful labellings of the cells of `S` that are
canonical, fixed by the canonical code.  They take values in the grid. -/
noncomputable def catalogue : Finset (Fin S.card → Label.{u}) :=
  {a ∈ Fintype.piFinset fun _ ↦ S.fieldGrid k | S.rows.IsLawful a ∧ canonicalCode k a = a}

variable {S k}

/-- Membership in the canonical catalogue: lawful and canonical. -/
theorem mem_catalogue {a : Fin S.card → Label.{u}} :
    a ∈ S.catalogue k ↔ S.rows.IsLawful a ∧ canonicalCode k a = a := by
  simp only [catalogue, Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨fun d ↦ ?_, h⟩⟩
  rw [← congrFun h.2 d]
  exact canonicalMap_mem_grid (by simp; omega) _

/-- A catalogue entry takes its values in the grid of the field layer. -/
theorem mem_fieldGrid_of_mem_catalogue {a : Fin S.card → Label.{u}} (ha : a ∈ S.catalogue k)
    (d : Fin S.card) : a d ∈ S.fieldGrid k := by
  simp only [catalogue, Finset.mem_filter, Fintype.mem_piFinset] at ha
  exact ha.1 d

variable (S k) in
/-- The catalogue entry of the new cell `i`. -/
noncomputable def catalogueEntry (i : Fin (S.catalogue k).card) : Fin S.card → Label.{u} :=
  ((S.catalogue k).equivFin.symm i).1

/-- A catalogue entry lies in the catalogue. -/
theorem catalogueEntry_mem (i : Fin (S.catalogue k).card) :
    S.catalogueEntry k i ∈ S.catalogue k :=
  ((S.catalogue k).equivFin.symm i).2

/-- Every member of the catalogue is the entry of some new cell. -/
theorem exists_catalogueEntry_eq {a : Fin S.card → Label.{u}} (ha : a ∈ S.catalogue k) :
    ∃ i, S.catalogueEntry k i = a :=
  ⟨(S.catalogue k).equivFin ⟨a, ha⟩, by simp [catalogueEntry]⟩

variable (S k) in
/-- The **field row** of a labelling `a` of the old cells: `a` on the old cells, and on the new
cell `j` the agreement height of `a` with its catalogue entry. -/
noncomputable def fieldRow (a : Fin S.card → Label.{u}) :
    Fin (S.card + (S.catalogue k).card) → Label.{u} :=
  Fin.append a fun j ↦ agreementHeight (S.fieldGrid k) a (S.catalogueEntry k j)

/-- The field row reads the labelling on the old cells. -/
@[simp] theorem fieldRow_castAdd (a : Fin S.card → Label.{u}) (d : Fin S.card) :
    S.fieldRow k a (Fin.castAdd _ d) = a d :=
  Fin.append_left _ _ d

/-- The field row reads an agreement height on the new cells. -/
@[simp] theorem fieldRow_natAdd (a : Fin S.card → Label.{u}) (j : Fin (S.catalogue k).card) :
    S.fieldRow k a (Fin.natAdd _ j) =
      agreementHeight (S.fieldGrid k) a (S.catalogueEntry k j) :=
  Fin.append_right _ _ j

/-- The field row of a catalogue entry takes its values in the grid. -/
theorem fieldRow_mem_fieldGrid {a : Fin S.card → Label.{u}} (ha : a ∈ S.catalogue k)
    (x : Fin (S.card + (S.catalogue k).card)) : S.fieldRow k a x ∈ S.fieldGrid k := by
  induction x using Fin.addCases with
  | left d => rw [fieldRow_castAdd]; exact mem_fieldGrid_of_mem_catalogue ha d
  | right j => rw [fieldRow_natAdd]; exact (agreementHeight_spec (bot_mem_grid _ _) _ _).1

/-- Two field rows agree capped at the agreement height of their labellings. -/
theorem min_fieldRow_agreementHeight (a b : Fin S.card → Label.{u})
    (x : Fin (S.card + (S.catalogue k).card)) :
    min (S.fieldRow k a x) (agreementHeight (S.fieldGrid k) a b) =
      min (S.fieldRow k b x) (agreementHeight (S.fieldGrid k) a b) := by
  induction x using Fin.addCases with
  | left d =>
    rw [fieldRow_castAdd, fieldRow_castAdd]
    exact (agreementHeight_spec (bot_mem_grid _ _) a b).2 d
  | right j =>
    rw [fieldRow_natAdd, fieldRow_natAdd]
    exact agreementHeight_tri (bot_mem_grid _ _) a b _

variable (S k) in
/-- **The canonical field layer** at grade `k`: the cells of `S`, followed by one cell of scope
`univ` and grade `k` for each entry of the canonical catalogue, whose row is the field row of the
entry. -/
noncomputable abbrev fieldLayer
    (hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d) : Scheme.{u} n :=
  S.appendFullCells k (S.catalogue k).card (fun i ↦ S.fieldRow k (S.catalogueEntry k i)) hS

variable {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- The row of a new cell is the field row of its catalogue entry. -/
theorem fieldLayer_row_natAdd (i : Fin (S.catalogue k).card) (t) :
    (S.fieldLayer k hS).rows.row (Fin.natAdd S.card i) t =
      S.fieldRow k (S.catalogueEntry k i) t.1 :=
  appendFullCells_row_natAdd i t

variable (S k hS) in
/-- **The old cells form a lower embedding** of `S` into the field layer, along `Fin.castAdd`. -/
theorem isLowerEmbedding_fieldLayer :
    S.toCellScheme.IsLowerEmbedding (S.fieldLayer k hS).toCellScheme (Fin.castAdd _) :=
  isLowerEmbedding_castAdd _ _ _ _

/-- **The rows of the field layer pull back to those of `S`** along the old cells. -/
theorem comap_rows_fieldLayer :
    (S.fieldLayer k hS).rows.comap (isLowerEmbedding_fieldLayer S k hS) = S.rows :=
  comap_rows_castAdd

/-- Every cell of the field layer has grade `k`. -/
theorem fieldLayer_grade (hk : ∀ d, S.toCellScheme.grade d = k)
    (d : Fin (S.fieldLayer k hS).card) :
    (S.fieldLayer k hS).toCellScheme.grade d = k := by
  induction d using Fin.addCases with
  | left d => exact (appendFullCellsScheme_grade_castAdd S k _ d).trans (hk d)
  | right i => exact appendFullCellsScheme_grade_natAdd S k _ i

/-- **The field row of a catalogue entry is a lawful section of the field layer.**  On the old
cells it is the entry, lawful in `S`; at a new cell its locality is the identity capped at the
agreement height, by the ultrametric inequality; availability at the full face holds at the cell
of the entry itself, whose diagonal entry is the ceiling of the grid. -/
theorem isLawful_fieldRow {a : Fin S.card → Label.{u}} (ha : a ∈ S.catalogue k) :
    (S.fieldLayer k hS).rows.IsLawful (S.fieldRow k a) := by
  refine isLawful_appendFullCells ?_ (fun i ↦ ?_) (fun i ↦ ?_) fun s _ ↦ ?_
  · convert (mem_catalogue.mp ha).1 using 1
    exact funext fun d ↦ fieldRow_castAdd a d
  · rw [fieldRow_natAdd]
    exact (properties_of_mem_grid (agreementHeight_spec (bot_mem_grid _ _) _ _).1).1
  · have hc := (properties_of_mem_grid (agreementHeight_spec (bot_mem_grid k (2 * S.card + 2))
      a (S.catalogueEntry k i)).1).1
    convert (TransformsTo.refl (fun t : (S.appendFullCellsScheme k (S.catalogue k).card).below
      ((S.appendFullCellsScheme k (S.catalogue k).card).gradedIndex (Fin.natAdd S.card i)) ↦
        (S.appendFullCellsScheme k (S.catalogue k).card).grade t)
          fun t ↦ S.fieldRow k (S.catalogueEntry k i) t.1)
      |>.min_const (K := k) (fun t ↦ t.2.2.trans (appendFullCellsScheme_grade_natAdd S k _ i).le)
        hc using 1
    funext t
    rw [fieldRow_natAdd]
    exact min_fieldRow_agreementHeight a _ t.1
  · obtain ⟨i, hi⟩ := exists_catalogueEntry_eq ha
    refine ⟨i, ?_⟩
    rw [fieldRow_natAdd, hi, agreementHeight_self (gridPoint_mem_grid le_rfl)
      fun x hx ↦ (properties_of_mem_grid hx).2.2.2.2]
    exact (properties_of_mem_grid (fieldRow_mem_fieldGrid ha s)).2.2.2.2

/-- **The field layer is consistent**: the old rows are those of `S`, and the new rows are field
rows of catalogue entries. -/
theorem isConsistent_fieldLayer (hcons : S.rows.IsConsistent) :
    (S.fieldLayer k hS).rows.IsConsistent :=
  isConsistent_appendFullCells hcons fun i ↦ isLawful_fieldRow (catalogueEntry_mem i)

/-- **The field layer is well formed.** -/
theorem isWellFormed_fieldLayer (hwf : S.IsWellFormed) (hk0 : 0 < k) (hkn : k ≤ n) :
    (S.fieldLayer k hS).IsWellFormed :=
  isWellFormed_appendFullCells hwf hk0 hkn

/-- **The field layer is coded**: the new rows take values in the grid, below `ω ^ 2`. -/
theorem isCoded_fieldLayer (hc : S.IsCoded) : (S.fieldLayer k hS).IsCoded :=
  isCoded_appendFullCells hc fun i x ↦
    (properties_of_mem_grid (fieldRow_mem_fieldGrid (catalogueEntry_mem i) x)).2.2.2.1

/-- **The new rows are short at `k` and never the formal top**: their values lie in the grid. -/
theorem isShort_row_fieldLayer (i : Fin (S.catalogue k).card) (t) :
    IsShort k ((S.fieldLayer k hS).rows.row (Fin.natAdd S.card i) t) ∧
      (S.fieldLayer k hS).rows.row (Fin.natAdd S.card i) t ≠ ⊤ := by
  rw [fieldLayer_row_natAdd]
  obtain ⟨-, hs, ht, -⟩ :=
    properties_of_mem_grid (fieldRow_mem_fieldGrid (catalogueEntry_mem i) t.1)
  exact ⟨hs, ht⟩

/-- The canonical code of a lawful section of `S` lies in the catalogue. -/
theorem canonicalCode_mem_catalogue (hk : ∀ d, S.toCellScheme.grade d = k)
    {p : Fin S.card → Label.{u}} (hp : S.rows.IsLawful p) :
    canonicalCode k p ∈ S.catalogue k :=
  mem_catalogue.mpr ⟨hp.canonicalCode fun d ↦ (hk d).le,
    canonicalCode_canonicalCode fun d ↦ hk d ▸ hp.orderly d⟩

/-- **Extension at the cap `⊥`**: every lawful section `p` of `S` extends to a lawful section of
the field layer.  It is the field row of the canonical code of `p`, read by the literal-reading
decoder at the least grid point, which reads the old cells literally and sends no other label to
bottom. -/
theorem exists_isLawful_fieldLayer (hk : ∀ d, S.toCellScheme.grade d = k)
    {p : Fin S.card → Label.{u}} (hp : S.rows.IsLawful p) :
    ∃ r, (S.fieldLayer k hS).rows.IsLawful r ∧ ∀ d, r (Fin.castAdd _ d) = p d := by
  have hv (d : Fin S.card) : IsSelfVisible k (p d) := hk d ▸ hp.orderly d
  have hb := canonicalCode_mem_catalogue hk hp
  refine ⟨literalDecoder k p (gridPoint k 0) ∘ S.fieldRow k (canonicalCode k p),
    (isLawful_fieldRow hb).map_of_apply_eq_bot (fun d ↦ (fieldLayer_grade hk d).le)
      (isWitness_literalDecoder hv (isSelfVisible_gridPoint k 0) (gridPoint_ne_bot k 0))
      fun _ ↦ eq_bot_of_literalDecoder_eq_bot (gridPoint_ne_bot k 0), fun d ↦ ?_⟩
  rw [Function.comp_apply, fieldRow_castAdd]
  exact literalDecoder_canonicalCode hv (min_canonicalCode_gridPoint_zero hv) d

/-! ### Extension from the boundary -/

variable {U V : Finset (Fin n) × ℕ}

/-- A cell of the field layer below a pair that is not above `(univ, k)` is old. -/
theorem exists_castAdd_eq {X : Finset (Fin n) × ℕ} (hX : ¬ ((univ : Finset (Fin n)), k) ≤ X)
    {d : Fin (S.fieldLayer k hS).card} (hd : d ∈ (S.fieldLayer k hS).toCellScheme.below X) :
    ∃ e, Fin.castAdd _ e = d :=
  ⟨⟨d, lt_card_of_mem_below hX hd⟩, rfl⟩

/-- A cell of the field layer of graded index `(univ, k)` is new. -/
theorem exists_natAdd_eq {u : Fin (S.fieldLayer k hS).card}
    (hu : (S.fieldLayer k hS).toCellScheme.gradedIndex u = (univ, k)) :
    ∃ i, Fin.natAdd S.card i = u := by
  by_cases hlt : (u : ℕ) < S.card
  · refine absurd ?_ (hS ⟨u, hlt⟩)
    rw [← appendFullCellsScheme_gradedIndex_of_lt hlt]
    exact hu.ge
  · have hu' : (u : ℕ) < S.card + (S.catalogue k).card := u.2
    exact ⟨⟨u - S.card, by omega⟩, Fin.ext (by simp; omega)⟩

/-- **The boundary labelling is lawful in `S`**: a labelling of the field layer lawful below two
pairs `U` and `V`, neither above `(univ, k)`, below one of which lies every old cell, is lawful
on the old cells. -/
theorem isLawful_castAdd_of_boundary (hk : ∀ d, S.toCellScheme.grade d = k)
    (hU : ¬ ((univ : Finset (Fin n)), k) ≤ U) (hV : ¬ ((univ : Finset (Fin n)), k) ≤ V)
    (hcover : ∀ d, S.toCellScheme.gradedIndex d ≤ U ∨ S.toCellScheme.gradedIndex d ≤ V)
    {w : Fin (S.fieldLayer k hS).card → Label.{u}}
    (hwU : (S.fieldLayer k hS).rows.IsLawfulBelow U (fun d ↦ w d))
    (hwV : (S.fieldLayer k hS).rows.IsLawfulBelow V (fun d ↦ w d)) :
    S.rows.IsLawful fun d ↦ w (Fin.castAdd _ d) :=
  CellScheme.Rows.isLawful_of_isLawfulBelow (X := (univ, k))
    (fun d ↦ ⟨subset_univ _, (hk d).le⟩)
    (CellScheme.Rows.IsLawfulBelow.glue (w := fun e ↦ w (Fin.castAdd _ e))
      ((isLawfulBelow_appendFullCells_iff hU).mp hwU)
      ((isLawfulBelow_appendFullCells_iff hV).mp hwV) fun d _ ↦ hcover d)

/-- **Extension from the boundary at the cap `⊥`**: every labelling lawful below `U` and `V` (the
boundary, here every old cell) extends, unchanged there, to a labelling lawful below `(univ, k)`. -/
theorem extendsFromBoundary_bot_fieldLayer (hk : ∀ d, S.toCellScheme.grade d = k)
    (hU : ¬ ((univ : Finset (Fin n)), k) ≤ U) (hV : ¬ ((univ : Finset (Fin n)), k) ≤ V)
    (hcover : ∀ d, S.toCellScheme.gradedIndex d ≤ U ∨ S.toCellScheme.gradedIndex d ≤ V) :
    (S.fieldLayer k hS).rows.ExtendsFromBoundary U V (univ, k) ⊥ fun _ ↦ ⊥ := by
  intro w hwU hwV _
  obtain ⟨r, hr, hre⟩ := exists_isLawful_fieldLayer (hS := hS) hk
    (isLawful_castAdd_of_boundary hk hU hV hcover hwU hwV)
  refine ⟨fun d ↦ r d, hr.isLawfulBelow _, fun d hd ↦ ?_, fun _ ↦ by simp⟩
  obtain ⟨e, he⟩ := hd.elim (exists_castAdd_eq hU) (exists_castAdd_eq hV)
  change r d.1 = w d.1
  rw [← he]
  exact hre e

/-- **Extension from the boundary at a positive cap, along a new row.**  Let `u` be a new cell, of
graded index `(univ, k)`, with catalogue entry `a`, and `h` a cap self-visible at `k` other than
bottom.  Every labelling `w` lawful below `U` and `V` (every old cell) that agrees with the row of
`u` capped at `h` on the old cells extends, unchanged there, to a labelling lawful below
`(univ, k)` that agrees with the row of `u` capped at `h` at every cell.  The extension is the
field row of the canonical code `b` of `w`, read by the literal-reading decoder of `w` at `h`:
relative room makes `b` agree with `a` capped at `h`, the agreement heights of `b` then agree with
those of `a` capped at `h`, the decoder keeps the cap, and the row of `u` is a lawful companion of
the same bottom pattern. -/
theorem extendsFromBoundary_fieldLayer (hk : ∀ d, S.toCellScheme.grade d = k)
    (hU : ¬ ((univ : Finset (Fin n)), k) ≤ U) (hV : ¬ ((univ : Finset (Fin n)), k) ≤ V)
    (hcover : ∀ d, S.toCellScheme.gradedIndex d ≤ U ∨ S.toCellScheme.gradedIndex d ≤ V)
    {u : Fin (S.fieldLayer k hS).card}
    (hu : (S.fieldLayer k hS).toCellScheme.gradedIndex u = (univ, k)) {h : Label.{u}}
    (hh : IsSelfVisible k h) (hbot : ⊥ < h) :
    (S.fieldLayer k hS).rows.ExtendsFromBoundary U V (univ, k) h
      ((S.fieldLayer k hS).rows.rowBelow u hu) := by
  intro w hwU hwV hwS
  obtain ⟨i, rfl⟩ := exists_natAdd_eq hu
  set a := S.catalogueEntry k i with ha_def
  have ha := catalogueEntry_mem (S := S) (k := k) i
  have hrowBelow (d : (S.fieldLayer k hS).toCellScheme.below (univ, k)) :
      (S.fieldLayer k hS).rows.rowBelow (Fin.natAdd S.card i) hu d = S.fieldRow k a d :=
    fieldLayer_row_natAdd i _
  -- The boundary labelling, on the old cells.
  set w₀ : Fin S.card → Label.{u} := fun d ↦ w (Fin.castAdd _ d) with hw₀_def
  have hw₀ : S.rows.IsLawful w₀ := isLawful_castAdd_of_boundary hk hU hV hcover hwU hwV
  have hv₀ (d : Fin S.card) : IsSelfVisible k (w₀ d) := hk d ▸ hw₀.orderly d
  have hold (d : Fin S.card) : Fin.castAdd (S.catalogue k).card d ∈
      (S.fieldLayer k hS).toCellScheme.below (univ, k) :=
    ⟨subset_univ _, (appendFullCellsScheme_grade_castAdd S k _ d).trans (hk d) |>.le⟩
  have hag₀ (d : Fin S.card) : min (w₀ d) h = min (a d) h := by
    have hbd : Fin.castAdd (S.catalogue k).card d ∈ (S.fieldLayer k hS).toCellScheme.below U ∨
        Fin.castAdd (S.catalogue k).card d ∈ (S.fieldLayer k hS).toCellScheme.below V := by
      simpa [CellScheme.mem_below] using hcover d
    have := hwS ⟨_, hold d⟩ hbd
    rwa [hrowBelow, fieldRow_castAdd] at this
  -- The canonical code of the boundary labelling, and its agreement with `a` (relative room).
  set b := canonicalCode k w₀ with hb_def
  have hb : b ∈ S.catalogue k := canonicalCode_mem_catalogue hk hw₀
  have hba (d : Fin S.card) : min (b d) h = min (a d) h :=
    min_canonicalCode_eq hv₀ (mem_catalogue.mp ha).2 hag₀ d
  have hrow (x : Fin (S.card + (S.catalogue k).card)) :
      min (S.fieldRow k b x) h = min (S.fieldRow k a x) h := by
    induction x using Fin.addCases with
    | left d => rw [fieldRow_castAdd, fieldRow_castAdd]; exact hba d
    | right j =>
      rw [fieldRow_natAdd, fieldRow_natAdd]
      exact min_agreementHeight_eq (bot_mem_grid _ _)
        (fun d ↦ ⟨mem_fieldGrid_of_mem_catalogue hb d, mem_fieldGrid_of_mem_catalogue ha d⟩) hba _
  have hvb (x : Fin (S.card + (S.catalogue k).card)) : IsSelfVisible k (S.fieldRow k b x) :=
    (properties_of_mem_grid (fieldRow_mem_fieldGrid hb x)).1
  have hcap (x : Fin (S.card + (S.catalogue k).card)) :
      min (literalDecoder k w₀ h (S.fieldRow k b x)) h = min (S.fieldRow k a x) h :=
    (min_literalDecoder_eq (hvb x)).trans (hrow x)
  have hlaw : (S.fieldLayer k hS).rows.IsLawful (literalDecoder k w₀ h ∘ S.fieldRow k b) :=
    (isLawful_fieldRow hb).map_of_min_eq (isLawful_fieldRow ha)
      (fun d ↦ (fieldLayer_grade hk d).le) (isWitness_literalDecoder hv₀ hh hbot.ne') hbot.ne'
      hcap
  refine ⟨fun d ↦ literalDecoder k w₀ h (S.fieldRow k b d), hlaw.isLawfulBelow _,
    fun d hd ↦ ?_, fun d ↦ by rw [hrowBelow]; exact hcap d⟩
  obtain ⟨e, he⟩ := hd.elim (exists_castAdd_eq hU) (exists_castAdd_eq hV)
  change literalDecoder k w₀ h (S.fieldRow k b d.1) = w d.1
  rw [← he, fieldRow_castAdd]
  exact literalDecoder_canonicalCode hv₀ (fun d ↦ (hba d).trans (hag₀ d).symm) e

end VaughtConjecture.Scheme
