/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import VaughtConjecture.Scheme.Row

/-!
# Coded copies of lawful sections

Roadmap, Layer 3 (the coatom extension construction: the row of the apex cell of its completion
must be coded); semantic contract, item 3 (rows are coded labellings).

The rows of a scheme are coded (`Scheme.IsCoded`: every row value lies below `ω ^ 2`), while the
labels of a stage type are arbitrary labels at its stage.  A cell above every other cell whose
label is the formal top (the apex of `VaughtConjecture.Extension.Apex`) needs, as its row, a
coded lawful labelling of the other cells that transforms back to their actual labels.  This file
constructs it: the coded copy of the labels.

**The block coding.**  Fix a finite set `V` of labels and a threshold `K`.  The *value blocks*
(`Label.valueBands V`) are the quotients `o / ω` of the ordinals `o` in `V` (a block
`[ω * b, ω * b + ω)` is indexed by `b`), and the *code blocks* (`Label.codeBands V`) are the value
blocks with their successors.  The block coding `Label.bandEncode V K` sends an ordinal
`o = ω * b + n` (`n < ω`) to `ω * r + n` if `b` is a value block and to `ω * r + K` otherwise, where
`r` is the number of code blocks at most `b` (`Label.codeRank`); it fixes `⊥` and sends the formal
top to `ω * (N + 1) + K`, `N` the number of code blocks.  Every code lies below `ω ^ 2`
(`Label.bandEncode_lt`).  The block decoding `Label.bandDecode V` sends `ω * (i + 1) + n` to
`ω * e + n` for the `i`-th code block `e`, the codes of rank `0` to `⊥`, and larger codes to the
formal top.  Both depend on `V` (and the coding on `K`); they are not a coding of all labels at
once.

* The coding is monotone (`Label.monotone_bandEncode`), and strictly increasing at the labels of
  `V` (`Label.bandEncode_lt_bandEncode`), since a value block is followed by its successor among the
  code blocks; it commutes with visibility replacement at every threshold `k ≤ K`
  (`Label.bandEncode_visibilityReplace`), since a block that is not a value block is sent to a code
  whose finite part is `K`, and so it keeps self-visibility at those thresholds.
* The decoding recovers every label of `V` and the formal top (`Label.bandDecode_bandEncode`,
  `Label.bandDecode_bandEncode_top`), and with the constant suppressor `⊤` it is a transformation
  witness (`Label.isWitness_bandDecode`): it relabels blocks and fixes finite parts.
* **Witness transfer** (`Label.IsWitness.bandEncode`): a witness `(g, σ)` whose suppressor takes its
  values at grades `≤ K` in `V` gives the witness `(bandEncode ∘ g, bandEncode ∘ σ)`, the coded
  suppressor replaced by bottom above `K` (the shifter is coded at every label).  The guard of the
  coded shifter implies the guard of `σ`, because the coding is strictly increasing at the values of
  `g`.

**Coded copies** (`CellScheme.Rows.IsLawful.exists_bandEncode`).  The *coded copy* of a labelling
`w` relative to a finite set `V` containing its labels is `bandEncode V K ∘ w`: every value lies
below `ω ^ 2`, and the block decoding recovers `w` from it.  For a lawful section `w` of rows over
finitely many cells of grade at most `K`, some finite `V` containing every label of `w` makes the
coded copy `bandEncode V K ∘ w` lawful: take for `V` the labels of `w` and the values of one
locality witness for each cell, and transfer the witnesses.  Nothing about the rows is assumed.

## Placement

The block coding belongs in a `Label/Coding.lean` beside `VaughtConjecture.Label.Transform`, and
`CellScheme.Rows.IsLawful.exists_bandEncode` in `VaughtConjecture.Scheme.Row`, after the lawful
sections.  They are stated here so that those folders are unchanged.

## References

Rows are coded as in the range normalization of [Kni26, Lemma 2.5.13]; transformation witnesses
are [Kni26, Definition 2.3.9], and visibility replacement is [Kni26, Definition 2.2.3].
-/

universe u

namespace VaughtConjecture.Label

open Finset Ordinal

/-! ### Blocks of ordinals -/

section Blocks

variable {a b x y : Ordinal.{u}}

/-- The quotient by `ω` of `ω * a + x`, for `x < ω`. -/
private theorem omega0_mul_add_div (hx : x < ω) : (ω * a + x) / ω = a := by
  rw [Ordinal.mul_add_div _ omega0_ne_zero, Ordinal.div_eq_zero_of_lt hx, add_zero]

/-- The finite part of `ω * a + x`, for `x < ω`. -/
private theorem omega0_mul_add_mod (hx : x < ω) : (ω * a + x) % ω = x := by
  rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx]

/-- An ordinal in a lower block lies below every ordinal in a higher block. -/
private theorem omega0_mul_add_lt (hx : x < ω) (h : a < b) (y : Ordinal.{u}) :
    ω * a + x < ω * b + y := by
  calc ω * a + x < ω * a + ω := add_lt_add_right hx _
    _ = ω * Order.succ a := (Ordinal.mul_succ _ _).symm
    _ ≤ ω * b := by gcongr; exact Order.succ_le_of_lt h
    _ ≤ ω * b + y := le_self_add

/-- Visibility replacement of `ω * a + x`, for `x < ω`, replaces `x`. -/
private theorem visibilityReplace_omega0_mul_add (hx : x < ω) (k i : ℕ) :
    Ordinal.visibilityReplace k i (ω * a + x) = ω * a + if x < k then (i : Ordinal) else x := by
  rw [Ordinal.visibilityReplace, omega0_mul_add_div hx, omega0_mul_add_mod hx]

/-- In one block, ordinals compare as their finite parts. -/
private theorem mod_le_mod_of_div_eq (h : x ≤ y) (he : x / ω = y / ω) : x % ω ≤ y % ω := by
  have := Ordinal.div_add_mod x ω ▸ Ordinal.div_add_mod y ω ▸ h
  rwa [he, add_le_add_iff_left] at this

/-- In one block, ordinals compare strictly as their finite parts. -/
private theorem mod_lt_mod_of_div_eq (h : x < y) (he : x / ω = y / ω) : x % ω < y % ω := by
  have := Ordinal.div_add_mod x ω ▸ Ordinal.div_add_mod y ω ▸ h
  rwa [he, add_lt_add_iff_left] at this

/-- `ω * n + x` lies below `ω ^ 2` for a natural number `n` and `x < ω`. -/
private theorem omega0_mul_natCast_add_lt (n : ℕ) (hx : x < ω) :
    ω * (n : Ordinal.{u}) + x < ω ^ 2 := by
  have h : ω * (n : Ordinal.{u}) + x < ω * ((n + 1 : ℕ) : Ordinal.{u}) + 0 :=
    omega0_mul_add_lt hx (by exact_mod_cast Nat.lt_succ_self n) 0
  calc ω * (n : Ordinal.{u}) + x < ω * ((n + 1 : ℕ) : Ordinal.{u}) := by rwa [add_zero] at h
    _ ≤ ω * ω := by gcongr; exact (natCast_lt_omega0 _).le
    _ = ω ^ 2 := (sq _).symm

end Blocks

/-! ### The block coding -/

variable (V : Finset Label.{u}) (K : ℕ)

/-- The *value blocks* of a finite set of labels: the quotients by `ω` of its ordinals. -/
noncomputable def valueBands : Finset Ordinal.{u} :=
  (V.preimage (fun o : Ordinal.{u} ↦ (o : Label.{u}))
    (WithBot.coe_injective.comp WithTop.coe_injective).injOn).image (· / ω)

/-- The *code blocks*: the value blocks and their successors. -/
noncomputable def codeBands : Finset Ordinal.{u} :=
  valueBands V ∪ (valueBands V).image Order.succ

/-- The *code rank* of a block: the number of code blocks at most it. -/
noncomputable def codeRank (b : Ordinal.{u}) : ℕ := #{e ∈ codeBands V | e ≤ b}

/-- The code blocks in increasing order. -/
noncomputable def codeBandEmb : Fin #(codeBands V) ↪o Ordinal.{u} :=
  (codeBands V).orderEmbOfFin rfl

open Classical in
/-- The coding of an ordinal: `ω * r + n` for `o = ω * b + n` in a value block `b` of code rank
`r`, and `ω * r + K` if `b` is not a value block. -/
noncomputable def bandEncodeOrd (o : Ordinal.{u}) : Ordinal.{u} :=
  ω * (codeRank V (o / ω) : Ordinal.{u}) + if o / ω ∈ valueBands V then o % ω else (K : Ordinal)

/-- The code of the formal top: `ω * (N + 1) + K`, for `N` code blocks. -/
noncomputable def bandTopCode : Ordinal.{u} := ω * ((#(codeBands V) + 1 : ℕ) : Ordinal.{u}) + K

/-- The **block coding** of labels: bottom is fixed, an ordinal is sent to `bandEncodeOrd V K`, and
the formal top to `bandTopCode V K`. -/
noncomputable def bandEncode : Label.{u} → Label.{u} :=
  recBotCoeTop ⊥ (fun o ↦ (bandEncodeOrd V K o : Label.{u})) (bandTopCode V K : Label.{u})

open Classical in
/-- The decoding of an ordinal code: `ω * (i + 1) + n` is read as `ω * e + n` for the `i`-th code
block `e`; codes of rank `0` are read as `⊥`, and larger codes as the formal top. -/
noncomputable def bandDecodeOrd (z : Ordinal.{u}) : Label.{u} :=
  if h : ∃ i : Fin #(codeBands V), z / ω = ((i + 1 : ℕ) : Ordinal.{u}) then
    ((ω * codeBandEmb V h.choose + z % ω : Ordinal.{u}) : Label.{u})
  else if z / ω = 0 then ⊥ else ⊤

/-- The **block decoding** of labels: bottom and the formal top are fixed, and an ordinal code is
read by `bandDecodeOrd V`. -/
noncomputable def bandDecode : Label.{u} → Label.{u} :=
  recBotCoeTop ⊥ (bandDecodeOrd V) ⊤

variable {V K}

/-- The coding fixes bottom. -/
@[simp] theorem bandEncode_bot : bandEncode V K ⊥ = ⊥ := rfl

/-- The coding of an ordinal. -/
@[simp] theorem bandEncode_coe (o : Ordinal.{u}) :
    bandEncode V K o = (bandEncodeOrd V K o : Label.{u}) := rfl

/-- The coding of the formal top. -/
@[simp] theorem bandEncode_top : bandEncode V K ⊤ = (bandTopCode V K : Label.{u}) := rfl

/-- The decoding fixes bottom. -/
@[simp] theorem bandDecode_bot : bandDecode V ⊥ = ⊥ := rfl

/-- The decoding of an ordinal code. -/
@[simp] theorem bandDecode_coe (z : Ordinal.{u}) : bandDecode V z = bandDecodeOrd V z := rfl

/-- The decoding fixes the formal top. -/
@[simp] theorem bandDecode_top : bandDecode V ⊤ = ⊤ := rfl

/-! #### Code blocks and ranks -/

/-- A value block is a code block. -/
theorem mem_codeBands_of_mem_valueBands {b : Ordinal.{u}} (hb : b ∈ valueBands V) :
    b ∈ codeBands V :=
  mem_union_left _ hb

/-- The successor of a value block is a code block. -/
theorem succ_mem_codeBands {b : Ordinal.{u}} (hb : b ∈ valueBands V) :
    Order.succ b ∈ codeBands V :=
  mem_union_right _ (mem_image_of_mem _ hb)

/-- The block of an ordinal of `V` is a value block. -/
theorem div_mem_valueBands {o : Ordinal.{u}} (ho : (o : Label.{u}) ∈ V) :
    o / ω ∈ valueBands V :=
  mem_image_of_mem _ (mem_preimage.mpr ho)

/-- The code rank increases with the block. -/
theorem codeRank_mono : Monotone (codeRank V) := fun _ _ h ↦
  card_le_card (monotone_filter_right _ fun _ _ h' ↦ h'.trans h)

/-- The code rank strictly increases past a code block. -/
theorem codeRank_lt_codeRank {b b' e : Ordinal.{u}} (he : e ∈ codeBands V) (hbe : b < e)
    (heb : e ≤ b') : codeRank V b < codeRank V b' := by
  refine card_lt_card ⟨monotone_filter_right _ fun _ _ h' ↦ h'.trans (hbe.le.trans heb),
    fun h ↦ ?_⟩
  exact hbe.not_ge (mem_filter.mp (h (mem_filter.mpr ⟨he, heb⟩))).2

/-- The code rank strictly increases past a value block. -/
theorem codeRank_lt_of_mem_valueBands {b b' : Ordinal.{u}} (hb : b ∈ valueBands V)
    (h : b < b') : codeRank V b < codeRank V b' :=
  codeRank_lt_codeRank (succ_mem_codeBands hb) (Order.lt_succ_of_not_isMax (not_isMax b))
    (Order.succ_le_of_lt h)

/-- The code rank is at most the number of code blocks. -/
theorem codeRank_le (b : Ordinal.{u}) : codeRank V b ≤ #(codeBands V) :=
  card_filter_le _ _

/-- The code rank of the `i`-th code block is `i + 1`. -/
theorem codeRank_codeBandEmb (i : Fin #(codeBands V)) :
    codeRank V (codeBandEmb V i) = i + 1 := by
  have : ({e ∈ codeBands V | e ≤ codeBandEmb V i} : Finset Ordinal.{u}) =
      (Iic i).map (codeBandEmb V).toEmbedding := by
    ext e
    simp only [mem_filter, mem_map, mem_Iic, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨he, hle⟩
      have : e ∈ Set.range (codeBandEmb V) := by
        rw [codeBandEmb, range_orderEmbOfFin]
        exact he
      obtain ⟨j, rfl⟩ := this
      exact ⟨j, (codeBandEmb V).le_iff_le.mp hle, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨orderEmbOfFin_mem _ _ j, (codeBandEmb V).le_iff_le.mpr hj⟩
  rw [codeRank, this, card_map, Fin.card_Iic]

/-- Every code block is the `i`-th code block for some `i`. -/
theorem exists_codeBandEmb_eq {e : Ordinal.{u}} (he : e ∈ codeBands V) :
    ∃ i, codeBandEmb V i = e := by
  have : e ∈ Set.range (codeBandEmb V) := by
    rw [codeBandEmb, range_orderEmbOfFin]
    exact he
  exact this

/-! #### Properties of the coding -/

/-- The finite part used by the coding is finite. -/
private theorem bandEncodeOrd_mod_lt (o : Ordinal.{u}) :
    (if o / ω ∈ valueBands V then o % ω else (K : Ordinal.{u})) < ω := by
  split_ifs
  · exact Ordinal.mod_lt _ omega0_ne_zero
  · exact natCast_lt_omega0 K

/-- A lower code rank gives a lower code. -/
private theorem bandEncodeOrd_lt_of_codeRank_lt {o o' : Ordinal.{u}}
    (h : codeRank V (o / ω) < codeRank V (o' / ω)) : bandEncodeOrd V K o < bandEncodeOrd V K o' :=
  omega0_mul_add_lt (bandEncodeOrd_mod_lt o) (by exact_mod_cast h) _

/-- The code of an ordinal lies below the code of the formal top. -/
private theorem bandEncodeOrd_lt_bandTopCode (o : Ordinal.{u}) :
    bandEncodeOrd V K o < bandTopCode V K :=
  omega0_mul_add_lt (bandEncodeOrd_mod_lt o)
    (by exact_mod_cast Nat.lt_succ_of_le (codeRank_le (o / ω))) _

/-- The coding of ordinals is monotone. -/
private theorem bandEncodeOrd_mono {o o' : Ordinal.{u}} (h : o ≤ o') :
    bandEncodeOrd V K o ≤ bandEncodeOrd V K o' := by
  have hb : o / ω ≤ o' / ω := Ordinal.div_le_left h ω
  rcases (codeRank_mono hb : codeRank V (o / ω) ≤ codeRank V (o' / ω)).lt_or_eq with hr | hr
  · exact (bandEncodeOrd_lt_of_codeRank_lt hr).le
  by_cases hB : o / ω ∈ valueBands V
  · -- The block of `o` is followed by its successor among the code blocks: same block.
    have he : o / ω = o' / ω := hb.eq_or_lt.resolve_right fun hlt ↦
      (codeRank_lt_of_mem_valueBands hB hlt).ne hr
    rw [bandEncodeOrd, bandEncodeOrd, ← he, hr, ite_eq_left hB, ite_eq_left hB]
    exact add_le_add_right (mod_le_mod_of_div_eq h he) _
  · -- The block of `o'` is not a value block either.
    have hB' : o' / ω ∉ valueBands V := fun hB' ↦ by
      rcases hb.eq_or_lt with he | hlt
      · exact hB (he ▸ hB')
      · exact (codeRank_lt_codeRank (mem_codeBands_of_mem_valueBands hB') hlt le_rfl).ne hr
    rw [bandEncodeOrd, bandEncodeOrd, hr, ite_eq_right hB, ite_eq_right hB']

/-- **The coding is monotone.** -/
theorem monotone_bandEncode : Monotone (bandEncode V K) := by
  intro x y h
  induction x using recBotCoeTop with
  | bot => exact bot_le
  | top => rw [top_le_iff.mp h]
  | coe o =>
    induction y using recBotCoeTop with
    | bot => exact absurd h (not_le.mpr (WithBot.bot_lt_coe _))
    | top =>
      exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (bandEncodeOrd_lt_bandTopCode o).le)
    | coe o' =>
      exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
        (bandEncodeOrd_mono (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h))))

/-- The coding of a label is bottom only for bottom. -/
@[simp] theorem bandEncode_eq_bot_iff {x : Label.{u}} : bandEncode V K x = ⊥ ↔ x = ⊥ := by
  induction x using recBotCoeTop <;> simp

/-- **The coding is strictly increasing at the labels of `V`.** -/
theorem bandEncode_lt_bandEncode {z y : Label.{u}} (hz : z ∈ V) (h : z < y) :
    bandEncode V K z < bandEncode V K y := by
  induction z using recBotCoeTop with
  | bot =>
    refine bot_lt_iff_ne_bot.mpr fun he ↦ ?_
    exact h.ne' (bandEncode_eq_bot_iff.mp he)
  | top => exact absurd h (not_lt.mpr le_top)
  | coe o =>
    have hB := div_mem_valueBands hz
    induction y using recBotCoeTop with
    | bot => exact absurd h (not_lt.mpr bot_le)
    | top => exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (bandEncodeOrd_lt_bandTopCode o))
    | coe o' =>
      have ho : o < o' := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h)
      refine WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ?_)
      rcases (Ordinal.div_le_left ho.le ω).eq_or_lt with he | hlt
      · rw [bandEncodeOrd, bandEncodeOrd, ← he, ite_eq_left hB, ite_eq_left hB]
        exact add_lt_add_right (mod_lt_mod_of_div_eq ho he) _
      · exact bandEncodeOrd_lt_of_codeRank_lt (codeRank_lt_of_mem_valueBands hB hlt)

/-- **The coding commutes with visibility replacement** at every threshold `k ≤ K`. -/
theorem bandEncode_visibilityReplace {k : ℕ} (hk : k ≤ K) (i : ℕ) (x : Label.{u}) :
    bandEncode V K (visibilityReplace k i x) = visibilityReplace k i (bandEncode V K x) := by
  have hK : ¬ (K : Ordinal.{u}) < k := by exact_mod_cast hk.not_gt
  induction x using recBotCoeTop with
  | bot => rfl
  | top =>
    simp only [visibilityReplace_top, bandEncode_top, visibilityReplace_coe, bandTopCode]
    rw [visibilityReplace_omega0_mul_add (natCast_lt_omega0 K), ite_eq_right hK]
  | coe o =>
    simp only [visibilityReplace_coe, bandEncode_coe, bandEncodeOrd, Ordinal.visibilityReplace_div]
    rw [visibilityReplace_omega0_mul_add (bandEncodeOrd_mod_lt o)]
    by_cases hB : o / ω ∈ valueBands V
    · rw [ite_eq_left hB, ite_eq_left hB, Ordinal.visibilityReplace_mod]
    · rw [ite_eq_right hB, ite_eq_right hB, ite_eq_right hK]

/-- The coding keeps self-visibility at every threshold `k ≤ K`. -/
theorem IsSelfVisible.bandEncode {k : ℕ} (hk : k ≤ K) {x : Label.{u}} (hx : IsSelfVisible k x) :
    IsSelfVisible k (bandEncode V K x) := by
  rw [IsSelfVisible, ← bandEncode_visibilityReplace hk, hx]

/-- The code of the formal top is self-visible at every threshold `k ≤ K`. -/
theorem isSelfVisible_bandEncode_top {k : ℕ} (hk : k ≤ K) : IsSelfVisible k (bandEncode V K ⊤) :=
  (isSelfVisible_top k).bandEncode hk

/-- **Every code lies below `ω ^ 2`.** -/
theorem bandEncode_lt (x : Label.{u}) :
    bandEncode V K x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => exact WithBot.bot_lt_coe _
  | top => exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
      (omega0_mul_natCast_add_lt _ (natCast_lt_omega0 K)))
  | coe o => exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
      (omega0_mul_natCast_add_lt _ (bandEncodeOrd_mod_lt o)))

/-- Every code lies at most the code of the formal top. -/
theorem bandEncode_le_bandEncode_top (x : Label.{u}) : bandEncode V K x ≤ bandEncode V K ⊤ :=
  monotone_bandEncode le_top

/-! #### The decoding -/

/-- The decoding of a code of rank `i + 1`. -/
theorem bandDecodeOrd_of_eq {z : Ordinal.{u}} (i : Fin #(codeBands V))
    (h : z / ω = ((i + 1 : ℕ) : Ordinal.{u})) :
    bandDecodeOrd V z = ((ω * codeBandEmb V i + z % ω : Ordinal.{u}) : Label.{u}) := by
  have hex : ∃ i : Fin #(codeBands V), z / ω = ((i + 1 : ℕ) : Ordinal.{u}) := ⟨i, h⟩
  have hi : hex.choose = i := Fin.ext (by
    have := hex.choose_spec.symm.trans h
    exact Nat.succ_injective (by exact_mod_cast this))
  rw [bandDecodeOrd, dite_eq_left hex, hi]

/-- The decoding of a code of rank `0`. -/
theorem bandDecodeOrd_of_eq_zero {z : Ordinal.{u}} (h : z / ω = 0) : bandDecodeOrd V z = ⊥ := by
  have hex : ¬ ∃ i : Fin #(codeBands V), z / ω = ((i + 1 : ℕ) : Ordinal.{u}) := by
    rintro ⟨i, hi⟩
    rw [h] at hi
    exact absurd (by exact_mod_cast hi.symm : (i : ℕ) + 1 = 0) (Nat.succ_ne_zero _)
  rw [bandDecodeOrd, dite_eq_right hex, ite_eq_left h]

/-- The decoding of a code of rank above the number of code blocks. -/
theorem bandDecodeOrd_of_lt {z : Ordinal.{u}} (h : ((#(codeBands V) : ℕ) : Ordinal.{u}) < z / ω) :
    bandDecodeOrd V z = ⊤ := by
  have hex : ¬ ∃ i : Fin #(codeBands V), z / ω = ((i + 1 : ℕ) : Ordinal.{u}) := by
    rintro ⟨i, hi⟩
    rw [hi] at h
    exact absurd (by exact_mod_cast h : #(codeBands V) < i + 1) (not_lt.mpr i.isLt)
  rw [bandDecodeOrd, dite_eq_right hex, ite_eq_right (fun h0 ↦ by simp [h0] at h)]

/-- The three kinds of codes: rank `0`, rank `i + 1` for a code block, and rank above the number
of code blocks. -/
private theorem codeRank_trichotomy (c : Ordinal.{u}) :
    c = 0 ∨ (∃ i : Fin #(codeBands V), c = ((i + 1 : ℕ) : Ordinal.{u})) ∨
      ((#(codeBands V) : ℕ) : Ordinal.{u}) < c := by
  rcases lt_or_ge ((#(codeBands V) : ℕ) : Ordinal.{u}) c with h | h
  · exact Or.inr (Or.inr h)
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp (h.trans_lt (natCast_lt_omega0 _))
  have hn : n ≤ #(codeBands V) := by exact_mod_cast h
  rcases n with _ | n
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inl ⟨⟨n, hn⟩, rfl⟩)

/-- Visibility replacement fixes the decoding of a code, block by block. -/
private theorem bandDecodeOrd_visibilityReplace (k i : ℕ) (z : Ordinal.{u}) :
    bandDecodeOrd V (Ordinal.visibilityReplace k i z) =
      visibilityReplace k i (bandDecodeOrd V z) := by
  have hdiv := Ordinal.visibilityReplace_div k i z
  rcases codeRank_trichotomy (V := V) (z / ω) with h | ⟨j, h⟩ | h
  · rw [bandDecodeOrd_of_eq_zero h, bandDecodeOrd_of_eq_zero (hdiv.trans h), visibilityReplace_bot]
  · rw [bandDecodeOrd_of_eq j h, bandDecodeOrd_of_eq j (hdiv.trans h), visibilityReplace_coe,
      visibilityReplace_omega0_mul_add (Ordinal.mod_lt _ omega0_ne_zero),
      Ordinal.visibilityReplace_mod]
  · rw [bandDecodeOrd_of_lt h, bandDecodeOrd_of_lt (hdiv ▸ h), visibilityReplace_top]

/-- The decoding of ordinal codes is monotone. -/
private theorem bandDecodeOrd_mono {z z' : Ordinal.{u}} (hz : z ≤ z') :
    bandDecodeOrd V z ≤ bandDecodeOrd V z' := by
  have hc : z / ω ≤ z' / ω := Ordinal.div_le_left hz ω
  rcases codeRank_trichotomy (V := V) (z / ω) with h | ⟨j, h⟩ | h
  · rw [bandDecodeOrd_of_eq_zero h]
    exact bot_le
  · rcases codeRank_trichotomy (V := V) (z' / ω) with h' | ⟨j', h'⟩ | h'
    · rw [h, h'] at hc
      exact absurd (by exact_mod_cast hc : (j : ℕ) + 1 ≤ 0) (Nat.not_succ_le_zero _)
    · rw [bandDecodeOrd_of_eq j h, bandDecodeOrd_of_eq j' h']
      refine WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ?_)
      have hjj : (j : ℕ) ≤ j' := by
        rw [h, h'] at hc
        exact Nat.succ_le_succ_iff.mp (by exact_mod_cast hc)
      rcases hjj.eq_or_lt with he | hlt
      · obtain rfl : j = j' := Fin.ext he
        exact add_le_add_right (mod_le_mod_of_div_eq hz (h.trans h'.symm)) _
      · exact (omega0_mul_add_lt (Ordinal.mod_lt _ omega0_ne_zero)
          ((codeBandEmb V).strictMono (Fin.mk_lt_mk.mpr hlt)) _).le
    · rw [bandDecodeOrd_of_lt h']
      exact le_top
  · rw [bandDecodeOrd_of_lt h, bandDecodeOrd_of_lt (h.trans_le hc)]

/-- **The decoding is a transformation witness** with the constant suppressor `⊤`: it fixes
bottom, is monotone, and commutes with every visibility replacement. -/
theorem isWitness_bandDecode : IsWitness (fun _ ↦ (⊤ : Label.{u})) (bandDecode V) where
  antitone := antitone_const
  isSelfVisible _ := isSelfVisible_top _
  map_bot := rfl
  monotone x y h := by
    induction x using recBotCoeTop with
    | bot => exact bot_le
    | top => rw [top_le_iff.mp h]
    | coe z =>
      induction y using recBotCoeTop with
      | bot => exact absurd h (not_le.mpr (WithBot.bot_lt_coe _))
      | top => exact le_top
      | coe z' => exact bandDecodeOrd_mono (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h))
  visibilityReplace_comm x k _ i _ := by
    induction x using recBotCoeTop with
    | bot => rfl
    | top => rfl
    | coe z => exact bandDecodeOrd_visibilityReplace k i z

/-- The decoding recovers the formal top. -/
theorem bandDecode_bandEncode_top : bandDecode V (bandEncode V K ⊤) = ⊤ :=
  bandDecodeOrd_of_lt (by
    rw [bandTopCode, omega0_mul_add_div (natCast_lt_omega0 K)]
    exact_mod_cast Nat.lt_succ_self _)

/-- **The decoding recovers every label of `V`.** -/
theorem bandDecode_bandEncode {z : Label.{u}} (hz : z ∈ V) :
    bandDecode V (bandEncode V K z) = z := by
  induction z using recBotCoeTop with
  | bot => rfl
  | top => exact bandDecode_bandEncode_top
  | coe o =>
    have hB := div_mem_valueBands hz
    obtain ⟨i, hi⟩ := exists_codeBandEmb_eq (mem_codeBands_of_mem_valueBands hB)
    have hr : bandEncodeOrd V K o / ω = ((i + 1 : ℕ) : Ordinal.{u}) := by
      rw [bandEncodeOrd, omega0_mul_add_div (bandEncodeOrd_mod_lt o), ← hi, codeRank_codeBandEmb]
    rw [bandEncode_coe, bandDecode_coe, bandDecodeOrd_of_eq i hr, hi, bandEncodeOrd, ite_eq_left hB,
      omega0_mul_add_mod (Ordinal.mod_lt _ omega0_ne_zero), Ordinal.div_add_mod]

/-! #### Witness transfer -/

variable {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}

/-- **Witness transfer.**  If the suppressor `g` takes its values at the grades `≤ K` in `V`, then
coding the shifter, and coding the suppressor and replacing it by bottom above `K`, gives a
witness. -/
theorem IsWitness.bandEncode (hw : IsWitness g σ) (hV : ∀ n ≤ K, g n ∈ V) :
    IsWitness (fun n ↦ if n ≤ K then bandEncode V K (g n) else ⊥) (bandEncode V K ∘ σ) where
  antitone n n' h := by
    beta_reduce
    split_ifs with h' h''
    · exact monotone_bandEncode (hw.antitone h)
    · exact absurd (h.trans h') h''
    · exact bot_le
    · exact le_rfl
  isSelfVisible n := by
    split_ifs with hn
    · exact (hw.isSelfVisible n).bandEncode hn
    · exact isSelfVisible_bot n
  map_bot := by simp [hw.map_bot]
  monotone := monotone_bandEncode.comp hw.monotone
  visibilityReplace_comm x k hx i hi := by
    simp only [Function.comp_apply] at hx ⊢
    split_ifs at hx with hk
    · -- The guard of `σ` holds: the coding is strictly increasing at the value `g k ∈ V`.
      have hg : σ x ≤ g k := not_lt.mp fun hlt ↦ (bandEncode_lt_bandEncode (hV k hk) hlt).not_ge hx
      rw [hw.visibilityReplace_comm x k hg i hi, bandEncode_visibilityReplace hk]
    · have hb : σ x = ⊥ := bandEncode_eq_bot_iff.mp (le_bot_iff.mp hx)
      rw [hw.visibilityReplace_comm x k (hb ▸ bot_le) i hi, hb, visibilityReplace_bot,
        bandEncode_bot, visibilityReplace_bot]

end VaughtConjecture.Label

/-! ### Coded copies of lawful sections -/

namespace VaughtConjecture.CellScheme.Rows

open Finset Label

variable {ι α : Type*} [Finite ι] {D : CellScheme ι α} {R : D.Rows.{u}} {w : ι → Label.{u}}

/-- **Coded copies of lawful sections.**  If `w` is a lawful section of rows over finitely many
cells of grade at most `K`, then for some finite set `V` of labels containing every label of `w`,
the coded copy `bandEncode V K ∘ w` is lawful: `V` holds the labels of `w` and the values at
grades `≤ K` of one locality witness for each cell, and the witnesses are transferred. -/
theorem IsLawful.exists_bandEncode (hw : R.IsLawful w) {K : ℕ} (hK : ∀ d, D.grade d ≤ K) :
    ∃ V : Finset Label.{u}, (∀ d, w d ∈ V) ∧ R.IsLawful (bandEncode V K ∘ w) := by
  classical
  have := Fintype.ofFinite ι
  choose g σ hg heq using hw.locality
  set V : Finset Label.{u} :=
    univ.image w ∪ (univ ×ˢ range (K + 1)).image fun p : ι × ℕ ↦ g p.1 p.2
  have hgV (s : ι) (n : ℕ) (hn : n ≤ K) : g s n ∈ V :=
    mem_union_right _ (mem_image.mpr
      ⟨(s, n), mem_product.mpr ⟨mem_univ _, mem_range.mpr (Nat.lt_succ_of_le hn)⟩, rfl⟩)
  refine ⟨V, fun d ↦ mem_union_left _ (mem_image_of_mem _ (mem_univ d)), ?_, ?_, ?_⟩
  · exact fun d ↦ (hw.orderly d).bandEncode (hK d)
  · intro s
    refine ⟨_, _, (hg s).bandEncode (hgV s), fun d ↦ ?_⟩
    simp only [Function.comp_apply, ite_eq_left (hK d)]
    rw [← monotone_bandEncode.map_min, ← monotone_bandEncode.map_min]
    exact congrArg _ (heq s d)
  · intro s t hst hgr
    obtain ⟨u, hu, hle⟩ := hw.availability s t hst hgr
    exact ⟨u, hu, monotone_bandEncode hle⟩

end VaughtConjecture.CellScheme.Rows
