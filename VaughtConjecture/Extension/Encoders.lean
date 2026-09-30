/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Coding
import VaughtConjecture.Extension.CodedSection
import VaughtConjecture.Extension.SectionTheorem

/-!
# The strongly coded encoder and its decoder

Roadmap, Layer 3, 3.1, row 6, checkpoint 2.3 (coded encoders and decoders; the numerical decoding
identities kept apart from lawfulness and from cap preservation) and 3.1 (catalogues and
decoders); semantic contract, item 3.

The band coding `bandEncode V K` of `VaughtConjecture.Extension.CodedSection` relabels the bands
of the labels of a finite set `V` and keeps their finite parts, so its codes lie below `ω ^ 2`
(the range normalization of [Kni26, Lemma 2.5.13]) but need not be strongly coded
(`Label.IsStronglyCoded`, finite part at most `K + 1`).  The **strongly coded encoder** first
gives every ordinal whose finite part exceeds `K` a band of its own and then applies the band
coding; every code it produces is strongly coded at `K`.  This is a theorem about the codes this
encoder constructs, not a bound on the rows of arbitrary legal inputs, which are only coded.

The codes are strongly coded at `K`, not short at `K` (`Label.IsShort`): a label whose finite
part exceeds `K` is sent to finite part `K + 1` (`Label.isShort_spread`), and the code of `3` at
`K = 1` is not short at `1` (`VaughtConjecture.Extension.TransformationExamples`).  A row built
from codes need not satisfy the shortness branch of the section theorem at its grade; where 2.5
and 2.6 need short full-scope rows, the shortness comes from how the field layer builds their
profiles, not from the encoder.

**Spreading** (`Label.spread K`).  An ordinal `ω * b + n` (`n < ω`) goes to `ω * (ω * b) + n` if
`n ≤ K` and to `ω * (ω * b + n) + (K + 1)` otherwise: the part of each band up to `K` is kept in
one band, and each point above `K` gets a band of its own, at finite part `K + 1`.  The
**unspreading** `Label.unspread K` sends `ω * (ω * b + j) + x` to `ω * b + min x K` if `j = 0` and
to `ω * b + max j K` otherwise, so that `unspread K ∘ spread K = id` (`Label.unspread_spread`).
Both are monotone, send only bottom to bottom, and commute with visibility replacement at every
threshold `k ≤ K`; they are witnesses bounded by `K` (`Label.isWitness_spread`,
`Label.isWitness_unspread`).

**The encoder and decoder.**  For a finite set `V` of labels,
`Label.strongEncode V K = bandEncode (V.image (spread K)) K ∘ spread K` and
`Label.strongDecode V K = unspread K ∘ bandDecode (V.image (spread K))`.

* *Witness laws.*  Both are witnesses bounded by `K` (`Label.isWitness_strongEncode`,
  `Label.isWitness_strongDecode`); the encoder sends only bottom to bottom
  (`Label.strongEncode_eq_bot_iff`).  So are the band coding and decoding themselves
  (`Label.isWitness_bandEncode_stepSuppressor`, and `Label.isWitness_bandDecode_stepSuppressor`,
  the truncation at `K` of `Label.isWitness_bandDecode`).
* *Coding.*  Every code is strongly coded at `K` (`Label.isStronglyCoded_strongEncode`) and lies
  in the coded alphabet with block bound `2 * #V + 1` and offset bound `K + 1`
  (`Label.strongEncode_mem_codedAlphabet`); the formal top has a proper code.
* *Numerical decoding identities.*  The decoder reads back every label of `V`
  (`Label.strongDecode_strongEncode`), so the encoder is injective on `V`
  (`Label.injOn_strongEncode`); both are monotone (`Label.monotone_strongEncode`,
  `Label.monotone_strongDecode`), so both commute with `min` (`Monotone.map_min`).
* *Cap preservation*, numerical, per coordinate, and separate from lawfulness.  The caps
  preserved are the labels `c` of `V`: capping commutes with decoding at the code of `c`
  (`Label.strongDecode_min_strongEncode`), so two codes that agree capped at the code of `c`
  decode to labels that agree capped at `c` (`Label.min_strongDecode_eq_min_strongDecode`, and
  `Label.min_strongDecode_eq_of_min_eq` when one code is read back); capped agreement at `c` is
  preserved and reflected by the encoder (`Label.forall_min_strongEncode_eq_iff`).  The caps used
  by 2.5 and 2.6 are self-visible at the grade bound `K`, and so are their codes
  (`Label.isSelfVisible_strongEncode`), so capping a lawful code section at such a code keeps it
  lawful ([Kni26, Lemma 2.5.8]).
* *Lawfulness* (`CellScheme.Rows.IsLawful.strongEncode`): the encoded section of a lawful
  section is lawful, for every `V`, since the encoder is a bottom-reflecting witness.  The
  decoder does not reflect bottom (it sends the codes below `ω` to bottom), and the decoded section
  of a lawful section need not be lawful; decoding is lawful ownerwise
  (`CellScheme.Rows.IsLawful.strongDecode_of_ownerwise`, in
  `VaughtConjecture.Extension.OwnerwiseDecoding`).

**The existential coded copies are redundant.**  The band coding is itself a bottom-reflecting
witness bounded by `K` (`Label.isWitness_bandEncode_stepSuppressor`), so
`CellScheme.Rows.IsLawful.map_of_bot_reflecting` makes `bandEncode V K ∘ w` lawful for every
finite set `V` of labels and every lawful section `w` on cells of grade at most `K`, with no
finiteness of the cells, as `CellScheme.Rows.IsLawful.strongEncode` does for the strongly coded
encoder.  The existential `CellScheme.Rows.IsLawful.exists_bandEncode` of
`VaughtConjecture.Extension.CodedSection`, and the witness transfer `Label.IsWitness.bandEncode`
by which it is proved, are therefore to be replaced by this universal form, in that file or in
the consolidation; the uses of `exists_bandEncode` through `.choose` in
`VaughtConjecture.Extension.ApexLayer` can take `V := univ.image w`.

## Placement

The label statements belong in a `Label/Coding.lean` beside the band coding, and the lawfulness
statements in `VaughtConjecture.Scheme.Row`.  They are stated here so that those folders are
unchanged.  The band arithmetic they use is stated once, in
`VaughtConjecture.Extension.WitnessAlgebra`.

## References

The coding of rows below `ω ^ 2` is the range normalization of [Kni26, Lemma 2.5.13]; the strong
coding of the codes is proved here for this encoder.  Witnesses are [Kni26, Definition 2.3.9], and
visibility replacement is [Kni26, Definition 2.2.3].
-/

universe u

namespace VaughtConjecture.Label

open Finset Ordinal

/-! ### Spreading -/

open Classical in
/-- Spreading of an ordinal at `K`: `ω * b + n` goes to `ω * (ω * b) + n` if `n ≤ K`, and to
`ω * (ω * b + n) + (K + 1)` otherwise. -/
noncomputable def spreadOrd (K : ℕ) (o : Ordinal.{u}) : Ordinal.{u} :=
  if o % ω ≤ K then ω * (ω * (o / ω)) + o % ω else ω * (ω * (o / ω) + o % ω) + (K + 1 : ℕ)

open Classical in
/-- Unspreading of an ordinal at `K`: `ω * (ω * b + j) + x` goes to `ω * b + min x K` if `j = 0`
and to `ω * b + max j K` otherwise. -/
noncomputable def unspreadOrd (K : ℕ) (z : Ordinal.{u}) : Ordinal.{u} :=
  ω * (z / ω / ω) + if z / ω % ω = 0 then min (z % ω) K else max (z / ω % ω) K

/-- The **spreading** of labels at `K`: bottom and the formal top are fixed, and ordinals are
spread by `spreadOrd K`. -/
noncomputable def spread (K : ℕ) : Label.{u} → Label.{u} := WithBot.map (WithTop.map (spreadOrd K))

/-- The **unspreading** of labels at `K`: bottom and the formal top are fixed, and ordinals are
unspread by `unspreadOrd K`. -/
noncomputable def unspread (K : ℕ) : Label.{u} → Label.{u} :=
  WithBot.map (WithTop.map (unspreadOrd K))

variable {K k i : ℕ}

/-- The band index of a spread ordinal, as a natural number. -/
private def spreadBand (K n : ℕ) : ℕ := if n ≤ K then 0 else n

/-- The finite part of a spread ordinal. -/
private def spreadFin (K n : ℕ) : ℕ := if n ≤ K then n else K + 1

/-- Spreading of `ω * b + n`. -/
private theorem spreadOrd_omega0_mul_add (b : Ordinal.{u}) (n : ℕ) :
    spreadOrd K (ω * b + n) = ω * (ω * b + spreadBand K n) + spreadFin K n := by
  rw [spreadOrd, omega0_mul_add_natCast_div, omega0_mul_add_natCast_mod, spreadBand, spreadFin]
  by_cases h : n ≤ K
  · simp [h]
  · simp [h, show ¬ (n : Ordinal.{u}) ≤ K by exact_mod_cast h]

/-- The value of an unspread ordinal in its band, as a natural number. -/
private def unspreadFin (K j x : ℕ) : ℕ := if j = 0 then min x K else max j K

/-- Unspreading of `ω * (ω * b + j) + x`. -/
private theorem unspreadOrd_omega0_mul_add (b : Ordinal.{u}) (j x : ℕ) :
    unspreadOrd K (ω * (ω * b + j) + x) = ω * b + unspreadFin K j x := by
  rw [unspreadOrd, omega0_mul_add_natCast_div, omega0_mul_add_natCast_div,
    omega0_mul_add_natCast_mod, omega0_mul_add_natCast_mod, unspreadFin]
  by_cases h : j = 0
  · simp [h, Nat.mono_cast.map_min]
  · simp [h, Nat.mono_cast.map_max]

/-- Every ordinal is `ω * (ω * b + j) + x` for natural numbers `j` and `x`. -/
private theorem exists_eq_omega0_mul_omega0_mul_add (z : Ordinal.{u}) :
    ∃ (b : Ordinal.{u}) (j x : ℕ), z = ω * (ω * b + j) + x := by
  obtain ⟨c, x, rfl⟩ := exists_eq_omega0_mul_add_natCast z
  obtain ⟨b, j, rfl⟩ := exists_eq_omega0_mul_add_natCast c
  exact ⟨b, j, x, rfl⟩

/-- **Unspreading undoes spreading**, on ordinals. -/
private theorem unspreadOrd_spreadOrd (o : Ordinal.{u}) : unspreadOrd K (spreadOrd K o) = o := by
  obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
  rw [spreadOrd_omega0_mul_add, unspreadOrd_omega0_mul_add]
  congr 2
  simp only [unspreadFin, spreadBand, spreadFin]
  split_ifs <;> omega

/-- Spreading of ordinals is monotone. -/
private theorem spreadOrd_mono {o o' : Ordinal.{u}} (h : o ≤ o') :
    spreadOrd K o ≤ spreadOrd K o' := by
  obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
  obtain ⟨b', n', rfl⟩ := exists_eq_omega0_mul_add_natCast o'
  rw [spreadOrd_omega0_mul_add, spreadOrd_omega0_mul_add]
  rcases omega0_mul_add_natCast_le_iff.mp h with hb | ⟨rfl, hn⟩
  · exact (omega0_mul_add_natCast_lt (omega0_mul_add_natCast_lt hb _ _) _ _).le
  · refine omega0_mul_add_natCast_le_iff.mpr ?_
    simp only [spreadBand, spreadFin, add_right_inj, Nat.cast_inj]
    rcases (show spreadBand K n ≤ spreadBand K n' by simp only [spreadBand]; split_ifs <;> omega)
      |>.lt_or_eq with hlt | heq
    · exact .inl (add_lt_add_right (by exact_mod_cast hlt) _)
    · refine .inr ⟨by simpa [spreadBand] using heq, ?_⟩
      simp only [spreadBand] at heq
      split_ifs at heq ⊢ <;> omega

/-- Unspreading of ordinals is monotone. -/
private theorem unspreadOrd_mono {z z' : Ordinal.{u}} (h : z ≤ z') :
    unspreadOrd K z ≤ unspreadOrd K z' := by
  obtain ⟨b, j, x, rfl⟩ := exists_eq_omega0_mul_omega0_mul_add z
  obtain ⟨b', j', x', rfl⟩ := exists_eq_omega0_mul_omega0_mul_add z'
  rw [unspreadOrd_omega0_mul_add, unspreadOrd_omega0_mul_add]
  rcases omega0_mul_add_natCast_le_iff.mp h with hc | ⟨hc, hx⟩
  · rcases lt_or_ge (ω * b + j) (ω * b' + j') |>.resolve_right (not_le.mpr hc) with hc
    have hc' := (omega0_mul_add_natCast_le_iff (m := j) (n := j')).mp hc.le
    rcases hc' with hb | ⟨rfl, hj⟩
    · exact (omega0_mul_add_natCast_lt hb _ _).le
    · have hj' : j < j' := by exact_mod_cast (add_lt_add_iff_left _).mp hc
      exact omega0_mul_add_natCast_le_iff.mpr
        (.inr ⟨rfl, by simp only [unspreadFin]; split_ifs <;> omega⟩)
  · obtain ⟨rfl, rfl⟩ : b = b' ∧ j = j' := by
      have := (omega0_mul_add_natCast_le_iff (m := j) (n := j')).mp hc.le
      rcases this with hb | ⟨rfl, -⟩
      · exact absurd hc (omega0_mul_add_natCast_lt hb _ _).ne
      · exact ⟨rfl, by exact_mod_cast (add_right_inj _).mp hc⟩
    exact omega0_mul_add_natCast_le_iff.mpr
      (.inr ⟨rfl, by simp only [unspreadFin]; split_ifs <;> omega⟩)

/-- Spreading commutes with visibility replacement at every threshold `k ≤ K`, on ordinals. -/
private theorem spreadOrd_visibilityReplace (hk : k ≤ K) (hi : i ≤ k) (o : Ordinal.{u}) :
    spreadOrd K (Ordinal.visibilityReplace k i o) =
      Ordinal.visibilityReplace k i (spreadOrd K o) := by
  obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
  have hband : spreadBand K (if n < k then i else n) = spreadBand K n := by
    simp only [spreadBand]; split_ifs <;> omega
  have hfin : spreadFin K (if n < k then i else n) =
      if spreadFin K n < k then i else spreadFin K n := by
    simp only [spreadFin]; split_ifs <;> omega
  rw [visibilityReplace_omega0_mul_add_natCast, spreadOrd_omega0_mul_add, spreadOrd_omega0_mul_add,
    visibilityReplace_omega0_mul_add_natCast, hband, hfin]

/-- Unspreading commutes with visibility replacement at every threshold `k ≤ K`, on ordinals. -/
private theorem unspreadOrd_visibilityReplace (hk : k ≤ K) (hi : i ≤ k) (z : Ordinal.{u}) :
    unspreadOrd K (Ordinal.visibilityReplace k i z) =
      Ordinal.visibilityReplace k i (unspreadOrd K z) := by
  obtain ⟨b, j, x, rfl⟩ := exists_eq_omega0_mul_omega0_mul_add z
  rw [visibilityReplace_omega0_mul_add_natCast, unspreadOrd_omega0_mul_add,
    unspreadOrd_omega0_mul_add, visibilityReplace_omega0_mul_add_natCast]
  congr 2
  simp only [unspreadFin]
  split_ifs <;> omega

/-- Spreading fixes bottom. -/
@[simp] theorem spread_bot (K : ℕ) : spread K (⊥ : Label.{u}) = ⊥ := rfl

/-- Spreading fixes the formal top. -/
@[simp] theorem spread_top (K : ℕ) : spread K (⊤ : Label.{u}) = ⊤ := rfl

/-- Spreading of an ordinal label. -/
@[simp] theorem spread_coe (K : ℕ) (o : Ordinal.{u}) :
    spread K (o : Label.{u}) = (spreadOrd K o : Label.{u}) := rfl

/-- Unspreading fixes bottom. -/
@[simp] theorem unspread_bot (K : ℕ) : unspread K (⊥ : Label.{u}) = ⊥ := rfl

/-- Unspreading fixes the formal top. -/
@[simp] theorem unspread_top (K : ℕ) : unspread K (⊤ : Label.{u}) = ⊤ := rfl

/-- Unspreading of an ordinal label. -/
@[simp] theorem unspread_coe (K : ℕ) (z : Ordinal.{u}) :
    unspread K (z : Label.{u}) = (unspreadOrd K z : Label.{u}) := rfl

/-- **Unspreading undoes spreading.** -/
@[simp] theorem unspread_spread (K : ℕ) (x : Label.{u}) : unspread K (spread K x) = x := by
  induction x using recBotCoeTop <;> simp [unspreadOrd_spreadOrd]

/-- Spreading sends a label to bottom only if it is bottom. -/
@[simp] theorem spread_eq_bot_iff {x : Label.{u}} : spread K x = ⊥ ↔ x = ⊥ := by
  induction x using recBotCoeTop <;> simp

/-- Unspreading sends a label to bottom only if it is bottom. -/
@[simp] theorem unspread_eq_bot_iff {x : Label.{u}} : unspread K x = ⊥ ↔ x = ⊥ := by
  induction x using recBotCoeTop <;> simp

/-- Spreading is monotone. -/
theorem monotone_spread (K : ℕ) : Monotone (spread K : Label.{u} → Label.{u}) :=
  (Monotone.withTop_map fun _ _ ↦ spreadOrd_mono).withBot_map

/-- Unspreading is monotone. -/
theorem monotone_unspread (K : ℕ) : Monotone (unspread K : Label.{u} → Label.{u}) :=
  (Monotone.withTop_map fun _ _ ↦ unspreadOrd_mono).withBot_map

/-- A map on labels that fixes bottom, is monotone, sends only bottom to bottom, and commutes
with visibility replacement at every threshold `k ≤ K`, is a witness bounded by `K`. -/
private theorem isWitness_of_bot_reflecting {f : Label.{u} → Label.{u}} (hbot : f ⊥ = ⊥)
    (hmono : Monotone f) (hrefl : ∀ x, f x = ⊥ → x = ⊥)
    (hcomm : ∀ x, ∀ k ≤ K, ∀ i ≤ k, f (visibilityReplace k i x) = visibilityReplace k i (f x)) :
    IsWitness (stepSuppressor.{u} K) f where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := hbot
  monotone := hmono
  visibilityReplace_comm x k hx i hi := by
    by_cases hk : k ≤ K
    · exact hcomm x k hk i hi
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
      rw [hrefl x hx, visibilityReplace_bot, hbot, visibilityReplace_bot]

/-- **Spreading is a witness bounded by `K`.** -/
theorem isWitness_spread (K : ℕ) : IsWitness (stepSuppressor.{u} K) (spread K) :=
  isWitness_of_bot_reflecting rfl (monotone_spread K) (fun _ ↦ spread_eq_bot_iff.mp)
    fun x k hk i hi ↦ by
      induction x using recBotCoeTop <;> simp [spreadOrd_visibilityReplace hk hi]

/-- **Unspreading is a witness bounded by `K`.** -/
theorem isWitness_unspread (K : ℕ) : IsWitness (stepSuppressor.{u} K) (unspread K) :=
  isWitness_of_bot_reflecting rfl (monotone_unspread K) (fun _ ↦ unspread_eq_bot_iff.mp)
    fun x k hk i hi ↦ by
      induction x using recBotCoeTop <;> simp [unspreadOrd_visibilityReplace hk hi]

/-- The finite part of a spread ordinal is at most `K + 1`. -/
private theorem spreadOrd_mod_le (K : ℕ) (o : Ordinal.{u}) : spreadOrd K o % ω ≤ (K + 1 : ℕ) := by
  obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
  rw [spreadOrd_omega0_mul_add, omega0_mul_add_natCast_mod, Nat.cast_le, spreadFin]
  split_ifs <;> omega

/-- **A spread label is short at `K + 1`**: its finite part, if any, is at most `K + 1`.  It
need not be short at `K`. -/
theorem isShort_spread (K : ℕ) (x : Label.{u}) : IsShort (K + 1) (spread K x) := by
  induction x using recBotCoeTop with
  | bot => exact isShort_bot _
  | top => exact isShort_top _
  | coe o => exact isShort_coe.mpr (spreadOrd_mod_le K o)

/-! ### The band coding as a witness bounded by `K` -/

variable {V : Finset Label.{u}}

/-- **The band coding is a witness bounded by `K`**: it commutes with visibility replacement at
the thresholds `≤ K` and sends only bottom to bottom.  So `bandEncode V K ∘ w` is lawful for every
`V` and every lawful `w` on cells of grade at most `K`
(`CellScheme.Rows.IsLawful.map_of_bot_reflecting`). -/
theorem isWitness_bandEncode_stepSuppressor (V : Finset Label.{u}) (K : ℕ) :
    IsWitness (stepSuppressor.{u} K) (bandEncode V K) :=
  isWitness_of_bot_reflecting rfl monotone_bandEncode (fun _ ↦ bandEncode_eq_bot_iff.mp)
    fun x _ hk i _ ↦ bandEncode_visibilityReplace hk i x

/-- **The band decoding is a witness bounded by `K`**, for every `K`: the truncation at `K` of
the band decoding with the constant suppressor `⊤`. -/
theorem isWitness_bandDecode_stepSuppressor (V : Finset Label.{u}) (K : ℕ) :
    IsWitness (stepSuppressor.{u} K) (bandDecode V) :=
  isWitness_bandDecode.truncate K

/-- The number of code bands is at most twice the number of labels. -/
private theorem card_codeBands_le (V : Finset Label.{u}) : #(codeBands V) ≤ 2 * #V := by
  classical
  have hv : #(valueBands V) ≤ #V := by
    refine card_image_le.trans ?_
    rw [card_preimage]
    exact card_filter_le _ _
  calc #(codeBands V) ≤ #(valueBands V) + #((valueBands V).image Order.succ) := card_union_le _ _
    _ ≤ #(valueBands V) + #(valueBands V) := add_le_add_right card_image_le _
    _ ≤ 2 * #V := by omega

/-- The band code of a label short at `j ≥ K` lies in the coded alphabet with block bound the
number of code bands plus one and offset bound `j`. -/
private theorem bandEncode_mem_codedAlphabet {j : ℕ} (hK : K ≤ j) {x : Label.{u}}
    (hx : IsShort j x) :
    bandEncode V K x ∈ codedAlphabet (#(codeBands V) + 1) j := by
  induction x using recBotCoeTop with
  | bot => exact mem_codedAlphabet.mpr (.inl rfl)
  | top => exact mem_codedAlphabet.mpr (.inr ⟨_, le_rfl, K, hK, rfl⟩)
  | coe o =>
    have hfin : (if o / ω ∈ valueBands V then o % ω else (K : Ordinal.{u})) ≤ j := by
      split_ifs
      · exact isShort_coe.mp hx
      · exact_mod_cast hK
    obtain ⟨n, hn⟩ := lt_omega0.mp (hfin.trans_lt (natCast_lt_omega0 j))
    refine mem_codedAlphabet.mpr (.inr ⟨codeRank V (o / ω), (codeRank_le _).trans (by omega), n,
      by exact_mod_cast hn ▸ hfin, ?_⟩)
    rw [bandEncode_coe, bandEncodeOrd, hn]

/-! ### The strongly coded encoder and its decoder -/

/-- The **strongly coded encoder** relative to a finite set `V` of labels at grade `K`: spreading
at `K` followed by the band coding of the spread labels of `V`. -/
noncomputable def strongEncode (V : Finset Label.{u}) (K : ℕ) : Label.{u} → Label.{u} :=
  bandEncode (V.image (spread K)) K ∘ spread K

/-- The **strongly coded decoder** relative to `V` at grade `K`: the band decoding of the spread
labels of `V` followed by unspreading at `K`. -/
noncomputable def strongDecode (V : Finset Label.{u}) (K : ℕ) : Label.{u} → Label.{u} :=
  unspread K ∘ bandDecode (V.image (spread K))

/-- The encoder, applied. -/
theorem strongEncode_apply (x : Label.{u}) :
    strongEncode V K x = bandEncode (V.image (spread K)) K (spread K x) := rfl

/-- The decoder, applied. -/
theorem strongDecode_apply (x : Label.{u}) :
    strongDecode V K x = unspread K (bandDecode (V.image (spread K)) x) := rfl

/-- The encoder sends a label to bottom exactly when it is bottom. -/
@[simp] theorem strongEncode_eq_bot_iff {x : Label.{u}} : strongEncode V K x = ⊥ ↔ x = ⊥ := by
  simp [strongEncode_apply]

/-- The encoder is monotone. -/
theorem monotone_strongEncode : Monotone (strongEncode V K) :=
  monotone_bandEncode.comp (monotone_spread K)

/-- The decoder is monotone. -/
theorem monotone_strongDecode : Monotone (strongDecode V K) :=
  (monotone_unspread K).comp (isWitness_bandDecode_stepSuppressor _ K).monotone

/-- **The encoder is a witness bounded by `K`.**  Used by 2.5 and 2.6: the boundary labels
transform to their strongly coded representative, which is lawful. -/
theorem isWitness_strongEncode : IsWitness (stepSuppressor.{u} K) (strongEncode V K) :=
  (isWitness_spread K).comp_of_bot_reflecting (isWitness_bandEncode_stepSuppressor _ K)
    fun _ ↦ bandEncode_eq_bot_iff.mp

/-- **The decoder is a witness bounded by `K`.**  Used by 2.5 and 2.6: it is the decoder of the
section theorem, which realizes a catalogue vector as a lawful section. -/
theorem isWitness_strongDecode : IsWitness (stepSuppressor.{u} K) (strongDecode V K) :=
  (isWitness_bandDecode_stepSuppressor _ K).comp_of_bot_reflecting (isWitness_unspread K)
    fun _ ↦ unspread_eq_bot_iff.mp

/-- **Every code is strongly coded at `K`**: its finite part is at most `K + 1`.  It need not be
short at `K` (`VaughtConjecture.Extension.TransformationExamples`).  Used by 2.5 and 2.6: the row
of a new cell of grade `K` built from codes is strongly coded
(`CellScheme.Rows.IsStronglyCodedAt`), so it keeps the coding of the extended scheme. -/
theorem isStronglyCoded_strongEncode (x : Label.{u}) : IsStronglyCoded K (strongEncode V K x) := by
  have h := bandEncode_mem_codedAlphabet (V := V.image (spread K)) (Nat.le_succ K)
    (isShort_spread K x)
  rcases mem_codedAlphabet.mp h with h | ⟨a, -, b, hb, h⟩
  · exact .inl h
  · exact .inr ⟨a, b, hb, h⟩

/-- **The codes lie in one coded alphabet**, with block bound `2 * #V + 1` and offset bound
`K + 1`.  Used by 2.5 and 2.6: the catalogue at grade `K` is finite, its vectors taking values in
this alphabet (`Label.finite_setOf_isStronglyCoded_lt`). -/
theorem strongEncode_mem_codedAlphabet (x : Label.{u}) :
    strongEncode V K x ∈ codedAlphabet (2 * #V + 1) (K + 1) := by
  have hcard : #(codeBands (V.image (spread K))) + 1 ≤ 2 * #V + 1 :=
    Nat.succ_le_succ ((card_codeBands_le _).trans (Nat.mul_le_mul_left 2 card_image_le))
  rcases (isStronglyCoded_strongEncode (V := V) x) with h | ⟨a, b, hb, h⟩
  · exact mem_codedAlphabet.mpr (.inl h)
  · refine mem_codedAlphabet.mpr (.inr ⟨a, ?_, b, hb, h⟩)
    have hmem := bandEncode_mem_codedAlphabet (V := V.image (spread K)) (Nat.le_succ K)
      (isShort_spread K x)
    rw [← strongEncode_apply, h] at hmem
    rcases mem_codedAlphabet.mp hmem with h' | ⟨a', ha', b', -, h'⟩
    · exact absurd h' (by simp)
    · have he : (ω * a + b : Ordinal.{u}) = ω * a' + b' := WithTop.coe_injective
        (WithBot.coe_injective h')
      have ha : a = a' := by
        have := congrArg (· / ω) he
        simp only [omega0_mul_add_natCast_div] at this
        exact_mod_cast this
      omega

/-! #### Numerical decoding identities -/

/-- **The decoder reads back every label of `V`.** -/
theorem strongDecode_strongEncode {z : Label.{u}} (hz : z ∈ V) :
    strongDecode V K (strongEncode V K z) = z := by
  rw [strongDecode_apply, strongEncode_apply, bandDecode_bandEncode (mem_image_of_mem _ hz),
    unspread_spread]

/-- The encoder is injective on `V`: the decoder is a left inverse on `V`.  Used by 2.5 and 2.6
through `Label.forall_min_strongEncode_eq_iff`. -/
theorem injOn_strongEncode : Set.InjOn (strongEncode V K) V :=
  Set.LeftInvOn.injOn (f₁' := strongDecode V K) fun _ hx ↦ strongDecode_strongEncode hx

/-! #### Cap preservation -/

/-- **The code of a cap self-visible at `K` is self-visible at `K`**, since the encoder is a
witness bounded by `K`.  Used by 2.5 and 2.6: capping a lawful code section at the code of such a
cap keeps it lawful ([Kni26, Lemma 2.5.8], `CellScheme.Rows.IsLawful.min_const_of_isSelfVisible`),
and the capped code section decodes to the capped decoded section
(`Label.strongDecode_min_strongEncode`). -/
theorem isSelfVisible_strongEncode {c : Label.{u}} (hc : IsSelfVisible K c) :
    IsSelfVisible K (strongEncode V K c) :=
  isWitness_strongEncode.isSelfVisible_apply hc (by simp)

/-- **Capping commutes with decoding at the code of a cap of `V`**: for a cap `c` in `V`, the
decoded label of any code `x` capped at `c` is the decoded label of `x` capped at the code of `c`.
So `min (strongDecode V K x) c` is determined by `min x (strongEncode V K c)`.  This is numerical,
per coordinate, and separate from lawfulness.  Used by 2.6, cell by cell: a lift of the encoded
prescription capped at the code of a cap decodes to the decoded lift capped at the cap. -/
theorem strongDecode_min_strongEncode {c : Label.{u}} (hc : c ∈ V) (x : Label.{u}) :
    strongDecode V K (min x (strongEncode V K c)) = min (strongDecode V K x) c := by
  rw [monotone_strongDecode.map_min, strongDecode_strongEncode hc]

/-- **Capped agreement of codes decodes**, per coordinate: for a cap `c` in `V`, two codes that
agree capped at the code of `c` decode to labels that agree capped at `c`.  The caps preserved are
the labels of `V`; those used by 2.5 and 2.6 are moreover self-visible at the grade bound `K`,
and so are their codes (`Label.isSelfVisible_strongEncode`).  Used by 2.6, cell by cell: a lift
that agrees with the encoded ambient labelling at the code of a cap decodes to one that agrees
with the decoded ambient labelling at the cap. -/
theorem min_strongDecode_eq_min_strongDecode {x x' c : Label.{u}} (hc : c ∈ V)
    (h : min x' (strongEncode V K c) = min x (strongEncode V K c)) :
    min (strongDecode V K x') c = min (strongDecode V K x) c := by
  rw [← strongDecode_min_strongEncode hc, h, strongDecode_min_strongEncode hc]

/-- **Capped agreement is preserved and reflected by the encoder**, for labellings with values in
`V` and a cap in `V`.  Used by 2.5 and 2.6: an ambient labelling and a prescription that agree at
a cap are encoded to codes that agree at the code of the cap, and conversely. -/
theorem forall_min_strongEncode_eq_iff {D : Type*} {q q' : D → Label.{u}} {c : Label.{u}}
    (hq : ∀ d, q d ∈ V) (hq' : ∀ d, q' d ∈ V) (hc : c ∈ V) :
    (∀ d, min (strongEncode V K (q' d)) (strongEncode V K c) =
      min (strongEncode V K (q d)) (strongEncode V K c)) ↔ ∀ d, min (q' d) c = min (q d) c := by
  have hmin (x : Label.{u}) (hx : x ∈ V) : min x c ∈ V := by
    rcases min_choice x c with h | h <;> rw [h] <;> assumption
  simp only [← (monotone_strongEncode (V := V) (K := K)).map_min]
  exact forall_congr' fun d ↦ injOn_strongEncode.eq_iff (hmin _ (hq' d)) (hmin _ (hq d))

/-- **Capped agreement with a code decodes**: a code `x` that agrees with the code of a label `y`
of `V` capped at the code of a cap `c` in `V` decodes to a label that agrees with `y` capped at
`c`; the case of `Label.min_strongDecode_eq_min_strongDecode` in which the second code is read
back.  Used by 2.6, cell by cell: a lift of the encoded prescription at the code of a cap decodes
to a lift that preserves the ambient observation at the cap on every cell. -/
theorem min_strongDecode_eq_of_min_eq {x y c : Label.{u}} (hy : y ∈ V) (hc : c ∈ V)
    (h : min x (strongEncode V K c) = min (strongEncode V K y) (strongEncode V K c)) :
    min (strongDecode V K x) c = min y c := by
  rw [min_strongDecode_eq_min_strongDecode hc h, strongDecode_strongEncode hy]

end VaughtConjecture.Label

/-! ### Lawfulness along the encoder -/

namespace VaughtConjecture.CellScheme.Rows

open Label

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {p : ι → Label.{u}} {K : ℕ}
  {V : Finset Label.{u}}

/-- **The encoded section of a lawful section is lawful**, for every finite set `V` of labels,
when the grades are at most `K`, with no finiteness of the cells.  Used by 2.5 and 2.6: the
strongly coded representative of the boundary labels is lawful. -/
theorem IsLawful.strongEncode (hp : R.IsLawful p) (hK : ∀ d, D.grade d ≤ K) :
    R.IsLawful (Label.strongEncode V K ∘ p) :=
  hp.map_of_bot_reflecting hK isWitness_strongEncode fun _ ↦ strongEncode_eq_bot_iff.mp

end VaughtConjecture.CellScheme.Rows
