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
  (`Label.isWitness_bandEncode_stepSuppressor`, `Label.isWitness_bandDecode_stepSuppressor`).
* *Coding.*  Every code is strongly coded at `K` (`Label.isStronglyCoded_strongEncode`) and lies
  in the coded alphabet with block bound `2 * #V + 1` and offset bound `K + 1`
  (`Label.strongEncode_mem_codedAlphabet`); the formal top has a proper code.
* *Numerical decoding identities.*  The decoder reads back every label of `V`
  (`Label.strongDecode_strongEncode`); the encoder reflects the order and is injective on `V`
  (`Label.strongEncode_le_strongEncode_iff`, `Label.injOn_strongEncode`) and commutes with `min`
  (`Label.strongEncode_min`, `Label.strongDecode_min`).
* *Cap preservation.*  Capped agreement at a cap `c` in `V` is preserved and reflected by the
  encoder (`Label.forall_min_strongEncode_eq_iff`), and a code that agrees with the code of a
  label `y` of `V` capped at the code of `c` decodes to a label that agrees with `y` capped at `c`
  (`Label.min_strongDecode_eq_of_min_eq`).
* *Lawfulness* (`CellScheme.Rows.IsLawful.strongEncode`): the encoded section of a lawful
  section is lawful, for every `V`, since the encoder is a bottom-reflecting witness.  The
  decoder does not reflect bottom (it sends the codes below `ω` to bottom), so the lawfulness of a
  decoded section is the section theorem (`CellScheme.Rows.IsLawful.strongDecode`).

## Placement

The label statements belong in a `Label/Coding.lean` beside the band coding, and the lawfulness
statements in `VaughtConjecture.Scheme.Row`.  They are stated here so that those folders are
unchanged.

## References

The coding of rows below `ω ^ 2` is the range normalization of [Kni26, Lemma 2.5.13]; the strong
coding of the codes is proved here for this encoder.  Witnesses are [Kni26, Definition 2.3.9], and
visibility replacement is [Kni26, Definition 2.2.3].
-/

universe u

namespace VaughtConjecture.Label

open Finset Ordinal

/-! ### Ordinals as bands with finite parts -/

section Bands

variable {a a' b : Ordinal.{u}} {x x' n : ℕ}

/-- Every ordinal is `ω * b + n` for an ordinal `b` and a natural number `n`. -/
private theorem exists_eq_omega0_mul_add (o : Ordinal.{u}) :
    ∃ (b : Ordinal.{u}) (n : ℕ), o = ω * b + n := by
  obtain ⟨n, hn⟩ := lt_omega0.mp (mod_lt o omega0_ne_zero)
  exact ⟨o / ω, n, by rw [← hn, div_add_mod]⟩

/-- The band of `ω * b + n`. -/
private theorem omega0_mul_add_div (b : Ordinal.{u}) (n : ℕ) : (ω * b + n) / ω = b := by
  rw [mul_add_div _ omega0_ne_zero, div_eq_zero_of_lt (natCast_lt_omega0 n), add_zero]

/-- The finite part of `ω * b + n`. -/
private theorem omega0_mul_add_mod (b : Ordinal.{u}) (n : ℕ) : (ω * b + n) % ω = n := by
  rw [mul_add_mod_self, natCast_mod_omega0]

/-- A lower band lies below a higher band. -/
private theorem omega0_mul_add_lt (h : a < a') (x : ℕ) (y : Ordinal.{u}) :
    ω * a + x < ω * a' + y :=
  calc ω * a + x < ω * a + ω := add_lt_add_right (natCast_lt_omega0 x) _
    _ = ω * Order.succ a := (mul_succ _ _).symm
    _ ≤ ω * a' := by gcongr; exact Order.succ_le_of_lt h
    _ ≤ ω * a' + y := le_self_add

/-- Ordinals compare lexicographically in band and finite part. -/
private theorem omega0_mul_add_le_iff :
    ω * a + x ≤ ω * a' + x' ↔ a < a' ∨ a = a' ∧ x ≤ x' := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases lt_trichotomy a a' with hlt | rfl | hgt
    · exact .inl hlt
    · exact .inr ⟨rfl, by exact_mod_cast (add_le_add_iff_left _).mp h⟩
    · exact absurd h (not_le.mpr (omega0_mul_add_lt hgt x' _))
  · rintro (h | ⟨rfl, h⟩)
    · exact (omega0_mul_add_lt h x _).le
    · exact add_le_add_right (by exact_mod_cast h) _

/-- Visibility replacement of `ω * b + n` replaces the natural number `n`. -/
private theorem visibilityReplace_omega0_mul_add (b : Ordinal.{u}) (k i n : ℕ) :
    Ordinal.visibilityReplace k i (ω * b + n) = ω * b + ((if n < k then i else n : ℕ) :
      Ordinal.{u}) := by
  rw [Ordinal.visibilityReplace, omega0_mul_add_div, omega0_mul_add_mod]
  split_ifs <;> simp_all

end Bands

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
  rw [spreadOrd, omega0_mul_add_div, omega0_mul_add_mod, spreadBand, spreadFin]
  by_cases h : n ≤ K
  · simp [h]
  · simp [h, show ¬ (n : Ordinal.{u}) ≤ K by exact_mod_cast h]

/-- The value of an unspread ordinal in its band, as a natural number. -/
private def unspreadFin (K j x : ℕ) : ℕ := if j = 0 then min x K else max j K

/-- Unspreading of `ω * (ω * b + j) + x`. -/
private theorem unspreadOrd_omega0_mul_add (b : Ordinal.{u}) (j x : ℕ) :
    unspreadOrd K (ω * (ω * b + j) + x) = ω * b + unspreadFin K j x := by
  rw [unspreadOrd, omega0_mul_add_div, omega0_mul_add_div, omega0_mul_add_mod,
    omega0_mul_add_mod, unspreadFin]
  by_cases h : j = 0
  · simp [h, Nat.mono_cast.map_min]
  · simp [h, Nat.mono_cast.map_max]

/-- Every ordinal is `ω * (ω * b + j) + x` for natural numbers `j` and `x`. -/
private theorem exists_eq_omega0_mul_omega0_mul_add (z : Ordinal.{u}) :
    ∃ (b : Ordinal.{u}) (j x : ℕ), z = ω * (ω * b + j) + x := by
  obtain ⟨c, x, rfl⟩ := exists_eq_omega0_mul_add z
  obtain ⟨b, j, rfl⟩ := exists_eq_omega0_mul_add c
  exact ⟨b, j, x, rfl⟩

/-- **Unspreading undoes spreading**, on ordinals. -/
private theorem unspreadOrd_spreadOrd (o : Ordinal.{u}) : unspreadOrd K (spreadOrd K o) = o := by
  obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add o
  rw [spreadOrd_omega0_mul_add, unspreadOrd_omega0_mul_add]
  congr 2
  simp only [unspreadFin, spreadBand, spreadFin]
  split_ifs <;> omega

/-- Spreading of ordinals is monotone. -/
private theorem spreadOrd_mono {o o' : Ordinal.{u}} (h : o ≤ o') :
    spreadOrd K o ≤ spreadOrd K o' := by
  obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add o
  obtain ⟨b', n', rfl⟩ := exists_eq_omega0_mul_add o'
  rw [spreadOrd_omega0_mul_add, spreadOrd_omega0_mul_add]
  rcases omega0_mul_add_le_iff.mp h with hb | ⟨rfl, hn⟩
  · exact (omega0_mul_add_lt (omega0_mul_add_lt hb _ _) _ _).le
  · refine omega0_mul_add_le_iff.mpr ?_
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
  rcases omega0_mul_add_le_iff.mp h with hc | ⟨hc, hx⟩
  · rcases lt_or_ge (ω * b + j) (ω * b' + j') |>.resolve_right (not_le.mpr hc) with hc
    have hc' := (omega0_mul_add_le_iff (x := j) (x' := j')).mp hc.le
    rcases hc' with hb | ⟨rfl, hj⟩
    · exact (omega0_mul_add_lt hb _ _).le
    · have hj' : j < j' := by exact_mod_cast (add_lt_add_iff_left _).mp hc
      exact omega0_mul_add_le_iff.mpr (.inr ⟨rfl, by simp only [unspreadFin]; split_ifs <;> omega⟩)
  · obtain ⟨rfl, rfl⟩ : b = b' ∧ j = j' := by
      have := (omega0_mul_add_le_iff (x := j) (x' := j')).mp hc.le
      rcases this with hb | ⟨rfl, -⟩
      · exact absurd hc (omega0_mul_add_lt hb _ _).ne
      · exact ⟨rfl, by exact_mod_cast (add_right_inj _).mp hc⟩
    exact omega0_mul_add_le_iff.mpr (.inr ⟨rfl, by simp only [unspreadFin]; split_ifs <;> omega⟩)

/-- Spreading commutes with visibility replacement at every threshold `k ≤ K`, on ordinals. -/
private theorem spreadOrd_visibilityReplace (hk : k ≤ K) (hi : i ≤ k) (o : Ordinal.{u}) :
    spreadOrd K (Ordinal.visibilityReplace k i o) =
      Ordinal.visibilityReplace k i (spreadOrd K o) := by
  obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add o
  have hband : spreadBand K (if n < k then i else n) = spreadBand K n := by
    simp only [spreadBand]; split_ifs <;> omega
  have hfin : spreadFin K (if n < k then i else n) =
      if spreadFin K n < k then i else spreadFin K n := by
    simp only [spreadFin]; split_ifs <;> omega
  rw [visibilityReplace_omega0_mul_add, spreadOrd_omega0_mul_add, spreadOrd_omega0_mul_add,
    visibilityReplace_omega0_mul_add, hband, hfin]

/-- Unspreading commutes with visibility replacement at every threshold `k ≤ K`, on ordinals. -/
private theorem unspreadOrd_visibilityReplace (hk : k ≤ K) (hi : i ≤ k) (z : Ordinal.{u}) :
    unspreadOrd K (Ordinal.visibilityReplace k i z) =
      Ordinal.visibilityReplace k i (unspreadOrd K z) := by
  obtain ⟨b, j, x, rfl⟩ := exists_eq_omega0_mul_omega0_mul_add z
  rw [visibilityReplace_omega0_mul_add, unspreadOrd_omega0_mul_add, unspreadOrd_omega0_mul_add,
    visibilityReplace_omega0_mul_add]
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
  obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add o
  rw [spreadOrd_omega0_mul_add, omega0_mul_add_mod, Nat.cast_le, spreadFin]
  split_ifs <;> omega

/-- Every ordinal label that is a spread label has finite part at most `K + 1`. -/
private theorem mod_le_of_coe_eq_spread {o : Ordinal.{u}} {x : Label.{u}}
    (h : (o : Label.{u}) = spread K x) : o % ω ≤ (K + 1 : ℕ) := by
  induction x using recBotCoeTop with
  | bot => exact absurd h (by simp)
  | top => exact absurd h (by simp)
  | coe o' =>
    rw [WithTop.coe_injective (WithBot.coe_injective h)]
    exact spreadOrd_mod_le K o'

/-! ### The band coding as a witness bounded by `K` -/

variable {V : Finset Label.{u}}

/-- **The band coding is a witness bounded by `K`**: it commutes with visibility replacement at
the thresholds `≤ K` and sends only bottom to bottom. -/
theorem isWitness_bandEncode_stepSuppressor (V : Finset Label.{u}) (K : ℕ) :
    IsWitness (stepSuppressor.{u} K) (bandEncode V K) :=
  isWitness_of_bot_reflecting rfl monotone_bandEncode (fun _ ↦ bandEncode_eq_bot_iff.mp)
    fun x _ hk i _ ↦ bandEncode_visibilityReplace hk i x

/-- **The band decoding is a witness bounded by `K`**, for every `K`. -/
theorem isWitness_bandDecode_stepSuppressor (V : Finset Label.{u}) (K : ℕ) :
    IsWitness (stepSuppressor.{u} K) (bandDecode V) :=
  isWitness_bandDecode.of_le (fun _ ↦ le_top) (IsWitness.id_step K).antitone
    (IsWitness.id_step K).isSelfVisible

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

/-- A band code whose ordinal argument has finite part at most `j ≥ K` lies in the coded alphabet
with block bound the number of code bands plus one and offset bound `j`. -/
private theorem bandEncode_mem_codedAlphabet {j : ℕ} (hK : K ≤ j) {x : Label.{u}}
    (hx : ∀ o : Ordinal.{u}, (o : Label.{u}) = x → o % ω ≤ j) :
    bandEncode V K x ∈ codedAlphabet (#(codeBands V) + 1) j := by
  induction x using recBotCoeTop with
  | bot => exact mem_codedAlphabet.mpr (.inl rfl)
  | top => exact mem_codedAlphabet.mpr (.inr ⟨_, le_rfl, K, hK, rfl⟩)
  | coe o =>
    have hfin : (if o / ω ∈ valueBands V then o % ω else (K : Ordinal.{u})) ≤ j := by
      split_ifs
      · exact hx o rfl
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

/-- **Every code is strongly coded at `K`.**  Used by 2.5 and 2.6: the row of a new cell of grade
`K` built from codes is strongly coded (`CellScheme.Rows.IsStronglyCodedAt`), so it keeps the
coding of the extended scheme. -/
theorem isStronglyCoded_strongEncode (x : Label.{u}) : IsStronglyCoded K (strongEncode V K x) := by
  have h := bandEncode_mem_codedAlphabet (V := V.image (spread K)) (Nat.le_succ K)
    (x := spread K x) fun _ ho ↦ mod_le_of_coe_eq_spread ho
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
      (x := spread K x) fun _ ho ↦ mod_le_of_coe_eq_spread ho
    rw [← strongEncode_apply, h] at hmem
    rcases mem_codedAlphabet.mp hmem with h' | ⟨a', ha', b', -, h'⟩
    · exact absurd h' (by simp)
    · have he : (ω * a + b : Ordinal.{u}) = ω * a' + b' := WithTop.coe_injective
        (WithBot.coe_injective h')
      have ha : a = a' := by
        have := congrArg (· / ω) he
        simp only [omega0_mul_add_div] at this
        exact_mod_cast this
      omega

/-! #### Numerical decoding identities -/

/-- **The decoder reads back every label of `V`.** -/
theorem strongDecode_strongEncode {z : Label.{u}} (hz : z ∈ V) :
    strongDecode V K (strongEncode V K z) = z := by
  rw [strongDecode_apply, strongEncode_apply, bandDecode_bandEncode (mem_image_of_mem _ hz),
    unspread_spread]

/-- The encoder reflects the order of the labels of `V`. -/
theorem strongEncode_le_strongEncode_iff {x y : Label.{u}} (hx : x ∈ V) (hy : y ∈ V) :
    strongEncode V K x ≤ strongEncode V K y ↔ x ≤ y :=
  ⟨fun h ↦ strongDecode_strongEncode (K := K) hx ▸ strongDecode_strongEncode (K := K) hy ▸
    monotone_strongDecode h, fun h ↦ monotone_strongEncode h⟩

/-- The encoder is injective on `V`. -/
theorem injOn_strongEncode : Set.InjOn (strongEncode V K) V := fun x hx y hy h ↦ by
  rw [← strongDecode_strongEncode (K := K) hx, ← strongDecode_strongEncode (K := K) hy, h]

/-- The encoder commutes with `min`. -/
theorem strongEncode_min (x y : Label.{u}) :
    strongEncode V K (min x y) = min (strongEncode V K x) (strongEncode V K y) :=
  monotone_strongEncode.map_min

/-- The decoder commutes with `min`. -/
theorem strongDecode_min (x y : Label.{u}) :
    strongDecode V K (min x y) = min (strongDecode V K x) (strongDecode V K y) :=
  monotone_strongDecode.map_min

/-! #### Cap preservation -/

/-- **Capped agreement is preserved and reflected by the encoder**, for labellings with values in
`V` and a cap in `V`.  Used by 2.5 and 2.6: an ambient labelling and a prescription that agree at
a cap are encoded to codes that agree at the code of the cap, and conversely. -/
theorem forall_min_strongEncode_eq_iff {D : Type*} {q q' : D → Label.{u}} {c : Label.{u}}
    (hq : ∀ d, q d ∈ V) (hq' : ∀ d, q' d ∈ V) (hc : c ∈ V) :
    (∀ d, min (strongEncode V K (q' d)) (strongEncode V K c) =
      min (strongEncode V K (q d)) (strongEncode V K c)) ↔ ∀ d, min (q' d) c = min (q d) c := by
  have hmin (x : Label.{u}) (hx : x ∈ V) : min x c ∈ V := by
    rcases min_choice x c with h | h <;> rw [h] <;> assumption
  simp only [← strongEncode_min]
  exact forall_congr' fun d ↦ injOn_strongEncode.eq_iff (hmin _ (hq' d)) (hmin _ (hq d))

/-- **Capped agreement decodes**: a code `x` that agrees with the code of a label `y` of `V`
capped at the code of a cap `c` in `V` decodes to a label that agrees with `y` capped at `c`.
Used by 2.6, cell by cell: a lift of the encoded prescription at the code of a cap decodes to a
lift that preserves the ambient observation at the cap on every cell. -/
theorem min_strongDecode_eq_of_min_eq {x y c : Label.{u}} (hy : y ∈ V) (hc : c ∈ V)
    (h : min x (strongEncode V K c) = min (strongEncode V K y) (strongEncode V K c)) :
    min (strongDecode V K x) c = min y c := by
  have := congrArg (strongDecode V K) h
  rwa [strongDecode_min, strongDecode_min, strongDecode_strongEncode hc,
    strongDecode_strongEncode hy] at this

end VaughtConjecture.Label

/-! ### Lawfulness along the encoder and the decoder -/

namespace VaughtConjecture.CellScheme.Rows

open Label

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {p : ι → Label.{u}} {K : ℕ}
  {V : Finset Label.{u}}

/-- **The encoded section of a lawful section is lawful**, for every finite set `V` of labels,
when the grades are at most `K`.  Used by 2.5 and 2.6: the strongly coded representative of the
boundary labels is lawful. -/
theorem IsLawful.strongEncode (hp : R.IsLawful p) (hK : ∀ d, D.grade d ≤ K) :
    R.IsLawful (Label.strongEncode V K ∘ p) :=
  hp.map_of_bot_reflecting hK isWitness_strongEncode fun _ ↦ strongEncode_eq_bot_iff.mp

/-- **The decoded section of a lawful section is lawful** when every owner is short or satisfies
its mapped locality: the section theorem with the decoder, a witness bounded by `K`.  Used by
2.5 and 2.6: a catalogue vector realized as a lawful section decodes to a lawful section. -/
theorem IsLawful.strongDecode (hp : R.IsLawful p) (hK : ∀ d, D.grade d ≤ K)
    (howner : ∀ s, (∀ t, IsShort (D.grade s) (R.row s t)) ∨
      TransformsTo (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (R.row s)
        (fun d ↦ min (Label.strongDecode V K (p d)) (Label.strongDecode V K (p s)))) :
    R.IsLawful (Label.strongDecode V K ∘ p) :=
  hp.map_of_isShort_or hK isWitness_strongDecode howner

end VaughtConjecture.CellScheme.Rows
