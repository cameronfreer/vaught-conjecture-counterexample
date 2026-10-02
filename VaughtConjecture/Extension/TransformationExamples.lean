/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.NormalForm
import VaughtConjecture.Extension.OwnerwiseDecoding
import VaughtConjecture.Geometry.IntervalPlan

/-!
# Examples: strongly coded normal forms, encoder round trips, composition, and decoding

Roadmap, Layer 3, 3.1, row 6, checkpoint 2.3 (transformation algebra, normal forms, coded
encoders); semantic contract, item 3.

* **A strongly coded normal form.**  On the cell scheme with one cell of scope `{0}` and grade
  `1` whose row takes the value `3` (the cell of `pointRow 3` in
  `VaughtConjecture.Extension.CodingExamples`), the section with label `3` is lawful and not
  strongly coded at grade `1`, since `3 > 1 + 1`; it has a lawful normal form strongly coded at
  grade `1` that transforms to it and back, and a witness bounded by grade `1` (a value map that is
  a witness with the suppressor that is the formal top at grades `≤ 1` and bottom above, whatever
  its values) decodes it (`exists_stronglyCoded_pointSection`).
* **Strongly coded, not short.**  At grade `1` the code of the label `3` relative to `{3}` has
  finite part `2`: it is strongly coded at `1` but not short at `1`
  (`isStronglyCoded_and_not_isShort_strongEncode`).  So the normal forms are not short at their
  grade, and the shortness branch of the section theorem does not apply to a row built from them
  by itself.
* **An encoder round trip.**  For `V = {3, ω + 5, ω + 7, ⊤}` at grade `1`, the decoder recovers
  each label, the codes are strongly coded at grade `1` although the labels `3`, `ω + 5`, and
  `ω + 7` are not, and the two labels `ω + 5 < ω + 7` of one block keep distinct, ordered codes
  (`strongEncode_roundTrip`).
* **Composition needs bottom reflection only off the short labels.**  Stage reduction to stage `1`
  and the block decoding for `{0}` are witnesses bounded by grade `0`, and the block decoding sends
  the value `0` of the first to bottom although `0` is not bottom, so the hypothesis of
  `Label.IsWitness.comp_of_bot_reflecting` fails; their composite is not a witness bounded by grade
  `0` (`not_isWitness_blockDecode_comp_reduce`), while `Label.IsWitness.exists_eq_comp_of_isShort`
  gives a witness bounded by grade `0` equal to the composite at every label short at `0`
  (`exists_eq_blockDecode_comp_reduce`).
* **A lawful section whose decoding is not lawful.**  On two cells `a`, `b` of grade `1` and one
  scope, with rows `(1, 1)` for `a` and `(1, 2)` for `b`, the section `(1, ω * 5 + 1)` is lawful
  (`isLawful_pairSection`).  The decoder does not reflect bottom: relative to the empty set of
  labels it sends `1` to bottom (`strongDecode_empty_one`), so the section decodes to `(⊥, ⊤)`,
  which is not lawful, since `(1, 2)` does not transform to `(⊥, ⊤)` at grade `1`; the unconditional
  decoding claim fails (`not_isLawful_strongDecode_pairSection`).  On the same rows, relative to the
  labels of the section, the decoded normal form is the section itself and is lawful by ownerwise
  decoding, `a` a new owner with a short row and `b` an inherited owner below which the decoded
  labels are those of the section (`isLawful_strongDecode_strongEncode_pairSection`): the failure of
  bottom reflection alone does not establish the failure of lawful decoding.

## References

Witnesses are [Kni26, Definition 2.3.9]; the range normalization of rows below `ω ^ 2` is that of
[Kni26, Lemma 2.5.13], and the strong coding of the normal forms is proved in this library.
-/

universe u

namespace VaughtConjecture

open Finset CellScheme Label
open scoped Ordinal

namespace TransformationExamples

/-! ### A strongly coded normal form -/

/-- The cell scheme with one cell of scope `{0}` and grade `1`. -/
private def pointScheme : CellScheme (Fin 1) (Fin 1) :=
  ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, fun _ ↦ 1⟩

/-- The rows of `pointScheme` with value `3`, the rows of `pointRow 3`. -/
private def pointRows : pointScheme.Rows.{u} := ⟨fun _ _ ↦ 3⟩

/-- The section of `pointScheme` with label `3` is lawful for the rows with value `3`. -/
private theorem isLawful_pointSection : pointRows.{u}.IsLawful fun _ ↦ (3 : Label.{u}) where
  orderly _ := by simp [pointScheme]
  locality _ := by
    simp only [min_self]
    exact TransformsTo.refl _ _
  availability _ t _ _ := ⟨t, rfl, le_rfl⟩

/-- **A strongly coded normal form of a section that is not strongly coded.**  The label `3` is
not strongly coded at grade `1`; the lawful section with label `3` has a lawful normal form
strongly coded at grade `1`, transforming to it and back, and decoded by a witness bounded by grade
`1`. -/
private theorem exists_stronglyCoded_pointSection :
    ¬ IsStronglyCoded 1 (3 : Label.{u}) ∧
      ∃ w' : Fin 1 → Label.{u}, pointRows.IsLawful w' ∧ (∀ d, IsStronglyCoded 1 (w' d)) ∧
        TransformsTo pointScheme.grade (fun _ ↦ 3) w' ∧
        TransformsTo pointScheme.grade w' (fun _ ↦ 3) ∧
        ∃ ν, IsWitness (stepSuppressor 1) ν ∧ ∀ d, ν (w' d) = 3 := by
  refine ⟨by simp, ?_⟩
  obtain ⟨w', hl, hs, -, h₁, h₂, ν, hν, hd⟩ :=
    isLawful_pointSection.exists_stronglyCoded (K := 1) fun _ ↦ le_rfl
  exact ⟨w', hl, hs, h₁, h₂, ν, hν, hd⟩

/-! ### A code that is strongly coded but not short -/

/-- **A code that is strongly coded but not short.**  At grade `1`, the code of the label `3`
relative to `{3}` is `ω * r + 2` for some `r`: its finite part `2 = 1 + 1` makes it strongly coded
at `1` and not short at `1`. -/
private theorem isStronglyCoded_and_not_isShort_strongEncode :
    IsStronglyCoded 1 (strongEncode ({3} : Finset Label.{u}) 1 3) ∧
      ¬ IsShort 1 (strongEncode ({3} : Finset Label.{u}) 1 3) := by
  refine ⟨isStronglyCoded_strongEncode _, fun h ↦ ?_⟩
  have h3 : (3 : Ordinal.{u}) = ((3 : ℕ) : Ordinal.{u}) := by norm_cast
  -- Spreading at `1` sends `3 = ω * 0 + 3` to `ω * (ω * 0 + 3) + 2 = ω * 3 + 2`.
  have hs : spreadOrd 1 (3 : Ordinal.{u}) = ω * 3 + (2 : ℕ) := by
    have h1 : (3 : Ordinal.{u}) % ω = 3 := by rw [h3, Ordinal.natCast_mod_omega0]
    have h2 : (3 : Ordinal.{u}) / ω = 0 :=
      Ordinal.div_eq_zero_of_lt (h3 ▸ Ordinal.natCast_lt_omega0 3)
    rw [spreadOrd, h1, h2, ite_eq_right (by rw [h3]; exact_mod_cast (by decide : ¬ 3 ≤ 1))]
    simp
  have he : (3 : Label.{u}) = ((3 : Ordinal.{u}) : Label.{u}) := rfl
  rw [strongEncode_apply, image_singleton, he, spread_coe, hs, blockEncode_coe] at h
  -- The block `3` of `ω * 3 + 2` is a value block, so the block coding keeps the finite part `2`.
  have hv : (ω * 3 + (2 : ℕ) : Ordinal.{u}) / ω ∈
      valueBlocks ({((ω * 3 + (2 : ℕ) : Ordinal.{u}) : Label.{u})} : Finset Label.{u}) :=
    div_mem_valueBlocks (by simp)
  have := isShort_coe.mp h
  rw [blockEncodeOrd, ite_eq_left hv, omega0_mul_add_natCast_mod, omega0_mul_add_natCast_mod]
    at this
  exact absurd this (by exact_mod_cast (by decide : ¬ 2 ≤ 1))

/-! ### An encoder round trip -/

/-- The label `ω · 1 + j`. -/
private noncomputable abbrev omega0Add (j : ℕ) : Label.{u} :=
  ((ω * (1 : ℕ) + (j : ℕ) : Ordinal.{u}) : Label.{u})

/-- The labels `3`, `ω + 5`, `ω + 7`, and `⊤`. -/
private noncomputable abbrev roundTripSet : Finset Label.{u} :=
  {3, omega0Add 5, omega0Add 7, ⊤}

/-- The encoder reflects the order of the labels of `V`, since the decoder recovers them. -/
private theorem strongEncode_le_strongEncode_iff {V : Finset Label.{u}} {K : ℕ} {x y : Label.{u}}
    (hx : x ∈ V) (hy : y ∈ V) : strongEncode V K x ≤ strongEncode V K y ↔ x ≤ y :=
  ⟨fun h ↦ strongDecode_strongEncode (K := K) hx ▸ strongDecode_strongEncode (K := K) hy ▸
    monotone_strongDecode h, fun h ↦ monotone_strongEncode h⟩

/-- `ω + 5 < ω + 7`. -/
private theorem omega0Add_five_lt_seven : omega0Add.{u} 5 < omega0Add 7 :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (add_lt_add_right (by exact_mod_cast
    (by decide : 5 < 7)) _))

/-- **An encoder round trip.**  For `V = {3, ω + 5, ω + 7, ⊤}` at grade `1`: the labels `3`,
`ω + 5`, and `ω + 7` are not strongly coded at grade `1`, but their codes and the code of `⊤` are;
the decoder recovers every label of `V`; and the codes of `ω + 5 < ω + 7`, in one block, are
ordered strictly. -/
private theorem strongEncode_roundTrip :
    (¬ IsStronglyCoded 1 (3 : Label.{u}) ∧ ¬ IsStronglyCoded 1 (omega0Add.{u} 5) ∧
      ¬ IsStronglyCoded 1 (omega0Add.{u} 7)) ∧
    (∀ x ∈ roundTripSet.{u}, IsStronglyCoded 1 (strongEncode roundTripSet 1 x)) ∧
    (∀ x ∈ roundTripSet.{u}, strongDecode roundTripSet 1 (strongEncode roundTripSet 1 x) = x) ∧
    strongEncode roundTripSet 1 (omega0Add.{u} 5) < strongEncode roundTripSet 1 (omega0Add 7) := by
  refine ⟨⟨by simp, fun h ↦ ?_, fun h ↦ ?_⟩, fun x _ ↦ isStronglyCoded_strongEncode x,
    fun x hx ↦ strongDecode_strongEncode hx, ?_⟩
  · exact absurd ((isStronglyCoded_coe_omega0_mul_add 1 1 5).mp h) (by decide)
  · exact absurd ((isStronglyCoded_coe_omega0_mul_add 1 1 7).mp h) (by decide)
  · have h5 : omega0Add.{u} 5 ∈ roundTripSet.{u} := by simp
    have h7 : omega0Add.{u} 7 ∈ roundTripSet.{u} := by simp
    exact lt_of_le_of_ne ((strongEncode_le_strongEncode_iff h5 h7).mpr omega0Add_five_lt_seven.le)
      fun h ↦ omega0Add_five_lt_seven.ne (injOn_strongEncode h5 h7 h)

/-! ### Composition without bottom reflection -/

/-- Visibility replacement at threshold `0` fixes every label. -/
private theorem visibilityReplace_zero_zero (x : Label.{u}) : visibilityReplace 0 0 x = x :=
  IsSelfVisible.visibilityReplace_eq (by
    induction x using recBotCoeTop <;> simp) 0

/-- Stage reduction to stage `1` is a witness bounded by grade `0`: it keeps `⊥` and `0` and sends
every other label to the formal top. -/
private theorem isWitness_reduce_one : IsWitness (stepSuppressor.{u} 0) (Label.reduce 1) where
  antitone := (IsWitness.id_step 0).antitone
  isSelfVisible := (IsWitness.id_step 0).isSelfVisible
  map_bot := reduce_bot
  monotone := monotone_reduce 1
  visibilityReplace_comm x k hx i hi := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · obtain rfl : i = 0 := Nat.le_zero.mp hi
      rw [visibilityReplace_zero_zero, visibilityReplace_zero_zero]
    · rw [stepSuppressor_of_lt hk, le_bot_iff, reduce_eq_bot_iff] at hx
      rw [hx, visibilityReplace_bot, reduce_bot, visibilityReplace_bot]

/-- The block decoding for `{0}` is a witness bounded by grade `0`. -/
private theorem isWitness_blockDecode_zero :
    IsWitness (stepSuppressor.{u} 0) (blockDecode {(0 : Label.{u})}) :=
  isWitness_blockDecode_stepSuppressor _ 0

/-- Stage reduction to stage `1` keeps ordinal zero. -/
private theorem reduce_one_zero : Label.reduce 1 (0 : Label.{u}) = 0 :=
  reduce_of_lt (by exact_mod_cast (zero_lt_one : (0 : Ordinal.{u}) < 1))

/-- The block decoding for `{0}` sends ordinal zero to bottom. -/
private theorem blockDecode_zero : blockDecode {(0 : Label.{u})} (0 : Label.{u}) = ⊥ :=
  blockDecodeOrd_of_eq_zero (by simp)

/-- **The hypothesis of guarded composition fails**: the block decoding for `{0}` sends the value
`0` of stage reduction to stage `1` to bottom, and `0` is not bottom. -/
private theorem not_bot_reflecting :
    blockDecode {(0 : Label.{u})} (Label.reduce 1 0) = ⊥ ∧ Label.reduce 1 (0 : Label.{u}) ≠ ⊥ := by
  rw [reduce_one_zero, blockDecode_zero]
  exact ⟨rfl, by simp⟩

/-- **Without bottom reflection the composite is not a witness**: at threshold `1` the guard holds
at `0`, whose image is bottom, but the replacement `1` of `0` goes to the formal top. -/
private theorem not_isWitness_blockDecode_comp_reduce :
    ¬ IsWitness (stepSuppressor.{u} 0) (blockDecode {(0 : Label.{u})} ∘ Label.reduce 1) := by
  intro h
  have h0 : (blockDecode {(0 : Label.{u})} ∘ Label.reduce 1) 0 = ⊥ := not_bot_reflecting.1
  have h1 := h.visibilityReplace_comm 0 1 (h0 ▸ bot_le) 1 le_rfl
  rw [h0, visibilityReplace_bot, visibilityReplace_zero, ite_eq_left one_pos, Function.comp_apply,
    reduce_of_le (by simp), blockDecode_top] at h1
  exact top_ne_bot h1

/-- **The composition on short labels needs no bottom reflection**: some witness bounded by grade
`0` agrees with the block decoding for `{0}` after stage reduction to stage `1` at every label short
at `0`. -/
private theorem exists_eq_blockDecode_comp_reduce :
    ∃ ρ, IsWitness (stepSuppressor.{u} 0) ρ ∧
      ∀ x, IsShort 0 x → ρ x = blockDecode {(0 : Label.{u})} (Label.reduce 1 x) :=
  isWitness_reduce_one.exists_eq_comp_of_isShort isWitness_blockDecode_zero le_rfl


/-! ### A lawful section whose decoding is not lawful -/

/-- The cell scheme with two cells of scope `{0}` and grade `1`: `false` (the cell `a`) and
`true` (the cell `b`). -/
private def pairScheme : CellScheme Bool (Fin 1) :=
  ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, fun _ ↦ 1⟩

/-- The rows of `pairScheme`: the row of `a` is `(1, 1)` and the row of `b` is `(1, 2)`. -/
private def pairRows : pairScheme.Rows.{u} := ⟨fun s t ↦ if s && t.1 then 2 else 1⟩

/-- The label `ω * 5 + 1`. -/
private noncomputable abbrev omega0FiveOne : Label.{u} :=
  ((ω * (5 : ℕ) + (1 : ℕ) : Ordinal.{u}) : Label.{u})

/-- The section `(1, ω * 5 + 1)` of `pairScheme`. -/
private noncomputable def pairSection : Bool → Label.{u} := fun b ↦ if b then omega0FiveOne else 1

/-- `1 ≤ ω * 5 + 1`. -/
private theorem one_le_omega0FiveOne : (1 : Label.{u}) ≤ omega0FiveOne :=
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by simp))

/-- The label `ω * 5 + 1` is self-visible at `1`. -/
private theorem isSelfVisible_omega0FiveOne : IsSelfVisible 1 omega0FiveOne.{u} :=
  isSelfVisible_coe.mpr (by rw [omega0_mul_add_natCast_mod])

/-- The labels of `pairSection` are at most `ω * 5 + 1`. -/
private theorem pairSection_le (b : Bool) : pairSection.{u} b ≤ omega0FiveOne := by
  cases b
  · exact one_le_omega0FiveOne
  · exact le_rfl

/-- The shifter of the locality of `b`: it fixes the labels `≤ 1` and sends the others to
`ω * 5 + 1`. -/
private noncomputable def pairShifter (x : Label.{u}) : Label.{u} :=
  if x ≤ 1 then x else omega0FiveOne

/-- `pairShifter` fixes bottom. -/
private theorem pairShifter_bot : pairShifter (⊥ : Label.{u}) = ⊥ := ite_eq_left bot_le

/-- `pairShifter` is a witness bounded by grade `1`. -/
private theorem isWitness_pairShifter : IsWitness (stepSuppressor.{u} 1) pairShifter where
  antitone := (IsWitness.id_step 1).antitone
  isSelfVisible := (IsWitness.id_step 1).isSelfVisible
  map_bot := pairShifter_bot
  monotone x y h := by
    unfold pairShifter
    split_ifs with hx hy hy
    · exact h
    · exact hx.trans one_le_omega0FiveOne
    · exact absurd (h.trans hy) hx
    · exact le_rfl
  visibilityReplace_comm x k hx i hi := by
    rcases le_or_gt k 1 with hk | hk
    · by_cases hx1 : x ≤ 1
      · unfold pairShifter
        rw [ite_eq_left hx1,
          ite_eq_left (visibilityReplace_le_of_le hi (isSelfVisible_one.mpr hk) hx1)]
      · have h1 : ¬ visibilityReplace k i x ≤ 1 :=
          fun h ↦ hx1 ((le_visibilityReplace (by omega) x).trans h)
        unfold pairShifter
        rw [ite_eq_right hx1, ite_eq_right h1,
          (isSelfVisible_omega0FiveOne.mono hk).visibilityReplace_eq]
    · rw [stepSuppressor_of_lt hk, le_bot_iff] at hx
      have hx0 : x = ⊥ := by
        unfold pairShifter at hx
        split_ifs at hx
        · exact hx
        · exact absurd hx (by simp)
      rw [hx0, visibilityReplace_bot, pairShifter_bot, visibilityReplace_bot]

/-- `2` is not at most `1`, as labels. -/
private theorem not_two_le_one : ¬ (2 : Label.{u}) ≤ 1 :=
  not_le.mpr (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr one_lt_two))

/-- **The section `(1, ω * 5 + 1)` is lawful** for the rows `(1, 1)` of `a` and `(1, 2)` of `b`.
The locality of `b` is witnessed by `pairShifter`, which sends `1` to `1` and `2` to `ω * 5 + 1`;
that of `a` is the identity. -/
private theorem isLawful_pairSection : pairRows.{u}.IsLawful pairSection where
  orderly d := by
    cases d
    · simp [pairSection, pairScheme]
    · exact isSelfVisible_omega0FiveOne
  locality s := by
    cases s
    · -- The capped target is the constant `1`, the row of `a`.
      convert TransformsTo.refl _ (pairRows.row false) using 1
      funext d
      simp only [pairRows, Bool.false_and, Bool.false_eq_true, ↓reduceIte, pairSection]
      exact min_eq_right (by split_ifs <;> simp)
    · refine ⟨_, pairShifter, isWitness_pairShifter, fun ⟨b, hb⟩ ↦ ?_⟩
      dsimp only
      rw [stepSuppressor_of_le (by simp [pairScheme]), min_top_right,
        show pairSection true = omega0FiveOne from rfl, min_eq_left (pairSection_le b)]
      cases b
      · exact (ite_eq_left le_rfl).symm
      · exact (ite_eq_right not_two_le_one).symm
  availability s _ _ _ := ⟨true, rfl, pairSection_le s⟩

/-- **The decoder does not reflect bottom**: relative to the empty set of labels at grade `1`, it
sends the label `1`, which is not bottom, to bottom (the block coding reserves the code rank `0`,
so every code below `ω` is decoded as bottom), and it sends `ω * 5 + 1` to the formal top. -/
private theorem strongDecode_empty_one :
    strongDecode (∅ : Finset Label.{u}) 1 1 = ⊥ ∧ (1 : Label.{u}) ≠ ⊥ ∧
      strongDecode (∅ : Finset Label.{u}) 1 omega0FiveOne = ⊤ := by
  have hcb : codeBlocks ((∅ : Finset Label.{u}).image (spread 1)) = ∅ := by
    simp [codeBlocks, valueBlocks]
  refine ⟨?_, by simp, ?_⟩
  · rw [strongDecode_apply, show (1 : Label.{u}) = ((1 : Ordinal.{u}) : Label.{u}) from rfl,
      blockDecode_coe, blockDecodeOrd_of_eq_zero (Ordinal.div_eq_zero_of_lt Ordinal.one_lt_omega0),
      unspread_bot]
  · rw [strongDecode_apply, blockDecode_coe, blockDecodeOrd_of_lt, unspread_top]
    rw [hcb, omega0_mul_add_natCast_div, card_empty]
    exact Nat.cast_lt.mpr (by decide)

/-- **The decoded section of a lawful section need not be lawful.**  The lawful section
`(1, ω * 5 + 1)` decodes, relative to the empty set of labels at grade `1`, to `(⊥, ⊤)`, which is
not lawful for the rows `(1, 1)` of `a` and `(1, 2)` of `b`: the row `(1, 2)` of `b` does not
transform, at grade `1`, to `(⊥, ⊤)`, since a shifter sending `1` to bottom sends its
visibility replacement `2` to bottom as well.  So the unconditional decoding claim fails for the
strongly coded decoder.  The hypotheses of ownerwise decoding fail at `b`, as they must: its row
is not short at grade `1`, and the decoded labels are not those of a lawful section. -/
private theorem not_isLawful_strongDecode_pairSection :
    pairRows.{u}.IsLawful pairSection ∧
      strongDecode ∅ 1 ∘ pairSection.{u} = (fun b ↦ if b then ⊤ else ⊥) ∧
      ¬ pairRows.{u}.IsLawful (strongDecode ∅ 1 ∘ pairSection) ∧
      ¬ ∀ t, IsShort (pairScheme.grade true) (pairRows.{u}.row true t) := by
  obtain ⟨h1, -, h5⟩ := strongDecode_empty_one.{u}
  have hdec : strongDecode ∅ 1 ∘ pairSection.{u} = (fun b ↦ if b then ⊤ else ⊥) := by
    funext b
    cases b
    · exact h1
    · exact h5
  refine ⟨isLawful_pairSection, hdec, fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨g, τ, hw, heq⟩ := h.locality true
    rw [hdec] at heq
    have ha := heq ⟨false, (mem_below _).mpr le_rfl⟩
    have hb := heq ⟨true, (mem_below _).mpr le_rfl⟩
    simp only [pairRows, pairScheme, Bool.and_true, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte, min_self, bot_le, min_eq_left] at ha hb
    -- The value at `b` forces `g 1 = ⊤`, so `τ 1 = ⊥` and `τ 2 = ⊤`.
    have hg : g 1 = ⊤ := top_le_iff.mp (hb.le.trans (min_le_right _ _))
    rw [hg, min_top_right] at ha hb
    have hc := hw.visibilityReplace_comm 1 2 (ha ▸ bot_le) 2 le_rfl
    rw [← ha, visibilityReplace_bot] at hc
    simp only [visibilityReplace_one, Nat.one_lt_ofNat, ↓reduceIte, Nat.cast_ofNat] at hc
    exact top_ne_bot (hb.trans hc)
  · have h2 := isShort_coe.mp
      (show IsShort 1 ((2 : Ordinal.{u}) : Label.{u}) from h ⟨true, (mem_below _).mpr le_rfl⟩)
    rw [show (2 : Ordinal.{u}) = ((2 : ℕ) : Ordinal.{u}) by norm_cast,
      Ordinal.natCast_mod_omega0] at h2
    exact absurd h2 (by exact_mod_cast (by decide : ¬ 2 ≤ 1))

/-- The labels of `pairSection`. -/
private noncomputable abbrev pairValues : Finset Label.{u} := {1, omega0FiveOne}

/-- The labels of `pairSection` lie in `pairValues`. -/
private theorem pairSection_mem (b : Bool) : pairSection.{u} b ∈ pairValues := by
  cases b <;> simp [pairSection]

/-- **Lawful decoding holds when the ownerwise hypotheses do**, on the same rows.  Relative to the
labels `{1, ω * 5 + 1}` of the section `(1, ω * 5 + 1)`, the decoder recovers it literally from
its normal form, and the decoded section is lawful by ownerwise decoding: the new owner `a` has
the row `(1, 1)`, short at grade `1`, and below the inherited owner `b` the decoded labels are
those of the lawful section `(1, ω * 5 + 1)`.  The decoder family is the same and never reflects
bottom (codes below `ω` go to `⊥` for every alphabet; `strongDecode_empty_one` for the empty
one): the failure of bottom reflection alone does not establish the failure of lawful
decoding. -/
private theorem isLawful_strongDecode_strongEncode_pairSection :
    strongDecode pairValues 1 ∘ (strongEncode pairValues 1 ∘ pairSection.{u}) = pairSection ∧
      pairRows.{u}.IsLawful (strongDecode pairValues 1 ∘ (strongEncode pairValues 1 ∘ pairSection))
      := by
  have hdecode (d : Bool) :
      strongDecode pairValues 1 (strongEncode pairValues 1 (pairSection.{u} d)) = pairSection d :=
    strongDecode_strongEncode (pairSection_mem d)
  refine ⟨funext hdecode, ?_⟩
  refine (isLawful_pairSection.strongEncode fun _ ↦ le_rfl).strongDecode_of_ownerwise
    isLawful_pairSection (fun _ ↦ le_rfl) {false} (fun c hc d ↦ ?_) fun c _ d ↦ hdecode d
  obtain rfl : c = false := hc
  exact show IsShort 1 ((1 : Ordinal.{u}) : Label.{u}) from
    isShort_coe.mpr (by exact_mod_cast (Ordinal.natCast_mod_omega0 1).le)

end TransformationExamples

end VaughtConjecture
