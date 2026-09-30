/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.NormalForm
import VaughtConjecture.Geometry.IntervalPlan

/-!
# Examples: strongly coded representatives, encoder round trips, and composition

Roadmap, Layer 3, 3.1, row 6, checkpoint 2.3 (transformation algebra, normal forms, coded
encoders); semantic contract, item 3.

* **A strongly coded representative.**  On the cell scheme with one cell of scope `{0}` and grade
  `1` whose row takes the value `3` (the cell of `pointRow 3` in
  `VaughtConjecture.Extension.CodingExamples`), the section with label `3` is lawful and not
  strongly coded at grade `1`, since `3 > 1 + 1`; it has a lawful representative strongly coded
  at grade `1` that transforms to it and back, and a witness bounded by `1` decodes it
  (`exists_stronglyCoded_pointSection`).
* **An encoder round trip.**  For `V = {3, ω + 5, ω + 7, ⊤}` at grade `1`, the decoder reads back
  each label, the codes are strongly coded at grade `1` although the labels `3`, `ω + 5`, and
  `ω + 7` are not, and the two labels `ω + 5 < ω + 7` of one band keep distinct, ordered codes
  (`strongEncode_roundTrip`).
* **Composition needs bottom reflection only off the short labels.**  Stage reduction to stage `1`
  and the band decoding for `{0}` are witnesses bounded by `0`, and the band decoding sends the
  value `0` of the first to bottom although `0` is not bottom, so the hypothesis of
  `Label.IsWitness.comp_of_bot_reflecting` fails; their composite is not a witness bounded by `0`
  (`not_isWitness_bandDecode_comp_reduce`), while
  `Label.IsWitness.exists_eq_comp_of_isShort` gives a witness bounded by `0` equal to the
  composite at every label short at `0` (`exists_eq_bandDecode_comp_reduce`).

## References

Witnesses are [Kni26, Definition 2.3.9]; the range normalization of rows below `ω ^ 2` is that of
[Kni26, Lemma 2.5.13], and the strong coding of the representatives is proved in this library.
-/

universe u

namespace VaughtConjecture

open Finset CellScheme Label
open scoped Ordinal

namespace TransformationExamples

/-! ### A strongly coded representative -/

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

/-- **A strongly coded representative of a section that is not strongly coded.**  The label `3`
is not strongly coded at grade `1`; the lawful section with label `3` has a lawful representative
strongly coded at grade `1`, transforming to it and back, and decoded by a witness bounded by
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

/-! ### An encoder round trip -/

/-- The label `ω · 1 + j`. -/
private noncomputable abbrev omega0Add (j : ℕ) : Label.{u} :=
  ((ω * (1 : ℕ) + (j : ℕ) : Ordinal.{u}) : Label.{u})

/-- The labels `3`, `ω + 5`, `ω + 7`, and `⊤`. -/
private noncomputable abbrev roundTripSet : Finset Label.{u} :=
  {3, omega0Add 5, omega0Add 7, ⊤}

/-- `ω + 5 < ω + 7`. -/
private theorem omega0Add_five_lt_seven : omega0Add.{u} 5 < omega0Add 7 :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (add_lt_add_right (by exact_mod_cast
    (by decide : 5 < 7)) _))

/-- **An encoder round trip.**  For `V = {3, ω + 5, ω + 7, ⊤}` at grade `1`: the labels `3`,
`ω + 5`, and `ω + 7` are not strongly coded at grade `1`, but their codes and the code of `⊤` are;
the decoder reads back every label of `V`; and the codes of `ω + 5 < ω + 7`, in one band, are
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

/-- Stage reduction to stage `1` is a witness bounded by `0`: it keeps `⊥` and `0` and sends every
other label to the formal top. -/
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

/-- The band decoding for `{0}` is a witness bounded by `0`. -/
private theorem isWitness_bandDecode_zero :
    IsWitness (stepSuppressor.{u} 0) (bandDecode {(0 : Label.{u})}) :=
  isWitness_bandDecode_stepSuppressor _ 0

/-- Stage reduction to stage `1` keeps ordinal zero. -/
private theorem reduce_one_zero : Label.reduce 1 (0 : Label.{u}) = 0 :=
  reduce_of_lt (by exact_mod_cast (zero_lt_one : (0 : Ordinal.{u}) < 1))

/-- The band decoding for `{0}` sends ordinal zero to bottom. -/
private theorem bandDecode_zero : bandDecode {(0 : Label.{u})} (0 : Label.{u}) = ⊥ :=
  bandDecodeOrd_of_eq_zero (by simp)

/-- **The hypothesis of guarded composition fails**: the band decoding for `{0}` sends the value
`0` of stage reduction to stage `1` to bottom, and `0` is not bottom. -/
private theorem not_bot_reflecting :
    bandDecode {(0 : Label.{u})} (Label.reduce 1 0) = ⊥ ∧ Label.reduce 1 (0 : Label.{u}) ≠ ⊥ := by
  rw [reduce_one_zero, bandDecode_zero]
  exact ⟨rfl, by simp⟩

/-- **Without bottom reflection the composite is not a witness**: at threshold `1` the guard holds
at `0`, whose image is bottom, but the replacement `1` of `0` goes to the formal top. -/
private theorem not_isWitness_bandDecode_comp_reduce :
    ¬ IsWitness (stepSuppressor.{u} 0) (bandDecode {(0 : Label.{u})} ∘ Label.reduce 1) := by
  intro h
  have h0 : (bandDecode {(0 : Label.{u})} ∘ Label.reduce 1) 0 = ⊥ := not_bot_reflecting.1
  have h1 := h.visibilityReplace_comm 0 1 (h0 ▸ bot_le) 1 le_rfl
  rw [h0, visibilityReplace_bot, visibilityReplace_zero, ite_eq_left one_pos, Function.comp_apply,
    reduce_of_le (by simp), bandDecode_top] at h1
  exact top_ne_bot h1

/-- **The composition on short labels needs no bottom reflection**: some witness bounded by `0`
agrees with the band decoding for `{0}` after stage reduction to stage `1` at every label short at
`0`. -/
private theorem exists_eq_bandDecode_comp_reduce :
    ∃ ρ, IsWitness (stepSuppressor.{u} 0) ρ ∧
      ∀ x, IsShort 0 x → ρ x = bandDecode {(0 : Label.{u})} (Label.reduce 1 x) :=
  isWitness_reduce_one.exists_eq_comp_of_isShort isWitness_bandDecode_zero le_rfl

end TransformationExamples

end VaughtConjecture
