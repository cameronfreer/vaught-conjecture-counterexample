/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.FlattenedSource
import VaughtConjecture.Geometry.IntervalPlan

/-!
# Examples: positive-cap transport and the flattened source

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.4 (owner alignment), and the special cases of the
checkpoints of `roadmap/IMPLEMENTATION.md` (zero, one coordinate, repeated coordinates, and the
bottom section).

* **The decoding counterexample does not refute positive-cap transport.**  On two cells `a`, `b`
  of scope `{0}` and grade `1` (repeated coordinates), with rows `(1, 1)` and `(1, 2)`, the lawful
  section `(1, ω * 5 + 1)` decodes, relative to the empty set of labels at grade `1`, to
  `(⊥, ⊤)`, which is not lawful (`VaughtConjecture.Extension.TransformationExamples`).  The
  hypothesis of `CellScheme.Rows.IsLawful.map_of_min_eq` fails there for every lawful `q` and
  every cap `γ ≠ ⊥`: it would make `q` bottom at `a` and not at `b`, and the row `(1, 2)` of `b`
  transforms to no labelling that is bottom at `a` and not at `b`.  At the cap `γ = ⊥` the
  hypothesis holds (with `q` the section itself) and the conclusion fails, so `γ ≠ ⊥` cannot be
  dropped.  Relative to the labels of the section, the decoded normal form is lawful by
  positive-cap transport.
* **The grade `0`.**  The code of `ω + 5` relative to `{ω + 5}` at grade `0`, flattened at `0`, is
  short at `0` and decodes to `ω + 5`.
* **One coordinate; a code at `K + 1`.**  On one cell of scope `{0}` and grade `1` with row `3`,
  the section `3` is lawful; its normal form at grade `1` has finite part `2 = K + 1` (strongly
  coded, not short), and its flattened source is lawful, short at `1`, and decodes to `3`.
* **A code already short.**  The code of `1` relative to `{1}` at grade `1` is short at `1`, and
  flattening fixes it.
* **The bottom section.**  The flattened source of the bottom labelling is bottom.
* **The cap `⊥` on one face.**  When the prescribed face is the target face, the flattened source
  of the prescription capped at the owner label is a coded lift, and the rows have owner-capped
  lifts at the cap `⊥`.
* **The hypotheses of non-merging.**  At a coding grade `K = 2` above the flattening grade `m = 1`,
  the flattened code of `2` relative to `{2}` decodes to `1`: the decoder at `K` separates the
  finite parts `1` and `2` that flattening at `1` merges.  For an arbitrary strongly coded normal
  form with an arbitrary decoder bounded by the grade, flattening may merge labels the decoder
  separates: the label `2` is strongly coded at `1` and decoded by the identity, a witness bounded
  by grade `1`, while its flattening at `1` is `1`.
-/

namespace VaughtConjecture

open Finset Label CellScheme
open scoped Ordinal

universe u

namespace FlatteningExamples

/-! ### The decoding counterexample and positive-cap transport -/

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

/-- The label `ω * 5 + 1` is self-visible at `1`. -/
private theorem isSelfVisible_omega0FiveOne : IsSelfVisible 1 omega0FiveOne.{u} :=
  isSelfVisible_coe.mpr (by rw [omega0_mul_add_natCast_mod])

/-- `1 ≤ ω * 5 + 1`. -/
private theorem one_le_omega0FiveOne : (1 : Label.{u}) ≤ omega0FiveOne :=
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by simp))

/-- The labels of `pairSection` are at most `ω * 5 + 1`. -/
private theorem pairSection_le (b : Bool) : pairSection.{u} b ≤ omega0FiveOne := by
  cases b
  · exact one_le_omega0FiveOne
  · exact le_rfl

/-- The shifter of the locality of `b`: it fixes the labels `≤ 1` and sends the others to
`ω * 5 + 1`. -/
private noncomputable def pairShifter (x : Label.{u}) : Label.{u} :=
  if x ≤ 1 then x else omega0FiveOne

/-- `pairShifter` is a witness bounded by grade `1`. -/
private theorem isWitness_pairShifter : IsWitness (stepSuppressor.{u} 1) pairShifter where
  antitone := (IsWitness.id_step 1).antitone
  isSelfVisible := (IsWitness.id_step 1).isSelfVisible
  map_bot := ite_eq_left bot_le
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
      have h0 : pairShifter (⊥ : Label.{u}) = ⊥ := ite_eq_left bot_le
      rw [hx0, visibilityReplace_bot, h0, visibilityReplace_bot]

/-- The section `(1, ω * 5 + 1)` is lawful for the rows `(1, 1)` and `(1, 2)`. -/
private theorem isLawful_pairSection : pairRows.{u}.IsLawful pairSection where
  orderly d := by
    cases d
    · simp [pairSection, pairScheme]
    · exact isSelfVisible_omega0FiveOne
  locality s := by
    cases s
    · convert TransformsTo.refl _ (pairRows.row false) using 1
      funext d
      simp only [pairRows, Bool.false_and, Bool.false_eq_true, ↓reduceIte, pairSection]
      exact min_eq_right (by split_ifs <;> simp)
    · refine ⟨_, pairShifter, isWitness_pairShifter, fun ⟨b, hb⟩ ↦ ?_⟩
      dsimp only
      rw [stepSuppressor_of_le (by simp [pairScheme]), min_top_right,
        show pairSection true = omega0FiveOne from rfl, min_eq_left (pairSection_le b)]
      cases b
      · exact (ite_eq_left le_rfl).symm
      · exact (ite_eq_right (not_le.mpr (WithBot.coe_lt_coe.mpr
          (WithTop.coe_lt_coe.mpr one_lt_two)))).symm
  availability s _ _ _ := ⟨true, rfl, pairSection_le s⟩

/-- Relative to the empty set of labels at grade `1`, the decoder sends `1` to bottom and
`ω * 5 + 1` to the formal top, so `pairSection` decodes to `(⊥, ⊤)`. -/
private theorem strongDecode_pairSection :
    strongDecode (∅ : Finset Label.{u}) 1 ∘ pairSection = fun b ↦ if b then ⊤ else ⊥ := by
  have hcb : codeBlocks ((∅ : Finset Label.{u}).image (spread 1)) = ∅ := by
    simp [codeBlocks, valueBlocks]
  funext b
  cases b
  · rw [Function.comp_apply, strongDecode_apply,
      show pairSection false = ((1 : Ordinal.{u}) : Label.{u}) from rfl, blockDecode_coe,
      blockDecodeOrd_of_eq_zero (Ordinal.div_eq_zero_of_lt Ordinal.one_lt_omega0), unspread_bot]
    rfl
  · rw [Function.comp_apply, strongDecode_apply, show pairSection true = omega0FiveOne from rfl,
      blockDecode_coe, blockDecodeOrd_of_lt, unspread_top]
    · rfl
    · rw [hcb, omega0_mul_add_natCast_div, card_empty]
      exact Nat.cast_lt.mpr (by decide)

/-- A lawful section of the rows `(1, 1)`, `(1, 2)` that is bottom at `a` is bottom at `b`: a
shifter sending the value `1` to bottom sends its visibility replacement `2` to bottom. -/
private theorem eq_bot_of_isLawful {q : Bool → Label.{u}} (hq : pairRows.IsLawful q)
    (ha : q false = ⊥) : q true = ⊥ := by
  obtain ⟨g, τ, hw, heq⟩ := hq.locality true
  have h₁ := heq ⟨false, (mem_below _).mpr le_rfl⟩
  have h₂ := heq ⟨true, (mem_below _).mpr le_rfl⟩
  simp only [pairRows, pairScheme, Bool.and_true, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte, min_self, ha, bot_le, min_eq_left] at h₁ h₂
  -- `τ 1 ≤ g 1` is the guard at `1`; the label at `b` is `min (τ 2) (g 1)`.
  by_contra hb
  have hg : g 1 ≠ ⊥ := fun h ↦ hb (by rw [h₂, h, min_bot_right])
  have hτ1 : τ 1 = ⊥ := by
    rw [eq_comm, min_eq_bot] at h₁
    exact h₁.resolve_right hg
  have h2 := hw.apply_visibilityReplace_eq_bot hτ1 2 le_rfl
  simp only [visibilityReplace_one, Nat.one_lt_ofNat, ↓reduceIte, Nat.cast_ofNat] at h2
  exact hb (by rw [h₂, h2, min_eq_left bot_le])

/-- **The test of positive-cap transport on the decoding counterexample.**  For no lawful section
`q` of the rows `(1, 1)`, `(1, 2)` and no cap `γ ≠ ⊥` does the decoded section `(⊥, ⊤)` agree with
`q` capped at `γ`: the agreement would make `q` bottom at `a` and not at `b`.  So the
counterexample does not satisfy the hypothesis of `CellScheme.Rows.IsLawful.map_of_min_eq`. -/
example : ¬ ∃ (q : Bool → Label.{u}) (γ : Label.{u}), pairRows.IsLawful q ∧ γ ≠ ⊥ ∧
    ∀ d, min ((strongDecode ∅ 1 ∘ pairSection) d) γ = min (q d) γ := by
  rintro ⟨q, γ, hq, hγ, hag⟩
  rw [strongDecode_pairSection] at hag
  have ha := (eq_bot_iff_of_min_eq (hag false) hγ).mp rfl
  have hb : q true ≠ ⊥ := fun h ↦ (eq_bot_iff_of_min_eq (hag true) hγ).mpr h |> top_ne_bot
  exact hb (eq_bot_of_isLawful hq ha)

/-- **The cap `⊥` cannot be allowed.**  At `γ = ⊥` the agreement holds with the lawful section
itself, and the decoded section `(⊥, ⊤)` is not lawful. -/
example : pairRows.{u}.IsLawful pairSection ∧
    (∀ d, min ((strongDecode ∅ 1 ∘ pairSection) d) ⊥ = min (pairSection d) ⊥) ∧
    ¬ pairRows.{u}.IsLawful (strongDecode ∅ 1 ∘ pairSection) := by
  refine ⟨isLawful_pairSection, fun _ ↦ by simp, fun h ↦ ?_⟩
  rw [strongDecode_pairSection] at h
  exact top_ne_bot (eq_bot_of_isLawful h rfl)

/-- **Positive-cap transport decodes the normal form.**  Relative to the labels
`{1, ω * 5 + 1}` of the section, the decoded normal form agrees with the section at every cap,
so positive-cap transport makes it lawful, without bottom reflection of the decoder. -/
example : pairRows.{u}.IsLawful
    (strongDecode {1, omega0FiveOne} 1 ∘ (strongEncode {1, omega0FiveOne} 1 ∘ pairSection)) := by
  have hdec (d : Bool) : strongDecode {1, omega0FiveOne} 1
      (strongEncode {1, omega0FiveOne} 1 (pairSection.{u} d)) = pairSection d :=
    strongDecode_strongEncode (by cases d <;> simp [pairSection])
  exact (isLawful_pairSection.strongEncode fun _ ↦ le_rfl).map_of_min_eq isLawful_pairSection
    (fun _ ↦ le_rfl) isWitness_strongDecode (γ := 1) (by simp) fun d ↦ by
      rw [Function.comp_apply, hdec]

/-! ### Special cases of the flattened source -/

/-- **The grade `0`**: the flattened code of `ω + 5` at grade `0` is short at `0` and decodes to
`ω + 5`. -/
example : let x : Label.{u} := ((ω + 5 : Ordinal.{u}) : Label.{u})
    IsShort 0 (flatten 0 (strongEncode {x} 0 x)) ∧
      strongDecode {x} 0 (flatten 0 (strongEncode {x} 0 x)) = x :=
  ⟨isShort_flatten 0 _, strongDecode_flatten_strongEncode le_rfl (mem_singleton_self _)⟩

/-- The cell scheme with one cell of scope `{0}` and grade `1`. -/
private def pointScheme : CellScheme (Fin 1) (Fin 1) :=
  ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, fun _ ↦ 1⟩

/-- The rows of `pointScheme` with value `3`. -/
private def pointRows : pointScheme.Rows.{u} := ⟨fun _ _ ↦ 3⟩

/-- The section of `pointScheme` with label `3` is lawful for the rows with value `3`. -/
private theorem isLawful_pointSection : pointRows.{u}.IsLawful fun _ ↦ (3 : Label.{u}) where
  orderly _ := by simp [pointScheme]
  locality _ := by
    simp only [min_self]
    exact TransformsTo.refl _ _
  availability _ t _ _ := ⟨t, rfl, le_rfl⟩

/-- The code of `3` relative to `{3}` at grade `1` has finite part `2`. -/
private theorem not_isShort_strongEncode_three :
    ¬ IsShort 1 (strongEncode ({3} : Finset Label.{u}) 1 3) := fun h ↦ by
  have h3 : (3 : Ordinal.{u}) = ((3 : ℕ) : Ordinal.{u}) := by norm_cast
  have hs : spreadOrd 1 (3 : Ordinal.{u}) = ω * 3 + (2 : ℕ) := by
    have h1 : (3 : Ordinal.{u}) % ω = 3 := by rw [h3, Ordinal.natCast_mod_omega0]
    have h2 : (3 : Ordinal.{u}) / ω = 0 :=
      Ordinal.div_eq_zero_of_lt (h3 ▸ Ordinal.natCast_lt_omega0 3)
    rw [spreadOrd, h1, h2, ite_eq_right (by rw [h3]; exact_mod_cast (by decide : ¬ 3 ≤ 1))]
    simp
  have he : (3 : Label.{u}) = ((3 : Ordinal.{u}) : Label.{u}) := rfl
  rw [strongEncode_apply, image_singleton, he, spread_coe, hs, blockEncode_coe] at h
  have hv : (ω * 3 + (2 : ℕ) : Ordinal.{u}) / ω ∈
      valueBlocks ({((ω * 3 + (2 : ℕ) : Ordinal.{u}) : Label.{u})} : Finset Label.{u}) :=
    div_mem_valueBlocks (by simp)
  have := isShort_coe.mp h
  rw [blockEncodeOrd, ite_eq_left hv, omega0_mul_add_natCast_mod, omega0_mul_add_natCast_mod]
    at this
  exact absurd this (by exact_mod_cast (by decide : ¬ 2 ≤ 1))

/-- **One coordinate, and a code at `K + 1`.**  On one cell of grade `1` with row `3`, the normal
form of the section `3` at grade `1` is strongly coded and not short at `1` (its finite part is
`2 = K + 1`); the flattened source is lawful, short at `1`, never the formal top, and decodes to
`3`. -/
example : IsStronglyCoded 1 (strongEncode ({3} : Finset Label.{u}) 1 3) ∧
    ¬ IsShort 1 (strongEncode ({3} : Finset Label.{u}) 1 3) ∧
    pointRows.{u}.IsLawful (flattenedSource {3} 1 fun _ ↦ 3) ∧
    (∀ d : Fin 1, IsShort 1 (flattenedSource ({3} : Finset Label.{u}) 1 (fun _ ↦ 3) d)) ∧
    (∀ d : Fin 1, flattenedSource ({3} : Finset Label.{u}) 1 (fun _ ↦ 3) d ≠ ⊤) ∧
    ∀ d : Fin 1,
      strongDecode {3} 1 (flattenedSource ({3} : Finset Label.{u}) 1 (fun _ ↦ 3) d) = 3 :=
  ⟨isStronglyCoded_strongEncode _, not_isShort_strongEncode_three,
    isLawful_pointSection.flattenedSource fun _ ↦ le_rfl, isShort_flattenedSource,
    flattenedSource_ne_top, fun _ ↦ strongDecode_flattenedSource (mem_singleton_self _)⟩

/-- **A code already short.**  The code of `1` relative to `{1}` at grade `1` is short at `1`, and
flattening at `1` fixes it. -/
example : IsShort 1 (strongEncode ({1} : Finset Label.{u}) 1 1) ∧
    flatten 1 (strongEncode ({1} : Finset Label.{u}) 1 1) = strongEncode {1} 1 1 := by
  have hshort : IsShort 1 (strongEncode ({1} : Finset Label.{u}) 1 1) := by
    have h1 : (1 : Ordinal.{u}) = ((1 : ℕ) : Ordinal.{u}) := by norm_cast
    have hs : spreadOrd 1 (1 : Ordinal.{u}) = ω * 0 + (1 : ℕ) := by
      rw [spreadOrd, h1, Ordinal.natCast_mod_omega0,
        Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 1), ite_eq_left le_rfl]
      simp
    have he : (1 : Label.{u}) = ((1 : Ordinal.{u}) : Label.{u}) := rfl
    rw [strongEncode_apply, image_singleton, he, spread_coe, hs, blockEncode_coe, isShort_coe]
    have hv : (ω * 0 + (1 : ℕ) : Ordinal.{u}) / ω ∈
        valueBlocks ({((ω * 0 + (1 : ℕ) : Ordinal.{u}) : Label.{u})} : Finset Label.{u}) :=
      div_mem_valueBlocks (by simp)
    rw [blockEncodeOrd, ite_eq_left hv, omega0_mul_add_natCast_mod, omega0_mul_add_natCast_mod]
  exact ⟨hshort, hshort.flatten_eq⟩

/-- **The bottom section**: the flattened source of the bottom labelling is bottom. -/
example (V : Finset Label.{u}) (m : ℕ) : flattenedSource V m (fun _ : Bool ↦ ⊥) = fun _ ↦ ⊥ := by
  funext d
  rw [flattenedSource_apply, strongEncode_apply, spread_bot, blockEncode_bot, flatten_bot]

/-- **The cap `⊥` on one face.**  When the prescribed face is the target face, the flattened
source of the prescription capped at the owner label is itself a coded lift, so the rows have
owner-capped lifts at the cap `⊥`, on finitely many cells, whatever the rows. -/
example {ι α : Type*} {D : CellScheme ι α} (R : D.Rows.{u}) (B : Finset α) (j : ℕ)
    [Finite (D.below (B, j + 1))] : R.HasOwnerCappedLifts (Finset.Subset.refl B) j ⊥ := by
  classical
  have := Fintype.ofFinite (D.below (B, j + 1))
  refine Rows.hasOwnerCappedLifts_bot_of_codedLift _ fun p hp o ho _ _ ↦ ?_
  set V := univ.image fun e ↦ min (p e) (p o)
  refine ⟨V, flattenedSource V (j + 1) fun e ↦ min (p e) (p o),
    fun e ↦ mem_image_of_mem _ (mem_univ e), ?_, fun e ↦ rfl,
    fun d h ↦ eq_bot_of_strongDecode_flatten_strongEncode_eq_bot (mem_image_of_mem _ (mem_univ d))
      h⟩
  exact (hp.min_const_of_isSelfVisible (hp.isSelfVisible_of_gradedIndex_eq ho)).flattenedSource
    le_rfl

/-! ### The hypotheses of non-merging -/

/-- **The coding grade must not exceed the flattening grade.**  The code of `2` relative to `{2}`
at the coding grade `2`, flattened at `1`, decodes to `1`: unspreading at `2` separates the finite
parts `1` and `2` of the block of `2`, which flattening at `1` merges. -/
example : strongDecode ({2} : Finset Label.{u}) 2 (flatten 1 (strongEncode {2} 2 2)) = 1 := by
  have h2 : (2 : Ordinal.{u}) = ((2 : ℕ) : Ordinal.{u}) := by norm_cast
  rw [strongDecode_flatten_strongEncode_eq (mem_singleton_self _),
    show (2 : Label.{u}) = ((2 : Ordinal.{u}) : Label.{u}) from rfl, spread_coe, flatten_coe,
    unspread_coe]
  have hs : spreadOrd 2 (2 : Ordinal.{u}) = ((2 : ℕ) : Ordinal.{u}) := by
    rw [spreadOrd, h2, Ordinal.natCast_mod_omega0,
      Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 2), ite_eq_left le_rfl]
    simp
  have hf : flattenOrd 1 ((2 : ℕ) : Ordinal.{u}) = ((1 : ℕ) : Ordinal.{u}) := by
    rw [flattenOrd, Ordinal.natCast_mod_omega0,
      Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 2)]
    simp
  have hu : unspreadOrd 2 ((1 : ℕ) : Ordinal.{u}) = ((1 : ℕ) : Ordinal.{u}) := by
    rw [unspreadOrd, Ordinal.natCast_mod_omega0,
      Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 1), Ordinal.zero_div,
      Ordinal.zero_mod, ite_eq_left rfl]
    simp
  rw [hs, hf, hu, Nat.cast_one]
  rfl

/-- **The decoder must be that of the encoder.**  The label `2` is strongly coded at `1`, so it is
its own strongly coded normal form at grade `1`, decoded by the identity, a witness bounded by
grade `1`; its flattening at `1` is `1`, which the identity reads as `1`, not `2`. -/
example : IsStronglyCoded 1 (2 : Label.{u}) ∧ IsWitness (stepSuppressor.{u} 1) id ∧
    id (flatten 1 (2 : Label.{u})) = 1 := by
  refine ⟨.inr ⟨0, 2, le_rfl, by simp⟩, IsWitness.id_step 1, ?_⟩
  have h2 : (2 : Label.{u}) = (((2 : ℕ) : Ordinal.{u}) : Label.{u}) := by norm_cast
  rw [id, h2, flatten_coe, flattenOrd, Ordinal.natCast_mod_omega0,
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 2)]
  simp

end FlatteningExamples

end VaughtConjecture
