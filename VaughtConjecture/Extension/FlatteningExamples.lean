/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.FlattenedSource
import VaughtConjecture.Extension.TransformationExamples

/-!
# Examples: positive-cap transport and the flattened source

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.4 (owner alignment), and the special cases of the
checkpoints of `roadmap/IMPLEMENTATION.md` (zero, one coordinate, repeated coordinates, and the
bottom section).  The schemes, rows, and sections are those of
`VaughtConjecture.Extension.TransformationExamples`.

* **The decoding counterexample does not refute positive-cap transport.**  On two cells `a`, `b`
  of scope `{0}` and grade `1` (repeated coordinates), with rows `(1, 1)` and `(1, 2)`, the lawful
  section `(1, ω * 5 + 1)` decodes, relative to the empty set of labels at grade `1`, to
  `(⊥, ⊤)`, which is not lawful.  The hypothesis of `CellScheme.Rows.IsLawful.map_of_min_eq`
  fails there for every lawful `q` and every cap `γ ≠ ⊥`: it would make `q` bottom at `a` and not
  at `b`, and the row `(1, 2)` of `b` transforms to no labelling that is bottom at `a` and not at
  `b`.  At the cap `γ = ⊥` the hypothesis holds (with `q` the section itself) and the conclusion
  fails, so `γ ≠ ⊥` cannot be dropped.
* **Positive-cap transport with a companion other than the result.**  Relative to the labels of
  the section, the decoded normal form agrees at the cap `1` with the lawful section capped at
  `1`, which differs from it at `b`; positive-cap transport makes the decoded normal form lawful.
* **The grade `0`.**  On one cell of grade `0` whose row is `ω + 5`, the section `ω + 5` is lawful,
  and its flattened source at `0` is lawful, short at `0`, and decodes to `ω + 5`.
* **One coordinate; a code at `K + 1`.**  On one cell of scope `{0}` and grade `1` with row `3`,
  the normal form of the section `3` at grade `1` has finite part `2 = K + 1` (strongly coded, not
  short), and its flattened source is lawful, short at `1`, and decodes to `3`.
* **Two codes at `K + 1`.**  The labels `2` and `3` both have finite part above `1`, so both
  their codes relative to `{2, 3}` at grade `1` have finite part `2 = K + 1`; their flattened codes
  are distinct.
* **A code already short.**  The code of `1` relative to `{1}` at grade `1` is short at `1`, and
  flattening fixes it.
* **The bottom section.**  The flattened source of the bottom labelling is bottom.
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

open TransformationExamples

/-! ### The decoding counterexample and positive-cap transport -/

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
  rw [not_isLawful_strongDecode_pairSection.2.1] at hag
  have ha := (eq_bot_iff_of_min_eq (hag false) hγ).mp rfl
  have hb : q true ≠ ⊥ := fun h ↦ (eq_bot_iff_of_min_eq (hag true) hγ).mpr h |> top_ne_bot
  exact hb (eq_bot_of_isLawful hq ha)

/-- **The cap `⊥` cannot be allowed.**  At `γ = ⊥` the agreement holds with the lawful section
itself, and the decoded section `(⊥, ⊤)` is not lawful. -/
example : pairRows.{u}.IsLawful pairSection ∧
    (∀ d, min ((strongDecode ∅ 1 ∘ pairSection) d) ⊥ = min (pairSection d) ⊥) ∧
    ¬ pairRows.{u}.IsLawful (strongDecode ∅ 1 ∘ pairSection) := by
  obtain ⟨hp, -, hn, -⟩ := not_isLawful_strongDecode_pairSection.{u}
  exact ⟨hp, fun _ ↦ by simp, hn⟩

/-- **Positive-cap transport with a companion other than the result.**  Relative to the labels
`{1, ω * 5 + 1}` of the section, the decoded normal form agrees at the cap `1` with the section
capped at `1`, which is lawful and differs from the decoded normal form at `b`; positive-cap
transport makes the decoded normal form lawful. -/
example : pairRows.{u}.IsLawful
      (strongDecode {1, omega0FiveOne} 1 ∘ (strongEncode {1, omega0FiveOne} 1 ∘ pairSection)) ∧
    strongDecode {1, omega0FiveOne} 1 ∘ (strongEncode {1, omega0FiveOne} 1 ∘ pairSection.{u}) ≠
      fun d ↦ min (pairSection d) 1 := by
  have hdec : strongDecode {1, omega0FiveOne} 1 ∘
      (strongEncode {1, omega0FiveOne} 1 ∘ pairSection.{u}) = pairSection :=
    funext fun d ↦ strongDecode_strongEncode (by cases d <;> simp [pairSection])
  have hq : pairRows.{u}.IsLawful fun d ↦ min (pairSection d) 1 :=
    isLawful_pairSection.min_const_of_isSelfVisible (K := 1) (fun _ ↦ le_rfl) (by simp)
  refine ⟨(isLawful_pairSection.strongEncode fun _ ↦ le_rfl).map_of_min_eq hq (fun _ ↦ le_rfl)
    isWitness_strongDecode (γ := 1) (by simp) fun d ↦ ?_, fun h ↦ ?_⟩
  · rw [show strongDecode {1, omega0FiveOne} 1
        ((strongEncode {1, omega0FiveOne} 1 ∘ pairSection) d) = pairSection d from
        congrFun hdec d, min_assoc, min_self]
  · have hb := congrFun (hdec.symm.trans h) true
    simp only [pairSection, ↓reduceIte] at hb
    have h5 : (0 : Ordinal.{u}) < ((5 : ℕ) : Ordinal.{u}) := by exact_mod_cast (by decide : 0 < 5)
    have h1 : (1 : Ordinal.{u}) < ω * (5 : ℕ) + (1 : ℕ) :=
      Ordinal.one_lt_omega0.trans_le ((Ordinal.le_mul_left ω h5).trans le_self_add)
    exact absurd (hb.trans_le (min_le_right _ _))
      (not_le.mpr (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr h1)))

/-! ### Special cases of the flattened source -/

/-- The cell scheme with one cell of scope `{0}` and grade `0`. -/
private def zeroScheme : CellScheme (Fin 1) (Fin 1) :=
  ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, fun _ ↦ 0⟩

/-- The label `ω + 5`. -/
private noncomputable abbrev omega0Five : Label.{u} := ((ω + 5 : Ordinal.{u}) : Label.{u})

/-- The rows of `zeroScheme` with value `ω + 5`. -/
private noncomputable def zeroRows : zeroScheme.Rows.{u} := ⟨fun _ _ ↦ omega0Five⟩

/-- **The grade `0`**: on one cell of grade `0` with row `ω + 5`, the section `ω + 5` is lawful,
and its flattened source at `0` is lawful, short at `0`, and decodes to `ω + 5`. -/
example : zeroRows.{u}.IsLawful (flattenedSource {omega0Five} 0 fun _ ↦ omega0Five) ∧
    (∀ d : Fin 1, IsShort 0 (flattenedSource ({omega0Five} : Finset Label.{u}) 0
      (fun _ ↦ omega0Five) d)) ∧
    ∀ d : Fin 1, strongDecode {omega0Five} 0
      (flattenedSource ({omega0Five} : Finset Label.{u}) 0 (fun _ ↦ omega0Five) d) =
        omega0Five := by
  have hw : zeroRows.{u}.IsLawful fun _ ↦ omega0Five :=
    { orderly := fun _ ↦ isSelfVisible_coe.mpr (by simp [zeroScheme])
      locality := fun _ ↦ by
        simp only [min_self]
        exact TransformsTo.refl _ _
      availability := fun _ t _ _ ↦ ⟨t, rfl, le_rfl⟩ }
  exact ⟨hw.flattenedSource fun _ ↦ le_rfl, isShort_flattenedSource,
    fun _ ↦ strongDecode_flattenedSource (mem_singleton_self _)⟩

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
  ⟨isStronglyCoded_strongEncode _, isStronglyCoded_and_not_isShort_strongEncode.2,
    isLawful_pointSection.flattenedSource fun _ ↦ le_rfl, isShort_flattenedSource,
    flattenedSource_ne_top, fun _ ↦ strongDecode_flattenedSource (mem_singleton_self _)⟩

/-- **Two codes at `K + 1`.**  The labels `2` and `3` both have finite part above `1`, so their
codes relative to `{2, 3}` at grade `1` both have finite part `2 = K + 1`; flattening at `1` keeps
them distinct. -/
example : flatten 1 (strongEncode ({2, 3} : Finset Label.{u}) 1 2) ≠
    flatten 1 (strongEncode ({2, 3} : Finset Label.{u}) 1 3) := fun h ↦ by
  have h23 := injOn_flatten_strongEncode (V := ({2, 3} : Finset Label.{u})) (K := 1) le_rfl
    (by simp) (by simp) h
  have h23' : ((2 : Ordinal.{u}) : Label.{u}) = ((3 : Ordinal.{u}) : Label.{u}) := h23
  rw [WithBot.coe_inj, WithTop.coe_inj] at h23'
  have : ((2 : ℕ) : Ordinal.{u}) = ((3 : ℕ) : Ordinal.{u}) := by exact_mod_cast h23'
  exact absurd (Nat.cast_injective this) (by decide)

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
