/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Transform

/-!
# The witness algebra of the coatom completion

Roadmap, Layer 3, 3.1 (the section theorem and the witnesses bounded by a grade) and 3.1, row 6,
checkpoint 2.3 (transformation algebra); Layer 1 (guarded composition retains its guards, and no
transitivity is declared); semantic contract, item 3.

A value map `ν` is a **witness bounded by grade `K`** when `(stepSuppressor K, ν)` is a witness
([Kni26, Definition 2.3.9]): a witness whose suppressor is the formal top at the grades `≤ K` and
bottom above, which bounds the grades where the guard is vacuous, not the values of `ν`.  Such a
`ν` fixes bottom, is monotone, commutes with visibility replacement at every threshold `k ≤ K`
without a guard, and above `K` sends the replacements of a label to bottom whenever it sends the
label to bottom.  This file proves the rules for such witnesses on which the lawfulness of
transformed sections rests: the section theorem (`VaughtConjecture.Extension.SectionTheorem`), the
normal forms (`VaughtConjecture.Extension.NormalForm`), and ownerwise decoding
(`VaughtConjecture.Extension.OwnerwiseDecoding`); the maxima of shifters are for the shifters of
the new cells in the completion of a seed, not formalized here.  Each rule is stated with the
statement it is used to prove.

* **Block arithmetic.**  An ordinal `o` is `ω * (o / ω) + o % ω`, its block and its finite part.
  The rules for ordinals `ω * a + x` with `x < ω` (`omega0_mul_add_div`, `omega0_mul_add_mod`,
  `omega0_mul_add_lt`, `mod_le_mod_of_div_eq`, `Ordinal.visibilityReplace_omega0_mul_add`, and
  their forms with a natural number `x`) are stated once, here, for this file and for
  `VaughtConjecture.Extension.Encoders`.
* **Short labels** (`IsShort m x`): bottom, the formal top, or an ordinal whose finite part is at
  most `m` (`isShort_coe`).  The **flattening of finite parts** at `m`, `flatten m`, replaces a
  finite part above `m` by `m` (`flatten_coe`); it is monotone (`monotone_flatten`), fixes the short
  labels (`IsShort.flatten_eq`), and commutes with visibility replacement at thresholds `k ≤ m`
  (`flatten_visibilityReplace`).
* **Repair of the bottom guard** (`isWitness_comp_flatten`): a monotone map fixing bottom that
  commutes with visibility replacement at the thresholds `≤ m` becomes a witness bounded by grade
  `m` after flattening of finite parts at `m`, because a map commuting with the replacements at
  `m` sends every flattened point of a block to bottom once it sends one of them to bottom.
* **Composition without bottom reflection on short labels**
  (`IsWitness.exists_eq_comp_of_isShort`): for witnesses `τ` bounded by grade `m` and `ν` bounded
  by a grade `K ≥ m`, some witness bounded by grade `m` agrees with `ν ∘ τ` at every label short at
  `m`.  The composite `ν ∘ τ` itself need not be a witness, and the library's guarded composition
  `IsWitness.comp_of_bot_reflecting` needs bottom reflection for it
  (`VaughtConjecture.Extension.TransformationExamples`).
* **The capped witness** (`TransformsTo.exists_isWitness_capped`): the locality at a cell `c`
  of maximal grade, with a label `p c` self-visible at that grade, has a witness bounded by the
  grade of `c` whose values are at most `p c` and which sends each source label exactly to its
  capped target.  The key step is `IsWitness.le_apply_visibilityReplace`: past a self-visible
  cap below the suppressor, a shifter stays past it at every replacement.
* **Mapped locality** (`TransformsTo.map_of_isShort`, `TransformsTo.map_of_bot_reflecting`): a
  locality `E ⇒ (d ↦ min (p d) (p c))` gives `E ⇒ (d ↦ min (ν (p d)) (ν (p c)))` for a witness
  `ν` bounded by a grade `K ≥` the grade of `c`, when the source row `E` is short at the grade of
  `c`, or when `ν` reflects bottom.
* **Maxima of shifters** (`IsWitness.max`, and over a nonempty finite set
  `IsWitness.finsetSup`) and **postcomposition** (`IsWitness.transformsTo_comp`): a witness
  bounded by grade `K` transforms every labelling of cells of grade `≤ K` to its image.

Two further rules are already in the library: capping the target at a self-visible label
is `TransformsTo.min_const` (a related target-capping variant of [Kni26, Lemma 2.3.12]), and a
transformation does not reverse two sources of the same grade (the fixed-grade case of
`TransformsTo.le_of_le`).

**Witnesses bounded by a grade suffice.**  The witnesses of the section theorem, of the normal
forms, and of ownerwise decoding are witnesses bounded by a grade `K`: their suppressor is
`stepSuppressor K` itself, and no witness with another suppressor is brought to that form.  The
laws they need are the rules above (`isWitness_comp_flatten`,
`IsWitness.exists_eq_comp_of_isShort`, `TransformsTo.exists_isWitness_capped`,
`IsWitness.transformsTo_comp`), the replacement of the suppressor by bottom above a grade
(`IsWitness.truncate`) of the library, and the witness laws of the encoders
(`Label.isWitness_spread`, `Label.isWitness_unspread`, `Label.isWitness_blockEncode_stepSuppressor`,
`Label.isWitness_blockDecode_stepSuppressor`, `Label.isWitness_strongEncode`,
`Label.isWitness_strongDecode`, in `VaughtConjecture.Extension.Encoders`).

## Placement

These statements belong in `VaughtConjecture.Label.Transform`, after the guarded composition, with
`IsShort` and `flatten` beside the self-visible labels of `VaughtConjecture.Label.Visibility`, and
the block arithmetic beside the blocks of `VaughtConjecture.Label.OrdinalVisibility`.  They are
stated here so that those files are unchanged.

## References

Witnesses are [Kni26, Definition 2.3.9] and visibility replacement is [Kni26, Definition 2.2.3].
-/

universe u

namespace VaughtConjecture.Label

open Ordinal

/-! ### Block arithmetic -/

section Blocks

variable {a b x y : Ordinal.{u}}

/-- Every ordinal is `ω * b + n` for an ordinal `b` and a natural number `n`. -/
theorem exists_eq_omega0_mul_add_natCast (o : Ordinal.{u}) :
    ∃ (b : Ordinal.{u}) (n : ℕ), o = ω * b + n := by
  obtain ⟨n, hn⟩ := lt_omega0.mp (mod_lt o omega0_ne_zero)
  exact ⟨o / ω, n, by rw [← hn, div_add_mod]⟩

/-- The block of `ω * a + x`, for `x < ω`. -/
theorem omega0_mul_add_div (hx : x < ω) : (ω * a + x) / ω = a := by
  rw [mul_add_div _ omega0_ne_zero, div_eq_zero_of_lt hx, add_zero]

/-- The finite part of `ω * a + x`, for `x < ω`. -/
theorem omega0_mul_add_mod (hx : x < ω) : (ω * a + x) % ω = x := by
  rw [mul_add_mod_self, mod_eq_of_lt hx]

/-- The block of `ω * a + n`, for a natural number `n`. -/
theorem omega0_mul_add_natCast_div (a : Ordinal.{u}) (n : ℕ) : (ω * a + n) / ω = a :=
  omega0_mul_add_div (natCast_lt_omega0 n)

/-- The finite part of `ω * a + n`, for a natural number `n`. -/
theorem omega0_mul_add_natCast_mod (a : Ordinal.{u}) (n : ℕ) : (ω * a + n) % ω = n :=
  omega0_mul_add_mod (natCast_lt_omega0 n)

/-- An ordinal of a lower block lies below every ordinal of a higher block. -/
theorem omega0_mul_add_lt (hx : x < ω) (h : a < b) (y : Ordinal.{u}) :
    ω * a + x < ω * b + y :=
  calc ω * a + x < ω * a + ω := add_lt_add_right hx _
    _ = ω * Order.succ a := (mul_succ _ _).symm
    _ ≤ ω * b := by gcongr; exact Order.succ_le_of_lt h
    _ ≤ ω * b + y := le_self_add

/-- An ordinal of a lower block lies below every ordinal of a higher block, for a natural number
as the finite part of the first. -/
theorem omega0_mul_add_natCast_lt (h : a < b) (n : ℕ) (y : Ordinal.{u}) :
    ω * a + n < ω * b + y :=
  omega0_mul_add_lt (natCast_lt_omega0 n) h y

/-- Ordinals with natural finite parts compare lexicographically in block and finite part. -/
theorem omega0_mul_add_natCast_le_iff {m n : ℕ} :
    ω * a + m ≤ ω * b + n ↔ a < b ∨ a = b ∧ m ≤ n := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases lt_trichotomy a b with hlt | rfl | hgt
    · exact .inl hlt
    · exact .inr ⟨rfl, by exact_mod_cast (add_le_add_iff_left _).mp h⟩
    · exact absurd h (not_le.mpr (omega0_mul_add_natCast_lt hgt n _))
  · rintro (h | ⟨rfl, h⟩)
    · exact (omega0_mul_add_natCast_lt h m _).le
    · exact add_le_add_right (by exact_mod_cast h) _

/-- In one block, ordinals compare as their finite parts. -/
theorem mod_le_mod_of_div_eq (h : x ≤ y) (he : x / ω = y / ω) : x % ω ≤ y % ω := by
  have := div_add_mod x ω ▸ div_add_mod y ω ▸ h
  rwa [he, add_le_add_iff_left] at this

/-- In one block, ordinals compare strictly as their finite parts. -/
theorem mod_lt_mod_of_div_eq (h : x < y) (he : x / ω = y / ω) : x % ω < y % ω := by
  have := div_add_mod x ω ▸ div_add_mod y ω ▸ h
  rwa [he, add_lt_add_iff_left] at this

/-- `ω * n + x` lies below `ω ^ 2` for a natural number `n` and `x < ω`. -/
theorem omega0_mul_natCast_add_lt (n : ℕ) (hx : x < ω) : ω * (n : Ordinal.{u}) + x < ω ^ 2 :=
  calc ω * (n : Ordinal.{u}) + x < ω * ((n + 1 : ℕ) : Ordinal.{u}) + 0 :=
        omega0_mul_add_lt hx (by exact_mod_cast Nat.lt_succ_self n) 0
    _ ≤ ω * ω := by rw [add_zero]; gcongr; exact (natCast_lt_omega0 _).le
    _ = ω ^ 2 := (sq _).symm

/-- Visibility replacement of `ω * a + x`, for `x < ω`, replaces `x`. -/
theorem _root_.Ordinal.visibilityReplace_omega0_mul_add (hx : x < ω) (k i : ℕ) :
    Ordinal.visibilityReplace k i (ω * a + x) = ω * a + if x < k then (i : Ordinal) else x := by
  rw [Ordinal.visibilityReplace, omega0_mul_add_div hx, omega0_mul_add_mod hx]

/-- Visibility replacement of `ω * a + n`, for a natural number `n`, replaces `n`. -/
theorem _root_.Ordinal.visibilityReplace_omega0_mul_add_natCast (a : Ordinal.{u}) (k i n : ℕ) :
    Ordinal.visibilityReplace k i (ω * a + n) =
      ω * a + ((if n < k then i else n : ℕ) : Ordinal.{u}) := by
  rw [Ordinal.visibilityReplace_omega0_mul_add (natCast_lt_omega0 n)]
  split_ifs <;> simp_all

end Blocks

variable {D : Type*} {grade : D → ℕ} {g : ℕ → Label.{u}} {σ τ ν f : Label.{u} → Label.{u}}
  {m K k i : ℕ} {x c : Label.{u}}

/-! ### Short labels and flattening of finite parts -/

/-- A label is **short** at grade `m`: it is bottom, the formal top, or an ordinal whose finite
part is at most `m`.  An owner is short when every entry of its row is short at its grade, and
the section theorem (`CellScheme.Rows.IsLawful.map_of_isShort_or`) needs no other condition at
such an owner.  Shortness of a row is not a consequence of the normal form: the normal forms of
`VaughtConjecture.Extension.NormalForm` have finite parts up to `K + 1`, so they are strongly
coded at `K` but not short at `K`.  Shortness of a new row of full scope is a property of the
construction of that row. -/
def IsShort (m : ℕ) (x : Label.{u}) : Prop := ∀ o : Ordinal.{u}, (o : Label.{u}) = x → o % ω ≤ m

/-- Bottom is short at every grade. -/
@[simp] theorem isShort_bot (m : ℕ) : IsShort m (⊥ : Label.{u}) := fun _ h ↦ absurd h (by simp)

/-- The formal top is short at every grade. -/
@[simp] theorem isShort_top (m : ℕ) : IsShort m (⊤ : Label.{u}) := fun _ h ↦ absurd h (by simp)

/-- An ordinal is short at `m` exactly when its finite part is at most `m`. -/
@[simp] theorem isShort_coe {o : Ordinal.{u}} : IsShort m (o : Label.{u}) ↔ o % ω ≤ m :=
  ⟨fun h ↦ h o rfl, fun h _ he ↦ by rwa [WithTop.coe_injective (WithBot.coe_injective he)]⟩

/-- The flattening of the finite part of an ordinal at `m`: its finite part is replaced by the
smaller of it and `m`, in the same block. -/
noncomputable def flattenOrd (m : ℕ) (o : Ordinal.{u}) : Ordinal.{u} :=
  ω * (o / ω) + min (o % ω) m

/-- The **flattening of finite parts** of labels at `m`: bottom and the formal top are fixed, and an
ordinal `ω * b + n` (`n < ω`) goes to `ω * b + min n m`. -/
noncomputable def flatten (m : ℕ) : Label.{u} → Label.{u} :=
  WithBot.map (WithTop.map (flattenOrd m))

/-- Flattening of finite parts fixes bottom. -/
@[simp] theorem flatten_bot (m : ℕ) : flatten m (⊥ : Label.{u}) = ⊥ := rfl

/-- Flattening of finite parts fixes the formal top. -/
@[simp] theorem flatten_top (m : ℕ) : flatten m (⊤ : Label.{u}) = ⊤ := rfl

/-- Flattening of the finite part of an ordinal label. -/
@[simp] theorem flatten_coe (m : ℕ) (o : Ordinal.{u}) :
    flatten m (o : Label.{u}) = (flattenOrd m o : Label.{u}) := rfl

/-- The flattened finite part is finite. -/
private theorem min_mod_lt (m : ℕ) (o : Ordinal.{u}) : min (o % ω) (m : Ordinal.{u}) < ω :=
  (min_le_left _ _).trans_lt (mod_lt _ omega0_ne_zero)

/-- Flattening of the finite part keeps the block. -/
private theorem flattenOrd_div (m : ℕ) (o : Ordinal.{u}) : flattenOrd m o / ω = o / ω := by
  rw [flattenOrd, omega0_mul_add_div (min_mod_lt m o)]

/-- The finite part after flattening. -/
private theorem flattenOrd_mod (m : ℕ) (o : Ordinal.{u}) :
    flattenOrd m o % ω = min (o % ω) (m : Ordinal.{u}) := by
  rw [flattenOrd, omega0_mul_add_mod (min_mod_lt m o)]

/-- Flattening of finite parts of ordinals is monotone. -/
private theorem flattenOrd_mono (m : ℕ) {o o' : Ordinal.{u}} (h : o ≤ o') :
    flattenOrd m o ≤ flattenOrd m o' := by
  rcases (div_le_left h ω).lt_or_eq with hlt | he
  · exact (omega0_mul_add_lt (min_mod_lt m o) hlt _).le
  · rw [flattenOrd, flattenOrd, he]
    exact add_le_add_right (min_le_min_right _ (mod_le_mod_of_div_eq h he)) _

/-- **Flattening of finite parts is monotone.** -/
theorem monotone_flatten (m : ℕ) : Monotone (flatten m : Label.{u} → Label.{u}) :=
  (Monotone.withTop_map fun _ _ ↦ flattenOrd_mono m).withBot_map

/-- Flattening of finite parts sends a label to bottom only if it is bottom. -/
@[simp] theorem flatten_eq_bot_iff : flatten m x = ⊥ ↔ x = ⊥ := by
  induction x using recBotCoeTop <;> simp

/-- **Flattening of finite parts at `m` fixes the labels short at `m`.** -/
theorem IsShort.flatten_eq (h : IsShort m x) : flatten m x = x := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe o =>
    rw [flatten_coe, flattenOrd, min_eq_left (isShort_coe.mp h), div_add_mod]

/-- **Flattening of finite parts commutes with visibility replacement** at every threshold `k ≤ m`
and every value `i ≤ k`. -/
theorem flatten_visibilityReplace (hk : k ≤ m) (hi : i ≤ k) (x : Label.{u}) :
    flatten m (visibilityReplace k i x) = visibilityReplace k i (flatten m x) := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe o =>
    have hkm : (k : Ordinal.{u}) ≤ m := by exact_mod_cast hk
    have him : (i : Ordinal.{u}) ≤ m := by exact_mod_cast hi.trans hk
    simp only [visibilityReplace_coe, flatten_coe, WithBot.coe_inj, WithTop.coe_inj]
    rw [flattenOrd, Ordinal.visibilityReplace_div, Ordinal.visibilityReplace_mod,
      Ordinal.visibilityReplace, flattenOrd_div, flattenOrd_mod]
    by_cases ho : o % ω < k
    · rw [ite_eq_left ho, ite_eq_left ((min_le_left _ _).trans_lt ho), min_eq_left him]
    · rw [ite_eq_right ho, ite_eq_right (not_lt.mpr (le_min (not_lt.mp ho) hkm))]

/-! ### Repair of the bottom guard -/

/-- A map commuting with visibility replacement at `m` that sends one flattened point of a block
to bottom sends every flattened point of that block to bottom. -/
private theorem apply_flatten_eq_bot (hmono : Monotone f)
    (hcomm : ∀ x, ∀ k ≤ m, ∀ i ≤ k, f (visibilityReplace k i x) = visibilityReplace k i (f x))
    {o o' : Ordinal.{u}} (he : o / ω = o' / ω) (ho : f (flatten m (o : Label.{u})) = ⊥) :
    f (flatten m (o' : Label.{u})) = ⊥ := by
  -- The start `ω * (o / ω)` of the block is sent to bottom.
  have h0 : f ((ω * (o / ω) : Ordinal.{u}) : Label.{u}) = ⊥ :=
    le_bot_iff.mp (ho ▸ hmono (show ((ω * (o / ω) : Ordinal.{u}) : Label.{u}) ≤ flatten m o from
      WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)))
  obtain ⟨n, hn⟩ := lt_omega0.mp (mod_lt o' omega0_ne_zero)
  have hflatten : flattenOrd m o' = ω * (o / ω) + (min n m : ℕ) := by
    rw [flattenOrd, hn, he, Nat.mono_cast.map_min]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [flatten_coe, hflatten, Nat.min_zero, Nat.cast_zero, add_zero, h0]
  · -- Otherwise the flattened point is a replacement of the block start at threshold `m`.
    have hvr : Ordinal.visibilityReplace m (min n m) (ω * (o / ω)) = flattenOrd m o' := by
      rw [hflatten, Ordinal.visibilityReplace_of_lt (by rw [mul_mod]; exact_mod_cast hm),
        mul_div_cancel _ omega0_ne_zero]
    rw [flatten_coe, ← hvr, ← visibilityReplace_coe, hcomm _ m le_rfl _ (min_le_right n m), h0,
      visibilityReplace_bot]

/-- **Repair of the bottom guard.**  A monotone map `f` fixing bottom and commuting with
visibility replacement at every threshold `≤ m` gives the witness `f ∘ flatten m` bounded by grade
`m`.  It gives the composition on short labels (`IsWitness.exists_eq_comp_of_isShort`). -/
theorem isWitness_comp_flatten (hbot : f ⊥ = ⊥) (hmono : Monotone f)
    (hcomm : ∀ x, ∀ k ≤ m, ∀ i ≤ k, f (visibilityReplace k i x) = visibilityReplace k i (f x)) :
    IsWitness (stepSuppressor.{u} m) (f ∘ flatten m) where
  antitone := (IsWitness.id_step m).antitone
  isSelfVisible := (IsWitness.id_step m).isSelfVisible
  map_bot := by simp [hbot]
  monotone := hmono.comp (monotone_flatten m)
  visibilityReplace_comm x k hx i hi := by
    simp only [Function.comp_apply] at hx ⊢
    by_cases hk : k ≤ m
    · rw [flatten_visibilityReplace hk hi, hcomm _ k hk i hi]
    rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
    rw [hx, visibilityReplace_bot]
    induction x using recBotCoeTop with
    | bot => simpa using hbot
    | top => exact hx
    | coe o =>
      rw [visibilityReplace_coe]
      exact apply_flatten_eq_bot hmono hcomm (Ordinal.visibilityReplace_div k i o).symm hx

/-! ### Composition on short labels -/

/-- **Composition without bottom reflection on short labels.**  For a witness `τ` bounded by grade
`m` and a witness `ν` bounded by a grade `K ≥ m`, some witness bounded by grade `m` agrees with
`ν ∘ τ` at every label short at `m`: the composite after flattening of finite parts at `m`.  It
gives the mapped locality of a short row (`TransformsTo.map_of_isShort`), and through it the
locality of the short owners in the section theorem. -/
theorem IsWitness.exists_eq_comp_of_isShort (hτ : IsWitness (stepSuppressor m) τ)
    (hν : IsWitness (stepSuppressor K) ν) (hmK : m ≤ K) :
    ∃ ρ, IsWitness (stepSuppressor.{u} m) ρ ∧ ∀ x, IsShort m x → ρ x = ν (τ x) := by
  refine ⟨(ν ∘ τ) ∘ flatten m, isWitness_comp_flatten (by simp [hτ.map_bot, hν.map_bot])
    (hν.monotone.comp hτ.monotone) fun x k hk i hi ↦ ?_, fun x hx ↦ by simp [hx.flatten_eq]⟩
  simp only [Function.comp_apply]
  rw [hτ.visibilityReplace_comm x k (by simp [hk]) i hi,
    hν.visibilityReplace_comm _ k (by simp [hk.trans hmK]) i hi]

/-! ### The capped witness -/

/-- **Past a self-visible cap below the suppressor, a shifter stays past it at every
replacement.**  If `c` is self-visible at `k`, `c ≤ g k`, and `c < σ x`, then
`c ≤ σ (visibilityReplace k i x)` for every `i ≤ k`.  It is the key step of the capped witness
(`TransformsTo.exists_isWitness_capped`). -/
theorem IsWitness.le_apply_visibilityReplace (hw : IsWitness g σ) (hc : IsSelfVisible k c)
    (hcg : c ≤ g k) (hx : c < σ x) (hi : i ≤ k) : c ≤ σ (visibilityReplace k i x) := by
  by_contra hlt
  rw [not_le] at hlt
  rcases hi.lt_or_eq with hi | rfl
  · -- The label is recovered by a second replacement, with which the shifter commutes.
    obtain ⟨j, hj, hx'⟩ := exists_visibilityReplace_visibilityReplace hi x
    have h := hw.visibilityReplace_comm _ k (hlt.le.trans hcg) j hj.le
    rw [hx'] at h
    exact hx.not_ge (h ▸ visibilityReplace_le_of_le hj.le hc hlt.le)
  · exact hx.not_ge ((hw.monotone (le_visibilityReplace (by omega) x)).trans hlt.le)

/-- **The capped witness.**  Let `c` be a cell of maximal grade whose label `p c` is
self-visible at its grade, and suppose `E ⇒ (d ↦ min (p d) (p c))`.  Then some witness `τ`
bounded by the grade of `c` has all its values at most `p c` and sends each source label exactly
to its capped target, `τ (E d) = min (p d) (p c)`.  It is the first step of the mapped locality
(`TransformsTo.map_of_isShort`, `TransformsTo.map_of_bot_reflecting`), and so of the locality of
an owner in the section theorem. -/
theorem TransformsTo.exists_isWitness_capped {E p : D → Label.{u}} {c : D}
    (hmax : ∀ d, grade d ≤ grade c) (hvis : IsSelfVisible (grade c) (p c))
    (hloc : TransformsTo grade E fun d ↦ min (p d) (p c)) :
    ∃ τ, IsWitness (stepSuppressor.{u} (grade c)) τ ∧ (∀ x, τ x ≤ p c) ∧
      ∀ d, τ (E d) = min (p d) (p c) := by
  by_cases hb : p c = ⊥
  · refine ⟨fun _ ↦ ⊥, IsWitness.bot_top.of_le (fun _ ↦ le_top)
      (IsWitness.id_step _).antitone (IsWitness.id_step _).isSelfVisible, fun _ ↦ bot_le,
      fun d ↦ by simp [hb]⟩
  obtain ⟨g, σ, hw, heq⟩ := hloc
  -- The cap lies below the suppressor at every grade up to that of `c`.
  have hcg (k : ℕ) (hk : k ≤ grade c) : p c ≤ g k := by
    have h := heq c
    simp only [min_self] at h
    exact h.le.trans ((min_le_right _ _).trans (hw.antitone hk))
  refine ⟨fun x ↦ min (σ x) (p c), ⟨(IsWitness.id_step _).antitone,
    (IsWitness.id_step _).isSelfVisible, by simp [hw.map_bot],
    fun _ _ h ↦ min_le_min_right _ (hw.monotone h), fun x k hx i hi ↦ ?_⟩,
    fun _ ↦ min_le_right _ _, fun d ↦ ?_⟩
  · by_cases hk : k ≤ grade c
    · have hck : IsSelfVisible k (p c) := hvis.mono hk
      rcases le_or_gt (σ x) (p c) with hle | hlt
      · rw [min_eq_left hle, hw.visibilityReplace_comm x k (hle.trans (hcg k hk)) i hi,
          min_eq_left (visibilityReplace_le_of_le hi hck hle)]
      · rw [min_eq_right hlt.le, hck.visibilityReplace_eq,
          min_eq_right (hw.le_apply_visibilityReplace hck (hcg k hk) hlt hi)]
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff, min_eq_bot] at hx
      have hσ : σ x = ⊥ := hx.resolve_right hb
      rw [hw.visibilityReplace_comm x k (hσ ▸ bot_le) i hi, hσ]
      simp
  · have h := heq d
    simp only at h
    calc min (σ (E d)) (p c) = min (min (σ (E d)) (g (grade d))) (p c) := by
          rw [min_assoc, min_eq_right (hcg _ (hmax d))]
      _ = min (p d) (p c) := by rw [← h, min_assoc, min_self]

/-! ### Mapped locality -/

/-- **Mapped locality of a short row.**  Let `c` be a cell of maximal grade, at most `K`, whose
label is self-visible at its grade, let the source row `E` be short at the grade of `c`, and let
`ν` be a witness bounded by grade `K`.  A locality `E ⇒ (d ↦ min (p d) (p c))` gives
`E ⇒ (d ↦ min (ν (p d)) (ν (p c)))`; no bottom reflection of `ν` is needed.  It proves the
locality of the short owners in the section theorem (`CellScheme.Rows.IsLawful.map_of_isShort_or`).
-/
theorem TransformsTo.map_of_isShort {E p : D → Label.{u}} {c : D}
    (hmax : ∀ d, grade d ≤ grade c) (hcK : grade c ≤ K) (hshort : ∀ d, IsShort (grade c) (E d))
    (hvis : IsSelfVisible (grade c) (p c)) (hloc : TransformsTo grade E fun d ↦ min (p d) (p c))
    (hν : IsWitness (stepSuppressor K) ν) :
    TransformsTo grade E fun d ↦ min (ν (p d)) (ν (p c)) := by
  obtain ⟨τ, hτ, -, hcap⟩ := hloc.exists_isWitness_capped hmax hvis
  obtain ⟨ρ, hρ, hρτ⟩ := hτ.exists_eq_comp_of_isShort hν hcK
  refine ⟨_, ρ, hρ, fun d ↦ ?_⟩
  rw [stepSuppressor_of_le (hmax d), min_top_right, hρτ _ (hshort d), hcap,
    hν.monotone.map_min]

/-- **Mapped locality through a bottom-reflecting witness.**  As `TransformsTo.map_of_isShort`,
with no condition on the source row and a witness `ν` bounded by grade `K` that sends a label to
bottom only if it is bottom.  It proves that a bottom-reflecting witness maps lawful sections to
lawful sections (`CellScheme.Rows.IsLawful.map_of_bot_reflecting`), and so that the normal form of
a lawful section is lawful (`CellScheme.Rows.IsLawful.strongEncode`). -/
theorem TransformsTo.map_of_bot_reflecting {E p : D → Label.{u}} {c : D}
    (hmax : ∀ d, grade d ≤ grade c) (hcK : grade c ≤ K) (hvis : IsSelfVisible (grade c) (p c))
    (hloc : TransformsTo grade E fun d ↦ min (p d) (p c)) (hν : IsWitness (stepSuppressor K) ν)
    (hbot : ∀ x, ν x = ⊥ → x = ⊥) :
    TransformsTo grade E fun d ↦ min (ν (p d)) (ν (p c)) := by
  obtain ⟨τ, hτ, -, hcap⟩ := hloc.exists_isWitness_capped hmax hvis
  refine ⟨_, _, hτ.comp_of_bot_reflecting (hν.of_le_stepSuppressor hcK) fun x ↦ hbot (τ x),
    fun d ↦ ?_⟩
  rw [stepSuppressor_of_le (hmax d), min_top_right, Function.comp_apply, hcap,
    hν.monotone.map_min]

/-! ### Maximum and postcomposition -/

/-- **The maximum of two shifters** with the same suppressor is a shifter for it: the guard of
the maximum implies the guards of both.  It gives the shifter of the locality of a new cell of
full scope in the completion of a seed: the maximum of the capped witness of an owner
(`TransformsTo.exists_isWitness_capped`) and a second witness bounded by the same grade, with
values in a new block. -/
theorem IsWitness.max (hσ : IsWitness g σ) (hτ : IsWitness g τ) :
    IsWitness g fun x ↦ max (σ x) (τ x) where
  antitone := hσ.antitone
  isSelfVisible := hσ.isSelfVisible
  map_bot := by simp [hσ.map_bot, hτ.map_bot]
  monotone _ _ h := max_le_max (hσ.monotone h) (hτ.monotone h)
  visibilityReplace_comm x k hx i hi := by
    rw [hσ.visibilityReplace_comm x k ((le_max_left _ _).trans hx) i hi,
      hτ.visibilityReplace_comm x k ((le_max_right _ _).trans hx) i hi,
      visibilityReplace_max hi]

/-- **The maximum of finitely many shifters** with the same suppressor, over a nonempty finite
set, is a shifter for it.  It gives the shifter of the interpolation across cells of different
grades in the completion of a seed, the maximum of finitely many shifters with one suppressor,
which enters the decoder of that construction. -/
theorem IsWitness.finsetSup {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {σ : ι → Label.{u} → Label.{u}} (h : ∀ j ∈ s, IsWitness g (σ j)) :
    IsWitness g fun x ↦ s.sup fun j ↦ σ j x := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h a (Finset.mem_singleton_self a)
  | cons a s ha _ ih =>
    simp only [Finset.sup_cons]
    exact (h a (Finset.mem_cons_self a s)).max (ih fun j hj ↦ h j (Finset.mem_cons_of_mem hj))

/-- **Postcomposition.**  On cells of grade at most `K`, every labelling transforms to its image
under a witness bounded by grade `K`.  It proves that a labelling transforms to its normal form
and back (`Label.transformsTo_strongEncode_comp`, `Label.strongEncode_comp_transformsTo`). -/
theorem IsWitness.transformsTo_comp (hν : IsWitness (stepSuppressor K) ν)
    (hK : ∀ d, grade d ≤ K) (p : D → Label.{u}) : TransformsTo grade p (ν ∘ p) :=
  ⟨_, ν, hν, fun d ↦ by rw [stepSuppressor_of_le (hK d), min_top_right, Function.comp_apply]⟩

end VaughtConjecture.Label
