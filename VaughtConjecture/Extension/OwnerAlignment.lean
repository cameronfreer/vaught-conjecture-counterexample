/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.FlattenedSource
import VaughtConjecture.Extension.Restoration
import VaughtConjecture.Label.Band

/-!
# Owner-local alignment

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.4 (the alignment of owners); Layer 1 (guarded
composition retains its guards); semantic contract, item 3.

Let `o` be an owner of grade `m` (a cell with its row `E`) of maximal grade among the cells below
it, and let `p` be a lawful prescription below `o`.  The owner-capped lift of the completion
(`CellScheme.Rows.HasOwnerCappedLifts`) must read `p` capped at the label `p o` literally on the
cells below `o`, while keeping the observation of an ambient labelling at a cap `γ < p o`.  The
ambient is known only through a **source** `s` below `o`: a lawful labelling, **short** at `m`
(`Label.IsShort m`: every finite part at most `m`), with `s o ≠ ⊤`, and a witness `τ` bounded by
grade `m` (a value map with `IsWitness (stepSuppressor m) τ`, a bound on the grades where its guard
is vacuous, not on its values) with `τ ≤ γ` and `τ ∘ s = min p γ`.  The **owner-local alignment**
(`Label.exists_ownerAlignment`, and below a pair
`CellScheme.Rows.IsLawfulBelow.exists_ownerAlignment`) produces

* a **source cap** `h`, with `⊥ < h ≤ s o`, `h ≠ ⊤`, and `h` self-visible at `m`;
* a **reading cap** `δ`, with `γ ≤ δ ≤ p o` and `δ` self-visible at `m`;
* a witness `ρ` bounded by grade `m`, the **alignment decoder**, with `ρ h = δ`,

such that `ρ` reads the prescription from the source capped at `δ`,
`min (p e) δ = min (ρ (s e)) δ`; every cell whose prescription capped at the owner label exceeds
`δ` has its source at least `h` (the **alignment**); and `ρ` agrees with `τ` capped at `γ` at every
label short at `m`.  The source and the prescription are lawful labellings of the same cells; no
relation between them is assumed beyond `τ ∘ s = min p γ`.

**The source cap.**  A cell `e` is *saturated* when `τ (s e) = γ`; the owner is saturated, since
`γ < p o`.  The source cap is the least value of `visibilityReplace m m (s e)` over the saturated
cells: the end `ω * b + m` of the *strip* `[ω * b, ω * b + m]` of `s e` when the finite part of
`s e` is below `m`, and `s e` itself otherwise.  A saturated cell whose source lies below `h` lies
in the strip that ends at `h`.

**The two cases.**  If every cell `e` with `γ < min (p e) (p o)` has `h ≤ s e`, the alignment
holds with `δ = γ` and `ρ = τ`.  Otherwise some such cell `d` has `s d < h`: its source is
`ω * b + i` with `i < m`, and `h = ω * b + m`.  Write `α` and `β` for the capped witnesses of the
localities of `s` and `p` at `o` (`Label.TransformsTo.exists_isWitness_capped`):
`α (E e) = min (s e) (s o)` and `β (E e) = min (p e) (p o)`.  Since `α (E d) = ω * b + i` is not
self-visible at `m`, the row entry `E d` is `ω * b' + i`, and `α` carries the strip of `b'` onto the
strip of `b` point by point (`α (ω * b' + n) = ω * b + n` for `n ≤ m`).  The alignment decoder is
the maximum of `τ` and of `β` after the *block shift* from the strip of `b` to the strip of `b'`,
repaired above `m` by flattening of finite parts (`Label.isWitness_comp_flatten`); the reading
cap is `δ = β (ω * b' + m)`.  It reads every saturated source in the strip of `h` through `β`,
because the strip of `b'` is the only strip that `α` carries onto the strip of `b`, and it reads
every source at least `h` as at least `δ`, because `α` reflects the order at the end of the strip.
In this second case the alignment decoder is **retuned**: it is no longer `τ`, but agrees with `τ`
capped at `γ` on the labels short at `m` and reads the strip of `h` through `β` above `γ`, and its
reading cap `δ` may exceed `γ` (`VaughtConjecture.Extension.AlignmentExamples` shows that it must,
in an example).

**The one-grade step.**  In the one-grade step of the recursion on the grade, `γ` is the cap of
the lift (when it is not `⊥`), `p` the prescription, and `s` the restriction to the cells below
the owner of the row of the full-scope cell that serves the lift: its locality for the ambient,
capped at `γ`, gives `τ`.  The alignment is the input of the aligned encoding
(`VaughtConjecture.Extension.AlignedEncoding`), which builds a lawful labelling of codes below the
owner that agrees with `s` capped at `h` and decodes literally to `p` capped at `p o`.  The
alignment also holds on the flattened source of the prescription
(`CellScheme.Rows.IsLawfulBelow.exists_ownerAlignment_flattenedSource`), the source of
`VaughtConjecture.Extension.FlattenedSource` with its witness.

## Placement

Checkpoint 2.4 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

Witnesses are [Kni26, Definition 2.3.9] and visibility replacement is [Kni26, Definition 2.2.3];
lawful sections are [Kni26, Definition 2.5.4].
-/

universe u

namespace VaughtConjecture.Label

open Ordinal

variable {m i n k : ℕ} {b b' : Ordinal.{u}} {α β τ : Label.{u} → Label.{u}}
  {x z γ : Label.{u}}

/-! ### Points of a block -/

/-- The point `ω * b + n` of the block `b`, as a label. -/
private noncomputable abbrev pt (b : Ordinal.{u}) (n : ℕ) : Label.{u} :=
  ((ω * b + n : Ordinal.{u}) : Label.{u})

/-- Visibility replacement of a point of a block replaces its finite part. -/
private theorem pt_visibilityReplace (b : Ordinal.{u}) (k i n : ℕ) :
    visibilityReplace k i (pt b n) = pt b (if n < k then i else n) := by
  rw [visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast]

/-- Points of blocks compare lexicographically in block and finite part. -/
private theorem pt_le_pt_iff {b b' : Ordinal.{u}} {n n' : ℕ} :
    pt b n ≤ pt b' n' ↔ b < b' ∨ b = b' ∧ n ≤ n' := by
  rw [WithBot.coe_le_coe, WithTop.coe_le_coe, omega0_mul_add_natCast_le_iff]

/-- Points of blocks compare strictly lexicographically in block and finite part. -/
private theorem pt_lt_pt_iff {b b' : Ordinal.{u}} {n n' : ℕ} :
    pt b n < pt b' n' ↔ b < b' ∨ b = b' ∧ n < n' := by
  rw [lt_iff_le_not_ge, pt_le_pt_iff, pt_le_pt_iff]
  constructor
  · rintro ⟨h | ⟨rfl, h⟩, h'⟩
    · exact .inl h
    · exact .inr ⟨rfl, by by_contra hn; exact h' (.inr ⟨rfl, by omega⟩)⟩
  · rintro (h | ⟨rfl, h⟩)
    · exact ⟨.inl h, fun h' ↦ h'.elim (fun h' ↦ h'.asymm h) fun h' ↦ h.ne h'.1.symm⟩
    · exact ⟨.inr ⟨rfl, h.le⟩, fun h' ↦ h'.elim (lt_irrefl _) fun h' ↦ by omega⟩

/-- A point of a block determines its block and its finite part. -/
private theorem pt_inj {b b' : Ordinal.{u}} {n n' : ℕ} (h : pt b n = pt b' n') :
    b = b' ∧ n = n' := by
  rcases (pt_le_pt_iff.mp h.le) with hb | ⟨rfl, hn⟩
  · exact absurd h (pt_lt_pt_iff.mpr (.inl hb)).ne
  · rcases (pt_le_pt_iff.mp h.ge) with hb | ⟨-, hn'⟩
    · exact absurd hb (lt_irrefl _)
    · exact ⟨rfl, le_antisymm hn hn'⟩

/-- A point of a block is self-visible at `k` exactly when its finite part is at least `k`. -/
private theorem isSelfVisible_pt {b : Ordinal.{u}} {k n : ℕ} :
    IsSelfVisible k (pt b n) ↔ k ≤ n := by
  rw [isSelfVisible_coe, omega0_mul_add_natCast_mod, Nat.cast_le]

/-- A point of a block is short at `m` exactly when its finite part is at most `m`. -/
private theorem isShort_pt {b : Ordinal.{u}} {m n : ℕ} : IsShort m (pt b n) ↔ n ≤ m := by
  rw [isShort_coe, omega0_mul_add_natCast_mod, Nat.cast_le]

/-- Every ordinal label is a point of a block. -/
private theorem exists_eq_pt (o : Ordinal.{u}) : ∃ b n, (o : Label.{u}) = pt b n := by
  obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
  exact ⟨b, n, rfl⟩

/-- A point of a block is not bottom. -/
private theorem pt_ne_bot (b : Ordinal.{u}) (n : ℕ) : pt b n ≠ ⊥ := WithBot.coe_ne_bot

/-- The point `ω * b + 0` is the start of the block. -/
private theorem pt_zero (b : Ordinal.{u}) : pt b 0 = ((ω * b : Ordinal.{u}) : Label.{u}) := by
  simp [pt]

/-- The start `ω * b` of a block is zero or a limit. -/
private theorem isSuccPrelimit_omega0_mul (b : Ordinal.{u}) : Order.IsSuccPrelimit (ω * b) :=
  isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right ω b)

/-! ### Strips carried by a witness -/

/-- A witness bounded by grade `m` commutes with every replacement at a threshold `k ≤ m`. -/
private theorem IsWitness.comm_of_le (hα : IsWitness (stepSuppressor m) α) (x : Label.{u})
    (hk : k ≤ m) (hi : i ≤ k) : α (visibilityReplace k i x) = visibilityReplace k i (α x) :=
  hα.visibilityReplace_comm x k (by simp [hk]) i hi

/-- **Strips carried by a witness.**  If a witness `α` bounded by grade `m` sends `x` to the point
`ω * b + i` with `i < m`, then `x` is a point `ω * b' + i`, and `α` carries the strip
`[ω * b', ω * b' + m]` onto the strip `[ω * b, ω * b + m]` point by point. -/
private theorem exists_strip (hα : IsWitness (stepSuppressor m) α) (hi : i < m)
    (hx : α x = pt b i) : ∃ b', x = pt b' i ∧ ∀ n ≤ m, α (pt b' n) = pt b n := by
  have hnv : ¬ IsSelfVisible m x := fun hv ↦ by
    have h := hα.comm_of_le x le_rfl le_rfl
    rw [hv, hx, pt_visibilityReplace, ite_eq_left hi] at h
    exact absurd (pt_inj h).2 (by omega)
  induction x using recBotCoeTop with
  | bot => exact absurd (isSelfVisible_bot m) hnv
  | top => exact absurd (isSelfVisible_top m) hnv
  | coe o =>
    obtain ⟨b', i', ho⟩ := exists_eq_pt o
    rw [ho] at hx hnv ⊢
    have hi' : i' < m := by
      by_contra h
      exact hnv (isSelfVisible_pt.mpr (by omega))
    have horbit (n : ℕ) (hn : n ≤ m) : α (pt b' n) = pt b n := by
      have h := hα.comm_of_le (pt b' i') le_rfl hn
      rw [pt_visibilityReplace, ite_eq_left hi', hx, pt_visibilityReplace, ite_eq_left hi] at h
      exact h
    have hii : i' = i := (pt_inj ((horbit i' hi'.le).symm.trans hx)).2
    subst hii
    exact ⟨b', rfl, horbit⟩

/-- Two strips carried onto the same strip by a monotone map are the same strip. -/
private theorem strip_unique {b₁ b₂ : Ordinal.{u}} (hmono : Monotone α) (hm : 0 < m)
    (h₁ : ∀ n ≤ m, α (pt b₁ n) = pt b n) (h₂ : ∀ n ≤ m, α (pt b₂ n) = pt b n) : b₁ = b₂ := by
  have key {c₁ c₂ : Ordinal.{u}} (hc₁ : ∀ n ≤ m, α (pt c₁ n) = pt b n)
      (hc₂ : ∀ n ≤ m, α (pt c₂ n) = pt b n) : ¬ c₁ < c₂ := fun hlt ↦ by
    have h := hmono (pt_lt_pt_iff.mpr (.inl hlt) : pt c₁ m < pt c₂ 0).le
    rw [hc₁ m le_rfl, hc₂ 0 (Nat.zero_le m), pt_le_pt_iff] at h
    rcases h with h | ⟨-, h⟩
    · exact lt_irrefl _ h
    · omega
  exact le_antisymm (not_lt.mp (key h₂ h₁)) (not_lt.mp (key h₁ h₂))

/-- **The end of a carried strip reflects the order**: a label whose image is at least the end
`ω * b + m` of the image strip is at least the end `ω * b' + m` of the source strip. -/
private theorem pt_le_of_le_apply (hbot : α ⊥ = ⊥) (hmono : Monotone α) (hm : 0 < m)
    (hstrip : ∀ n ≤ m, α (pt b' n) = pt b n) (hz : pt b m ≤ α z) : pt b' m ≤ z := by
  by_contra hlt
  rw [not_le] at hlt
  induction z using recBotCoeTop with
  | bot => exact absurd (hz.trans_eq hbot) (not_le.mpr (WithBot.bot_lt_coe _))
  | top => exact absurd hlt (not_lt.mpr le_top)
  | coe o =>
    obtain ⟨c, n, ho⟩ := exists_eq_pt o
    rw [ho] at hz hlt
    rcases pt_lt_pt_iff.mp hlt with hc | ⟨rfl, hn⟩
    · have h := hz.trans (hmono (pt_lt_pt_iff.mpr (.inl hc) : pt c n < pt b' 0).le)
      rw [hstrip 0 (Nat.zero_le m), pt_le_pt_iff] at h
      rcases h with h | ⟨-, h⟩
      · exact lt_irrefl _ h
      · omega
    · rw [hstrip n hn.le, pt_le_pt_iff] at hz
      rcases hz with h | ⟨-, h⟩
      · exact lt_irrefl _ h
      · omega

/-- **The preimage of a point of a carried strip**: a label sent to the point `ω * b + n`,
`n < m`, of the image strip is the point `ω * b' + n` of the source strip. -/
private theorem eq_pt_of_apply_eq (hα : IsWitness (stepSuppressor m) α) (hn : n < m)
    (hstrip : ∀ k ≤ m, α (pt b' k) = pt b k) (hz : α z = pt b n) : z = pt b' n := by
  obtain ⟨b'', rfl, h''⟩ := exists_strip hα hn hz
  rw [strip_unique hα.monotone (by omega) h'' hstrip]

/-- **The floor bound**: a lower bound self-visible at `m` of a witness bounded by grade `m` at a
point `ω * b + i`, `i < m`, is a lower bound at the start of the block. -/
private theorem le_apply_pt_zero (hβ : IsWitness (stepSuppressor m) β) (hi : i < m)
    (hγ : IsSelfVisible m γ) (h : γ ≤ β (pt b i)) : γ ≤ β (pt b 0) := by
  have he := hβ.comm_of_le (pt b i) le_rfl (Nat.zero_le m)
  rw [pt_visibilityReplace, ite_eq_left hi] at he
  rw [he, ← hγ.visibilityReplace_eq 0]
  exact monotone_visibilityReplace (Nat.zero_le m) h

/-! ### The block shift -/

open Classical in
/-- The block shift from the strip of `b` to the strip of `b'` at `m`: bottom below the block `b`;
`ω * b + n ↦ ω * b' + min n m` on the block `b`; and `ω * b' + m` above it. -/
private noncomputable def blockShift (b b' : Ordinal.{u}) (m : ℕ) (x : Label.{u}) : Label.{u} :=
  if x < ((ω * b : Ordinal.{u}) : Label.{u}) then ⊥ else bandMap (ω * b') (ω * b) m x

/-- Below the block `b` the block shift is bottom. -/
private theorem blockShift_of_lt (h : x < ((ω * b : Ordinal.{u}) : Label.{u})) :
    blockShift b b' m x = ⊥ := ite_eq_left h

/-- From the block `b` on, the block shift is the band map. -/
private theorem blockShift_of_le (h : ((ω * b : Ordinal.{u}) : Label.{u}) ≤ x) :
    blockShift b b' m x = bandMap (ω * b') (ω * b) m x := ite_eq_right (not_lt.mpr h)

/-- The block shift carries the strip of `b` onto the strip of `b'` point by point. -/
private theorem blockShift_pt (hn : n ≤ m) : blockShift b b' m (pt b n) = pt b' n := by
  rw [blockShift_of_le (by rw [← pt_zero]; exact pt_le_pt_iff.mpr (.inr ⟨rfl, Nat.zero_le n⟩)),
    bandMap_coe_add_natCast, min_eq_left hn]

/-- The block shift is bottom, or its argument lies at or above the block `b` and its value at or
above the block `b'`. -/
private theorem blockShift_eq_bot_or (x : Label.{u}) :
    blockShift b b' m x = ⊥ ∨ ((ω * b : Ordinal.{u}) : Label.{u}) ≤ x ∧
      ((ω * b' : Ordinal.{u}) : Label.{u}) ≤ blockShift b b' m x := by
  by_cases h : x < ((ω * b : Ordinal.{u}) : Label.{u})
  · exact .inl (blockShift_of_lt h)
  · have hx : x ≠ ⊥ := fun hx ↦ h (hx ▸ WithBot.bot_lt_coe _)
    exact .inr ⟨not_lt.mp h, (blockShift_of_le (not_lt.mp h)).symm ▸ coe_le_bandMap hx⟩

/-- **The block shift is a witness bounded by grade `m`.** -/
private theorem isWitness_blockShift (b b' : Ordinal.{u}) (m : ℕ) :
    IsWitness (stepSuppressor.{u} m) (blockShift b b' m) where
  antitone := (IsWitness.id_step m).antitone
  isSelfVisible := (IsWitness.id_step m).isSelfVisible
  map_bot := blockShift_of_lt (WithBot.bot_lt_coe _)
  monotone x y hxy := by
    by_cases hy : y < ((ω * b : Ordinal.{u}) : Label.{u})
    · rw [blockShift_of_lt (hxy.trans_lt hy)]; exact bot_le
    by_cases hx : x < ((ω * b : Ordinal.{u}) : Label.{u})
    · rw [blockShift_of_lt hx]; exact bot_le
    rw [blockShift_of_le (not_lt.mp hx), blockShift_of_le (not_lt.mp hy)]
    exact monotone_bandMap _ _ _ hxy
  visibilityReplace_comm x k hx i hi := by
    have hlt : visibilityReplace k i x < ((ω * b : Ordinal.{u}) : Label.{u}) ↔
        x < ((ω * b : Ordinal.{u}) : Label.{u}) :=
      visibilityReplace_lt_iff (isSuccPrelimit_omega0_mul b)
    by_cases hxb : x < ((ω * b : Ordinal.{u}) : Label.{u})
    · rw [blockShift_of_lt hxb, blockShift_of_lt (hlt.mpr hxb), visibilityReplace_bot]
    by_cases hk : k ≤ m
    · rw [blockShift_of_le (not_lt.mp hxb), blockShift_of_le (not_lt.mp (mt hlt.mp hxb)),
        bandMap_visibilityReplace (isSuccPrelimit_omega0_mul b') (isSuccPrelimit_omega0_mul b) hk
          hi (not_lt.mp hxb)]
    · -- Above `m` the guard forces the value bottom, which happens only below the block.
      rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
      have hne : x ≠ ⊥ := fun h ↦ hxb (h ▸ WithBot.bot_lt_coe _)
      have h := (blockShift_of_le (b' := b') (m := m) (not_lt.mp hxb)).symm ▸ coe_le_bandMap hne
      exact absurd (hx ▸ h) (not_le.mpr (WithBot.bot_lt_coe _))

/-! ### Retuning a saturated strip -/

/-- **Retuning a saturated strip** (the construction of the retuned decoder of the second case of
the alignment, see the module docstring).  Let `α`, `β`, `τ` be witnesses bounded by grade `m`, let
`α x = ω * b + i` with `i < m`, let `τ ≤ γ` with `γ` self-visible at `m`, `τ (ω * b + i) = γ`, and
`γ ≤ β x ≤ M`.  Some witness `ρ` bounded by grade `m` and some `δ` with `γ ≤ δ ≤ M`, self-visible
at `m`, have: `ρ (ω * b + m) = δ`; `ρ (α z) = β z` whenever `α z` lies in the strip of `b` below
its end; `δ ≤ β z` whenever `α z` is at least the end of the strip; and `ρ` agrees with `τ`
capped at `γ` at every label short at `m`. -/
private theorem exists_retuning {M : Label.{u}} (hα : IsWitness (stepSuppressor m) α)
    (hβ : IsWitness (stepSuppressor m) β) (hτ : IsWitness (stepSuppressor m) τ) (hi : i < m)
    (hx : α x = pt b i) (hγ : IsSelfVisible m γ) (hτγ : ∀ z, τ z ≤ γ) (hsat : τ (pt b i) = γ)
    (hp : γ ≤ β x) (hβM : ∀ z, β z ≤ M) :
    ∃ ρ δ, IsWitness (stepSuppressor.{u} m) ρ ∧ γ ≤ δ ∧ δ ≤ M ∧ IsSelfVisible m δ ∧
      ρ (pt b m) = δ ∧ (∀ z n, n < m → α z = pt b n → ρ (α z) = β z) ∧
      (∀ z, pt b m ≤ α z → δ ≤ β z) ∧ ∀ z, IsShort m z → min (ρ z) γ = min (τ z) γ := by
  obtain ⟨b', rfl, hstrip⟩ := exists_strip hα hi hx
  have hbf : γ ≤ β (pt b' 0) := le_apply_pt_zero hβ hi hγ hp
  have htf : τ (pt b 0) = γ := le_antisymm (hτγ _) (le_apply_pt_zero hτ hi hγ hsat.ge)
  have hβmono (n : ℕ) : β (pt b' 0) ≤ β (pt b' n) :=
    hβ.monotone (pt_le_pt_iff.mpr (.inr ⟨rfl, Nat.zero_le n⟩))
  -- The composite of the block shift and `β`, repaired above `m` by flattening.
  have hη := isWitness_blockShift b b' m
  have hκ : IsWitness (stepSuppressor m) ((β ∘ blockShift b b' m) ∘ flatten m) :=
    isWitness_comp_flatten (by simp [hη.map_bot, hβ.map_bot]) (hβ.monotone.comp hη.monotone)
      fun z k hk i hi ↦ by
        simp only [Function.comp_apply]
        rw [hη.comm_of_le z hk hi, hβ.comm_of_le _ hk hi]
  have hκshort (z : Label.{u}) (hz : IsShort m z) :
      ((β ∘ blockShift b b' m) ∘ flatten m) z = β (blockShift b b' m z) := by
    simp only [Function.comp_apply, hz.flatten_eq]
  set ρ : Label.{u} → Label.{u} :=
    fun z ↦ max (τ z) (((β ∘ blockShift b b' m) ∘ flatten m) z) with hρ_def
  have hρ : IsWitness (stepSuppressor m) ρ := hτ.max hκ
  have hρstrip (n : ℕ) (hn : n ≤ m) : ρ (pt b n) = β (pt b' n) := by
    simp only [hρ_def]
    rw [hκshort _ (isShort_pt.mpr hn), blockShift_pt hn]
    exact max_eq_right ((hτγ _).trans (hbf.trans (hβmono n)))
  have hδvis : IsSelfVisible m (β (pt b' m)) := by
    have h := hβ.comm_of_le (pt b' m) le_rfl le_rfl
    rw [pt_visibilityReplace, ite_eq_right (lt_irrefl m)] at h
    exact h.symm
  refine ⟨ρ, β (pt b' m), hρ, hbf.trans (hβmono m), hβM _, hδvis, hρstrip m le_rfl,
    fun z n hn hz ↦ ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hz, hρstrip n hn.le, eq_pt_of_apply_eq hα hn hstrip hz]
  · exact hβ.monotone (pt_le_of_le_apply hα.map_bot hα.monotone (by omega) hstrip hz)
  · simp only [hρ_def]
    rw [hκshort z hz]
    rcases blockShift_eq_bot_or (b := b) (b' := b') (m := m) z with h | ⟨hzb, hηz⟩
    · rw [h, hβ.map_bot, max_bot_right]
    · have hτz : τ z = γ := le_antisymm (hτγ z) (htf ▸ hτ.monotone (pt_zero b ▸ hzb))
      have hβz : γ ≤ β (blockShift b b' m z) := hbf.trans (hβ.monotone (pt_zero b' ▸ hηz))
      rw [hτz, max_eq_right hβz, min_eq_right hβz, min_self]

/-! ### The owner-local alignment -/

/-- The source cap lies below the visibility replacement at `m` of every saturated source. -/
private theorem exists_sourceCap {I : Type*} [Finite I] {s : I → Label.{u}} {o : I}
    (ho : τ (s o) = γ) :
    ∃ e₀, τ (s e₀) = γ ∧
      ∀ e, τ (s e) = γ → visibilityReplace m m (s e₀) ≤ visibilityReplace m m (s e) := by
  classical
  have := Fintype.ofFinite I
  obtain ⟨e₀, he₀, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun e ↦ τ (s e) = γ)
    (fun e ↦ visibilityReplace m m (s e)) ⟨o, by simp [ho]⟩
  exact ⟨e₀, (Finset.mem_filter.mp he₀).2, fun e he ↦ hmin e (by simp [he])⟩

/-- **The owner-local alignment**, on a finite family of cells.  Let `o` be a cell of maximal
grade `m` (`grade o = m`), `E` its row, and `s`, `p` labellings of the cells with labels at `o`
self-visible at `m` and localities `E ⇒ (e ↦ min (s e) (s o))` and `E ⇒ (e ↦ min (p e) (p o))`.
Let `s` be short at `m` with `s o ≠ ⊤`, and let `τ` be a witness bounded by grade `m` with `τ ≤ γ`
and `τ ∘ s = min p γ`, where `⊥ < γ < p o` and `γ` is self-visible at `m`.  Then some source cap
`h`, reading cap `δ`, and alignment decoder `ρ` satisfy:

* `⊥ < h ≤ s o`, `h ≠ ⊤`, `h` self-visible at `m`;
* `ρ` is a witness bounded by grade `m`; `γ ≤ δ ≤ p o`, `δ` self-visible at `m`, and `ρ h = δ`;
* `min (p e) δ = min (ρ (s e)) δ` at every cell;
* the alignment: `h ≤ s e` at every cell with `δ < min (p e) (p o)`;
* `min (ρ z) γ = min (τ z) γ` at every label `z` short at `m`.

It is the alignment of the one-grade step at a positive cap (see the module docstring), and the
input of the aligned encoding
(`CellScheme.Rows.IsLawfulBelow.exists_alignedEncoding`). -/
theorem exists_ownerAlignment {I : Type*} [Finite I] {grade : I → ℕ} {E s p : I → Label.{u}}
    {o : I} (hmax : ∀ e, grade e ≤ m) (hom : grade o = m) (hso : IsSelfVisible m (s o))
    (hlocs : TransformsTo grade E fun e ↦ min (s e) (s o)) (hpo : IsSelfVisible m (p o))
    (hlocp : TransformsTo grade E fun e ↦ min (p e) (p o))
    (hshort : ∀ e, IsShort m (s e)) (htop : s o ≠ ⊤)
    (hτ : IsWitness (stepSuppressor m) τ) (hτγ : ∀ x, τ x ≤ γ)
    (hface : ∀ e, τ (s e) = min (p e) γ) (hγ : IsSelfVisible m γ) (hγbot : ⊥ < γ)
    (hγo : γ < p o) :
    ∃ h δ ρ, ⊥ < h ∧ h ≠ ⊤ ∧ IsSelfVisible m h ∧ h ≤ s o ∧
      IsWitness (stepSuppressor.{u} m) ρ ∧ γ ≤ δ ∧ δ ≤ p o ∧
      IsSelfVisible m δ ∧ ρ h = δ ∧ (∀ e, min (p e) δ = min (ρ (s e)) δ) ∧
      (∀ e, δ < min (p e) (p o) → h ≤ s e) ∧
      ∀ z, IsShort m z → min (ρ z) γ = min (τ z) γ := by
  subst hom
  set m := grade o with hm_def
  have hosat : τ (s o) = γ := by rw [hface o, min_eq_right hγo.le]
  -- The source cap: the least replacement at `m` of a saturated source.
  obtain ⟨e₀, he₀, hmin⟩ := exists_sourceCap (m := m) hosat
  set h := visibilityReplace m m (s e₀) with hh_def
  have hhvis : IsSelfVisible m h := isSelfVisible_visibilityReplace_self m _
  have hhτ : τ h = γ :=
    le_antisymm (hτγ h) (he₀ ▸ hτ.monotone (le_visibilityReplace (by omega) (s e₀)))
  have hhbot : ⊥ < h := bot_lt_iff_ne_bot.mpr fun hb ↦ by
    rw [hb, hτ.map_bot] at hhτ
    exact hγbot.ne hhτ
  have hho : h ≤ s o := (hmin o hosat).trans_eq hso
  have hhtop : h ≠ ⊤ := ne_top_of_le_ne_top htop hho
  -- A saturated source below the source cap lies in the strip that ends at the source cap.
  have hstripCap (e : I) (he : τ (s e) = γ) (hlt : s e < h) :
      visibilityReplace m m (s e) = h :=
    le_antisymm ((monotone_visibilityReplace le_rfl hlt.le).trans_eq hhvis) (hmin e he)
  by_cases halign : ∀ e, γ < min (p e) (p o) → h ≤ s e
  · -- The first case: `δ = γ` and `ρ = τ`.
    refine ⟨h, γ, τ, hhbot, hhtop, hhvis, hho, hτ, le_rfl, hγo.le, hγ, hhτ, fun e ↦ ?_, halign,
      fun _ _ ↦ rfl⟩
    rw [hface e, min_assoc, min_self]
  push Not at halign
  obtain ⟨d, hpd, hsd⟩ := halign
  have hdsat : τ (s d) = γ := by
    rw [hface d, min_eq_right (hpd.trans_le (min_le_left _ _)).le]
  -- The source cap is the end `ω * b + m` of the strip of `s d`, which has finite part `i < m`.
  have hstrip_of (e : I) (he : τ (s e) = γ) (hlt : s e < h) :
      ∃ b n, n < m ∧ s e = pt b n ∧ h = pt b m := by
    have hv := hstripCap e he hlt
    induction hse : s e using recBotCoeTop with
    | bot => rw [hse, visibilityReplace_bot] at hv; exact absurd hv.symm hhbot.ne'
    | top => rw [hse] at hlt; exact absurd hlt (not_lt.mpr le_top)
    | coe o' =>
      obtain ⟨b, n, ho'⟩ := exists_eq_pt o'
      rw [hse, ho', pt_visibilityReplace] at hv
      rw [hse, ho'] at hlt
      by_cases hn : n < m
      · rw [ite_eq_left hn] at hv
        exact ⟨b, n, hn, ho', hv.symm⟩
      · rw [ite_eq_right hn] at hv
        exact absurd hv.symm hlt.ne'
  obtain ⟨b, i, hi, hsdi, hhb⟩ := hstrip_of d hdsat hsd
  -- The capped witnesses of the two localities at the owner.
  obtain ⟨α, hα, -, hαread⟩ := hlocs.exists_isWitness_capped hmax hso
  obtain ⟨β, hβ, hβle, hβread⟩ := hlocp.exists_isWitness_capped hmax hpo
  have hαlow (e : I) (he : s e < h) : α (E e) = s e :=
    (hαread e).trans (min_eq_left (he.le.trans hho))
  obtain ⟨ρ, δ, hρ, hγδ, hδo, hδvis, hρend, htransfer, habove, hcap⟩ :=
    exists_retuning (x := E d) hα hβ hτ hi ((hαlow d hsd).trans hsdi) hγ hτγ (hsdi ▸ hdsat)
      (by rw [hβread d]; exact hpd.le) hβle
  have hρh : ρ h = δ := hhb ▸ hρend
  -- Below the source cap, `ρ` reads the prescription capped at the owner label.
  have hsub (e : I) (he : s e < h) : min (p e) (p o) = ρ (s e) := by
    by_cases hlo : τ (s e) < γ
    · have hpe : p e = τ (s e) := by
        rw [hface e] at hlo ⊢
        exact (min_eq_left ((min_lt_iff.mp hlo).resolve_right (lt_irrefl γ)).le).symm
      have hρe : ρ (s e) = τ (s e) := by
        have h' := hcap (s e) (hshort e)
        rw [min_eq_left (hτγ _)] at h'
        have hργ : ρ (s e) < γ := by
          by_contra hc
          rw [min_eq_right (not_lt.mp hc)] at h'
          exact hlo.ne' h'
        rwa [min_eq_left hργ.le] at h'
      rw [hpe, hρe, min_eq_left (hlo.le.trans hγo.le)]
    · have hesat : τ (s e) = γ := le_antisymm (hτγ _) (not_lt.mp hlo)
      obtain ⟨b₁, n, hn, hsen, hhb₁⟩ := hstrip_of e hesat he
      have hb₁ : b₁ = b := (pt_inj (hhb₁.symm.trans hhb)).1
      subst hb₁
      have h' := htransfer (E e) n hn ((hαlow e he).trans hsen)
      rw [hαlow e he, hβread e] at h'
      exact h'.symm
  refine ⟨h, δ, ρ, hhbot, hhtop, hhvis, hho, hρ, hγδ, hδo, hδvis, hρh, fun e ↦ ?_, fun e he ↦ ?_,
    hcap⟩
  · by_cases he : s e < h
    · rw [← hsub e he, min_assoc, min_eq_right hδo]
    · have hle : pt b m ≤ α (E e) := by
        rw [hαread e, ← hhb]
        exact le_min (not_lt.mp he) hho
      have hδp : δ ≤ p e := (habove _ hle).trans ((hβread e).le.trans (min_le_left _ _))
      rw [min_eq_right hδp, min_eq_right (hρh ▸ hρ.monotone (not_lt.mp he))]
  · by_contra hn
    have hle : min (p e) (p o) ≤ δ := by
      rw [hsub e (not_le.mp hn), ← hρh]
      exact hρ.monotone (not_le.mp hn).le
    exact absurd he (not_lt.mpr hle)

end VaughtConjecture.Label

namespace VaughtConjecture.CellScheme.Rows

open Label

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {X : Finset α × ℕ}
  {τ : Label.{u} → Label.{u}} {γ : Label.{u}}

/-- **The owner-local alignment below a pair.**  Let `o` be a cell of graded index `X` below `X`,
on finitely many cells, let `s` and `p` be lawful below `X`, `s` short at the grade of `X` with
`s o ≠ ⊤`, and let `τ` be a witness bounded by the grade of `X` with `τ ≤ γ` and
`τ ∘ s = min p γ`, where `⊥ < γ < p o` and `γ` is self-visible at the grade of `X`.  Then some
source cap `h`, reading cap `δ`, and alignment decoder `ρ` satisfy the conclusions of
`Label.exists_ownerAlignment`, at the grade of `X`.  In the one-grade step, `X = (C, j + 1)`, `p` is
the prescription, `o` its owner, `γ` the cap of the lift, and `s` the source below the owner; the
result is the input of the aligned encoding (`CellScheme.Rows.IsLawfulBelow.alignedEncode`). -/
theorem IsLawfulBelow.exists_ownerAlignment [Finite (D.below X)] {s p : D.below X → Label.{u}}
    (hs : R.IsLawfulBelow X s) (hp : R.IsLawfulBelow X p) {o : D.below X}
    (ho : D.gradedIndex o = X) (hshort : ∀ e, IsShort X.2 (s e)) (htop : s o ≠ ⊤)
    (hτ : IsWitness (stepSuppressor X.2) τ) (hτγ : ∀ x, τ x ≤ γ)
    (hface : ∀ e, τ (s e) = min (p e) γ) (hγ : IsSelfVisible X.2 γ) (hγbot : ⊥ < γ)
    (hγo : γ < p o) :
    ∃ h δ ρ, ⊥ < h ∧ h ≠ ⊤ ∧ IsSelfVisible X.2 h ∧ h ≤ s o ∧
      IsWitness (stepSuppressor.{u} X.2) ρ ∧ γ ≤ δ ∧ δ ≤ p o ∧ IsSelfVisible X.2 δ ∧ ρ h = δ ∧
      (∀ e, min (p e) δ = min (ρ (s e)) δ) ∧ (∀ e, δ < min (p e) (p o) → h ≤ s e) ∧
      ∀ z, IsShort X.2 z → min (ρ z) γ = min (τ z) γ := by
  classical
  -- The cells below the owner are the cells below `X`.
  have hmem (e : D.below X) : e.1 ∈ D.below (D.gradedIndex o.1) := le_trans e.2 ho.ge
  have hgrade : D.grade o.1 = X.2 := congrArg Prod.snd ho
  have hcells : D.below (D.gradedIndex o.1) = D.below X := by rw [ho]
  have : Finite (D.below (D.gradedIndex o.1)) := by rw [hcells]; infer_instance
  have hext (w : D.below X → Label.{u}) (d : D.below (D.gradedIndex o.1)) :
      extendBot X w d = w ⟨d.1, le_trans d.2 ho.le⟩ := extendBot_of_mem w _
  have hexte (w : D.below X → Label.{u}) (e : D.below X) : extendBot X w e.1 = w e :=
    extendBot_of_mem w e.2
  have hloc (w : D.below X → Label.{u}) (hw : R.IsLawfulBelow X w) :
      TransformsTo (fun d : D.below (D.gradedIndex o.1) ↦ D.grade d) (R.row o.1)
        fun d ↦ min (extendBot X w d) (extendBot X w o.1) :=
    (isLawfulBelow_iff_forall.mp (isLawfulBelow_extendBot.mpr hw)).2.1 o.1 o.2
  have hvis (w : D.below X → Label.{u}) (hw : R.IsLawfulBelow X w) :
      IsSelfVisible X.2 (extendBot X w o.1) := by
    rw [hexte]
    exact hgrade ▸ (isLawfulBelow_iff.mp hw).orderly o
  obtain ⟨h, δ, ρ, hhbot, hhtop, hhvis, hho, hρ, hγδ, hδo, hδvis, hρh, hread, halign, hcap⟩ :=
    Label.exists_ownerAlignment (I := D.below (D.gradedIndex o.1))
      (grade := fun d ↦ D.grade d) (E := R.row o.1) (s := fun d ↦ extendBot X s d)
      (p := fun d ↦ extendBot X p d) (o := ⟨o.1, D.mem_below_gradedIndex o.1⟩) (τ := τ) (γ := γ)
      (fun d ↦ hgrade ▸ d.2.2) hgrade (hvis s hs) (hloc s hs) (hvis p hp) (hloc p hp)
      (fun d ↦ by rw [hext]; exact hshort _) (by rwa [hexte]) hτ hτγ
      (fun d ↦ by rw [hext, hext]; exact hface _) hγ hγbot (by rwa [hexte])
  simp only [hexte] at hho hδo halign
  refine ⟨h, δ, ρ, hhbot, hhtop, hhvis, hho, hρ, hγδ, hδo, hδvis, hρh, fun e ↦ ?_, fun e he ↦ ?_,
    hcap⟩
  · have h' := hread ⟨e.1, hmem e⟩
    simp only [hexte] at h'
    exact h'
  · have h' := halign ⟨e.1, hmem e⟩
    simp only [hexte] at h'
    exact h' he

/-- **The owner-local alignment on the flattened source of the prescription.**  For `p` lawful
below `X` with values in `V`, on finitely many cells, and an owner `o` of graded index `X` with
`⊥ < γ < p o`, `γ` self-visible at the grade of `X`, the alignment holds with the source
`flattenedSource V X.2 p` and the witness `τ` that comes with it
(`CellScheme.Rows.IsLawfulBelow.flattenedSource_prescription`), which decodes it capped at `γ`. -/
theorem IsLawfulBelow.exists_ownerAlignment_flattenedSource [Finite (D.below X)]
    {V : Finset Label.{u}} {p : D.below X → Label.{u}} (hp : R.IsLawfulBelow X p)
    (hV : ∀ e, p e ∈ V) {o : D.below X} (ho : D.gradedIndex o = X) (hγ : IsSelfVisible X.2 γ)
    (hγbot : ⊥ < γ) (hγo : γ < p o) :
    ∃ τ, IsWitness (stepSuppressor.{u} X.2) τ ∧ (∀ x, τ x ≤ γ) ∧
      (∀ e, τ (Label.flattenedSource V X.2 p e) = min (p e) γ) ∧
      ∃ h δ ρ, ⊥ < h ∧ h ≠ ⊤ ∧ IsSelfVisible X.2 h ∧ h ≤ Label.flattenedSource V X.2 p o ∧
        IsWitness (stepSuppressor.{u} X.2) ρ ∧ γ ≤ δ ∧ δ ≤ p o ∧ IsSelfVisible X.2 δ ∧
        ρ h = δ ∧ (∀ e, min (p e) δ = min (ρ (Label.flattenedSource V X.2 p e)) δ) ∧
        (∀ e, δ < min (p e) (p o) → h ≤ Label.flattenedSource V X.2 p e) ∧
        ∀ z, IsShort X.2 z → min (ρ z) γ = min (τ z) γ := by
  obtain ⟨hs, hshort, -, htop, -, -, hτex⟩ := hp.flattenedSource_prescription hV
  obtain ⟨τ, hτ, hτγ, hface⟩ := hτex γ hγ
  exact ⟨τ, hτ, hτγ, hface, hs.exists_ownerAlignment hp ho hshort (htop o) hτ hτγ hface hγ hγbot
    hγo⟩

end VaughtConjecture.CellScheme.Rows
