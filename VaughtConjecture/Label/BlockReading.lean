/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.BlockCode

/-!
# Reading blocks through a decoder

Roadmap, Layer 3 (the template of the growth construction).

Let `θ` be monotone and commute with visibility replacement at every threshold `k ≤ N` with every
value `i ≤ k` (as the capped decoder of a section at the cap does, `Scheme.exists_cappedDecoder`).
If `θ` reads an ordinal code `s` as `μ + j` (`μ` zero or a limit, `j < N`), then:

* the finite part of `s` is `j` (`Label.finNat_eq_of_read`);
* codes read in the same block lie in one block (`Label.blockOf_eq_of_read`), and codes read in
  increasing blocks lie in increasing blocks (`Label.blockOf_lt_of_read`);
* below a code `sa` read as `⊤`, the block of `s` plus `N` is at most the replacement of `sa` at
  the threshold `N` with value `R < N`, whose finite part is at least `R`
  (`Label.blockOf_add_le_of_read_top`).

These are the facts by which the strips of a block code are read off the cap's row.

## References

Visibility replacement is [Kni26, Definition 2.2.3].
-/

universe u

namespace VaughtConjecture.Label

open Ordinal

variable {θ : Label.{u} → Label.{u}} {N : ℕ}

/-- Ordinal labels are equal exactly when the ordinals are. -/
theorem coe_inj' {a b : Ordinal.{u}} : (a : Label.{u}) = (b : Label.{u}) ↔ a = b := by
  constructor
  · intro h; exact WithTop.coe_injective (WithBot.coe_injective h)
  · rintro rfl; rfl

theorem coe_lt_coe_iff {a b : Ordinal.{u}} : (a : Label.{u}) < (b : Label.{u}) ↔ a < b := by
  rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe]

/-- Visibility replacement of a block start plus a finite part, at a threshold above it. -/
theorem visibilityReplace_blockOf_of_lt {o : Ordinal.{u}} {k : ℕ} (h : finNat o < k) (i : ℕ) :
    Ordinal.visibilityReplace k i o = blockOf o + i := by
  rw [visibilityReplace_eq_blockOf, ite_eq_left h]

theorem visibilityReplace_blockOf_of_le {o : Ordinal.{u}} {k : ℕ} (h : k ≤ finNat o) (i : ℕ) :
    Ordinal.visibilityReplace k i o = o := by
  rw [visibilityReplace_eq_blockOf, ite_eq_right (not_lt.mpr h), blockOf_add_finNat]

section Read

variable (hθm : Monotone θ)
  (hθv : ∀ k ≤ N, ∀ i ≤ k, ∀ x, θ (visibilityReplace k i x) = visibilityReplace k i (θ x))
include hθv

/-- **The finite part is read**: a code read as `μ + j`, `j < N`, has finite part `j`. -/
theorem finNat_eq_of_read {s μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) {j : ℕ} (hj : j < N)
    (hs : θ (s : Label.{u}) = ((μ + j : Ordinal.{u}) : Label.{u})) : finNat s = j := by
  by_cases hf : finNat s < j + 1
  · have h1 := hθv (j + 1) hj (finNat s) hf.le (s : Label.{u})
    rw [visibilityReplace_coe, visibilityReplace_blockOf_of_lt hf, blockOf_add_finNat, hs,
      visibilityReplace_coe_add hμ, ite_eq_left (Nat.lt_succ_self j)] at h1
    have h2 := coe_inj'.mp h1
    exact_mod_cast ((add_left_cancel h2).symm)
  · have h1 := hθv (j + 1) hj (j + 1) le_rfl (s : Label.{u})
    rw [visibilityReplace_coe, visibilityReplace_blockOf_of_le (not_lt.mp hf), hs,
      visibilityReplace_coe_add hμ, ite_eq_left (Nat.lt_succ_self j)] at h1
    have h2 := add_left_cancel (coe_inj'.mp h1)
    exact absurd (by exact_mod_cast h2 : j = j + 1) (Nat.succ_ne_self j).symm

include hθm in
/-- **Codes read in one block lie in one block.** -/
theorem blockOf_eq_of_read (hN : 0 < N) {s s' μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ)
    {j j' : ℕ} (hj : j < N) (hj' : j' < N)
    (hs : θ (s : Label.{u}) = ((μ + j : Ordinal.{u}) : Label.{u}))
    (hs' : θ (s' : Label.{u}) = ((μ + j' : Ordinal.{u}) : Label.{u})) : blockOf s = blockOf s' := by
  have hf := finNat_eq_of_read hθv hμ hj hs
  have hf' := finNat_eq_of_read hθv hμ hj' hs'
  -- a code in a lower block forces `μ + N ≤ μ`
  have key : ∀ {a b : Ordinal.{u}} {ja jb : ℕ}, ja < N → jb < N →
      θ (a : Label.{u}) = ((μ + ja : Ordinal.{u}) : Label.{u}) →
      θ (b : Label.{u}) = ((μ + jb : Ordinal.{u}) : Label.{u}) → blockOf a < blockOf b → False := by
    intro a b ja jb hja hjb ha hb hab
    have hfa := finNat_eq_of_read hθv hμ hja ha
    have hfb := finNat_eq_of_read hθv hμ hjb hb
    have h1 := hθv N le_rfl N le_rfl (a : Label.{u})
    rw [visibilityReplace_coe, visibilityReplace_blockOf_of_lt (hfa ▸ hja), ha,
      visibilityReplace_coe_add hμ, ite_eq_left hja] at h1
    have h2 := hθv N le_rfl 0 (Nat.zero_le _) (b : Label.{u})
    rw [visibilityReplace_coe, visibilityReplace_blockOf_of_lt (hfb ▸ hjb), hb,
      visibilityReplace_coe_add hμ, ite_eq_left hjb] at h2
    have hle : ((blockOf a + N : Ordinal.{u}) : Label.{u}) ≤
        ((blockOf b + ((0 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) := by
      rw [coe_le_coe_iff, Nat.cast_zero, add_zero]
      exact (add_natCast_lt_of_lt (isSuccPrelimit_blockOf b) hab N).le
    have h3 := hθm hle
    rw [h1, h2, coe_le_coe_iff, Nat.cast_zero, add_zero] at h3
    have : (N : Ordinal.{u}) ≤ 0 := by
      have := (add_le_add_iff_left μ).mp (h3.trans_eq (add_zero μ).symm)
      exact this
    exact absurd (by exact_mod_cast this : N ≤ 0) (by omega)
  rcases lt_trichotomy (blockOf s) (blockOf s') with h | h | h
  · exact (key hj hj' hs hs' h).elim
  · exact h
  · exact (key hj' hj hs' hs h).elim

include hθm in
/-- **Codes read in increasing blocks lie in increasing blocks.** -/
theorem blockOf_lt_of_read {s s' μ μ' : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ)
    (hμ' : Order.IsSuccPrelimit μ') (hlt : μ < μ') {j j' : ℕ} (hj : j < N) (hj' : j' < N)
    (hs : θ (s : Label.{u}) = ((μ + j : Ordinal.{u}) : Label.{u}))
    (hs' : θ (s' : Label.{u}) = ((μ' + j' : Ordinal.{u}) : Label.{u})) :
    blockOf s < blockOf s' := by
  have hf := finNat_eq_of_read hθv hμ hj hs
  have hf' := finNat_eq_of_read hθv hμ' hj' hs'
  rcases lt_trichotomy (blockOf s) (blockOf s') with h | h | h
  · exact h
  · -- one block: `θ (λ + j)` is read in the block of `μ'`
    exfalso
    have h1 := hθv N le_rfl j hj.le (s' : Label.{u})
    rw [visibilityReplace_coe, visibilityReplace_blockOf_of_lt (hf' ▸ hj'), hs',
      visibilityReplace_coe_add hμ', ite_eq_left hj', ← h] at h1
    have hsj : blockOf s + (j : Ordinal.{u}) = s := hf ▸ blockOf_add_finNat s
    rw [hsj, hs] at h1
    have h2 := coe_inj'.mp h1
    have : μ = μ' := by
      have := congrArg blockOf h2
      rwa [blockOf_add_natCast hμ, blockOf_add_natCast hμ'] at this
    exact hlt.ne this
  · exfalso
    have hss : s' < s := by
      calc s' = blockOf s' + finNat s' := (blockOf_add_finNat s').symm
        _ < blockOf s := add_natCast_lt_of_lt (isSuccPrelimit_blockOf s) h _
        _ ≤ s := by
          conv_rhs => rw [← blockOf_add_finNat s]
          exact le_self_add
    have h3 := hθm (coe_le_coe_iff.mpr hss.le)
    rw [hs, hs', coe_le_coe_iff] at h3
    exact absurd h3 (not_le.mpr ((add_natCast_lt_of_lt hμ' hlt j).trans_le
      (le_self_add (a := μ') (b := (j' : Ordinal.{u})))))

include hθm in
/-- **Below a code read as `⊤`.**  If `θ` reads `sa` as `⊤` and `s` as `μ + j`, `j < N`, then
the block of `s` plus `N` is at most the replacement of `sa` at `N` with any value `R`. -/
theorem blockOf_add_le_of_read_top {s sa μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) {j R : ℕ}
    (hj : j < N) (hs : θ (s : Label.{u}) = ((μ + j : Ordinal.{u}) : Label.{u}))
    (hsa : θ (sa : Label.{u}) = ⊤) :
    blockOf s + N ≤ Ordinal.visibilityReplace N R sa := by
  have hf := finNat_eq_of_read hθv hμ hj hs
  have hssa : s < sa := by
    by_contra hle
    have h3 := hθm (coe_le_coe_iff.mpr (not_lt.mp hle))
    rw [hs, hsa] at h3
    exact absurd (top_le_iff.mp h3) (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne
  rcases (blockOf_mono hssa.le).lt_or_eq with hlt | heq
  · have h1 : blockOf sa ≤ Ordinal.visibilityReplace N R sa := by
      rw [visibilityReplace_eq_blockOf]; exact le_self_add
    exact (add_natCast_lt_of_lt (isSuccPrelimit_blockOf sa) hlt N).le.trans h1
  · by_cases hfa : finNat sa < N
    · exfalso
      have h1 := hθv N le_rfl j hj.le (sa : Label.{u})
      rw [visibilityReplace_coe, visibilityReplace_blockOf_of_lt hfa, hsa, visibilityReplace_top,
        ← heq] at h1
      have hsj : blockOf s + (j : Ordinal.{u}) = s := hf ▸ blockOf_add_finNat s
      rw [hsj, hs] at h1
      exact absurd h1 (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne
    · rw [visibilityReplace_blockOf_of_le (not_lt.mp hfa), heq]
      conv_rhs => rw [← blockOf_add_finNat sa]
      exact (add_le_add_iff_left _).mpr (by exact_mod_cast not_lt.mp hfa)

end Read

/-- The replacement of a code at `N` with value `R < N` has finite part at least `R`. -/
theorem le_finNat_visibilityReplace {sa : Ordinal.{u}} {R : ℕ} (hR : R < N) :
    R ≤ finNat (Ordinal.visibilityReplace N R sa) := by
  by_cases hfa : finNat sa < N
  · rw [visibilityReplace_blockOf_of_lt hfa, finNat_add_natCast (isSuccPrelimit_blockOf sa)]
  · rw [visibilityReplace_blockOf_of_le (not_lt.mp hfa)]
    omega

end VaughtConjecture.Label
