/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Transform

/-!
# Block codes: relabelling finitely many blocks by a witness

Roadmap, Layer 3 (the template of the growth construction).

A **block code** (`Label.BlockCode`) relabels the blocks of labels: it assigns to a block `μ` (an
ordinal `ω * b`) either no target, sending the block to `⊥`, or a target strip `Λ μ = l` (zero or a
limit), monotonically, strictly on the **listed** blocks; on a listed block the finite part is
kept up to `N`, on an unlisted block with a target the whole block goes to `l + N`; the formal top
goes to a code `htop` whose finite part is at least `R < N`, above every `l + N`.  The code
(`Label.BlockCode.code`) is monotone (`Label.BlockCode.monotone_code`), fixes `⊥`, and commutes
with visibility replacement at every threshold `k ≤ R` with every value `i ≤ k`
(`Label.BlockCode.code_visibilityReplace`); so it is a witness bounded by the grade `R`
(`Label.BlockCode.isWitness_code`).

## References

Visibility replacement is [Kni26, Definition 2.2.3].
-/

universe u

namespace VaughtConjecture.Label

open Ordinal

/-- The finite part of an ordinal, as a natural number: `o % ω`. -/
noncomputable def finNat (o : Ordinal.{u}) : ℕ :=
  Classical.choose (lt_omega0.mp (Ordinal.mod_lt o omega0_ne_zero))

theorem finNat_spec (o : Ordinal.{u}) : o % ω = (finNat o : Ordinal.{u}) :=
  Classical.choose_spec (lt_omega0.mp (Ordinal.mod_lt o omega0_ne_zero))

/-- The block of an ordinal: `ω * (o / ω)`, zero or a limit. -/
noncomputable def blockOf (o : Ordinal.{u}) : Ordinal.{u} := ω * (o / ω)

theorem isSuccPrelimit_blockOf (o : Ordinal.{u}) : Order.IsSuccPrelimit (blockOf o) :=
  isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _)

theorem blockOf_add_finNat (o : Ordinal.{u}) : blockOf o + finNat o = o := by
  rw [blockOf, ← finNat_spec, Ordinal.div_add_mod]

/-- The block of a block start plus a natural number is the block start. -/
theorem blockOf_add_natCast {l : Ordinal.{u}} (hl : Order.IsSuccPrelimit l) (n : ℕ) :
    blockOf (l + n) = l := by
  obtain ⟨b, rfl⟩ := isSuccPrelimit_iff_omega0_dvd.mp hl
  rw [blockOf, Ordinal.mul_add_div _ omega0_ne_zero,
    Ordinal.div_eq_zero_of_lt (natCast_lt_omega0 n), add_zero]

/-- The finite part of a block start plus a natural number is that number. -/
theorem finNat_add_natCast {l : Ordinal.{u}} (hl : Order.IsSuccPrelimit l) (n : ℕ) :
    finNat (l + n) = n := by
  have h := blockOf_add_finNat (l + n)
  rw [blockOf_add_natCast hl] at h
  exact_mod_cast (add_left_cancel h)

/-- Visibility replacement of an ordinal in its block. -/
theorem visibilityReplace_eq_blockOf (k i : ℕ) (o : Ordinal.{u}) :
    Ordinal.visibilityReplace k i o =
      blockOf o + ((if finNat o < k then i else finNat o : ℕ) : Ordinal.{u}) := by
  conv_lhs => rw [← blockOf_add_finNat o]
  rw [Ordinal.visibilityReplace_add (isSuccPrelimit_blockOf o), Ordinal.visibilityReplace_natCast]
  split_ifs <;> rfl

/-- A block start plus `n` is below a larger block start plus `m`. -/
theorem add_natCast_lt_of_lt {l l' : Ordinal.{u}} (hl' : Order.IsSuccPrelimit l') (h : l < l')
    (n : ℕ) : l + n < l' :=
  hl'.add_natCast_lt h n

/-- **A block code.** -/
structure BlockCode : Type (u + 1) where
  /-- The listed-offset bound. -/
  N : ℕ
  /-- The grade through which the code commutes. -/
  R : ℕ
  R_lt_N : R < N
  /-- The target strip of a block, if any. -/
  Λ : Ordinal.{u} → Option Ordinal.{u}
  /-- The listed blocks. -/
  listed : Ordinal.{u} → Prop
  [dec : DecidablePred listed]
  /-- The top code. -/
  htop : Ordinal.{u}
  R_le_htop : R ≤ finNat htop
  Λ_limit : ∀ μ l, Λ μ = some l → Order.IsSuccPrelimit l
  Λ_le : ∀ μ l, Λ μ = some l → l + N ≤ htop
  low_down : ∀ μ μ', μ ≤ μ' → Λ μ' = none → Λ μ = none
  Λ_mono : ∀ μ μ' l l', μ ≤ μ' → Λ μ = some l → Λ μ' = some l' → l ≤ l'
  Λ_strict : ∀ μ μ' l l', μ < μ' → listed μ' → Λ μ = some l → Λ μ' = some l' → l < l'

namespace BlockCode

variable (B : BlockCode.{u})

attribute [instance] BlockCode.dec

/-- The offset kept on a value: its finite part up to `N` on a listed block, `N` otherwise. -/
noncomputable def off (a : Ordinal.{u}) : ℕ :=
  if B.listed (blockOf a) then min (finNat a) B.N else B.N

theorem off_le_N (a : Ordinal.{u}) : B.off a ≤ B.N := by
  unfold off; split_ifs
  · exact min_le_right _ _
  · exact le_rfl

/-- The code of an ordinal label. -/
noncomputable def codeOrd (a : Ordinal.{u}) : Label.{u} :=
  match B.Λ (blockOf a) with
  | none => ⊥
  | some l => ((l + B.off a : Ordinal.{u}) : Label.{u})

/-- **The code.** -/
noncomputable def code (x : Label.{u}) : Label.{u} :=
  match x with
  | none => ⊥
  | some none => ((B.htop : Ordinal.{u}) : Label.{u})
  | some (some a) => B.codeOrd a

@[simp] theorem code_bot : B.code ⊥ = ⊥ := rfl

@[simp] theorem code_top : B.code ⊤ = ((B.htop : Ordinal.{u}) : Label.{u}) := rfl

@[simp] theorem code_coe (a : Ordinal.{u}) : B.code (a : Label.{u}) = B.codeOrd a := rfl

theorem codeOrd_of_none {a : Ordinal.{u}} (h : B.Λ (blockOf a) = none) : B.codeOrd a = ⊥ := by
  unfold codeOrd; rw [h]

theorem codeOrd_of_some {a l : Ordinal.{u}} (h : B.Λ (blockOf a) = some l) :
    B.codeOrd a = ((l + B.off a : Ordinal.{u}) : Label.{u}) := by
  unfold codeOrd; rw [h]

/-- On a listed block with target `l`, a value with finite part at most `N` goes to `l` plus its
finite part. -/
theorem codeOrd_listed {a l : Ordinal.{u}} (hl : B.listed (blockOf a))
    (h : B.Λ (blockOf a) = some l) (hfp : finNat a ≤ B.N) :
    B.codeOrd a = ((l + finNat a : Ordinal.{u}) : Label.{u}) := by
  rw [B.codeOrd_of_some h, off, ite_eq_left hl, min_eq_left hfp]

end BlockCode

theorem coe_le_coe_iff {a b : Ordinal.{u}} : (a : Label.{u}) ≤ (b : Label.{u}) ↔ a ≤ b := by
  rw [WithBot.coe_le_coe, WithTop.coe_le_coe]

theorem blockOf_mono {a b : Ordinal.{u}} (h : a ≤ b) : blockOf a ≤ blockOf b :=
  mul_le_mul_right (Ordinal.div_le_left h ω) ω

/-- Within one block, the order of values is the order of their finite parts. -/
theorem finNat_le_of_le {a b : Ordinal.{u}} (h : a ≤ b) (hab : blockOf a = blockOf b) :
    finNat a ≤ finNat b := by
  have h1 : blockOf b + (finNat a : Ordinal.{u}) = a := hab ▸ blockOf_add_finNat a
  have h2 := blockOf_add_finNat b
  have h3 : blockOf b + (finNat a : Ordinal.{u}) ≤ blockOf b + finNat b := by rw [h1, h2]; exact h
  exact_mod_cast (add_le_add_iff_left _).mp h3

namespace BlockCode

variable (B : BlockCode.{u})

theorem strip_le_htop {μ l : Ordinal.{u}} (h : B.Λ μ = some l) {n : ℕ} (hn : n ≤ B.N) :
    l + n ≤ B.htop :=
  ((add_le_add_iff_left l).mpr (Nat.cast_le.mpr hn)).trans (B.Λ_le μ l h)

/-- **The code is monotone.** -/
theorem monotone_code : Monotone B.code := by
  intro x y hxy
  induction x using Label.recBotCoeTop with
  | bot => exact bot_le
  | top =>
    obtain rfl : y = ⊤ := top_le_iff.mp hxy
    exact le_rfl
  | coe a =>
    induction y using Label.recBotCoeTop with
    | bot => exact absurd (le_bot_iff.mp hxy) (by simp)
    | top =>
      rw [code_coe, code_top]
      rcases h : B.Λ (blockOf a) with _ | l
      · rw [B.codeOrd_of_none h]; exact bot_le
      · rw [B.codeOrd_of_some h, coe_le_coe_iff]
        exact B.strip_le_htop h (B.off_le_N a)
    | coe b =>
      rw [coe_le_coe_iff] at hxy
      rw [code_coe, code_coe]
      have hlp := blockOf_mono hxy
      rcases ha : B.Λ (blockOf a) with _ | l
      · rw [B.codeOrd_of_none ha]; exact bot_le
      rcases hb : B.Λ (blockOf b) with _ | l'
      · exact absurd (B.low_down _ _ hlp hb) (by rw [ha]; exact Option.some_ne_none l)
      rw [B.codeOrd_of_some ha, B.codeOrd_of_some hb, coe_le_coe_iff]
      have hll' : l ≤ l' := B.Λ_mono _ _ l l' hlp ha hb
      rcases hll'.lt_or_eq with hlt | rfl
      · exact ((add_natCast_lt_of_lt (B.Λ_limit _ l' hb) hlt _).trans_le le_self_add).le
      · refine (add_le_add_iff_left l).mpr (Nat.cast_le.mpr ?_)
        rcases hlp.lt_or_eq with hlt | heq
        · have hnl : ¬ B.listed (blockOf b) := fun hl ↦
            lt_irrefl l (B.Λ_strict _ _ l l hlt hl ha hb)
          have : B.off b = B.N := by unfold off; simp [hnl]
          rw [this]
          exact B.off_le_N a
        · have hfp := finNat_le_of_le hxy heq
          unfold off
          rw [heq]
          split_ifs
          · exact min_le_min_right _ hfp
          · exact le_rfl

/-- **The code commutes with visibility replacement** at every threshold `k ≤ R` with every value
`i ≤ k`. -/
theorem code_visibilityReplace (x : Label.{u}) {k i : ℕ} (hk : k ≤ B.R) (hi : i ≤ k) :
    B.code (visibilityReplace k i x) = visibilityReplace k i (B.code x) := by
  have hkN : k ≤ B.N := hk.trans B.R_lt_N.le
  induction x using Label.recBotCoeTop with
  | bot => rfl
  | top =>
    rw [visibilityReplace_top, code_top, visibilityReplace_coe, visibilityReplace_eq_blockOf,
      ite_eq_right (not_lt.mpr (hk.trans B.R_le_htop)), blockOf_add_finNat]
  | coe a =>
    rw [visibilityReplace_coe, visibilityReplace_eq_blockOf, code_coe, code_coe]
    have hμ := isSuccPrelimit_blockOf a
    by_cases hfa : finNat a < k
    · rw [ite_eq_left hfa]
      have hb : blockOf (blockOf a + i) = blockOf a := blockOf_add_natCast hμ i
      have hf : finNat (blockOf a + i) = i := finNat_add_natCast hμ i
      rcases h : B.Λ (blockOf a) with _ | l
      · rw [B.codeOrd_of_none h, B.codeOrd_of_none (by rw [hb]; exact h)]
        rfl
      · have hl := B.Λ_limit _ l h
        rw [B.codeOrd_of_some h, B.codeOrd_of_some (by rw [hb]; exact h), off, off, hb, hf]
        by_cases hls : B.listed (blockOf a)
        · rw [ite_eq_left hls, ite_eq_left hls, min_eq_left (hi.trans hkN),
            min_eq_left (hfa.le.trans hkN), visibilityReplace_coe_add hl, ite_eq_left hfa]
        · rw [ite_eq_right hls, ite_eq_right hls, visibilityReplace_coe_add hl,
            ite_eq_right (not_lt.mpr hkN)]
    · rw [ite_eq_right hfa, blockOf_add_finNat]
      rcases h : B.Λ (blockOf a) with _ | l
      · rw [B.codeOrd_of_none h]; rfl
      · have hl := B.Λ_limit _ l h
        rw [B.codeOrd_of_some h, visibilityReplace_coe_add hl, ite_eq_right]
        unfold off
        split_ifs
        · exact not_lt.mpr (le_min (not_lt.mp hfa) hkN)
        · exact not_lt.mpr hkN

/-- **The code is a witness bounded by the grade `R`**: above `R` the suppressor is `⊥`, and the
only label sent below it is `⊥`'s preimage, closed under visibility replacement. -/
theorem isWitness_code (hbotinv : ∀ x, B.code x = ⊥ → ∀ k i, i ≤ k →
    B.code (visibilityReplace k i x) = ⊥) : IsWitness (stepSuppressor B.R) B.code where
  antitone := (IsWitness.id_step B.R).antitone
  isSelfVisible := (IsWitness.id_step B.R).isSelfVisible
  map_bot := rfl
  monotone := B.monotone_code
  visibilityReplace_comm x k hx i hi := by
    by_cases hk : k ≤ B.R
    · exact B.code_visibilityReplace x hk hi
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
      rw [hx, visibilityReplace_bot]
      exact hbotinv x hx k i hi

end BlockCode

end VaughtConjecture.Label
