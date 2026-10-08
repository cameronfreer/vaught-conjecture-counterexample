/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Finset.Max
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

/-- Visibility replacement keeps the block. -/
theorem blockOf_visibilityReplace (k i : ℕ) (a : Ordinal.{u}) :
    blockOf (Ordinal.visibilityReplace k i a) = blockOf a := by
  rw [visibilityReplace_eq_blockOf]
  exact blockOf_add_natCast (isSuccPrelimit_blockOf a) _

namespace BlockCode

variable (B : BlockCode.{u})

/-- The labels the code sends to `⊥` stay there under every visibility replacement. -/
theorem code_visibilityReplace_eq_bot {x : Label.{u}} (hx : B.code x = ⊥) (k i : ℕ) :
    B.code (visibilityReplace k i x) = ⊥ := by
  induction x using Label.recBotCoeTop with
  | bot => rfl
  | top => exact absurd hx (by simp)
  | coe a =>
    rw [code_coe] at hx
    rw [visibilityReplace_coe, code_coe]
    rcases h : B.Λ (blockOf a) with _ | l
    · exact B.codeOrd_of_none (by rw [blockOf_visibilityReplace]; exact h)
    · rw [B.codeOrd_of_some h] at hx
      exact absurd hx (by simp)

/-- **The code is a witness bounded by the grade `R`.** -/
theorem isWitness_code' : IsWitness (stepSuppressor B.R) B.code :=
  B.isWitness_code fun _ hx k i _ ↦ B.code_visibilityReplace_eq_bot hx k i

/-! ### A block code from finitely many listed blocks -/

end BlockCode

section OfFinset

variable (N R : ℕ) (hR : R < N) (S : Finset Ordinal.{u}) (strip : Ordinal.{u} → Ordinal.{u})
  (htop : Ordinal.{u})

/-- The target of a block: the strip of the largest listed block at or below it. -/
noncomputable def targetOf (μ : Ordinal.{u}) : Option Ordinal.{u} :=
  if h : (S.filter fun μ' ↦ μ' ≤ μ).Nonempty then some (strip ((S.filter fun μ' ↦ μ' ≤ μ).max' h))
  else none

theorem targetOf_eq_none_iff (μ : Ordinal.{u}) :
    targetOf S strip μ = none ↔ ¬ (S.filter fun μ' ↦ μ' ≤ μ).Nonempty := by
  unfold targetOf
  split_ifs with h <;> simp [h]

theorem targetOf_eq_some {μ : Ordinal.{u}} (h : (S.filter fun μ' ↦ μ' ≤ μ).Nonempty) :
    targetOf S strip μ = some (strip ((S.filter fun μ' ↦ μ' ≤ μ).max' h)) := by
  unfold targetOf
  rw [dite_eq_left h]

theorem max'_filter_spec {μ : Ordinal.{u}} (h : (S.filter fun μ' ↦ μ' ≤ μ).Nonempty) :
    (S.filter fun μ' ↦ μ' ≤ μ).max' h ∈ S ∧ (S.filter fun μ' ↦ μ' ≤ μ).max' h ≤ μ ∧
      ∀ μ' ∈ S, μ' ≤ μ → μ' ≤ (S.filter fun μ' ↦ μ' ≤ μ).max' h := by
  have hm := Finset.max'_mem _ h
  rw [Finset.mem_filter] at hm
  refine ⟨hm.1, hm.2, fun μ' hμ' hle ↦ Finset.le_max' _ _ ?_⟩
  rw [Finset.mem_filter]
  exact ⟨hμ', hle⟩

/-- **A block code from finitely many listed blocks** with a strip function, zero or a limit,
strictly increasing on them, with `strip μ + N ≤ htop`, and `R` at most the finite part of
`htop`. -/
noncomputable def BlockCode.ofFinset (hlim : ∀ μ ∈ S, Order.IsSuccPrelimit (strip μ))
    (hle : ∀ μ ∈ S, strip μ + N ≤ htop)
    (hstrict : ∀ μ ∈ S, ∀ μ' ∈ S, μ < μ' → strip μ < strip μ')
    (hRtop : R ≤ finNat htop) : BlockCode.{u} where
  N := N
  R := R
  R_lt_N := hR
  Λ := targetOf S strip
  listed := fun μ ↦ μ ∈ S
  dec := fun _ ↦ Classical.propDecidable _
  htop := htop
  R_le_htop := hRtop
  Λ_limit := by
    intro μ l hl
    by_cases h : (S.filter fun μ' ↦ μ' ≤ μ).Nonempty
    · rw [targetOf_eq_some S strip h, Option.some.injEq] at hl
      rw [← hl]
      exact hlim _ (max'_filter_spec S h).1
    · rw [(targetOf_eq_none_iff S strip μ).mpr h] at hl
      exact absurd hl (Option.some_ne_none l).symm
  Λ_le := by
    intro μ l hl
    by_cases h : (S.filter fun μ' ↦ μ' ≤ μ).Nonempty
    · rw [targetOf_eq_some S strip h, Option.some.injEq] at hl
      rw [← hl]
      exact hle _ (max'_filter_spec S h).1
    · rw [(targetOf_eq_none_iff S strip μ).mpr h] at hl
      exact absurd hl (Option.some_ne_none l).symm
  low_down := by
    intro μ μ' hμμ' hnone
    rw [targetOf_eq_none_iff] at hnone ⊢
    intro ⟨ν, hν⟩
    rw [Finset.mem_filter] at hν
    exact hnone ⟨ν, Finset.mem_filter.mpr ⟨hν.1, hν.2.trans hμμ'⟩⟩
  Λ_mono := by
    intro μ μ' l l' hμμ' hl hl'
    by_cases h : (S.filter fun ν ↦ ν ≤ μ).Nonempty
    swap
    · rw [(targetOf_eq_none_iff S strip μ).mpr h] at hl
      exact absurd hl (Option.some_ne_none l).symm
    by_cases h' : (S.filter fun ν ↦ ν ≤ μ').Nonempty
    swap
    · rw [(targetOf_eq_none_iff S strip μ').mpr h'] at hl'
      exact absurd hl' (Option.some_ne_none l').symm
    rw [targetOf_eq_some S strip h, Option.some.injEq] at hl
    rw [targetOf_eq_some S strip h', Option.some.injEq] at hl'
    rw [← hl, ← hl']
    obtain ⟨hm1, hm2, -⟩ := max'_filter_spec S h
    obtain ⟨hm1', -, hm3'⟩ := max'_filter_spec S h'
    have hle' := hm3' _ hm1 (hm2.trans hμμ')
    rcases hle'.lt_or_eq with hlt | heq
    · exact (hstrict _ hm1 _ hm1' hlt).le
    · rw [heq]
  Λ_strict := by
    intro μ μ' l l' hμμ' hμ'S hl hl'
    by_cases h : (S.filter fun ν ↦ ν ≤ μ).Nonempty
    swap
    · rw [(targetOf_eq_none_iff S strip μ).mpr h] at hl
      exact absurd hl (Option.some_ne_none l).symm
    have h' : (S.filter fun ν ↦ ν ≤ μ').Nonempty := ⟨μ', Finset.mem_filter.mpr ⟨hμ'S, le_rfl⟩⟩
    rw [targetOf_eq_some S strip h, Option.some.injEq] at hl
    rw [targetOf_eq_some S strip h', Option.some.injEq] at hl'
    rw [← hl, ← hl']
    obtain ⟨hm1, hm2, -⟩ := max'_filter_spec S h
    obtain ⟨-, -, hm3'⟩ := max'_filter_spec S h'
    have hmax' : (S.filter fun ν ↦ ν ≤ μ').max' h' = μ' :=
      le_antisymm (max'_filter_spec S h').2.1 (hm3' _ hμ'S le_rfl)
    rw [hmax']
    exact hstrict _ hm1 _ hμ'S (hm2.trans_lt hμμ')

/-- A listed block's target is its own strip. -/
theorem BlockCode.ofFinset_Λ (hlim : ∀ μ ∈ S, Order.IsSuccPrelimit (strip μ))
    (hle : ∀ μ ∈ S, strip μ + N ≤ htop)
    (hstrict : ∀ μ ∈ S, ∀ μ' ∈ S, μ < μ' → strip μ < strip μ')
    (hRtop : R ≤ finNat htop) {μ : Ordinal.{u}} (hμ : μ ∈ S) :
    (BlockCode.ofFinset N R hR S strip htop hlim hle hstrict hRtop).Λ μ = some (strip μ) := by
  classical
  have h : (S.filter fun ν ↦ ν ≤ μ).Nonempty := ⟨μ, Finset.mem_filter.mpr ⟨hμ, le_rfl⟩⟩
  change targetOf S strip μ = some (strip μ)
  rw [targetOf_eq_some S strip h]
  congr 2
  exact le_antisymm (max'_filter_spec S h).2.1 ((max'_filter_spec S h).2.2 _ hμ le_rfl)

end OfFinset

end VaughtConjecture.Label
