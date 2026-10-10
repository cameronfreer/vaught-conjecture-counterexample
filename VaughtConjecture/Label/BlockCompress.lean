/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import VaughtConjecture.Label.BlockCode

/-!
# Compressing finitely many labels below `ω ^ 2`

Roadmap, Layer 3 ((R3) and (R4), the labelling of the replicated scheme).

Finitely many labels `V` occupy finitely many blocks (`Label.blockSet V`, `r` of them).  The
**block compression** of `V` at a grade `K` (`Label.blockCompress V K`) is the block code
(`Label.BlockCode.ofFinset`) sending the block of rank `i` among the blocks of `V` to the strip
`ω * i`, keeping finite parts up to a bound `N > K` at least every finite part of a label of `V`,
and sending the formal top to `ω * r + N`.  It is a witness bounded by `K`
(`Label.isWitness_blockCompress`), sends a label of `V` to `⊥` only if it is `⊥`
(`Label.blockCompress_eq_bot_iff`), and sends `V` below `ω * (r + 1)`
(`Label.blockCompress_lt`), so below `ω ^ 2` and at most every grid point `ω * B' + 2` with
`r < B'` (`Label.blockCompress_le_gridPoint`).

The **block expansion** (`Label.blockExpand V`) sends `ω * i + j` to the block of rank `i` of `V`
plus `j` for `i < r`, every other ordinal label and the formal top to the formal top, and `⊥` to
`⊥`.  It is a witness bounded by every grade (`Label.isWitness_blockExpand`), sends only `⊥` to
`⊥` (`Label.blockExpand_eq_bot_iff`), and inverts the compression on `V`
(`Label.blockExpand_blockCompress`).

So a labelling with values in `V`, lawful for some rows, is the expansion of a labelling with
values below `ω ^ 2`, lawful for the same rows (the compression is a witness reflecting `⊥` on
`V`); and the expansion of a lawful labelling is lawful (it is a witness reflecting `⊥`).

## References

Visibility replacement is [Kni26, Definition 2.2.3].
-/

universe u

namespace VaughtConjecture.Label

open Ordinal Finset

/-! ### Blocks and finite parts of labels -/

/-- The block of a label: the block of an ordinal label, none for `⊥` and the formal top. -/
noncomputable def labelBlocks : Label.{u} → Finset Ordinal.{u} :=
  recBotCoeTop ∅ (fun a ↦ {blockOf a}) ∅

/-- The finite part of a label: that of an ordinal label, `0` for `⊥` and the formal top. -/
noncomputable def labelFinNat : Label.{u} → ℕ :=
  recBotCoeTop 0 finNat 0

@[simp] theorem labelBlocks_coe (a : Ordinal.{u}) : labelBlocks (a : Label.{u}) = {blockOf a} :=
  rfl

@[simp] theorem labelFinNat_coe (a : Ordinal.{u}) : labelFinNat (a : Label.{u}) = finNat a := rfl

variable (V : Finset Label.{u})

/-- The blocks of the ordinal labels of `V`. -/
noncomputable def blockSet : Finset Ordinal.{u} := V.biUnion labelBlocks

/-- The number of blocks of `V`. -/
noncomputable def blockCount : ℕ := (blockSet V).card

/-- The rank of an ordinal among the blocks of `V`: the number of blocks of `V` below it. -/
noncomputable def blockRank (μ : Ordinal.{u}) : ℕ := ((blockSet V).filter (· < μ)).card

/-- The bound of the kept finite parts at the grade `K`: above `K` and at least every finite part
of a label of `V`. -/
noncomputable def compressBound (K : ℕ) : ℕ := K + 1 + V.sup labelFinNat

/-- The block of rank `i` of `V`, for `i` below the number of blocks (`0` otherwise). -/
noncomputable def nthBlock (i : ℕ) : Ordinal.{u} :=
  if h : i < blockCount V then (blockSet V).orderEmbOfFin rfl ⟨i, h⟩ else 0

variable {V}

theorem blockOf_mem_blockSet {a : Ordinal.{u}} (ha : (a : Label.{u}) ∈ V) :
    blockOf a ∈ blockSet V :=
  mem_biUnion.mpr ⟨_, ha, by simp⟩

theorem finNat_le_compressBound {a : Ordinal.{u}} (ha : (a : Label.{u}) ∈ V) (K : ℕ) :
    finNat a ≤ compressBound V K := by
  have h := le_sup (f := labelFinNat) ha
  rw [labelFinNat_coe] at h
  unfold compressBound
  omega

theorem isSuccPrelimit_of_mem_blockSet {μ : Ordinal.{u}} (hμ : μ ∈ blockSet V) :
    Order.IsSuccPrelimit μ := by
  obtain ⟨x, -, hx⟩ := mem_biUnion.mp hμ
  induction x using recBotCoeTop with
  | bot => simp [labelBlocks, recBotCoeTop] at hx
  | top => simp [labelBlocks, recBotCoeTop] at hx
  | coe a =>
    rw [labelBlocks_coe, mem_singleton] at hx
    rw [hx]
    exact isSuccPrelimit_blockOf a

theorem blockRank_le (μ : Ordinal.{u}) : blockRank V μ ≤ blockCount V :=
  card_filter_le _ _

theorem blockRank_lt {μ : Ordinal.{u}} (hμ : μ ∈ blockSet V) : blockRank V μ < blockCount V :=
  card_lt_card (filter_ssubset.mpr ⟨μ, hμ, lt_irrefl μ⟩)

theorem blockRank_strictMono {μ μ' : Ordinal.{u}} (hμ : μ ∈ blockSet V) (h : μ < μ') :
    blockRank V μ < blockRank V μ' := by
  refine card_lt_card ((ssubset_iff_of_subset fun x hx ↦ ?_).mpr ⟨μ, ?_, ?_⟩)
  · rw [mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans h⟩
  · exact mem_filter.mpr ⟨hμ, h⟩
  · simp

theorem omega0_mul_natCast_lt_iff {i j : ℕ} :
    ω * (i : Ordinal.{u}) < ω * (j : Ordinal.{u}) ↔ i < j := by
  rw [mul_lt_mul_iff_right₀ omega0_pos, Nat.cast_lt]

theorem omega0_mul_natCast_le_iff {i j : ℕ} :
    ω * (i : Ordinal.{u}) ≤ ω * (j : Ordinal.{u}) ↔ i ≤ j := by
  rw [mul_le_mul_iff_right₀ omega0_pos, Nat.cast_le]

theorem omega0_mul_natCast_inj {i j : ℕ} :
    ω * (i : Ordinal.{u}) = ω * (j : Ordinal.{u}) ↔ i = j := by
  refine ⟨fun h ↦ le_antisymm ?_ ?_, fun h ↦ by rw [h]⟩
  · exact omega0_mul_natCast_le_iff.mp h.le
  · exact omega0_mul_natCast_le_iff.mp h.ge

theorem isSuccPrelimit_omega0_mul (o : Ordinal.{u}) : Order.IsSuccPrelimit (ω * o) :=
  isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _)

/-! ### The blocks in increasing order -/

theorem nthBlock_of_lt {i : ℕ} (hi : i < blockCount V) :
    nthBlock V i = (blockSet V).orderEmbOfFin rfl ⟨i, hi⟩ :=
  dite_eq_left hi

theorem nthBlock_mem {i : ℕ} (hi : i < blockCount V) : nthBlock V i ∈ blockSet V := by
  rw [nthBlock_of_lt hi]
  exact orderEmbOfFin_mem _ _ _

theorem nthBlock_strictMono {i j : ℕ} (hij : i < j) (hj : j < blockCount V) :
    nthBlock V i < nthBlock V j := by
  rw [nthBlock_of_lt (hij.trans hj), nthBlock_of_lt hj]
  exact ((blockSet V).orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr hij)

theorem blockRank_nthBlock {i : ℕ} (hi : i < blockCount V) : blockRank V (nthBlock V i) = i := by
  rw [nthBlock_of_lt hi]
  set e := (blockSet V).orderEmbOfFin (k := blockCount V) rfl
  have hS : blockSet V = univ.image e := (image_orderEmbOfFin_univ _ _).symm
  have key : (blockSet V).filter (· < e ⟨i, hi⟩) = (Iio ⟨i, hi⟩).image e := by
    ext x
    rw [mem_filter, mem_image]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨j, -, rfl⟩ := mem_image.mp (hS ▸ hx)
      exact ⟨j, mem_Iio.mpr (e.lt_iff_lt.mp hlt), rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨orderEmbOfFin_mem _ _ _, e.lt_iff_lt.mpr (mem_Iio.mp hj)⟩
  change ((blockSet V).filter (· < e ⟨i, hi⟩)).card = i
  rw [key, card_image_of_injective _ e.injective, Fin.card_Iio]

theorem nthBlock_blockRank {μ : Ordinal.{u}} (hμ : μ ∈ blockSet V) :
    nthBlock V (blockRank V μ) = μ := by
  have hr : Set.range ((blockSet V).orderEmbOfFin (k := blockCount V) rfl) = blockSet V :=
    range_orderEmbOfFin _ _
  obtain ⟨j, hj⟩ : μ ∈ Set.range ((blockSet V).orderEmbOfFin (k := blockCount V) rfl) := by
    rw [hr]; exact hμ
  have hjn : nthBlock V j = μ := by rw [nthBlock_of_lt j.2]; exact hj
  rw [← hjn, blockRank_nthBlock j.2]

/-! ### The compression -/

variable (V)

/-- The block code of the compression of `V` at the grade `K`. -/
noncomputable def compressCode (K : ℕ) : BlockCode.{u} :=
  BlockCode.ofFinset (compressBound V K) (compressBound V K - 1)
    (by unfold compressBound; omega) (blockSet V) (fun μ ↦ ω * (blockRank V μ : Ordinal.{u}))
    (ω * (blockCount V : Ordinal.{u}) + compressBound V K)
    (fun _ _ ↦ isSuccPrelimit_omega0_mul _)
    (fun μ _ ↦ by gcongr; exact blockRank_le μ)
    (fun μ hμ μ' _ h ↦ omega0_mul_natCast_lt_iff.mpr (blockRank_strictMono hμ h))
    (by rw [finNat_add_natCast (isSuccPrelimit_omega0_mul _)]; omega)

/-- **The block compression** of `V` at the grade `K`. -/
noncomputable def blockCompress (K : ℕ) : Label.{u} → Label.{u} := (compressCode V K).code

variable {V}

/-- **The compression is a witness bounded by the grade `K`.** -/
theorem isWitness_blockCompress (K : ℕ) :
    IsWitness (stepSuppressor K) (blockCompress V K) :=
  (compressCode V K).isWitness_code'.of_le_stepSuppressor (by
    change K ≤ compressBound V K - 1
    unfold compressBound
    omega)

@[simp] theorem blockCompress_bot (K : ℕ) : blockCompress V K ⊥ = ⊥ := rfl

theorem blockCompress_top (K : ℕ) :
    blockCompress V K ⊤ =
      ((ω * (blockCount V : Ordinal.{u}) + compressBound V K : Ordinal.{u}) : Label.{u}) := rfl

/-- The compression of an ordinal label of `V`: its block goes to `ω` times its rank, its finite
part is kept. -/
theorem blockCompress_coe {a : Ordinal.{u}} (ha : (a : Label.{u}) ∈ V) (K : ℕ) :
    blockCompress V K a =
      ((ω * (blockRank V (blockOf a) : Ordinal.{u}) + finNat a : Ordinal.{u}) : Label.{u}) := by
  have hS := blockOf_mem_blockSet ha
  change (compressCode V K).codeOrd a = _
  exact (compressCode V K).codeOrd_listed hS
    (BlockCode.ofFinset_Λ _ _ _ _ _ _ _ _ _ _ hS) (finNat_le_compressBound ha K)

/-- **The compression sends a label of `V` to `⊥` only if it is `⊥`.** -/
theorem blockCompress_eq_bot_iff {x : Label.{u}} (hx : x ∈ V) (K : ℕ) :
    blockCompress V K x = ⊥ ↔ x = ⊥ := by
  induction x using recBotCoeTop with
  | bot => simp
  | top => rw [blockCompress_top]; simp
  | coe a => rw [blockCompress_coe hx]; simp

/-- **The compression sends `V` below `ω * (r + 1)`**, `r` the number of blocks of `V`. -/
theorem blockCompress_lt {x : Label.{u}} (hx : x ∈ V) (K : ℕ) :
    blockCompress V K x < ((ω * ((blockCount V + 1 : ℕ) : Ordinal.{u}) : Ordinal.{u}) :
      Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => exact WithBot.bot_lt_coe _
  | top =>
    rw [blockCompress_top, WithBot.coe_lt_coe, WithTop.coe_lt_coe, Nat.cast_succ, mul_add_one]
    exact add_lt_add_right (natCast_lt_omega0 _) _
  | coe a =>
    rw [blockCompress_coe hx, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
    have h1 : ω * (blockRank V (blockOf a) : Ordinal.{u}) + finNat a <
        ω * ((blockRank V (blockOf a) + 1 : ℕ) : Ordinal.{u}) := by
      rw [Nat.cast_succ, mul_add_one]
      exact add_lt_add_right (natCast_lt_omega0 _) _
    refine h1.trans_le (omega0_mul_natCast_le_iff.mpr ?_)
    have := blockRank_lt (blockOf_mem_blockSet hx)
    omega

/-- **The compression sends `V` below `ω ^ 2`.** -/
theorem blockCompress_lt_omega0_sq {x : Label.{u}} (hx : x ∈ V) (K : ℕ) :
    blockCompress V K x < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := by
  refine (blockCompress_lt hx K).trans ?_
  rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe, sq]
  exact (mul_lt_mul_iff_right₀ omega0_pos).mpr (natCast_lt_omega0 _)

/-! ### The expansion -/

variable (V) in
open Classical in
/-- The expansion of an ordinal: `ω * i + j` goes to the block of rank `i` of `V` plus `j` for `i`
below the number of blocks, every other ordinal to the formal top. -/
noncomputable def expandOrd (a : Ordinal.{u}) : Label.{u} :=
  if h : ∃ i, i < blockCount V ∧ blockOf a = ω * (i : Ordinal.{u}) then
    ((nthBlock V (Nat.find h) + finNat a : Ordinal.{u}) : Label.{u})
  else ⊤

variable (V) in
/-- **The block expansion** of `V`: `⊥` and the formal top are fixed, ordinal labels are expanded
(`Label.expandOrd`). -/
noncomputable def blockExpand : Label.{u} → Label.{u} :=
  recBotCoeTop ⊥ (expandOrd V) ⊤

@[simp] theorem blockExpand_bot : blockExpand V ⊥ = ⊥ := rfl

@[simp] theorem blockExpand_top : blockExpand V ⊤ = ⊤ := rfl

@[simp] theorem blockExpand_coe (a : Ordinal.{u}) : blockExpand V a = expandOrd V a := rfl

theorem expandOrd_of {a : Ordinal.{u}} {i : ℕ} (hi : i < blockCount V)
    (hb : blockOf a = ω * (i : Ordinal.{u})) :
    expandOrd V a = ((nthBlock V i + finNat a : Ordinal.{u}) : Label.{u}) := by
  classical
  have h : ∃ i, i < blockCount V ∧ blockOf a = ω * (i : Ordinal.{u}) := ⟨i, hi, hb⟩
  have hf : Nat.find h = i :=
    omega0_mul_natCast_inj.mp ((Nat.find_spec h).2.symm.trans hb)
  unfold expandOrd
  rw [dite_eq_left h, hf]

theorem expandOrd_of_not {a : Ordinal.{u}}
    (h : ¬ ∃ i, i < blockCount V ∧ blockOf a = ω * (i : Ordinal.{u})) : expandOrd V a = ⊤ := by
  classical
  unfold expandOrd
  rw [dite_eq_right h]

/-- A block at most `ω * j` is `ω * i` for some `i ≤ j`. -/
theorem exists_blockOf_eq_of_le {a : Ordinal.{u}} {j : ℕ}
    (h : blockOf a ≤ ω * (j : Ordinal.{u})) : ∃ i ≤ j, blockOf a = ω * (i : Ordinal.{u}) := by
  have hq : a / ω ≤ (j : Ordinal.{u}) := (mul_le_mul_iff_right₀ omega0_pos).mp h
  obtain ⟨i, hi⟩ := lt_omega0.mp (hq.trans_lt (natCast_lt_omega0 j))
  refine ⟨i, Nat.cast_le.mp (hi ▸ hq), ?_⟩
  rw [blockOf, hi]

/-- **The expansion is monotone.** -/
theorem monotone_blockExpand : Monotone (blockExpand V) := by
  intro x y hxy
  induction x using recBotCoeTop with
  | bot => exact bot_le
  | top =>
    obtain rfl : y = ⊤ := top_le_iff.mp hxy
    exact le_rfl
  | coe a =>
    induction y using recBotCoeTop with
    | bot => exact absurd (le_bot_iff.mp hxy) (by simp)
    | top => exact le_top
    | coe b =>
      rw [WithBot.coe_le_coe, WithTop.coe_le_coe] at hxy
      rw [blockExpand_coe, blockExpand_coe]
      by_cases hb : ∃ j, j < blockCount V ∧ blockOf b = ω * (j : Ordinal.{u})
      · obtain ⟨j, hj, hbj⟩ := hb
        obtain ⟨i, hij, hai⟩ := exists_blockOf_eq_of_le ((blockOf_mono hxy).trans hbj.le)
        rw [expandOrd_of (hij.trans_lt hj) hai, expandOrd_of hj hbj, WithBot.coe_le_coe,
          WithTop.coe_le_coe]
        rcases hij.lt_or_eq with hlt | rfl
        · have hl : Order.IsSuccPrelimit (nthBlock V j) :=
            isSuccPrelimit_of_mem_blockSet (nthBlock_mem hj)
          exact ((add_natCast_lt_of_lt hl (nthBlock_strictMono hlt hj) _).trans_le
            le_self_add).le
        · exact add_le_add_right (Nat.cast_le.mpr (finNat_le_of_le hxy (hai.trans hbj.symm))) _
      · rw [expandOrd_of_not hb]
        exact le_top

/-- **The expansion commutes with visibility replacement** at every threshold. -/
theorem blockExpand_visibilityReplace (x : Label.{u}) (k i : ℕ) :
    blockExpand V (visibilityReplace k i x) = visibilityReplace k i (blockExpand V x) := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe a =>
    rw [visibilityReplace_coe, blockExpand_coe, blockExpand_coe]
    have hb := blockOf_visibilityReplace k i a
    by_cases h : ∃ j, j < blockCount V ∧ blockOf a = ω * (j : Ordinal.{u})
    · obtain ⟨j, hj, haj⟩ := h
      have hl : Order.IsSuccPrelimit (nthBlock V j) :=
        isSuccPrelimit_of_mem_blockSet (nthBlock_mem hj)
      rw [expandOrd_of hj (hb.trans haj), expandOrd_of hj haj, visibilityReplace_coe_add hl,
        visibilityReplace_eq_blockOf, finNat_add_natCast (isSuccPrelimit_blockOf a)]
      split_ifs <;> rfl
    · rw [expandOrd_of_not h, expandOrd_of_not (by rwa [hb]), visibilityReplace_top]

/-- **The expansion is a witness bounded by every grade.** -/
theorem isWitness_blockExpand (K : ℕ) : IsWitness (stepSuppressor K) (blockExpand V) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := rfl
  monotone := monotone_blockExpand
  visibilityReplace_comm x k _ i _ := blockExpand_visibilityReplace x k i

/-- **The expansion sends only `⊥` to `⊥`.** -/
@[simp] theorem blockExpand_eq_bot_iff {x : Label.{u}} : blockExpand V x = ⊥ ↔ x = ⊥ := by
  induction x using recBotCoeTop with
  | bot => simp
  | top => simp
  | coe a =>
    rw [blockExpand_coe]
    by_cases h : ∃ j, j < blockCount V ∧ blockOf a = ω * (j : Ordinal.{u})
    · obtain ⟨j, hj, haj⟩ := h
      rw [expandOrd_of hj haj]
      simp
    · rw [expandOrd_of_not h]
      simp

/-- **The expansion inverts the compression on `V`.** -/
theorem blockExpand_blockCompress {x : Label.{u}} (hx : x ∈ V) (K : ℕ) :
    blockExpand V (blockCompress V K x) = x := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top =>
    rw [blockCompress_top, blockExpand_coe, expandOrd_of_not]
    rintro ⟨j, hj, h⟩
    rw [blockOf_add_natCast (isSuccPrelimit_omega0_mul _), omega0_mul_natCast_inj] at h
    omega
  | coe a =>
    have hS := blockOf_mem_blockSet hx
    have hr := blockRank_lt hS
    rw [blockCompress_coe hx, blockExpand_coe,
      expandOrd_of hr (blockOf_add_natCast (isSuccPrelimit_omega0_mul _) _),
      finNat_add_natCast (isSuccPrelimit_omega0_mul _), nthBlock_blockRank hS,
      blockOf_add_finNat]


end VaughtConjecture.Label
