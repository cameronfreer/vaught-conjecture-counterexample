/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CappedDonorReading
import VaughtConjecture.Realization.PrivateContext

/-!
# The private context with the margin

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the private context with its reference
cells and the margin of the capped reading); the private context of
`VaughtConjecture.Realization.PrivateContext` and the reference data of
`VaughtConjecture.Extension.CappedDonorReading`.

Let `R` be a model at a stage `α` that is zero or a limit, `x` an occurrence (the **root**), `d` a
stage type on `x.arity + 1` points (the **donor**), and `ν < α` an ordinal (the **cutoff**).  The
**requested blocks** are the blocks of the ordinal labels of `d` together with the block of `ν`
(a block is indexed by `b`, it is the interval `[ω * b, ω * b + ω)`).

**The private context with the margin** (`Realization.IsModel.exists_marginContext`): an
occurrence `y` containing `x` as a literal face along `f`, of arity `n` above `x.arity + 1` and at
least a requested `N₀`, with reference data `P` on the cells of the type of `y`
(`CappedDonorReading.PrivateReference`) whose cap has graded index `(univ, n)`, whose full grade
is `n`, whose blocks are the requested blocks, and which has the margin
(`CappedDonorReading.PrivateReference.HasMargin`): the cap is labelled at least every
`ω * b + n`.  The donor reads in the blocks (every ordinal label lies in a requested block, with
finite part at most `n`), and the cutoff lies strictly below the cut of the actual labels:
`ν < max_b (ω * b + n)`; the finite parts of the ordinal labels of the donor are below `n`; and
the margin is strict: the cap is labelled strictly above every `ω * b + n`.

The proof follows `Realization.IsModel.exists_privateContext`: one uniformity step per requested
block gives the reference cells, and the arity is raised by dominance; the difference is the floor
of the last dominance step, `max_b (ω * b + n)` with `n` the final arity, fixed in advance.  Since
`α` is zero or a limit, that floor lies below `α`.  Of the clauses of a model only uniformity,
high-arity dominance and exact consistency (for the reference cells to survive the padding) are
used.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`, beside
`VaughtConjecture.Realization.PrivateContext`.

## References

The private context is that of [Kni26, Lemma 8.1.1], clauses 3 and 4.
-/

universe u v

namespace VaughtConjecture

open Finset Label
open scoped Ordinal

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-- The **requested block** of a donor label: its block if it is an ordinal, and `b₀` otherwise. -/
noncomputable def requestedBlock (b₀ : Ordinal.{u}) : Label.{u} → Ordinal.{u} :=
  recBotCoeTop b₀ (fun o ↦ o / ω) b₀

variable (hR : R.IsModel)
include hR

/-- **The private context with the margin.**  Over an occurrence `x`, for a donor `d` on
`x.arity + 1` points and a cutoff `ν < α` at a stage `α` that is zero or a limit: an occurrence
`y` containing `x` as a literal face along `f`, of arity `n` above `x.arity + 1` and at least
`N₀`, and reference data `P` on its cells with full grade `n`, a cap of graded index `(univ, n)`,
the requested blocks (those of the ordinal labels of `d` and that of `ν`), and the margin.  The
donor reads in the blocks, with finite parts below `n`, and `ν` lies below the cut of the actual
labels. -/
theorem IsModel.exists_marginContext (hα : Order.IsSuccPrelimit α) (x : R.Occurrence)
    (d : StageType.{u} α (x.arity + 1)) {ν : Ordinal.{u}} (hν : ν < α) (N₀ : ℕ) :
    ∃ (y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity)
      (P : CappedDonorReading.PrivateReference.{u} (Fin y.type.card)),
      f.trans y.tuple = x.tuple ∧ x.arity + 1 < y.arity ∧ N₀ ≤ y.arity ∧
        P.fullGrade = y.arity ∧ y.type.toCellScheme.gradedIndex P.cap = (univ, y.arity) ∧
        P.HasMargin y.type.rows y.type.label ∧ P.ReadsInBlocks d.label ∧
        ν / ω ∈ P.blocks ∧ ((ν : Ordinal.{u}) : Label.{u}) < P.cut y.type.label ∧
        (∀ (t : Fin d.card) (o : Ordinal.{u}), d.label t = o → o % ω < (y.arity : Ordinal.{u})) ∧
        ∀ b ∈ P.blocks, ((ω * b + P.fullGrade : Ordinal.{u}) : Label.{u}) < y.type.label P.cap := by
  classical
  -- the requested blocks, and a bound on the finite parts of the donor's ordinal labels
  let blocks : Finset Ordinal.{u} :=
    insert (ν / ω) (univ.image fun j ↦ requestedBlock (ν / ω) (d.label j))
  let fp : Label.{u} → ℕ := recBotCoeTop 0 (fun o ↦ finitePart o) 0
  let Dd : ℕ := univ.sup fun j ↦ fp (d.label j)
  have hblk : ∀ (j : Fin d.card) (o : Ordinal.{u}), d.label j = o →
      o / ω ∈ blocks ∧ finitePart o ≤ Dd := by
    intro j o ho
    refine ⟨mem_insert_of_mem (mem_image.mpr ⟨j, mem_univ _, ?_⟩), ?_⟩
    · rw [ho]; rfl
    · have h : fp (d.label j) ≤ Dd := le_sup (f := fun j ↦ fp (d.label j)) (mem_univ j)
      rwa [ho] at h
  have hblk_lt : ∀ b ∈ blocks, ω * b < α := by
    have hν' : ω * (ν / ω) < α := (Ordinal.mul_div_le ν ω).trans_lt hν
    intro b hb
    rcases mem_insert.mp hb with rfl | hb
    · exact hν'
    obtain ⟨j, -, rfl⟩ := mem_image.mp hb
    induction hj : d.label j using recBotCoeTop with
    | bot => exact hν'
    | top => exact hν'
    | coe o =>
      have ho : o < α := atStage_coe.mp (hj ▸ d.atStage j)
      exact (Ordinal.mul_div_le o ω).trans_lt ho
  have hα0 : (0 : Ordinal.{u}) < α := zero_le.trans_lt hν
  -- reference cells by uniformity, one per requested block
  obtain ⟨y₁, f₁, K, B, hf₁, -, hBα, hanc⟩ :=
    hR.exists_extend_uniformity x hα0 (blocks.toList.map (ω * ·)) fun μ hμ ↦ by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hμ
      exact ⟨isSuccPrelimit_omega0_mul b, hblk_lt b (mem_toList.mp hb)⟩
  -- the final arity, fixed in advance, and the floor of the last dominance step
  let k : ℕ := x.arity + 1 + N₀ + K + Dd + finitePart ν
  let n : ℕ := y₁.arity + (k + 1)
  let γ : Ordinal.{u} := max B (blocks.sup fun b ↦ ω * b + n)
  have hγ : γ < α := max_lt hBα ((Finset.sup_lt_iff hα0).mpr fun b hb ↦
    hα.add_natCast_lt (hblk_lt b hb) n)
  obtain ⟨y, f₂, hf₂, hy, C, hC, hγC⟩ := hR.exists_extend_dominance y₁ hγ k
  have hyn : y.arity = n := hy
  -- the reference cells survive in `y`
  have href : ∀ b ∈ blocks, ∃ z : Fin y.type.card, ∃ kb < K,
      y.type.label z = ((ω * b + kb : Ordinal.{u}) : Label.{u}) := by
    intro b hb
    obtain ⟨z₁, kb, hkb, hz₁, -⟩ :=
      hanc (ω * b) (List.mem_map.mpr ⟨b, mem_toList.mpr hb, rfl⟩)
    obtain ⟨z, hz⟩ := Occurrence.exists_label_eq_of_trans_eq hR.isConsistent hf₂ z₁
    exact ⟨z, kb, hkb, hz.trans hz₁⟩
  have : Nonempty (Fin y.type.card) := ⟨C⟩
  choose! zf kf hkf hzf using href
  let P : CappedDonorReading.PrivateReference.{u} (Fin y.type.card) :=
    ⟨C, y.arity, blocks, zf, fun b ↦ kf b.1⟩
  have hP : P.HasMargin y.type.rows y.type.label :=
    { isLawful := y.type.isLawful
      mem_below := fun z ↦ by
        -- Membership below the cap is the comparison of graded indices.
        change y.type.toCellScheme.gradedIndex z ≤ y.type.toCellScheme.gradedIndex C
        rw [hC, CellScheme.gradedIndex_le_iff]
        refine ⟨subset_univ _, ?_⟩
        calc y.type.toCellScheme.grade z ≤ #(y.type.toCellScheme.scope z) :=
              y.type.isWellFormed.isWellFormed.grade_le_card z
          _ ≤ #(univ : Finset (Fin y.arity)) := card_le_card (subset_univ _)
          _ = y.arity := by simp
      grade_cap := congrArg Prod.snd hC
      off_lt := fun b hb ↦ by
        -- The full grade of `P` is the arity of `y` (by definition).
        change kf b < y.arity
        have := hkf b hb
        omega
      label_ref := fun b hb ↦ hzf b hb
      margin := fun b hb ↦ by
        refine le_of_lt (lt_of_le_of_lt ?_ hγC)
        refine WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ?_)
        -- The full grade of `P` is the arity of `y` (by definition).
        change ω * b + (y.arity : Ordinal.{u}) ≤ γ
        rw [hyn]
        exact le_max_of_le_right (le_sup (f := fun b ↦ ω * b + (n : Ordinal.{u})) hb) }
  refine ⟨y, f₁.trans f₂, P, by rw [Function.Embedding.trans_assoc, hf₂, hf₁], by omega,
    by omega, rfl, hC, hP, fun t o ho ↦ ?_, mem_insert_self _ _, ?_, fun t o ho ↦ ?_,
    fun b hb ↦ ?_⟩
  · obtain ⟨h₁, h₂⟩ := hblk t o ho
    refine ⟨h₁, ?_⟩
    rw [← natCast_finitePart]
    -- The full grade of `P` is the arity of `y` (by definition).
    change ((finitePart o : ℕ) : Ordinal.{u}) ≤ (y.arity : Ordinal.{u})
    exact_mod_cast (show finitePart o ≤ y.arity by omega)
  · rw [hP.cut_eq]
    refine lt_of_lt_of_le ?_ (le_sup (f := fun b ↦ ((ω * b + P.fullGrade : Ordinal.{u}) :
      Label.{u})) (mem_insert_self (ν / ω) _))
    refine WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ?_)
    conv_lhs => rw [← omega0_mul_div_add_finitePart ν]
    -- The full grade of `P` is the arity of `y` (by definition).
    change ω * (ν / ω) + (finitePart ν : Ordinal.{u}) < ω * (ν / ω) + (y.arity : Ordinal.{u})
    exact (add_lt_add_iff_left _).mpr (by exact_mod_cast (show finitePart ν < y.arity by omega))
  · obtain ⟨-, h₂⟩ := hblk t o ho
    rw [← natCast_finitePart]
    exact_mod_cast (show finitePart o < y.arity by omega)
  · refine lt_of_le_of_lt (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ?_)) hγC
    -- The full grade of `P` is the arity of `y` (by definition).
    change ω * b + (y.arity : Ordinal.{u}) ≤ γ
    rw [hyn]
    exact le_max_of_le_right (le_sup (f := fun b ↦ ω * b + (n : Ordinal.{u})) hb)

end Realization

end VaughtConjecture
