/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerBand
import VaughtConjecture.Continuation.ReadingLayerRootOffsets

/-!
# The band fill

Roadmap, Layer 3 ((R3) of the table of 3.4).

The fill at the short positive caps from the left coatom (`TowerProfile.ReadingFillPos`) in the
band case: a labelling `f` lawful below the left coatom, agreeing with a reading mark `e` capped at
`h`, with a value in `[h, f r)` at a cell of the left coatom.  The fill is built directly at every
grade, not as a union of two lifts along `e`.

* **A block threshold** (`Label.isWitness_blockStep`, compiled in this repository (theorem
  named)): the map sending the labels at least `ω * β` to `a` and the others to `⊥` is a witness
  bounded by every grade at which `a` is self-visible (visibility replacement keeps the block).
* **The fill from a server** (`TowerProfile.exists_three_of_server`,
  `TowerProfile.exists_fill_of_server`, compiled): let `u` be a cell of graded index `(univ, 1)`
  with `h ≤ e u` whose row `ρ` reads a cell `x` of grade `1` (with `h ≤ e x`) at `ω * β + 1` and the
  cells of grade `1` of the left coatom not `⊥` in `f` below the block `β`.  Suppose `f` takes one
  value `A ≥ h` at those cells, a value `V` (self-visible at `2`, `h ≤ V ≤ A`) is at most every
  value of `f` at least `h` at the cells of the left coatom of grade at most `2` and at least those
  of grade `2`, and `f ≤ h` at the cells of the left coatom of grade `3`.  Then some labelling
  lawful below `(univ, 4)` is `f` on the left coatom, agrees with `e` capped at `h`, and is `⊤` at
  `x`.  The labelling: `f` on the left coatom; at the other cells of grade `1`, the row `ρ` decoded
  by `max (min (raise h ∘ τ) A) (blockStep β ⊤)`, where `τ` carries `ρ` to `e` capped at `h`
  (lawful by the transport with `e` as companion); at the other cells of grade `2`, `e` raised to
  `V` above `h`; at those of grade `3`, `e` capped at `h`; at the grade `4`, the completion along
  `e` (`TowerProfile.exists_isLawfulBelow_four`).  The right coatom needs no separate extension: its
  cells are cells of grade at most `3` off the left coatom, labelled by the same rules (the new top
  `x` at `⊤`).  The cap agreement on the new cells holds because each rule is the identity below
  `h`; locality at a new cell of grade `2` or `3` is that of the raised (or capped) `e`, every cell
  below it being `e` below `h` and at least `V` (or `h`) at or above it; availability at those
  grades is that of `e`.  No union of two lifts and no extension from a boundary is used.
* **The fill from the tie of the marker** (`TowerProfile.readingFillPos_left_of_tie`, compiled):
  at a seed whose right coatom type raises at the point `3` (`StageType.RowsRaiseAt`: its cells of
  grade `1` through `3` read the cells through `3` as themselves and the others as `⊥`; `rightType`
  does), with the marker `r` of grade `4` on the left
  coatom, a new top `x` of grade `1` through the point `4`, and cells `t₁`, `t₂` of grades `1`, `2`
  of the left coatom.  Hypotheses: in every labelling lawful below the left coatom and not `⊥` at
  `r`, the cells of grade `1` not `⊥` take the value at `t₁`, the only cell of grade `2` not `⊥` is
  `t₂`, the cells of grade `3` are `⊥`; the marker is a cell `c` of the left coatom type labelled
  `⊤`, of full scope and grade at least the arity of a root `ι`, with **the root offsets below its
  grade** (`StageType.RootOffsetsBelow`, the acquisition condition), and `t₁`, `t₂` carry one
  proper root label.  Then the fill holds for `X = {x}`: the marker keeps the tie of `t₁` and `t₂`
  (`StageType.keepsProperRootTies_of_rootOffsetsBelow`), its row reading `t₂` at most as `t₁`.
  In the band the tie gives `h ≤ f t₁` and `f t₂ ≤ f t₁`; the server is
  `TowerProfile.exists_server_of_rightType` (one cell for all the cells of the left coatom,
  reading `x` at a code of the grade `1`); the fill is the fill from the server with `A = f t₁`
  and `V = max h (f t₂)`.
* **At `seedThree`**: the hypotheses hold (module
  `VaughtConjecture.Continuation.ReadingLayerCoatoms`, where they are stated as conditions on the
  two coatom types and checked at `threeType` and `rightType`), so the restricted reading layer at
  `seedThree` is legal below the full grade.

**The schema.**  The hypothesis on the marker in the compiled theorem is the acquisition condition:
every proper root label has finite part below the grade of the cap (at `seedThree` the proper
label is `3` and the grade is `4`).  The tie of the marker follows from it
(`StageType.keepsProperRootTies_of_rootOffsetsBelow`, module
`VaughtConjecture.Continuation.ReadingLayerRootOffsets`).  The structure hypotheses on the left
coatom are stated on the cells of the profile layer here; on the coatom types in the module
`VaughtConjecture.Continuation.ReadingLayerCoatoms`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label
open Ordinal hiding univ

/-! ### A block threshold -/

namespace Label

open Classical in
/-- **The block threshold** at the block `β`: `a` at the labels at least `ω * β`, `⊥` below. -/
noncomputable def blockStep (β : Ordinal.{u}) (a x : Label.{u}) : Label.{u} :=
  if (((ω * β : Ordinal.{u}) : Label.{u})) ≤ x then a else ⊥

/-- Visibility replacement keeps the block of an ordinal. -/
theorem omega0_mul_le_visibilityReplace_iff (β : Ordinal.{u}) (k i : ℕ) (x : Label.{u}) :
    (((ω * β : Ordinal.{u}) : Label.{u})) ≤ visibilityReplace k i x ↔
      (((ω * β : Ordinal.{u}) : Label.{u})) ≤ x := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe o =>
    rw [visibilityReplace_coe, WithBot.coe_le_coe, WithTop.coe_le_coe, WithBot.coe_le_coe,
      WithTop.coe_le_coe, Ordinal.visibilityReplace]
    have key : ∀ q : Ordinal.{u}, ∀ n : ℕ, ω * β ≤ ω * q + n ↔ β ≤ q := fun q n ↦ by
      rw [Ordinal.mul_le_iff_le_div omega0_ne_zero, Ordinal.mul_add_div _ omega0_ne_zero,
        Ordinal.div_eq_zero_of_lt (natCast_lt_omega0 n), add_zero]
    have ho : ω * β ≤ o ↔ β ≤ o / ω := Ordinal.mul_le_iff_le_div omega0_ne_zero
    split_ifs with h
    · rw [key, ho]
    · obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (Ordinal.mod_lt o omega0_ne_zero)
      rw [hn, key, ho]

/-- **The block threshold is a witness** bounded by every grade `K` at which `a` is self-visible:
visibility replacement keeps the block of a label. -/
theorem isWitness_blockStep {K : ℕ} (β : Ordinal.{u}) {a : Label.{u}} (ha : IsSelfVisible K a) :
    IsWitness (stepSuppressor K) (blockStep β a) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := by
    unfold blockStep
    exact ite_eq_right (not_le.mpr (WithBot.bot_lt_coe _))
  monotone := by
    intro x y hxy
    unfold blockStep
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.trans hxy) h2
    · exact bot_le
    · exact le_rfl
  visibilityReplace_comm x k hx i hi := by
    unfold blockStep at hx ⊢
    by_cases h : (((ω * β : Ordinal.{u}) : Label.{u})) ≤ x
    · rw [ite_eq_left ((omega0_mul_le_visibilityReplace_iff β k i x).mpr h)]
      rw [ite_eq_left h] at hx ⊢
      by_cases hk : k ≤ K
      · exact ((ha.mono hk).visibilityReplace_eq i).symm
      · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
        rw [hx, visibilityReplace_bot]
    · rw [ite_eq_right fun h' ↦ h ((omega0_mul_le_visibilityReplace_iff β k i x).mp h'),
        ite_eq_right h, visibilityReplace_bot]

end Label

/-! ### Capped agreement -/

namespace Label

variable {a b h : Label.{u}}

/-- At or above the cap, a label agreeing capped with another is at or above it too. -/
theorem le_of_min_eq_of_le' (hab : min a h = min b h) (hb : h ≤ b) : h ≤ a := by
  rw [min_eq_right hb] at hab
  exact min_eq_right_iff.mp hab

/-- An ordinal label self-visible at `1` and at least `ω * β` is at least `ω * β + 1`. -/
theorem omega0_mul_add_one_le {β : Ordinal.{u}} {t : Label.{u}} (ht : IsSelfVisible 1 t)
    (hβ : (((ω * β : Ordinal.{u}) : Label.{u})) ≤ t) :
    (((ω * β + 1 : Ordinal.{u}) : Label.{u})) ≤ t := by
  induction t using recBotCoeTop with
  | bot => exact absurd hβ (not_le.mpr (WithBot.bot_lt_coe _))
  | top => exact le_top
  | coe o =>
    rw [WithBot.coe_le_coe, WithTop.coe_le_coe] at hβ ⊢
    have h1 : (1 : Ordinal.{u}) ≤ o % ω := by exact_mod_cast isSelfVisible_coe.mp ht
    have hq : β ≤ o / ω := (Ordinal.mul_le_iff_le_div omega0_ne_zero).mp hβ
    rcases hq.lt_or_eq with hlt | heq
    · exact ((omega0_mul_add_natCast_lt hlt 1 0).trans_le
        (by rw [add_zero]; exact Ordinal.mul_div_le o ω)).le.trans' (by simp)
    · calc ω * β + 1 ≤ ω * β + o % ω := (add_le_add_iff_left _).mpr h1
        _ = o := by rw [heq]; exact Ordinal.div_add_mod o ω

end Label

/-! ### The fill from a server -/

namespace TowerProfile

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- The row of a cell, read below its graded index, is lawful there. -/
theorem isLawfulBelow_rowAt {u : Fin (scheme I).card} {Y : Finset (Fin 5) × ℕ}
    (hu : (scheme I).toCellScheme.gradedIndex u = Y) :
    (scheme I).rows.IsLawfulBelow Y fun d ↦ (scheme I).rowAt u d := by
  have h1 := CellScheme.Rows.isLawfulBelow_rowBelow (R := (scheme I).rows) hu
    (isConsistent_scheme u)
  convert h1 using 1
  funext d
  exact Scheme.rowAt_of_mem (le_trans d.2 hu.ge)

/-- **A code at the grade `1` is a block plus one**: a value of the code grid at the grade `1`,
self-visible at `1` and not `⊥`, is `ω * β + 1`. -/
theorem exists_eq_omega0_mul_add_one {B : ℕ} {t : Label.{u}} (ht : t ∈ codeGrid 1 B)
    (hvis : IsSelfVisible 1 t) (ht0 : t ≠ ⊥) :
    ∃ β : Ordinal.{u}, t = ((ω * β + 1 : Ordinal.{u}) : Label.{u}) := by
  rcases mem_codeGrid.mp ht with h | ⟨b, -, f, hf, rfl⟩
  · exact absurd h ht0
  have h1 : (1 : Ordinal.{u}) ≤ (f : Ordinal.{u}) := by
    have := isSelfVisible_coe.mp hvis
    rwa [Ordinal.mul_add_mod_self, Ordinal.natCast_mod_omega0, Nat.cast_one] at this
  have hf1 : f = 1 := le_antisymm hf (by exact_mod_cast h1)
  exact ⟨b, by rw [hf1, Nat.cast_one]⟩

/-- Below `ω * β + 1`, a label self-visible at `1` is below `ω * β`. -/
theorem lt_omega0_mul_of_lt_add_one {β : Ordinal.{u}} {t : Label.{u}} (hvis : IsSelfVisible 1 t)
    (ht : t < ((ω * β + 1 : Ordinal.{u}) : Label.{u})) :
    t < ((ω * β : Ordinal.{u}) : Label.{u}) :=
  not_le.mp fun h ↦ not_le.mpr ht (Label.omega0_mul_add_one_le hvis h)

/-- **A labelling of the cells of grade at most `3` from a server.**  Let `e` be lawful below
`(univ, 4)` in the profile layer, `h` a positive cap self-visible at `4`, and `f` lawful below the
left coatom agreeing with `e` capped at `h`.  Let `x` be a cell of grade `1` with `h ≤ e x`, and
`u` a cell of graded index `(univ, 1)` with `h ≤ e u` (a server) whose row reads `x` at
`ω * β + 1` and every cell of grade `1` of the left coatom not `⊥` in `f` below the block `β`.
Suppose that `f` takes one value `A ≥ h` at those cells, that a value `V` with
`h ≤ V ≤ A`, self-visible at `2`, bounds below the values of `f` at least `h` at the cells of the
left coatom of grade at most `2` and bounds above those of grade `2`, and that `f` is at most `h`
at the cells of the left coatom of grade `3`.  Then some labelling lawful below `(univ, 3)` is `f`
on the left coatom, agrees with `e` capped at `h`, and is `⊤` at `x`.

The labelling is `f` on the left coatom; at the other cells of grade `1` it is the row `ρ` of `u`
read by `ν = max (min (raise h ∘ τ) A) (blockStep β ⊤)`, where `τ` is the witness carrying `ρ` to
`e` capped at `h` (`CellScheme.Rows.exists_isWitness_rowBelow`), lawful by the transport with `e` as
companion (`CellScheme.Rows.IsLawfulBelow.map_of_bot_iff`); at the other cells of grade `2` it is
`e` raised to `V` above `h`, and at those of grade `3` it is `e` capped at `h`.  Locality at a
cell of grade `2` or `3` off the coatom is that of the raised `e`, since every cell below it is
`e` below `h` and at least `V` (or `h`) at or above it. -/
theorem exists_three_of_server {e : Fin (scheme I).card → Label.{u}}
    (he : (scheme I).rows.IsLawfulBelow (univ, 4) fun d ↦ e d)
    {h : Label.{u}} (hh : IsSelfVisible 4 h) (hhb : ⊥ < h)
    {f : Fin (scheme I).card → Label.{u}}
    (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d)
    (hfe : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      min (f d) h = min (e d) h)
    {x : Fin (scheme I).card} (hgx : (scheme I).toCellScheme.grade x = 1) (hex : h ≤ e x)
    {u : Fin (scheme I).card}
    (hu : (scheme I).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), 1)) (heu : h ≤ e u)
    {β : Ordinal.{u}} (hux : (scheme I).rowAt u x = ((ω * β + 1 : Ordinal.{u}) : Label.{u}))
    {A : Label.{u}} (hA : IsSelfVisible 1 A) (hhA : h ≤ A)
    (hfA : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.grade d = 1 → f d ≠ ⊥ →
        f d = A ∧ (scheme I).rowAt u d < ((ω * β : Ordinal.{u}) : Label.{u}))
    {V : Label.{u}} (hV : IsSelfVisible 2 V) (hhV : h ≤ V) (hVA : V ≤ A)
    (hfV : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.grade d ≤ 2 → h ≤ f d → V ≤ f d)
    (hfV' : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.grade d = 2 → h ≤ f d → f d ≤ V)
    (hf3 : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.grade d = 3 → f d ≤ h) :
    ∃ w : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 3) (fun d ↦ w d) ∧
      (∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4), w d = f d) ∧
      (∀ d ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        min (w d) h = min (e d) h) ∧ w x = ⊤ := by
  classical
  set C := (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) with hCdef
  have hh0 : h ≠ ⊥ := hhb.ne'
  have hA0 : A ≠ ⊥ := (hhb.trans_le hhA).ne'
  have hV0 : V ≠ ⊥ := (hhb.trans_le hhV).ne'
  have hpos (d : Fin (scheme I).card) : 1 ≤ (scheme I).toCellScheme.grade d :=
    isWellFormed_scheme.isWellFormed.grade_pos d
  have hmem1 {d : Fin (scheme I).card} (hd : (scheme I).toCellScheme.grade d = 1) :
      d ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 1) :=
    ⟨subset_univ _, hd.le⟩
  -- the row of the server
  set ρ : Fin (scheme I).card → Label.{u} := fun d ↦ (scheme I).rowAt u d with hρdef
  have hρl : (scheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 1) fun d ↦ ρ d :=
    isLawfulBelow_rowAt hu
  have he1 : (scheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 1) fun d ↦ e d :=
    he.mono (X := ((univ : Finset (Fin 5)), 1)) ⟨subset_rfl, by omega⟩
  obtain ⟨τ, hτ, -, hτρ⟩ := CellScheme.Rows.exists_isWitness_rowBelow (R := (scheme I).rows) hu
    he1 (c := h) (hh.mono (by omega)) heu
  have hτ' {d : Fin (scheme I).card}
      (hd : d ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 1)) :
      τ (ρ d) = min (e d) h := by
    have := hτρ ⟨d, hd⟩
    rwa [show CellScheme.Rows.rowBelow (scheme I).rows u hu ⟨d, hd⟩ = ρ d from
      (Scheme.rowAt_of_mem (le_trans hd hu.ge)).symm] at this
  -- the decoder of the row
  set ν : Label.{u} → Label.{u} := fun t ↦ max (min (raise h (τ t)) A) (blockStep β ⊤ t)
    with hνdef
  have hν : IsWitness (stepSuppressor 1) ν := by
    have h1 : IsWitness (stepSuppressor 1) ((fun t ↦ min (raise h t) A) ∘ τ) :=
      hτ.comp_of_bot_reflecting
        ((isWitness_raise (K := 1) (hh.mono (by omega)) hhb).min_const hA) fun t ht ↦
          eq_bot_of_raise_eq_bot ((min_eq_bot.mp ht).resolve_right hA0)
    exact h1.max (isWitness_blockStep β (isSelfVisible_top 1))
  -- reading `x` and above
  have hρx : ρ x = ((ω * β + 1 : Ordinal.{u}) : Label.{u}) := hux
  have hτx : τ (ρ x) = h := by rw [hτ' (hmem1 hgx), min_eq_right hex]
  have hhigh {d : Fin (scheme I).card}
      (hd : d ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 1))
      (hβd : (((ω * β : Ordinal.{u}) : Label.{u})) ≤ ρ d) : h ≤ e d := by
    have hvis : IsSelfVisible 1 (ρ d) := by
      have := (CellScheme.Rows.isLawfulBelow_iff_forall.mp hρl).1 d hd
      rwa [show (scheme I).toCellScheme.grade d = 1 from le_antisymm hd.2 (hpos d)] at this
    have hle : τ (ρ x) ≤ τ (ρ d) := hτ.monotone (hρx ▸ omega0_mul_add_one_le hvis hβd)
    rw [hτx, hτ' hd] at hle
    exact le_trans hle (min_le_left _ _)
  have hνbot {d : Fin (scheme I).card}
      (hd : d ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 1)) :
      ν (ρ d) = ⊥ ↔ e d = ⊥ := by
    constructor
    · intro h0
      have h1 : min (raise h (τ (ρ d))) A = ⊥ := le_bot_iff.mp (h0 ▸ le_max_left _ _)
      have h2 : τ (ρ d) = ⊥ := eq_bot_of_raise_eq_bot ((min_eq_bot.mp h1).resolve_right hA0)
      rw [hτ' hd] at h2
      exact (min_eq_bot.mp h2).resolve_right hh0
    · intro h0
      have hβ : ¬ (((ω * β : Ordinal.{u}) : Label.{u})) ≤ ρ d := fun hβd ↦ by
        have := hhigh hd hβd
        rw [h0] at this
        exact absurd this (not_le.mpr hhb)
      simp only [hνdef, blockStep, ite_eq_right hβ, hτ' hd, h0, min_eq_left bot_le,
        raise_bot hhb, max_eq_left bot_le]
  have hg₁ : (scheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 1) fun d ↦ ν (ρ d) :=
    hρl.map_of_bot_iff he1 (fun d ↦ d.2.2) hν fun d ↦ hνbot d.2
  -- the decoded row below and above the cap
  have hν_lt {d : Fin (scheme I).card}
      (hd : d ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 1)) (hed : e d < h) :
      ν (ρ d) = e d := by
    have hβ : ¬ (((ω * β : Ordinal.{u}) : Label.{u})) ≤ ρ d := fun hβd ↦
      absurd (hhigh hd hβd) (not_le.mpr hed)
    simp only [hνdef, blockStep, ite_eq_right hβ, hτ' hd, min_eq_left hed.le,
      show raise h (e d) = e d from ite_eq_right (not_le.mpr hed),
      min_eq_left (hed.le.trans hhA), max_eq_left bot_le]
  have hν_ge {d : Fin (scheme I).card}
      (hd : d ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 1)) (hed : h ≤ e d) :
      A ≤ ν (ρ d) := by
    refine le_trans ?_ (le_max_left _ _)
    rw [hτ' hd, min_eq_right hed, show raise h h = ⊤ from ite_eq_left le_rfl, min_top_left]
  -- the cells of grade `1` of the left coatom
  have hF1 {d : Fin (scheme I).card} (hdC : d ∈ C)
      (hd : (scheme I).toCellScheme.grade d = 1) : f d = ν (ρ d) := by
    by_cases hf0 : f d = ⊥
    · have he0 : e d = ⊥ := by
        have := hfe d hdC
        rw [hf0, min_eq_left bot_le] at this
        exact (min_eq_bot.mp this.symm).resolve_right hh0
      rw [hf0, (hνbot (hmem1 hd)).mpr he0]
    · obtain ⟨hfdA, hρd⟩ := hfA d hdC hd hf0
      have hed : h ≤ e d := Label.le_of_min_eq_of_le' (hfe d hdC).symm (hfdA ▸ hhA)
      have hβ : ¬ (((ω * β : Ordinal.{u}) : Label.{u})) ≤ ρ d := not_le.mpr hρd
      simp only [hνdef, blockStep, ite_eq_right hβ, hτ' (hmem1 hd), min_eq_right hed,
        show raise h h = ⊤ from ite_eq_left le_rfl, min_top_left, max_eq_left bot_le, hfdA]
  -- the raised and capped ambient
  set Θ₂ : Label.{u} → Label.{u} := fun z ↦ min (raise h z) V with hΘ₂def
  set Θ₃ : Label.{u} → Label.{u} := fun z ↦ min z h with hΘ₃def
  have hΘ₂ : IsWitness (stepSuppressor 2) Θ₂ :=
    (isWitness_raise (K := 2) (hh.mono (by omega)) hhb).min_const hV
  have hΘ₃ : IsWitness (stepSuppressor 3) Θ₃ := (IsWitness.id_step 3).min_const (hh.mono (by omega))
  have he2 : (scheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 2) fun d ↦ Θ₂ (e d) :=
    (he.mono (X := ((univ : Finset (Fin 5)), 2)) ⟨subset_rfl, by omega⟩).map_of_apply_eq_bot
      (fun d ↦ d.2.2) hΘ₂ fun _ h0 ↦ eq_bot_of_raise_eq_bot ((min_eq_bot.mp h0).resolve_right hV0)
  have he3 : (scheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun d ↦ Θ₃ (e d) :=
    (he.mono (X := ((univ : Finset (Fin 5)), 3)) ⟨subset_rfl, by omega⟩).map_of_apply_eq_bot
      (fun d ↦ d.2.2) hΘ₃ fun _ h0 ↦ (min_eq_bot.mp h0).resolve_right hh0
  have hΘ₂_lt {z : Label.{u}} (hz : z < h) : Θ₂ z = z := by
    simp only [hΘ₂def, show raise h z = z from ite_eq_right (not_le.mpr hz),
      min_eq_left (hz.le.trans hhV)]
  have hΘ₂_ge {z : Label.{u}} (hz : h ≤ z) : Θ₂ z = V := by
    simp only [hΘ₂def, show raise h z = ⊤ from ite_eq_left hz, min_top_left]
  have hΘ₂_le (z : Label.{u}) : Θ₂ z ≤ V := min_le_right _ _
  -- the labelling
  set w : Fin (scheme I).card → Label.{u} := fun d ↦
    if d ∈ C then f d
    else if (scheme I).toCellScheme.grade d = 1 then ν (ρ d)
    else if (scheme I).toCellScheme.grade d = 2 then Θ₂ (e d) else Θ₃ (e d) with hwdef
  have hwC {d : Fin (scheme I).card} (hd : d ∈ C) : w d = f d := ite_eq_left hd
  have hw1 {d : Fin (scheme I).card} (hd : (scheme I).toCellScheme.grade d = 1) :
      w d = ν (ρ d) := by
    by_cases hdC : d ∈ C
    · rw [hwC hdC, hF1 hdC hd]
    · simp only [hwdef, ite_eq_right hdC, ite_eq_left hd]
  have hw2 {d : Fin (scheme I).card} (hdC : d ∉ C) (hd : (scheme I).toCellScheme.grade d = 2) :
      w d = Θ₂ (e d) := by
    have h1 : (scheme I).toCellScheme.grade d ≠ 1 := by omega
    simp only [hwdef, ite_eq_right hdC, ite_eq_right h1, ite_eq_left hd]
  have hw3 {d : Fin (scheme I).card} (hdC : d ∉ C) (hd : (scheme I).toCellScheme.grade d = 3) :
      w d = Θ₃ (e d) := by
    have h1 : (scheme I).toCellScheme.grade d ≠ 1 := by omega
    have h2 : (scheme I).toCellScheme.grade d ≠ 2 := by omega
    simp only [hwdef, ite_eq_right hdC, ite_eq_right h1, ite_eq_right h2]
  -- the invariants
  have hinv2 {d : Fin (scheme I).card} (hd : (scheme I).toCellScheme.grade d ≤ 2) :
      (e d < h → w d = e d) ∧ (h ≤ e d → V ≤ w d) := by
    by_cases hdC : d ∈ C
    · rw [hwC hdC]
      exact ⟨fun hed ↦ Label.eq_of_min_eq_of_lt (hfe d hdC).symm hed, fun hed ↦
        hfV d hdC hd (Label.le_of_min_eq_of_le' (hfe d hdC) hed)⟩
    · rcases (show (scheme I).toCellScheme.grade d = 1 ∨ (scheme I).toCellScheme.grade d = 2 by
        have := hpos d; omega) with h1 | h2
      · rw [hw1 h1]
        exact ⟨hν_lt (hmem1 h1), fun hed ↦ hVA.trans (hν_ge (hmem1 h1) hed)⟩
      · rw [hw2 hdC h2]
        exact ⟨hΘ₂_lt, fun hed ↦ (hΘ₂_ge hed).ge⟩
  have hinv3 {d : Fin (scheme I).card} (hd : (scheme I).toCellScheme.grade d ≤ 3) :
      (e d < h → w d = e d) ∧ (h ≤ e d → h ≤ w d) := by
    by_cases hd2 : (scheme I).toCellScheme.grade d ≤ 2
    · exact ⟨(hinv2 hd2).1, fun hed ↦ hhV.trans ((hinv2 hd2).2 hed)⟩
    have hd3 : (scheme I).toCellScheme.grade d = 3 := by omega
    by_cases hdC : d ∈ C
    · rw [hwC hdC]
      exact ⟨fun hed ↦ Label.eq_of_min_eq_of_lt (hfe d hdC).symm hed,
        Label.le_of_min_eq_of_le' (hfe d hdC)⟩
    · rw [hw3 hdC hd3]
      exact ⟨fun hed ↦ min_eq_left hed.le, fun hed ↦ le_of_eq (min_eq_right hed).symm⟩
  have hub2 {d : Fin (scheme I).card} (hd : (scheme I).toCellScheme.grade d = 2) :
      w d ≤ Θ₂ (e d) := by
    by_cases hdC : d ∈ C
    · rw [hwC hdC]
      rcases lt_or_ge (e d) h with hed | hed
      · rw [Label.eq_of_min_eq_of_lt (hfe d hdC).symm hed, hΘ₂_lt hed]
      · rw [hΘ₂_ge hed]
        exact hfV' d hdC hd (Label.le_of_min_eq_of_le' (hfe d hdC) hed)
    · rw [hw2 hdC hd]
  have hub3 {d : Fin (scheme I).card} (hd : (scheme I).toCellScheme.grade d = 3) :
      w d ≤ Θ₃ (e d) := by
    by_cases hdC : d ∈ C
    · rw [hwC hdC]
      rcases lt_or_ge (e d) h with hed | hed
      · rw [Label.eq_of_min_eq_of_lt (hfe d hdC).symm hed]
        exact le_min le_rfl hed.le
      · exact le_min ((hf3 d hdC hd).trans hed) (hf3 d hdC hd)
    · rw [hw3 hdC hd]
  -- the gluing
  have hmemC {s t : Fin (scheme I).card}
      (hst : (scheme I).toCellScheme.gradedIndex s = (scheme I).toCellScheme.gradedIndex t) :
      s ∈ C ↔ t ∈ C := by
    rw [hCdef, CellScheme.mem_below, CellScheme.mem_below, hst]
  have hCle {d s : Fin (scheme I).card}
      (hds : (scheme I).toCellScheme.gradedIndex d ≤ (scheme I).toCellScheme.gradedIndex s)
      (hs : s ∈ C) : d ∈ C := by
    rw [hCdef] at hs ⊢
    exact le_trans hds hs
  obtain ⟨hfo, hfl, hfa⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hf
  obtain ⟨hgo, hgl, hga⟩ := (CellScheme.Rows.isLawfulBelow_iff_forall (w := fun z ↦ ν (ρ z))).mp hg₁
  obtain ⟨h2o, h2l, -⟩ := (CellScheme.Rows.isLawfulBelow_iff_forall (w := fun z ↦ Θ₂ (e z))).mp he2
  obtain ⟨h3o, h3l, -⟩ := (CellScheme.Rows.isLawfulBelow_iff_forall (w := fun z ↦ Θ₃ (e z))).mp he3
  obtain ⟨-, -, hea⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp he
  have hgrade {d : Fin (scheme I).card}
      (hd : d ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3)) :
      (scheme I).toCellScheme.grade d = 1 ∨ (scheme I).toCellScheme.grade d = 2 ∨
        (scheme I).toCellScheme.grade d = 3 := by
    have h1 := hpos d
    have h2 : (scheme I).toCellScheme.grade d ≤ 3 := hd.2
    omega
  have hw : (scheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun d ↦ w d := by
    refine CellScheme.Rows.isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_,
      fun s t ht hst hg ↦ ?_⟩
    · -- order
      by_cases hdC : d ∈ C
      · rw [hwC hdC]; exact hfo d hdC
      rcases hgrade hd with h1 | h2 | h3
      · rw [hw1 h1]; exact hgo d (hmem1 h1)
      · rw [hw2 hdC h2]; exact h2o d ⟨subset_univ _, h2.le⟩
      · rw [hw3 hdC h3]; exact h3o d ⟨subset_univ _, h3.le⟩
    · -- locality
      by_cases hsC : s ∈ C
      · have heq : (fun d : (scheme I).toCellScheme.below
            ((scheme I).toCellScheme.gradedIndex s) ↦ min (w d) (w s)) =
            fun d :
              (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex s) ↦
              min (f d) (f s) :=
          funext fun d ↦ by rw [hwC hsC, hwC (hCle d.2 hsC)]
        rw [heq]
        exact hfl s hsC
      rcases hgrade hs with h1 | h2 | h3
      · have heq : (fun d : (scheme I).toCellScheme.below
            ((scheme I).toCellScheme.gradedIndex s) ↦ min (w d) (w s)) =
            fun d :
              (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex s) ↦
              min (ν (ρ d)) (ν (ρ s)) :=
          funext fun d ↦ by
            have hd1 : (scheme I).toCellScheme.grade d = 1 :=
              le_antisymm (h1 ▸ d.2.2) (hpos d)
            rw [hw1 h1, hw1 hd1]
        rw [heq]
        exact hgl s (hmem1 h1)
      · have heq : (fun d : (scheme I).toCellScheme.below
            ((scheme I).toCellScheme.gradedIndex s) ↦ min (w d) (w s)) =
            fun d :
              (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex s) ↦
              min (Θ₂ (e d)) (Θ₂ (e s)) :=
          funext fun d ↦ by
            have hd2 : (scheme I).toCellScheme.grade d ≤ 2 := h2 ▸ d.2.2
            rw [hw2 hsC h2]
            rcases lt_or_ge (e d) h with hed | hed
            · rw [(hinv2 hd2).1 hed, hΘ₂_lt hed]
            · rw [hΘ₂_ge hed, min_eq_right (hΘ₂_le _),
                min_eq_right ((hΘ₂_le _).trans ((hinv2 hd2).2 hed))]
        rw [heq]
        exact h2l s ⟨subset_univ _, h2.le⟩
      · have heq : (fun d : (scheme I).toCellScheme.below
            ((scheme I).toCellScheme.gradedIndex s) ↦ min (w d) (w s)) =
            fun d :
              (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex s) ↦
              min (Θ₃ (e d)) (Θ₃ (e s)) :=
          funext fun d ↦ by
            have hd3 : (scheme I).toCellScheme.grade d ≤ 3 := h3 ▸ d.2.2
            rw [hw3 hsC h3]
            rcases lt_or_ge (e d) h with hed | hed
            · rw [(hinv3 hd3).1 hed]
              exact congrArg (min · _) (min_eq_left hed.le).symm
            · have h1 : Θ₃ (e d) = h := min_eq_right hed
              have h2 : Θ₃ (e s) ≤ h := min_le_right _ _
              rw [h1, min_eq_right h2, min_eq_right (h2.trans ((hinv3 hd3).2 hed))]
        rw [heq]
        exact h3l s ⟨subset_univ _, h3.le⟩
    · -- availability
      by_cases htC : t ∈ C
      · have hsC : s ∈ C :=
          ⟨hst.trans htC.1, (show (scheme I).toCellScheme.grade s ≤ 4 from hg ▸ htC.2)⟩
        obtain ⟨v, hv, hle⟩ := hfa s t htC hst hg
        exact ⟨v, hv, by rw [hwC hsC, hwC ((hmemC hv).mpr htC)]; exact hle⟩
      rcases hgrade ht with h1 | h2 | h3
      · obtain ⟨v, hv, hle⟩ := hga s t (hmem1 h1) hst hg
        have hv1 : (scheme I).toCellScheme.grade v = 1 := by
          have h' : (scheme I).toCellScheme.grade v = (scheme I).toCellScheme.grade t := by
            rw [← CellScheme.gradedIndex_snd, hv, CellScheme.gradedIndex_snd]
          omega
        exact ⟨v, hv, by rw [hw1 (hg.trans h1), hw1 hv1]; exact hle⟩
      · obtain ⟨v, hv, hle⟩ := hea s t (mem_below_univ_four t) hst hg
        have hv2 : (scheme I).toCellScheme.grade v = 2 := by
          have h' : (scheme I).toCellScheme.grade v = (scheme I).toCellScheme.grade t := by
            rw [← CellScheme.gradedIndex_snd, hv, CellScheme.gradedIndex_snd]
          omega
        have hvC : v ∉ C := fun h' ↦ htC ((hmemC hv).mp h')
        exact ⟨v, hv, by
          rw [hw2 hvC hv2]
          exact (hub2 (hg.trans h2)).trans (hΘ₂.monotone hle)⟩
      · obtain ⟨v, hv, hle⟩ := hea s t (mem_below_univ_four t) hst hg
        have hv3 : (scheme I).toCellScheme.grade v = 3 := by
          have h' : (scheme I).toCellScheme.grade v = (scheme I).toCellScheme.grade t := by
            rw [← CellScheme.gradedIndex_snd, hv, CellScheme.gradedIndex_snd]
          omega
        have hvC : v ∉ C := fun h' ↦ htC ((hmemC hv).mp h')
        exact ⟨v, hv, by
          rw [hw3 hvC hv3]
          exact (hub3 (hg.trans h3)).trans (hΘ₃.monotone hle)⟩
  refine ⟨w, hw, fun d hd ↦ hwC hd, fun d hd ↦ ?_, ?_⟩
  · rcases lt_or_ge (e d) h with hed | hed
    · rw [(hinv3 hd.2).1 hed]
    · rw [min_eq_right hed, min_eq_right ((hinv3 hd.2).2 hed)]
  · rw [hw1 hgx]
    refine top_le_iff.mp (le_trans ?_ (le_max_right _ _))
    simp only [blockStep, hρx]
    rw [ite_eq_left]
    exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)

/-- **The fill from a server.**  Under the hypotheses of `TowerProfile.exists_three_of_server`,
with `e` lawful, some labelling lawful below `(univ, 4)` is `f` on the left coatom, agrees with `e`
capped at `h` everywhere, and is `⊤` at `x` (so it reads `x` at least as every cell): the
labelling of the cells of grade at most `3` (`⊤` at `x`) completed at the grade `4` along `e`
(`TowerProfile.exists_isLawfulBelow_four`). -/
theorem exists_fill_of_server {e : Fin (scheme I).card → Label.{u}}
    (hel : (scheme I).rows.IsLawful e)
    {h : Label.{u}} (hh : IsSelfVisible 4 h) (hhb : ⊥ < h)
    {f : Fin (scheme I).card → Label.{u}}
    (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d)
    (hfe : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      min (f d) h = min (e d) h)
    {x : Fin (scheme I).card} (hgx : (scheme I).toCellScheme.grade x = 1) (hex : h ≤ e x)
    {u : Fin (scheme I).card}
    (hu : (scheme I).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), 1)) (heu : h ≤ e u)
    {β : Ordinal.{u}} (hux : (scheme I).rowAt u x = ((ω * β + 1 : Ordinal.{u}) : Label.{u}))
    {A : Label.{u}} (hA : IsSelfVisible 1 A) (hhA : h ≤ A)
    (hfA : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.grade d = 1 → f d ≠ ⊥ →
        f d = A ∧ (scheme I).rowAt u d < ((ω * β : Ordinal.{u}) : Label.{u}))
    {V : Label.{u}} (hV : IsSelfVisible 2 V) (hhV : h ≤ V) (hVA : V ≤ A)
    (hfV : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.grade d ≤ 2 → h ≤ f d → V ≤ f d)
    (hfV' : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.grade d = 2 → h ≤ f d → f d ≤ V)
    (hf3 : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.grade d = 3 → f d ≤ h) :
    ∃ g : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 4) (fun d ↦ g d) ∧
      (∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4), g d = f d) ∧
      (∀ d, min (g d) h = min (e d) h) ∧ g x = ⊤ := by
  obtain ⟨w, hw, hwf, hwe, hwx⟩ := exists_three_of_server (hel.isLawfulBelow _) hh hhb hf hfe
    hgx hex hu heu hux hA hhA hfA hV hhV hVA hfV hfV' hf3
  have hwU : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ w d :=
    (CellScheme.Rows.isLawfulBelow_congr fun d hd ↦ hwf d hd).mpr hf
  obtain ⟨g, hg, hgw, hga⟩ := exists_isLawfulBelow_four (x := Fin.last 4)
    (y := Fin.castSucc (Fin.last 3)) (by simp) (by simp) (by decide) hwU hw hel hh
    fun d hd ↦ hd.elim (fun hd ↦ by rw [hwf d hd]; exact hfe d hd) (hwe d)
  have hx3 : x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
    ⟨subset_univ _, show (scheme I).toCellScheme.grade x ≤ 3 by rw [hgx]; omega⟩
  refine ⟨g, hg, fun d hd ↦ (hgw d (.inl hd)).trans (hwf d hd),
    fun d ↦ hga d (mem_below_univ_four d), ?_⟩
  rw [hgw x (.inr hx3), hwx]

end TowerProfile

/-! ### The left coatom of `seedThree` -/

namespace TopReadingApexExample

open TwoFaceLiftExistsCounterexample CaseSplitCounterexample TowerProfile

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- The rows of `threeType` at its old cells are those of `S`. -/
theorem rowAt_threeType_castSucc (a b : Fin CaseSplitCounterexample.S.{u}.card) :
    (threeType hα).toScheme.rowAt (Fin.castSucc a) (Fin.castSucc b) =
      CaseSplitCounterexample.S.rowAt a b :=
  Scheme.rowAt_of_comap (Scheme.isLowerEmbedding_castSucc 4
    (StageType.apexRow (t := threeBase hα) isLegalBelowFullGrade_S)
    isLegalBelowFullGrade_S.not_le) Scheme.comap_rows_castSucc a b

/-- The labelling `labelling 3 3 ⊥` is `⊥` at the cells of grade `3`. -/
theorem labelling_three_eq_bot_of_grade {a : Fin 19}
    (ha : TwoFaceLiftCounterexample.cellGrade a = 3) :
    CaseSplitCounterexample.labelling lab3 lab3 ⊥ a = (⊥ : Label.{u}) := by
  unfold CaseSplitCounterexample.labelling
  split_ifs <;> simp_all

/-- Where `labelling 3 3 ⊥` is not `⊥` the cell is live. -/
theorem live_of_labelling_three_ne_bot {a : Fin 19}
    (h : CaseSplitCounterexample.labelling lab3 lab3 ⊥ a ≠ (⊥ : Label.{u})) :
    CaseSplitCounterexample.live a = true := by
  by_contra hl
  exact h (by unfold CaseSplitCounterexample.labelling; simp [hl])

/-- The live cell of grade `2` of `S` is the cell `15`. -/
theorem eq_fifteen_of_live : ∀ a : Fin 19, TwoFaceLiftCounterexample.cellGrade a = 2 →
    CaseSplitCounterexample.live a = true → a = 15 := by
  decide

/-- A set inside the left coatom avoids the last point. -/
theorem last_notMem_of_subset {s : Finset (Fin 5)} (hs : s ⊆ univ.erase (Fin.last 4)) :
    Fin.last 4 ∉ s := fun h ↦ Finset.notMem_erase (Fin.last 4) univ (hs h)

/-- Every cell is visible through the identity. -/
theorem mem_visibleCells_refl {k : ℕ} (t' : StageType.{u} α k) (z : Fin t'.card) :
    z ∈ t'.visibleCells (Function.Embedding.refl (Fin k)) :=
  Scheme.mem_visibleCells.mpr fun x _ ↦ ⟨x, rfl⟩

/-- The labelling `labelling 3 3 ⊥` takes the values `3` and `⊥`. -/
theorem labelling_three_cases (a : Fin 19) :
    CaseSplitCounterexample.labelling lab3 lab3 ⊥ a = (lab3 : Label.{u}) ∨
      CaseSplitCounterexample.labelling lab3 lab3 ⊥ a = (⊥ : Label.{u}) := by
  unfold CaseSplitCounterexample.labelling
  split_ifs <;> simp

end TopReadingApexExample

/-! ### The fill from the ties of the marker -/

namespace TowerProfile

open TopReadingApexExample

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **The fill at the short positive caps from the left coatom, from the ties of the marker**, at a
seed whose right coatom type raises at the point `3` (`StageType.RowsRaiseAt`; `rightType` does,
`TowerProfile.rowsRaiseAt_rightType`).  Let `r` be a marker of grade `4` on the left coatom,
`x` a cell of the amalgam of grade `1` through the point `4` (a new top), and `t₁`, `t₂` cells of
the left coatom of grades `1` and `2`.  Suppose that in every labelling `f` lawful below the left
coatom and not `⊥` at `r` the cells of grade `1` not `⊥` take the value at `t₁`, the only cell of
grade `2` not `⊥` is `t₂`, and the cells of grade `3` are `⊥`.  Suppose the marker is the cell of
a cell `c` of the left coatom type labelled `⊤`, of full scope and grade at least the arity of a
root `ι`, with **the root offsets below its grade** (`StageType.RootOffsetsBelow`), and `t₁`, `t₂`
are the cells of cells visible through `ι` carrying one proper label.  Then
`ReadingFillPos I r X (Fin.last 4)` for `X = {x}`: the marker keeps the tie of `t₁` and `t₂`
(`StageType.keepsProperRootTies_of_rootOffsetsBelow`), its row reading `t₂` at most as `t₁`.

Below the cap at the marker it is the fill of the profile layer; outside the band,
`TowerProfile.exists_fillPos_left_of_noBand`.  In the band (a cell of the left coatom with a value
in `[h, f r)`), the tie gives `h ≤ f t₁` and `f t₂ ≤ f t₁`; a server
(`TowerProfile.exists_server_of_rightType`) reads `x` at `ω * β + 1` (a code of the grade `1`) and
every cell of the left coatom below the block `β`; the fill from the server
(`TowerProfile.exists_fill_of_server`, with `A = f t₁` and `V = max h (f t₂)`) is `⊤` at `x`. -/
theorem readingFillPos_left_of_tie (hraise : I.right.RowsRaiseAt 3)
    {r : Fin (scheme I).card} (hgr : (scheme I).toCellScheme.grade r = 4)
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    {xa : Fin I.amalgam.card} (hPx : Fin.last 4 ∈ I.amalgam.toCellScheme.scope xa)
    (hgxa : I.amalgam.toCellScheme.grade xa = 1) {X : Finset (Fin (scheme I).card)}
    (hxX : embed3 I xa ∈ X) (hX : ∀ x ∈ X, x = embed3 I xa)
    {t₁ t₂ : Fin (scheme I).card}
    (ht₁ : t₁ ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hg₁ : (scheme I).toCellScheme.grade t₁ = 1)
    (ht₂ : t₂ ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hg₂ : (scheme I).toCellScheme.grade t₂ = 2)
    (H1 : ∀ f : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) (fun d ↦ f d) → f r ≠ ⊥ →
      ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        (scheme I).toCellScheme.grade d = 1 → f d ≠ ⊥ → f d = f t₁)
    (H2 : ∀ f : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) (fun d ↦ f d) → f r ≠ ⊥ →
      ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        (scheme I).toCellScheme.grade d = 2 → f d ≠ ⊥ → d = t₂)
    (H3 : ∀ f : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) (fun d ↦ f d) → f r ≠ ⊥ →
      ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        (scheme I).toCellScheme.grade d = 3 → f d = ⊥)
    {n : ℕ} {ι : Fin n ↪ Fin 4} {c z₁ z₂ : Fin I.left.card} (hrc : leftCell I c = r)
    (hz₁ : leftCell I z₁ = t₁) (hz₂ : leftCell I z₂ = t₂) (hc : I.left.label c = ⊤)
    (hcs : I.left.toCellScheme.scope c = univ) (hn : n ≤ I.left.toCellScheme.grade c)
    (hoff : I.left.RootOffsetsBelow ι (I.left.toCellScheme.grade c))
    (hv₁ : z₁ ∈ I.left.visibleCells ι) (hv₂ : z₂ ∈ I.left.visibleCells ι)
    (hlab : I.left.label z₂ = I.left.label z₁) (hprop : IsProper (I.left.label z₂)) :
    ReadingFillPos I r X (Fin.last 4) := by
  classical
  -- the marker keeps the tie of `t₁` and `t₂` (root offsets below its grade)
  have hrow : (scheme I).rowAt r t₂ ≤ (scheme I).rowAt r t₁ := by
    rw [← hrc, ← hz₁, ← hz₂, rowAt_leftCell, rowAt_leftCell]
    exact StageType.keepsProperRootTies_of_rootOffsetsBelow hc hcs hn hoff z₂ hv₂ z₁ hv₁
      hlab.le (.inr hprop)
  have hbelow {z : Fin I.left.card} (hz : z ∈ I.left.visibleCells ι) :
      leftCell I z ∈ (scheme I).toCellScheme.below
        ((scheme I).toCellScheme.gradedIndex (leftCell I c)) := by
    have h := StageType.mem_below_of_mem_visibleCells hcs hn hz
    rw [CellScheme.mem_below, CellScheme.gradedIndex_le_iff] at h
    rw [CellScheme.mem_below, gradedIndex_leftCell, gradedIndex_leftCell]
    exact Prod.mk_le_mk.mpr ⟨map_subset_map.mpr h.1, h.2⟩
  have hr₁ : t₁ ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r) :=
    hz₁ ▸ hrc ▸ hbelow hv₁
  have hr₂ : t₂ ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r) :=
    hz₂ ▸ hrc ▸ hbelow hv₂
  intro e he h hh _ hhb f hf hfe
  have hel : (scheme I).rows.IsLawful e :=
    (Scheme.mem_catalogue.mp (Scheme.readingMarks_subset _ _ he)).1
  have hgx : (scheme I).toCellScheme.grade (embed3 I xa) = 1 := by
    rw [← CellScheme.gradedIndex_snd, gradedIndex_embed3, CellScheme.gradedIndex_snd, hgxa]
  have hX3 : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 3 := fun x hx ↦ by
    rw [hX x hx, hgx]; omega
  by_cases hre : h ≤ e r
  swap
  · obtain ⟨g, hg, hgf, hga⟩ := exists_fill_four (x := Fin.last 4)
      (y := Fin.castSucc (Fin.last 3)) (by simp) (by simp) (by decide) hf hel hh hfe
    exact ⟨g, hg, hgf, hga, reads_of_lt he (not_le.mp hre) hga⟩
  have hfr : h ≤ f r := Label.le_of_min_eq_of_le' (hfe _ hrC) hre
  by_cases hband : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 3),
      h ≤ f d → f r ≤ f d
  · exact exists_fillPos_left_of_noBand hgr hrC hX3 he hh hhb hf hfe hre hband
  push Not at hband
  obtain ⟨d₀, hd₀, hhd₀, hd₀r⟩ := hband
  have hfr0 : f r ≠ ⊥ := (hhb.trans_le hfr).ne'
  have hpos (d : Fin (scheme I).card) : 1 ≤ (scheme I).toCellScheme.grade d :=
    isWellFormed_scheme.isWellFormed.grade_pos d
  -- the band: `h ≤ A` and `F ≤ A`
  have hd₀C : d₀ ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) :=
    (CellScheme.mem_below _).mpr (le_trans ((CellScheme.mem_below _).mp hd₀)
      (Prod.mk_le_mk.mpr ⟨subset_rfl, by omega⟩))
  have htie : min (f t₂) (f r) ≤ min (f t₁) (f r) :=
    ((CellScheme.Rows.isLawfulBelow_iff_forall.mp hf).2.1 r hrC).le_of_le
      (d := ⟨t₂, hr₂⟩) (d' := ⟨t₁, hr₁⟩)
      (by rw [← Scheme.rowAt_of_mem, ← Scheme.rowAt_of_mem]; exact hrow) (by rw [hg₁, hg₂]; omega)
  have hd₀3 : (scheme I).toCellScheme.grade d₀ ≤ 3 :=
    ((scheme I).toCellScheme.gradedIndex_le_iff.mp ((CellScheme.mem_below _).mp hd₀)).2
  have hd₀0 : f d₀ ≠ ⊥ := (hhb.trans_le hhd₀).ne'
  obtain ⟨hhA, hFA⟩ : h ≤ f t₁ ∧ f t₂ ≤ f t₁ := by
    rcases (show (scheme I).toCellScheme.grade d₀ = 1 ∨ (scheme I).toCellScheme.grade d₀ = 2 ∨
        (scheme I).toCellScheme.grade d₀ = 3 by have := hpos d₀; omega) with h1 | h2 | h3
    · rw [H1 f hf hfr0 d₀ hd₀C h1 hd₀0] at hhd₀ hd₀r
      rw [min_eq_left hd₀r.le] at htie
      refine ⟨hhd₀, ?_⟩
      rcases lt_or_ge (f t₂) (f r) with hlt | hge
      · rwa [min_eq_left hlt.le] at htie
      · rw [min_eq_right hge] at htie
        exact absurd htie (not_le.mpr hd₀r)
    · rw [H2 f hf hfr0 d₀ hd₀C h2 hd₀0] at hhd₀ hd₀r
      rw [min_eq_left hd₀r.le] at htie
      have hF := htie.trans (min_le_left _ _)
      exact ⟨hhd₀.trans hF, hF⟩
    · exact absurd (H3 f hf hfr0 d₀ hd₀C h3) hd₀0
  -- the server
  have hex : h ≤ e (embed3 I xa) := hre.trans (Scheme.le_of_mem_readingMarks he hxX)
  obtain ⟨u, hu, hxu, hlt, hcode⟩ := exists_server_of_rightType I.restrictFace_right hraise
    (hel.isLawfulBelow _) hPx hgxa
    (hhb.trans_le hex).ne'
  have hvis {d : Fin (scheme I).card} (hd : (scheme I).toCellScheme.grade d = 1) :
      IsSelfVisible 1 ((scheme I).rowAt u d) := by
    have := (CellScheme.Rows.isLawfulBelow_iff_forall.mp (isLawfulBelow_rowAt hu)).1 d
      ⟨subset_univ _, hd.le⟩
    rwa [hd] at this
  have hleft {d : Fin (scheme I).card}
      (hd : d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
      (hg : (scheme I).toCellScheme.grade d = 1) :
      (scheme I).rowAt u d < (scheme I).rowAt u (embed3 I xa) := by
    have hsd := ((scheme I).toCellScheme.gradedIndex_le_iff.mp ((CellScheme.mem_below _).mp hd)).1
    obtain ⟨dam, rfl⟩ := mem_range_embed3 d fun h' ↦ last_notMem_of_subset hsd (h' ▸ mem_univ _)
    refine hlt dam (by rw [← scope_embed3]; exact last_notMem_of_subset hsd) ?_
    rw [← CellScheme.gradedIndex_snd, ← gradedIndex_embed3, CellScheme.gradedIndex_snd, hg]
  have hnex : (scheme I).rowAt u (embed3 I xa) ≠ ⊥ := (bot_le.trans_lt (hleft ht₁ hg₁)).ne'
  obtain ⟨β, hβ⟩ := exists_eq_omega0_mul_add_one hcode (hvis hgx) hnex
  -- the fill from the server
  obtain ⟨hfo, -, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hf
  obtain ⟨g, hg, hgf, hga, hgxtop⟩ := exists_fill_of_server hel hh hhb hf hfe hgx hex hu
    (hex.trans hxu) hβ (V := max h (f t₂)) (by have := hfo t₁ ht₁; rwa [hg₁] at this) hhA
    (fun d hd hg h0 ↦ ⟨H1 f hf hfr0 d hd hg h0,
      lt_omega0_mul_of_lt_add_one (hvis hg) (hβ ▸ hleft hd hg)⟩)
    ((hh.mono (by omega)).max (by have := hfo t₂ ht₂; rwa [hg₂] at this))
    (le_max_left _ _) (max_le hhA hFA)
    (fun d hd hg hfd ↦ by
      have h0 : f d ≠ ⊥ := (hhb.trans_le hfd).ne'
      rcases (show (scheme I).toCellScheme.grade d = 1 ∨ (scheme I).toCellScheme.grade d = 2 by
          have := hpos d; omega) with h1 | h2
      · rw [H1 f hf hfr0 d hd h1 h0]
        exact max_le hhA hFA
      · rw [H2 f hf hfr0 d hd h2 h0] at hfd ⊢
        exact max_le hfd le_rfl)
    (fun d hd hg hfd ↦ by
      rw [H2 f hf hfr0 d hd hg (hhb.trans_le hfd).ne']
      exact le_max_right _ _)
    (fun d hd hg ↦ by rw [H3 f hf hfr0 d hd hg]; exact bot_le)
  refine ⟨g, hg, hgf, hga, fun x hx ↦ ?_⟩
  rw [hX x hx, hgxtop]
  exact le_top

end TowerProfile

end VaughtConjecture
