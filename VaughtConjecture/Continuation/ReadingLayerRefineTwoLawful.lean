/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerRefineTwoProof

/-!
# Lawful labellings and separating servers at the grade `2`

Roadmap, Layer 3 ((R3) of the table of 3.4).

A server (a cell of graded index `(univ, 2)`) at least `h` in a lawful `e` reads the cells of
the layer at the grade `1` through a witness at `2` capped at `h`
(`TowerProfile.exists_witness_server`).
Hence:

* `TowerProfile.entry_lt_of_server`: its entry codes every cell less than `h` in `e` strictly
  below every cell at least `h` in `e`.
* `TowerProfile.false_of_server_sameBlock`: no cell at least `h` in `e` is coded in the block
  `[ω * β, ω * (β + 1))` of a cell less than `h` in `e` (`Label.false_of_sameBlock`: replacing the
  finite part, below `2`, of the upper code by that of the lower one, or that of the lower code by
  `2`, commutes with the witness).  The configuration of a cell of graded index `(univ, 1)` at
  least `h` coded `ω * β + 1` in the block of a cell of grade `2` less than `h` coded `ω * β + 2`
  contradicts lawfulness.
* `TowerProfile.frozenServerTwo_bot`: a frozen server (`TowerProfile.FrozenServerTwo`) reads a
  cell at least `h` below `2` and codes every cell less than `h` by `⊥`.
* `TowerProfile.separatingServerTwo_of_least`: a server whose least code of a cell at least `h` is
  self-visible at `2` separates; `TowerProfile.LeastCodesTwo I` implies
  `TowerProfile.SeparatingServersTwo I` and `TowerProfile.RefiningServerTwo I`.
* `TowerProfile.exists_frozen_of_entry`, `TowerProfile.not_separatingServersTwo_of_lowEntry`: an
  entry coding a cell below `2` and not by `⊥` (`TowerProfile.LowEntryTwo`) gives a lawful
  labelling (the support of its field row) at which every server at least `4` is frozen, so
  `TowerProfile.SeparatingServersTwo I` fails.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label
open scoped Ordinal

namespace Label

/-- Two ordinals of one block `[ω * β, ω * (β + 1))` have quotient `β` by `ω`. -/
theorem div_omega0_eq_of_block {β o : Ordinal.{u}} (h₁ : ω * β ≤ o) (h₂ : o < ω * (β + 1)) :
    o / ω = β := by
  refine le_antisymm ?_ ((Ordinal.mul_le_iff_le_div Ordinal.omega0_ne_zero).mp h₁)
  exact Order.lt_add_one_iff.mp ((Ordinal.lt_mul_iff_div_lt Ordinal.omega0_ne_zero).mp h₂)

/-- **No two codes of one block straddle a cap**: a witness at `2` reading a code `x₁`, short
at `2`, at the cap `h` (self-visible at `3`) and a code `x₂` of the same block at a label `y < h`
self-visible at `1` is impossible. -/
theorem false_of_sameBlock {τ : Label.{u} → Label.{u}} (hτ : IsWitness (stepSuppressor 2) τ)
    {h y x₁ x₂ : Label.{u}} (hh : IsSelfVisible 3 h) (hy : IsSelfVisible 1 y) (hyh : y < h)
    (h₁ : τ x₁ = h) (h₂ : τ x₂ = y) (hx₁ : IsShort 2 x₁) {β : Ordinal.{u}}
    (hβ : (((ω * β : Ordinal.{u})) : Label.{u}) ≤ x₂)
    (hβ₁ : x₁ < (((ω * (β + 1) : Ordinal.{u})) : Label.{u})) : False := by
  have hlt : x₂ < x₁ := not_le.mp fun hle ↦ (hyh.trans_le (h₁ ▸ h₂ ▸ hτ.monotone hle)).false
  induction x₂ using recBotCoeTop with
  | bot => exact absurd hβ (not_le.mpr (WithBot.bot_lt_coe _))
  | top => exact absurd hlt (not_lt.mpr le_top)
  | coe o₂ =>
  induction x₁ using recBotCoeTop with
  | bot => exact absurd hlt (not_lt.mpr bot_le)
  | top => exact absurd hβ₁ (not_lt.mpr le_top)
  | coe o₁ =>
  rw [WithBot.coe_le_coe, WithTop.coe_le_coe] at hβ
  rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe] at hβ₁ hlt
  have hd₁ : o₁ / ω = β := div_omega0_eq_of_block (hβ.trans hlt.le) hβ₁
  have hd₂ : o₂ / ω = β := div_omega0_eq_of_block hβ (hlt.trans hβ₁)
  have hm₁ : o₁ % ω ≤ 2 := hx₁ o₁ rfl
  have he₁ : o₁ = ω * β + o₁ % ω := by rw [← hd₁, Ordinal.div_add_mod]
  have he₂ : o₂ = ω * β + o₂ % ω := by rw [← hd₂, Ordinal.div_add_mod]
  have hm : o₂ % ω < o₁ % ω := by
    rw [he₁, he₂] at hlt
    exact (add_lt_add_iff_left _).mp hlt
  rcases hm₁.lt_or_eq with hm₁ | hm₁
  · -- the finite part of `x₁` is below `2`: replacing it by `0` reaches `x₂`
    have hm₂ : o₂ % ω = 0 := by
      have : o₁ % ω ≤ 1 := Order.lt_succ_iff.mp (by simpa [one_add_one_eq_two] using hm₁)
      exact Order.lt_one_iff.mp (hm.trans_le this)
    have hrep : visibilityReplace 2 0 ((o₁ : Ordinal.{u}) : Label.{u}) = (o₂ : Label.{u}) := by
      rw [visibilityReplace_coe, Ordinal.visibilityReplace_of_lt (by exact_mod_cast hm₁),
        hd₁, he₂, hm₂]
      simp
    have := hτ.visibilityReplace_comm (o₁ : Label.{u}) 2
      (by rw [stepSuppressor_of_le le_rfl]; exact le_top) 0
      (by omega)
    rw [hrep, h₁, (hh.mono (by omega)).visibilityReplace_eq, h₂] at this
    exact hyh.ne this
  · -- the finite part of `x₁` is `2`: replacing that of `x₂` by `2` reaches `x₁`
    have hrep : visibilityReplace 2 2 ((o₂ : Ordinal.{u}) : Label.{u}) = (o₁ : Label.{u}) := by
      rw [visibilityReplace_coe, Ordinal.visibilityReplace_of_lt (by exact_mod_cast hm₁ ▸ hm),
        hd₂, he₁, hm₁]
      simp
    have := hτ.visibilityReplace_comm (o₂ : Label.{u}) 2
      (by rw [stepSuppressor_of_le le_rfl]; exact le_top) 2
      le_rfl
    rw [hrep, h₁, h₂] at this
    -- `visibilityReplace 2 2 y < h`
    have hle := visibilityReplace_two_two_le_of_lt hy hyh
    by_cases hy2 : IsSelfVisible 2 y
    · rw [hy2.visibilityReplace_eq] at this
      exact hyh.ne this.symm
    have hb : y ≠ ⊥ := fun h' ↦ hy2 (h' ▸ isSelfVisible_bot 2)
    have ht : y ≠ ⊤ := fun h' ↦ hy2 (h' ▸ isSelfVisible_top 2)
    obtain ⟨q, n, rfl⟩ := exists_block hb ht
    have hn : n < 2 := by
      by_contra hn
      exact hy2 (isSelfVisible_block.mpr (by omega))
    rw [this, visibilityReplace_block, ite_eq_left hn, isSelfVisible_block] at hh
    omega

end Label

namespace TowerProfile

open TopReadingApexExample StageType

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- The layer at the grade `1` inside the layer at the grade `2`, below `(univ, 2)`. -/
theorem castAdd_mem_below_two (d : Fin (I.tower 1).card)
    (hd : (I.tower 1).toCellScheme.grade d ≤ 2) :
    (Fin.castAdd _ d : Fin (I.tower 2).card) ∈
      (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2) := by
  have g1 : (I.tower 2).toCellScheme.gradedIndex (Fin.castAdd _ d) =
      (I.tower 1).toCellScheme.gradedIndex d :=
    Scheme.appendFullCellsScheme_gradedIndex_castAdd (I.tower 1) 2 _ d
  exact (CellScheme.mem_below _).mpr (g1.trans_le
    (((I.tower 1).toCellScheme.gradedIndex_le_iff).mpr ⟨subset_univ _, hd⟩))

/-- **The witness of a server at the grade `2`**: a cell `i` of graded index `(univ, 2)` at
least `h` in a lawful `e` reads, through a witness at `2` capped at `h`, the cells of the layer at
the grade `1` by its entry and the other cells of graded index `(univ, 2)` by agreement heights. -/
theorem exists_witness_server {e : Fin (scheme I).card → Label.{u}}
    (he : (scheme I).rows.IsLawfulBelow (univ, 2) fun d ↦ e d)
    {h : Label.{u}} (hh : IsSelfVisible 2 h) {i : Fin ((I.tower 1).catalogue 2).card}
    (heu : h ≤ e (twoCell I (Fin.natAdd _ i))) :
    ∃ τ, IsWitness (stepSuppressor 2) τ ∧
      (∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 →
        τ ((I.tower 1).catalogueEntry 2 i d) = min (e (oneCell I d)) h) ∧
      ∀ j, τ (agreementHeight ((I.tower 1).fieldGrid 2) ((I.tower 1).catalogueEntry 2 i)
        ((I.tower 1).catalogueEntry 2 j)) = min (e (twoCell I (Fin.natAdd _ j))) h := by
  have he₂ := isLawfulBelow_two_of_scheme he
  have hu' : (I.tower 2).toCellScheme.gradedIndex (Fin.natAdd _ i) =
      ((univ : Finset (Fin 5)), 2) :=
    Scheme.appendFullCellsScheme_gradedIndex_natAdd (I.tower 1) 2 _ i
  obtain ⟨τ₀, hτ₀, -, hτ₀E⟩ := CellScheme.Rows.exists_isWitness_rowBelow
    (R := (I.tower 2).rows) hu' he₂ (c := h) hh heu
  have hfr (x : Fin (I.tower 2).card)
      (hx : x ∈ (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2)) :
      τ₀ ((I.tower 1).fieldRow 2 ((I.tower 1).catalogueEntry 2 i) x) =
        min (e (twoCell I x)) h := by
    have := hτ₀E ⟨x, hx⟩
    have h2 := Scheme.fieldLayer_row_natAdd (S := I.tower 1) (k := 2)
      (hS := I.not_univ_succ_le_tower 1) i ⟨x, le_trans hx hu'.ge⟩
    exact (congrArg τ₀ h2).symm.trans this
  refine ⟨τ₀, hτ₀, fun d hd ↦ ?_, fun j ↦ ?_⟩
  · exact (congrArg τ₀ (Scheme.fieldRow_castAdd (S := I.tower 1) (k := 2) _ d)).symm.trans
      (hfr _ (castAdd_mem_below_two d hd))
  · exact (congrArg τ₀ (Scheme.fieldRow_natAdd (S := I.tower 1) (k := 2) _ j)).symm.trans
      (hfr _ (Scheme.natAdd_mem_below (hS := I.not_univ_succ_le_tower 1) j))

/-- A lawful `e` reads a cell of the layer at the grade `1` of grade at most `2` at a label
self-visible at `1`. -/
theorem isSelfVisible_one_oneCell {e : Fin (scheme I).card → Label.{u}}
    (he : (scheme I).rows.IsLawfulBelow (univ, 2) fun d ↦ e d) (d : Fin (I.tower 1).card)
    (hd : (I.tower 1).toCellScheme.grade d ≤ 2) : IsSelfVisible 1 (e (oneCell I d)) := by
  have he₂ := isLawfulBelow_two_of_scheme he
  have h1 := (CellScheme.Rows.isLawfulBelow_iff.mp he₂).orderly ⟨_, castAdd_mem_below_two d hd⟩
  have hg : (I.tower 2).toCellScheme.grade (Fin.castAdd _ d) = (I.tower 1).toCellScheme.grade d :=
    Scheme.appendFullCellsScheme_grade_castAdd (I.tower 1) 2 _ d
  change IsSelfVisible ((I.tower 2).toCellScheme.grade (Fin.castAdd _ d)) _ at h1
  rw [hg] at h1
  have h2 := isWellFormed_scheme.isWellFormed.grade_pos (oneCell I d)
  rw [← CellScheme.gradedIndex_snd, gradedIndex_oneCell, CellScheme.gradedIndex_snd] at h2
  exact h1.mono h2

/-- **The entry of a server orders the cells by `e` capped at `h`**: a cell of the layer at the
grade `1` less than `h` in `e` is coded strictly below a cell at least `h` in `e`. -/
theorem entry_lt_of_server {e : Fin (scheme I).card → Label.{u}}
    (he : (scheme I).rows.IsLawfulBelow (univ, 2) fun d ↦ e d)
    {h : Label.{u}} (hh : IsSelfVisible 2 h) {i : Fin ((I.tower 1).catalogue 2).card}
    (heu : h ≤ e (twoCell I (Fin.natAdd _ i))) {d₁ d₂ : Fin (I.tower 1).card}
    (hd₁ : (I.tower 1).toCellScheme.grade d₁ ≤ 2) (he₁ : h ≤ e (oneCell I d₁))
    (hd₂ : (I.tower 1).toCellScheme.grade d₂ ≤ 2) (he₂ : ¬ h ≤ e (oneCell I d₂)) :
    (I.tower 1).catalogueEntry 2 i d₂ < (I.tower 1).catalogueEntry 2 i d₁ := by
  obtain ⟨τ, hτ, hτd, -⟩ := exists_witness_server he hh heu
  refine not_le.mp fun hle ↦ he₂ ?_
  have := hτ.monotone hle
  rw [hτd d₁ hd₁, hτd d₂ hd₂, min_eq_right he₁] at this
  exact (le_min_iff.mp this).1

/-- **The block configuration contradicts lawfulness**: a server at least `h` in a lawful `e`
never codes a cell at least `h` in `e` in the block `[ω * β, ω * (β + 1))` of a cell less than
`h` in `e`. -/
theorem false_of_server_sameBlock {e : Fin (scheme I).card → Label.{u}}
    (he : (scheme I).rows.IsLawfulBelow (univ, 2) fun d ↦ e d)
    {h : Label.{u}} (hh : IsSelfVisible 3 h) {i : Fin ((I.tower 1).catalogue 2).card}
    (heu : h ≤ e (twoCell I (Fin.natAdd _ i))) {d₁ d₂ : Fin (I.tower 1).card}
    (hd₁ : (I.tower 1).toCellScheme.grade d₁ ≤ 2) (he₁ : h ≤ e (oneCell I d₁))
    (hd₂ : (I.tower 1).toCellScheme.grade d₂ ≤ 2) (he₂ : ¬ h ≤ e (oneCell I d₂))
    {β : Ordinal.{u}}
    (hβ : (((ω * β : Ordinal.{u})) : Label.{u}) ≤ (I.tower 1).catalogueEntry 2 i d₂)
    (hβ₁ : (I.tower 1).catalogueEntry 2 i d₁ < (((ω * (β + 1) : Ordinal.{u})) : Label.{u})) :
    False := by
  have hh2 : IsSelfVisible 2 h := hh.mono (by decide)
  obtain ⟨τ, hτ, hτd, -⟩ := exists_witness_server he hh2 heu
  have hlt := not_le.mp he₂
  have hy : IsSelfVisible 1 (min (e (oneCell I d₂)) h) :=
    (isSelfVisible_one_oneCell he d₂ hd₂).min (hh.mono (by decide))
  have hyh : min (e (oneCell I d₂)) h < h := by
    rw [min_eq_left hlt.le]
    exact hlt
  exact Label.false_of_sameBlock hτ hh hy hyh ((hτd d₁ hd₁).trans (min_eq_right he₁))
    (hτd d₂ hd₂) (isShort_of_mem_codeGrid (Scheme.mem_codeGrid_of_mem_catalogue
      (Scheme.catalogueEntry_mem i) d₁)) hβ hβ₁

/-- **A frozen server codes the cells less than `h` by `⊥`**: at a lawful `e`, a frozen server
(`TowerProfile.FrozenServerTwo`) at least `h` in `e` reads a cell at least `h` in `e` below `2`,
and then every cell of the layer at the grade `1` of grade at most `2` less than `h` in `e` is
coded `⊥` and labelled `⊥` (the configuration of a block shared with a cell less than `h` is
impossible, `TowerProfile.false_of_server_sameBlock`). -/
theorem frozenServerTwo_bot {e : Fin (scheme I).card → Label.{u}}
    (he : (scheme I).rows.IsLawfulBelow (univ, 2) fun d ↦ e d)
    {h : Label.{u}} (hh : IsSelfVisible 4 h) (hhb : ⊥ < h)
    {i : Fin ((I.tower 1).catalogue 2).card} (heu : h ≤ e (twoCell I (Fin.natAdd _ i)))
    (hfr : FrozenServerTwo I e h i) :
    (∃ d₁, (I.tower 1).toCellScheme.grade d₁ ≤ 2 ∧ h ≤ e (oneCell I d₁) ∧
      (I.tower 1).catalogueEntry 2 i d₁ < (((2 : Ordinal.{u})) : Label.{u})) ∧
    ∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 → ¬ h ≤ e (oneCell I d) →
      (I.tower 1).catalogueEntry 2 i d = ⊥ ∧ e (oneCell I d) = ⊥ := by
  have hh3 : IsSelfVisible 3 h := hh.mono (by decide)
  obtain ⟨d₁, hd₁, he₁, hcase⟩ := hfr
  have hlow : (I.tower 1).catalogueEntry 2 i d₁ < (((2 : Ordinal.{u})) : Label.{u}) := by
    rcases hcase with hlow | ⟨d₂, β, hd₂, he₂, hβ, hβ₁⟩
    · exact hlow
    · exact (false_of_server_sameBlock he hh3 heu hd₁ he₁ hd₂ he₂ hβ hβ₁).elim
  refine ⟨⟨d₁, hd₁, he₁, hlow⟩, fun d hd hed ↦ ?_⟩
  have hbot : (I.tower 1).catalogueEntry 2 i d = ⊥ := by
    by_contra hne
    have h0 : (((ω * 0 : Ordinal.{u})) : Label.{u}) ≤ (I.tower 1).catalogueEntry 2 i d := by
      induction hx : (I.tower 1).catalogueEntry 2 i d using recBotCoeTop with
      | bot => exact absurd hx hne
      | top => exact le_top
      | coe o => exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by simp))
    have h2ω : (((2 : Ordinal.{u})) : Label.{u}) ≤ (((ω * (0 + 1) : Ordinal.{u})) : Label.{u}) :=
      WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by
        simpa using (Ordinal.natCast_lt_omega0 2).le))
    exact false_of_server_sameBlock he hh3 heu hd₁ he₁ hd hed h0 (hlow.trans_le h2ω)
  obtain ⟨τ, hτ, hτd, -⟩ := exists_witness_server he (hh.mono (by decide)) heu
  have := hτd d hd
  rw [hbot, hτ.map_bot] at this
  exact ⟨hbot, ((min_eq_bot.mp this.symm).resolve_right hhb.ne')⟩

/-- **A separating server from a least code self-visible at `2`**: if a server at least `h` in
a lawful `e` codes the cells at least `h` in `e` at least at the code of one of them that is
self-visible at `2` (finite part `2`), its block separates. -/
theorem separatingServerTwo_of_least {e : Fin (scheme I).card → Label.{u}}
    (he : (scheme I).rows.IsLawfulBelow (univ, 2) fun d ↦ e d)
    {h : Label.{u}} (hh : IsSelfVisible 4 h) (hhb : ⊥ < h)
    {i : Fin ((I.tower 1).catalogue 2).card} (heu : h ≤ e (twoCell I (Fin.natAdd _ i)))
    {d₀ : Fin (I.tower 1).card} (hd₀ : (I.tower 1).toCellScheme.grade d₀ ≤ 2)
    (he₀ : h ≤ e (oneCell I d₀)) (hv : IsSelfVisible 2 ((I.tower 1).catalogueEntry 2 i d₀))
    (hleast : ∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 → h ≤ e (oneCell I d) →
      (I.tower 1).catalogueEntry 2 i d₀ ≤ (I.tower 1).catalogueEntry 2 i d) :
    SeparatingServerTwo I e h := by
  have hh3 : IsSelfVisible 3 h := hh.mono (by decide)
  obtain ⟨τ, hτ, hτd, hτj⟩ := exists_witness_server he (hh.mono (by decide)) heu
  set a₀ := (I.tower 1).catalogueEntry 2 i with ha₀def
  have hτ0 : τ (a₀ d₀) = h := (hτd d₀ hd₀).trans (min_eq_right he₀)
  have hb : a₀ d₀ ≠ ⊥ := fun h0 ↦ hhb.ne' (by rw [← hτ0, h0, hτ.map_bot])
  have hmem := Scheme.mem_codeGrid_of_mem_catalogue (Scheme.catalogueEntry_mem i) d₀
  obtain ⟨γ, n, hγ⟩ := exists_block hb (ne_top_of_mem_codeGrid hmem)
  have hn2 : 2 ≤ n := isSelfVisible_block.mp (hγ ▸ hv)
  have hn2' : n ≤ 2 := by
    have := isShort_of_mem_codeGrid hmem (ω * γ + n) hγ.symm
    rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (Ordinal.natCast_lt_omega0 n)] at this
    exact_mod_cast this
  obtain rfl : n = 2 := le_antisymm hn2' hn2
  have hc : a₀ d₀ = (((ω * γ + 2 : Ordinal.{u})) : Label.{u}) := by
    rw [hγ]
    rfl
  have hτc : τ (((ω * γ + 2 : Ordinal.{u})) : Label.{u}) = h := hc ▸ hτ0
  have hcγ : a₀ d₀ < (((ω * (γ + 1) : Ordinal.{u})) : Label.{u}) := by
    rw [hc, WithBot.coe_lt_coe, WithTop.coe_lt_coe, mul_add_one]
    exact add_lt_add_right (Ordinal.natCast_lt_omega0 2) _
  have hup (d : Fin (I.tower 1).card) (hd : (I.tower 1).toCellScheme.grade d ≤ 2)
      (hcd : (((ω * γ + 2 : Ordinal.{u})) : Label.{u}) ≤ a₀ d) : h ≤ e (oneCell I d) := by
    have := hτ.monotone hcd
    rw [hτc, hτd d hd] at this
    exact (le_min_iff.mp this).1
  refine ⟨i, γ, heu, fun d hd ↦ ⟨⟨hup d hd, fun hed ↦ hc ▸ hleast d hd hed⟩, fun hdc ↦ ?_⟩,
    fun j hj ↦ ?_⟩
  · have hed : ¬ h ≤ e (oneCell I d) := fun hed ↦ hdc.not_ge (hc ▸ hleast d hd hed)
    exact not_le.mp fun hθ ↦ false_of_server_sameBlock he hh3 heu hd₀ he₀ hd hed hθ hcγ
  · have := hτ.monotone hj
    rw [hτc, hτj j] at this
    exact (le_min_iff.mp this).1

/-- **Least codes self-visible at `2`** at a seed on five points: for every labelling `e` of the
profile layer lawful below `(univ, 2)` and every cap `h` self-visible at `4` with a cell of grade
`2` of the layer at the grade `1` at least `h` in `e`, some server at least `h` in `e` codes the
cells at least `h` in `e` at least at the code, self-visible at `2`, of one of them. -/
def LeastCodesTwo (I : Seed.{u} α 3) : Prop :=
  ∀ e : Fin (scheme I).card → Label.{u}, (scheme I).rows.IsLawfulBelow (univ, 2) (fun d ↦ e d) →
    ∀ h : Label.{u}, IsSelfVisible 4 h → ⊥ < h →
      (∃ z₀, (I.tower 1).toCellScheme.grade z₀ = 2 ∧ h ≤ e (oneCell I z₀)) →
      ∃ i : Fin ((I.tower 1).catalogue 2).card, h ≤ e (twoCell I (Fin.natAdd _ i)) ∧
        ∃ d₀, (I.tower 1).toCellScheme.grade d₀ ≤ 2 ∧ h ≤ e (oneCell I d₀) ∧
          IsSelfVisible 2 ((I.tower 1).catalogueEntry 2 i d₀) ∧
          ∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 → h ≤ e (oneCell I d) →
            (I.tower 1).catalogueEntry 2 i d₀ ≤ (I.tower 1).catalogueEntry 2 i d

/-- Least codes self-visible at `2` give separating servers. -/
theorem separatingServersTwo_of_leastCodes (hI : LeastCodesTwo I) : SeparatingServersTwo I :=
  fun e he h hh hhb hz₀ ↦ by
    obtain ⟨i, heu, d₀, hd₀, he₀, hv, hleast⟩ := hI e he h hh hhb hz₀
    exact separatingServerTwo_of_least he hh hhb heu hd₀ he₀ hv hleast

/-- **A refining server exists at the grade `2` under least codes self-visible at `2`.** -/
theorem refiningServerTwo_of_leastCodes (hI : LeastCodesTwo I) : RefiningServerTwo I :=
  refiningServerTwo_of_separating (separatingServersTwo_of_leastCodes hI)

/-! ### A lawful labelling at which every server at least `4` is frozen -/

/-- The support map: `⊥` at `⊥` and the formal top elsewhere. -/
noncomputable def supportMap (t : Label.{u}) : Label.{u} := if t = ⊥ then ⊥ else ⊤

theorem supportMap_eq_bot_iff {t : Label.{u}} : supportMap t = ⊥ ↔ t = ⊥ := by
  unfold supportMap
  split_ifs with ht <;> simp [ht]

theorem supportMap_of_ne_bot {t : Label.{u}} (ht : t ≠ ⊥) : supportMap t = ⊤ := ite_eq_right ht

/-- The support map is a witness at `2`. -/
theorem isWitness_supportMap : IsWitness (stepSuppressor 2) (supportMap.{u}) where
  antitone := (IsWitness.id_step 2).antitone
  isSelfVisible := (IsWitness.id_step 2).isSelfVisible
  map_bot := ite_eq_left rfl
  monotone := fun x y hxy ↦ by
    by_cases hx : x = ⊥
    · rw [hx, show supportMap (⊥ : Label.{u}) = ⊥ from ite_eq_left rfl]
      exact bot_le
    · have hy : y ≠ ⊥ := fun hy ↦ hx (le_bot_iff.mp (hy ▸ hxy))
      rw [supportMap_of_ne_bot hx, supportMap_of_ne_bot hy]
  visibilityReplace_comm := fun x k _ i _ ↦ by
    by_cases hx : x = ⊥
    · rw [hx, visibilityReplace_bot, show supportMap (⊥ : Label.{u}) = ⊥ from ite_eq_left rfl,
        visibilityReplace_bot]
    · rw [supportMap_of_ne_bot hx, visibilityReplace_top, supportMap_of_ne_bot]
      exact fun h ↦ hx (visibilityReplace_eq_bot_iff.mp h)

/-- Agreement capped at a label carries to every smaller cap. -/
theorem min_eq_min_of_le' {a b x y : Label.{u}} (h : min a x = min b x) (hy : y ≤ x) :
    min a y = min b y := by
  rw [← min_eq_right hy, ← min_assoc, h, min_assoc]

/-- **A labelling at which every server at least `4` is frozen**, from an entry `i` coding a cell
`d₁` of grade at most `2` below `2` and not by `⊥`: the support of the field row of the entry
(`⊤` where it is not `⊥`), lawful below `(univ, 2)`.  The servers at least `4` in it are those
agreeing with the entry `i` capped at `2`, and each codes `d₁` below `2`
(`TowerProfile.FrozenServerTwo`); no separating server exists there. -/
theorem exists_frozen_of_entry {i : Fin ((I.tower 1).catalogue 2).card}
    {d₁ : Fin (I.tower 1).card} (hd₁ : (I.tower 1).toCellScheme.grade d₁ ≤ 2)
    (hb₁ : (I.tower 1).catalogueEntry 2 i d₁ ≠ ⊥)
    (hb₁2 : (I.tower 1).catalogueEntry 2 i d₁ < (((2 : Ordinal.{u})) : Label.{u})) :
    ∃ e : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 2) (fun d ↦ e d) ∧
      (∀ d, e (oneCell I d) = supportMap ((I.tower 1).catalogueEntry 2 i d)) ∧
      (∀ j, 4 ≤ e (twoCell I (Fin.natAdd _ j)) → ∀ d,
        min ((I.tower 1).catalogueEntry 2 j d) (((2 : Ordinal.{u})) : Label.{u}) =
          min ((I.tower 1).catalogueEntry 2 i d) (((2 : Ordinal.{u})) : Label.{u})) ∧
      (∀ j, 4 ≤ e (twoCell I (Fin.natAdd _ j)) → FrozenServerTwo I e 4 j) ∧
      ¬ SeparatingServerTwo I e 4 := by
  classical
  set b := (I.tower 1).catalogueEntry 2 i with hbdef
  have hb : b ∈ (I.tower 1).catalogue 2 := Scheme.catalogueEntry_mem i
  have hp : (I.tower 1).rows.IsLawfulBelow (univ, 2) fun d ↦ b d.1 :=
    (Scheme.mem_catalogue.mp hb).1.isLawfulBelow _
  obtain ⟨r, hr, -, hrc⟩ := Scheme.exists_extension_fieldLayer (S := I.tower 1) (k := 2)
    (hS := I.not_univ_succ_le_tower 1) hp hb (h := ⊤) (isSelfVisible_top 2) bot_lt_top
    (.inl fun o ho ↦ absurd ho (by simp)) fun _ _ ↦ rfl
  have hrf (x : (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2)) :
      r x = (I.tower 1).fieldRow 2 b x.1 := by
    simpa using hrc x
  have hlaw : (I.tower 2).rows.IsLawfulBelow (univ, 2) (supportMap ∘ r) :=
    hr.map_of_bot_iff hr (fun d ↦ d.2.2) isWitness_supportMap fun _ ↦ supportMap_eq_bot_iff
  set e : Fin (scheme I).card → Label.{u} := fun x ↦
    if hx : (x : ℕ) < (I.tower 2).card then supportMap ((I.tower 1).fieldRow 2 b ⟨x, hx⟩)
    else ⊥ with hedef
  have hetwo (y : Fin (I.tower 2).card) :
      e (twoCell I y) = supportMap ((I.tower 1).fieldRow 2 b y) := by
    have hy : ((twoCell I y : Fin (scheme I).card) : ℕ) < (I.tower 2).card := y.2
    simp only [hedef, hy, ↓reduceDIte]
    rfl
  have heone (d : Fin (I.tower 1).card) : e (oneCell I d) = supportMap (b d) := by
    refine (hetwo (Fin.castAdd _ d)).trans ?_
    rw [Scheme.fieldRow_castAdd]
  have henew (j : Fin ((I.tower 1).catalogue 2).card) :
      e (twoCell I (Fin.natAdd _ j)) = supportMap (agreementHeight ((I.tower 1).fieldGrid 2) b
        ((I.tower 1).catalogueEntry 2 j)) := by
    refine (hetwo (Fin.natAdd _ j)).trans ?_
    rw [Scheme.fieldRow_natAdd]
  have he : (scheme I).rows.IsLawfulBelow (univ, 2) (fun d ↦ e d) := by
    refine isLawfulBelow_scheme_of_two ?_
    have heq : (fun d : (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2) ↦
        e (twoCell I d)) = supportMap ∘ r := funext fun d ↦ by
      exact (hetwo d.1).trans (congrArg supportMap (hrf d).symm)
    rw [heq]
    exact hlaw
  have hagree (j : Fin ((I.tower 1).catalogue 2).card)
      (hj : 4 ≤ e (twoCell I (Fin.natAdd _ j))) (d : Fin (I.tower 1).card) :
      min ((I.tower 1).catalogueEntry 2 j d) (((2 : Ordinal.{u})) : Label.{u}) =
        min (b d) (((2 : Ordinal.{u})) : Label.{u}) := by
    rw [henew] at hj
    set g := agreementHeight ((I.tower 1).fieldGrid 2) b ((I.tower 1).catalogueEntry 2 j)
    have hg0 : g ≠ ⊥ := fun h0 ↦ by
      rw [h0, show supportMap (⊥ : Label.{u}) = ⊥ from ite_eq_left rfl] at hj
      exact absurd hj (by simp)
    obtain ⟨hgG, hgag⟩ := agreementHeight_spec (bot_mem_grid 2 _) b ((I.tower 1).catalogueEntry 2 j)
    have h2g : (((2 : Ordinal.{u})) : Label.{u}) ≤ g := by
      rcases mem_grid.mp hgG with h0 | ⟨c, -, hc⟩
      · exact absurd h0 hg0
      · have := (gridPoint_le_gridPoint (k := 2)).mpr (Nat.zero_le c)
        have h2 : (((2 : Ordinal.{u})) : Label.{u}) ≤ gridPoint 2 c := by
          simpa [gridPoint] using this
        exact h2.trans_eq hc.symm
    exact (min_eq_min_of_le' (hgag d) h2g).symm
  have hfrozen (j : Fin ((I.tower 1).catalogue 2).card)
      (hj : 4 ≤ e (twoCell I (Fin.natAdd _ j))) : FrozenServerTwo I e 4 j := by
    have h12 := (hagree j hj d₁).symm
    rw [min_eq_left hb₁2.le] at h12
    refine ⟨d₁, hd₁, ?_, .inl ?_⟩
    · rw [heone, supportMap_of_ne_bot hb₁]
      exact le_top
    · refine not_le.mp fun hle ↦ hb₁2.ne ?_
      rw [h12, min_eq_right hle]
  exact ⟨e, he, heone, hagree, hfrozen, not_separatingServerTwo_of_frozen hfrozen⟩

/-- **The state where route (b) fails**: an entry `i` coding a cell of grade at most `2` below `2`
and not by `⊥`, and a cell of grade `2` not by `⊥`. -/
def LowEntryTwo (I : Seed.{u} α 3) : Prop :=
  ∃ i : Fin ((I.tower 1).catalogue 2).card,
    (∃ d₁, (I.tower 1).toCellScheme.grade d₁ ≤ 2 ∧ (I.tower 1).catalogueEntry 2 i d₁ ≠ ⊥ ∧
      (I.tower 1).catalogueEntry 2 i d₁ < (((2 : Ordinal.{u})) : Label.{u})) ∧
    ∃ z₀, (I.tower 1).toCellScheme.grade z₀ = 2 ∧ (I.tower 1).catalogueEntry 2 i z₀ ≠ ⊥

/-- **Separating servers fail at a low entry**: the support labelling of
`TowerProfile.exists_frozen_of_entry` meets every hypothesis of `TowerProfile.SeparatingServersTwo`
with the cap `4`, and no server separates there. -/
theorem not_separatingServersTwo_of_lowEntry (hI : LowEntryTwo I) : ¬ SeparatingServersTwo I := by
  obtain ⟨i, ⟨d₁, hd₁, hb₁, hb₁2⟩, z₀, hz₀, hbz⟩ := hI
  obtain ⟨e, he, heone, -, -, hns⟩ := exists_frozen_of_entry hd₁ hb₁ hb₁2
  intro hs
  refine hns (hs e he 4 ((isSelfVisible_ofNat 4).mpr le_rfl) (WithBot.bot_lt_coe _) ⟨z₀, hz₀, ?_⟩)
  rw [heone, supportMap_of_ne_bot hbz]
  exact le_top

end TowerProfile

end VaughtConjecture
