/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.FamilyCofaces

/-!
# Examples: nonempty uniformity and dominance instances

Regression examples for `VaughtConjecture.Extension.FamilyCofaces`.

* The one-point stage type with label `1` at `ω` is legal.
* Over the stage type on no points, unconditionally: uniformity at `γ = 0` at stage `ω` (label
  `1`), uniformity at `γ = ω` at stage `ω · 2` (label `ω + 1`), and dominance at `γ = 5` at stage
  `ω` (label `6`).  The donor is itself the coface; no coatom extension is used.
* Over every legal type: uniformity at `γ = ω` at stage `ω · 2` under the plain coatom extension
  property, and dominance under the form with apex.
-/

namespace VaughtConjecture.StageType

open Label
open scoped Ordinal

/-- The one-point stage type with label `1` at `ω`. -/
example : ∃ d : StageType.{0} ω 1, d.IsLegal ∧ ∃ i, d.toCellScheme.grade i = 1 ∧ d.label i = 1 := by
  simpa using exists_onePoint_label (α := ω) (c := 1) (by simp) Ordinal.one_lt_omega0

/-- Uniformity at `γ = 0` over the stage type on no points at `ω`, by the label `1`. -/
example (p : StageType.{0} ω 0) : (p.cofaces ∩ uniformityFamily 0).Nonempty := by
  obtain ⟨d, hd, i, -, hdi⟩ :=
    exists_onePoint_label (α := ω) (c := 1) (by simp) Ordinal.one_lt_omega0
  exact ⟨d, mem_cofaces_of_zero hd, i, by rw [hdi]; exact_mod_cast zero_le_one,
    by rw [hdi, zero_add]; exact_mod_cast Ordinal.one_lt_omega0⟩

/-- `ω + 1 < ω · 2`. -/
private theorem omega0_add_one_lt : (ω + 1 : Ordinal.{0}) < ω * 2 := by
  rw [Ordinal.mul_two]
  exact (add_lt_add_iff_left ω).mpr Ordinal.one_lt_omega0

/-- Uniformity at `γ = ω` over the stage type on no points at `ω · 2`, by the label `ω + 1`. -/
example (p : StageType.{0} (ω * 2) 0) : (p.cofaces ∩ uniformityFamily ω).Nonempty := by
  have hc :=
    isSelfVisible_coe_add (k := 1) (K := 1) Ordinal.isSuccLimit_omega0.isSuccPrelimit le_rfl
  obtain ⟨d, hd, i, -, hdi⟩ := exists_onePoint_label (α := ω * 2) (c := ω + 1)
    (by simpa using hc) omega0_add_one_lt
  exact ⟨d, mem_cofaces_of_zero hd, i, by rw [hdi]; exact_mod_cast le_self_add,
    by rw [hdi]; exact_mod_cast (add_lt_add_iff_left ω).mpr Ordinal.one_lt_omega0⟩

/-- Dominance at `γ = 5` over the stage type on no points at `ω`, by the label `6` at a cell of
grade `1`. -/
example (p : StageType.{0} ω 0) : (p.cofaces ∩ dominanceFamily 5).Nonempty := by
  obtain ⟨d, hd, i, hgi, hdi⟩ := exists_onePoint_label (α := ω) (c := (6 : ℕ))
    (isSelfVisible_natCast 6 |>.mpr (by omega)) (Ordinal.natCast_lt_omega0 6)
  refine ⟨d, mem_cofaces_of_zero hd, i, hgi, ?_⟩
  rw [hdi]
  exact_mod_cast (show (5 : ℕ) < 6 by omega)

/-- Uniformity at `γ = ω` at stage `ω · 2`, over every legal type, under the plain coatom
extension property. -/
example (hext : HasCoatomExtensions.{0} (ω * 2)) {n : ℕ} {p : StageType.{0} (ω * 2) n}
    (hp : p.IsLegal) : (p.cofaces ∩ uniformityFamily ω).Nonempty :=
  nonempty_cofaces_inter_uniformityFamily hext
    (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 two_pos).isSuccPrelimit hp
    ((lt_add_of_pos_right ω Ordinal.omega0_pos).trans_eq (Ordinal.mul_two ω).symm)

/-- Dominance at every `γ < ω`, over every legal type, under the coatom extension property with
apex. -/
example (hext : HasApexCoatomExtensions.{0} ω) {n : ℕ} {p : StageType.{0} ω n} (hp : p.IsLegal)
    {γ : Ordinal.{0}} (hγ : γ < ω) : (p.cofaces ∩ dominanceFamily γ).Nonempty :=
  nonempty_cofaces_inter_dominanceFamily hext Ordinal.isSuccLimit_omega0.isSuccPrelimit hp hγ

end VaughtConjecture.StageType
