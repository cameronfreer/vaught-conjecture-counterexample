/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OrbitCode

/-!
# The cutoff must be coded with the profile

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the coding of the states
above the controllers); semantic contract, items 3 and 8.

The sections indexed by states (`VaughtConjecture.Continuation.LowStateLevel`) read the controllers
at the code of a state.  Capped agreement of a decoded construction on codes
(`Label.min_upperDecoderAt_comp_eq`) asks the codes of two labellings agreeing capped at a cap to
agree capped there.  For the cells of the labelling this is prefix stability
(`Label.orbitCode_eq_of_min_eq`).  For a value that is **not** a value of the labelling, such as a
cutoff coded by the orbit map of the amalgam profile alone, it fails
(`Label.not_min_orbitMap_eq_extra`, compiled in this repository): with one cell, `w = ω + 1` and
`w' = ω · 2 + 1` agree capped at `h = ω + 1`; the value `x = ω` below `h` has the key `h`, a key of
`w` (through its cell) but not of `w'`, so its orbit map is the grid point `ω + 1` of the code
block `1` for `w` and the grid point `1` of the code block `0` for `w'`, apart already capped at
`h`.  So the cutoff of a state is coded together with its profile: the state code is the orbit
code over all fields (`ProfileTower.scode`), where the cutoff is a value of the labelling and
prefix stability applies.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Label

open Ordinal

/-- **The orbit map of a value outside the labelling does not agree capped**: two labellings of
one cell agreeing capped at a cap `h` self-visible and short at `1` code a value `x < h` apart,
capped at `h`. -/
theorem not_min_orbitMap_eq_extra :
    ∃ (w w' : Unit → Label.{u}) (h x : Label.{u}), IsSelfVisible 1 h ∧ IsShort 1 h ∧
      (∀ d, min (w d) h = min (w' d) h) ∧ x < h ∧
      min (orbitMap 1 w x) h ≠ min (orbitMap 1 w' x) h := by
  classical
  set h : Label.{u} := gridPoint 1 1 with hh
  set h' : Label.{u} := gridPoint 1 2 with hh'
  set x : Label.{u} := ((ω * ((1 : ℕ) : Ordinal.{u}) + ((0 : ℕ) : Ordinal.{u}) : Ordinal.{u}) :
    Label.{u}) with hx
  have hxh : visibilityReplace 1 1 x = h := by
    rw [hx, visibilityReplace_block]
    rfl
  have hhv : visibilityReplace 1 1 h = h := isSelfVisible_gridPoint 1 1
  have hh'v : visibilityReplace 1 1 h' = h' := isSelfVisible_gridPoint 1 2
  have hlt : h < h' := gridPoint_lt_gridPoint.mpr (by omega)
  have hx0 : x ≠ ⊥ := by rw [hx]; exact WithBot.coe_ne_bot
  have hh0 : h ≠ ⊥ := gridPoint_ne_bot 1 1
  have hh'0 : h' ≠ ⊥ := gridPoint_ne_bot 1 2
  refine ⟨fun _ ↦ h, fun _ ↦ h', h, x, isSelfVisible_gridPoint 1 1, isShort_gridPoint 1 1,
    fun _ ↦ by rw [min_self, min_eq_right hlt.le], ?_, ?_⟩
  · rw [hx, hh, gridPoint]
    refine WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ?_)
    have h01 : ((0 : ℕ) : Ordinal.{u}) < ((1 : ℕ) : Ordinal.{u}) := by
      exact_mod_cast Nat.zero_lt_one
    exact (add_lt_add_iff_left _).mpr h01
  -- the code of `x` for `w`: a key, not an orbit key, of rank at least `1`
  have hkey : IsKey 1 (fun _ : Unit ↦ h) x := ⟨(), hh0, by rw [hhv, hxh]⟩
  have hnorb : ¬ IsOrbitKey 1 (fun _ : Unit ↦ h) x := fun ⟨_, _, hsv⟩ ↦ hsv hhv
  have hcb : 1 ≤ codeBlock 1 (fun _ : Unit ↦ h) x := by
    rw [codeBlock_of_not_isOrbitKey hkey hnorb]
    have := one_le_keyRank hkey
    omega
  have h1 : orbitMap 1 (fun _ : Unit ↦ h) x = gridPoint 1 (codeBlock 1 (fun _ : Unit ↦ h) x) :=
    orbitMap_of_not_isOrbitKey hx0 hnorb
  -- the code of `x` for `w'`: no key at or below the key of `x`
  have hnorb' : ¬ IsOrbitKey 1 (fun _ : Unit ↦ h') x := fun ⟨_, _, hsv⟩ ↦ hsv hh'v
  have hrank : keyRank 1 (fun _ : Unit ↦ h') x = 0 := by
    unfold keyRank valueRank
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy
    obtain ⟨_, -, rfl⟩ := Finset.mem_image.mp hy
    rw [hh'v, hxh, not_and, not_le]
    exact fun _ ↦ hlt
  have hcb' : codeBlock 1 (fun _ : Unit ↦ h') x = 0 := by
    unfold codeBlock
    split_ifs <;> simp [hrank]
  have h2 : orbitMap 1 (fun _ : Unit ↦ h') x = gridPoint 1 0 := by
    rw [orbitMap_of_not_isOrbitKey hx0 hnorb', hcb']
  rw [h1, h2, min_eq_right (gridPoint_le_gridPoint.mpr hcb),
    min_eq_left (gridPoint_le_gridPoint.mpr (by omega))]
  exact (gridPoint_lt_gridPoint.mpr (by omega)).ne'

end VaughtConjecture.Label
