/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedGradeThreeStrip

/-!
# Decoder preservation at a cut: key strips and non-key strips

Roadmap, Layer 3 ((R3) and (R4), the decoder of a lift at a grade `k ≥ 3`).

Let `W` be a state whose orbit code `P = orbitCode k W` agrees with `W` capped at a cut `h` (as for
the state step of a lift with a canonical anchor: `Label.min_orbitCode_eq`).  **Decoder
preservation** at a label `x` is `min (orbitDecoder k W h x) h = min x h`.

* **The dichotomy** (`Label.orbitDecoder_eq_or_code_at_cut`): for `x` on the strip of `h` below
  it, either the orbit decoder reads `x` literally, or some cell is coded at the cut `h` with a
  value that is not an orbit key.  On a key strip the second premise of
  `Label.orbitDecoder_of_orbitClass` (the original key of the cell is the key of `x`) is derived,
  not assumed: a cell coded below `h` carries its code as value (capped agreement), and a cell
  coded at `h` with an orbit key value shares its key with a value of its class coded below `h`.
* **The exact criterion** (`Label.min_orbitDecoder_eq_iff`): preservation fails at `x` exactly
  when `x` lies on the strip of `h` below it and a cell is coded at `h` from a non-orbit key value
  (then `Label.le_orbitDecoder_of_code_at_cut` applies).
* **Even cuts** (`Label.min_orbitDecoder_eq_of_even`): a non-orbit key is coded in an odd block, so
  at a cut `ω * (2 r) + k` preservation holds at every label; this covers the code of a strip pair,
  whose block is even and positive (`Label.orbitCode_stripPair_even`; the instance
  `Label.stripPair_moved` moves the pair `ω * 5 + 2`, `ω * 5 + 3` at the grade `3` to the block
  `2`).
* **The failing case on a non-key strip** (`Label.exists_nonKeyStrip_failure`): with a canonical
  anchor, a state agreeing with it capped at the cut `ω + k`, coded at the cut from a non-orbit key,
  and the lower-layer grid height `ω + j` (`2 ≤ j < k`) on the strip, preservation fails.

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset
open scoped Ordinal

namespace Label

variable {ι : Type*} [Fintype ι] {k : ℕ} {W : ι → Label.{u}} {h x : Label.{u}}

/-- A cell coded strictly below the cut carries its code as value, when the code agrees with the
state capped at the cut. -/
theorem eq_orbitCode_of_lt (hag : ∀ d, min (orbitCode k W d) h = min (W d) h) {e : ι}
    (hlt : orbitCode k W e < h) : W e = orbitCode k W e := by
  have h1 := hag e
  rw [min_eq_left hlt.le] at h1
  rcases le_or_gt h (W e) with hle | hgt
  · rw [min_eq_right hle] at h1
    exact absurd h1 hlt.ne
  · rw [min_eq_left hgt.le] at h1
    exact h1.symm

/-- **The dichotomy at a key strip**: for `x` on the strip of `h` below it, either the orbit decoder
reads `x` literally or some cell is coded at `h` from a value that is not an orbit key. -/
theorem orbitDecoder_eq_or_code_at_cut (hag : ∀ d, min (orbitCode k W d) h = min (W d) h)
    (hxh : x < h) (hx : visibilityReplace k k x = h) :
    orbitDecoder k W h x = x ∨ ∃ e, orbitCode k W e = h ∧ ¬ IsOrbitKey k W (W e) := by
  by_cases hjump : ∃ e, orbitCode k W e = h ∧ ¬ IsOrbitKey k W (W e)
  · exact .inr hjump
  refine .inl (orbitDecoder_of_orbitClass hxh fun e he ↦ ?_)
  rw [hx] at he ⊢
  have hh0 : h ≠ ⊥ := ne_bot_of_gt hxh
  have hWe : W e ≠ ⊥ := fun h0 ↦ hh0 (by
    rw [← he, orbitCode_eq_bot_iff.mpr h0, visibilityReplace_bot])
  have hok : IsOrbitKey k W (W e) := by
    by_contra hn
    have hP : orbitCode k W e = gridPoint k (codeBlock k W (W e)) := by
      rw [orbitCode_apply]; exact orbitMap_of_not_isOrbitKey hWe hn
    have hsv : IsSelfVisible k (orbitCode k W e) := hP ▸ isSelfVisible_gridPoint k _
    exact hjump ⟨e, hsv.symm.trans he, hn⟩
  -- a cell coded strictly below the cut has the key of the cut
  have hbelow {e' : ι} (hv : visibilityReplace k k (orbitCode k W e') = h)
      (hlt : orbitCode k W e' < h) : visibilityReplace k k (W e') = h := by
    rw [eq_orbitCode_of_lt hag hlt]; exact hv
  refine ⟨hok, ?_⟩
  have hPle : orbitCode k W e ≤ h := he ▸ le_visibilityReplace (by omega) _
  rcases hPle.lt_or_eq with hlt | heq
  · exact hbelow he hlt
  · obtain ⟨e', he'k, hnv⟩ := id hok
    have hWe' : W e' ≠ ⊥ := fun h0 ↦ hnv (h0 ▸ isSelfVisible_bot k)
    have hv' : visibilityReplace k k (orbitCode k W e') = h := by
      rw [orbitCode_apply, visibilityReplace_orbitMap hWe', codeBlock_congr he'k,
        ← visibilityReplace_orbitMap hWe, ← orbitCode_apply, he]
    have hnv' : ¬ IsSelfVisible k (orbitCode k W e') := by
      rw [orbitCode_apply, isSelfVisible_orbitMap_iff hWe']
      rintro (h' | h')
      · exact h' ((isOrbitKey_congr he'k).mpr hok)
      · exact hnv h'
    have hle' : orbitCode k W e' ≤ h := hv' ▸ le_visibilityReplace (by omega) _
    have hlt' : orbitCode k W e' < h := lt_of_le_of_ne hle' fun hq ↦ hnv' (by
      rw [hq, ← hv']
      exact visibilityReplace_self_visibilityReplace_of_le le_rfl le_rfl _)
    rw [← he'k]
    exact hbelow hv' hlt'

/-- **The exact criterion of decoder preservation**: for a cut `h` self-visible at `k` and a code
agreeing with the state capped at `h`, the orbit decoder keeps `x` capped at `h` exactly when `x`
is not on the strip of `h` below it with a cell coded at `h` from a non-orbit key value. -/
theorem min_orbitDecoder_eq_iff (hag : ∀ d, min (orbitCode k W d) h = min (W d) h)
    (hh : IsSelfVisible k h) :
    min (orbitDecoder k W h x) h = min x h ↔
      ¬ (x < h ∧ visibilityReplace k k x = h ∧
        ∃ e, orbitCode k W e = h ∧ ¬ IsOrbitKey k W (W e)) := by
  constructor
  · rintro hpres ⟨hxh, hx, e, he, hno⟩
    have hWe : h ≤ W e := by
      have h1 := hag e
      rw [he, min_self] at h1
      exact min_eq_right_iff.mp h1.symm
    have hj := le_orbitDecoder_of_code_at_cut hh he hno hWe hx
    rw [min_eq_right hj, min_eq_left hxh.le] at hpres
    exact hxh.ne hpres.symm
  · intro hno
    rcases le_or_gt h x with hhx | hxh
    · rw [min_eq_right hhx]
      exact min_eq_right ((min_eq_right hhx).symm.trans_le (le_max_left _ _))
    rcases lt_or_ge (visibilityReplace k k x) h with hv | hv
    · rw [orbitDecoder_of_visibilityReplace_lt hxh hv]
    have hvx : visibilityReplace k k x = h := le_antisymm
      (hh ▸ monotone_visibilityReplace le_rfl hxh.le) hv
    rcases orbitDecoder_eq_or_code_at_cut hag hxh hvx with hl | hr
    · rw [hl]
    · exact absurd ⟨hxh, hvx, hr⟩ hno

/-- A value that is not an orbit key is coded in an odd block. -/
theorem orbitCode_ne_even_of_not_isOrbitKey {e : ι} (hWe : W e ≠ ⊥)
    (hno : ¬ IsOrbitKey k W (W e)) (r : ℕ) : orbitCode k W e ≠ gridPoint k (2 * r) := by
  intro h
  have hk : IsKey k W (W e) := isKey_apply_iff.mpr hWe
  have h1 := one_le_keyRank hk
  rw [orbitCode_apply, orbitMap_of_not_isOrbitKey hWe hno, codeBlock_of_not_isOrbitKey hk hno]
    at h
  have := gridPoint_le_gridPoint.mp h.le
  have := gridPoint_le_gridPoint.mp h.ge
  omega

/-- **Decoder preservation at an even cut**: at a cut `ω * (2 r) + k`, for a code agreeing with the
state capped at the cut, the orbit decoder keeps every label capped at the cut. -/
theorem min_orbitDecoder_eq_of_even (r : ℕ)
    (hag : ∀ d, min (orbitCode k W d) (gridPoint k (2 * r)) = min (W d) (gridPoint k (2 * r)))
    (y : Label.{u}) :
    min (orbitDecoder k W (gridPoint k (2 * r)) y) (gridPoint k (2 * r)) =
      min y (gridPoint k (2 * r)) := by
  refine (min_orbitDecoder_eq_iff hag (isSelfVisible_gridPoint k _)).mpr ?_
  rintro ⟨hlt, -, e, he, hno⟩
  have hWe : W e ≠ ⊥ := fun h0 ↦ gridPoint_ne_bot k (2 * r) (by
    rw [← he, orbitCode_eq_bot_iff.mpr h0])
  exact orbitCode_ne_even_of_not_isOrbitKey hWe hno r he

/-- **The code of a strip pair is at an even positive block**: for a value `W a` not self-visible
at `k` with the key `W a' = visibilityReplace k k (W a)` off the natural strip, the code of `W a'`
is `ω * (2 r) + k` with `r ≥ 1`. -/
theorem orbitCode_stripPair_even {a a' : ι} (h0 : W a ≠ ⊥) (hnv : ¬ IsSelfVisible k (W a))
    (hkey : visibilityReplace k k (W a) = W a') (hnat : W a' ≠ gridPoint k 0) :
    ∃ r, 1 ≤ r ∧ orbitCode k W a' = gridPoint k (2 * r) := by
  have hidem : visibilityReplace k k (W a') = visibilityReplace k k (W a) := by
    rw [← hkey]
    exact visibilityReplace_self_visibilityReplace_of_le le_rfl le_rfl _
  have h0' : W a' ≠ ⊥ := fun h ↦ h0 (visibilityReplace_eq_bot_iff.mp (hkey.trans h))
  have hok' : IsOrbitKey k W (W a') := (isOrbitKey_congr hidem).mpr ⟨a, rfl, hnv⟩
  have hvis' : visibilityReplace k k (W a') = W a' := hidem.trans hkey
  have hn : visibilityReplace k k (W a') ≠ gridPoint k 0 := by rw [hvis']; exact hnat
  have hcb := codeBlock_of_isOrbitKey hok' hn
  have hk := one_le_keyRank hok'.isKey
  refine ⟨keyRank k W (W a'), hk, ?_⟩
  have hP : IsSelfVisible k (orbitCode k W a') := by
    rw [orbitCode_apply]
    exact (isSelfVisible_orbitMap_iff h0').mpr (.inr hvis')
  have hv := visibilityReplace_orbitMap (k := k) (w := W) h0'
  rw [hcb, ← orbitCode_apply] at hv
  exact hP.symm.trans hv

/-- **The inherited strip pair at the grade `3`, moved to a positive block**: the pair
`ω * 5 + 2`, `ω * 5 + 3` is coded at the grade `3` in the block `2` (`r = 1`), and every state whose
code agrees with it capped at the moved cut `ω * 2 + 3` keeps every label capped there. -/
theorem stripPair_moved :
    orbitCode 3 (![gridPoint 2 5, gridPoint 3 5] : Fin 2 → Label.{u}) 1 = gridPoint 3 2 ∧
      ∀ {κ : Type*} [Fintype κ] (W' : κ → Label.{u}),
        (∀ d, min (orbitCode 3 W' d) (gridPoint 3 2) = min (W' d) (gridPoint 3 2)) →
        ∀ y, min (orbitDecoder 3 W' (gridPoint 3 2) y) (gridPoint 3 2) =
          min y (gridPoint 3 2) := by
  refine ⟨?_, fun W' hag y ↦ min_orbitDecoder_eq_of_even 1 hag y⟩
  set W : Fin 2 → Label.{u} := ![gridPoint 2 5, gridPoint 3 5] with hW
  have hkey : visibilityReplace 3 3 (W 0) = W 1 := visibilityReplace_gridPoint_of_lt (by omega) 5
  have hnv : ¬ IsSelfVisible 3 (W 0) := fun h ↦ by
    have h' : gridPoint.{u} 2 5 = gridPoint 3 5 := h.symm.trans hkey
    exact absurd (gridPoint_lt_gridPoint_iff_lex.mpr (.inr ⟨rfl, by omega⟩) :
      gridPoint.{u} 2 5 < gridPoint 3 5) (by rw [h']; exact lt_irrefl _)
  have hnat : W 1 ≠ gridPoint 3 0 := fun h ↦ by
    have := gridPoint_le_gridPoint.mp h.le
    omega
  -- the key rank is one: both values have the key `ω * 5 + 3`
  have hconst : (fun d ↦ visibilityReplace 3 3 (W d)) = fun _ ↦ gridPoint 3 5 := by
    funext d
    fin_cases d
    · exact hkey
    · exact isSelfVisible_gridPoint 3 5
  have hk1 : keyRank 3 W (W 1) ≤ 1 := by
    classical
    unfold keyRank valueRank
    rw [hconst]
    refine (card_le_card (filter_subset _ _)).trans ?_
    rw [image_const univ_nonempty, card_singleton]
  have h0' : W 1 ≠ ⊥ := gridPoint_ne_bot 3 5
  have hok' : IsOrbitKey 3 W (W 1) :=
    ⟨0, hkey.trans (isSelfVisible_gridPoint.{u} 3 5).symm, hnv⟩
  have hcb := codeBlock_of_isOrbitKey hok' (by
    rw [show visibilityReplace 3 3 (W 1) = W 1 from isSelfVisible_gridPoint 3 5]; exact hnat)
  have hrank := one_le_keyRank hok'.isKey
  have hP' : IsSelfVisible 3 (orbitCode 3 W 1) := by
    rw [orbitCode_apply]
    exact (isSelfVisible_orbitMap_iff h0').mpr (.inr (isSelfVisible_gridPoint 3 5))
  have hv := visibilityReplace_orbitMap (k := 3) (w := W) h0'
  rw [hcb, ← orbitCode_apply, show keyRank 3 W (W 1) = 1 by omega] at hv
  exact hP'.symm.trans hv

/-- The orbit code of a single cell at a grid point of its grade is the grid point of the
block `1`. -/
theorem orbitCode_single_gridPoint (k b : ℕ) :
    orbitCode k (fun _ : Fin 1 ↦ gridPoint.{u} k b) 0 = gridPoint k 1 := by
  classical
  have hno : ¬ IsOrbitKey k (fun _ : Fin 1 ↦ gridPoint.{u} k b) (gridPoint k b) :=
    fun ⟨_, _, hs⟩ ↦ hs (isSelfVisible_gridPoint k b)
  have hkey : IsKey k (fun _ : Fin 1 ↦ gridPoint.{u} k b) (gridPoint k b) :=
    isKey_apply_iff (d := 0).mpr (gridPoint_ne_bot k b)
  have hr : keyRank k (fun _ : Fin 1 ↦ gridPoint.{u} k b) (gridPoint k b) = 1 :=
    le_antisymm ((keyRank_le_card _ _ _).trans (by simp)) (one_le_keyRank hkey)
  rw [orbitCode_apply, orbitMap_of_not_isOrbitKey (gridPoint_ne_bot k b) hno,
    codeBlock_of_not_isOrbitKey hkey hno, hr]

/-- **The failing case on a non-key strip**: at a grade `k` and a lower grade `2 ≤ j < k`, the
canonical anchor `ω + k` (one cell), the state `ω * 2 + k` agreeing with it capped at the cut
`ω + k` (its code is the anchor, coded at the cut from a non-orbit key), and the lower-layer grid
height `ω + j` on the strip of the cut: decoder preservation fails at `ω + j`. -/
theorem exists_nonKeyStrip_failure {j : ℕ} (hj : j < k) :
    orbitCode k (fun _ : Fin 1 ↦ gridPoint.{u} k 1) = (fun _ ↦ gridPoint k 1) ∧
      (∀ d : Fin 1, min ((fun _ ↦ gridPoint.{u} k 2) d) (gridPoint k 1) =
        min ((fun _ ↦ gridPoint.{u} k 1) d) (gridPoint k 1)) ∧
      ¬ (min (orbitDecoder k (fun _ : Fin 1 ↦ gridPoint.{u} k 2) (gridPoint k 1) (gridPoint j 1))
          (gridPoint k 1) = min (gridPoint j 1) (gridPoint k 1)) := by
  have hle : gridPoint.{u} k 1 ≤ gridPoint k 2 := gridPoint_le_gridPoint.mpr (by omega)
  refine ⟨funext fun d ↦ ?_, fun _ ↦ by simp only [min_eq_right hle, min_self], ?_⟩
  · fin_cases d; exact orbitCode_single_gridPoint k 1
  · obtain ⟨-, -, hlt, hjump, -⟩ := lowerHeight_strip_jump (Γ := ∅) (B' := 1) hj le_rfl
      (W := fun _ : Fin 1 ↦ gridPoint.{u} k 2) (e := 0) (orbitCode_single_gridPoint k 2)
      (fun ⟨_, _, hs⟩ ↦ hs (isSelfVisible_gridPoint k 2)) hle
    intro h
    rw [min_eq_right hjump, min_eq_left hlt.le] at h
    exact hlt.ne h.symm

end Label

end VaughtConjecture
