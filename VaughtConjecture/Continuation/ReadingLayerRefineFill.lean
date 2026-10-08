/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerRefine

/-!
# The fill from a refining server

Roadmap, Layer 3 ((R3) of the table of 3.4).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label
open scoped Ordinal

namespace TowerProfile

open TopReadingApexExample

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **A labelling of the cells of grade at most `3` from one of grade `1`.**  As
`TowerProfile.exists_three_of_server`, with the labelling of the cells of grade `1` given: a
labelling `w₁` lawful below `(univ, 1)`, equal to `f` on the left coatom, to `e` where `e` is below
the cap, and at least `V` where `e` is at least the cap.  Then some labelling lawful below
`(univ, 3)` is `f` on the left coatom, `w₁` at the grade `1`, and agrees with `e` capped at `h`. -/
theorem exists_three_of_one {e : Fin (scheme I).card → Label.{u}}
    (he : (scheme I).rows.IsLawfulBelow (univ, 4) fun d ↦ e d)
    {h : Label.{u}} (hh : IsSelfVisible 4 h) (hhb : ⊥ < h)
    {f : Fin (scheme I).card → Label.{u}}
    (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d)
    (hfe : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      min (f d) h = min (e d) h)
    {V : Label.{u}} (hV : IsSelfVisible 2 V) (hhV : h ≤ V)
    (hfV : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.grade d ≤ 2 → h ≤ f d → V ≤ f d)
    (hfV' : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.grade d = 2 → h ≤ f d → f d ≤ V)
    (hf3 : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.grade d = 3 → f d ≤ h)
    {w₁ : Fin (scheme I).card → Label.{u}}
    (hw₁ : (scheme I).rows.IsLawfulBelow (univ, 1) fun d ↦ w₁ d)
    (hw₁f : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.grade d = 1 → f d = w₁ d)
    (hw₁lt : ∀ d, (scheme I).toCellScheme.grade d = 1 → e d < h → w₁ d = e d)
    (hw₁ge : ∀ d, (scheme I).toCellScheme.grade d = 1 → h ≤ e d → V ≤ w₁ d) :
    ∃ w : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 3) (fun d ↦ w d) ∧
      (∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4), w d = f d) ∧
      (∀ d ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        min (w d) h = min (e d) h) ∧
      ∀ d, (scheme I).toCellScheme.grade d = 1 → w d = w₁ d := by
  classical
  set C := (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) with hCdef
  have hh0 : h ≠ ⊥ := hhb.ne'
  have hV0 : V ≠ ⊥ := (hhb.trans_le hhV).ne'
  have hpos (d : Fin (scheme I).card) : 1 ≤ (scheme I).toCellScheme.grade d :=
    isWellFormed_scheme.isWellFormed.grade_pos d
  have hmem1 {d : Fin (scheme I).card} (hd : (scheme I).toCellScheme.grade d = 1) :
      d ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 1) :=
    ⟨subset_univ _, hd.le⟩
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
    else if (scheme I).toCellScheme.grade d = 1 then w₁ d
    else if (scheme I).toCellScheme.grade d = 2 then Θ₂ (e d) else Θ₃ (e d) with hwdef
  have hwC {d : Fin (scheme I).card} (hd : d ∈ C) : w d = f d := ite_eq_left hd
  have hw1 {d : Fin (scheme I).card} (hd : (scheme I).toCellScheme.grade d = 1) :
      w d = w₁ d := by
    by_cases hdC : d ∈ C
    · rw [hwC hdC, hw₁f d hdC hd]
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
        exact ⟨hw₁lt d h1, hw₁ge d h1⟩
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
  obtain ⟨hgo, hgl, hga⟩ := (CellScheme.Rows.isLawfulBelow_iff_forall (w := fun z ↦ w₁ z)).mp hw₁
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
              min (w₁ d) (w₁ s) :=
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
  · intro d hd
    exact hw1 hd

end TowerProfile

end VaughtConjecture
