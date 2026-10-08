/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerRefine

/-!
# The fill from a refining server

Roadmap, Layer 3 ((R3) of the table of 3.4).

* **Gluing** (`TowerProfile.exists_three_of_one`, compiled): a labelling of the grade `1` as given
  by `TowerProfile.exists_one_of_target` glues with the raised and capped reading mark at the
  grades `2` and `3`.
* **The target** (`TowerProfile.isLawfulBelow_target`, `TowerProfile.isLawfulBelow_comp_embed3`,
  compiled): `f` on the left coatom and `e` raised to `⊤` above the cap through the point `4` is
  lawful below `(univ, 1)` on the amalgam when `f` is `⊥` on the common face.
* **The fill from the left coatom without a tie at the grade `1`**
  (`TowerProfile.readingFillPos_left_of_refine`, compiled): no tie at the grade `1`, no condition
  on the rows of the right coatom type, no relation among the new tops.

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

/-- **A labelling lawful below a pair in the profile layer is lawful below it on the amalgam**:
the old cells form a lower embedding along which the rows pull back, and a cell available at a
graded index of an old cell is old. -/
theorem isLawfulBelow_comp_embed3 {X : Finset (Fin 5) × ℕ} {Q : Fin (scheme I).card → Label.{u}}
    (hQ : (scheme I).rows.IsLawfulBelow X fun d ↦ Q d) :
    (I.tower 0).rows.IsLawfulBelow X fun d ↦ Q (embed3 I d.1) := by
  obtain ⟨ho, hl, ha⟩ := (CellScheme.Rows.isLawfulBelow_iff_forall (w := Q)).mp hQ
  have hmemX {d : Fin I.amalgam.card} (hd : d ∈ I.amalgam.toCellScheme.below X) :
      embed3 I d ∈ (scheme I).toCellScheme.below X := by
    rw [CellScheme.mem_below, gradedIndex_embed3]; exact hd
  refine (CellScheme.Rows.isLawfulBelow_iff_forall (w := fun d ↦ Q (embed3 I d))).mpr
    ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · have := ho _ (hmemX hd)
    rwa [← CellScheme.gradedIndex_snd, gradedIndex_embed3, CellScheme.gradedIndex_snd] at this
  · set φ : I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s) →
        (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex (embed3 I s)) :=
      fun d ↦ ⟨embed3 I d.1, by
        rw [CellScheme.mem_below, gradedIndex_embed3, gradedIndex_embed3]; exact d.2⟩ with hφ
    have hloc := (hl _ (hmemX hs)).reindex φ
    have e1 : ((fun d : (scheme I).toCellScheme.below
        ((scheme I).toCellScheme.gradedIndex (embed3 I s)) ↦ (scheme I).toCellScheme.grade d.1) ∘
        φ) = fun d ↦ I.amalgam.toCellScheme.grade d.1 := by
      funext d
      change (scheme I).toCellScheme.grade (embed3 I d.1) = _
      rw [← CellScheme.gradedIndex_snd, gradedIndex_embed3, CellScheme.gradedIndex_snd]
    have e2 : ((scheme I).rows.row (embed3 I s) ∘ φ) = I.amalgam.rows.row s := by
      funext d
      exact (Scheme.rowAt_of_mem (φ d).2).symm.trans ((rowAt_embed3 s d.1).trans
        (Scheme.rowAt_of_mem d.2))
    rw [e1, e2] at hloc
    exact hloc
  · obtain ⟨u, hu, hle⟩ := ha (embed3 I s) (embed3 I t) (hmemX ht)
      (by rw [scope_embed3, scope_embed3]; exact hst)
      ((congrArg Prod.snd (gradedIndex_embed3 (I := I) s)).trans
        (hg.trans (congrArg Prod.snd (gradedIndex_embed3 (I := I) t)).symm))
    have hus : (scheme I).toCellScheme.scope u ≠ univ := by
      rw [show (scheme I).toCellScheme.scope u = I.amalgam.toCellScheme.scope t from
        (congrArg Prod.fst hu).trans (scope_embed3 t)]
      exact I.scope_ne_univ t
    obtain ⟨u', rfl⟩ := mem_range_embed3 u hus
    exact ⟨u', (gradedIndex_embed3 u').symm.trans (hu.trans (gradedIndex_embed3 t)), hle⟩

/-- Raising above a cap keeps the cap. -/
theorem min_raise_self (h x : Label.{u}) : min (raise h x) h = min x h := by
  unfold raise
  split_ifs with hx
  · rw [min_top_left, min_eq_right hx]
  · rfl

/-- **The target on the amalgam**: `f` on the left coatom and `e` raised at `h` through the point
`4`, lawful below `(univ, 1)` when `f` is bottom on the common face. -/
theorem isLawfulBelow_target {e f : Fin (scheme I).card → Label.{u}} {h : Label.{u}}
    (hhb : ⊥ < h)
    (hfa : (I.tower 0).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f (embed3 I d.1))
    (hRa : (I.tower 0).rows.IsLawfulBelow (univ, 1) fun d ↦ raise h (e (embed3 I d.1)))
    (hfe : ∀ d : Fin I.amalgam.card, Fin.last 4 ∉ I.amalgam.toCellScheme.scope d →
      min (f (embed3 I d)) h = min (e (embed3 I d)) h)
    (hface : ∀ d : Fin I.amalgam.card, Fin.last 4 ∉ I.amalgam.toCellScheme.scope d →
      Fin.castSucc (Fin.last 3) ∉ I.amalgam.toCellScheme.scope d → f (embed3 I d) = ⊥) :
    (I.tower 0).rows.IsLawfulBelow (univ, 1) fun d ↦
      if Fin.last 4 ∈ I.amalgam.toCellScheme.scope d.1 then raise h (e (embed3 I d.1))
      else f (embed3 I d.1) := by
  classical
  set q : Fin I.amalgam.card → Label.{u} := fun d ↦
    if Fin.last 4 ∈ I.amalgam.toCellScheme.scope d then raise h (e (embed3 I d))
    else f (embed3 I d) with hqdef
  obtain ⟨hfo, hfl, hfav⟩ := (CellScheme.Rows.isLawfulBelow_iff_forall
    (w := fun d ↦ f (embed3 I d))).mp hfa
  obtain ⟨hRo, hRl, hRav⟩ := (CellScheme.Rows.isLawfulBelow_iff_forall
    (w := fun d ↦ raise h (e (embed3 I d)))).mp hRa
  have hC {d : Fin I.amalgam.card} (hd : I.amalgam.toCellScheme.grade d ≤ 1)
      (h4 : Fin.last 4 ∉ I.amalgam.toCellScheme.scope d) :
      d ∈ I.amalgam.toCellScheme.below (univ.erase (Fin.last 4), 4) :=
    (I.amalgam.toCellScheme.gradedIndex_le_iff).mpr
      ⟨fun x hx ↦ mem_erase.mpr ⟨fun h' ↦ h4 (h' ▸ hx), mem_univ _⟩, by omega⟩
  have hle (d : Fin I.amalgam.card) : q d ≤ raise h (e (embed3 I d)) := by
    by_cases h4 : Fin.last 4 ∈ I.amalgam.toCellScheme.scope d
    · simp only [hqdef, h4, ↓reduceIte, le_refl]
    · simp only [hqdef, h4, ↓reduceIte]
      have := hfe d h4
      rcases lt_or_ge (f (embed3 I d)) h with hl | hl
      · rw [min_eq_left hl.le] at this
        have hel : e (embed3 I d) < h := by
          by_contra hge; rw [min_eq_right (not_lt.mp hge)] at this; exact hl.ne this
        rw [min_eq_left hel.le] at this
        rw [this]
        unfold raise
        simp only [not_le.mpr hel, ↓reduceIte, le_refl]
      · have hge : h ≤ e (embed3 I d) := Label.le_of_min_eq_of_le' this.symm hl
        unfold raise
        simp only [hge, ↓reduceIte, le_top]
  refine (CellScheme.Rows.isLawfulBelow_iff_forall (w := q)).mpr
    ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · by_cases h4 : Fin.last 4 ∈ I.amalgam.toCellScheme.scope d
    · simp only [hqdef, h4, ↓reduceIte]; exact hRo d hd
    · simp only [hqdef, h4, ↓reduceIte]; exact hfo d (hC hd.2 h4)
  · by_cases h4 : Fin.last 4 ∈ I.amalgam.toCellScheme.scope s
    · -- through the point `4`: the raised `e`
      have hsD : I.amalgam.toCellScheme.scope s ⊆ univ.erase (Fin.castSucc (Fin.last 3)) :=
        (I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem s)
          (I.scope_ne_univ s)).resolve_left fun h' ↦
            Finset.notMem_erase (Fin.last 4) univ (h' h4)
      have heq : (fun d : I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s) ↦
          min (q d) (q s)) = fun d ↦ min (raise h (e (embed3 I d.1)))
            (raise h (e (embed3 I s))) := by
        funext d
        have hqd : q d = raise h (e (embed3 I d)) := by
          by_cases h4d : Fin.last 4 ∈ I.amalgam.toCellScheme.scope d
          · simp only [hqdef, h4d, ↓reduceIte]
          · have hsub : I.amalgam.toCellScheme.scope d ⊆ I.amalgam.toCellScheme.scope s :=
              ((I.amalgam.toCellScheme.gradedIndex_le_iff).mp d.2).1
            have h3 : Fin.castSucc (Fin.last 3) ∉ I.amalgam.toCellScheme.scope d := fun h' ↦
              Finset.notMem_erase _ univ (hsD (hsub h'))
            have hf0 := hface d h4d h3
            have he0 : e (embed3 I d) = ⊥ := by
              have := hfe d h4d
              rw [hf0, min_eq_left bot_le] at this
              exact (min_eq_bot.mp this.symm).resolve_right hhb.ne'
            simp only [hqdef, h4d, ↓reduceIte, hf0, he0, raise_bot hhb]
        rw [hqd]
        simp only [hqdef, h4, ↓reduceIte]
      convert hRl s hs using 1
      exact heq
    · have hsub (d : I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s)) :
          Fin.last 4 ∉ I.amalgam.toCellScheme.scope d := fun h' ↦
        h4 (((I.amalgam.toCellScheme.gradedIndex_le_iff).mp d.2).1 h')
      have heq : (fun d : I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s) ↦
          min (q d) (q s)) = fun d ↦ min (f (embed3 I d.1)) (f (embed3 I s)) := by
        funext d
        simp only [hqdef, hsub d, h4, ↓reduceIte]
      convert hfl s (hC hs.2 h4) using 1
      exact heq
  · by_cases h4 : Fin.last 4 ∈ I.amalgam.toCellScheme.scope t
    · obtain ⟨u, hu, hleu⟩ := hRav s t ht hst hg
      have h4u : Fin.last 4 ∈ I.amalgam.toCellScheme.scope u := by
        rw [show I.amalgam.toCellScheme.scope u = I.amalgam.toCellScheme.scope t from
          congrArg Prod.fst hu]
        exact h4
      refine ⟨u, hu, (hle s).trans ?_⟩
      simp only [hqdef, h4u, ↓reduceIte]
      exact hleu
    · have h4s : Fin.last 4 ∉ I.amalgam.toCellScheme.scope s := fun h' ↦ h4 (hst h')
      obtain ⟨u, hu, hleu⟩ := hfav s t (hC ht.2 h4) hst hg
      have h4u : Fin.last 4 ∉ I.amalgam.toCellScheme.scope u := by
        rw [show I.amalgam.toCellScheme.scope u = I.amalgam.toCellScheme.scope t from
          congrArg Prod.fst hu]
        exact h4
      refine ⟨u, hu, ?_⟩
      simp only [hqdef, h4s, h4u, ↓reduceIte]
      exact hleu

/-- **The fill at the short positive caps from the left coatom, from a refining server.**  Let `r`
be a cell of the left coatom and `X` a set of cells of grade `1` through the point
`4`.  Suppose that every labelling `f` lawful below the left coatom and not `⊥` at `r` is `⊥` on
the common face, takes one value at the cells of grade `2` not `⊥` (that at `t₂`), at most every
value not `⊥` at the cells of grade `1`, and is `⊥` at the cells of grade `3`.  Then
`ReadingFillPos I r X (Fin.last 4)`.  No tie at the grade `1` is asked (the cells of grade `1` of
the left coatom may carry any values), no condition on the rows of the right coatom type, and no
relation among the new tops: the fill at the grade `1` is `f` on the left coatom and `e` raised to
`⊤` above the cap through the point `4` (`TowerProfile.exists_one_of_target`, the refining server
built by the lexicographic raise), glued at the grades `2` and `3`
(`TowerProfile.exists_three_of_one`) and completed at the grade `4`
(`TowerProfile.exists_isLawfulBelow_four`). -/
theorem readingFillPos_left_of_refine {r : Fin (scheme I).card}
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    {X : Finset (Fin (scheme I).card)}
    (hX : ∀ x ∈ X, ∃ y, embed3 I y = x ∧ Fin.last 4 ∈ I.amalgam.toCellScheme.scope y ∧
      I.amalgam.toCellScheme.grade y = 1)
    {t₂ : Fin (scheme I).card}
    (ht₂ : t₂ ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hg₂ : (scheme I).toCellScheme.grade t₂ = 2)
    (H2 : ∀ f : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) (fun d ↦ f d) → f r ≠ ⊥ →
      ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        (scheme I).toCellScheme.grade d = 2 → f d ≠ ⊥ → f d = f t₂)
    (H12 : ∀ f : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) (fun d ↦ f d) → f r ≠ ⊥ →
      ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        (scheme I).toCellScheme.grade d = 1 → f d ≠ ⊥ → f t₂ ≤ f d)
    (H3 : ∀ f : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) (fun d ↦ f d) → f r ≠ ⊥ →
      ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        (scheme I).toCellScheme.grade d = 3 → f d = ⊥)
    (Hface : ∀ f : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) (fun d ↦ f d) → f r ≠ ⊥ →
      ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        Fin.castSucc (Fin.last 3) ∉ (scheme I).toCellScheme.scope d → f d = ⊥) :
    ReadingFillPos I r X (Fin.last 4) := by
  classical
  intro e he h hh _ hhb f hf hfe
  have hel : (scheme I).rows.IsLawful e :=
    (Scheme.mem_catalogue.mp (Scheme.readingMarks_subset _ _ he)).1
  have hfill_bot : ∃ g : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 4) (fun d ↦ g d) ∧
      (∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4), g d = f d) ∧
      ∀ d, min (g d) h = min (e d) h :=
    exists_fill_four (x := Fin.last 4) (y := Fin.castSucc (Fin.last 3)) (by simp) (by simp)
      (by decide) hf hel hh hfe
  by_cases hre : h ≤ e r
  swap
  · obtain ⟨g, hg, hgf, hga⟩ := hfill_bot
    exact ⟨g, hg, hgf, hga, reads_of_lt he (not_le.mp hre) hga⟩
  rcases X.eq_empty_or_nonempty with hXe | ⟨x₀, hx₀⟩
  · obtain ⟨g, hg, hgf, hga⟩ := hfill_bot
    exact ⟨g, hg, hgf, hga, fun x hx ↦ absurd (hXe ▸ hx) (Finset.notMem_empty x)⟩
  obtain ⟨z₀, hz₀, hPz₀, hgz₀⟩ := hX x₀ hx₀
  have hfr : h ≤ f r := Label.le_of_min_eq_of_le' (hfe _ hrC) hre
  have hfr0 : f r ≠ ⊥ := (hhb.trans_le hfr).ne'
  obtain ⟨hfo, -, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hf
  have hpos (d : Fin (scheme I).card) : 1 ≤ (scheme I).toCellScheme.grade d :=
    isWellFormed_scheme.isWellFormed.grade_pos d
  set V : Label.{u} := max h (f t₂) with hVdef
  have hV : IsSelfVisible 2 V :=
    (hh.mono (by omega)).max (by have := hfo t₂ ht₂; rwa [hg₂] at this)
  have hhV : h ≤ V := le_max_left _ _
  -- the conditions on the left coatom
  have hfV : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.grade d ≤ 2 → h ≤ f d → V ≤ f d := fun d hd hg2 hfd ↦ by
    have h0 : f d ≠ ⊥ := (hhb.trans_le hfd).ne'
    rcases (show (scheme I).toCellScheme.grade d = 1 ∨ (scheme I).toCellScheme.grade d = 2 by
      have := hpos d; omega) with h1 | h2
    · exact max_le hfd (H12 f hf hfr0 d hd h1 h0)
    · exact max_le hfd (H2 f hf hfr0 d hd h2 h0).ge
  have hfV' : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.grade d = 2 → h ≤ f d → f d ≤ V := fun d hd h2 hfd ↦ by
    rw [H2 f hf hfr0 d hd h2 (hhb.trans_le hfd).ne']
    exact le_max_right _ _
  have hf3 : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.grade d = 3 → f d ≤ h := fun d hd h3 ↦ by
    rw [H3 f hf hfr0 d hd h3]; exact bot_le
  -- the target on the amalgam
  have hRs : (scheme I).rows.IsLawfulBelow (univ, 1) fun d ↦ raise h (e d) :=
    (hel.isLawfulBelow _).map_of_apply_eq_bot (fun d ↦ d.2.2)
      (isWitness_raise (K := 1) (hh.mono (by omega)) hhb) fun _ h0 ↦ eq_bot_of_raise_eq_bot h0
  have hCem (d : Fin I.amalgam.card) (h4 : Fin.last 4 ∉ I.amalgam.toCellScheme.scope d) :
      embed3 I d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) := by
    rw [CellScheme.mem_below, gradedIndex_embed3]
    refine (I.amalgam.toCellScheme.gradedIndex_le_iff).mpr
      ⟨fun x hx ↦ mem_erase.mpr ⟨fun h' ↦ h4 (h' ▸ hx), mem_univ _⟩, ?_⟩
    have h1 := I.amalgam.isWellFormed.isWellFormed.grade_le_card d
    have h2 : #(I.amalgam.toCellScheme.scope d) ≤ 4 := by
      have := card_le_card (s := I.amalgam.toCellScheme.scope d)
        (t := univ.erase (Fin.last 4)) fun x hx ↦ mem_erase.mpr ⟨fun h' ↦ h4 (h' ▸ hx), mem_univ _⟩
      simpa using this
    exact h1.trans h2
  have hq := isLawfulBelow_target (I := I) (e := e) (f := f) hhb (isLawfulBelow_comp_embed3 hf)
    (isLawfulBelow_comp_embed3 (Q := fun d ↦ raise h (e d)) hRs) (fun d h4 ↦ hfe _ (hCem d h4))
    (fun d h4 h3 ↦ Hface f hf hfr0 _ (hCem d h4) (by rwa [scope_embed3]))
  set q : Fin I.amalgam.card → Label.{u} := fun d ↦
    if Fin.last 4 ∈ I.amalgam.toCellScheme.scope d then raise h (e (embed3 I d))
    else f (embed3 I d) with hqdef
  have hqe (d : Fin I.amalgam.card) (_ : I.amalgam.toCellScheme.grade d ≤ 1) :
      min (q d) h = min (e (embed3 I d)) h := by
    by_cases h4 : Fin.last 4 ∈ I.amalgam.toCellScheme.scope d
    · simp only [hqdef, h4, ↓reduceIte]; exact min_raise_self _ _
    · simp only [hqdef, h4, ↓reduceIte]; exact hfe _ (hCem d h4)
  have hqV (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 1) (hqd : h ≤ q d) :
      V ≤ q d := by
    by_cases h4 : Fin.last 4 ∈ I.amalgam.toCellScheme.scope d
    · simp only [hqdef, h4, ↓reduceIte] at hqd ⊢
      unfold raise at hqd ⊢
      split_ifs with hed
      · exact le_top
      · simp only [hed, ↓reduceIte] at hqd
    · simp only [hqdef, h4, ↓reduceIte] at hqd ⊢
      exact hfV _ (hCem d h4) (by
        rw [← CellScheme.gradedIndex_snd, gradedIndex_embed3, CellScheme.gradedIndex_snd]; omega)
        hqd
  have hez₀ : h ≤ e (embed3 I z₀) :=
    hre.trans (Scheme.le_of_mem_readingMarks he (hz₀ ▸ hx₀))
  obtain ⟨w₁, hw₁, hw₁q, hw₁e, hw₁V⟩ := exists_one_of_target (hel.isLawfulBelow _) hh hhb
    (hV.mono (by omega)) hhV hq hqe hqV hgz₀ hez₀
  have hmem1 {d : Fin (scheme I).card} (hd : (scheme I).toCellScheme.grade d = 1) :
      d ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 1) :=
    ⟨subset_univ _, hd.le⟩
  obtain ⟨w, hw, hwf, hwe, hww₁⟩ := exists_three_of_one (hel.isLawfulBelow _) hh hhb hf hfe hV hhV
    hfV hfV' hf3 hw₁
    (fun d hd hg1 ↦ by
      have hsd : (scheme I).toCellScheme.scope d ≠ univ := fun h' ↦ by
        have := ((scheme I).toCellScheme.gradedIndex_le_iff.mp ((CellScheme.mem_below _).mp hd)).1
        rw [h'] at this
        exact Finset.notMem_erase (Fin.last 4) univ (this (mem_univ _))
      obtain ⟨d', rfl⟩ := mem_range_embed3 d hsd
      have h4 : Fin.last 4 ∉ I.amalgam.toCellScheme.scope d' := fun h' ↦ by
        have := ((scheme I).toCellScheme.gradedIndex_le_iff.mp ((CellScheme.mem_below _).mp hd)).1
        rw [scope_embed3] at this
        exact Finset.notMem_erase (Fin.last 4) univ (this h')
      have hg' : I.amalgam.toCellScheme.grade d' ≤ 1 := by
        rw [← CellScheme.gradedIndex_snd, gradedIndex_embed3, CellScheme.gradedIndex_snd] at hg1
        omega
      rw [hw₁q d' hg']
      simp only [hqdef, h4, ↓reduceIte])
    (fun d hd hed ↦ Label.eq_of_min_eq_of_lt (hw₁e d (hmem1 hd)).symm hed)
    (fun d hd hed ↦ hw₁V d (hmem1 hd) hed)
  have hwU : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ w d :=
    (CellScheme.Rows.isLawfulBelow_congr fun d hd ↦ hwf d hd).mpr hf
  obtain ⟨g, hg, hgw, hga⟩ := exists_isLawfulBelow_four (x := Fin.last 4)
    (y := Fin.castSucc (Fin.last 3)) (by simp) (by simp) (by decide) hwU hw hel hh
    fun d hd ↦ hd.elim (fun hd ↦ by rw [hwf d hd]; exact hfe d hd) (hwe d)
  refine ⟨g, hg, fun d hd ↦ (hgw d (.inl hd)).trans (hwf d hd),
    fun d ↦ hga d (mem_below_univ_four d), fun x hx ↦ ?_⟩
  obtain ⟨y, rfl, hPy, hgy⟩ := hX x hx
  have hgy' : (scheme I).toCellScheme.grade (embed3 I y) = 1 := by
    rw [← CellScheme.gradedIndex_snd, gradedIndex_embed3, CellScheme.gradedIndex_snd, hgy]
  have hx3 : embed3 I y ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
    ⟨subset_univ _, show (scheme I).toCellScheme.grade (embed3 I y) ≤ 3 by rw [hgy']; omega⟩
  have hey : h ≤ e (embed3 I y) := hre.trans (Scheme.le_of_mem_readingMarks he hx)
  rw [hgw _ (.inr hx3), hww₁ _ hgy', hw₁q y hgy.le]
  simp only [hqdef, hPy, ↓reduceIte]
  unfold raise
  simp only [hey, ↓reduceIte, le_top]

end TowerProfile

end VaughtConjecture
