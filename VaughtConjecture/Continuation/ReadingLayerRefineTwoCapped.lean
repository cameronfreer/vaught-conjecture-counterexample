/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerRefineTwoRefute

/-!
# The refining server at the grade `2` for targets capped at grade `2`

Roadmap, Layer 3 ((R3) of the table of 3.4).

`TowerProfile.RefiningServerTwo'` is the statement `TowerProfile.RefiningServerTwo` with the
target `q` at most `V` at the cells of grade `2` at least `h` (so equal to `V` there).  It holds at
every seed on five points (`TowerProfile.refiningServerTwo'`, from
`TowerProfile.exists_two_of_capped`): the labelling is `q` on the layer at the grade `1`, `V` at
the cells of graded index `(univ, 2)` at least `h` in `e` and `e` at the others.  No condition on
the servers or on collisions is used: every cell at least `h` reads `V` capped at `V`, so the
servers at least `h` read through the raise of their witness, and availability from a cell of
grade `2` at least `h` asks only for a server at least `h`, which `e` provides.  The cap is what
fails in the refutation at `seedL` (`TowerProfile.not_refiningServerTwo_seedL`: `V = 4`, the
target `ω + 2` at a cell of grade `2`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme
open scoped Ordinal

namespace TowerProfile

open TopReadingApexExample StageType

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **The refining server at the grade `2` for a target capped at grade `2`.**  The statement of
`TowerProfile.RefiningServerTwo` at `e`, `h`, `V`, `q`, with the target `q` at most `V` at the
cells of grade `2` at least `h` (so `q = V` there).  The labelling: `q` on the layer at the grade
`1`, `V` at the cells of graded index `(univ, 2)` at least `h` in `e`, and `e` at the others.
Every cell at least `h` in `e` reads `V` capped at `V`, so each cell of graded index `(univ, 2)` at
least `h` reads its row through the raise of its witness capped at `V`; one below `h` reads as in
`e`; the old cells read as in the extension of `q` (`Scheme.exists_isLawfulBelow_fieldLayer`). -/
theorem exists_two_of_capped {e : Fin (scheme I).card → Label.{u}}
    (he : (scheme I).rows.IsLawfulBelow (univ, 2) fun d ↦ e d)
    {h : Label.{u}} (hh : IsSelfVisible 4 h) (hhb : ⊥ < h)
    {V : Label.{u}} (hV : IsSelfVisible 2 V) (hhV : h ≤ V)
    {q : Fin (I.tower 1).card → Label.{u}}
    (hq : (I.tower 1).rows.IsLawfulBelow (univ, 2) fun d ↦ q d.1)
    (hqe : ∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 → min (q d) h = min (e (oneCell I d)) h)
    (hqV : ∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 → h ≤ q d → V ≤ q d)
    (hqcap : ∀ d, (I.tower 1).toCellScheme.grade d = 2 → h ≤ q d → q d ≤ V) :
    ∃ w : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 2) (fun d ↦ w d) ∧
      (∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 → w (oneCell I d) = q d) ∧
      (∀ x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 2),
        min (w x) h = min (e x) h) ∧
      ∀ x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 2), h ≤ e x → V ≤ w x := by
  classical
  have hh0 : h ≠ ⊥ := hhb.ne'
  have hV0 : V ≠ ⊥ := (hhb.trans_le hhV).ne'
  have he₂ := isLawfulBelow_two_of_scheme he
  set E : Fin (I.tower 2).card → Label.{u} := fun y ↦ e (twoCell I y) with hEdef
  obtain ⟨hoE, hlE, haE⟩ := CellScheme.Rows.isLawfulBelow_iff_forall (w := E) |>.mp he₂
  -- the extension of `q`
  obtain ⟨r, hr, hrq⟩ := Scheme.exists_isLawfulBelow_fieldLayer (S := I.tower 1) (k := 2)
    (hS := I.not_univ_succ_le_tower 1) hq
  set R : Fin (I.tower 2).card → Label.{u} := fun y ↦ CellScheme.Rows.extendBot (univ, 2) r y
    with hRdef
  have hR : (I.tower 2).rows.IsLawfulBelow (univ, 2) fun y ↦ R y :=
    CellScheme.Rows.isLawfulBelow_extendBot.mpr hr
  obtain ⟨hoR, hlR, haR⟩ := CellScheme.Rows.isLawfulBelow_iff_forall (w := R) |>.mp hR
  -- the labelling of the layer at the grade `2`
  set w : Fin (I.tower 2).card → Label.{u} := fun y ↦
    if hy : (y : ℕ) < (I.tower 1).card then q ⟨y, hy⟩ else if h ≤ E y then V else E y with hwdef
  have hwold (x : Fin (I.tower 1).card) : w (Fin.castAdd _ x) = q x := by
    have hx : ((Fin.castAdd ((I.tower 1).catalogue 2).card x : Fin (I.tower 2).card) : ℕ) <
        (I.tower 1).card := x.2
    simp only [hwdef, hx, ↓reduceDIte]
    rfl
  have hwnew (j : Fin ((I.tower 1).catalogue 2).card) :
      w (Fin.natAdd _ j) = if h ≤ E (Fin.natAdd _ j) then V else E (Fin.natAdd _ j) := by
    have hx : ¬ ((Fin.natAdd (I.tower 1).card j : Fin (I.tower 2).card) : ℕ) <
        (I.tower 1).card := by simp
    simp only [hwdef, hx, ↓reduceDIte]
  have hcases (y : Fin (I.tower 2).card) : (∃ x : Fin (I.tower 1).card, Fin.castAdd _ x = y) ∨
      ∃ j : Fin ((I.tower 1).catalogue 2).card, Fin.natAdd _ j = y := by
    change Fin ((I.tower 1).card + ((I.tower 1).catalogue 2).card) at y
    induction y using Fin.addCases with
    | left d => exact .inl ⟨d, rfl⟩
    | right j => exact .inr ⟨j, rfl⟩
  have hgcast (x : Fin (I.tower 1).card) : (I.tower 2).toCellScheme.grade (Fin.castAdd _ x) =
      (I.tower 1).toCellScheme.grade x :=
    Scheme.appendFullCellsScheme_grade_castAdd (I.tower 1) 2 _ x
  have hgnew (j : Fin ((I.tower 1).catalogue 2).card) :
      (I.tower 2).toCellScheme.grade (Fin.natAdd _ j) = 2 :=
    Scheme.appendFullCellsScheme_grade_natAdd (I.tower 1) 2 _ j
  have hEold (x : Fin (I.tower 1).card) : E (Fin.castAdd _ x) = e (oneCell I x) := rfl
  -- `w` and `e` capped at `h`, and `V` where `e` is at least `h`
  have hwd (y : Fin (I.tower 2).card)
      (hy : y ∈ (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2)) :
      (h ≤ E y → V ≤ w y) ∧ (¬ h ≤ E y → w y = E y) := by
    rcases hcases y with ⟨x, rfl⟩ | ⟨j, rfl⟩
    · have hx : (I.tower 1).toCellScheme.grade x ≤ 2 := (hgcast x).symm.trans_le hy.2
      rw [hwold, hEold]
      refine ⟨fun hex ↦ hqV x hx (Label.le_of_min_eq_of_le' (hqe x hx) hex), fun hex ↦ ?_⟩
      exact Label.eq_of_min_eq_of_lt (hqe x hx).symm (not_le.mp hex)
    · rw [hwnew]
      exact ⟨fun hex ↦ by rw [ite_eq_left hex], fun hex ↦ by rw [ite_eq_right hex]⟩
  have hmin (y : Fin (I.tower 2).card)
      (hy : y ∈ (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2)) :
      min (w y) h = min (E y) h := by
    by_cases hex : h ≤ E y
    · rw [min_eq_right ((hwd y hy).1 hex |>.trans' hhV), min_eq_right hex]
    · rw [(hwd y hy).2 hex]
  -- the old cells: below their graded index every cell is old, where `w` is `R`
  have hnot (x : Fin (I.tower 1).card) :
      ¬ ((univ : Finset (Fin 5)), 2) ≤ (I.tower 2).toCellScheme.gradedIndex (Fin.castAdd _ x) := by
    intro hle
    have h1 : (univ : Finset (Fin 5)) ⊆ (I.tower 2).toCellScheme.scope (Fin.castAdd _ x) := hle.1
    have h2 : 2 ≤ (I.tower 2).toCellScheme.grade (Fin.castAdd _ x) := hle.2
    rw [hgcast] at h2
    rcases I.tower_grade_le_or 1 x with hg | hs
    · omega
    · exact hs (univ_subset_iff.mp (h1.trans_eq
        (Scheme.appendFullCellsScheme_scope_castAdd (I.tower 1) 2 _ x)))
  have hwR (y : Fin (I.tower 2).card) (hyc : (y : ℕ) < (I.tower 1).card)
      (hy : y ∈ (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2)) : w y = R y := by
    obtain ⟨x, rfl⟩ : ∃ x : Fin (I.tower 1).card, Fin.castAdd _ x = y := ⟨⟨y, hyc⟩, rfl⟩
    have hx : (I.tower 1).toCellScheme.grade x ≤ 2 := (hgcast x).symm.trans_le hy.2
    rw [hwold, hRdef]
    simp only
    rw [CellScheme.Rows.extendBot_of_mem r hy]
    exact (hrq x hx).symm
  have hold_below (x : Fin (I.tower 1).card) {d : Fin (I.tower 2).card}
      (hd : d ∈ (I.tower 2).toCellScheme.below
        ((I.tower 2).toCellScheme.gradedIndex (Fin.castAdd _ x))) :
      (d : ℕ) < (I.tower 1).card :=
    Scheme.lt_card_of_mem_below (S := I.tower 1) (k := 2) (M := ((I.tower 1).catalogue 2).card)
      (hnot x) hd
  -- the witness at a cell of graded index `(univ, 2)` at least `h`
  have hσ (j : Fin ((I.tower 1).catalogue 2).card) (hj : h ≤ E (Fin.natAdd _ j)) :
      ∃ σ, IsWitness (stepSuppressor 2) σ ∧
        ∀ d : (I.tower 2).toCellScheme.below
          ((I.tower 2).toCellScheme.gradedIndex (Fin.natAdd _ j)),
          σ ((I.tower 2).rows.row (Fin.natAdd _ j) d) = min (raise h (min (E d) h)) V := by
    have hu : (I.tower 2).toCellScheme.gradedIndex (Fin.natAdd _ j) =
        ((univ : Finset (Fin 5)), 2) :=
      Scheme.appendFullCellsScheme_gradedIndex_natAdd (I.tower 1) 2 _ j
    obtain ⟨τ, hτ, -, hτE⟩ := CellScheme.Rows.exists_isWitness_rowBelow
      (R := (I.tower 2).rows) hu he₂ (c := h) (hh.mono (by omega)) hj
    refine ⟨(fun t ↦ min (raise h t) V) ∘ τ,
      hτ.comp_of_bot_reflecting ((isWitness_raise (K := 2) (hh.mono (by omega)) hhb).min_const hV)
        fun t ht ↦ eq_bot_of_raise_eq_bot ((min_eq_bot.mp ht).resolve_right hV0), fun d ↦ ?_⟩
    have := hτE ⟨d.1, d.2.trans hu.le⟩
    simp only [Function.comp]
    rw [← this]
    rfl
  -- lawfulness on the layer at the grade `2`
  have hlaw : (I.tower 2).rows.IsLawfulBelow (univ, 2) fun y ↦ w y := by
    refine CellScheme.Rows.isLawfulBelow_iff_forall.mpr ⟨fun y hy ↦ ?_, fun s hs ↦ ?_,
      fun s t ht hst hg ↦ ?_⟩
    · -- orderly
      rcases hcases y with ⟨x, rfl⟩ | ⟨j, rfl⟩
      · rw [hwR _ x.2 hy]
        exact hoR _ hy
      · rw [hwnew, hgnew]
        split_ifs
        · exact hV
        · simpa [hgnew] using hoE _ hy
    · -- locality
      rcases hcases s with ⟨x, rfl⟩ | ⟨j, rfl⟩
      · have heq : (fun d : (I.tower 2).toCellScheme.below
            ((I.tower 2).toCellScheme.gradedIndex (Fin.castAdd _ x)) ↦
              min (w d.1) (w (Fin.castAdd _ x))) =
            fun d : (I.tower 2).toCellScheme.below
              ((I.tower 2).toCellScheme.gradedIndex (Fin.castAdd _ x)) ↦
              min (R d.1) (R (Fin.castAdd _ x)) := funext fun d ↦ by
          rw [hwR _ (hold_below x d.2) ((CellScheme.mem_below _).mpr (le_trans d.2 hs)),
            hwR _ x.2 hs]
        rw [heq]
        exact hlR _ hs
      · by_cases hj : h ≤ E (Fin.natAdd _ j)
        · obtain ⟨σ, hσw, hσr⟩ := hσ j hj
          refine ⟨stepSuppressor 2, σ, hσw, fun d ↦ ?_⟩
          have hd : (d : Fin (I.tower 2).card) ∈
              (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2) :=
            (CellScheme.mem_below _).mpr (le_trans d.2 hs)
          have hg2 : (I.tower 2).toCellScheme.grade (d : Fin (I.tower 2).card) ≤ 2 := hd.2
          change min (w d.1) (w (Fin.natAdd _ j)) =
            min (σ ((I.tower 2).rows.row (Fin.natAdd _ j) d))
              (stepSuppressor 2 ((I.tower 2).toCellScheme.grade d.1))
          rw [hσr, stepSuppressor_of_le hg2, min_top_right, hwnew, ite_eq_left hj]
          by_cases hed : h ≤ E d
          · rw [min_eq_right hed, show raise h h = ⊤ from ite_eq_left le_rfl, min_top_left,
              min_eq_right ((hwd _ hd).1 hed)]
          · have hlt := not_le.mp hed
            rw [(hwd _ hd).2 hed, min_eq_left hlt.le,
              show raise h (E d) = E d from ite_eq_right hed, min_eq_left (hlt.le.trans hhV)]
        · have heq : (fun d : (I.tower 2).toCellScheme.below
              ((I.tower 2).toCellScheme.gradedIndex (Fin.natAdd _ j)) ↦
                min (w d.1) (w (Fin.natAdd _ j))) =
              fun d : (I.tower 2).toCellScheme.below
                ((I.tower 2).toCellScheme.gradedIndex (Fin.natAdd _ j)) ↦
                min (E d.1) (E (Fin.natAdd _ j)) := funext fun d ↦ by
            have hd : (d : Fin (I.tower 2).card) ∈
                (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2) :=
              (CellScheme.mem_below _).mpr (le_trans d.2 hs)
            have hlt := not_le.mp hj
            rw [hwnew, ite_eq_right hj]
            by_cases hed : h ≤ E d
            · rw [min_eq_right (hlt.le.trans (hhV.trans ((hwd _ hd).1 hed))),
                min_eq_right (hlt.le.trans hed)]
            · rw [(hwd _ hd).2 hed]
          rw [heq]
          exact hlE _ hs
    · -- availability
      rcases hcases t with ⟨x, rfl⟩ | ⟨j, rfl⟩
      · have hsb : s ∈ (I.tower 2).toCellScheme.below
            ((I.tower 2).toCellScheme.gradedIndex (Fin.castAdd _ x)) :=
          (CellScheme.gradedIndex_le_iff _).mpr ⟨hst, hg.le⟩
        obtain ⟨u, hu, hle⟩ := haR s _ ht hst hg
        have hub : u ∈ (I.tower 2).toCellScheme.below
            ((I.tower 2).toCellScheme.gradedIndex (Fin.castAdd _ x)) := hu.le
        refine ⟨u, hu, ?_⟩
        rw [hwR _ (hold_below x hsb) ((CellScheme.mem_below _).mpr (le_trans hsb ht)),
          hwR _ (hold_below x hub) ((CellScheme.mem_below _).mpr (le_trans hub ht))]
        exact hle
      · have hsb : s ∈ (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2) :=
          (CellScheme.mem_below _).mpr
            (le_trans ((CellScheme.gradedIndex_le_iff _).mpr ⟨hst, hg.le⟩) ht)
        rcases hcases s with ⟨x, rfl⟩ | ⟨j', rfl⟩
        · obtain ⟨u, hu, hle⟩ := haE _ _ ht hst hg
          have hu' : (I.tower 2).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), 2) :=
            hu.trans (Scheme.appendFullCellsScheme_gradedIndex_natAdd (I.tower 1) 2 _ j)
          have hub : u ∈ (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2) := hu'.le
          refine ⟨u, hu, ?_⟩
          by_cases hex : h ≤ E (Fin.castAdd _ x)
          · obtain ⟨j₀, rfl⟩ := Scheme.exists_natAdd_eq (hS := I.not_univ_succ_le_tower 1) hu'
            have hx2 : (I.tower 1).toCellScheme.grade x = 2 := (hgcast x).symm.trans
              (hg.trans (hgnew j))
            rw [hwold, hwnew, ite_eq_left (hex.trans hle)]
            have hqx : h ≤ q x := Label.le_of_min_eq_of_le' (hqe x hx2.le) hex
            exact hqcap x hx2 hqx
          · rw [(hwd _ hsb).2 hex]
            have := hmin u hub
            calc E (Fin.castAdd _ x) = min (E (Fin.castAdd _ x)) h :=
                  (min_eq_left (not_le.mp hex).le).symm
              _ ≤ min (E u) h := min_le_min_right _ hle
              _ = min (w u) h := this.symm
              _ ≤ w u := min_le_left _ _
        · exact ⟨Fin.natAdd _ j',
            (Scheme.appendFullCellsScheme_gradedIndex_natAdd (I.tower 1) 2 _ j').trans
              (Scheme.appendFullCellsScheme_gradedIndex_natAdd (I.tower 1) 2 _ j).symm, le_rfl⟩
  -- the labelling of the profile layer
  set W : Fin (scheme I).card → Label.{u} := fun x ↦
    if hx : (x : ℕ) < (I.tower 2).card then w ⟨x, hx⟩ else ⊥ with hWdef
  have hWtwo (y : Fin (I.tower 2).card) : W (twoCell I y) = w y := by
    have hy : ((twoCell I y : Fin (scheme I).card) : ℕ) < (I.tower 2).card := y.2
    simp only [hWdef, hy, ↓reduceDIte]
    rfl
  have hmemtwo {x : Fin (scheme I).card}
      (hx : x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 2)) :
      ∃ y : Fin (I.tower 2).card, twoCell I y = x ∧
        y ∈ (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2) := by
    obtain ⟨y, rfl⟩ := exists_twoCell_eq hx
    refine ⟨y, rfl, ?_⟩
    rw [CellScheme.mem_below, ← gradedIndex_twoCell]
    exact hx
  refine ⟨W, isLawfulBelow_scheme_of_two ?_, fun d hd ↦ ?_, fun x hx ↦ ?_, fun x hx hex ↦ ?_⟩
  · have heq : (fun d : (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2) ↦
        W (twoCell I d)) =
        fun d : (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2) ↦ w d.1 :=
      funext fun d ↦ hWtwo d
    rw [heq]
    exact hlaw
  · exact (hWtwo (Fin.castAdd _ d)).trans (hwold d)
  · obtain ⟨y, rfl, hy⟩ := hmemtwo hx
    rw [hWtwo]
    exact hmin y hy
  · obtain ⟨y, rfl, hy⟩ := hmemtwo hx
    rw [hWtwo]
    exact (hwd y hy).1 hex

/-- **"A refining server exists at the grade `2`" for capped targets**: the statement of
`TowerProfile.RefiningServerTwo` with the target `q` at most `V` at the cells of grade `2` at
least `h` (`hqcap`).  `TowerProfile.RefiningServerTwo` itself is refuted at `seedL`
(`TowerProfile.not_refiningServerTwo_seedL`), where the target reads a cell of grade `2` above `V`
and two cells of grade `1` apart that every server at least `h` codes alike. -/
def RefiningServerTwo' (I : Seed.{u} α 3) : Prop :=
  ∀ e : Fin (scheme I).card → Label.{u}, (scheme I).rows.IsLawfulBelow (univ, 2) (fun d ↦ e d) →
    ∀ h : Label.{u}, IsSelfVisible 4 h → ⊥ < h → ∀ V : Label.{u}, IsSelfVisible 2 V → h ≤ V →
    ∀ q : Fin (I.tower 1).card → Label.{u},
      (I.tower 1).rows.IsLawfulBelow (univ, 2) (fun d ↦ q d.1) →
      (∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 → min (q d) h = min (e (oneCell I d)) h) →
      (∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 → h ≤ q d → V ≤ q d) →
      (∀ d, (I.tower 1).toCellScheme.grade d = 2 → h ≤ q d → q d ≤ V) →
      (∃ z₀, (I.tower 1).toCellScheme.grade z₀ = 2 ∧ h ≤ e (oneCell I z₀)) →
      ∃ w : Fin (scheme I).card → Label.{u},
        (scheme I).rows.IsLawfulBelow (univ, 2) (fun d ↦ w d) ∧
        (∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 → w (oneCell I d) = q d) ∧
        (∀ x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 2),
          min (w x) h = min (e x) h) ∧
        ∀ x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 2), h ≤ e x → V ≤ w x

/-- **A refining server exists at the grade `2` for capped targets**, at every seed on five points
(`TowerProfile.exists_two_of_capped`). -/
theorem refiningServerTwo' (I : Seed.{u} α 3) : RefiningServerTwo' I :=
  fun _ he _ hh hhb _ hV hhV _ hq hqe hqV hqcap _ ↦
    exists_two_of_capped he hh hhb hV hhV hq hqe hqV hqcap

/-- The uncapped statement gives the capped one. -/
theorem RefiningServerTwo.capped (hI : RefiningServerTwo I) : RefiningServerTwo' I :=
  fun e he h hh hhb V hV hhV q hq hqe hqV _ hz₀ ↦ hI e he h hh hhb V hV hhV q hq hqe hqV hz₀

end TowerProfile

end VaughtConjecture
