/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerTies

/-!
# Servers in a field layer

Roadmap, Layer 3 ((R3) of the table of 3.4).

The band case of the fill at the short caps from the left coatom
(`TowerProfile.not_exists_fill_of_noServer`) needs a **server**: a cell of full scope at the grade
of the new top `x`, at least the cap in the mark `e`, whose row reads the band cell `y` strictly
below `x`.  This file shows that servers always exist at the seeds whose right coatom type is
`rightType` (`seedThree` among them), so that obstruction never applies there.

* **Servers in a field layer** (`Scheme.exists_server_fieldLayer`, compiled in this repository
  (theorem named)): in the field layer at a grade `k`, a labelling lawful below `(univ, k)` not `⊥`
  at an old cell `x` of grade `k` has a new cell at least its value at `x` whose entry reads
  every cell of a set `Q` strictly below `x`, provided every entry not `⊥` at `x` reading `x` at
  most as some cell of `Q` has a **raise**: an entry reading every cell of `Q` strictly below `x`
  that agrees with it capped at its value at `x`.  The cell serving `x` (availability) reads the
  cell of the raise at least as `x` (their agreement height is at least that value, a grid point,
  `Scheme.mem_fieldGrid_of_mem_catalogue`), so locality puts the raise at least at `x`.
* **The raise** (`Scheme.exists_raise_entry`, compiled): for a property `P` of cells closed upward
  under the scopes, holding at grade `k` only, whose cells of grade `k` read the cells with `P`
  below them as themselves and the others as `⊥`, the orbit code of an entry raised to `⊤` at its
  cells with `P` at least its value at `x` is a raise.
* **At `rightType`** (`TowerProfile.rowP_right`, `TowerProfile.exists_server_of_rightType`,
  `TowerProfile.exists_server_above_cap_of_rightType`, compiled): with `P` the cells through the
  point `4` (the right coatom off the common face), the live cells of grade `1` of `rightType` read
  the live cells of grade `1` below them at `v1` and the others as `⊥`
  (`TowerProfile.rowAt_S_live`).  So at every seed whose right coatom type is `rightType`, for every
  labelling lawful below `(univ, 4)` at least a positive cap `h` at a cell `x` of grade `1` through
  the point `4`, a server exists, one cell for every cell of grade at most `1` off that point.

**Verdict (step A)**: every reading mark at `seedThree` has a server at each band cell of grade
`1`; the no-server obstruction does not refute the fill there.  Step B (the union with a server,
giving the fill) is not done here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label
open Ordinal hiding univ

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {k : ℕ}

/-- A value of the code grid self-visible at `k` lies in the grid. -/
theorem mem_grid_of_mem_codeGrid {B B' : ℕ} (hBB : B ≤ B') {x : Label.{u}}
    (hx : x ∈ codeGrid k B) (hv : IsSelfVisible k x) : x ∈ grid k B' := by
  rcases mem_codeGrid.mp hx with rfl | ⟨b, hb, f, hf, rfl⟩
  · exact bot_mem_grid _ _
  · have h := isSelfVisible_coe.mp hv
    have hmod : (ω * (b : Ordinal.{u}) + (f : Ordinal.{u})) % ω = f := by
      rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (Ordinal.natCast_lt_omega0 f)]
    rw [hmod] at h
    have hfk : f = k := le_antisymm hf (by exact_mod_cast h)
    subst hfk
    exact mem_grid.mpr (.inr ⟨b, hb.trans hBB, rfl⟩)

/-- A catalogue entry at a cell of grade `k` lies in the field grid. -/
theorem mem_fieldGrid_of_mem_catalogue {b : Fin S.card → Label.{u}} (hb : b ∈ S.catalogue k)
    {x : Fin S.card} (hgx : S.toCellScheme.grade x = k) : b x ∈ S.fieldGrid k :=
  mem_grid_of_mem_codeGrid (by omega) (mem_codeGrid_of_mem_catalogue hb x)
    (hgx ▸ (mem_catalogue.mp hb).1.orderly x)

variable {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- **Servers in a field layer.**  Let `w` be lawful below `(univ, k)` in the field layer at the
grade `k`, `x` an old cell of grade `k` not `⊥` in `w`, and `Q` a set of old cells.  Suppose
every catalogue entry `b` that is not `⊥` at `x` and reads `x` at most as some cell of `Q` has a
*raise*: an entry reading every cell of `Q` strictly below `x` that agrees with `b` capped at
`b x`.  Then some new cell at least `w x` reads every cell of `Q` strictly below `x`: the cell
serving `x` (availability), or the cell of the raise of its entry, read by the serving cell at
least as `x` (the agreement height of the two entries is at least `b x`) and so at least `w x`
(locality). -/
theorem exists_server_fieldLayer {w : Fin (S.fieldLayer k hS).card → Label.{u}}
    (hw : (S.fieldLayer k hS).rows.IsLawfulBelow (univ, k) fun d ↦ w d) {x : Fin S.card}
    {Q : Fin S.card → Prop} (hgx : S.toCellScheme.grade x = k)
    (hx0 : w (Fin.castAdd _ x) ≠ ⊥)
    (hraise : ∀ b ∈ S.catalogue k, b x ≠ ⊥ → (∃ y, Q y ∧ b x ≤ b y) → ∃ b' ∈ S.catalogue k,
      (∀ y, Q y → b' y < b' x) ∧ ∀ d, min (b' d) (b x) = min (b d) (b x)) :
    ∃ i, w (Fin.castAdd _ x) ≤ w (Fin.natAdd _ i) ∧
      ∀ y, Q y → S.catalogueEntry k i y < S.catalogueEntry k i x := by
  obtain ⟨-, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hw
  obtain ⟨i₀, -⟩ := exists_catalogueEntry_eq (orbitCode_splice_bot_mem_catalogue (S := S) (k := k)
    (p := fun _ ↦ ⊥) (CellScheme.Rows.isLawfulBelow_const_bot _))
  have hxb : Fin.castAdd (S.catalogue k).card x ∈
      (S.fieldLayer k hS).toCellScheme.below (univ, k) :=
    castAdd_mem_below (hS := hS) hgx.le
  obtain ⟨u, hu, hxu⟩ := havail (Fin.castAdd _ x) (Fin.natAdd _ i₀) (natAdd_mem_below i₀)
    (by rw [appendFullCellsScheme_scope_natAdd]; exact subset_univ _)
    (by rw [appendFullCellsScheme_grade_castAdd, appendFullCellsScheme_grade_natAdd, hgx])
  have hu' : (S.fieldLayer k hS).toCellScheme.gradedIndex u = (univ, k) :=
    hu.trans (appendFullCellsScheme_gradedIndex_natAdd _ _ _ _)
  obtain ⟨i, rfl⟩ := exists_natAdd_eq (hS := hS) hu'
  have hub : Fin.natAdd S.card i ∈ (S.fieldLayer k hS).toCellScheme.below (univ, k) :=
    natAdd_mem_below i
  set b := S.catalogueEntry k i with hbdef
  by_cases hlt : ∀ y, Q y → b y < b x
  · exact ⟨i, hxu, hlt⟩
  have hle : ∃ y, Q y ∧ b x ≤ b y := by
    push Not at hlt
    exact hlt
  have hxr : Fin.castAdd (S.catalogue k).card x ∈ (S.fieldLayer k hS).toCellScheme.below
      ((S.fieldLayer k hS).toCellScheme.gradedIndex (Fin.natAdd S.card i)) := by
    rw [hu']; exact hxb
  -- the entry is not `⊥` at `x`
  have hbx : b x ≠ ⊥ := by
    intro hb
    have h := (hloc _ hub).eq_bot (d := ⟨_, hxr⟩) (by
      rw [fieldLayer_row_natAdd, fieldRow_castAdd]; exact hb)
    change min (w (Fin.castAdd _ x)) (w (Fin.natAdd _ i)) = ⊥ at h
    rw [min_eq_left hxu] at h
    exact hx0 h
  obtain ⟨b', hb', hlt', hag⟩ := hraise b (catalogueEntry_mem i) hbx hle
  obtain ⟨j, hj⟩ := exists_catalogueEntry_eq hb'
  have hjr : Fin.natAdd S.card j ∈ (S.fieldLayer k hS).toCellScheme.below
      ((S.fieldLayer k hS).toCellScheme.gradedIndex (Fin.natAdd S.card i)) := by
    rw [hu']; exact natAdd_mem_below j
  have hheight : b x ≤ agreementHeight (S.fieldGrid k) b b' :=
    le_agreementHeight (mem_fieldGrid_of_mem_catalogue (catalogueEntry_mem i) hgx)
      fun d ↦ (hag d).symm
  have h := (hloc _ hub).le_of_le (d := ⟨_, hxr⟩) (d' := ⟨_, hjr⟩)
    (by
      rw [fieldLayer_row_natAdd, fieldLayer_row_natAdd, fieldRow_castAdd, fieldRow_natAdd, hj]
      exact hheight)
    (by
      change (S.fieldLayer k hS).toCellScheme.grade (Fin.natAdd _ j) ≤
        (S.fieldLayer k hS).toCellScheme.grade (Fin.castAdd _ x)
      rw [appendFullCellsScheme_grade_castAdd, appendFullCellsScheme_grade_natAdd, hgx])
  change min (w (Fin.castAdd _ x)) (w (Fin.natAdd _ i)) ≤
    min (w (Fin.natAdd _ j)) (w (Fin.natAdd _ i)) at h
  rw [min_eq_left hxu] at h
  refine ⟨j, h.trans (min_le_left _ _), ?_⟩
  rw [hj]
  exact hlt'

/-- **A raise of a catalogue entry.**  Let `P` be a property of the cells of `S` closed upward
under the scopes, holding only at cells of grade `k` among those of grade at most `k`, such that
the row of a cell of grade `k` with `P` reads the cells with `P` below it as it reads itself and
the others as `⊥`.  For every catalogue entry `b` not `⊥` at a cell `x` of grade `k` with `P`,
the orbit code of `b` raised to `⊤` at the cells with `P` at least `b x` is a catalogue entry that
reads every cell without `P` strictly below `x` and agrees with `b` capped at `b x`. -/
theorem exists_raise_entry {P : Fin S.card → Prop}
    (hPscope : ∀ s t, S.toCellScheme.scope s ⊆ S.toCellScheme.scope t → P s → P t)
    (hPk : ∀ d, P d → S.toCellScheme.grade d ≤ k → S.toCellScheme.grade d = k)
    (hrowP : ∀ s, P s → S.toCellScheme.grade s = k →
      ∀ d (hd : d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex s)),
        (P d → S.rows.row s ⟨d, hd⟩ = S.rows.row s ⟨s, S.toCellScheme.mem_below_gradedIndex s⟩) ∧
        (¬ P d → S.rows.row s ⟨d, hd⟩ = ⊥))
    {b : Fin S.card → Label.{u}} (hb : b ∈ S.catalogue k) {x : Fin S.card} (hPx : P x)
    (hgx : S.toCellScheme.grade x = k) (hx0 : b x ≠ ⊥) :
    ∃ b' ∈ S.catalogue k, (∀ y, ¬ P y → b' y < b' x) ∧
      ∀ d, min (b' d) (b x) = min (b d) (b x) := by
  classical
  obtain ⟨hbl, hbk, hbo⟩ := mem_catalogue.mp hb
  set W : Fin S.card → Label.{u} := fun d ↦ if P d ∧ b x ≤ b d then ⊤ else b d with hWdef
  have hWge (d : Fin S.card) : b d ≤ W d := by
    rw [hWdef]; dsimp only; split_ifs
    exacts [le_top, le_rfl]
  -- below a raised cell
  have hbelow {s : Fin S.card} (hPs : P s) (hbs : b x ≤ b s) (hgs : S.toCellScheme.grade s = k)
      (d : Fin S.card) (hd : d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex s)) :
      (P d → b s ≤ b d) ∧ (¬ P d → b d = ⊥) := by
    have hs0 : b s ≠ ⊥ := fun h ↦ hx0 (le_bot_iff.mp (h ▸ hbs))
    refine ⟨fun hPd ↦ ?_, fun hPd ↦ ?_⟩
    · have h := (hbl.locality s).le_of_le (d := ⟨s, S.toCellScheme.mem_below_gradedIndex s⟩)
        (d' := ⟨d, hd⟩) ((hrowP s hPs hgs d hd).1 hPd).ge hd.2
      change min (b s) (b s) ≤ min (b d) (b s) at h
      rw [min_self] at h
      exact h.trans (min_le_left _ _)
    · have h := (hbl.locality s).eq_bot (d := ⟨d, hd⟩) ((hrowP s hPs hgs d hd).2 hPd)
      change min (b d) (b s) = ⊥ at h
      exact (min_eq_bot.mp h).resolve_right hs0
  have hW : S.rows.IsLawfulBelow (univ, k) fun d ↦ W d := by
    refine CellScheme.Rows.isLawfulBelow_iff_forall.mpr ⟨fun d _ ↦ ?_, fun s hs ↦ ?_,
      fun s t ht hst hg ↦ ?_⟩
    · rw [hWdef]; dsimp only; split_ifs
      exacts [isSelfVisible_top _, hbl.orderly d]
    · by_cases hUs : P s ∧ b x ≤ b s
      · have hgs : S.toCellScheme.grade s = k := hPk s hUs.1 hs.2
        have hss : S.rows.row s ⟨s, S.toCellScheme.mem_below_gradedIndex s⟩ ≠ ⊥ := fun h ↦ by
          have h' := (hbl.locality s).eq_bot (d := ⟨s, S.toCellScheme.mem_below_gradedIndex s⟩) h
          change min (b s) (b s) = ⊥ at h'
          rw [min_self] at h'
          exact hx0 (le_bot_iff.mp (h' ▸ hUs.2))
        refine transformsTo_of_eq_bot_iff _ (K := k) (fun d ↦ d.2.2.trans hgs.le)
          (isSelfVisible_top k) _ _ fun d ↦ ?_
        have hWs : W s = ⊤ := ite_eq_left hUs
        rw [hWs, min_top_right]
        obtain ⟨h1, h2⟩ := hbelow hUs.1 hUs.2 hgs d d.2
        by_cases hPd : P d
        · rw [ite_eq_right (by rw [(hrowP s hUs.1 hgs d d.2).1 hPd]; exact hss)]
          exact ite_eq_left ⟨hPd, hUs.2.trans (h1 hPd)⟩
        · rw [ite_eq_left ((hrowP s hUs.1 hgs d d.2).2 hPd)]
          rw [hWdef]; dsimp only
          rw [ite_eq_right fun h ↦ hPd h.1]
          exact h2 hPd
      · have hWs : W s = b s := ite_eq_right hUs
        have heq : (fun d : S.toCellScheme.below (S.toCellScheme.gradedIndex s) ↦
            min (W d) (W s)) =
            fun d : S.toCellScheme.below (S.toCellScheme.gradedIndex s) ↦ min (b d) (b s) :=
          funext fun d ↦ by
          rw [hWs]
          by_cases hUd : P (d : Fin S.card) ∧ b x ≤ b d
          · have hPs : P s := hPscope _ _ d.2.1 hUd.1
            have hgd : S.toCellScheme.grade d = k := hPk _ hUd.1 (d.2.2.trans hs.2)
            have hgs : S.toCellScheme.grade s = k := le_antisymm hs.2 (hgd ▸ d.2.2)
            have hbs : b s < b x := not_le.mp fun h ↦ hUs ⟨hPs, h⟩
            change min (W d) (b s) = min (b d) (b s)
            rw [show W d = ⊤ from ite_eq_left hUd, min_top_left,
              min_eq_right (hbs.le.trans hUd.2)]
          · rw [show W d = b d from ite_eq_right hUd]
        rw [heq]
        exact hbl.locality s
    · obtain ⟨u, hu, hsu⟩ := hbl.availability s t hst hg
      refine ⟨u, hu, ?_⟩
      by_cases hUs : P s ∧ b x ≤ b s
      · have hPu : P u := hPscope _ _ (hst.trans (congrArg Prod.fst hu).ge) hUs.1
        rw [show W u = ⊤ from ite_eq_left ⟨hPu, hUs.2.trans hsu⟩]
        exact le_top
      · rw [show W s = b s from ite_eq_right hUs]
        exact hsu.trans (hWge u)
  have hsplice : S.toCellScheme.splice k (fun _ ↦ ⊥) W = W := by
    funext d
    by_cases hd : S.toCellScheme.grade d ≤ k
    · exact CellScheme.splice_of_le hd
    · rw [CellScheme.splice_of_lt (not_le.mp hd)]
      have hbd := hbk d (not_le.mp hd)
      rw [hWdef]; dsimp only
      rw [ite_eq_right fun h ↦ hx0 (le_bot_iff.mp (hbd ▸ h.2)), hbd]
  have hmem := orbitCode_splice_bot_mem_catalogue (S := S) (k := k) hW
  rw [hsplice] at hmem
  have hWx : W x = ⊤ := ite_eq_left ⟨hPx, le_rfl⟩
  refine ⟨orbitCode k W, hmem, fun y hPy ↦ ?_, fun d ↦ ?_⟩
  · have hWy : W y = b y := ite_eq_right fun h ↦ hPy h.1
    by_contra hge
    have hge' := not_lt.mp hge
    by_cases hy0 : W y = ⊥
    · have h1 : orbitCode k W y = ⊥ := orbitCode_eq_bot_iff.mpr hy0
      rw [h1, le_bot_iff, orbitCode_eq_bot_iff, hWx] at hge'
      exact top_ne_bot hge'
    · have h := (visibilityReplace_orbitCode_le_iff (k := k) (w := W) hy0
        (by rw [hWx]; exact top_ne_bot)).mp (monotone_visibilityReplace le_rfl hge')
      rw [hWx, visibilityReplace_top, top_le_iff, visibilityReplace_eq_top_iff, hWy] at h
      exact ne_top_of_mem_codeGrid (mem_codeGrid_of_mem_catalogue hb y) h
  · refine min_orbitCode_eq (hgx ▸ hbl.orderly x)
      (isShort_of_mem_codeGrid (mem_codeGrid_of_mem_catalogue hb x)) hbo (fun e ↦ ?_) d
    rw [hWdef]; dsimp only
    split_ifs with h
    · rw [min_top_left, min_eq_right h.2]
    · rfl

/-- **Rows along a lower embedding whose rows pull back**: the row of the image of `a` at the image
of `b` is the row of `a` at `b`. -/
theorem rowAt_of_comap {n : ℕ} {S T : Scheme.{u} n} {φ : Fin T.card → Fin S.card}
    (hφ : T.toCellScheme.IsLowerEmbedding S.toCellScheme φ) (hR : S.rows.comap hφ = T.rows)
    (a b : Fin T.card) : S.rowAt (φ a) (φ b) = T.rowAt a b := by
  by_cases hb : b ∈ T.toCellScheme.below (T.toCellScheme.gradedIndex a)
  · have hb' : φ b ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex (φ a)) :=
      (hφ.le_iff b a).mpr hb
    rw [rowAt_of_mem hb', rowAt_of_mem hb, ← hR, CellScheme.Rows.comap_row]
  · have hb' : φ b ∉ S.toCellScheme.below (S.toCellScheme.gradedIndex (φ a)) :=
      fun h ↦ hb ((hφ.le_iff b a).mp h)
    rw [rowAt_of_notMem hb', rowAt_of_notMem hb]

end Scheme

/-! ### Servers at a seed whose right coatom type is `rightType` -/

namespace TowerProfile

open TwoFaceLiftExistsCounterexample CaseSplitCounterexample TopReadingApexExample

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- The cell of the layer at the grade `1` in the profile layer. -/
noncomputable abbrev oneCell (I : Seed.{u} α 3) (a : Fin (I.tower 1).card) :
    Fin (scheme I).card :=
  Fin.castAdd _ (Fin.castAdd _ a)

theorem isLowerEmbedding_oneCell :
    (I.tower 1).toCellScheme.IsLowerEmbedding (scheme I).toCellScheme (oneCell I) :=
  (Scheme.isLowerEmbedding_castAdd 3 (mult I) (fun i ↦ fieldLab I (entry I i))
    (I.not_univ_succ_le_tower 2)).comp
    (Scheme.isLowerEmbedding_fieldLayer (I.tower 1) 2 (I.not_univ_succ_le_tower 1))

theorem comap_rows_oneCell :
    (scheme I).rows.comap (isLowerEmbedding_oneCell (I := I)) = (I.tower 1).rows := by
  have h := CellScheme.Rows.comap_comap (scheme I).rows
    (Scheme.isLowerEmbedding_castAdd 3 (mult I) (fun i ↦ fieldLab I (entry I i))
      (I.not_univ_succ_le_tower 2))
    (Scheme.isLowerEmbedding_fieldLayer (I.tower 1) 2 (I.not_univ_succ_le_tower 1))
  rw [Scheme.comap_rows_castAdd (h := I.not_univ_succ_le_tower 2)] at h
  exact h.symm.trans (Scheme.comap_rows_fieldLayer (S := I.tower 1) (k := 2)
    (hS := I.not_univ_succ_le_tower 1))

theorem rowAt_oneCell (a b : Fin (I.tower 1).card) :
    (scheme I).rowAt (oneCell I a) (oneCell I b) = (I.tower 1).rowAt a b :=
  Scheme.rowAt_of_comap isLowerEmbedding_oneCell comap_rows_oneCell a b

theorem gradedIndex_oneCell (a : Fin (I.tower 1).card) :
    (scheme I).toCellScheme.gradedIndex (oneCell I a) = (I.tower 1).toCellScheme.gradedIndex a := by
  have h1 := isLowerEmbedding_oneCell (I := I)
  exact Prod.ext ((Scheme.appendFullCellsScheme_scope_castAdd (I.tower 2) 3 (mult I) _).trans
    (Scheme.appendFullCellsScheme_scope_castAdd (I.tower 1) 2 _ a)) (h1.grade_eq a)

/-- A labelling lawful below `(univ, 1)` in the profile layer is lawful below `(univ, 1)` in the
layer at the grade `1`. -/
theorem isLawfulBelow_one_of_scheme {e : Fin (scheme I).card → Label.{u}}
    (he : (scheme I).rows.IsLawfulBelow (univ, 1) fun d ↦ e d) :
    (I.tower 1).rows.IsLawfulBelow (univ, 1) fun d ↦ e (oneCell I d) := by
  have h1 := (Scheme.isLawfulBelow_appendFullCells_iff (S := I.tower 2) (k := 3) (M := mult I)
    (r := fun i ↦ fieldLab I (entry I i)) (h := I.not_univ_succ_le_tower 2) (v := e)
    (X := ((univ : Finset (Fin 5)), 1)) (fun h ↦ absurd h.2 (by omega))).mp he
  exact (Scheme.isLawfulBelow_appendFullCells_iff (S := I.tower 1) (k := 2)
    (M := ((I.tower 1).catalogue 2).card)
    (r := fun i ↦ (I.tower 1).fieldRow 2 ((I.tower 1).catalogueEntry 2 i))
    (h := I.not_univ_succ_le_tower 1) (v := fun d ↦ e (Fin.castAdd _ d))
    (X := ((univ : Finset (Fin 5)), 1)) (fun h ↦ absurd h.2 (by omega))).mp h1

/-! ### The right coatom type `rightType` -/

theorem live_iff_three_mem : ∀ a : Fin 19, TwoFaceLiftCounterexample.cellGrade a = 1 →
    (CaseSplitCounterexample.live a = true ↔
      (3 : Fin 4) ∈ TwoFaceLiftCounterexample.cellScope a) := by
  decide

theorem cellGrade_pos : ∀ a : Fin 19, 1 ≤ TwoFaceLiftCounterexample.cellGrade a := by decide

/-- The rows of `rightType` at its old cells are those of `S`. -/
theorem rowAt_rightType_castSucc (a b : Fin CaseSplitCounterexample.S.{u}.card) :
    (rightType α).toScheme.rowAt (Fin.castSucc a) (Fin.castSucc b) =
      CaseSplitCounterexample.S.rowAt a b :=
  Scheme.rowAt_of_comap (Scheme.isLowerEmbedding_castSucc 4
    (StageType.apexRow (t := rightBase α) isLegalBelowFullGrade_S) isLegalBelowFullGrade_S.not_le)
    Scheme.comap_rows_castSucc a b

/-- **The rows of a live cell of grade `1` of `S`**: a cell of grade `1` inside its scope is read
at `v1` when live and as `⊥` otherwise. -/
theorem rowAt_S_live {a b : Fin 19} (ha : TwoFaceLiftCounterexample.cellGrade a = 1)
    (hla : CaseSplitCounterexample.live a = true) (hb : TwoFaceLiftCounterexample.cellGrade b = 1)
    (hsub : TwoFaceLiftCounterexample.cellScope b ⊆ TwoFaceLiftCounterexample.cellScope a) :
    CaseSplitCounterexample.S.{u}.rowAt a b =
      if CaseSplitCounterexample.live b = true then TwoFaceLiftCounterexample.v1 else ⊥ := by
  have hmem : b ∈ CaseSplitCounterexample.S.{u}.toCellScheme.below
      (CaseSplitCounterexample.S.{u}.toCellScheme.gradedIndex a) := by
    change TwoFaceLiftCounterexample.cells.gradedIndex b ≤
      TwoFaceLiftCounterexample.cells.gradedIndex a
    rw [TwoFaceLiftCounterexample.gradedIndex_cells, TwoFaceLiftCounterexample.gradedIndex_cells]
    exact Prod.mk_le_mk.mpr ⟨hsub, by rw [ha, hb]⟩
  rw [Scheme.rowAt_of_mem hmem]
  change CaseSplitCounterexample.rows.row a ⟨b, hmem⟩ = _
  simp only [CaseSplitCounterexample.rows, hla, ha, hb, true_and]
  split_ifs <;> simp_all

variable (hR : StageType.restrictFace (Coatom.right 3) I.amalgam = some (rightType α))

include hR in
/-- A cell of the amalgam inside the right coatom is a cell of `rightType`. -/
theorem exists_right_cell {d : Fin I.amalgam.card}
    (hd : I.amalgam.toCellScheme.scope d ⊆ univ.erase (Fin.castSucc (Fin.last 3))) :
    ∃ z, StageType.faceCell hR z = d := by
  obtain ⟨hf, he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hR
  refine I.amalgam.toScheme.exists_faceCell_eq _ (Scheme.mem_visibleCells.mpr fun p hp ↦ ?_)
  have hp' := hd (mem_coe.mp hp)
  rw [← univ_map_right_eq] at hp'
  obtain ⟨a, -, rfl⟩ := mem_map.mp hp'
  exact ⟨a, rfl⟩

include hR in
/-- The point `4` lies in the scope of a cell of `rightType` carried to the amalgam exactly when
the point `3` lies in its scope. -/
theorem last_mem_scope_right (z : Fin (rightType α).card) :
    Fin.last 4 ∈ I.amalgam.toCellScheme.scope (StageType.faceCell hR z) ↔
      (3 : Fin 4) ∈ (rightType α).toCellScheme.scope z := by
  rw [StageType.scope_faceCell, mem_map]
  constructor
  · rintro ⟨a, ha, hae⟩
    have : a = 3 := by
      have h3 : Coatom.right 3 3 = Fin.last 4 := by decide
      exact (Coatom.right 3).injective (hae.trans h3.symm)
    rwa [← this]
  · intro h
    exact ⟨3, h, by decide⟩

include hR in
/-- **The rows of the amalgam at a live cell of grade `1` of the right coatom** read the cells
below it through the point `4` as they read the cell itself, and the others as `⊥`. -/
theorem rowP_right (s : Fin I.amalgam.card) (hPs : Fin.last 4 ∈ I.amalgam.toCellScheme.scope s)
    (hgs : I.amalgam.toCellScheme.grade s = 1) (d : Fin I.amalgam.card)
    (hd : d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s)) :
    (Fin.last 4 ∈ I.amalgam.toCellScheme.scope d → I.amalgam.toScheme.rows.row s ⟨d, hd⟩ =
        I.amalgam.toScheme.rows.row s ⟨s, I.amalgam.toCellScheme.mem_below_gradedIndex s⟩) ∧
      (Fin.last 4 ∉ I.amalgam.toCellScheme.scope d →
        I.amalgam.toScheme.rows.row s ⟨d, hd⟩ = ⊥) := by
  have hsD : I.amalgam.toCellScheme.scope s ⊆ univ.erase (Fin.castSucc (Fin.last 3)) := by
    rcases I.scope_subset_or (x := Fin.last 4) (y := Fin.castSucc (Fin.last 3)) (by simp)
      (by simp) (by decide) s with h | h
    · exact absurd (h hPs) (by simp)
    · exact h
  obtain ⟨zs, rfl⟩ := exists_right_cell hR hsD
  obtain ⟨zd, rfl⟩ := exists_right_cell hR (hd.1.trans hsD)
  have hgzs : (rightType α).toCellScheme.grade zs = 1 :=
    (StageType.grade_faceCell hR zs).symm.trans hgs
  have hgzd : (rightType α).toCellScheme.grade zd ≤ 1 :=
    (StageType.grade_faceCell hR zd).symm.trans_le (hd.2.trans hgs.le)
  -- both are old cells of `rightType`
  have hold (z : Fin (rightType α).card) (hz : (rightType α).toCellScheme.grade z ≤ 1) :
      ∃ a, Fin.castSucc a = z := by
    revert hz
    change Fin (CaseSplitCounterexample.S.{u}.card + 1) at z
    induction z using Fin.lastCases with
    | last =>
      intro hz
      have h4 : (rightType α).toCellScheme.grade (Fin.last _) = 4 :=
        congrArg Prod.snd (StageType.addApex_gradedIndex_last (t := rightBase α)
          isLegalBelowFullGrade_S (by omega))
      exact absurd (le_of_eq_of_le h4.symm hz) (by omega)
    | cast a => exact fun _ ↦ ⟨a, rfl⟩
  have hsubz : (rightType α).toCellScheme.scope zd ⊆ (rightType α).toCellScheme.scope zs := by
    have h : I.amalgam.toCellScheme.scope (StageType.faceCell hR zd) ⊆
        I.amalgam.toCellScheme.scope (StageType.faceCell hR zs) := hd.1
    rw [StageType.scope_faceCell hR, StageType.scope_faceCell hR, map_subset_map] at h
    exact h
  have hPzs := (last_mem_scope_right hR zs).mp hPs
  have hPzd := last_mem_scope_right hR zd
  obtain ⟨as, rfl⟩ := hold zs hgzs.le
  obtain ⟨ad, rfl⟩ := hold zd hgzd
  have hga : TwoFaceLiftCounterexample.cellGrade as = 1 :=
    (Scheme.appendFullCellScheme_grade_castSucc CaseSplitCounterexample.S 4 as).symm.trans hgzs
  have hgd : TwoFaceLiftCounterexample.cellGrade ad = 1 :=
    le_antisymm
      ((Scheme.appendFullCellScheme_grade_castSucc CaseSplitCounterexample.S 4 ad).symm.trans_le
        hgzd) (cellGrade_pos ad)
  have hsc (a : Fin 19) : (rightType α).toCellScheme.scope (Fin.castSucc a) =
      TwoFaceLiftCounterexample.cellScope a :=
    Scheme.appendFullCellScheme_scope_castSucc CaseSplitCounterexample.S 4 a
  have hsub : TwoFaceLiftCounterexample.cellScope ad ⊆ TwoFaceLiftCounterexample.cellScope as :=
    (hsc ad).symm.subset.trans (hsubz.trans (hsc as).subset)
  have hlive_s : CaseSplitCounterexample.live as = true :=
    (live_iff_three_mem as hga).mpr (Eq.mp (congrArg (3 ∈ ·) (hsc as)) hPzs)
  have hrow (a : Fin (rightBase α).card) (hga' : TwoFaceLiftCounterexample.cellGrade a = 1)
      (hsa : TwoFaceLiftCounterexample.cellScope a ⊆ TwoFaceLiftCounterexample.cellScope as)
      (hm : StageType.faceCell hR (Fin.castSucc a) ∈ I.amalgam.toCellScheme.below
        (I.amalgam.toCellScheme.gradedIndex (StageType.faceCell hR (Fin.castSucc as)))) :
      I.amalgam.toScheme.rows.row _ ⟨_, hm⟩ =
        if CaseSplitCounterexample.live a = true then TwoFaceLiftCounterexample.v1 else ⊥ :=
    (Scheme.rowAt_of_mem hm).symm.trans ((StageType.rowAt_faceCell hR _ _).trans
      ((rowAt_rightType_castSucc as a).trans (rowAt_S_live hga hlive_s hga' hsa)))
  refine ⟨fun hPd ↦ ?_, fun hPd ↦ ?_⟩
  · have hld : CaseSplitCounterexample.live ad = true :=
      (live_iff_three_mem ad hgd).mpr (Eq.mp (congrArg (3 ∈ ·) (hsc ad)) (hPzd.mp hPd))
    rw [hrow ad hgd hsub hd, hrow as hga subset_rfl, hld, hlive_s]
  · have hld : CaseSplitCounterexample.live ad = false := by
      rcases h : CaseSplitCounterexample.live ad
      · rfl
      · exact absurd (hPzd.mpr (Eq.mpr (congrArg (3 ∈ ·) (hsc ad))
          ((live_iff_three_mem ad hgd).mp h))) hPd
    rw [hrow ad hgd hsub hd, hld]
    rfl

include hR in
/-- **Servers at a seed whose right coatom type is `rightType`.**  For every labelling `e` lawful
below `(univ, 1)` in the profile layer, every cell `x` of the amalgam of grade `1` through the
point `4` (a cell of the right coatom off the common face, such as the new top `{3}` of
`rightType`) not `⊥` in `e`, some cell of graded index `(univ, 1)` at least `e x` reads every cell
of grade at most `1` off the point `4` (the cells of the left coatom, such as the cells labelled
`3` by `threeType`) strictly below `x`, and reads `x` at a point of the code grid
(`Scheme.exists_server_fieldLayer`, with the raise of `Scheme.exists_raise_entry` at the cells
through the point `4`). -/
theorem exists_server_of_rightType {e : Fin (scheme I).card → Label.{u}}
    (he : (scheme I).rows.IsLawfulBelow (univ, 1) fun d ↦ e d) {x : Fin I.amalgam.card}
    (hPx : Fin.last 4 ∈ I.amalgam.toCellScheme.scope x)
    (hgx : I.amalgam.toCellScheme.grade x = 1) (hx0 : e (embed3 I x) ≠ ⊥) :
    ∃ u, (scheme I).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), 1) ∧
      e (embed3 I x) ≤ e u ∧
      (∀ y, Fin.last 4 ∉ I.amalgam.toCellScheme.scope y → I.amalgam.toCellScheme.grade y ≤ 1 →
        (scheme I).rowAt u (embed3 I y) < (scheme I).rowAt u (embed3 I x)) ∧
      (scheme I).rowAt u (embed3 I x) ∈ codeGrid 1 (2 * (I.tower 0).card) := by
  classical
  obtain ⟨i, hxi, hlt⟩ := Scheme.exists_server_fieldLayer (S := I.tower 0) (k := 1)
    (hS := I.not_univ_succ_le_tower 0) (w := fun d ↦ e (oneCell I d))
    (isLawfulBelow_one_of_scheme he) (x := x)
    (Q := fun y ↦ Fin.last 4 ∉ I.amalgam.toCellScheme.scope y) hgx hx0 fun b hb hbx _ ↦
      Scheme.exists_raise_entry (S := I.amalgam.toScheme) (k := 1)
        (P := fun d ↦ Fin.last 4 ∈ I.amalgam.toCellScheme.scope d)
        (fun _ _ hst hs ↦ hst hs)
        (fun d _ hd ↦ le_antisymm hd (I.amalgam.isWellFormed.isWellFormed.grade_pos d))
        (fun s hs hgs d hd ↦ rowP_right hR s hs hgs d hd) hb hPx hgx hbx
  refine ⟨oneCell I (Fin.natAdd _ i), ?_, hxi, ?_⟩
  · exact (gradedIndex_oneCell (I := I) _).trans
      (Scheme.appendFullCellsScheme_gradedIndex_natAdd (I.tower 0) 1 _ i)
  · have hrow (z : Fin I.amalgam.card) (hz : I.amalgam.toCellScheme.grade z ≤ 1) :
        (scheme I).rowAt (oneCell I (Fin.natAdd _ i)) (embed3 I z) =
          (I.tower 0).catalogueEntry 1 i z := by
      have hm : (Fin.castAdd _ z : Fin (I.tower 1).card) ∈ (I.tower 1).toCellScheme.below
          ((I.tower 1).toCellScheme.gradedIndex (Fin.natAdd _ i)) := by
        have e1 : (I.tower 1).toCellScheme.gradedIndex (Fin.castAdd _ z) =
            I.amalgam.toCellScheme.gradedIndex z :=
          Scheme.appendFullCellsScheme_gradedIndex_castAdd (I.tower 0) 1 _ z
        have e2 : (I.tower 1).toCellScheme.gradedIndex (Fin.natAdd _ i) =
            ((univ : Finset (Fin 5)), 1) :=
          Scheme.appendFullCellsScheme_gradedIndex_natAdd (I.tower 0) 1 _ i
        exact e1.trans_le (le_of_le_of_eq (Prod.mk_le_mk.mpr ⟨subset_univ _, hz⟩) e2.symm)
      refine (rowAt_oneCell (I := I) (Fin.natAdd _ i) (Fin.castAdd _ z)).trans ?_
      rw [Scheme.rowAt_of_mem hm]
      exact (Scheme.fieldLayer_row_natAdd (S := I.tower 0) (k := 1)
        (hS := I.not_univ_succ_le_tower 0) i _).trans (Scheme.fieldRow_castAdd _ z)
    refine ⟨fun y hPy hgy ↦ ?_, ?_⟩
    · rw [hrow y hgy, hrow x hgx.le]
      exact hlt y hPy
    · rw [hrow x hgx.le]
      exact Scheme.mem_codeGrid_of_mem_catalogue (Scheme.catalogueEntry_mem i) x

include hR in
/-- **The band obstruction never applies at a seed whose right coatom type is `rightType`**: for
every labelling lawful below `(univ, 4)` at least a positive cap `h` at a cell `x` of grade `1`
through the point `4`, and every cell `y` of grade at most `1` off it, some cell of graded index
`(univ, 1)` at least `h` reads `y` strictly below `x` — a server, so the hypothesis of
`TowerProfile.not_exists_fill_of_noServer` fails. -/
theorem exists_server_above_cap_of_rightType {e : Fin (scheme I).card → Label.{u}}
    (he : (scheme I).rows.IsLawfulBelow (univ, 4) fun d ↦ e d) {x y : Fin I.amalgam.card}
    (hPx : Fin.last 4 ∈ I.amalgam.toCellScheme.scope x)
    (hgx : I.amalgam.toCellScheme.grade x = 1)
    (hPy : Fin.last 4 ∉ I.amalgam.toCellScheme.scope y)
    (hgy : I.amalgam.toCellScheme.grade y ≤ 1) {h : Label.{u}} (hhb : ⊥ < h)
    (hxh : h ≤ e (embed3 I x)) :
    ∃ u, (scheme I).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), 1) ∧ h ≤ e u ∧
      ¬ (scheme I).rowAt u (embed3 I x) ≤ (scheme I).rowAt u (embed3 I y) := by
  obtain ⟨u, hu, hxu, hlt, -⟩ := exists_server_of_rightType hR
    (he.mono (X := ((univ : Finset (Fin 5)), 1)) ⟨subset_rfl, by omega⟩) hPx hgx
    (fun h0 ↦ (hhb.trans_le hxh).ne' h0)
  exact ⟨u, hu, hxh.trans hxu, not_le.mpr (hlt y hPy hgy)⟩

end TowerProfile

end VaughtConjecture
