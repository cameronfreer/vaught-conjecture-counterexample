/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapReadingCatalogue
import VaughtConjecture.Continuation.SourceGapSeparationObstruction

/-!
# The mixed entry is forced at the tops of a full-catalogue layer

Roadmap, Layer 3 ((R2) of the table of 3.4, the reading of the new tops at the cells labelled `⊤`);
the sheet layers of `VaughtConjecture.Extension.MarkedCatalogue` and the forced tops of
`VaughtConjecture.Continuation.SourceGapReadingCatalogue`.

**The site** (`Scheme.IsMixedSite S y z o r z' o' r'`).  A scheme `S` with cells of grade at most
`2`, whose cells of grade `2` are a **context** pair `o`, `r` and a **donor** pair `o'`, `r'`; the
rows of `o` and `r` read exactly `y`, `z`, `o`, `r` (the cells `y`, `z` of grade at most `1`), the
rows of `o'` and `r'` read exactly `y`, `z'`, `o'`, `r'`; the row of `o` reads `y` and `z` at least
as `o`, the row of `o'` reads `y` and `z'` at least as `o'`; and the scope of a context cell of
grade `2` is not contained in that of a donor cell of grade `2`.  The cells of the amalgam of two
copies of the input `SeparationObstruction.T` over the face `{0}` form such a site
(`MixedEntry.isMixedSite_A`), and so do they in every layer of cells of full scope and grade `1`
over it (`Scheme.IsMixedSite.appendFullCells`).

**The mixed labelling** (`Scheme.mixedLabelling e b o' r'`): the grid point `ω * b + 2` at `o'` and
`r'`, and elsewhere the collapse of `e` above `ω * b + 2` (labels at least `ω * b + 2` go to `⊤`).
For a lawful labelling `e` of a site at least `ω * b + 2` at the four cells of grade `2`, it is
lawful (`Scheme.IsMixedSite.isLawful_mixedLabelling`): at the cells of grade at most `1` by the
collapse of a transformation (`Label.TransformsTo.collapse`), at the cells of grade `2` by their
rows, which read only cells at least `ω * b + 2` or at `⊥`.  It is `⊤` at every context cell and
`ω * b + 2` at the donor cells of grade `2`, and agrees with `e` capped at `ω * b + 2`.

**The mixed entry is forced** (compiled in this repository,
`Scheme.IsMixedSite.exists_top_lt_of_serves`).  Let `L` be a sheet layer at grade `2` over a site
whose entries lie in the canonical catalogue and which **serves the capped agreements**
(`Scheme.ServesAgreements`: a catalogue entry agreeing with the entry of a new cell `i` capped at a
grid point at most a value of that entry is the entry of a new cell `j` with sheet cap from `i` at
least that point).  This holds when every catalogue entry is an entry and the caps are at least the
values of their entries (`Scheme.servesAgreements_of_le`; the canonical field layer, and the
leaf-and-marked layer with the ceiling cap), and in the leaf-and-marked layer for every set of
marks marked-closed for its cap (`Scheme.servesAgreements_markedLayer`), the closure under which
the lifts along marked cells hold.  Let `q` be a lawful labelling of `L` labelling `⊤` the four
cells of grade `2`.  Then some new cell `j` is labelled `⊤` and its entry reads `o'` and `r'`
strictly below every context cell `y`, `z`, `o`, `r`.  Proof: availability from `o` gives a new
cell `u` labelled `⊤`; its entry `e` is lawful, orbit-canonical, and other than `⊥` at the four
cells of grade `2`; the least of these values is a grid point `ω * b + 2`; the orbit code of the
mixed labelling at `b` is a catalogue entry agreeing with `e` capped at `ω * b + 2`
(`Label.min_orbitCode_eq`), so it is the entry of a new cell whose cross height with `u` is at
least that least value, and that cell is `⊤`
(`Scheme.eq_top_natAdd_sheetLayer`); the orbit code keeps the order of the keys
(`Label.visibilityReplace_orbitCode_le_iff`), and `ω * b + 2 < ⊤`.

No legality, bountifulness, choice of marks or caps beyond marked closure, or condition on the
layer at grade `1` enters.  The canonical field layer is the sheet layer with one sheet
(`Scheme.fieldLayer_eq_sheetLayer`), so it is covered as well.  In the form of a reading
(`Scheme.IsMixedSite.not_exists_reading`): no context cell `s` is read at most as `o'` by every new
cell labelled `⊤`.  Over the amalgam of two copies of
`SeparationObstruction.T` and any layer of cells of full scope and grade `1` over it (the lower
layer at the arity one, canonical or leaf-and-marked with any marks), this holds for the
leaf-and-marked layer at grade `2` with any marks marked-closed for its cap
(`MixedEntry.not_exists_reading_markedLayer`) and for the canonical field layer at grade `2`
(`MixedEntry.not_exists_reading_fieldLayer`).

The reading at the tops (`StageType.ReadsEachNewTopAtTops`) asks, for the new top `o'` of grade
`2`, some cell `s` of the context labelled `⊤` (`y`, `z`, `o` or `r`) read at most as `o'` by every
cell of full scope and grade `2` labelled `⊤`.  So a coface reading each new top at its tops at
this input, with the donor `T` itself, does not come from the completion at the arity one, canonical
or leaf-and-marked (argued, not formalized: the identification of the cells of the amalgam of the
seed with those of `MixedEntry.A`).  A reading coface exists at this input
(`ReadingInstance.exists_readsEachNewTop_T`, through a display of kinds, not a catalogue layer).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label
open scoped Ordinal

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {y z o r z' o' r' : Fin S.card}

/-- The **site of the mixed labelling** in a scheme `S` of grade at most `2`: the context cells
`y`, `z`, `o`, `r`, the donor cells `z'`, `o'`, `r'`, with the cells of grade `2` exactly `o`, `r`,
`o'`, `r'`, and the reading of the rows of these four cells as in two copies of
`SeparationObstruction.T` glued along `y`. -/
structure IsMixedSite (S : Scheme.{u} n) (y z o r z' o' r' : Fin S.card) : Prop where
  grade_le (d : Fin S.card) : S.toCellScheme.grade d ≤ 2
  grade_eq_two_iff (d : Fin S.card) :
    S.toCellScheme.grade d = 2 ↔ d = o ∨ d = r ∨ d = o' ∨ d = r'
  grade_y : S.toCellScheme.grade y ≤ 1
  grade_z : S.toCellScheme.grade z ≤ 1
  rowAt_context (c : Fin S.card) (hc : c = o ∨ c = r) (d : Fin S.card) :
    S.rowAt c d ≠ ⊥ ↔ d = y ∨ d = z ∨ d = o ∨ d = r
  rowAt_donor (c : Fin S.card) (hc : c = o' ∨ c = r') (d : Fin S.card) :
    S.rowAt c d ≠ ⊥ ↔ d = y ∨ d = z' ∨ d = o' ∨ d = r'
  rowAt_o_le_y : S.rowAt o o ≤ S.rowAt o y
  rowAt_o_le_z : S.rowAt o o ≤ S.rowAt o z
  rowAt_o'_le_y : S.rowAt o' o' ≤ S.rowAt o' y
  rowAt_o'_le_z' : S.rowAt o' o' ≤ S.rowAt o' z'
  not_scope_subset (s t : Fin S.card) (hs : s = o ∨ s = r) (ht : t = o' ∨ t = r') :
    ¬ S.toCellScheme.scope s ⊆ S.toCellScheme.scope t

/-- A lawful labelling keeps the order of a row that reads `x` at least as the cell `c` itself. -/
theorem le_of_rowAt_le {e : Fin S.card → Label.{u}} (he : S.rows.IsLawful e) {c x : Fin S.card}
    (hc : S.rowAt c c ≠ ⊥) (hle : S.rowAt c c ≤ S.rowAt c x)
    (hg : S.toCellScheme.grade x ≤ S.toCellScheme.grade c) : e c ≤ e x := by
  have hcc : c ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex c) := mem_below_of_rowAt_ne_bot hc
  have hx : x ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex c) :=
    mem_below_of_rowAt_ne_bot fun h ↦ hc (le_bot_iff.mp (h ▸ hle))
  rw [rowAt_of_mem hcc, rowAt_of_mem hx] at hle
  have h := (he.locality c).le_of_le (d := ⟨c, hcc⟩) (d' := ⟨x, hx⟩) hle hg
  simp only [min_self] at h
  exact h.trans (min_le_left _ _)

namespace IsMixedSite

variable (hs : S.IsMixedSite y z o r z' o' r')
include hs

theorem grade_o : S.toCellScheme.grade o = 2 := (hs.grade_eq_two_iff o).mpr (.inl rfl)
theorem grade_r : S.toCellScheme.grade r = 2 := (hs.grade_eq_two_iff r).mpr (.inr (.inl rfl))
theorem grade_o' : S.toCellScheme.grade o' = 2 :=
  (hs.grade_eq_two_iff o').mpr (.inr (.inr (.inl rfl)))
theorem grade_r' : S.toCellScheme.grade r' = 2 :=
  (hs.grade_eq_two_iff r').mpr (.inr (.inr (.inr rfl)))

/-- A context cell is not a donor cell of grade `2`. -/
theorem not_donor {s : Fin S.card} (hsc : s = y ∨ s = z ∨ s = o ∨ s = r) : ¬ (s = o' ∨ s = r') := by
  intro hd
  have h2 : S.toCellScheme.grade s = 2 := (hs.grade_eq_two_iff s).mpr (.inr (.inr hd))
  rcases hsc with rfl | rfl | rfl | rfl
  · have := hs.grade_y; omega
  · have := hs.grade_z; omega
  · exact hs.not_scope_subset s s (.inl rfl) hd le_rfl
  · exact hs.not_scope_subset s s (.inr rfl) hd le_rfl

/-- **The order of a lawful labelling at a site**: the context cells `y`, `z` are at least `o`, the
donor cells `y`, `z'` at least `o'`. -/
theorem le_of_isLawful {e : Fin S.card → Label.{u}} (he : S.rows.IsLawful e) :
    e o ≤ e y ∧ e o ≤ e z ∧ e o' ≤ e y ∧ e o' ≤ e z' := by
  have ho : S.rowAt o o ≠ ⊥ := (hs.rowAt_context o (.inl rfl) o).mpr (.inr (.inr (.inl rfl)))
  have ho' : S.rowAt o' o' ≠ ⊥ := (hs.rowAt_donor o' (.inl rfl) o').mpr (.inr (.inr (.inl rfl)))
  refine ⟨le_of_rowAt_le he ho hs.rowAt_o_le_y ?_, le_of_rowAt_le he ho hs.rowAt_o_le_z ?_,
    le_of_rowAt_le he ho' hs.rowAt_o'_le_y ?_, le_of_rowAt_le he ho' hs.rowAt_o'_le_z' ?_⟩
  · rw [hs.grade_o]; have := hs.grade_y; omega
  · rw [hs.grade_o]; have := hs.grade_z; omega
  · rw [hs.grade_o']; have := hs.grade_y; omega
  · rw [hs.grade_o']; exact hs.grade_le z'

end IsMixedSite

/-! ### The mixed labelling -/

variable (o' r') in
/-- The **mixed labelling** of `e` at the block `b`: the grid point `ω * b + 2` at `o'` and `r'`,
and elsewhere the collapse of `e` above `ω * b + 2`. -/
noncomputable def mixedLabelling (e : Fin S.card → Label.{u}) (b : ℕ) : Fin S.card → Label.{u} :=
  fun d ↦ if d = o' ∨ d = r' then gridPoint 2 b else Label.collapse (ω * (b : Ordinal.{u})) 2 (e d)

theorem mixedLabelling_of_donor {e : Fin S.card → Label.{u}} {b : ℕ} {d : Fin S.card}
    (hd : d = o' ∨ d = r') : mixedLabelling o' r' e b d = gridPoint 2 b := ite_eq_left hd

theorem mixedLabelling_of_not_donor {e : Fin S.card → Label.{u}} {b : ℕ} {d : Fin S.card}
    (hd : ¬ (d = o' ∨ d = r')) :
    mixedLabelling o' r' e b d = Label.collapse (ω * (b : Ordinal.{u})) 2 (e d) := ite_eq_right hd

/-- The collapse above the grid point `ω * b + 2` sends a label at least that point to `⊤`. -/
theorem collapse_of_le {b : ℕ} {x : Label.{u}} (hx : gridPoint 2 b ≤ x) :
    Label.collapse (ω * (b : Ordinal.{u})) 2 x = ⊤ :=
  reduce_of_le hx

/-- The collapse fixes `⊥`. -/
theorem collapse_bot (b : ℕ) : Label.collapse (ω * (b : Ordinal.{u})) 2 (⊥ : Label.{u}) = ⊥ :=
  reduce_bot

/-- The start `ω * b` of a block is zero or a limit. -/
private theorem isSuccPrelimit_block (b : ℕ) : Order.IsSuccPrelimit (ω * (b : Ordinal.{u})) :=
  Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right ω _)

namespace IsMixedSite

variable (hs : S.IsMixedSite y z o r z' o' r')
include hs

/-- **The mixed labelling is lawful** for a lawful labelling `e` at least `ω * b + 2` at the four
cells of grade `2`. -/
theorem isLawful_mixedLabelling {e : Fin S.card → Label.{u}} (he : S.rows.IsLawful e) {b : ℕ}
    (hb : ∀ c, (c = o ∨ c = r ∨ c = o' ∨ c = r') → gridPoint 2 b ≤ e c) :
    S.rows.IsLawful (mixedLabelling o' r' e b) := by
  obtain ⟨hoy, hoz, ho'y, ho'z'⟩ := hs.le_of_isLawful he
  -- every cell read by a cell of grade `2` other than at `⊥` is at least `ω * b + 2`
  have hctx (d : Fin S.card) (hd : d = y ∨ d = z ∨ d = o ∨ d = r) : gridPoint 2 b ≤ e d := by
    have ho := hb o (.inl rfl)
    rcases hd with rfl | rfl | rfl | rfl
    exacts [ho.trans hoy, ho.trans hoz, ho, hb _ (.inr (.inl rfl))]
  have hdon (d : Fin S.card) (hd : d = y ∨ d = z' ∨ d = o' ∨ d = r') : gridPoint 2 b ≤ e d := by
    have ho' := hb o' (.inr (.inr (.inl rfl)))
    rcases hd with rfl | rfl | rfl | rfl
    exacts [ho'.trans ho'y, ho'.trans ho'z', ho', hb _ (.inr (.inr (.inr rfl)))]
  have hne (c : Fin S.card) (hc : c = o ∨ c = r ∨ c = o' ∨ c = r') : e c ≠ ⊥ := fun h ↦ by
    have h' := hb c hc
    rw [h, le_bot_iff] at h'
    exact WithBot.coe_ne_bot h'
  -- a cell read at `⊥` by a cell of grade `2` is `⊥` in `e`, so is not a donor cell of grade `2`
  have hbotread (c : Fin S.card) (hc : c = o ∨ c = r ∨ c = o' ∨ c = r')
      (d : S.toCellScheme.below (S.toCellScheme.gradedIndex c)) (hd : S.rows.row c d = ⊥) :
      e d = ⊥ ∧ ¬ ((d : Fin S.card) = o' ∨ (d : Fin S.card) = r') := by
    have h := (he.locality c).eq_bot hd
    simp only [_root_.min_eq_bot, hne c hc, or_false] at h
    refine ⟨h, fun hd' ↦ hne d (.inr (.inr hd')) h⟩
  have hrow (c : Fin S.card) (d : S.toCellScheme.below (S.toCellScheme.gradedIndex c)) :
      S.rows.row c d = S.rowAt c d := (rowAt_of_mem d.2).symm
  refine ⟨fun d ↦ ?_, fun c ↦ ?_, fun s t hst hg ↦ ?_⟩
  · -- order
    by_cases hd : d = o' ∨ d = r'
    · rw [mixedLabelling_of_donor hd, (hs.grade_eq_two_iff d).mpr (.inr (.inr hd))]
      exact isSelfVisible_gridPoint 2 b
    · rw [mixedLabelling_of_not_donor hd]
      exact (he.orderly d).reduce _
  · -- locality
    by_cases hc2 : S.toCellScheme.grade c = 2
    · have hc4 := (hs.grade_eq_two_iff c).mp hc2
      have hgr (d : S.toCellScheme.below (S.toCellScheme.gradedIndex c)) :
          S.toCellScheme.grade d ≤ 2 := hs.grade_le d
      rcases hc4 with hc | hc | hc | hc
      · -- the context cell `o`: the section is `⊤` at the cells read other than at `⊥`
        have hcc : ¬ (c = o' ∨ c = r') := hs.not_donor (.inr (.inr (.inl hc)))
        refine transformsTo_of_eq_bot_iff _ hgr (isSelfVisible_top 2) _ _ fun d ↦ ?_
        rw [mixedLabelling_of_not_donor hcc, collapse_of_le (hctx c (.inr (.inr (.inl hc)))),
          min_top_right]
        split_ifs with hd
        · obtain ⟨h1, h2⟩ := hbotread c (.inl hc) d hd
          rw [mixedLabelling_of_not_donor h2, h1, collapse_bot]
        · have hd' := (hs.rowAt_context c (.inl hc) d).mp (hrow c d ▸ hd)
          rw [mixedLabelling_of_not_donor (hs.not_donor hd'), collapse_of_le (hctx d hd')]
      · -- the context cell `r`
        have hcc : ¬ (c = o' ∨ c = r') := hs.not_donor (.inr (.inr (.inr hc)))
        refine transformsTo_of_eq_bot_iff _ hgr (isSelfVisible_top 2) _ _ fun d ↦ ?_
        rw [mixedLabelling_of_not_donor hcc, collapse_of_le (hctx c (.inr (.inr (.inr hc)))),
          min_top_right]
        split_ifs with hd
        · obtain ⟨h1, h2⟩ := hbotread c (.inr (.inl hc)) d hd
          rw [mixedLabelling_of_not_donor h2, h1, collapse_bot]
        · have hd' := (hs.rowAt_context c (.inr hc) d).mp (hrow c d ▸ hd)
          rw [mixedLabelling_of_not_donor (hs.not_donor hd'), collapse_of_le (hctx d hd')]
      · -- the donor cell `o'`: the section is `ω * b + 2` at the cells read other than at `⊥`
        refine transformsTo_of_eq_bot_iff _ hgr (isSelfVisible_gridPoint 2 b) _ _ fun d ↦ ?_
        rw [mixedLabelling_of_donor (.inl hc)]
        split_ifs with hd
        · obtain ⟨h1, h2⟩ := hbotread c (.inr (.inr (.inl hc))) d hd
          rw [mixedLabelling_of_not_donor h2, h1, collapse_bot, min_eq_left bot_le]
        · have hd' := (hs.rowAt_donor c (.inl hc) d).mp (hrow c d ▸ hd)
          refine min_eq_right ?_
          by_cases hdd : (d : Fin S.card) = o' ∨ (d : Fin S.card) = r'
          · rw [mixedLabelling_of_donor hdd]
          · rw [mixedLabelling_of_not_donor hdd, collapse_of_le (hdon d hd')]
            exact le_top
      · -- the donor cell `r'`
        refine transformsTo_of_eq_bot_iff _ hgr (isSelfVisible_gridPoint 2 b) _ _ fun d ↦ ?_
        rw [mixedLabelling_of_donor (.inr hc)]
        split_ifs with hd
        · obtain ⟨h1, h2⟩ := hbotread c (.inr (.inr (.inr hc))) d hd
          rw [mixedLabelling_of_not_donor h2, h1, collapse_bot, min_eq_left bot_le]
        · have hd' := (hs.rowAt_donor c (.inr hc) d).mp (hrow c d ▸ hd)
          refine min_eq_right ?_
          by_cases hdd : (d : Fin S.card) = o' ∨ (d : Fin S.card) = r'
          · rw [mixedLabelling_of_donor hdd]
          · rw [mixedLabelling_of_not_donor hdd, collapse_of_le (hdon d hd')]
            exact le_top
    · -- a cell of grade at most `1`: the collapse of the locality of `e`
      have hc1 : S.toCellScheme.grade c ≤ 1 := by have := hs.grade_le c; omega
      have hnd (d : Fin S.card) (hd : S.toCellScheme.grade d ≤ 1) : ¬ (d = o' ∨ d = r') :=
        fun h ↦ by rw [(hs.grade_eq_two_iff d).mpr (.inr (.inr h))] at hd; omega
      have hK (d : S.toCellScheme.below (S.toCellScheme.gradedIndex c)) :
          S.toCellScheme.grade d ≤ 1 := d.2.2.trans hc1
      convert (he.locality c).collapse (isSuccPrelimit_block b) hK (by omega : 1 < 2) using 1
      funext d
      rw [Function.comp_apply, mixedLabelling_of_not_donor (hnd d (hK d)),
        mixedLabelling_of_not_donor (hnd c hc1)]
      exact ((monotone_reduce _).map_min).symm
  · -- availability
    obtain ⟨u', hu', hle⟩ := he.availability s t hst hg
    by_cases hsd : s = o' ∨ s = r'
    · refine ⟨u', hu', ?_⟩
      rw [mixedLabelling_of_donor hsd]
      by_cases hud : u' = o' ∨ u' = r'
      · rw [mixedLabelling_of_donor hud]
      · rw [mixedLabelling_of_not_donor hud, collapse_of_le ((hb s (.inr (.inr hsd))).trans hle)]
        exact le_top
    · by_cases hud : u' = o' ∨ u' = r'
      · exfalso
        have hgu : S.toCellScheme.grade u' = 2 := (hs.grade_eq_two_iff u').mpr (.inr (.inr hud))
        have hgt : S.toCellScheme.grade t = 2 := by
          rw [← hgu]; exact (congrArg Prod.snd hu').symm
        rcases (hs.grade_eq_two_iff s).mp (hg.trans hgt) with h | h | h | h
        · exact hs.not_scope_subset s u' (.inl h) hud
            (hst.trans (congrArg Prod.fst hu').symm.le)
        · exact hs.not_scope_subset s u' (.inr h) hud
            (hst.trans (congrArg Prod.fst hu').symm.le)
        · exact hsd (.inl h)
        · exact hsd (.inr h)
      · refine ⟨u', hu', ?_⟩
        rw [mixedLabelling_of_not_donor hsd, mixedLabelling_of_not_donor hud]
        exact monotone_reduce _ hle

end IsMixedSite

/-! ### The mixed entry is forced -/

variable {M : ℕ} {ε : Fin M → Fin S.card → Label.{u}} {σ : Fin M → Bool}
  {κ : (Fin S.card → Label.{u}) → Label.{u}}
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), 2) ≤ S.toCellScheme.gradedIndex d}

/-- An old cell lies below every new cell of a sheet layer at grade `2` over a site. -/
private theorem old_mem_below_new (hs : S.IsMixedSite y z o r z' o' r') (c : Fin S.card)
    (i : Fin M) : Fin.castAdd M c ∈ (S.sheetLayer 2 ε σ κ hS).toCellScheme.below
      ((S.sheetLayer 2 ε σ κ hS).toCellScheme.gradedIndex (Fin.natAdd S.card i)) := by
  rw [appendFullCellsScheme_gradedIndex_natAdd, CellScheme.mem_below,
    appendFullCellsScheme_gradedIndex_castAdd]
  exact ⟨subset_univ _, hs.grade_le c⟩

/-- A new cell labelled `⊤` reads every old cell labelled `⊤` other than at `⊥`. -/
private theorem ne_bot_of_eq_top (hs : S.IsMixedSite y z o r z' o' r')
    {q : Fin (S.card + M) → Label.{u}} (hq : (S.sheetLayer 2 ε σ κ hS).rows.IsLawful q)
    {i : Fin M} (hi : q (Fin.natAdd S.card i) = ⊤) {c : Fin S.card}
    (hc : q (Fin.castAdd M c) = ⊤) : ε i c ≠ ⊥ := by
  intro h
  have h' := (hq.locality (Fin.natAdd S.card i)).eq_bot (d := ⟨_, old_mem_below_new hs c i⟩)
    (by rw [sheetLayer_row_natAdd, sheetRow_castAdd, h])
  simp only [hc, hi, min_self] at h'
  exact top_ne_bot h'

/-- A catalogue entry other than `⊥` at a cell of grade `2` is a grid point at grade `2`. -/
private theorem exists_eq_gridPoint {a : Fin S.card → Label.{u}} (ha : a ∈ S.catalogue 2)
    {c : Fin S.card} (hc : S.toCellScheme.grade c = 2) (hne : a c ≠ ⊥) :
    ∃ b ≤ 2 * S.card, a c = gridPoint 2 b := by
  have hv : IsSelfVisible 2 (a c) := hc ▸ (mem_catalogue.mp ha).1.orderly c
  rcases mem_codeGrid.mp (mem_codeGrid_of_mem_catalogue ha c) with h | ⟨b, hb, f, hf, h⟩
  · exact absurd h hne
  · rw [h, isSelfVisible_coe, Label.omega0_mul_add_natCast_mod, Nat.cast_le] at hv
    obtain rfl : f = 2 := le_antisymm hf hv
    exact ⟨b, hb, h⟩

/-- The layer **serves the capped agreements** at grade `k`: every catalogue entry `a` agreeing
with the entry of a new cell `i` capped at a grid point `ω * b + k` at most some value of that entry
is the entry of a new cell `j` whose sheet cap from `i` is at least `ω * b + k`. -/
def ServesAgreements (S : Scheme.{u} n) (k : ℕ) (ε : Fin M → Fin S.card → Label.{u})
    (σ : Fin M → Bool) (κ : (Fin S.card → Label.{u}) → Label.{u}) : Prop :=
  ∀ i, ∀ a ∈ S.catalogue k, ∀ b : ℕ, (∃ x, gridPoint k b ≤ ε i x) →
    (∀ d, min (a d) (gridPoint k b) = min (ε i d) (gridPoint k b)) →
      ∃ j, ε j = a ∧ gridPoint k b ≤ S.sheetCap ε σ κ i j

/-- A layer with every catalogue entry an entry, and caps at least the values of their entries,
serves the capped agreements. -/
theorem servesAgreements_of_le {k : ℕ} (hκ : ∀ i x, ε i x ≤ κ (ε i))
    (hall : ∀ a ∈ S.catalogue k, ∃ j, ε j = a) : S.ServesAgreements k ε σ κ := by
  intro i a ha b ⟨x, hx⟩ _
  obtain ⟨j, hj⟩ := hall a ha
  refine ⟨j, hj, ?_⟩
  rw [sheetCap]
  split_ifs
  exacts [le_top, hx.trans (hκ i x)]

/-- **The leaf-and-marked layer serves the capped agreements** for every set of marks in the
catalogue that is marked-closed for its cap: along a leaf, by the leaf of the entry; along a marked
cell, by the leaf of the entry at a point at most its cap, and above its cap by the marked cell of
the entry, which marked closure puts in the marks. -/
theorem servesAgreements_markedLayer {k : ℕ} {Mk : Finset (Fin S.card → Label.{u})}
    (hcl : MarkedClosed S k Mk κ) :
    S.ServesAgreements k (S.markedEntry k Mk) (markedSheet _ Mk.card) κ := by
  intro i a ha b _ hag
  induction i using Fin.addCases with
  | left i =>
    obtain ⟨j, hj, hjs⟩ := exists_leaf_eq (Mk := Mk) ha
    refine ⟨j, hj, ?_⟩
    rw [sheetCap, ite_eq_left (by rw [markedSheet_castAdd, hjs])]
    exact le_top
  | right m =>
    by_cases hle : gridPoint k b ≤ κ (S.markedEntry k Mk (Fin.natAdd _ m))
    · obtain ⟨j, hj, hjs⟩ := exists_leaf_eq (Mk := Mk) ha
      refine ⟨j, hj, ?_⟩
      rw [sheetCap, ite_eq_right (by rw [markedSheet_natAdd, hjs]; decide)]
      exact hle
    · have hmk : S.markedEntry k Mk (Fin.natAdd _ m) ∈ Mk := by
        rw [markedEntry_natAdd]; exact markEntry_mem Mk m
      obtain ⟨j, hj, hjs⟩ := exists_mark_eq (k := k)
        (hcl _ hmk a ha _ (isSelfVisible_gridPoint k b) (isShort_gridPoint k b)
          (WithBot.bot_lt_coe _) hle hag)
      refine ⟨j, hj, ?_⟩
      rw [sheetCap, ite_eq_left (by rw [markedSheet_natAdd, hjs])]
      exact le_top

namespace IsMixedSite

variable (hs : S.IsMixedSite y z o r z' o' r')
include hs

/-- **The mixed entry is forced at the tops.**  In a sheet layer at grade `2` over a site, with
entries in the canonical catalogue and some new cell, serving the capped agreements, every lawful
labelling `⊤` at the four cells of grade `2` labels `⊤` a new cell whose entry reads `o'` and `r'`
strictly below every context cell. -/
theorem exists_top_lt_of_serves (hε : ∀ i, ε i ∈ S.catalogue 2) (j₀ : Fin M)
    (hserve : S.ServesAgreements 2 ε σ κ) {q : Fin (S.card + M) → Label.{u}}
    (hq : (S.sheetLayer 2 ε σ κ hS).rows.IsLawful q)
    (htop : ∀ c, (c = o ∨ c = r ∨ c = o' ∨ c = r') → q (Fin.castAdd M c) = ⊤) :
    ∃ j, q (Fin.natAdd S.card j) = ⊤ ∧
      ∀ s, (s = y ∨ s = z ∨ s = o ∨ s = r) → ε j o' < ε j s ∧ ε j r' < ε j s := by
  -- availability from `o` gives a new cell `u` labelled `⊤`
  obtain ⟨u, hu, hle⟩ := hq.availability (Fin.castAdd M o) (Fin.natAdd S.card j₀)
    (by rw [appendFullCellsScheme_scope_natAdd]; exact subset_univ _)
    (by rw [appendFullCellsScheme_grade_castAdd, appendFullCellsScheme_grade_natAdd, hs.grade_o])
  rw [htop o (.inl rfl), top_le_iff] at hle
  rw [appendFullCellsScheme_gradedIndex_natAdd] at hu
  obtain ⟨i, rfl⟩ := exists_natAdd_eq_sheetLayer hu
  set e := ε i with he_def
  obtain ⟨hel, -, hecode⟩ := mem_catalogue.mp (hε i)
  have hne (c : Fin S.card) (hc : c = o ∨ c = r ∨ c = o' ∨ c = r') : e c ≠ ⊥ :=
    ne_bot_of_eq_top hs hq hle (htop c hc)
  -- the least value of `e` at the four cells of grade `2`, a grid point `ω * b + 2`
  obtain ⟨x₀, hx₀, hmin⟩ := Finset.exists_min_image ({o, r, o', r'} : Finset (Fin S.card)) e
    ⟨o, by simp⟩
  have hx₀' : x₀ = o ∨ x₀ = r ∨ x₀ = o' ∨ x₀ = r' := by simpa using hx₀
  have hmin' (c : Fin S.card) (hc : c = o ∨ c = r ∨ c = o' ∨ c = r') : e x₀ ≤ e c :=
    hmin c (by simpa using hc)
  have hg₀ : S.toCellScheme.grade x₀ = 2 := (hs.grade_eq_two_iff x₀).mpr hx₀'
  obtain ⟨b, hb, hbx⟩ := exists_eq_gridPoint (hε i) hg₀ (hne x₀ hx₀')
  have hgb (c : Fin S.card) (hc : c = o ∨ c = r ∨ c = o' ∨ c = r') : gridPoint 2 b ≤ e c :=
    hbx ▸ hmin' c hc
  -- the mixed labelling and its code
  set g := mixedLabelling o' r' e b
  have hg : S.rows.IsLawful g := hs.isLawful_mixedLabelling hel hgb
  have hsplice : S.toCellScheme.splice 2 (fun _ ↦ ⊥) g = g :=
    funext fun d ↦ CellScheme.splice_of_le (hs.grade_le d)
  have hmem : orbitCode 2 g ∈ S.catalogue 2 := by
    have h := orbitCode_splice_bot_mem_catalogue (hg.isLawfulBelow (univ, 2))
    rwa [hsplice] at h
  obtain ⟨hoy, hoz, ho'y, ho'z'⟩ := hs.le_of_isLawful hel
  have hag (d : Fin S.card) : min (g d) (gridPoint 2 b) = min (e d) (gridPoint 2 b) := by
    by_cases hd : d = o' ∨ d = r'
    · rw [show g d = gridPoint 2 b from mixedLabelling_of_donor hd, min_self,
        min_eq_right (hgb d (.inr (.inr hd)))]
    · rw [show g d = Label.collapse _ 2 (e d) from mixedLabelling_of_not_donor hd]
      rcases le_or_gt (gridPoint 2 b) (e d) with h | h
      · rw [collapse_of_le h, min_eq_right h, min_top_left]
      · rw [Label.collapse, reduce_of_lt h]
  have hcode (d : Fin S.card) :
      min (orbitCode 2 g d) (gridPoint 2 b) = min (e d) (gridPoint 2 b) :=
    min_orbitCode_eq (isSelfVisible_gridPoint 2 b) (isShort_gridPoint 2 b) hecode hag d
  -- the cell of the code is labelled `⊤`
  obtain ⟨j, hj, hcap⟩ := hserve i _ hmem b ⟨x₀, hbx.ge⟩ hcode
  have hcross : e x₀ ≤ S.crossHeight 2 ε σ κ i j := by
    rw [show e x₀ = gridPoint 2 b from hbx, crossHeight]
    refine le_min (le_agreementHeight (gridPoint_mem_grid (by omega)) fun d ↦ ?_) hcap
    rw [hj]; exact (hcode d).symm
  have hjtop : q (Fin.natAdd S.card j) = ⊤ :=
    eq_top_natAdd_sheetLayer hq (hg₀.le) hle (htop x₀ hx₀') hcross
  refine ⟨j, hjtop, fun s hsc ↦ ?_⟩
  -- the code keeps the order of the keys: `⊤` at the context cells, `ω * b + 2` at `o'`, `r'`
  have hgs : g s = ⊤ := by
    rw [show g s = Label.collapse _ 2 (e s) from mixedLabelling_of_not_donor (hs.not_donor hsc)]
    refine collapse_of_le ?_
    rcases hsc with rfl | rfl | rfl | rfl
    exacts [(hgb o (.inl rfl)).trans hoy, (hgb o (.inl rfl)).trans hoz, hgb _ (.inl rfl),
      hgb _ (.inr (.inl rfl))]
  have hlt (d : Fin S.card) (hd : d = o' ∨ d = r') : orbitCode 2 g d < orbitCode 2 g s := by
    have hgd : g d = gridPoint 2 b := mixedLabelling_of_donor hd
    refine lt_of_not_ge fun hle' ↦ ?_
    have h1 := monotone_visibilityReplace (k := 2) le_rfl hle'
    rw [visibilityReplace_orbitCode_le_iff (hgd ▸ WithBot.coe_ne_bot) (hgs ▸ top_ne_bot), hgs,
      hgd, visibilityReplace_top, isSelfVisible_gridPoint 2 b, top_le_iff] at h1
    exact ne_top_of_mem_codeGrid (grid_subset_codeGrid 2 b (gridPoint_mem_grid le_rfl)) h1
  rw [hj]
  exact ⟨hlt o' (.inl rfl), hlt r' (.inr rfl)⟩

/-- **The mixed entry is forced at the tops**, for a layer with every catalogue entry an entry and
caps at least the values of their entries. -/
theorem exists_top_lt (hε : ∀ i, ε i ∈ S.catalogue 2) (hκ : ∀ i x, ε i x ≤ κ (ε i))
    (hall : ∀ a ∈ S.catalogue 2, ∃ j, ε j = a) {q : Fin (S.card + M) → Label.{u}}
    (hq : (S.sheetLayer 2 ε σ κ hS).rows.IsLawful q)
    (htop : ∀ c, (c = o ∨ c = r ∨ c = o' ∨ c = r') → q (Fin.castAdd M c) = ⊤) :
    ∃ j, q (Fin.natAdd S.card j) = ⊤ ∧
      ∀ s, (s = y ∨ s = z ∨ s = o ∨ s = r) → ε j o' < ε j s ∧ ε j r' < ε j s :=
  hs.exists_top_lt_of_serves hε (hall _ (orbitCode_splice_bot_mem_catalogue (S := S) (k := 2)
    (p := fun _ ↦ ⊥) (CellScheme.Rows.isLawfulBelow_const_bot _))).choose
    (servesAgreements_of_le hκ hall) hq htop

end IsMixedSite

/-! ### Layers of grade one over a site -/

section Append

variable {M : ℕ} {rr : Fin M → Fin (S.card + M) → Label.{u}}
  {h1 : ∀ d, ¬ ((univ : Finset (Fin n)), 1) ≤ S.toCellScheme.gradedIndex d}

/-- Old cells are read after appending cells of full scope as before. -/
theorem rowAt_appendFullCells_castAdd (c d : Fin S.card) :
    (S.appendFullCells 1 M rr h1).rowAt (Fin.castAdd M c) (Fin.castAdd M d) = S.rowAt c d := by
  have hiff : Fin.castAdd M d ∈ (S.appendFullCells 1 M rr h1).toCellScheme.below
      ((S.appendFullCells 1 M rr h1).toCellScheme.gradedIndex (Fin.castAdd M c)) ↔
      d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex c) := by
    rw [CellScheme.mem_below, CellScheme.mem_below, appendFullCellsScheme_gradedIndex_castAdd,
      appendFullCellsScheme_gradedIndex_castAdd]
  by_cases hd : d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex c)
  · rw [rowAt_of_mem (hiff.mpr hd), rowAt_of_mem hd, appendFullCells_row_castAdd]
    exact S.rows.row_congr rfl rfl
  · rw [rowAt_of_notMem (mt hiff.mp hd), rowAt_of_notMem hd]

/-- An old cell does not read a new cell of full scope. -/
theorem rowAt_appendFullCells_natAdd (c : Fin S.card) (i : Fin M) :
    (S.appendFullCells 1 M rr h1).rowAt (Fin.castAdd M c) (Fin.natAdd S.card i) = ⊥ := by
  refine rowAt_of_notMem fun h ↦ h1 c ?_
  rw [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_natAdd,
    appendFullCellsScheme_gradedIndex_castAdd] at h
  exact h

private theorem natAdd_ne_castAdd (i : Fin M) (x : Fin S.card) :
    Fin.natAdd S.card i ≠ Fin.castAdd M x := fun h ↦ by
  have := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at this
  omega

/-- **A site stays a site after appending cells of full scope and grade `1`.** -/
theorem IsMixedSite.appendFullCells (hs : S.IsMixedSite y z o r z' o' r') :
    (S.appendFullCells 1 M rr h1).IsMixedSite (Fin.castAdd M y) (Fin.castAdd M z)
      (Fin.castAdd M o) (Fin.castAdd M r) (Fin.castAdd M z') (Fin.castAdd M o')
      (Fin.castAdd M r') := by
  have hinj (a b : Fin S.card) : Fin.castAdd M a = Fin.castAdd M b ↔ a = b :=
    (Fin.castAdd_injective S.card M).eq_iff
  refine ⟨fun d ↦ ?_, fun d ↦ ?_, ?_, ?_, fun c hc d ↦ ?_, fun c hc d ↦ ?_, ?_, ?_, ?_, ?_,
    fun s t hs' ht' ↦ ?_⟩
  · induction d using Fin.addCases with
    | left d => rw [appendFullCellsScheme_grade_castAdd]; exact hs.grade_le d
    | right i => rw [appendFullCellsScheme_grade_natAdd]; omega
  · induction d using Fin.addCases with
    | left d =>
      rw [appendFullCellsScheme_grade_castAdd, hs.grade_eq_two_iff, hinj, hinj, hinj, hinj]
    | right i =>
      rw [appendFullCellsScheme_grade_natAdd]
      simp only [natAdd_ne_castAdd, OfNat.one_ne_ofNat, or_self]
  · rw [appendFullCellsScheme_grade_castAdd]; exact hs.grade_y
  · rw [appendFullCellsScheme_grade_castAdd]; exact hs.grade_z
  · obtain ⟨c', rfl, hc'⟩ : ∃ c', Fin.castAdd M c' = c ∧ (c' = o ∨ c' = r) := by
      rcases hc with rfl | rfl
      exacts [⟨o, rfl, .inl rfl⟩, ⟨r, rfl, .inr rfl⟩]
    induction d using Fin.addCases with
    | left d => rw [rowAt_appendFullCells_castAdd, hs.rowAt_context c' hc', hinj, hinj, hinj, hinj]
    | right i => simp only [rowAt_appendFullCells_natAdd, ne_eq, not_true_eq_false,
        natAdd_ne_castAdd, or_self]
  · obtain ⟨c', rfl, hc'⟩ : ∃ c', Fin.castAdd M c' = c ∧ (c' = o' ∨ c' = r') := by
      rcases hc with rfl | rfl
      exacts [⟨o', rfl, .inl rfl⟩, ⟨r', rfl, .inr rfl⟩]
    induction d using Fin.addCases with
    | left d => rw [rowAt_appendFullCells_castAdd, hs.rowAt_donor c' hc', hinj, hinj, hinj, hinj]
    | right i => simp only [rowAt_appendFullCells_natAdd, ne_eq, not_true_eq_false,
        natAdd_ne_castAdd, or_self]
  · rw [rowAt_appendFullCells_castAdd, rowAt_appendFullCells_castAdd]; exact hs.rowAt_o_le_y
  · rw [rowAt_appendFullCells_castAdd, rowAt_appendFullCells_castAdd]; exact hs.rowAt_o_le_z
  · rw [rowAt_appendFullCells_castAdd, rowAt_appendFullCells_castAdd]; exact hs.rowAt_o'_le_y
  · rw [rowAt_appendFullCells_castAdd, rowAt_appendFullCells_castAdd]; exact hs.rowAt_o'_le_z'
  · obtain ⟨s', rfl, hs''⟩ : ∃ s', Fin.castAdd M s' = s ∧ (s' = o ∨ s' = r) := by
      rcases hs' with rfl | rfl
      exacts [⟨o, rfl, .inl rfl⟩, ⟨r, rfl, .inr rfl⟩]
    obtain ⟨t', rfl, ht''⟩ : ∃ t', Fin.castAdd M t' = t ∧ (t' = o' ∨ t' = r') := by
      rcases ht' with rfl | rfl
      exacts [⟨o', rfl, .inl rfl⟩, ⟨r', rfl, .inr rfl⟩]
    rw [appendFullCellsScheme_scope_castAdd, appendFullCellsScheme_scope_castAdd]
    exact hs.not_scope_subset s' t' hs'' ht''

end Append

/-- The row of a new cell of a sheet layer at grade `2` over a site at an old cell is its entry. -/
theorem IsMixedSite.rowAt_natAdd_castAdd (hs : S.IsMixedSite y z o r z' o' r') {M : ℕ}
    {ε : Fin M → Fin S.card → Label.{u}} {σ : Fin M → Bool}
    {κ : (Fin S.card → Label.{u}) → Label.{u}}
    {hS : ∀ d, ¬ ((univ : Finset (Fin n)), 2) ≤ S.toCellScheme.gradedIndex d} (j : Fin M)
    (x : Fin S.card) :
    (S.sheetLayer 2 ε σ κ hS).rowAt (Fin.natAdd S.card j) (Fin.castAdd M x) = ε j x := by
  rw [rowAt_of_mem (old_mem_below_new hs x j), sheetLayer_row_natAdd, sheetRow_castAdd]

/-- **No context cell is read as low as `o'` at the tops**: in a layer as in
`Scheme.IsMixedSite.exists_top_lt_of_serves`, no context cell `s` is read at most as `o'` by every
new cell labelled `⊤`. -/
theorem IsMixedSite.not_exists_reading (hs : S.IsMixedSite y z o r z' o' r') {M : ℕ}
    {ε : Fin M → Fin S.card → Label.{u}} {σ : Fin M → Bool}
    {κ : (Fin S.card → Label.{u}) → Label.{u}}
    {hS : ∀ d, ¬ ((univ : Finset (Fin n)), 2) ≤ S.toCellScheme.gradedIndex d}
    (hε : ∀ i, ε i ∈ S.catalogue 2) (j₀ : Fin M) (hserve : S.ServesAgreements 2 ε σ κ)
    {q : Fin (S.card + M) → Label.{u}} (hq : (S.sheetLayer 2 ε σ κ hS).rows.IsLawful q)
    (htop : ∀ c, (c = o ∨ c = r ∨ c = o' ∨ c = r') → q (Fin.castAdd M c) = ⊤) :
    ¬ ∃ s, (s = y ∨ s = z ∨ s = o ∨ s = r) ∧ ∀ j, q (Fin.natAdd S.card j) = ⊤ →
      (S.sheetLayer 2 ε σ κ hS).rowAt (Fin.natAdd S.card j) (Fin.castAdd M s) ≤
        (S.sheetLayer 2 ε σ κ hS).rowAt (Fin.natAdd S.card j) (Fin.castAdd M o') := by
  rintro ⟨s, hsc, hread⟩
  obtain ⟨j, hj, hlt⟩ := hs.exists_top_lt_of_serves hε j₀ hserve hq htop
  have h := hread j hj
  rw [hs.rowAt_natAdd_castAdd, hs.rowAt_natAdd_castAdd] at h
  exact (hlt s hsc).1.not_ge h

/-- `Scheme.IsMixedSite.not_exists_reading` for a layer of cells of full scope whose rows are equal
to sheet rows. -/
theorem IsMixedSite.not_exists_reading_of_eq (hs : S.IsMixedSite y z o r z' o' r') {M : ℕ}
    {ε : Fin M → Fin S.card → Label.{u}} {σ : Fin M → Bool}
    {κ : (Fin S.card → Label.{u}) → Label.{u}}
    {hS : ∀ d, ¬ ((univ : Finset (Fin n)), 2) ≤ S.toCellScheme.gradedIndex d}
    (hε : ∀ i, ε i ∈ S.catalogue 2) (j₀ : Fin M) (hserve : S.ServesAgreements 2 ε σ κ)
    {rr : Fin M → Fin (S.card + M) → Label.{u}} (hrr : rr = S.sheetRow 2 ε σ κ)
    {q : Fin (S.card + M) → Label.{u}}
    (hq : (S.appendFullCells 2 M rr hS).rows.IsLawful q)
    (htop : ∀ c, (c = o ∨ c = r ∨ c = o' ∨ c = r') → q (Fin.castAdd M c) = ⊤) :
    ¬ ∃ s, (s = y ∨ s = z ∨ s = o ∨ s = r) ∧ ∀ j, q (Fin.natAdd S.card j) = ⊤ →
      (S.appendFullCells 2 M rr hS).rowAt (Fin.natAdd S.card j) (Fin.castAdd M s) ≤
        (S.appendFullCells 2 M rr hS).rowAt (Fin.natAdd S.card j) (Fin.castAdd M o') := by
  subst hrr
  exact hs.not_exists_reading hε j₀ hserve hq htop

/-- **The field rows are the sheet rows with one sheet** of the catalogue entries, at every cap. -/
theorem fieldRow_eq_sheetRow {k : ℕ} (κ : (Fin S.card → Label.{u}) → Label.{u}) :
    (fun i ↦ S.fieldRow k (S.catalogueEntry k i)) =
      S.sheetRow k (S.catalogueEntry k) (fun _ ↦ false) κ := by
  funext i x
  induction x using Fin.addCases with
  | left d => rw [fieldRow_castAdd, sheetRow_castAdd]
  | right j =>
    rw [sheetRow_natAdd, crossHeight_of_eq (σ := fun _ ↦ false) rfl]
    exact Fin.append_right _ _ j

/-- **The canonical field layer is the sheet layer with one sheet** of the catalogue entries, at
every cap. -/
theorem fieldLayer_eq_sheetLayer {k : ℕ}
    (hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d)
    (κ : (Fin S.card → Label.{u}) → Label.{u}) :
    S.fieldLayer k hS = S.sheetLayer k (S.catalogueEntry k) (fun _ ↦ false) κ hS :=
  congrArg (fun rr ↦ S.appendFullCells k _ rr hS) (fieldRow_eq_sheetRow κ)

end Scheme
/-! ### The amalgam of two copies of the input `T` -/

namespace MixedEntry

open SeparationObstruction SeparatedInstance

/-- The cells on `Fin 3` of the amalgam of two copies of `SeparationObstruction.T` over `{0}`:
`y` (`0`, scope `{0}`), the dead cells `e` (`1`, `{1}`) and `e'` (`5`, `{2}`), `z` (`2`) and `z'`
(`6`) of grade `1`, `o`, `r` (`3`, `4`, scope `{0, 1}`) and `o'`, `r'` (`7`, `8`, scope `{0, 2}`) of
grade `2`. -/
def cells : CellScheme (Fin 9) (Fin 3) :=
  ⟨univ, {∅, {0}, {1}, {2}, {0, 1}, {0, 2}},
    ![{0}, {1}, {0, 1}, {0, 1}, {0, 1}, {2}, {0, 2}, {0, 2}, {0, 2}], ![1, 1, 1, 2, 2, 1, 1, 2, 2]⟩

/-- The kinds of row values: `⊥`, `2`, `ω + 2`. -/
noncomputable def kindLabel : Fin 3 → Label.{u} := ![⊥, low, omegaAddTwo]

/-- The kinds of the rows: those of `SeparationObstruction.T` on each copy, `⊥` across the copies;
as there, values at cells not below the reading cell are never read. -/
def rowKind : Fin 9 → Fin 9 → Fin 3 :=
  ![![1, 0, 1, 0, 0, 0, 1, 0, 0], fun _ ↦ 0, ![1, 0, 1, 0, 0, 0, 0, 0, 0],
    ![2, 0, 2, 2, 1, 0, 0, 0, 0], ![1, 0, 1, 1, 2, 0, 0, 0, 0], fun _ ↦ 0,
    ![1, 0, 0, 0, 0, 0, 1, 0, 0], ![2, 0, 0, 0, 0, 0, 2, 2, 1], ![1, 0, 0, 0, 0, 0, 1, 1, 2]]

/-- The rows (`MixedEntry.rowValue_context`, `MixedEntry.rowValue_donor`). -/
noncomputable def rowValue (s d : Fin 9) : Label.{u} := kindLabel (rowKind s d)

/-- The amalgam, as a scheme on three points. -/
noncomputable abbrev A : Scheme.{u} 3 := ⟨9, cells, ⟨fun s d ↦ rowValue s d.1⟩⟩

/-- The cells `0, 1, 2, 3, 4` of the amalgam carry the rows of `SeparationObstruction.T`. -/
theorem rowValue_context (s d : Fin 5) :
    rowValue.{u} (Fin.castLE (by omega) s) (Fin.castLE (by omega) d) =
      SeparationObstruction.rowValue s d := by
  fin_cases s <;> fin_cases d <;> rfl

/-- The cells `0, 5, 6, 7, 8` of the amalgam carry the rows of `SeparationObstruction.T`. -/
theorem rowValue_donor (s d : Fin 5) :
    rowValue.{u} (![0, 5, 6, 7, 8] s) (![0, 5, 6, 7, 8] d) =
      SeparationObstruction.rowValue s d := by
  fin_cases s <;> fin_cases d <;> rfl

/-- No cell of the amalgam has full scope. -/
theorem not_univ_le (j : ℕ) (d : Fin A.{u}.card) :
    ¬ ((univ : Finset (Fin 3)), j) ≤ A.{u}.toCellScheme.gradedIndex d := fun h ↦ by
  have key : ∀ d : Fin 9, cells.scope d ≠ univ := by decide
  exact key d (univ_subset_iff.mp h.1)

/-- The row of `c` read at `d`. -/
theorem rowAt_A (c d : Fin 9) :
    A.{u}.rowAt c d =
      kindLabel (if cells.gradedIndex d ≤ cells.gradedIndex c then rowKind c d else 0) := by
  by_cases h : cells.gradedIndex d ≤ cells.gradedIndex c
  · rw [Scheme.rowAt_of_mem h, ite_eq_left h]; rfl
  · rw [Scheme.rowAt_of_notMem h, ite_eq_right h]; rfl

/-- A kind is read other than at `⊥` exactly when it is not `0`. -/
theorem kindLabel_ne_bot_iff (k : Fin 3) : kindLabel.{u} k ≠ ⊥ ↔ k ≠ 0 := by
  fin_cases k
  · simp [kindLabel]
  · exact iff_of_true WithBot.coe_ne_bot (by decide)
  · exact iff_of_true WithBot.coe_ne_bot (by decide)

/-- **The amalgam is a site of the mixed labelling**: context `y, z, o, r = 0, 2, 3, 4`, donor
`z', o', r' = 6, 7, 8`. -/
theorem isMixedSite_A : A.{u}.IsMixedSite 0 2 3 4 6 7 8 := by
  refine ⟨fun d ↦ ?_, fun d ↦ ?_, by decide, by decide, fun c hc d ↦ ?_, fun c hc d ↦ ?_,
    ?_, ?_, ?_, ?_, fun s t hs ht ↦ ?_⟩
  · revert d; decide
  · revert d; decide
  · rw [rowAt_A, kindLabel_ne_bot_iff]
    rcases hc with rfl | rfl <;> revert d <;> decide
  · rw [rowAt_A, kindLabel_ne_bot_iff]
    rcases hc with rfl | rfl <;> revert d <;> decide
  any_goals (rw [rowAt_A, rowAt_A]; exact le_of_eq (congrArg kindLabel (by decide)))
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> decide

/-! ### The completions at the arity one over the amalgam -/

section Completion

variable {M₁ : ℕ} {rr : Fin M₁ → Fin (A.{u}.card + M₁) → Label.{u}}

/-- The site in any layer of cells of full scope and grade `1` over the amalgam. -/
theorem isMixedSite_appendFullCells :
    (A.{u}.appendFullCells 1 M₁ rr (not_univ_le.{u} 1)).IsMixedSite (Fin.castAdd M₁ 0)
      (Fin.castAdd M₁ 2) (Fin.castAdd M₁ 3) (Fin.castAdd M₁ 4) (Fin.castAdd M₁ 6)
      (Fin.castAdd M₁ 7) (Fin.castAdd M₁ 8) :=
  isMixedSite_A.{u}.appendFullCells

/-- **The leaf-and-marked completion does not read `o'` at its tops.**  Over any layer of cells of
full scope and grade `1` over the amalgam (the leaf-and-marked layer with any marks and caps, or
the canonical field layer), in the leaf-and-marked layer at grade `2` with any marks in the
catalogue and any cap for which they are marked-closed (`Scheme.MarkedClosed`; the ceiling cap
with any marks, `Scheme.markedClosed_ceilingCap`), every lawful labelling `⊤` at `o`, `r`, `o'`,
`r'` labels `⊤` a cell of full scope and grade `2` reading `o'` strictly below each of `y`, `z`,
`o`, `r`. -/
theorem not_exists_reading_markedLayer
    (Mk : Finset (Fin (A.{u}.appendFullCells 1 M₁ rr (not_univ_le.{u} 1)).card → Label.{u}))
    (hMk : Mk ⊆ (A.{u}.appendFullCells 1 M₁ rr (not_univ_le.{u} 1)).catalogue 2)
    {κ : (Fin (A.{u}.appendFullCells 1 M₁ rr (not_univ_le.{u} 1)).card → Label.{u}) → Label.{u}}
    (hcl : (A.{u}.appendFullCells 1 M₁ rr (not_univ_le.{u} 1)).MarkedClosed 2 Mk κ)
    {hS : ∀ d, ¬ ((univ : Finset (Fin 3)), 2) ≤
      (A.{u}.appendFullCells 1 M₁ rr (not_univ_le.{u} 1)).toCellScheme.gradedIndex d}
    {q : Fin _ → Label.{u}}
    (hq : ((A.{u}.appendFullCells 1 M₁ rr (not_univ_le.{u} 1)).markedLayer 2 Mk κ
      hS).rows.IsLawful q)
    (htop : ∀ c : Fin 9, (c = 3 ∨ c = 4 ∨ c = 7 ∨ c = 8) →
      q (Fin.castAdd _ (Fin.castAdd M₁ c)) = ⊤) :
    ¬ ∃ s : Fin 9, (s = 0 ∨ s = 2 ∨ s = 3 ∨ s = 4) ∧ ∀ j, q (Fin.natAdd _ j) = ⊤ →
      ((A.{u}.appendFullCells 1 M₁ rr (not_univ_le.{u} 1)).markedLayer 2 Mk κ hS).rowAt
          (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd M₁ s)) ≤
      ((A.{u}.appendFullCells 1 M₁ rr (not_univ_le.{u} 1)).markedLayer 2 Mk κ hS).rowAt
          (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd M₁ 7)) := by
  rintro ⟨s, hsc, hread⟩
  refine (isMixedSite_appendFullCells.{u} (M₁ := M₁) (rr := rr)).not_exists_reading
    (Scheme.markedEntry_mem hMk)
    (Scheme.exists_leaf_eq (Mk := Mk) (Scheme.orbitCode_splice_bot_mem_catalogue
      (p := fun _ ↦ ⊥) (CellScheme.Rows.isLawfulBelow_const_bot _))).choose
    (Scheme.servesAgreements_markedLayer hcl) hq (fun c hc ↦ ?_) ⟨Fin.castAdd M₁ s, ?_, hread⟩
  · obtain ⟨c', rfl, hc'⟩ : ∃ c' : Fin 9, Fin.castAdd M₁ c' = c ∧
        (c' = 3 ∨ c' = 4 ∨ c' = 7 ∨ c' = 8) := by
      rcases hc with rfl | rfl | rfl | rfl
      exacts [⟨3, rfl, .inl rfl⟩, ⟨4, rfl, .inr (.inl rfl)⟩, ⟨7, rfl, .inr (.inr (.inl rfl))⟩,
        ⟨8, rfl, .inr (.inr (.inr rfl))⟩]
    exact htop c' hc'
  · rcases hsc with rfl | rfl | rfl | rfl
    exacts [.inl rfl, .inr (.inl rfl), .inr (.inr (.inl rfl)), .inr (.inr (.inr rfl))]

/-- **The canonical completion does not read `o'` at its tops**: as
`MixedEntry.not_exists_reading_markedLayer`, for the canonical field layer at grade `2` (the layer
at grade two of `Seed.fieldLayerOne` over its lower layer). -/
theorem not_exists_reading_fieldLayer
    {hS : ∀ d, ¬ ((univ : Finset (Fin 3)), 2) ≤
      (A.{u}.appendFullCells 1 M₁ rr (not_univ_le.{u} 1)).toCellScheme.gradedIndex d}
    {q : Fin _ → Label.{u}}
    (hq : ((A.{u}.appendFullCells 1 M₁ rr (not_univ_le.{u} 1)).fieldLayer 2 hS).rows.IsLawful q)
    (htop : ∀ c : Fin 9, (c = 3 ∨ c = 4 ∨ c = 7 ∨ c = 8) →
      q (Fin.castAdd _ (Fin.castAdd M₁ c)) = ⊤) :
    ¬ ∃ s : Fin 9, (s = 0 ∨ s = 2 ∨ s = 3 ∨ s = 4) ∧ ∀ j, q (Fin.natAdd _ j) = ⊤ →
      ((A.{u}.appendFullCells 1 M₁ rr (not_univ_le.{u} 1)).fieldLayer 2 hS).rowAt (Fin.natAdd _ j)
          (Fin.castAdd _ (Fin.castAdd M₁ s)) ≤
      ((A.{u}.appendFullCells 1 M₁ rr (not_univ_le.{u} 1)).fieldLayer 2 hS).rowAt (Fin.natAdd _ j)
          (Fin.castAdd _ (Fin.castAdd M₁ 7)) := by
  rintro ⟨s, hsc, hread⟩
  refine (isMixedSite_appendFullCells.{u} (M₁ := M₁) (rr := rr)).not_exists_reading_of_eq
    (fun i ↦ Scheme.catalogueEntry_mem i)
    (Scheme.exists_catalogueEntry_eq (Scheme.orbitCode_splice_bot_mem_catalogue
      (p := fun _ ↦ ⊥) (CellScheme.Rows.isLawfulBelow_const_bot _))).choose
    (Scheme.servesAgreements_of_le (fun _ _ ↦ le_top) fun a ha ↦ Scheme.exists_catalogueEntry_eq ha)
    (Scheme.fieldRow_eq_sheetRow fun _ ↦ ⊤) hq
    (fun c hc ↦ ?_) ⟨Fin.castAdd M₁ s, ?_, hread⟩
  · obtain ⟨c', rfl, hc'⟩ : ∃ c' : Fin 9, Fin.castAdd M₁ c' = c ∧
        (c' = 3 ∨ c' = 4 ∨ c' = 7 ∨ c' = 8) := by
      rcases hc with rfl | rfl | rfl | rfl
      exacts [⟨3, rfl, .inl rfl⟩, ⟨4, rfl, .inr (.inl rfl)⟩, ⟨7, rfl, .inr (.inr (.inl rfl))⟩,
        ⟨8, rfl, .inr (.inr (.inr rfl))⟩]
    exact htop c' hc'
  · rcases hsc with rfl | rfl | rfl | rfl
    exacts [.inl rfl, .inr (.inl rfl), .inr (.inr (.inl rfl)), .inr (.inr (.inr rfl))]

end Completion

end MixedEntry

end VaughtConjecture
