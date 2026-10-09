/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapMixedSeed
import VaughtConjecture.Continuation.SourceGapTwistedDonor

/-!
# The twisted entry is forced at the tops of a full-catalogue layer, and the LOW admission

Roadmap, Layer 3 ((R2) of the table of 3.4, the coatom step for a donor other than the context);
the mixed entry of `VaughtConjecture.Continuation.SourceGapMixedEntry` and the twisted donor of
`VaughtConjecture.Continuation.SourceGapTwistedDonor`.

**The twisted seed.**  The input `SeparationObstruction.T α` (labels `(⊤, ⊥, ⊤, ⊤, ⊤)`) with the
donor `TwistedDonor.Utop` (the same scheme, labels `(⊤, ⊥, ⊤, ⊤, v)`), over the face `{0}`
(`TwistedDonor.seedU`).  For `v ≠ ⊤` the donor is not the context, its copy `r'` of the lost top is
not `⊤`, and its new top `o'` is not forced by a root top (so
`StageType.exists_coatomStep_of_forall_unique` does not apply).  The amalgam of the twisted seed
has the scheme of the amalgam of the input with itself (`TwistedDonor.amalgam_seedU`, through
`TwistedDonor.amalgam_congr`, without unfolding the cardinalities), so its completion at the arity
one has the scheme `(MixedSeed.I α).fieldLayerOne` (`TwistedDonor.fieldLayerOne_seedU`).

**(b) The full-catalogue completion does not read `o'` at its tops** (compiled in this repository).
* `Scheme.twistedLabelling o' r' e b`: `ω * b + 2` at `o'`, `min (e r') (ω * b + 2)` at `r'`, the
  collapse of `e` above `ω * b + 2` elsewhere; lawful for a lawful `e` at least `ω * b + 2` at `o`,
  `r`, `o'`, with **no condition at `r'`** (`Scheme.IsMixedSite.isLawful_twistedLabelling`).
* `Scheme.IsMixedSite.exists_top_lt_of_serves_twisted`: in a sheet layer at grade `2` serving the
  capped agreements, every lawful labelling `⊤` at `o`, `r`, `o'` labels `⊤` a new cell reading `o'`
  strictly below `y`, `z`, `o`, `r` (the forcing of `Scheme.IsMixedSite.exists_top_lt_of_serves`,
  with the least value taken over `o`, `r`, `o'` only).
* At the seed: `MixedSeed.not_exists_reading_fieldLayerOne_twisted` and
  `MixedSeed.exists_top_lt_fieldLayerOne_twisted`; with the glued labelling of the twisted seed
  (`TwistedDonor.isLawful_gluedU`, `TwistedDonor.gluedU_values`: `⊤` at `o`, `r`, `o'`, `v` at
  `r'`), every lawful labelling of the completion extending it, among them the completion's own
  labelling (`TwistedDonor.exists_extension_gluedU`), fails the reading at the tops
  (`TwistedDonor.not_exists_reading_of_extends`).  So the doubling is not the only design that
  breaks for a twist: the full catalogue breaks too, whatever the label of `r'`.

**B-T3 at the twisted seed: the LOW admission** (`TwistedDonor.LowAdmitted α st b`), on states of
the cells of the amalgam with a cutoff `b`: the designated donor cells are `z'`, `e'`, `o'`,
`r'`; the tops `z'`, `o'`; the frontier `min (st o) (R₂ (st r))`; if `max (st e') (st r') < b`
then every designated top is at least `max b frontier`.
* (i) `TwistedDonor.not_lowAdmitted_of_lt`: a state reading `o'` strictly below `o` and `r` is not
  admitted at any cutoff above its non-top donor values; `TwistedDonor.exists_not_lowAdmitted_row`:
  the offending rows of the full-catalogue completion are such states.  The glued state is admitted
  at every cutoff (`TwistedDonor.lowAdmitted_glued`).
* (ii) `TwistedDonor.eq_top_of_forall_lowAdmitted`: for **every** completion below the full grade of
  the seed, a lawful labelling with `o`, `r` at `⊤` in which every cell of full scope and grade `2`
  labelled `⊤` has an admitted state (at a cutoff above its non-top donor values) has `o'` at `⊤`.
  `TwistedDonor.not_forall_lowAdmitted`: the full-catalogue completion carries a lawful labelling
  (`TwistedDonor.exists_twisted_extension`: context at `⊤`, `o'` at `ω * b₀ + 2`) violating that
  hypothesis at every cutoff above its value at `r'`.

Not compiled here: a completion whose rows at the grade `2` are restricted to admitted states (its
legality, in particular bountifulness, is the open clause of the admission design that provides
admitted entries to the lifts), and the recognition step from admitted rows to admitted states of
lawful labellings.  The determination from the admission asks the admission of the states, which is
what recognition is to provide.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label
open scoped Ordinal

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {y z o r z' o' r' : Fin S.card}

variable (o' r') in
/-- The **twisted labelling** of `e` at the block `b`: the grid point `h = ω * b + 2` at `o'`,
`min (e r') h` at `r'`, and elsewhere the collapse of `e` above `h`. -/
noncomputable def twistedLabelling (e : Fin S.card → Label.{u}) (b : ℕ) :
    Fin S.card → Label.{u} :=
  fun d ↦ if d = o' then gridPoint 2 b else if d = r' then min (e r') (gridPoint 2 b)
    else Label.collapse (ω * (b : Ordinal.{u})) 2 (e d)

theorem twistedLabelling_o' {e : Fin S.card → Label.{u}} {b : ℕ} :
    twistedLabelling o' r' e b o' = gridPoint 2 b := ite_eq_left rfl

theorem twistedLabelling_r' {e : Fin S.card → Label.{u}} {b : ℕ} (hb : gridPoint 2 b ≤ e o') :
    twistedLabelling o' r' e b r' = min (e r') (gridPoint 2 b) := by
  by_cases h : r' = o'
  · subst h
    rw [twistedLabelling_o', min_eq_right hb]
  · rw [twistedLabelling, ite_eq_right h, ite_eq_left rfl]

theorem twistedLabelling_of_ne {e : Fin S.card → Label.{u}} {b : ℕ} {d : Fin S.card}
    (h₁ : d ≠ o') (h₂ : d ≠ r') :
    twistedLabelling o' r' e b d = Label.collapse (ω * (b : Ordinal.{u})) 2 (e d) := by
  rw [twistedLabelling, ite_eq_right h₁, ite_eq_right h₂]

/-- The collapse above `h` is at least the value capped at `h`. -/
theorem min_le_collapse (b : ℕ) (x : Label.{u}) :
    min x (gridPoint 2 b) ≤ Label.collapse (ω * (b : Ordinal.{u})) 2 x := by
  rcases le_or_gt (gridPoint 2 b) x with h | h
  · rw [collapse_of_le h]; exact le_top
  · rw [Label.collapse, reduce_of_lt h]; exact min_le_left _ _

/-- The start `ω * b` of a block is zero or a limit. -/
private theorem isSuccPrelimit_block' (b : ℕ) : Order.IsSuccPrelimit (ω * (b : Ordinal.{u})) :=
  Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right ω _)


namespace IsMixedSite

variable (hs : S.IsMixedSite y z o r z' o' r')
include hs

/-- **The twisted labelling agrees with `e` capped at `h`.** -/
theorem min_twistedLabelling {e : Fin S.card → Label.{u}} {b : ℕ} (hb : gridPoint 2 b ≤ e o')
    (d : Fin S.card) :
    min (twistedLabelling o' r' e b d) (gridPoint 2 b) = min (e d) (gridPoint 2 b) := by
  by_cases h₁ : d = o'
  · subst h₁
    rw [twistedLabelling_o', min_self, min_eq_right hb]
  by_cases h₂ : d = r'
  · subst h₂
    rw [twistedLabelling_r' hb, min_assoc, min_self]
  rw [twistedLabelling_of_ne h₁ h₂]
  rcases le_or_gt (gridPoint 2 b) (e d) with h | h
  · rw [collapse_of_le h, min_eq_right h, min_top_left]
  · rw [Label.collapse, reduce_of_lt h]

/-- **The twisted labelling is lawful** for a lawful labelling `e` at least `h = ω * b + 2` at `o`,
`r`, `o'` (with no condition at `r'`). -/
theorem isLawful_twistedLabelling {e : Fin S.card → Label.{u}} (he : S.rows.IsLawful e) {b : ℕ}
    (hb : ∀ c, (c = o ∨ c = r ∨ c = o') → gridPoint 2 b ≤ e c) :
    S.rows.IsLawful (twistedLabelling o' r' e b) := by
  set g := twistedLabelling o' r' e b with hg_def
  obtain ⟨hoy, hoz, ho'y, ho'z'⟩ := hs.le_of_isLawful he
  have hbo' := hb o' (.inr (.inr rfl))
  have hctx (d : Fin S.card) (hd : d = y ∨ d = z ∨ d = o ∨ d = r) : gridPoint 2 b ≤ e d := by
    have ho := hb o (.inl rfl)
    rcases hd with rfl | rfl | rfl | rfl
    exacts [ho.trans hoy, ho.trans hoz, ho, hb _ (.inr (.inl rfl))]
  have hne (c : Fin S.card) (hc : c = o ∨ c = r ∨ c = o') : e c ≠ ⊥ := fun h ↦ by
    have h' := hb c hc
    rw [h, le_bot_iff] at h'
    exact WithBot.coe_ne_bot h'
  have hrow (c : Fin S.card) (d : S.toCellScheme.below (S.toCellScheme.gradedIndex c)) :
      S.rows.row c d = S.rowAt c d := (rowAt_of_mem d.2).symm
  have hg_o' : g o' = gridPoint 2 b := twistedLabelling_o'
  have hg_r' : g r' = min (e r') (gridPoint 2 b) := twistedLabelling_r' hbo'
  have hg_ne (d : Fin S.card) (h₁ : d ≠ o') (h₂ : d ≠ r') :
      g d = Label.collapse (ω * (b : Ordinal.{u})) 2 (e d) := twistedLabelling_of_ne h₁ h₂
  have hag (d : Fin S.card) : min (g d) (gridPoint 2 b) = min (e d) (gridPoint 2 b) :=
    hs.min_twistedLabelling hbo' d
  -- the context cells are `⊤`
  have hg_ctx (d : Fin S.card) (hd : d = y ∨ d = z ∨ d = o ∨ d = r) : g d = ⊤ := by
    have hnd := hs.not_donor hd
    rw [hg_ne d (fun h ↦ hnd (.inl h)) (fun h ↦ hnd (.inr h)), collapse_of_le (hctx d hd)]
  have hg_bot (d : Fin S.card) (hd : e d = ⊥) : g d = ⊥ := by
    by_cases h₁ : d = o'
    · exact absurd hd (hne d (.inr (.inr h₁)))
    by_cases h₂ : d = r'
    · rw [h₂, hg_r', ← h₂, hd, min_eq_left bot_le]
    · rw [hg_ne d h₁ h₂, hd, collapse_bot]
  have hdon (c : Fin S.card) (hc : c = o' ∨ c = r') :
      IsSelfVisible 2 (g c) ∧ g c ≤ gridPoint 2 b ∧ g c ≤ e c := by
    rcases hc with rfl | rfl
    · rw [hg_o']; exact ⟨isSelfVisible_gridPoint 2 b, le_rfl, hbo'⟩
    · rw [hg_r']
      have := he.orderly c
      rw [(hs.grade_eq_two_iff c).mpr (.inr (.inr (.inr rfl)))] at this
      exact ⟨this.min (isSelfVisible_gridPoint 2 b), min_le_right _ _, min_le_left _ _⟩
  refine ⟨fun d ↦ ?_, fun c ↦ ?_, fun s t hst hgr ↦ ?_⟩
  · -- order
    by_cases h₁ : d = o'
    · rw [h₁, hg_o', (hs.grade_eq_two_iff o').mpr (.inr (.inr (.inl rfl)))]
      exact isSelfVisible_gridPoint 2 b
    by_cases h₂ : d = r'
    · rw [h₂, hg_r', (hs.grade_eq_two_iff r').mpr (.inr (.inr (.inr rfl)))]
      have := he.orderly r'
      rw [(hs.grade_eq_two_iff r').mpr (.inr (.inr (.inr rfl)))] at this
      exact this.min (isSelfVisible_gridPoint 2 b)
    · rw [hg_ne d h₁ h₂]
      exact (he.orderly d).reduce _
  · -- locality
    have hgr2 (d : S.toCellScheme.below (S.toCellScheme.gradedIndex c)) :
        S.toCellScheme.grade d ≤ 2 := hs.grade_le d
    by_cases hc2 : S.toCellScheme.grade c = 2
    · rcases (hs.grade_eq_two_iff c).mp hc2 with hc | hc | hc | hc
      · -- a context cell: the section is `⊤` at the cells read other than at `⊥`
        refine transformsTo_of_eq_bot_iff _ hgr2 (isSelfVisible_top 2) _ _ fun d ↦ ?_
        rw [hg_ctx c (.inr (.inr (.inl hc))), min_top_right]
        split_ifs with hd
        · have h := (he.locality c).eq_bot hd
          simp only [_root_.min_eq_bot, hne c (.inl hc), or_false] at h
          exact hg_bot d h
        · exact hg_ctx d ((hs.rowAt_context c (.inl hc) d).mp (hrow c d ▸ hd))
      · refine transformsTo_of_eq_bot_iff _ hgr2 (isSelfVisible_top 2) _ _ fun d ↦ ?_
        rw [hg_ctx c (.inr (.inr (.inr hc))), min_top_right]
        split_ifs with hd
        · have h := (he.locality c).eq_bot hd
          simp only [_root_.min_eq_bot, hne c (.inr (.inl hc)), or_false] at h
          exact hg_bot d h
        · exact hg_ctx d ((hs.rowAt_context c (.inr hc) d).mp (hrow c d ▸ hd))
      all_goals
        -- a donor cell: the locality of `e` capped at the value of `g`
        obtain ⟨hsv, hgh, hge⟩ := hdon c (by first | exact .inl hc | exact .inr hc)
        convert (he.locality c).min_const hgr2 hsv using 1
        funext d
        calc min (g d) (g c) = min (min (g d) (gridPoint 2 b)) (g c) := by
              rw [min_assoc, min_eq_right hgh]
          _ = min (min (e d) (gridPoint 2 b)) (g c) := by rw [hag]
          _ = min (e d) (g c) := by rw [min_assoc, min_eq_right hgh]
          _ = min (min (e d) (e c)) (g c) := by rw [min_assoc, min_eq_right hge]
    · -- a cell of grade at most `1`: the collapse of the locality of `e`
      have hc1 : S.toCellScheme.grade c ≤ 1 := by have := hs.grade_le c; omega
      have hnd (d : Fin S.card) (hd : S.toCellScheme.grade d ≤ 1) : d ≠ o' ∧ d ≠ r' :=
        ⟨fun h ↦ by rw [h, (hs.grade_eq_two_iff o').mpr (.inr (.inr (.inl rfl)))] at hd; omega,
          fun h ↦ by rw [h, (hs.grade_eq_two_iff r').mpr (.inr (.inr (.inr rfl)))] at hd; omega⟩
      have hK (d : S.toCellScheme.below (S.toCellScheme.gradedIndex c)) :
          S.toCellScheme.grade d ≤ 1 := d.2.2.trans hc1
      convert (he.locality c).collapse (isSuccPrelimit_block' b) hK (by omega : 1 < 2) using 1
      funext d
      rw [Function.comp_apply, hg_ne _ (hnd d (hK d)).1 (hnd d (hK d)).2,
        hg_ne c (hnd c hc1).1 (hnd c hc1).2]
      exact ((monotone_reduce _).map_min).symm
  · -- availability
    obtain ⟨u', hu', hle⟩ := he.availability s t hst hgr
    refine ⟨u', hu', ?_⟩
    by_cases hso : s = o'
    · rw [hso, hg_o']
      have hu'h : gridPoint 2 b ≤ e u' := hbo'.trans (hso ▸ hle)
      by_cases hu1 : u' = o'
      · rw [hu1, hg_o']
      by_cases hu2 : u' = r'
      · rw [hu2, hg_r', min_eq_right (hu2 ▸ hu'h)]
      · rw [hg_ne u' hu1 hu2, collapse_of_le hu'h]; exact le_top
    by_cases hsr : s = r'
    · rw [hsr, hg_r']
      have hle' : e r' ≤ e u' := hsr ▸ hle
      by_cases hu1 : u' = o'
      · rw [hu1, hg_o']; exact min_le_right _ _
      by_cases hu2 : u' = r'
      · rw [hu2, hg_r']
      · rw [hg_ne u' hu1 hu2]; exact (min_le_min_right _ hle').trans (min_le_collapse b _)
    by_cases hud : u' = o' ∨ u' = r'
    · exfalso
      have hgu : S.toCellScheme.grade u' = 2 := (hs.grade_eq_two_iff u').mpr (.inr (.inr hud))
      have hgt : S.toCellScheme.grade t = 2 := by
        rw [← hgu]; exact (congrArg Prod.snd hu').symm
      rcases (hs.grade_eq_two_iff s).mp (hgr.trans hgt) with h | h | h | h
      · exact hs.not_scope_subset s u' (.inl h) hud (hst.trans (congrArg Prod.fst hu').symm.le)
      · exact hs.not_scope_subset s u' (.inr h) hud (hst.trans (congrArg Prod.fst hu').symm.le)
      · exact hso h
      · exact hsr h
    · rw [hg_ne s hso hsr, hg_ne u' (fun h ↦ hud (.inl h)) (fun h ↦ hud (.inr h))]
      exact monotone_reduce _ hle

end IsMixedSite

/-! ### The twisted entry is forced -/

variable {M : ℕ} {ε : Fin M → Fin S.card → Label.{u}} {σ : Fin M → Bool}
  {κ : (Fin S.card → Label.{u}) → Label.{u}}
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), 2) ≤ S.toCellScheme.gradedIndex d}

/-- An old cell lies below every new cell of a sheet layer at grade `2` over a site. -/
private theorem old_mem_below_new' (hs : S.IsMixedSite y z o r z' o' r') (c : Fin S.card)
    (i : Fin M) : Fin.castAdd M c ∈ (S.sheetLayer 2 ε σ κ hS).toCellScheme.below
      ((S.sheetLayer 2 ε σ κ hS).toCellScheme.gradedIndex (Fin.natAdd S.card i)) := by
  rw [appendFullCellsScheme_gradedIndex_natAdd, CellScheme.mem_below,
    appendFullCellsScheme_gradedIndex_castAdd]
  exact ⟨subset_univ _, hs.grade_le c⟩

/-- A new cell labelled `⊤` reads every old cell labelled `⊤` other than at `⊥`. -/
private theorem ne_bot_of_eq_top' (hs : S.IsMixedSite y z o r z' o' r')
    {q : Fin (S.card + M) → Label.{u}} (hq : (S.sheetLayer 2 ε σ κ hS).rows.IsLawful q)
    {i : Fin M} (hi : q (Fin.natAdd S.card i) = ⊤) {c : Fin S.card}
    (hc : q (Fin.castAdd M c) = ⊤) : ε i c ≠ ⊥ := by
  intro h
  have h' := (hq.locality (Fin.natAdd S.card i)).eq_bot (d := ⟨_, old_mem_below_new' hs c i⟩)
    (by rw [sheetLayer_row_natAdd, sheetRow_castAdd, h])
  simp only [hc, hi, min_self] at h'
  exact top_ne_bot h'

/-- A catalogue entry other than `⊥` at a cell of grade `2` is a grid point at grade `2`. -/
private theorem exists_eq_gridPoint' {a : Fin S.card → Label.{u}} (ha : a ∈ S.catalogue 2)
    {c : Fin S.card} (hc : S.toCellScheme.grade c = 2) (hne : a c ≠ ⊥) :
    ∃ b ≤ 2 * S.card, a c = gridPoint 2 b := by
  have hv : IsSelfVisible 2 (a c) := hc ▸ (mem_catalogue.mp ha).1.orderly c
  rcases mem_codeGrid.mp (mem_codeGrid_of_mem_catalogue ha c) with h | ⟨b, hb, f, hf, h⟩
  · exact absurd h hne
  · rw [h, isSelfVisible_coe, Label.omega0_mul_add_natCast_mod, Nat.cast_le] at hv
    obtain rfl : f = 2 := le_antisymm hf hv
    exact ⟨b, hb, h⟩

namespace IsMixedSite

variable (hs : S.IsMixedSite y z o r z' o' r')
include hs

/-- **The twisted entry is forced at the tops.**  In a sheet layer at grade `2` over a site, with
entries in the canonical catalogue and some new cell, serving the capped agreements, every lawful
labelling `⊤` at `o`, `r`, `o'` (with no condition at `r'`) labels `⊤` a new cell whose entry
reads `o'` strictly below every context cell. -/
theorem exists_top_lt_of_serves_twisted (hε : ∀ i, ε i ∈ S.catalogue 2) (j₀ : Fin M)
    (hserve : S.ServesAgreements 2 ε σ κ) {q : Fin (S.card + M) → Label.{u}}
    (hq : (S.sheetLayer 2 ε σ κ hS).rows.IsLawful q)
    (htop : ∀ c, (c = o ∨ c = r ∨ c = o') → q (Fin.castAdd M c) = ⊤) :
    ∃ j, q (Fin.natAdd S.card j) = ⊤ ∧
      ∀ s, (s = y ∨ s = z ∨ s = o ∨ s = r) → ε j o' < ε j s := by
  -- availability from `o` gives a new cell `u` labelled `⊤`
  obtain ⟨u, hu, hle⟩ := hq.availability (Fin.castAdd M o) (Fin.natAdd S.card j₀)
    (by rw [appendFullCellsScheme_scope_natAdd]; exact subset_univ _)
    (by rw [appendFullCellsScheme_grade_castAdd, appendFullCellsScheme_grade_natAdd, hs.grade_o])
  rw [htop o (.inl rfl), top_le_iff] at hle
  rw [appendFullCellsScheme_gradedIndex_natAdd] at hu
  obtain ⟨i, rfl⟩ := exists_natAdd_eq_sheetLayer hu
  set e := ε i with he_def
  obtain ⟨hel, -, hecode⟩ := mem_catalogue.mp (hε i)
  have hne (c : Fin S.card) (hc : c = o ∨ c = r ∨ c = o') : e c ≠ ⊥ :=
    ne_bot_of_eq_top' hs hq hle (htop c hc)
  -- the least value of `e` at `o`, `r`, `o'`, a grid point `ω * b + 2`
  obtain ⟨x₀, hx₀, hmin⟩ := Finset.exists_min_image ({o, r, o'} : Finset (Fin S.card)) e
    ⟨o, by simp⟩
  have hx₀' : x₀ = o ∨ x₀ = r ∨ x₀ = o' := by simpa using hx₀
  have hmin' (c : Fin S.card) (hc : c = o ∨ c = r ∨ c = o') : e x₀ ≤ e c :=
    hmin c (by simpa using hc)
  have hg₀ : S.toCellScheme.grade x₀ = 2 := by
    rcases hx₀' with rfl | rfl | rfl
    exacts [hs.grade_o, hs.grade_r, hs.grade_o']
  obtain ⟨b, hb, hbx⟩ := exists_eq_gridPoint' (hε i) hg₀ (hne x₀ hx₀')
  have hgb (c : Fin S.card) (hc : c = o ∨ c = r ∨ c = o') : gridPoint 2 b ≤ e c :=
    hbx ▸ hmin' c hc
  -- the twisted labelling and its code
  set g := twistedLabelling o' r' e b
  have hg : S.rows.IsLawful g := hs.isLawful_twistedLabelling hel hgb
  have hsplice : S.toCellScheme.splice 2 (fun _ ↦ ⊥) g = g :=
    funext fun d ↦ CellScheme.splice_of_le (hs.grade_le d)
  have hmem : orbitCode 2 g ∈ S.catalogue 2 := by
    have h := orbitCode_splice_bot_mem_catalogue (hg.isLawfulBelow (univ, 2))
    rwa [hsplice] at h
  obtain ⟨hoy, hoz, -, -⟩ := hs.le_of_isLawful hel
  have hag (d : Fin S.card) : min (g d) (gridPoint 2 b) = min (e d) (gridPoint 2 b) :=
    hs.min_twistedLabelling (hgb o' (.inr (.inr rfl))) d
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
  -- the code keeps the order of the keys: `⊤` at the context cells, `ω * b + 2` at `o'`
  have hgs : g s = ⊤ := by
    have hnd := hs.not_donor hsc
    change twistedLabelling o' r' e b s = ⊤
    rw [twistedLabelling_of_ne (fun h ↦ hnd (.inl h)) (fun h ↦ hnd (.inr h))]
    refine collapse_of_le ?_
    rcases hsc with rfl | rfl | rfl | rfl
    exacts [(hgb o (.inl rfl)).trans hoy, (hgb o (.inl rfl)).trans hoz, hgb _ (.inl rfl),
      hgb _ (.inr (.inl rfl))]
  have hgd : g o' = gridPoint 2 b := twistedLabelling_o'
  rw [hj]
  refine lt_of_not_ge fun hle' ↦ ?_
  have h1 := monotone_visibilityReplace (k := 2) le_rfl hle'
  rw [visibilityReplace_orbitCode_le_iff (hgd ▸ WithBot.coe_ne_bot) (hgs ▸ top_ne_bot), hgs,
    hgd, visibilityReplace_top, isSelfVisible_gridPoint 2 b, top_le_iff] at h1
  exact ne_top_of_mem_codeGrid (grid_subset_codeGrid 2 b (gridPoint_mem_grid le_rfl)) h1

/-- `Scheme.IsMixedSite.exists_top_lt_of_serves_twisted` for a layer whose rows are equal to sheet
rows, read through `rowAt`. -/
theorem exists_top_lt_twisted_of_eq {M : ℕ} {ε : Fin M → Fin S.card → Label.{u}}
    {σ : Fin M → Bool} {κ : (Fin S.card → Label.{u}) → Label.{u}}
    {hS : ∀ d, ¬ ((univ : Finset (Fin n)), 2) ≤ S.toCellScheme.gradedIndex d}
    (hε : ∀ i, ε i ∈ S.catalogue 2) (j₀ : Fin M) (hserve : S.ServesAgreements 2 ε σ κ)
    {rr : Fin M → Fin (S.card + M) → Label.{u}} (hrr : rr = S.sheetRow 2 ε σ κ)
    {q : Fin (S.card + M) → Label.{u}}
    (hq : (S.appendFullCells 2 M rr hS).rows.IsLawful q)
    (htop : ∀ c, (c = o ∨ c = r ∨ c = o') → q (Fin.castAdd M c) = ⊤) :
    ∃ j, q (Fin.natAdd S.card j) = ⊤ ∧ ∀ s, (s = y ∨ s = z ∨ s = o ∨ s = r) →
      (S.appendFullCells 2 M rr hS).rowAt (Fin.natAdd S.card j) (Fin.castAdd M o') <
        (S.appendFullCells 2 M rr hS).rowAt (Fin.natAdd S.card j) (Fin.castAdd M s) := by
  subst hrr
  obtain ⟨j, hj, hlt⟩ := hs.exists_top_lt_of_serves_twisted hε j₀ hserve hq htop
  refine ⟨j, hj, fun s hsc ↦ ?_⟩
  rw [hs.rowAt_natAdd_castAdd, hs.rowAt_natAdd_castAdd]
  exact hlt s hsc

/-- **No context cell is read as low as `o'` at the tops**, under `⊤` at `o`, `r`, `o'` only. -/
theorem not_exists_reading_twisted {M : ℕ} {ε : Fin M → Fin S.card → Label.{u}}
    {σ : Fin M → Bool} {κ : (Fin S.card → Label.{u}) → Label.{u}}
    {hS : ∀ d, ¬ ((univ : Finset (Fin n)), 2) ≤ S.toCellScheme.gradedIndex d}
    (hε : ∀ i, ε i ∈ S.catalogue 2) (j₀ : Fin M) (hserve : S.ServesAgreements 2 ε σ κ)
    {rr : Fin M → Fin (S.card + M) → Label.{u}} (hrr : rr = S.sheetRow 2 ε σ κ)
    {q : Fin (S.card + M) → Label.{u}}
    (hq : (S.appendFullCells 2 M rr hS).rows.IsLawful q)
    (htop : ∀ c, (c = o ∨ c = r ∨ c = o') → q (Fin.castAdd M c) = ⊤) :
    ¬ ∃ s, (s = y ∨ s = z ∨ s = o ∨ s = r) ∧ ∀ j, q (Fin.natAdd S.card j) = ⊤ →
      (S.appendFullCells 2 M rr hS).rowAt (Fin.natAdd S.card j) (Fin.castAdd M s) ≤
        (S.appendFullCells 2 M rr hS).rowAt (Fin.natAdd S.card j) (Fin.castAdd M o') := by
  subst hrr
  rintro ⟨s, hsc, hread⟩
  obtain ⟨j, hj, hlt⟩ := hs.exists_top_lt_of_serves_twisted hε j₀ hserve hq htop
  have h := hread j hj
  rw [hs.rowAt_natAdd_castAdd, hs.rowAt_natAdd_castAdd] at h
  exact (hlt s hsc).not_ge h

end IsMixedSite

end Scheme

namespace MixedSeed

open SeparationObstruction

variable {α : Ordinal.{u}}

section Completion

variable {M₁ : ℕ} {rr : Fin M₁ → Fin ((I α).amalgam.card + M₁) → Label.{u}}

/-- **No canonical field layer over the seed reads `o'` at its tops, with no condition at `r'`**:
over any layer of cells of full scope and grade `1` over the amalgam of the input with itself, in
the canonical field layer at grade `2`, under `⊤` at `o`, `r`, `o'`. -/
theorem not_exists_reading_fieldLayer_twisted
    {hS : ∀ d, ¬ ((univ : Finset (Fin 3)), 2) ≤
      ((I α).amalgam.toScheme.appendFullCells 1 M₁ rr
        ((I α).not_univ_le 1)).toCellScheme.gradedIndex d}
    {q : Fin _ → Label.{u}}
    (hq : (((I α).amalgam.toScheme.appendFullCells 1 M₁ rr ((I α).not_univ_le 1)).fieldLayer 2
      hS).rows.IsLawful q)
    (htop : ∀ c, (c = lc α 3 ∨ c = lc α 4 ∨ c = rc α 3) →
      q (Fin.castAdd _ (Fin.castAdd M₁ c)) = ⊤) :
    ¬ ∃ s, (s = lc α 0 ∨ s = lc α 2 ∨ s = lc α 3 ∨ s = lc α 4) ∧ ∀ j, q (Fin.natAdd _ j) = ⊤ →
      (((I α).amalgam.toScheme.appendFullCells 1 M₁ rr ((I α).not_univ_le 1)).fieldLayer 2
        hS).rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd M₁ s)) ≤
      (((I α).amalgam.toScheme.appendFullCells 1 M₁ rr ((I α).not_univ_le 1)).fieldLayer 2
        hS).rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd M₁ (rc α 3))) := by
  rintro ⟨s, hsc, hread⟩
  have htop' (c : Fin ((I α).amalgam.card + M₁))
      (hc : c = Fin.castAdd M₁ (lc α 3) ∨ c = Fin.castAdd M₁ (lc α 4) ∨
        c = Fin.castAdd M₁ (rc α 3)) : q (Fin.castAdd _ c) = ⊤ := by
    rcases hc with rfl | rfl | rfl
    exacts [htop _ (.inl rfl), htop _ (.inr (.inl rfl)), htop _ (.inr (.inr rfl))]
  have hs' : Fin.castAdd M₁ s = Fin.castAdd M₁ (lc α 0) ∨ Fin.castAdd M₁ s = Fin.castAdd M₁ (lc α 2)
      ∨ Fin.castAdd M₁ s = Fin.castAdd M₁ (lc α 3) ∨
      Fin.castAdd M₁ s = Fin.castAdd M₁ (lc α 4) := by
    rcases hsc with rfl | rfl | rfl | rfl
    exacts [.inl rfl, .inr (.inl rfl), .inr (.inr (.inl rfl)), .inr (.inr (.inr rfl))]
  exact (isMixedSite_appendFullCells (α := α) (M₁ := M₁) (rr := rr)).not_exists_reading_twisted
    (fun i ↦ Scheme.catalogueEntry_mem i)
    (Scheme.exists_catalogueEntry_eq (Scheme.orbitCode_splice_bot_mem_catalogue
      (p := fun _ ↦ ⊥) (CellScheme.Rows.isLawfulBelow_const_bot _))).choose
    (Scheme.servesAgreements_of_le (fun _ _ ↦ le_top) fun a ha ↦ Scheme.exists_catalogueEntry_eq ha)
    (Scheme.fieldRow_eq_sheetRow fun _ ↦ ⊤) hq htop' ⟨_, hs', hread⟩

/-- **The twisted entry at the tops of a canonical field layer over the seed**, positively: under
`⊤` at `o`, `r`, `o'`, some cell of full scope and grade `2` labelled `⊤` reads `o'` strictly
below each of `y`, `z`, `o`, `r`. -/
theorem exists_top_lt_fieldLayer_twisted
    {hS : ∀ d, ¬ ((univ : Finset (Fin 3)), 2) ≤
      ((I α).amalgam.toScheme.appendFullCells 1 M₁ rr
        ((I α).not_univ_le 1)).toCellScheme.gradedIndex d}
    {q : Fin _ → Label.{u}}
    (hq : (((I α).amalgam.toScheme.appendFullCells 1 M₁ rr ((I α).not_univ_le 1)).fieldLayer 2
      hS).rows.IsLawful q)
    (htop : ∀ c, (c = lc α 3 ∨ c = lc α 4 ∨ c = rc α 3) →
      q (Fin.castAdd _ (Fin.castAdd M₁ c)) = ⊤) :
    ∃ j, q (Fin.natAdd _ j) = ⊤ ∧ ∀ s, (s = lc α 0 ∨ s = lc α 2 ∨ s = lc α 3 ∨ s = lc α 4) →
      (((I α).amalgam.toScheme.appendFullCells 1 M₁ rr ((I α).not_univ_le 1)).fieldLayer 2
        hS).rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd M₁ (rc α 3))) <
      (((I α).amalgam.toScheme.appendFullCells 1 M₁ rr ((I α).not_univ_le 1)).fieldLayer 2
        hS).rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd M₁ s)) := by
  have hs := isMixedSite_appendFullCells (α := α) (M₁ := M₁) (rr := rr)
  have htop' (c : Fin ((I α).amalgam.card + M₁))
      (hc : c = Fin.castAdd M₁ (lc α 3) ∨ c = Fin.castAdd M₁ (lc α 4) ∨
        c = Fin.castAdd M₁ (rc α 3)) : q (Fin.castAdd _ c) = ⊤ := by
    rcases hc with rfl | rfl | rfl
    exacts [htop _ (.inl rfl), htop _ (.inr (.inl rfl)), htop _ (.inr (.inr rfl))]
  obtain ⟨j, hj, hlt⟩ := hs.exists_top_lt_twisted_of_eq
    (fun i ↦ Scheme.catalogueEntry_mem i)
    (Scheme.exists_catalogueEntry_eq (Scheme.orbitCode_splice_bot_mem_catalogue
      (p := fun _ ↦ ⊥) (CellScheme.Rows.isLawfulBelow_const_bot _))).choose
    (Scheme.servesAgreements_of_le (fun _ _ ↦ le_top) fun a ha ↦ Scheme.exists_catalogueEntry_eq ha)
    (Scheme.fieldRow_eq_sheetRow fun _ ↦ ⊤) hq htop'
  refine ⟨j, hj, fun s hsc ↦ hlt _ ?_⟩
  rcases hsc with rfl | rfl | rfl | rfl
  exacts [.inl rfl, .inr (.inl rfl), .inr (.inr (.inl rfl)), .inr (.inr (.inr rfl))]

end Completion

/-- **The canonical completion at the arity one over the amalgam of two copies of the input does not
read `o'` at its tops, with no condition at `r'`**: every lawful labelling of `Seed.fieldLayerOne`
`⊤` at `o`, `r`, `o'` labels `⊤` a cell of full scope and grade `2` reading `o'` strictly below each
of `y`, `z`, `o`, `r`.  (`MixedSeed.not_exists_reading_fieldLayerOne` asks `⊤` at `r'` too.) -/
theorem not_exists_reading_fieldLayerOne_twisted {q : Fin (I α).fieldLayerOne.card → Label.{u}}
    (hq : (I α).fieldLayerOne.rows.IsLawful q)
    (htop : ∀ c, (c = lc α 3 ∨ c = lc α 4 ∨ c = rc α 3) →
      q (Fin.castAdd _ (Fin.castAdd _ c)) = ⊤) :
    ¬ ∃ s, (s = lc α 0 ∨ s = lc α 2 ∨ s = lc α 3 ∨ s = lc α 4) ∧ ∀ j, q (Fin.natAdd _ j) = ⊤ →
      (I α).fieldLayerOne.rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd _ s)) ≤
      (I α).fieldLayerOne.rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd _ (rc α 3))) :=
  not_exists_reading_fieldLayer_twisted (M₁ := ((I α).amalgam.toScheme.catalogue 1).card)
    (rr := fun i ↦ (I α).amalgam.toScheme.fieldRow 1 ((I α).amalgam.toScheme.catalogueEntry 1 i))
    (hS := (I α).not_univ_two_le_lowerFieldLayer) hq htop

/-- **The twisted entry at the tops of the canonical completion at the arity one**, positively. -/
theorem exists_top_lt_fieldLayerOne_twisted {q : Fin (I α).fieldLayerOne.card → Label.{u}}
    (hq : (I α).fieldLayerOne.rows.IsLawful q)
    (htop : ∀ c, (c = lc α 3 ∨ c = lc α 4 ∨ c = rc α 3) →
      q (Fin.castAdd _ (Fin.castAdd _ c)) = ⊤) :
    ∃ j, q (Fin.natAdd _ j) = ⊤ ∧ ∀ s, (s = lc α 0 ∨ s = lc α 2 ∨ s = lc α 3 ∨ s = lc α 4) →
      (I α).fieldLayerOne.rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd _ (rc α 3))) <
      (I α).fieldLayerOne.rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd _ s)) :=
  exists_top_lt_fieldLayer_twisted (M₁ := ((I α).amalgam.toScheme.catalogue 1).card)
    (rr := fun i ↦ (I α).amalgam.toScheme.fieldRow 1 ((I α).amalgam.toScheme.catalogueEntry 1 i))
    (hS := (I α).not_univ_two_le_lowerFieldLayer) hq htop

end MixedSeed

namespace TwistedDonor

open SeparationObstruction MixedSeed

variable {α : Ordinal.{u}} {v : Label.{u}} (hv : IsSelfVisible 2 v) (hvα : AtStage α v)

/-- The twisted donor with `o` at `⊤`: the input labelled `(⊤, ⊥, ⊤, ⊤, v)`. -/
noncomputable abbrev Utop : StageType.{u} α 2 :=
  U α (isSelfVisible_top 2) hv le_top (Or.inr rfl) hvα

/-- **The seed of the input with the twisted donor.** -/
noncomputable abbrev seedU : Seed.{u} α 1 :=
  Seed.ofCoatoms (isLegal_T α) (isLegal_U (isSelfVisible_top 2) hv le_top (Or.inr rfl) hvα)
    (restrictFace_T α) (restrictFace_U_face (isSelfVisible_top 2) hv le_top (Or.inr rfl) hvα)

/-- Amalgams of equal coatom schemes are equal. -/
theorem amalgam_congr {m : ℕ} {Sa Sb Sb' : Scheme.{u} (m + 1)} (e : Sb = Sb')
    (h : Sa.comap (Coatom.face m) = Sb.comap (Coatom.face m))
    (h' : Sa.comap (Coatom.face m) = Sb'.comap (Coatom.face m)) :
    Coatom.amalgam h = Coatom.amalgam h' := by
  subst e; rfl

/-- **The amalgam of the input with the twisted donor has the scheme of the amalgam of the input
with itself**: the amalgamated scheme depends only on the schemes of the coatom types. -/
theorem amalgam_seedU : (seedU hv hvα).amalgam.toScheme = (I α).amalgam.toScheme :=
  amalgam_congr (Sa := (T α).toScheme)
    (Sb := (U α (isSelfVisible_top 2) hv le_top (Or.inr rfl) hvα).toScheme)
    (Sb' := (T α).toScheme) rfl _ _

/-- Two field layers over equal schemes are equal. -/
theorem fieldLayer_fieldLayer_congr {A B : Scheme.{u} 3} (e : A = B)
    (h₁ : ∀ d, ¬ ((univ : Finset (Fin 3)), 1) ≤ A.toCellScheme.gradedIndex d)
    (h₁' : ∀ d, ¬ ((univ : Finset (Fin 3)), 1) ≤ B.toCellScheme.gradedIndex d)
    (h₂ : ∀ d, ¬ ((univ : Finset (Fin 3)), 2) ≤ (A.fieldLayer 1 h₁).toCellScheme.gradedIndex d)
    (h₂' : ∀ d, ¬ ((univ : Finset (Fin 3)), 2) ≤ (B.fieldLayer 1 h₁').toCellScheme.gradedIndex d) :
    (A.fieldLayer 1 h₁).fieldLayer 2 h₂ = (B.fieldLayer 1 h₁').fieldLayer 2 h₂' := by
  subst e; rfl

/-- The canonical completions at the arity one of equal amalgams are equal. -/
theorem fieldLayerOne_congr {I₁ I₂ : Seed.{u} α 1}
    (e : I₁.amalgam.toScheme = I₂.amalgam.toScheme) : I₁.fieldLayerOne = I₂.fieldLayerOne :=
  fieldLayer_fieldLayer_congr e _ _ _ _

/-- Lawfulness along an equality of schemes. -/
theorem isLawful_cast {n : ℕ} {X Y : Scheme.{u} n} (e : X = Y) {p : Fin X.card → Label.{u}}
    (hp : X.rows.IsLawful p) :
    Y.rows.IsLawful fun i ↦ p (Fin.cast (congrArg Scheme.card e).symm i) := by
  subst e; exact hp

/-- Cells of a face along an equality of schemes. -/
theorem val_faceCell_cast {n m : ℕ} {X Y : Scheme.{u} n} (e : X = Y) {f : Fin m ↪ Fin n}
    {Tm : Scheme.{u} m} (hX : X.comap f = Tm) (hY : Y.comap f = Tm) (i : Fin Tm.card) :
    (X.faceCell f hX i : ℕ) = Y.faceCell f hY i := by
  subst e; rfl

/-- **The scheme of the completion at the arity one of the twisted seed** is that of the input with
itself. -/
theorem fieldLayerOne_seedU : (seedU hv hvα).fieldLayerOne = (I α).fieldLayerOne :=
  fieldLayerOne_congr (amalgam_seedU hv hvα)

/-- **The glued labelling of the input and the twisted donor is lawful** on the amalgam of the
input with itself. -/
theorem isLawful_gluedU : (I α).amalgam.toScheme.rows.IsLawful fun c ↦
    (seedU hv hvα).amalgam.label (Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm c) :=
  isLawful_cast (amalgam_seedU hv hvα) (seedU hv hvα).amalgam.isLawful

theorem cast_lc (w : Fin 5) :
    Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm (lc α w) =
      StageType.faceCell (seedU hv hvα).restrictFace_left (cellT α w) :=
  Fin.ext (val_faceCell_cast (amalgam_seedU hv hvα).symm
    (StageType.comap_toScheme_of_restrictFace (I α).restrictFace_left) _ _)

theorem cast_rc (w : Fin 5) :
    Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm (rc α w) =
      StageType.faceCell (seedU hv hvα).restrictFace_right (cellT α w) :=
  Fin.ext (val_faceCell_cast (amalgam_seedU hv hvα).symm
    (StageType.comap_toScheme_of_restrictFace ((I α).restrictFace_right_left (hLR α))) _ _)

/-- **The glued labelling is `⊤` at `o`, `r`, `o'` and `v` at `r'`.** -/
theorem gluedU_values :
    (seedU hv hvα).amalgam.label (Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm
      (lc α 3)) = ⊤ ∧
    (seedU hv hvα).amalgam.label (Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm
      (lc α 4)) = ⊤ ∧
    (seedU hv hvα).amalgam.label (Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm
      (rc α 3)) = ⊤ ∧
    (seedU hv hvα).amalgam.label (Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm
      (rc α 4)) = v := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cast_lc]; exact StageType.label_faceCell (seedU hv hvα).restrictFace_left (cellT α 3)
  · rw [cast_lc]; exact StageType.label_faceCell (seedU hv hvα).restrictFace_left (cellT α 4)
  · rw [cast_rc]; exact StageType.label_faceCell (seedU hv hvα).restrictFace_right (cellT α 3)
  · rw [cast_rc]; exact StageType.label_faceCell (seedU hv hvα).restrictFace_right (cellT α 4)

/-- **The glued labelling extends to the canonical completion at the arity one** (every lawful
labelling of the amalgam does, `Seed.exists_isLawful_fieldLayerOne`). -/
theorem exists_extension_gluedU : ∃ q : Fin (I α).fieldLayerOne.card → Label.{u},
    (I α).fieldLayerOne.rows.IsLawful q ∧ ∀ c, q (Fin.castAdd _ (Fin.castAdd _ c)) =
      (seedU hv hvα).amalgam.label (Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm c)
    := (I α).exists_isLawful_fieldLayerOne (isLawful_gluedU hv hvα)

/-- **The full-catalogue completion at the arity one of the twisted seed does not read `o'` at its
tops.**  The seed is the input `SeparationObstruction.T α` with the donor `TwistedDonor.Utop`,
labelled `(⊤, ⊥, ⊤, ⊤, v)`, for every `v` (in particular `v ≠ ⊤`, the donor other than the
context); its completion at the arity one has the scheme `(I α).fieldLayerOne`
(`TwistedDonor.fieldLayerOne_seedU`).  In every lawful labelling of it extending the glued
labelling (`TwistedDonor.exists_extension_gluedU`; the completion's own labelling is one), some cell
of full scope and grade `2` labelled `⊤` reads `o'` strictly below each of `y`, `z`, `o`, `r`, so no
cell of the context labelled `⊤` is read at most as `o'` by every such cell.  The copy of `r` in the
donor is `v`, not `⊤`: the obstruction does not use it. -/
theorem not_exists_reading_of_extends {q : Fin (I α).fieldLayerOne.card → Label.{u}}
    (hq : (I α).fieldLayerOne.rows.IsLawful q)
    (hqe : ∀ c, q (Fin.castAdd _ (Fin.castAdd _ c)) =
      (seedU hv hvα).amalgam.label
        (Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm c)) :
    ¬ ∃ c, (c = lc α 0 ∨ c = lc α 2 ∨ c = lc α 3 ∨ c = lc α 4) ∧
      ∀ j, q (Fin.natAdd _ j) = ⊤ →
        (I α).fieldLayerOne.rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd _ c)) ≤
        (I α).fieldLayerOne.rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd _ (rc α 3))) := by
  obtain ⟨h3, h4, h3', -⟩ := gluedU_values hv hvα
  refine not_exists_reading_fieldLayerOne_twisted hq fun c hc ↦ ?_
  rw [hqe]
  rcases hc with rfl | rfl | rfl
  exacts [h3, h4, h3']

/-! ### The LOW admission at the twisted seed -/

variable (α) in
/-- **The LOW admission at the seed**, on states of the cells of the amalgam with a cutoff `b`.  The
designated donor cells are the copies `z'`, `e'`, `o'`, `r'` of the donor off the root; its tops
(in the donor `TwistedDonor.Utop`) are `z'`, `o'`, the others `e'` (dead) and `r'` (labelled `v`).
The frontier is `min (st o) (R₂ (st r))`, with `R₂ = visibilityReplace 2 2`, from the owner `o`
and the lost top `r` of the context.  Admission: if the state is below `b` at the non-top donor
cells, then every designated top is at least `max b frontier`. -/
def LowAdmitted (st : Fin (I α).amalgam.card → Label.{u}) (b : Label.{u}) : Prop :=
  max (st (rc α 1)) (st (rc α 4)) < b → ∀ x, (x = rc α 2 ∨ x = rc α 3) →
    max b (min (st (lc α 3)) (visibilityReplace 2 2 (st (lc α 4)))) ≤ st x

/-- **(i) A state reading `o'` strictly below the owner and the lost top is not admitted** at any
cutoff above its values at the non-top donor cells: `R₂` does not lower, so the frontier exceeds
`o'`.  The entries forced at the tops of the full-catalogue completion
(`Scheme.IsMixedSite.exists_top_lt_of_serves_twisted`) are such states. -/
theorem not_lowAdmitted_of_lt {st : Fin (I α).amalgam.card → Label.{u}} {b : Label.{u}}
    (hb : max (st (rc α 1)) (st (rc α 4)) < b) (ho : st (rc α 3) < st (lc α 3))
    (hr : st (rc α 3) < st (lc α 4)) : ¬ LowAdmitted α st b := fun hadm ↦ by
  have h := (le_max_right _ _).trans (hadm hb (rc α 3) (.inr rfl))
  have hR : st (lc α 4) ≤ visibilityReplace 2 2 (st (lc α 4)) :=
    le_visibilityReplace (k := 2) (i := 2) (by omega) _
  exact (lt_min ho (hr.trans_le hR)).not_ge h

/-- **The glued state is admitted** at every cutoff: its designated tops `z'`, `o'` are `⊤`. -/
theorem lowAdmitted_glued (b : Label.{u}) : LowAdmitted α (fun c ↦ (seedU hv hvα).amalgam.label
    (Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm c)) b := by
  intro _ x hx
  have h2 : (seedU hv hvα).amalgam.label
      (Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm (rc α 2)) = ⊤ := by
    rw [cast_rc]; exact StageType.label_faceCell (seedU hv hvα).restrictFace_right (cellT α 2)
  rcases hx with rfl | rfl
  · beta_reduce; rw [h2]; exact le_top
  · beta_reduce; rw [(gluedU_values hv hvα).2.2.1]; exact le_top

/-- **(i) The offending rows of the full-catalogue completion are not admitted**: in every lawful
labelling of the completion at the arity one extending the glued labelling (the completion's own
labelling among them), some cell of full scope and grade `2` labelled `⊤` has a row (on the old
cells) reading `o'` strictly below `o` and `r`; that row is not LOW-admitted at any cutoff above its
values at the non-top donor cells `e'`, `r'`. -/
theorem exists_not_lowAdmitted_row {q : Fin (I α).fieldLayerOne.card → Label.{u}}
    (hq : (I α).fieldLayerOne.rows.IsLawful q)
    (hqe : ∀ c, q (Fin.castAdd _ (Fin.castAdd _ c)) =
      (seedU hv hvα).amalgam.label
        (Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm c)) :
    ∃ j, q (Fin.natAdd _ j) = ⊤ ∧ ∀ b,
      max ((I α).fieldLayerOne.rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd _ (rc α 1))))
        ((I α).fieldLayerOne.rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd _ (rc α 4)))) < b →
      ¬ LowAdmitted α
        (fun c ↦ (I α).fieldLayerOne.rowAt (Fin.natAdd _ j) (Fin.castAdd _ (Fin.castAdd _ c))) b
    := by
  obtain ⟨h3, h4, h3', -⟩ := gluedU_values hv hvα
  obtain ⟨j, hj, hlt⟩ := exists_top_lt_fieldLayerOne_twisted hq fun c hc ↦ by
    rw [hqe]
    rcases hc with rfl | rfl | rfl
    exacts [h3, h4, h3']
  exact ⟨j, hj, fun b hb ↦ not_lowAdmitted_of_lt hb (hlt _ (.inr (.inr (.inl rfl))))
    (hlt _ (.inr (.inr (.inr rfl))))⟩

/-- **(ii) The determination from the LOW admission**, for every completion below the full grade
`F` of the seed of the input with itself (in particular the completion at the arity one, whose
scheme is also that of the twisted seed).  In a lawful labelling `q` of `F` with the owner `o`
and the lost top `r` at `⊤`, if at a cutoff `b` above `q` at the non-top donor cells the state of
every cell of full scope and grade `2` labelled `⊤` is admitted, then `o'` is `⊤`: availability
from `o` gives such a cell, its state is `q` on the old cells, and the frontier is `⊤`. -/
theorem eq_top_of_forall_lowAdmitted (F : CompletionBelowFullGrade (I α))
    {q : Fin F.scheme.card → Label.{u}} (hq : F.scheme.rows.IsLawful q)
    (ho : q (F.embed (lc α 3)) = ⊤) (hr : q (F.embed (lc α 4)) = ⊤) {b : Label.{u}}
    (hb : max (q (F.embed (rc α 1))) (q (F.embed (rc α 4))) < b)
    (hadm : ∀ u, F.scheme.toCellScheme.gradedIndex u = ((univ : Finset (Fin 3)), 2) →
      q u = ⊤ → LowAdmitted α (fun c ↦ min (q (F.embed c)) (q u)) b) :
    q (F.embed (rc α 3)) = ⊤ := by
  have hwf := F.isLegalBelowFullGrade.isWellFormed
  obtain ⟨t, ht⟩ := F.isLegalBelowFullGrade.exists_gradedIndex_eq ((univ : Finset (Fin 3)), 2)
    ⟨hwf.univ_mem_faces, by omega, by simp⟩ (by omega)
  have hg : F.scheme.toCellScheme.gradedIndex (F.embed (lc α 3)) =
      ((cells.scope 3).map (Coatom.left 1), cells.grade 3) :=
    (F.gradedIndex_embed _).trans (gradedIndex_lc 3)
  obtain ⟨u, hu, hle⟩ := hq.availability (F.embed (lc α 3)) t
    (by rw [show F.scheme.toCellScheme.scope t = univ from congrArg Prod.fst ht]
        exact subset_univ _)
    (by rw [show F.scheme.toCellScheme.grade t = 2 from congrArg Prod.snd ht,
          show F.scheme.toCellScheme.grade _ = _ from congrArg Prod.snd hg]
        rfl)
  rw [ho, top_le_iff] at hle
  have h := hadm u (hu.trans ht) hle
  simp only [hle, min_top_right] at h
  have h' := h hb (rc α 3) (.inr rfl)
  beta_reduce at h'
  rw [ho, hr, visibilityReplace_top, min_self, max_top_right, top_le_iff] at h'
  exact h'

include hv hvα in
/-- **The full-catalogue completion carries a lawful labelling with the context at `⊤` and `o'`
below `⊤`**: the twisted labelling of the glued labelling at a block `b₀` (`⊤` on the context,
`ω * b₀ + 2` at `o'`, `min v (ω * b₀ + 2)` at `r'`, `⊥` at `e'`), extended through the completion
at the arity one (`Seed.completionBelowFullGradeOne` of the seed of the input with itself, whose
scheme is that of the twisted seed, `TwistedDonor.fieldLayerOne_seedU`). -/
theorem exists_twisted_extension (b₀ : ℕ) :
    ∃ q : Fin (I α).completionBelowFullGradeOne.scheme.card → Label.{u},
      (I α).completionBelowFullGradeOne.scheme.rows.IsLawful q ∧
      q ((I α).completionBelowFullGradeOne.embed (lc α 3)) = ⊤ ∧
      q ((I α).completionBelowFullGradeOne.embed (lc α 4)) = ⊤ ∧
      q ((I α).completionBelowFullGradeOne.embed (rc α 3)) = gridPoint 2 b₀ ∧
      q ((I α).completionBelowFullGradeOne.embed (rc α 4)) = min v (gridPoint 2 b₀) ∧
      q ((I α).completionBelowFullGradeOne.embed (rc α 1)) = ⊥ := by
  have hs := isMixedSite (α := α)
  obtain ⟨h3, h4, h3', h4'⟩ := gluedU_values hv hvα
  have he1 : (seedU hv hvα).amalgam.label
      (Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm (rc α 1)) = ⊥ := by
    rw [cast_rc]; exact StageType.label_faceCell (seedU hv hvα).restrictFace_right (cellT α 1)
  have hgb (c : Fin (I α).amalgam.card) (hc : c = lc α 3 ∨ c = lc α 4 ∨ c = rc α 3) :
      gridPoint 2 b₀ ≤ (seedU hv hvα).amalgam.label
        (Fin.cast (congrArg Scheme.card (amalgam_seedU hv hvα)).symm c) := by
    rcases hc with rfl | rfl | rfl
    · rw [h3]; exact le_top
    · rw [h4]; exact le_top
    · rw [h3']; exact le_top
  have hg := hs.isLawful_twistedLabelling (isLawful_gluedU hv hvα) hgb
  obtain ⟨q, hq, hqe⟩ := (I α).exists_isLawful_fieldLayerOne hg
  have h13 : rc α 1 ≠ rc α 3 := fun h ↦ absurd (rc_injective α h) (by decide)
  have h14 : rc α 1 ≠ rc α 4 := fun h ↦ absurd (rc_injective α h) (by decide)
  refine ⟨q, hq, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show q ((I α).completionBelowFullGradeOne.embed (lc α 3)) = _ from hqe _]
    have hnd := hs.not_donor (.inr (.inr (.inl rfl)))
    rw [Scheme.twistedLabelling_of_ne (fun h ↦ hnd (.inl h)) (fun h ↦ hnd (.inr h)), h3]
    exact Scheme.collapse_of_le le_top
  · rw [show q ((I α).completionBelowFullGradeOne.embed (lc α 4)) = _ from hqe _]
    have hnd := hs.not_donor (.inr (.inr (.inr rfl)))
    rw [Scheme.twistedLabelling_of_ne (fun h ↦ hnd (.inl h)) (fun h ↦ hnd (.inr h)), h4]
    exact Scheme.collapse_of_le le_top
  · rw [show q ((I α).completionBelowFullGradeOne.embed (rc α 3)) = _ from hqe _]
    exact Scheme.twistedLabelling_o'
  · rw [show q ((I α).completionBelowFullGradeOne.embed (rc α 4)) = _ from hqe _,
      Scheme.twistedLabelling_r' (by rw [h3']; exact le_top), h4']
  · rw [show q ((I α).completionBelowFullGradeOne.embed (rc α 1)) = _ from hqe _,
      Scheme.twistedLabelling_of_ne h13 h14, he1]
    exact Scheme.collapse_bot _

include hv hvα in
/-- **The full-catalogue completion fails the LOW admission at the reading grade**: in the lawful
labelling `TwistedDonor.exists_twisted_extension` (the context at `⊤`, `o'` below `⊤`), at every
cutoff above its value at `r'`, some cell of full scope and grade `2` labelled `⊤` has a state that
is not admitted (`TwistedDonor.eq_top_of_forall_lowAdmitted`). -/
theorem not_forall_lowAdmitted (b₀ : ℕ) :
    ∃ q : Fin (I α).completionBelowFullGradeOne.scheme.card → Label.{u},
      (I α).completionBelowFullGradeOne.scheme.rows.IsLawful q ∧
      ∀ b, min v (gridPoint 2 b₀) < b → ∃ u,
        (I α).completionBelowFullGradeOne.scheme.toCellScheme.gradedIndex u =
          ((univ : Finset (Fin 3)), 2) ∧ q u = ⊤ ∧
        ¬ LowAdmitted α
          (fun c ↦ min (q ((I α).completionBelowFullGradeOne.embed c)) (q u)) b := by
  obtain ⟨q, hq, h3, h4, h3', h4', h1⟩ := exists_twisted_extension hv hvα b₀
  refine ⟨q, hq, fun b hb ↦ ?_⟩
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  have := eq_top_of_forall_lowAdmitted _ hq h3 h4
    (by rw [h1, h4', max_eq_right bot_le]; exact hb) hall
  rw [h3'] at this
  exact ne_top_of_mem_codeGrid (grid_subset_codeGrid 2 b₀ (gridPoint_mem_grid le_rfl)) this

end TwistedDonor

end VaughtConjecture
