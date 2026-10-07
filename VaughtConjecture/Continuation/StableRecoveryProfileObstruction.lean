/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryCoatom
import VaughtConjecture.Extension.TowerProfileCompletion

/-!
# The profile completion does not read through the cap

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.1 (the completion of the coatom extension, at `m = 3`); semantic contract, item 8.

The reading coatom completion (`StageType.HasReadingCoatomCompletions`, a named hypothesis, open)
asks for a completion of the last coatom pair whose every cell at `(univ, N)` reads the new cells of
the coface `D` through the cap (`StageType.IsCapReadingExtension`).  At `m = 3` every seed has a
compiled completion below the full grade (`TowerProfile.completion`): the tower `T 2`, a layer at
the grade `3` with one cell per rank-normalized profile (`RankProfile.rankCat`), and the canonical
field layer at the grade `4` with one cell per catalogue entry (`Scheme.catalogue`).  This file
shows that, as built, it never reads an ordinally labelled new cell through a cap of grade `3` or
`4`.  Each item below is compiled in this repository (theorem named), unless marked otherwise.

**A row reading `⊥` reads no ordinal through the cap**
(`StageType.not_readsThroughCap_of_row_eq_bot`): the ordinal clause of `StageType.ReadsThroughCap`
asks for the value `ω · c + n`.

**The constant `⊥` labelling is an entry of both catalogues** (`Scheme.bot_mem_catalogue`,
`TowerProfile.bot_mem_rankCat`): it is lawful (below both coatoms), bottom above every grade, and
fixed by the orbit code (`Label.orbitCode_eq_bot_iff`), with values in the code grid.  So the field
layer at the grade `k` has a cell at `(univ, k)` whose row is `⊥` at every old cell
(`Scheme.exists_fieldLayer_row_eq_bot`), and the profile layer has a cell at `(univ, 3)` whose row
is `⊥` at every cell of the amalgam (`TowerProfile.exists_scheme_row_eq_bot`).

**The obstruction** (`TowerProfile.not_isCapReadingExtension_completion`).  Let `I` be the seed of
two legal coatom types `T⁺`, `tb` on four points over a common face, at a stage zero or a limit,
and let `D` be a coface reached along `f` followed by the new point inside the second coatom, with
a new cell labelled `μ + n` (`μ` zero or a limit).  For every cell `b` of `T⁺` of grade `3` or `4`
above the arity of the root, the coatom extension with apex built from `TowerProfile.completion I`
(`CompletionBelowFullGrade.completion`) is not a cap-reading extension of `T⁺` along
`f.trans Fin.castSuccEmb` for `D` and `b`: the cell of the `⊥` entry at `(univ, N)` reads the new
cell as `⊥`.  So the unrestricted catalogue layers lose the reading at the layer of the grade of the
cap, at both grades `3` and `4`.  This refutes the reading for this completion only; it is not a
refutation of `StageType.HasReadingCoatomCompletions`, which asks for some completion.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

/-! ### A row reading `⊥` -/

namespace StageType

/-- **A row reading `⊥` reads no ordinal through the cap**: if the row of `u` reads `e` as `⊥`
and both `e` and the cap lie below `u`, then `u` does not read `e` through the cap as a cell
labelled `μ + n`. -/
theorem not_readsThroughCap_of_row_eq_bot {α : Ordinal.{u}} {m : ℕ} {Tp : StageType.{u} α m}
    {E : Scheme.{u} (m + 1)} {b : Fin (E.comap Fin.castSuccEmb).card} {u e : Fin E.card}
    (he : e ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u))
    (hb : E.cellMap Fin.castSuccEmb b ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u))
    (hrow : E.rows.row u ⟨e, he⟩ = ⊥) {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) (n : ℕ) :
    ¬ Tp.ReadsThroughCap E b u e ((μ + n : Ordinal.{u}) : Label.{u}) := by
  intro h
  obtain ⟨-, -, hord⟩ := h he hb
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hre⟩ := hord μ n hμ rfl
  rw [hrow] at hre
  exact WithBot.bot_ne_coe hre

end StageType

/-! ### The `⊥` entry of the canonical catalogue -/

namespace Scheme

variable {n : ℕ}

/-- **The constant `⊥` labelling is a catalogue entry**: lawful, bottom above `k`, and fixed by
the orbit code. -/
theorem bot_mem_catalogue (S : Scheme.{u} n) (k : ℕ) :
    (fun _ ↦ ⊥ : Fin S.card → Label.{u}) ∈ S.catalogue k :=
  mem_catalogue.mpr ⟨CellScheme.Rows.isLawful_const_bot, fun _ _ ↦ rfl,
    funext fun _ ↦ orbitCode_eq_bot_iff.mpr rfl⟩

/-- **The field layer has a cell reading `⊥`**: the cell of the `⊥` entry has graded index
`(univ, k)` and its row is `⊥` at every old cell. -/
theorem exists_fieldLayer_row_eq_bot (S : Scheme.{u} n) (k : ℕ)
    (hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d) :
    ∃ u : Fin (S.fieldLayer k hS).card,
      (S.fieldLayer k hS).toCellScheme.gradedIndex u = ((univ : Finset (Fin n)), k) ∧
      ∀ (d : Fin S.card)
        (hd : Fin.castAdd _ d ∈ (S.fieldLayer k hS).toCellScheme.below
          ((S.fieldLayer k hS).toCellScheme.gradedIndex u)),
        (S.fieldLayer k hS).rows.row u ⟨_, hd⟩ = ⊥ := by
  obtain ⟨i, hi⟩ := exists_catalogueEntry_eq (bot_mem_catalogue S k)
  refine ⟨Fin.natAdd _ i, appendFullCellsScheme_gradedIndex_natAdd S k _ i, fun d hd ↦ ?_⟩
  rw [fieldLayer_row_natAdd, fieldRow_castAdd, hi]

end Scheme

/-! ### The profile completion -/

namespace TowerProfile

open ProfileCatalogue (Profile)
open RankProfile (rankCat mem_rankCat)

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **The constant `⊥` profile is in the rank-normalized catalogue**: lawful below both coatoms,
in the code grid, and fixed by the orbit code. -/
theorem bot_mem_rankCat : (fun _ ↦ ⊥ : Profile I) ∈ rankCat I 3 := by
  simp only [rankCat, Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun _ ↦ Finset.mem_insert_self _ _, ⟨Rows.isLawfulBelow_const_bot _,
    Rows.isLawfulBelow_const_bot _⟩, funext fun _ ↦ orbitCode_eq_bot_iff.mpr rfl⟩

/-- **The profile layer has a cell reading `⊥`**: the cell of the `⊥` profile has graded index
`(univ, 3)` and its row is `⊥` at every cell of the amalgam. -/
theorem exists_scheme_row_eq_bot :
    ∃ u : Fin (scheme I).card,
      (scheme I).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), 3) ∧
      ∀ (d : Fin I.amalgam.card)
        (hd : embed3 I d ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex u)),
        (scheme I).rows.row u ⟨_, hd⟩ = ⊥ := by
  obtain ⟨i, hi⟩ := exists_entry_eq (bot_mem_rankCat (I := I))
  refine ⟨Fin.natAdd _ i, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ 3 _ i,
    fun d hd ↦ ?_⟩
  rw [Scheme.appendFullCells_row_natAdd]
  -- the row of the cell of a profile is its field labelling
  change fieldLab I (entry I i) (embed3 I d) = ⊥
  rw [embed3_apply, fieldLab_old, hi]

/-- **The top layer has a cell reading `⊥` at the grade `3` and at the grade `4`**: for `N = 3` or
`N = 4`, some cell of `TowerProfile.top I` at `(univ, N)` reads every old cell of the amalgam as
`⊥` (the cell of the `⊥` entry of the profile layer, kept by the field layer, and the cell of the
`⊥` entry of the field layer). -/
theorem exists_top_row_eq_bot {N : ℕ} (hN : N = 3 ∨ N = 4) :
    ∃ u : Fin (top I).card,
      (top I).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), N) ∧
      ∀ (d : Fin I.amalgam.card)
        (hd : embed4 I d ∈ (top I).toCellScheme.below ((top I).toCellScheme.gradedIndex u)),
        (top I).rows.row u ⟨_, hd⟩ = ⊥ := by
  rcases hN with rfl | rfl
  · obtain ⟨u, hu, hrow⟩ := exists_scheme_row_eq_bot (I := I)
    refine ⟨Fin.castAdd _ u, ?_, fun d hd ↦ ?_⟩
    · rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, hu]
    · have hd' : embed3 I d ∈ (scheme I).toCellScheme.below
          ((scheme I).toCellScheme.gradedIndex u) := by
        have := hd
        rw [CellScheme.mem_below, embed4_apply, Scheme.appendFullCellsScheme_gradedIndex_castAdd,
          Scheme.appendFullCellsScheme_gradedIndex_castAdd] at this
        exact this
      rw [← hrow d hd']
      have key := congrArg (fun R : (scheme I).toCellScheme.Rows ↦ R.row u ⟨embed3 I d, hd'⟩)
        (Scheme.comap_rows_fieldLayer (S := scheme I) (k := 4) (hS := not_univ_four_le))
      exact key
  · obtain ⟨u, hu, hrow⟩ := Scheme.exists_fieldLayer_row_eq_bot (scheme I) 4 not_univ_four_le
    exact ⟨u, hu, fun d hd ↦ hrow (embed3 I d) hd⟩

end TowerProfile

namespace Scheme

/-- The row of an old cell at an old cell after appending a cell of full scope is the old row. -/
theorem appendFullCell_row_castSucc_castSucc {n : ℕ} {S : Scheme.{u} n} {j : ℕ}
    {r : Fin (S.card + 1) → Label.{u}}
    {h : ∀ d, ¬ ((univ : Finset (Fin n)), j) ≤ S.toCellScheme.gradedIndex d} (s t : Fin S.card)
    (ht : t ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex s))
    (ht' : t.castSucc ∈ (S.appendFullCell j r h).toCellScheme.below
      ((S.appendFullCell j r h).toCellScheme.gradedIndex s.castSucc)) :
    (S.appendFullCell j r h).rows.row s.castSucc ⟨_, ht'⟩ = S.rows.row s ⟨t, ht⟩ := by
  have key := congrArg (fun R : S.toCellScheme.Rows ↦ R.row s ⟨t, ht⟩)
    (comap_rows_castSucc (S := S) (j := j) (r := r) (h := h))
  simpa only [CellScheme.Rows.comap_row] using key

end Scheme

namespace TowerProfile

open ProfileCatalogue (Profile)

variable {α : Ordinal.{u}}

/-- **The profile completion is not a cap-reading extension** at a cap of grade `3` or `4`.  Let `I`
be a seed on five points at a stage zero or a limit, `f` an embedding of `k` points into the
common face, `D` a stage type on `k + 1` points with a new cell labelled `μ + n` (`μ` zero or a
limit), and `b` a cell of the first coatom type of grade `N ∈ {3, 4}` with `k < N`.  Then the
coatom extension with apex built from the profile completion
(`CompletionBelowFullGrade.completion` of `TowerProfile.completion I`) is not a cap-reading
extension of the first coatom type along `f.trans Fin.castSuccEmb` for `D` and `b`: the cell of the
`⊥` entry at `(univ, N)` (`TowerProfile.exists_top_row_eq_bot`) reads the new cell as `⊥`. -/
theorem not_isCapReadingExtension_completion (hα : Order.IsSuccPrelimit α) (I : Seed.{u} α 3)
    {k : ℕ} (f : Fin k ↪ Fin 3) (D : StageType.{u} α (k + 1)) (b : Fin I.left.card)
    (hN : I.left.toCellScheme.grade b = 3 ∨ I.left.toCellScheme.grade b = 4)
    (hk : k < I.left.toCellScheme.grade b) {j : Fin D.card}
    (hj : Fin.last k ∈ D.toCellScheme.scope j) {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ)
    {n : ℕ} (hD : D.label j = ((μ + n : Ordinal.{u}) : Label.{u})) :
    ¬ StageType.IsCapReadingExtension I.left (f.trans Fin.castSuccEmb) D b
      ((completion I).completion hα).toScheme := by
  intro hcap
  set E := ((completion I).completion hα).toScheme with hEdef
  set N := I.left.toCellScheme.grade b
  obtain ⟨hE, -, hT, hf, hED, b', hb'b, hread⟩ := hcap
  obtain ⟨u₀, hu₀, hrow₀⟩ := exists_top_row_eq_bot (I := I) hN
  -- the cell `u₀` of the top layer, as a cell of the coatom extension
  have hu : E.toCellScheme.gradedIndex (Fin.castSucc u₀) = ((univ : Finset (Fin 5)), N) :=
    (Scheme.appendFullCellScheme_gradedIndex_castSucc _ _ u₀).trans hu₀
  -- the new cell `j` of `D`, as a cell of the face along `f` followed by the new point
  have hcard : (E.comap (extendByLast (f.trans Fin.castSuccEmb))).card = D.card :=
    congrArg Scheme.card hED
  set i : Fin (E.comap (extendByLast (f.trans Fin.castSuccEmb))).card := Fin.cast hcard.symm j
  have hr := hread (Fin.castSucc u₀) hu i j rfl hj
  rw [hD] at hr
  set e := E.cellMap (extendByLast (f.trans Fin.castSuccEmb)) i with he_def
  -- the grade of `e` is at most `k + 1 ≤ N`, and its scope is not the ground set
  have hwf := hE.isWellFormed.comap (extendByLast (f.trans Fin.castSuccEmb)) hf
  have hge : E.toCellScheme.grade e ≤ N := by
    have h1 := (hwf.isWellFormed.grade_le_card i).trans
      ((card_le_univ _).trans_eq (Fintype.card_fin (k + 1)))
    -- the grade of a cell of the face is the grade of its image
    change (E.comap (extendByLast (f.trans Fin.castSuccEmb))).toCellScheme.grade i ≤ N
    omega
  have hscope : E.toCellScheme.scope e ≠ univ := by
    intro hu'
    have hsub := E.cellMap_mem (extendByLast (f.trans Fin.castSuccEmb)) i
    rw [Scheme.visibleCells, Finset.mem_filter, ← he_def, hu'] at hsub
    have hc := card_le_card hsub.2
    rw [card_map, Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin] at hc
    omega
  have he : e ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex (Fin.castSucc u₀)) := by
    rw [CellScheme.mem_below, hu]
    exact ⟨subset_univ _, hge⟩
  have hgb : E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b') = N :=
    Scheme.grade_congr hT hb'b
  have hb : E.cellMap Fin.castSuccEmb b' ∈
      E.toCellScheme.below (E.toCellScheme.gradedIndex (Fin.castSucc u₀)) := by
    rw [CellScheme.mem_below, hu]
    exact ⟨subset_univ _, hgb.le⟩
  refine StageType.not_readsThroughCap_of_row_eq_bot he hb ?_ hμ n hr
  -- `e` is an old cell of the top layer, of scope other than the ground set
  have hne : e ≠ Fin.last _ := by
    intro hl
    apply hscope
    rw [hl]
    exact Scheme.appendFullCellScheme_scope_last _ _
  obtain ⟨z, hz⟩ : ∃ z : Fin (top I).card, Fin.castSucc z = e :=
    ⟨e.castPred hne, Fin.castSucc_castPred e hne⟩
  have hzs : (top I).toCellScheme.scope z ≠ univ := by
    rw [← Scheme.appendFullCellScheme_scope_castSucc (top I) 5 z]
    rw [hz]
    exact hscope
  obtain ⟨d, rfl⟩ := mem_range_embed4 z hzs
  have hd : embed4 I d ∈ (top I).toCellScheme.below ((top I).toCellScheme.gradedIndex u₀) := by
    -- the cell scheme of the coatom extension is the top layer with the apex appended
    have h1 : ((top I).appendFullCellScheme 5).gradedIndex (Fin.castSucc (embed4 I d)) ≤
        ((top I).appendFullCellScheme 5).gradedIndex (Fin.castSucc u₀) := hz ▸ he
    rw [Scheme.appendFullCellScheme_gradedIndex_castSucc,
      Scheme.appendFullCellScheme_gradedIndex_castSucc] at h1
    exact h1
  have key := Scheme.appendFullCell_row_castSucc_castSucc (S := top I) (j := 5)
    (h := (completion I).isLegalBelowFullGrade.not_le) u₀ (embed4 I d) hd (hz ▸ he)
  rw [hrow₀ d hd] at key
  exact (E.rows.row_congr rfl hz.symm).trans key

end TowerProfile

end VaughtConjecture
