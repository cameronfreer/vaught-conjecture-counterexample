/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryProfileObstruction
import VaughtConjecture.Extension.MarkedCatalogueCompletion

/-!
# No reading gate in the leaf-and-marked completion

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.1 (the leaf-and-marked completion at `m = 3`); semantic contract, item 8.

The reading clause of a cap-reading extension (`StageType.IsCapReadingExtension`) asks every cell
at `(univ, N)` to read the new cells of `D` through the cap.  The leaf-and-marked layer
(`Scheme.markedLayer`, `TowerProfile.markedTop`) keeps one **leaf** for every entry of the
canonical catalogue, the constant `⊥` included (`Scheme.bot_mem_catalogue`), so at the grade `4`
the clause fails as in `VaughtConjecture.Continuation.StableRecoveryProfileObstruction`; the
profile layer at the grade `3` is unchanged.  A **gate** (`CellScheme.Rows.ReadsOnly`,
`CellScheme.Rows.IsLawful.recover_of_readsOnly`) would confine availability to chosen readers: a
cell `G` at `(univ, N)` whose row is `⊥` at every other cell there except the readers, provided
the label of `G` is not `⊥` in every lawful labelling that recovery has to serve.  This file shows
that a marked cell cannot be such a gate.  Each item below is compiled in this repository (theorem
named), unless marked otherwise.

**A marked gate has cap `⊥`** (`Scheme.markedLayer_cap_eq_bot_of_row_leaf`,
`Scheme.markedLayer_cap_eq_bot_of_readsOnly`, in `VaughtConjecture.Extension.MarkedCatalogue`).  If
the row of the marked cell `m` is `⊥` at every leaf (in particular if it reads only marked cells),
its cap is `⊥`: the leaf with the same entry is read at the cross height
`min (agreement height) (cap)`, and the agreement height of an entry with itself is the top point
`gridPoint k (2 * S.card + 2)` of the field grid, above every cap.

**A marked cell of cap `⊥` is `⊥` in a lawful extension of every labelling**
(`Scheme.exists_isLawfulBelow_markedLayer_eq_bot`, in `VaughtConjecture.Extension.MarkedCatalogue`).
The extension at `⊥` through the leaf whose
entry is the orbit code of the splice (`Scheme.exists_isLawfulBelow_sheetLayer`) labels the marked
cell by the orbit decoder of the cross height of the leaf and the marked cell, which is `⊥`: the
agreement height `A` of the two entries is `⊥`, or else the two entries agree capped at the grid
point `A`, short and self-visible, so their caps agree capped at `A`
(`Scheme.CapRespects`) and the cap of the leaf is `⊥` too.

**The obstruction** (`TowerProfile.exists_isLawful_markedTop_eq_bot`, in
`VaughtConjecture.Extension.MarkedCatalogueCompletion`, with the cells reading `⊥` at the grades
`3` and `4`, `TowerProfile.exists_markedTop_row_eq_bot`).  For every marked
specification `D` of a seed on five points and every marked cell whose row is `⊥` at every leaf,
some lawful labelling of the marked top extends the glued labelling of the amalgam (so has the
first coatom type as its face) and is `⊥` at that marked cell.  So the hypothesis `q G ≠ ⊥` of
`CellScheme.Rows.IsLawful.recover_of_readsOnly` fails for every marked gate, for every choice of
marks and cap: availability for the reading escapes through the leaves.  Turning this labelling
into a stage type at the stage (stage reduction, the apex labelled `⊥`) is argued, not formalized.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace TowerProfile

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} (D : MarkedSpec I)

/-- **The leaf-and-marked completion is not a cap-reading extension** at a cap of grade `3` or `4`,
for every marked specification: the cell of `TowerProfile.exists_markedTop_row_eq_bot` reads the
new cell as `⊥` (as in `TowerProfile.not_isCapReadingExtension_completion`). -/
theorem not_isCapReadingExtension_markedCompletion (hα : Order.IsSuccPrelimit α)
    {k : ℕ} (f : Fin k ↪ Fin 3) (Dn : StageType.{u} α (k + 1)) (b : Fin I.left.card)
    (hN : I.left.toCellScheme.grade b = 3 ∨ I.left.toCellScheme.grade b = 4)
    (hk : k < I.left.toCellScheme.grade b) {j : Fin Dn.card}
    (hj : Fin.last k ∈ Dn.toCellScheme.scope j) {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ)
    {n : ℕ} (hD : Dn.label j = ((μ + n : Ordinal.{u}) : Label.{u})) :
    ¬ StageType.IsCapReadingExtension I.left (f.trans Fin.castSuccEmb) Dn b
      ((markedCompletion I D).completion hα).toScheme := by
  intro hcap
  set E := ((markedCompletion I D).completion hα).toScheme with hEdef
  set N := I.left.toCellScheme.grade b
  obtain ⟨hE, -, hT, hf, hED, b', hb'b, hread⟩ := hcap
  obtain ⟨u₀, hu₀, hrow₀⟩ := exists_markedTop_row_eq_bot D hN
  -- the cell `u₀` of the top layer, as a cell of the coatom extension
  have hu : E.toCellScheme.gradedIndex (Fin.castSucc u₀) = ((univ : Finset (Fin 5)), N) :=
    (Scheme.appendFullCellScheme_gradedIndex_castSucc _ _ u₀).trans hu₀
  -- the new cell `j` of `D`, as a cell of the face along `f` followed by the new point
  have hcard : (E.comap (extendByLast (f.trans Fin.castSuccEmb))).card = Dn.card :=
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
  obtain ⟨z, hz⟩ : ∃ z : Fin (markedTop I D).card, Fin.castSucc z = e :=
    ⟨e.castPred hne, Fin.castSucc_castPred e hne⟩
  have hzs : (markedTop I D).toCellScheme.scope z ≠ univ := by
    rw [← Scheme.appendFullCellScheme_scope_castSucc (markedTop I D) 5 z]
    rw [hz]
    exact hscope
  obtain ⟨d, rfl⟩ := mem_range_markedEmbed D z hzs
  have hd : markedEmbed I D d ∈
      (markedTop I D).toCellScheme.below ((markedTop I D).toCellScheme.gradedIndex u₀) := by
    -- the cell scheme of the coatom extension is the top layer with the apex appended
    have h1 : ((markedTop I D).appendFullCellScheme 5).gradedIndex
        (Fin.castSucc (markedEmbed I D d)) ≤
        ((markedTop I D).appendFullCellScheme 5).gradedIndex (Fin.castSucc u₀) := hz ▸ he
    rw [Scheme.appendFullCellScheme_gradedIndex_castSucc,
      Scheme.appendFullCellScheme_gradedIndex_castSucc] at h1
    exact h1
  have key := Scheme.appendFullCell_row_castSucc_castSucc (S := markedTop I D) (j := 5)
    (h := (markedCompletion I D).isLegalBelowFullGrade.not_le) u₀ (markedEmbed I D d) hd (hz ▸ he)
  rw [hrow₀ d hd] at key
  exact (E.rows.row_congr rfl hz.symm).trans key

end TowerProfile

end VaughtConjecture
