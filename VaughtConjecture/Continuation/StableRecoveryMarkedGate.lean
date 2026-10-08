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
`Scheme.markedLayer_cap_eq_bot_of_readsOnly`).  If the row of the marked cell `m` is `⊥` at every
leaf (in particular if it reads only marked cells), its cap is `⊥`: the leaf with the same entry is
read at the cross height `min (agreement height) (cap)`, and the agreement height of an entry with
itself is the top point `gridPoint k (2 * S.card + 2)` of the field grid, above every cap.

**A marked cell of cap `⊥` is `⊥` in a lawful extension of every labelling**
(`Scheme.exists_isLawfulBelow_markedLayer_eq_bot`).  The extension at `⊥` through the leaf whose
entry is the orbit code of the splice (`Scheme.exists_isLawfulBelow_sheetLayer`) labels the marked
cell by the orbit decoder of the cross height of the leaf and the marked cell, which is `⊥`: the
agreement height `A` of the two entries is `⊥`, or else the two entries agree capped at the grid
point `A`, short and self-visible, so their caps agree capped at `A`
(`Scheme.CapRespects`) and the cap of the leaf is `⊥` too.

**The obstruction** (`TowerProfile.exists_isLawful_markedTop_eq_bot`).  For every marked
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

namespace Scheme

variable {n k : ℕ} {S : Scheme.{u} n} {Mk : Finset (Fin S.card → Label.{u})}
  {κ : (Fin S.card → Label.{u}) → Label.{u}}
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- **A marked cell whose row is `⊥` at every leaf has cap `⊥`.**  The leaf with the entry of the
marked cell is read at the cross height `min (agreement height) (cap)`, and the agreement height of
an entry with itself is the top point `gridPoint k (2 * S.card + 2)` of the field grid, above every
cap in the field grid. -/
theorem markedLayer_cap_eq_bot_of_row_leaf (hMk : Mk ⊆ S.catalogue k)
    (hκ : ∀ e, κ e ∈ S.fieldGrid k) (m : Fin Mk.card)
    (hleaf : ∀ (i : Fin (S.catalogue k).card) (t), (S.markedLayer k Mk κ hS).rows.row
      (Fin.natAdd S.card (Fin.natAdd _ m)) t = ⊥ ∨
        t.1 ≠ Fin.natAdd S.card (Fin.castAdd Mk.card i)) :
    κ (S.markEntry Mk m) = ⊥ := by
  obtain ⟨j₀, hj₀, hσ⟩ := exists_leaf_eq (Mk := Mk) (hMk (markEntry_mem Mk m))
  obtain ⟨i, rfl⟩ : ∃ i, Fin.castAdd Mk.card i = j₀ := by
    induction j₀ using Fin.addCases with
    | left i => exact ⟨i, rfl⟩
    | right m' => rw [markedSheet_natAdd] at hσ; exact absurd hσ (by decide)
  have hmem : Fin.natAdd S.card (Fin.castAdd Mk.card i) ∈
      (S.markedLayer k Mk κ hS).toCellScheme.below
        ((S.markedLayer k Mk κ hS).toCellScheme.gradedIndex
          (Fin.natAdd S.card (Fin.natAdd _ m))) := by
    rw [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_natAdd,
      appendFullCellsScheme_gradedIndex_natAdd]
  rcases hleaf i ⟨_, hmem⟩ with h | h
  · rw [sheetLayer_row_natAdd, sheetRow_natAdd, crossHeight_of_ne (by simp), hj₀,
      markedEntry_natAdd, agreementHeight_self (gridPoint_mem_grid le_rfl)
        fun x hx ↦ le_gridPoint_of_mem_grid hx,
      min_eq_right (le_gridPoint_of_mem_grid (hκ _))] at h
    exact h
  · exact absurd rfl h

/-- **A marked cell that reads only marked cells has cap `⊥`**: its row is `⊥` at every leaf
(`Scheme.markedLayer_cap_eq_bot_of_row_leaf`). -/
theorem markedLayer_cap_eq_bot_of_readsOnly (hMk : Mk ⊆ S.catalogue k)
    (hκ : ∀ e, κ e ∈ S.fieldGrid k) (m : Fin Mk.card) {T : Set (Fin (S.markedLayer k Mk κ hS).card)}
    (honly : (S.markedLayer k Mk κ hS).rows.ReadsOnly (Fin.natAdd S.card (Fin.natAdd _ m)) T)
    (hT : ∀ i : Fin (S.catalogue k).card, Fin.natAdd S.card (Fin.castAdd Mk.card i) ∉ T) :
    κ (S.markEntry Mk m) = ⊥ := by
  refine markedLayer_cap_eq_bot_of_row_leaf (hS := hS) hMk hκ m fun i t ↦ ?_
  by_cases ht : t.1 = Fin.natAdd S.card (Fin.castAdd Mk.card i)
  · left
    have hgi : (S.markedLayer k Mk κ hS).toCellScheme.gradedIndex t.1 =
        (S.markedLayer k Mk κ hS).toCellScheme.gradedIndex
          (Fin.natAdd S.card (Fin.natAdd _ m)) := by
      rw [ht, appendFullCellsScheme_gradedIndex_natAdd, appendFullCellsScheme_gradedIndex_natAdd]
    have hne : t.1 ≠ Fin.natAdd S.card (Fin.natAdd _ m) := by
      rw [ht]
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    have h := honly t.1 hgi hne (ht ▸ hT i)
    exact (S.markedLayer k Mk κ hS).rows.row_congr rfl rfl |>.trans h
  · exact .inr ht

/-- **A marked cell of cap `⊥` is `⊥` in a lawful extension of every labelling**: every labelling
`p` lawful below `(univ, k)` in `S` extends, unchanged at the old cells of grade at most `k`, to a
labelling lawful below `(univ, k)` in the leaf-and-marked layer that is `⊥` at the marked cell.  It
is the extension at `⊥` through the leaf of the orbit code of the splice of `p`. -/
theorem exists_isLawfulBelow_markedLayer_eq_bot (hMk : Mk ⊆ S.catalogue k)
    (hκ : ∀ e, κ e ∈ S.fieldGrid k) (hκr : CapRespects S k κ) (m : Fin Mk.card)
    (hm : κ (S.markEntry Mk m) = ⊥) {p : Fin S.card → Label.{u}}
    (hp : S.rows.IsLawfulBelow (univ, k) fun d ↦ p d) :
    ∃ r : (S.markedLayer k Mk κ hS).toCellScheme.below (univ, k) → Label.{u},
      (S.markedLayer k Mk κ hS).rows.IsLawfulBelow (univ, k) r ∧
        (∀ d (hd : S.toCellScheme.grade d ≤ k),
          r ⟨Fin.castAdd _ d, castAdd_mem_below_sheetLayer hd⟩ = p d) ∧
        r ⟨Fin.natAdd S.card (Fin.natAdd _ m), natAdd_mem_below_sheetLayer _⟩ = ⊥ := by
  set b := orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) p)
  have hb : b ∈ S.catalogue k := orbitCode_splice_bot_mem_catalogue hp
  obtain ⟨j₀, hj₀, hσ⟩ := exists_leaf_eq (Mk := Mk) hb
  obtain ⟨r, hr, hrp, hrx⟩ := exists_isLawfulBelow_sheetLayer (hS := hS)
    (markedEntry_mem hMk) hκ hκr (σ := markedSheet _ _) hj₀
  refine ⟨r, hr, hrp, ?_⟩
  rw [hrx, sheetRow_natAdd, crossHeight_of_ne (by rw [hσ, markedSheet_natAdd]; decide), hj₀,
    markedEntry_natAdd]
  -- the cross height of the leaf and the marked cell is `⊥`
  set e := S.markEntry Mk m
  have he : e ∈ S.catalogue k := hMk (markEntry_mem Mk m)
  obtain ⟨hA, hAag⟩ := agreementHeight_spec (bot_mem_grid k (2 * S.card + 2)) b e
  have hcross : min (agreementHeight (S.fieldGrid k) b e) (κ b) = ⊥ := by
    rcases eq_or_ne (agreementHeight (S.fieldGrid k) b e) ⊥ with h0 | h0
    · rw [h0]
      exact min_eq_left bot_le
    have hcap := hκr b hb e he _ (isSelfVisible_of_mem_grid hA) (isShort_of_mem_grid hA) hAag
    rw [hm, min_bot_left, min_comm] at hcap
    exact hcap
  rw [hcross]
  exact orbitDecoder_bot

end Scheme

namespace TowerProfile

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} (D : MarkedSpec I)

/-- **No marked gate in the marked top.**  For every marked specification `D` of a seed on five
points and every marked cell `m` whose row is `⊥` at every leaf (for instance a gate reading only
marked cells), some lawful labelling of the marked top extends the glued labelling of the amalgam
and is `⊥` at `m`.  So no marked cell is a gate that is not `⊥` in every lawful labelling with the
face of the first coatom type. -/
theorem exists_isLawful_markedTop_eq_bot (m : Fin D.marks.card)
    (hleaf : ∀ (i : Fin ((scheme I).catalogue 4).card) (t), (markedTop I D).rows.row
      (Fin.natAdd (scheme I).card (Fin.natAdd _ m)) t = ⊥ ∨
        t.1 ≠ Fin.natAdd (scheme I).card (Fin.castAdd D.marks.card i)) :
    ∃ q : Fin (markedTop I D).card → Label.{u}, (markedTop I D).rows.IsLawful q ∧
      (∀ d, q (markedEmbed I D d) = I.amalgam.label d) ∧
      q (Fin.natAdd (scheme I).card (Fin.natAdd _ m)) = ⊥ := by
  have hm := Scheme.markedLayer_cap_eq_bot_of_row_leaf (hS := not_univ_four_le) D.marks_subset
    D.cap_mem m hleaf
  -- a lawful labelling of the profile layer extending the glued labelling
  obtain ⟨q₀, hq₀, hq₀e⟩ := exists_isLawful_markedTop D
  have hp : (scheme I).rows.IsLawful fun d ↦ q₀ (Fin.castAdd _ d) := by
    have h := hq₀.comap (Scheme.isLowerEmbedding_castAdd (S := scheme I) 4 _ _ not_univ_four_le)
    rwa [Scheme.comap_rows_sheetLayer (hS := not_univ_four_le)] at h
  obtain ⟨r, hr, hrp, hrm⟩ := Scheme.exists_isLawfulBelow_markedLayer_eq_bot
    (hS := not_univ_four_le) D.marks_subset D.cap_mem D.capRespects m hm
    (p := fun d ↦ q₀ (Fin.castAdd _ d)) (hp.isLawfulBelow (univ, 4))
  have hall (z : Fin (markedTop I D).card) : z ∈ (markedTop I D).toCellScheme.below (univ, 4) :=
    ⟨subset_univ _, by
      have := grade_markedTop_lt D z
      -- the grade of the pair below is the grade of the cell
      change (markedTop I D).toCellScheme.grade z ≤ 4
      omega⟩
  refine ⟨fun z ↦ r ⟨z, hall z⟩, hr.isLawful hall, fun d ↦ ?_, hrm⟩
  have hd : (scheme I).toCellScheme.grade (embed3 I d) ≤ 4 := by
    have h1 := (isLowerEmbedding_embed3 (I := I)).grade_eq d
    have h2 := I.grade_lt d
    omega
  rw [← hq₀e d]
  exact hrp (embed3 I d) hd

/-- **The marked top has a cell reading `⊥` at the grade `3` and at the grade `4`**: the cell of the
`⊥` profile of the profile layer, and the leaf of the `⊥` entry of the catalogue.  Both read every
old cell of the amalgam as `⊥`. -/
theorem exists_markedTop_row_eq_bot {N : ℕ} (hN : N = 3 ∨ N = 4) :
    ∃ u : Fin (markedTop I D).card,
      (markedTop I D).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), N) ∧
      ∀ (d : Fin I.amalgam.card)
        (hd : markedEmbed I D d ∈
          (markedTop I D).toCellScheme.below ((markedTop I D).toCellScheme.gradedIndex u)),
        (markedTop I D).rows.row u ⟨_, hd⟩ = ⊥ := by
  rcases hN with rfl | rfl
  · obtain ⟨u, hu, hrow⟩ := exists_scheme_row_eq_bot (I := I)
    refine ⟨Fin.castAdd _ u, ?_, fun d hd ↦ ?_⟩
    · rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, hu]
    · have hd' : embed3 I d ∈ (scheme I).toCellScheme.below
          ((scheme I).toCellScheme.gradedIndex u) := by
        have := hd
        rw [CellScheme.mem_below, markedEmbed_apply,
          Scheme.appendFullCellsScheme_gradedIndex_castAdd,
          Scheme.appendFullCellsScheme_gradedIndex_castAdd] at this
        exact this
      rw [← hrow d hd']
      have key := congrArg (fun R : (scheme I).toCellScheme.Rows ↦ R.row u ⟨embed3 I d, hd'⟩)
        (Scheme.comap_rows_sheetLayer (S := scheme I) (k := 4) (hS := not_univ_four_le)
          (ε := (scheme I).markedEntry 4 D.marks) (σ := Scheme.markedSheet _ _) (κ := D.cap))
      exact key
  · obtain ⟨j₀, hj₀, -⟩ := Scheme.exists_leaf_eq (Mk := D.marks) (Scheme.bot_mem_catalogue
      (scheme I) 4)
    refine ⟨Fin.natAdd _ j₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ 4 _ j₀,
      fun d hd ↦ ?_⟩
    rw [Scheme.sheetLayer_row_natAdd (hS := not_univ_four_le)]
    -- the row of a leaf at an old cell is its entry
    change (scheme I).sheetRow 4 ((scheme I).markedEntry 4 D.marks) (Scheme.markedSheet _ _)
      D.cap j₀ (Fin.castAdd _ (embed3 I d)) = ⊥
    rw [Scheme.sheetRow_castAdd, hj₀]

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
