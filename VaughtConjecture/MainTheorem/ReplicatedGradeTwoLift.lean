/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedGradeStateStep
import VaughtConjecture.Extension.LadderTowerContextLiftOne
import VaughtConjecture.Extension.ReplicatedServingCell
import VaughtConjecture.Extension.ReplicatedContextGap

/-!
# The one-level lift at the grade two

Roadmap, Layer 3 ((R3) and (R4), the context lift of the replicated scheme at one level).

**The statement** (`Seed.cappedLift_two`, compiled; at the tie input `TieInstance.cappedLift_two`):
for a seed with `m = 1` (so the grade `2` is the top grade), requests calibrated on the class with
the labels pair admitted, the relative lift on the exact class and threshold `2`, and a context
cell at `(univ, 2)`, the **one-level scheme** — the replicated scheme with values the code grid
`codeGrid 2 B` (`2 · #cells ≤ B ≤ B'`) and the catalogue predicate `Seed.attachAdmitsCoded`
(admitted, and canonical for the orbit code at `2`) — lifts capped from the context coatom into
`(univ, 2)`.

**The composition.**  `CellScheme.Rows.cappedLift_of_ownerCappedLift` from the lift at the grade
one (`Seed.cappedLift_context_one`) and owner-capped lifts at every cap self-visible at `2`: at the
cap `⊥` (`Seed.hasOwnerCappedLifts_bot`), and at a positive cap from the serving rows
(`CellScheme.Rows.hasOwnerCappedLifts_of_rows_short`), whose four inputs are the consistency of the
rows (`Seed.isConsistent_replicated`), shortness and no formal top
(`Seed.isShort_ne_top_rowBelow`), and the short lift at the row
(`Seed.cappedLiftAtShort_rowBelow`).

**The four labels** are kept apart: the ambient is the row of the serving cell, the writing of its
state `R` (`Seed.exists_rowAt_eq_replicatedWriting`); the coded values are those of
`codeGrid 2 B`; the external cap is the cap of the owner-capped lift; the source cut is the cut `h`
of the short lift.

**The cell classes** of the capped agreement with the row (`Seed.replicatedWriting_cases`): the
cells of the attachment and the ladder (values `⊥`, `1`, values of the state), the cells of the
layer `2` (agreement heights, self-visible at `2`), and the copies (their originals).  The decoder
`orbitDecoder 2 W h` keeps each capped at `h` (`Label.min_orbitDecoder_eq_of_writingValue`): a code
is read as its value, `1` on the natural strip literally (`Label.orbitDecoder_one`), a height off
the strip; and the writings of the code and of `R` agree capped at `h`
(`Seed.min_replicatedWriting_eq_of_cut`).

**Scope.**  The grade `2` with `m = 1` only: at a grade `k ≥ 3` the heights of the lower layers lie
on the strips of the cuts (`Label.lowerHeight_strip_jump`, `Scheme.not_isStripFree_heightSet`), in
every block `b ≥ 1` (`Scheme.not_isStripFreeOffNatural_heightSet`); the block `0`, the natural
strip, is read literally at every grade (`Label.orbitDecoder_of_natural`,
`Label.natural_cut_no_jump`).
The one-level scheme is not the scheme of the choice of the assembly (`Seed.seedValues`,
`Seed.attachAdmits`): its values are the code grid and its catalogue keeps the canonical states
only.

## References

Bountifulness is [Kni26, Definition 2.5.14]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Label

/-- The key of `1` at a grade `k ≥ 2` is the least grid point `k`. -/
theorem visibilityReplace_one_eq_gridPoint {k : ℕ} (hk : 2 ≤ k) :
    visibilityReplace k k (1 : Label.{u}) = gridPoint k 0 := by
  have h : (1 : Label.{u}) = gridPoint 1 0 := by simp [gridPoint]
  rw [h]
  exact visibilityReplace_gridPoint_of_lt (by omega) 0

/-- **A code with the natural key is an orbit key with the natural key**: if the key of the code
of a cell is at most the least grid point `ω * 0 + k`, the cell's value is not `⊥`, its code block
is `0`, so (`Label.le_codeBlock`, the key rank being positive) its value is an orbit key with the
natural key `ω * 0 + k`. -/
theorem natural_of_visibilityReplace_orbitCode_le {k : ℕ} {ι : Type*} [Fintype ι]
    {W : ι → Label.{u}} {e : ι} (hWe : W e ≠ ⊥)
    (hle : visibilityReplace k k (orbitCode k W e) ≤ gridPoint k 0) :
    visibilityReplace k k (orbitCode k W e) = gridPoint k 0 ∧ IsOrbitKey k W (W e) ∧
      visibilityReplace k k (W e) = gridPoint k 0 := by
  have hve : visibilityReplace k k (orbitCode k W e) = gridPoint k (codeBlock k W (W e)) := by
    rw [orbitCode_apply]
    exact visibilityReplace_orbitMap hWe
  have hcb : codeBlock k W (W e) = 0 := by
    rw [hve] at hle
    exact Nat.le_zero.mp (gridPoint_le_gridPoint.mp hle)
  have hnat : IsOrbitKey k W (W e) ∧ visibilityReplace k k (W e) = gridPoint k 0 := by
    by_contra hn
    have h2 := le_codeBlock hn
    have h3 := one_le_keyRank (isKey_apply_iff.mpr hWe : IsKey k W (W e))
    rw [hcb] at h2
    omega
  exact ⟨by rw [hve, hcb], hnat⟩

/-- **The natural strip is read literally** at every grade: a label `x` on the strip of the least
grid point `ω * 0 + k` (a finite label below `k`, or `k` itself) and below the cut `h` is read by
`orbitDecoder k W h` as `x`.  A cell whose code has key at least `h` and at most the key of `x` has
the natural key and an orbit key value (`Label.natural_of_visibilityReplace_orbitCode_le`), and
its reading of `x` moves `x` to the block `0` of its value, which is `x`. -/
theorem orbitDecoder_of_natural {k : ℕ} {ι : Type*} [Fintype ι] {W : ι → Label.{u}}
    {h x : Label.{u}} (hx : visibilityReplace k k x = gridPoint k 0) (hxh : x < h) :
    orbitDecoder k W h x = x := by
  classical
  unfold orbitDecoder
  rw [min_eq_left hxh.le]
  refine max_eq_left (Finset.sup_le fun e he ↦ ?_)
  have hhe : h ≤ visibilityReplace k k (orbitCode k W e) := (Finset.mem_filter.mp he).2
  by_cases hlt : visibilityReplace k k x < visibilityReplace k k (orbitCode k W e)
  · rw [cellReading, ite_eq_left hlt]
    exact bot_le
  have hWe : W e ≠ ⊥ := by
    intro h0
    rw [orbitCode_eq_bot_iff.mpr h0, visibilityReplace_bot] at hhe
    exact absurd ((bot_le.trans_lt hxh).trans_le hhe) (lt_irrefl _)
  obtain ⟨hve, hkey, hWk⟩ :=
    natural_of_visibilityReplace_orbitCode_le hWe (hx ▸ not_lt.mp hlt)
  have hc : visibilityReplace k k x = visibilityReplace k k (orbitCode k W e) ∧
      IsOrbitKey k W (W e) := ⟨hx.trans hve.symm, hkey⟩
  rw [cellReading, ite_eq_right hlt, ite_eq_left hc, moveToBlock_eq_self (hWk.trans hx.symm)]

/-- **The natural strip is read literally**: at a grade `k ≥ 2` and a cut `h` above `1`, the orbit
decoder reads `1` as `1` (`Label.orbitDecoder_of_natural`). -/
theorem orbitDecoder_one {k : ℕ} (hk : 2 ≤ k) {ι : Type*} [Fintype ι] {W : ι → Label.{u}}
    {h : Label.{u}} (h1 : (1 : Label.{u}) < h) : orbitDecoder k W h 1 = 1 :=
  orbitDecoder_of_natural (visibilityReplace_one_eq_gridPoint hk) h1

/-- **On the natural strip the decoder keeps every label capped at the cut**, whatever `W` and the
cut: above the cut both are the cut, below it the label is read literally. -/
theorem min_orbitDecoder_eq_of_natural {k : ℕ} {ι : Type*} [Fintype ι] {W : ι → Label.{u}}
    {h x : Label.{u}} (hx : visibilityReplace k k x = gridPoint k 0) :
    min (orbitDecoder k W h x) h = min x h := by
  rcases le_or_gt h x with hhx | hxh
  · rw [min_eq_right hhx]
    exact min_eq_right ((min_eq_right hhx).symm.trans_le (le_max_left _ _))
  · rw [orbitDecoder_of_natural hx hxh]

/-- **No strip jump in the block `0`**: a cell whose code is the natural cut `ω * 0 + k` has an
orbit key value, so the hypothesis `¬ IsOrbitKey k W (W e)` of
`Label.le_orbitDecoder_of_code_at_cut` fails there; and every lower-layer grid height
`ω * 0 + j`, `j < k`, below that cut is read literally (`Label.orbitDecoder_of_natural`),
whatever the codes.  So a cut in the block `0` asks no strip freedom (contrast
`Label.lowerHeight_strip_jump`, in a block `b ≥ 1`). -/
theorem natural_cut_no_jump {j k : ℕ} (hj : j < k) {ι : Type*} [Fintype ι] {W : ι → Label.{u}} :
    (∀ e, orbitCode k W e = gridPoint k 0 → IsOrbitKey k W (W e)) ∧
      orbitDecoder k W (gridPoint k 0) (gridPoint j 0) = gridPoint j 0 := by
  refine ⟨fun e he ↦ ?_, orbitDecoder_of_natural (visibilityReplace_gridPoint_of_lt hj 0)
    (gridPoint_lt_gridPoint_iff_lex.mpr (.inr ⟨rfl, hj⟩))⟩
  have hWe : W e ≠ ⊥ := fun h0 ↦ gridPoint_ne_bot k 0 (he ▸ orbitCode_eq_bot_iff.mpr h0)
  have hle : visibilityReplace k k (orbitCode k W e) ≤ gridPoint k 0 := by
    rw [he, isSelfVisible_gridPoint k 0]
  exact (natural_of_visibilityReplace_orbitCode_le hWe hle).2.1

/-- **The orbit decoder keeps the labels of a writing capped at the cut** (a grade `k ≥ 2`, the
code `orbitCode k W` agreeing with `W` capped at `h`): at `⊥`, at `1`, at a code value and at a
label self-visible at `k`, `orbitDecoder k W h` agrees with the identity capped at `h`.  Above
the cut both are the cut; a code is read as its value (`Label.orbitDecoder_orbitCode`); below the
cut off its strip the decoder is the identity
(`Label.orbitDecoder_of_visibilityReplace_lt`); a label self-visible at `k` below the cut is off
its strip; `1` on the strip of the cut is read literally (`Label.orbitDecoder_one`). -/
theorem min_orbitDecoder_eq_of_writingValue {k : ℕ} (hk : 2 ≤ k) {ι : Type*} [Fintype ι]
    {W : ι → Label.{u}} {h y : Label.{u}} (hag : ∀ d, min (orbitCode k W d) h = min (W d) h)
    (hy : y = ⊥ ∨ y = 1 ∨ (∃ d, y = orbitCode k W d) ∨ IsSelfVisible k y) :
    min (orbitDecoder k W h y) h = min y h := by
  classical
  rcases le_or_gt h y with hhy | hyh
  · rw [min_eq_right hhy]
    exact min_eq_right ((min_eq_right hhy).symm.trans_le (le_max_left _ _))
  rcases hy with rfl | rfl | ⟨d, rfl⟩ | hv
  · rw [orbitDecoder_bot]
  · rw [orbitDecoder_one hk hyh]
  · rw [orbitDecoder_orbitCode hag d, hag d]
  · rw [orbitDecoder_of_visibilityReplace_lt hyh (hv.symm ▸ hyh)]

/-- **A cut short at `2` below the top is a grid point**: a label self-visible and short at `2`,
other than `⊥`, at most `ω * B' + 2`, is `ω * b + 2` for some `b ≤ B'`. -/
theorem exists_eq_gridPoint_two {h : Label.{u}} {B' : ℕ} (hh : IsSelfVisible 2 h)
    (hs : IsShort 2 h) (h0 : h ≠ ⊥) (hle : h ≤ gridPoint 2 B') :
    ∃ b ≤ B', h = gridPoint 2 b := by
  rcases lt_omega0_sq_iff.mp (hle.trans_lt (gridPoint_lt_omega0_sq 2 B')) with h' | ⟨i, j, rfl⟩
  · exact absurd h' h0
  have hj1 : j ≤ 2 := by
    have := isShort_coe.mp hs
    rw [omega0_mul_add_natCast_mod] at this
    exact_mod_cast this
  have hj2 : 2 ≤ j := by
    have := isSelfVisible_coe.mp hh
    rw [omega0_mul_add_natCast_mod] at this
    exact_mod_cast this
  obtain rfl : j = 2 := by omega
  exact ⟨i, gridPoint_le_gridPoint.mp hle, rfl⟩

end Label

namespace Scheme

/-- **Strip freedom off the natural strip** (the refined invariant at a grade `k ≥ 3`): as
`Scheme.IsStripFree`, for the cuts other than the natural cut `ω * 0 + k`.  At the natural cut the
decoder reads its whole strip literally and no code there jumps (`Label.natural_cut_no_jump`), so
the block `0` asks nothing. -/
def IsStripFreeOffNatural (G : ℕ → Finset Label.{u}) (Γ : Finset Label.{u}) (M : ℕ) : Prop :=
  ∀ j k, 2 ≤ j → j < k → k ≤ M → ∀ x ∈ G j, ∀ c ∈ G k, c ∈ Γ → c ≠ gridPoint k 0 →
    ¬ (visibilityReplace k k x = c ∧ x < c)

theorem IsStripFree.offNatural {G : ℕ → Finset Label.{u}} {Γ : Finset Label.{u}} {M : ℕ}
    (h : IsStripFree G Γ M) : IsStripFreeOffNatural G Γ M :=
  fun j k hj hjk hkM x hx c hc hcΓ _ ↦ h j k hj hjk hkM x hx c hc hcΓ

/-- **The current heights fail strip freedom off the natural strip as well**: a cut `ω * b + k`,
`k ≥ 3`, of a block `b ≥ 1` has the layer-`2` grid height `ω * b + 2` on its strip below it. -/
theorem not_isStripFreeOffNatural_heightSet {Γ : Finset Label.{u}} {B' k b M : ℕ} (hk : 3 ≤ k)
    (hkM : k ≤ M) (hb1 : 1 ≤ b) (hb : b ≤ B') (hc : gridPoint k b ∈ Γ) :
    ¬ IsStripFreeOffNatural (fun j ↦ heightSet Γ B' j) Γ M := fun h ↦
  h 2 k le_rfl (by omega) hkM (gridPoint 2 b) (mem_heightSet.mpr (.inl (gridPoint_mem_grid hb)))
    (gridPoint k b) (mem_heightSet.mpr (.inr ⟨hc, isSelfVisible_gridPoint k b⟩)) hc
    (fun he ↦ by have := gridPoint_le_gridPoint.mp he.le; omega)
    ⟨Label.visibilityReplace_gridPoint_of_lt (by omega) b,
      gridPoint_lt_gridPoint_iff_lex.mpr (.inr ⟨rfl, by omega⟩)⟩

variable {n : ℕ} {σ : Type*}

/-- **A new cell of a layer reads the writing of its state**: if the entry of the new cell `i` of
the next layer is the writing of `R`, its row is the writing of `R` in the next layer at every
cell below it (the old cells through the entry, the new cells through the agreement heights). -/
theorem LayerTower.rowAt_next_natAdd {k : ℕ} (T : LayerTower.{u} n σ k) (Cs : Finset σ)
    (Gs : Finset Label.{u}) (i : Fin (T.entries Cs).card) {R : σ}
    (hR : T.v R = layerEntry (T.entries Cs) i) (z : Fin (T.next Cs Gs).S.card)
    (hz : z ∈ (T.next Cs Gs).S.toCellScheme.below
      ((T.next Cs Gs).S.toCellScheme.gradedIndex (Fin.natAdd _ i))) :
    (T.next Cs Gs).S.rowAt (Fin.natAdd _ i) z = (T.next Cs Gs).v R z := by
  change (T.S.catalogueLayer (k + 2) (fun d ↦ d) Gs (T.entries Cs) T.not_le).rowAt _ z =
    layerRow T.S (fun d ↦ d) Gs (T.entries Cs) (T.v R) z
  induction z using Fin.addCases with
  | left t =>
    have hgt : T.S.toCellScheme.grade t ≤ k + 2 := by
      have h : (T.S.appendFullCellsScheme (k + 2) _).grade (Fin.castAdd _ t) ≤
          (T.S.appendFullCellsScheme (k + 2) _).grade (Fin.natAdd _ i) := hz.2
      rwa [appendFullCellsScheme_grade_castAdd, appendFullCellsScheme_grade_natAdd] at h
    rw [rowAt_catalogueLayer_castAdd i hgt, layerRow_castAdd, hR]
  | right i' =>
    rw [rowAt_catalogueLayer_natAdd, layerRow_natAdd, hR]

end Scheme

namespace Seed

variable {α : Ordinal.{u}} {n : ℕ} {I : Seed.{u} α 1} {g : Fin n ↪ Fin 1} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- The replicated scheme. -/
local notation "𝔼" => Seed.replicated I g H Γ A B'

/-- **A serving row at the grade `2` is the writing of its state** (`m = 1`, the top layer): a cell
`u` of the replicated scheme at `(univ, 2)` is the cell of a state `R` of the catalogue at `2`, and
its row at every cell below it is the writing of `R` (`Seed.replicatedWriting`): on the cells of
the tower through the entry and the agreement heights of its layer
(`Scheme.LayerTower.rowAt_next_natAdd`), on the copies through their originals. -/
theorem exists_rowAt_eq_replicatedWriting {u : Fin (𝔼).card}
    (hu : (𝔼).toCellScheme.gradedIndex u = ((univ : Finset (Fin 3)), 2)) :
    ∃ R ∈ (I.attachmentBase g).towerCat Γ A 2, ∀ z,
      z ∈ (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex u) →
      (𝔼).rowAt u z = I.replicatedWriting g H Γ A B' R z := by
  classical
  obtain ⟨u, rfl⟩ : ∃ u' : Fin (I.attachTower g H Γ A B').card, u = Fin.castAdd _ u' := by
    induction u using Fin.addCases with
    | left u => exact ⟨u, rfl⟩
    | right jj =>
      exfalso
      exact ((I.mem_mixedFaces g).mp (scope_replicated_natAdd jj)).2.1 (congrArg Prod.fst hu)
  have hmir (z : Fin (𝔼).card)
      (hz : z ∈ (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex (Fin.castAdd _ u))) :
      (𝔼).rowAt (Fin.castAdd _ u) z = (I.attachTower g H Γ A B').rowAt u
        ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) z) ∧
      (I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) z ∈
        (I.attachTower g H Γ A B').toCellScheme.below
          ((I.attachTower g H Γ A B').toCellScheme.gradedIndex u) := by
    have h1 := Scheme.rowAt_mirror_of_mem hz
    have h2 := (Scheme.mirrorData (I.not_subset_scope_tower g H Γ A B')).orig_mem_below hz
    rw [Scheme.mirrorOrig_castAdd] at h1
    change _ ∈ (I.attachTower g H Γ A B').toCellScheme.below
      ((I.attachTower g H Γ A B').toCellScheme.gradedIndex
        ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (Fin.castAdd _ u))) at h2
    rw [Scheme.mirrorOrig_castAdd] at h2
    exact ⟨h1, h2⟩
  set T := (I.attachmentBase g).towerBase H with hT
  set C2 := (I.attachmentBase g).towerCat Γ A 2 with hC2
  have hu' : (T.S.catalogueLayer 2 (fun d ↦ d) (Scheme.heightSet Γ B' 2) (T.entries C2)
      T.not_le).toCellScheme.gradedIndex u = ((univ : Finset (Fin 3)), 2) :=
    (Scheme.gradedIndex_mirror_castAdd u).symm.trans hu
  obtain ⟨i, rfl⟩ := Scheme.exists_eq_natAdd_of_gradedIndex_catalogueLayer hu'
  obtain ⟨R, hR, hRe⟩ := mem_image.mp (Scheme.layerEntry_mem (C := T.entries C2) i)
  refine ⟨R, hR, fun z hz ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hmir z hz
  rw [h1]
  exact T.rowAt_next_natAdd C2 (Scheme.heightSet Γ B' 2) i hRe _ h2

/-- **The values of a writing at the grade `2`** (`m = 1`): the writing of a lawful state `R` is,
at every cell, `⊥`, `1`, a value of `R` (the cells of the attachment and the ladder,
`Scheme.LadderBaseData.stateExt_eq`), or a height of the layer `2` (the agreement heights of the
layer); a copy reads its original. -/
theorem replicatedWriting_cases (hcard : (I.attachmentBase g).S.card ≤ H)
    {R : Fin (I.attachment g).card → Label.{u}} (hR : (I.attachment g).rows.IsLawful R)
    (z : Fin (𝔼).card) :
    I.replicatedWriting g H Γ A B' R z = ⊥ ∨ I.replicatedWriting g H Γ A B' R z = 1 ∨
      (∃ a, I.replicatedWriting g H Γ A B' R z = R a) ∨
      I.replicatedWriting g H Γ A B' R z ∈ Scheme.heightSet Γ B' 2 := by
  classical
  set T := (I.attachmentBase g).towerBase H with hT
  set C2 := (I.attachmentBase g).towerCat Γ A 2 with hC2
  have key (t : Fin (T.next C2 (Scheme.heightSet Γ B' 2)).S.card) :
      (T.next C2 (Scheme.heightSet Γ B' 2)).v R t = ⊥ ∨
        (T.next C2 (Scheme.heightSet Γ B' 2)).v R t = 1 ∨
        (∃ a, (T.next C2 (Scheme.heightSet Γ B' 2)).v R t = R a) ∨
        (T.next C2 (Scheme.heightSet Γ B' 2)).v R t ∈ Scheme.heightSet Γ B' 2 := by
    induction t using Fin.addCases with
    | left x =>
      have e : (T.next C2 (Scheme.heightSet Γ B' 2)).v R (Fin.castAdd _ x) =
          (I.attachmentBase g).stateExt H R x :=
        Scheme.layerRow_castAdd (S := T.S) (read := fun d ↦ d) (G := Scheme.heightSet Γ B' 2)
          (C := T.entries C2) (T.v R) x
      rw [e]
      rcases Scheme.LadderBaseData.stateExt_eq hR hcard x with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
    | right i =>
      have e : (T.next C2 (Scheme.heightSet Γ B' 2)).v R (Fin.natAdd _ i) =
          agreementHeight (Scheme.heightSet Γ B' 2) (T.v R)
            (Scheme.layerEntry (T.entries C2) i) :=
        Scheme.layerRow_natAdd (S := T.S) (read := fun d ↦ d) (G := Scheme.heightSet Γ B' 2)
          (C := T.entries C2) (T.v R) i
      rw [e]
      exact .inr (.inr (.inr (agreementHeight_spec (Scheme.bot_mem_heightSet _ _ _) _ _).1))
  exact key ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) z)

/-! ### The coded catalogue and the lift of a lawful admitted state -/

variable {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

variable (I g) in
/-- **The catalogue predicate of the one-level scheme**: admitted (`Seed.attachAdmits`) and
canonical for the orbit code at the grade `2`. -/
def attachAdmitsCoded
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    (Q : GrowthRequests I.left d.toScheme) (K : ℕ)
    (R : Fin (I.attachmentBase g).S.card → Label.{u}) : Prop :=
  I.attachAdmits g hd Q K R ∧ orbitCode 2 R = R

theorem attachAdmitsCoded_succ
    {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
    {Q : GrowthRequests I.left d.toScheme} (k : ℕ) (R : Fin (I.attachmentBase g).S.card → Label.{u})
    (h : I.attachAdmitsCoded g hd Q (k + 3) R) : I.attachAdmitsCoded g hd Q (k + 2) R :=
  ⟨I.attachAdmits_succ g hd Q k R h.1, h.2⟩

/-- The code grid at the grade `2` lies below the top grid point `ω * B' + 2`, `B ≤ B'`. -/
theorem le_gridPoint_of_mem_codeGrid_two {B B' : ℕ} (hBB : B ≤ B') :
    ∀ x ∈ codeGrid.{u} 2 B, x ≤ gridPoint 2 B' := by
  intro x hx
  rcases mem_codeGrid.mp hx with rfl | ⟨b, hb, f, hf, rfl⟩
  · exact bot_le
  · change gridPoint f b ≤ gridPoint 2 B'
    exact gridPoint_le_gridPoint_iff_lex.mpr (by omega)

/-- **The orbit code of a lawful admitted state is in the coded catalogue** at every grade: values
in the code grid (`Label.orbitMap_mem_codeGrid`), lawful at the top grade
(`Seed.isLawful_orbitCode_top`), admitted (`Seed.attachAdmits_comp_of_le`), canonical
(`Label.orbitCode_orbitCode`). -/
theorem orbitCode_mem_towerCat_coded
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) (hth : Q.threshold ≤ 2)
    {B : ℕ} (hB : 2 * (I.attachment g).card ≤ B) {W : Fin (I.attachment g).card → Label.{u}}
    (hW : (I.attachment g).rows.IsLawful W) {K₀ : ℕ} (hK₀ : Q.threshold ≤ K₀)
    (hWA : I.attachAdmits g hd Q K₀ W) (K : ℕ) :
    orbitCode 2 W ∈ (I.attachmentBase g).towerCat (codeGrid 2 B) (I.attachAdmitsCoded g hd Q) K :=
  Scheme.LadderBaseData.mem_towerCat.mpr ⟨fun _ ↦ orbitMap_mem_codeGrid (by simpa using hB) _,
    isLawful_orbitCode_top hW,
    attachAdmits_comp_of_le hd hQ hK₀ hth hWA (isWitness_orbitMap 2 W)
      (fun _ ↦ orbitMap_eq_bot_iff) K, orbitCode_orbitCode⟩

/-- **A context cell below the context coatom**: a cell of the attachment below
`(ctxCoatom 1, j)` is the cell of a context cell of grade at most `j`. -/
theorem exists_attachCtxCell_eq {j : ℕ} {a : Fin (I.attachment g).card}
    (ha : a ∈ (I.attachment g).toCellScheme.below (ctxCoatom 1, j)) :
    ∃ x, I.attachCtxCell g x = a ∧ I.left.toCellScheme.grade x ≤ j := by
  have hvis : a ∈ (I.attachment g).visibleCells Fin.castSuccEmb := by
    rw [Scheme.mem_visibleCells]
    intro z hz
    have hz' : z ∈ univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) := by
      rw [map_castSuccEmb_eq_ctxCoatom]
      exact ha.1 (mem_coe.mp hz)
    obtain ⟨y, -, rfl⟩ := mem_map.mp hz'
    exact ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := StageType.exists_faceCell_eq (I.restrictFace_left_attachmentType g) hvis
  exact ⟨x, rfl, (grade_attachCtxCell x).symm.trans_le ha.2⟩

/-- **A state literal on the context section reads the prescription**: if `W` is the context
section of `f` at the context cells of grade at most `j`, then `W` is `f` at every cell of the
attachment below the context coatom. -/
theorem eq_of_ctxSection {j : ℕ}
    {f : (𝔼).toCellScheme.below (ctxCoatom 1, j) → Label.{u}}
    {W : Fin (I.attachment g).card → Label.{u}}
    (hW : ∀ x, I.left.toCellScheme.grade x ≤ j → W (I.attachCtxCell g x) = ctxSection H Γ A B' f x)
    (e : (𝔼).toCellScheme.below (ctxCoatom 1, j)) (a : Fin (I.attachment g).card)
    (ha : I.attachEmb g H Γ A B' a = e.1) : W a = f e := by
  have hab : a ∈ (I.attachment g).toCellScheme.below (ctxCoatom 1, j) :=
    (attachEmb_mem_below_iff a _).mp (ha ▸ e.2)
  obtain ⟨x, rfl, hx⟩ := exists_attachCtxCell_eq hab
  rw [hW x hx]
  exact (prescriptionState_of_mem _ hab).trans (congrArg f (Subtype.ext ha))

/-- **The decoded writing of the orbit code of a lawful admitted state is lawful** below
`(univ, 2)` in the one-level scheme (values `codeGrid 2 B`, predicate `Seed.attachAdmitsCoded`):
the orbit decoder at a cut `h ≠ ⊥` self-visible at `2` is a witness bounded by `2` sending only `⊥`
to `⊥` (`Seed.isLawfulBelow_map_replicatedWriting`). -/
theorem isLawfulBelow_decodedWriting (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) (hth : Q.threshold ≤ 2)
    {B : ℕ} (hB : 2 * (I.attachment g).card ≤ B) (hBB : B ≤ B')
    {W : Fin (I.attachment g).card → Label.{u}} (hW : (I.attachment g).rows.IsLawful W)
    (hWA : I.attachAdmits g hd Q 2 W) {h : Label.{u}} (hh : IsSelfVisible 2 h) (h0 : h ≠ ⊥) :
    (I.replicated g H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q) B').rows.IsLawfulBelow
      ((univ : Finset (Fin 3)), 2) fun z ↦ orbitDecoder 2 W h
        (I.replicatedWriting g H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q) B'
          (orbitCode 2 W) z) :=
  isLawfulBelow_map_replicatedWriting hH hcard (le_gridPoint_of_mem_codeGrid_two hBB)
    attachAdmitsCoded_succ (orbitCode_mem_towerCat_coded hd hQ hth hB hW hth hWA _) _
    (isWitness_orbitDecoder hh h0) fun _ hx ↦ eq_bot_of_orbitDecoder_eq_bot h0 hx

/-- **The writings of two states of the code grid agreeing capped at a cut agree capped at it**
(`m = 1`): when the cut is a height of the layer `2`, by
`Scheme.LadderBaseData.min_v_eq_of_mem_heightSet`; otherwise it lies above the top
`ω * B' + 2` of the heights (`Label.exists_eq_gridPoint_two`), so above every value of the code
grid, and the two states are equal. -/
theorem min_replicatedWriting_eq_of_cut (hcard : (I.attachmentBase g).S.card ≤ H) {B : ℕ}
    (hBB : B ≤ B') {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop}
    {R R' : Fin (I.attachment g).card → Label.{u}} (hR : (I.attachment g).rows.IsLawful R)
    (hR' : (I.attachment g).rows.IsLawful R') (hRΓ : ∀ a, R a ∈ codeGrid.{u} 2 B)
    (hR'Γ : ∀ a, R' a ∈ codeGrid.{u} 2 B) {h : Label.{u}} (hh : IsSelfVisible 2 h)
    (hs : IsShort 2 h) (h0 : h ≠ ⊥) (hag : ∀ a, min (R' a) h = min (R a) h)
    (z : Fin (I.replicated g H (codeGrid 2 B) A B').card) :
    min (I.replicatedWriting g H (codeGrid 2 B) A B' R' z) h =
      min (I.replicatedWriting g H (codeGrid 2 B) A B' R z) h := by
  by_cases hmem : h ∈ Scheme.heightSet (codeGrid 2 B) B' 2
  · exact Scheme.LadderBaseData.min_v_eq_of_mem_heightSet hcard h0 (hh.mono (by omega)) hR hR'
      hag 1 (fun K' hK' ↦ by obtain rfl : K' = 0 := (by omega); exact hmem) _
  · have hlt : ∀ x ∈ codeGrid.{u} 2 B, x < h := by
      intro x hx
      by_contra hle
      have hhB : h ≤ gridPoint 2 B' :=
        (not_lt.mp hle).trans (le_gridPoint_of_mem_codeGrid_two hBB x hx)
      obtain ⟨b, hb, rfl⟩ := exists_eq_gridPoint_two hh hs h0 hhB
      exact hmem (Scheme.mem_heightSet.mpr (.inl (gridPoint_mem_grid hb)))
    have hRR : R' = R := funext fun a ↦ by
      have e := hag a
      rwa [min_eq_left (hlt _ (hR'Γ a)).le, min_eq_left (hlt _ (hRΓ a)).le] at e
    rw [hRR]

/-- **The serving-row short lift at the grade `2`** (`m = 1`, the one-level scheme: values
`codeGrid 2 B`, predicate `Seed.attachAdmitsCoded`, threshold `2`): for every cell `u` at
`(univ, 2)`, the rows lift capped from the context coatom to `(univ, 2)` at the ambient given by
the row of `u`, at every cut `h` self-visible and short at `2`.  The labels are kept distinct: the
ambient is the row of `u`, the writing of its state `R` (`Seed.exists_rowAt_eq_replicatedWriting`);
the coded values are those of `codeGrid 2 B`; the cut is `h`; the prescription is `f`.
* **The state step** (`Seed.exists_stateStep_threshold`, unconditional at the threshold): the
  context section of `f` and the anchor `R` give a lawful admitted state `W`, literal on the
  context and agreeing with `R` capped at `h`.
* **The code** `P = orbitCode 2 W` is in the catalogue (`Seed.orbitCode_mem_towerCat_coded`) and
  agrees with `R` capped at `h` (`Label.min_orbitCode_eq`, `R` canonical).
* **The lift** is the decoded writing `orbitDecoder 2 W h ∘ w_P`, lawful
  (`Seed.isLawfulBelow_decodedWriting`), reading `P` as `W` on the attachment, hence `f` on the
  context (`Label.orbitDecoder_orbitCode`, `Seed.eq_of_ctxSection`).
* **The cell classes for the capped agreement with the row of `u`**: every value of the writing of
  `P` is `⊥`, `1`, a value of `P`, or a height of the layer `2` (`Seed.replicatedWriting_cases`;
  the cells of the attachment and the ladder, the agreement heights of the layer, and the copies
  through their originals); the decoder keeps each capped at `h`
  (`Label.min_orbitDecoder_eq_of_writingValue`: a value of `P` is read as its value of `W`, the
  ladder value `1` on the natural strip is read literally, a height is self-visible at `2`, off the
  strip); and the writings of `P` and `R` agree capped at `h`
  (`Seed.min_replicatedWriting_eq_of_cut`). -/
theorem cappedLiftAtShort_rowBelow (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hth : Q.threshold = 2) {B : ℕ} (hB : 2 * (I.attachment g).card ≤ B) (hBB : B ≤ B')
    {u : Fin (I.replicated g H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q) B').card}
    (hu : (I.replicated g H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q) B').toCellScheme.gradedIndex
      u = ((univ : Finset (Fin 3)), 2)) :
    (I.replicated g H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q) B').rows.CappedLiftAtShort
      (ctxCoatom_le 2)
      ((I.replicated g H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q) B').rows.rowBelow u hu) := by
  intro h hh hs hb f hf _ hfS
  obtain ⟨R, hRC, hrow⟩ := exists_rowAt_eq_replicatedWriting hu
  obtain ⟨hRΓ, hRl, hRA, hRcan⟩ := Scheme.LadderBaseData.mem_towerCat.mp hRC
  have hS (e : (I.replicated g H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q) B').toCellScheme.below
      ((univ : Finset (Fin 3)), 2)) :
      (I.replicated g H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q) B').rows.rowBelow u hu e =
        I.replicatedWriting g H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q) B' R e.1 := by
    have hmem : e.1 ∈ (I.replicated g H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q)
        B').toCellScheme.below ((I.replicated g H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q)
          B').toCellScheme.gradedIndex u) := by
      rw [hu]; exact e.2
    exact (Scheme.rowAt_of_mem hmem).symm.trans (hrow e.1 hmem)
  set w := ctxSection H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q) B' f with hw
  have hwl : I.left.rows.IsLawful w := isLawful_ctxSection hf
  have hwR (x : Fin I.left.card) (hx : I.left.toCellScheme.grade x ≤ 2) :
      min (w x) h = min (R (I.attachCtxCell g x)) h := by
    have hmem : I.attachCtxCell g x ∈ (I.attachment g).toCellScheme.below (ctxCoatom 1, 2) :=
      ⟨scope_attachCtxCell_subset x, (grade_attachCtxCell x).trans_le hx⟩
    have h1 : w x = f ⟨_, (attachEmb_mem_below_iff _ _).mpr hmem⟩ := prescriptionState_of_mem _ hmem
    rw [h1, hfS, hS, replicatedWriting_attachEmb hcard hRl]
  obtain ⟨W, hWctx, hWl2, hWA, hWR⟩ := exists_stateStep_threshold hte hdp hdL hn hd hQ hpair hrel
    hth (by norm_num) hRl hRA hh (hwl.isLawfulBelow _) hwR
  have hWl : (I.attachment g).rows.IsLawful W :=
    Rows.isLawful_of_isLawfulBelow (X := ((univ : Finset (Fin 3)), 2))
      (fun a ↦ ⟨subset_univ _, grade_attachment_le a⟩) hWl2
  have hPR : ∀ a, min (orbitCode 2 W a) h = min (R a) h := min_orbitCode_eq hh hs hRcan hWR
  have hPW : ∀ a, min (orbitCode 2 W a) h = min (W a) h := fun a ↦ (hPR a).trans (hWR a).symm
  have hPC := orbitCode_mem_towerCat_coded hd hQ hth.le hB hWl hth.le hWA 2
  obtain ⟨hPΓ, hPl, -⟩ := Scheme.LadderBaseData.mem_towerCat.mp hPC
  refine ⟨fun z ↦ orbitDecoder 2 W h (I.replicatedWriting g H (codeGrid 2 B)
      (I.attachAdmitsCoded g hd Q) B' (orbitCode 2 W) z.1),
    isLawfulBelow_decodedWriting hH hcard hd hQ hth.le hB hBB hWl hWA hh hb.ne', fun e ↦ ?_,
    fun z ↦ ?_⟩
  · obtain ⟨a, ha⟩ := exists_attachEmb_eq_of_mem_below_ctx e.2
    change orbitDecoder 2 W h (I.replicatedWriting g H (codeGrid 2 B)
      (I.attachAdmitsCoded g hd Q) B' (orbitCode 2 W) e.1) = f e
    rw [← ha, replicatedWriting_attachEmb hcard hPl, orbitDecoder_orbitCode hPW]
    exact eq_of_ctxSection hWctx e a ha
  · rw [hS z, ← min_replicatedWriting_eq_of_cut hcard hBB hRl hPl hRΓ hPΓ hh hs hb.ne' hPR z.1]
    refine min_orbitDecoder_eq_of_writingValue le_rfl hPW ?_
    rcases replicatedWriting_cases hcard hPl z.1 with h1 | h1 | ⟨a, h1⟩ | h1
    · exact .inl h1
    · exact .inr (.inl h1)
    · exact .inr (.inr (.inl ⟨a, h1⟩))
    · exact .inr (.inr (.inr (Scheme.isSelfVisible_of_mem_heightSet h1)))

/-- **The owner-capped lift at the cap `⊥`** (`m = 1`, the one-level scheme, threshold `2`): the
prescription capped at its owner label `M` is lawful below the context coatom; the state step at
the cut `⊥` from the bottom anchor (`Seed.exists_stateStep_threshold`) gives a lawful admitted
state literal on its context section, and the decoded writing of its orbit code at the cut
`ω * 0 + 2` (`Label.min_orbitCode_gridPoint_zero`: the code agrees with the state capped there)
is a lawful section below `(univ, 2)` reading the capped prescription on the context coatom.  At
the cap `⊥` the capped agreement with the ambient is void. -/
theorem hasOwnerCappedLifts_bot (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hth : Q.threshold = 2) {B : ℕ} (hB : 2 * (I.attachment g).card ≤ B) (hBB : B ≤ B') :
    (I.replicated g H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q) B').rows.HasOwnerCappedLifts
      (erase_subset (Fin.last 2) univ) 1 ⊥ := by
  intro p q hp _ _ o ho _ _
  have hM : IsSelfVisible (1 + 1) (p o) := hp.isSelfVisible_of_gradedIndex_eq ho
  have hp' := hp.min_const_of_isSelfVisible hM
  set w := ctxSection H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q) B' (fun e ↦ min (p e) (p o))
    with hw
  have hwl : I.left.rows.IsLawful w := isLawful_ctxSection hp'
  obtain ⟨W, hWctx, hWl2, hWA, -⟩ := exists_stateStep_threshold hte hdp hdL hn hd hQ hpair hrel
    hth (by norm_num) (R₀ := fun _ ↦ ⊥) Rows.isLawful_const_bot (I.attachAdmits_bot g hd Q 2)
    (isSelfVisible_bot 2) (hwl.isLawfulBelow _) fun _ _ ↦ by rw [min_bot_right, min_bot_right]
  have hWl : (I.attachment g).rows.IsLawful W :=
    Rows.isLawful_of_isLawfulBelow (X := ((univ : Finset (Fin 3)), 2))
      (fun a ↦ ⟨subset_univ _, grade_attachment_le a⟩) hWl2
  have hPW : ∀ a, min (orbitCode 2 W a) (gridPoint 2 0) = min (W a) (gridPoint 2 0) :=
    min_orbitCode_gridPoint_zero
  obtain ⟨-, hPl, -⟩ := Scheme.LadderBaseData.mem_towerCat.mp
    (orbitCode_mem_towerCat_coded hd hQ hth.le hB hWl hth.le hWA 2)
  refine ⟨fun z ↦ orbitDecoder 2 W (gridPoint 2 0) (I.replicatedWriting g H (codeGrid 2 B)
      (I.attachAdmitsCoded g hd Q) B' (orbitCode 2 W) z.1),
    isLawfulBelow_decodedWriting hH hcard hd hQ hth.le hB hBB hWl hWA
      (isSelfVisible_gridPoint 2 0) (gridPoint_ne_bot 2 0), fun e ↦ ?_,
    fun _ ↦ by rw [min_bot_right, min_bot_right]⟩
  obtain ⟨a, ha⟩ := exists_attachEmb_eq_of_mem_below_ctx e.2
  change orbitDecoder 2 W (gridPoint 2 0) (I.replicatedWriting g H (codeGrid 2 B)
    (I.attachAdmitsCoded g hd Q) B' (orbitCode 2 W) e.1) = min (p e) (p o)
  rw [← ha, replicatedWriting_attachEmb hcard hPl, orbitDecoder_orbitCode hPW]
  exact eq_of_ctxSection hWctx e a ha

/-- `1` is short at `2`. -/
theorem isShort_one_two : IsShort 2 (1 : Label.{u}) := by
  have h : (1 : Label.{u}) = gridPoint 1 0 := by simp [gridPoint]
  rw [h, gridPoint, isShort_coe, omega0_mul_add_natCast_mod]
  exact_mod_cast (by norm_num : 1 ≤ 2)

/-- **The serving rows at the grade `2` are short and never the formal top** (the one-level
scheme): the row of a cell at `(univ, 2)` is the writing of a state of the code grid
(`Seed.exists_rowAt_eq_replicatedWriting`), whose values are `⊥`, `1`, values of the code grid
and heights of the layer `2` (`Seed.replicatedWriting_cases`). -/
theorem isShort_ne_top_rowBelow (hcard : (I.attachmentBase g).S.card ≤ H) {B : ℕ}
    (hBB : B ≤ B') {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop}
    {u : Fin (I.replicated g H (codeGrid 2 B) A B').card}
    (hu : (I.replicated g H (codeGrid 2 B) A B').toCellScheme.gradedIndex u =
      ((univ : Finset (Fin 3)), 2))
    (e : (I.replicated g H (codeGrid 2 B) A B').toCellScheme.below ((univ : Finset (Fin 3)), 2)) :
    IsShort 2 ((I.replicated g H (codeGrid 2 B) A B').rows.rowBelow u hu e) ∧
      (I.replicated g H (codeGrid 2 B) A B').rows.rowBelow u hu e ≠ ⊤ := by
  obtain ⟨R, hRC, hrow⟩ := exists_rowAt_eq_replicatedWriting hu
  obtain ⟨hRΓ, hRl, -⟩ := Scheme.LadderBaseData.mem_towerCat.mp hRC
  have hmem : e.1 ∈ (I.replicated g H (codeGrid 2 B) A B').toCellScheme.below
      ((I.replicated g H (codeGrid 2 B) A B').toCellScheme.gradedIndex u) := by
    rw [hu]; exact e.2
  have hS : (I.replicated g H (codeGrid 2 B) A B').rows.rowBelow u hu e =
      I.replicatedWriting g H (codeGrid 2 B) A B' R e.1 :=
    (Scheme.rowAt_of_mem hmem).symm.trans (hrow e.1 hmem)
  have hΓ := le_gridPoint_of_mem_codeGrid_two.{u} hBB
  have htop : ∀ x : Label.{u}, x ≤ gridPoint 2 B' → x ≠ ⊤ := fun x hx ↦
    ne_top_of_le_ne_top (gridPoint_ne_top 2 B') hx
  rw [hS]
  rcases replicatedWriting_cases hcard hRl e.1 with h1 | h1 | ⟨a, h1⟩ | h1
  · rw [h1]; exact ⟨isShort_bot 2, bot_ne_top⟩
  · rw [h1]
    refine ⟨isShort_one_two, ?_⟩
    have h : (1 : Label.{u}) = gridPoint 1 0 := by simp [gridPoint]
    rw [h]
    exact gridPoint_ne_top 1 0
  · rw [h1]; exact ⟨isShort_of_mem_codeGrid (hRΓ a), htop _ (hΓ _ (hRΓ a))⟩
  · refine ⟨(Scheme.mem_heightSet.mp h1).elim isShort_of_mem_grid
      fun hx ↦ isShort_of_mem_codeGrid hx.1, htop _ ?_⟩
    exact Scheme.le_gridPoint_of_mem_heightSet hΓ le_rfl h1

/-- **The context lift at the grade `2` on the one level** (`m = 1`; values `codeGrid 2 B`,
predicate `Seed.attachAdmitsCoded`, threshold `2`, a context cell at `(univ, 2)`): the composition
of the lift at the grade one (`Seed.cappedLift_context_one`) and the owner-capped lifts at every
cap self-visible at `2` (`CellScheme.Rows.cappedLift_of_ownerCappedLift`): at the cap `⊥`
(`Seed.hasOwnerCappedLifts_bot`), and at a positive cap from the serving rows
(`CellScheme.Rows.hasOwnerCappedLifts_of_rows_short`: consistent rows,
`Seed.isConsistent_replicated`; short and never the formal top, `Seed.isShort_ne_top_rowBelow`;
the short lift at the row, `Seed.cappedLiftAtShort_rowBelow`).  The serving cell exists for the
bottom state (`Seed.exists_cell_of_mem_towerCat`). -/
theorem cappedLift_two (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hth : Q.threshold = 2) {B : ℕ} (hB : 2 * (I.attachment g).card ≤ B) (hBB : B ≤ B')
    (hX : ∃ x : Fin I.left.card,
      I.left.toCellScheme.gradedIndex x = ((univ : Finset (Fin 2)), 2)) :
    (I.replicated g H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q) B').rows.CappedLift
      (X := (univ.erase (Fin.last 2), 2)) (Y := ((univ : Finset (Fin 3)), 2))
      ⟨erase_subset _ _, le_rfl⟩ := by
  have hlift1 := cappedLift_context_one (Γ := codeGrid 2 B) (A := I.attachAdmitsCoded g hd Q)
    (B' := B') hH hcard (donor_mem_faces hd) (root_mem_faces hte) (by rw [card_root]; exact hn)
  have hY : ∃ t : Fin (I.replicated g H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q) B').card,
      (I.replicated g H (codeGrid 2 B) (I.attachAdmitsCoded g hd Q) B').toCellScheme.gradedIndex
        t = ((univ : Finset (Fin 3)), 1 + 1) := by
    have hbot : (fun _ ↦ ⊥) ∈ (I.attachmentBase g).towerCat (codeGrid 2 B)
        (I.attachAdmitsCoded g hd Q) 2 :=
      Scheme.LadderBaseData.mem_towerCat.mpr ⟨fun _ ↦ mem_insert_self _ _,
        Rows.isLawful_const_bot, I.attachAdmits_bot g hd Q 2,
        funext fun _ ↦ orbitCode_eq_bot_iff.mpr rfl⟩
    obtain ⟨u, -, hu, -⟩ := exists_cell_of_mem_towerCat (B' := B') hcard le_rfl le_rfl hbot
    exact ⟨u, hu⟩
  refine Rows.cappedLift_of_ownerCappedLift (j := 1) (erase_subset _ _) ?_ hlift1 fun c hc ↦ ?_
  · obtain ⟨x, hx⟩ := hX
    refine ⟨I.attachEmb g H _ _ B' (I.attachCtxCell g x), ?_⟩
    rw [gradedIndex_attachEmb]
    refine Prod.ext ?_ ((grade_attachCtxCell x).trans (congrArg Prod.snd hx))
    change (I.attachment g).toCellScheme.scope (I.attachCtxCell g x) = _
    have hsx : I.left.toCellScheme.scope x = univ := congrArg Prod.fst hx
    rw [attachCtxCell, Scheme.scope_faceCell, hsx]
    exact map_castSuccEmb_eq_ctxCoatom
  · by_cases hc0 : c = ⊥
    · subst hc0
      exact hasOwnerCappedLifts_bot hH hcard hte hdp hdL hn hd hQ hpair hrel hth hB hBB
    · refine Rows.hasOwnerCappedLifts_of_rows_short (erase_subset _ _)
        (bot_lt_iff_ne_bot.mpr hc0) hc hY fun u hu ↦ ⟨isConsistent_replicated hH hcard
          (le_gridPoint_of_mem_codeGrid_two hBB) attachAdmitsCoded_succ u,
          fun e ↦ (isShort_ne_top_rowBelow hcard hBB hu e).1,
          fun e ↦ (isShort_ne_top_rowBelow hcard hBB hu e).2,
          cappedLiftAtShort_rowBelow hH hcard hte hdp hdL hn hd hQ hpair hrel hth hB hBB hu⟩

end Seed

namespace TieInstance

/-- The root of the input. -/
local notation "𝕣" => Function.Embedding.refl (Fin 1)

/-- The context lift at the grade `2` on the one level, for the first coatom type given up to
equality. -/
theorem cappedLift_two_aux {α : Ordinal.{u}} {I : Seed.{u} α 1} {t' : StageType.{u} α 2}
    (hI : I.left = t') {p : StageType.{u} α 1}
    {hte : restrictFace ((𝕣).trans Fin.castSuccEmb) t' = some p} {d : StageType.{u} α 2}
    (hdp : restrictFace Fin.castSuccEmb d = some p) (hdL : d.IsLegal)
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests t' d.toScheme} (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hdp) (hth : Q.threshold = 2)
    {H B B' : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕣).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕣).card ≤ B) (hBB : B ≤ B')
    (hX : ∃ x : Fin t'.card, t'.toCellScheme.gradedIndex x = ((univ : Finset (Fin 2)), 2)) :
    (I.replicated 𝕣 H (codeGrid 2 B) (I.attachAdmitsCoded 𝕣 hdA (hI ▸ Q)) B').rows.CappedLift
      (X := (univ.erase (Fin.last 2), 2)) (Y := ((univ : Finset (Fin 3)), 2))
      ⟨erase_subset _ _, le_rfl⟩ := by
  subst hI
  exact Seed.cappedLift_two hH hcard hte hdp hdL Nat.one_pos hdA hQ hpair hrel hth hB hBB hX

/-- **The context lift at the top grade `2` of the tie input, on the one level** (compiled end to
end): at every seed of the input, for the one-level scheme with values the code grid
`codeGrid 2 B` (`2 · #cells ≤ B ≤ B'`) and the coded catalogue predicate
(`Seed.attachAdmitsCoded`) over the requests `req ω` (threshold `2`), the rows lift capped from
the context coatom into `(univ, 2)` (`Seed.cappedLift_two`).  The context cell at `(univ, 2)` is
`r`. -/
theorem cappedLift_two (I : Seed.{u} ω 1) (hI : I.left = ctx ω)
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some (don ω))
    {H B B' : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕣).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕣).card ≤ B) (hBB : B ≤ B') :
    (I.replicated 𝕣 H (codeGrid 2 B) (I.attachAdmitsCoded 𝕣 hdA (hI ▸ req ω)) B').rows.CappedLift
      (X := (univ.erase (Fin.last 2), 2)) (Y := ((univ : Finset (Fin 3)), 2))
      ⟨erase_subset _ _, le_rfl⟩ :=
  cappedLift_two_aux hI (hte := restrictFace_ctx_root ω) (don_mem_cofaces ω).2
    (don_mem_cofaces ω).1 hdA (correctAt_req ω) (classCalibrated_req ω)
    (hasRelativeLiftOnClass_req ω) (threshold_req ω) hH hcard hB hBB ⟨cellR.{u} ω, rfl⟩

end TieInstance

end VaughtConjecture
