/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedGradeLevel
import VaughtConjecture.Extension.LadderTowerContextLiftAmbient

/-!
# The state step at a grade

Roadmap, Layer 3 ((R3) and (R4), one level of the values per grade): from an anchor state of the
attachment and a context prescription agreeing with it capped at a cut `h`, a state of the
attachment literal on the context, lawful below the grade, admitted, and agreeing with the anchor
capped at `h` (`Seed.exists_stateStep`).

**The construction.**  The prescription, the anchor's context section and the anchor's donor
section are truncated at the grade `k` (`Scheme.isLawful_truncate`: lawful).  The donor step
(`StageType.exists_donorStep`) gives a lawful donor section reading the prescription on the root,
agreeing with the anchor's donor section capped at `h` at the donor cells of grade at most `k`,
and admitted with the prescription; the two sections glue over the attachment
(`StageType.exists_joint_extension`) to a lawful state.  Above the grade `k` the state is replaced
by the anchor: the lawfulness below `(univ, k)` and the admission (read at the threshold) are
unchanged, and the capped agreement holds at every cell.

**The premise on the anchor.**  From the threshold on, the donor step asks the admission of the
anchor's **truncation at `k`** (`hamb`).  The admission of the anchor (`Seed.attachAdmits`) is
that of its truncation at the threshold; the two coincide at `k = threshold`
(`Seed.exists_stateStep_threshold`), as at the top grade `2` of the tie input
(`TieInstance.exists_stateStep_two`) and at the grade `2` of the apex input, below its top grade
(`ApexInstance.exists_stateStep_two`).  Above the threshold the truncation at `k` keeps donor
values of grade in `(threshold, k]`; for an anchor in the catalogue its admission is the ambient
admission of the anchor's writing (`Seed.ambientAdmitted`), so the state step holds at every grade
(`Seed.exists_stateStep_of_mem_towerCat`; at the apex input at the grade `3`,
`ApexInstance.exists_stateStep_three`).  **Status**: unconditional at `k = threshold`; for
`k > threshold`, unconditional for an anchor in the catalogue and conditional on `hamb` for any
other anchor (`Seed.exists_stateStep`).

**Toward the serving-row short lift** (not proved here).  The lift of a serving row from the state
`W` would be `orbitDecoder k W h ∘ w_P`, with `P` the orbit code of `W`: it reads `P` literally as
`W` at the cells of the attachment, and is the identity below `h` off the strip of `h`
(`Label.orbitDecoder_of_visibilityReplace_lt`).  A code at the cut (forced when the anchor takes the
value `h`, as at the cut of `Seed.not_gap_of_context_cell`) makes it jump on the strip of `h`
(`Label.le_orbitDecoder_of_code_at_cut`): a row value on the strip of `h` below `h` that is not a
code value is read at least at `h`, against the capped agreement with the row.  At the grade `2`
the row values of the strip below a cut `ω * b + 2` are values `ω * b + 1` of the state, read
literally.  At a grade `k ≥ 3` the heights `ω * b + j`, `2 ≤ j < k`, of the lower layers lie on the
strip (`Label.lowerHeight_strip_jump`: a height of the layer `j` in `Scheme.heightSet Γ B' j`, on
the strip of `ω * b + k` and below it, read at least at `ω * b + k`; the hypotheses are met,
`Label.exists_strip_jump`, e.g. at `k = 3` the height `ω + 2` under the cut `ω + 3`).

**The invariant at a grade `k ≥ 3`** (stated, `Scheme.IsStripFree`; not implemented).  A lift of
a serving row at the grade `k` with the cut `h` (a cut of the grade `k`: a value of `Γ`, a height
of the layer `k`, `Seed.reachableCut_mem`) asks three things of the heights `G j` of the layers
`2 ≤ j ≤ m + 1`:
* (N2) **separation**: `h ∈ G k` (`Scheme.LadderBaseData.exists_cell_le_v_of_capAgree`; without
  it, the pin of `Seed.not_exists_lift_of_tie_of_pin`);
* (N3) **the cut is a height of every lower layer**, for the lift by a decoded writing:
  `h ∈ G j` for `2 ≤ j ≤ k` (the capped agreement of two writings,
  `Scheme.LadderBaseData.min_v_eq_of_mem_heightSet`, asks it at every layer; otherwise two states
  agreeing capped at `h` can have agreement heights differing below `h` at a cell of the layer
  `j`);
* (N4) **strip freedom**: no height of a layer `j < k` lies on the strip of `h` strictly below it
  (`Scheme.IsStripFree`).  The current heights violate (N4) (`Scheme.not_isStripFree_heightSet`;
  with the values `codeGrid (m + 1) B`, `m ≥ 2`, `Scheme.not_isStripFree_codeGrid`).
So heights of the layer `j` only at points `ω * b_j + j` of blocks of their own grade fail (N3):
a cut of the grade `k` must also be a height of every layer below `k`.

**Proposed heights and lemma** (exact statement; not implemented).  Choose from the seed block sets
`D k ⊆ {1, …, B' - 1}`, `2 ≤ k ≤ m + 1`, pairwise disjoint (for instance
`D k = {b | 1 ≤ b < B', b % (m + 2) = k}`); place the codes of the grade `k` in the blocks of
`D k` (finite parts at most `k`, so the cuts of the grade `k` are the points `ω * b + k`,
`b ∈ D k`); and take
```
G j = {⊥, ω * B' + j} ∪ {ω * b + k ∈ Γ | j ≤ k ≤ m + 1, b ∈ D k}.
```
Proposed lemma: `IsStripFree G Γ (m + 1)` (with the block `0` added below:
`IsStripFreeOffNatural G Γ (m + 1)`), that is, for all `2 ≤ j < k ≤ m + 1`, `x ∈ G j` and
`c ∈ G k ∩ Γ`, not (`visibilityReplace k k x = c` and `x < c`).  Proof: `c ≤ ω * B' + 2`, so
`c = ω * b + k` with `b ∈ D k`; a label on the strip of `c` lies in the block `b`; the only height
of `G j` in a block of `D k` is `ω * b + k = c` (the `D` are disjoint, `⊥` and `ω * B' + j` lie in
other blocks); so `x = c`.  (N2) and (N3): `ω * b + k ∈ G j` for every `j ≤ k`.  `G` keeps the
contract `Scheme.IsHeights` (bottom, self-visible at `j`, the top `ω * B' + j`, below it).

**What it changes.**  `Scheme.heightSet Γ B' j` (`Extension/BaseLadderTower.lean`: the grid
`grid j B'` of every block is replaced by the top point and the per-grade cut blocks, and `Γ` is
filtered by block and grade); the default heights `G` of `Scheme.LadderBaseData.ladderTower`,
`Seed.attachTower` and `Seed.replicated` (the argument `G (k + 2)` of `Scheme.layerTower`); the
orbit code's blocks (`Label.codeBlock`: `2 r` and `2 r - 1`) composed with an enumeration of
`D k`, and the code grid `codeGrid` accordingly.  The laws generic in `G` under `Scheme.IsHeights`
are unchanged (`Scheme.LadderBaseData.ladderTower_lawful_of_isHeights`,
`Seed.isLawful_replicatedWriting_of_isHeights`); the lemmas stated for `Scheme.heightSet` are to be
restated (`Scheme.LadderBaseData.min_v_eq_of_mem_heightSet`,
`Seed.replicatedWriting_castAdd_mem_heightSet`, `TieInstance.tieValue_mem_heightSet`).
**The natural strip (block `0`): settled, no block sets needed there.**  A cut in the block `0`
at a grade `k`, self-visible and short at `k`, is the natural cut `ω * 0 + k`; a code at it is an
orbit key, and the orbit decoder reads every label of its strip below it literally, lower-layer
heights `ω * 0 + j` included (`Label.natural_cut_no_jump`, `Label.orbitDecoder_of_natural`,
`Label.min_orbitDecoder_eq_of_natural`).  So the invariant to ask is strip freedom off the natural
strip (`Scheme.IsStripFreeOffNatural`, implied by `Scheme.IsStripFree`), which the current heights
still fail in every block `b ≥ 1` (`Scheme.not_isStripFreeOffNatural_heightSet`).  In the proposal
the block `0` keeps its heights as now: `G j` also contains `ω * 0 + j` and the finite values of
`Γ` self-visible at `j`, so (N2) and (N3) hold for a finite cut `f` (a height of every layer
`j ≤ f`).

## References

Lawful sections are [Kni26, Definition 2.5.4]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Label

/-- **A code at the cut makes the orbit decoder jump on the strip of the cut**: if a cell `e` has
its orbit code at the cut `h` (self-visible at `k`), the key of `W e` is not an orbit key, and
`h ≤ W e`, then every label `x` of the strip of `h` (`visibilityReplace k k x = h`) is read by
`orbitDecoder k W h` at least at `h`, through the reading `visibilityReplace k k (W e)` of `e`.
So a lift `orbitDecoder k W h ∘ w` agrees with a row capped at `h` at a cell whose row value is
such an `x < h` only if that value is a code value read literally. -/
theorem le_orbitDecoder_of_code_at_cut {k : ℕ} {ι : Type*} [Fintype ι] {W : ι → Label.{u}}
    {h x : Label.{u}} (hh : IsSelfVisible k h) {e : ι} (he : orbitCode k W e = h)
    (hno : ¬ IsOrbitKey k W (W e)) (hWe : h ≤ W e) (hxh : visibilityReplace k k x = h) :
    h ≤ orbitDecoder k W h x := by
  classical
  unfold orbitDecoder
  refine le_max_of_le_right ?_
  have hmem : e ∈ ({d | h ≤ visibilityReplace k k (orbitCode k W d)} : Finset ι) := by
    rw [Finset.mem_filter, he]
    exact ⟨Finset.mem_univ _, hh.symm.le⟩
  refine le_trans ?_ (Finset.le_sup (f := fun d ↦ cellReading k W d x) hmem)
  have hkey : visibilityReplace k k x = visibilityReplace k k (orbitCode k W e) := by
    rw [he, hxh]; exact hh.symm
  unfold cellReading
  rw [ite_eq_right (not_lt.mpr hkey.ge), ite_eq_right (fun hc ↦ hno hc.2)]
  calc h = visibilityReplace k k h := hh.symm
    _ ≤ visibilityReplace k k (W e) := monotone_visibilityReplace le_rfl hWe

/-- A grid point of a lower grade lies on the strip of the grid point of the same block. -/
theorem visibilityReplace_gridPoint_of_lt {j k : ℕ} (hj : j < k) (b : ℕ) :
    visibilityReplace k k (gridPoint.{u} j b) = gridPoint k b := by
  rw [gridPoint, visibilityReplace_block, ite_eq_left hj, gridPoint]

/-- **The strip jump at a lower-layer height** (the failing step at a grade `k ≥ 3`): for grades
`j < k` and a block `b ≤ B'`, the grid point `ω * b + j` is a height of the layer `j`
(`Scheme.heightSet Γ B' j`, for every `Γ`), lies on the strip of the cut `ω * b + k` strictly
below it, and, when a cell `e` has its orbit code at that cut (its value at least the cut, its key
not an orbit key), `orbitDecoder k W (ω * b + k)` reads it at least at the cut
(`le_orbitDecoder_of_code_at_cut`): its reading capped at the cut differs from the height itself
capped at the cut.  At the grade `2` no layer lies below, so no lower-layer height meets the
strip. -/
theorem lowerHeight_strip_jump {j k b B' : ℕ} (hj : j < k) (hb : b ≤ B') (Γ : Finset Label.{u})
    {ι : Type*} [Fintype ι] {W : ι → Label.{u}} {e : ι} (he : orbitCode k W e = gridPoint k b)
    (hno : ¬ IsOrbitKey k W (W e)) (hWe : gridPoint k b ≤ W e) :
    gridPoint j b ∈ Scheme.heightSet Γ B' j ∧
      visibilityReplace k k (gridPoint.{u} j b) = gridPoint k b ∧
      gridPoint.{u} j b < gridPoint k b ∧
      gridPoint k b ≤ orbitDecoder k W (gridPoint k b) (gridPoint j b) ∧
      min (orbitDecoder k W (gridPoint k b) (gridPoint j b)) (gridPoint k b) ≠
        min (gridPoint j b) (gridPoint k b) := by
  have hlt : gridPoint.{u} j b < gridPoint k b :=
    gridPoint_lt_gridPoint_iff_lex.mpr (.inr ⟨rfl, hj⟩)
  have hjump := le_orbitDecoder_of_code_at_cut (isSelfVisible_gridPoint k b) he hno hWe
    (visibilityReplace_gridPoint_of_lt hj b)
  refine ⟨Scheme.mem_heightSet.mpr (.inl (gridPoint_mem_grid hb)),
    visibilityReplace_gridPoint_of_lt hj b, hlt, hjump, ?_⟩
  rw [min_eq_right hjump, min_eq_left hlt.le]
  exact hlt.ne'

/-- **The hypotheses of the strip jump are met**: on one cell with the value `ω * 2 + k`, the
orbit code is the cut `ω + k` (the value is self-visible, so its key is a key and not an orbit
key, of key rank `1` and code block `1`), and the value is above the cut.  So at the grade `3`
the layer-`2` height `ω + 2` is read by `orbitDecoder 3 W (ω + 3)` at least at `ω + 3`. -/
theorem exists_strip_jump (k : ℕ) :
    ∃ W : Fin 1 → Label.{u}, orbitCode k W 0 = gridPoint k 1 ∧ ¬ IsOrbitKey k W (W 0) ∧
      gridPoint k 1 ≤ W 0 := by
  classical
  refine ⟨fun _ ↦ gridPoint k 2, ?_, ?_, gridPoint_le_gridPoint.mpr (by omega)⟩
  · have hno : ¬ IsOrbitKey k (fun _ : Fin 1 ↦ gridPoint.{u} k 2) (gridPoint k 2) :=
      fun ⟨_, _, hs⟩ ↦ hs (isSelfVisible_gridPoint k 2)
    have hkey : IsKey k (fun _ : Fin 1 ↦ gridPoint.{u} k 2) (gridPoint k 2) :=
      isKey_apply_iff (d := 0).mpr (gridPoint_ne_bot k 2)
    have hr : keyRank k (fun _ : Fin 1 ↦ gridPoint.{u} k 2) (gridPoint k 2) = 1 :=
      le_antisymm ((keyRank_le_card _ _ _).trans (by simp)) (one_le_keyRank hkey)
    rw [orbitCode_apply, orbitMap_of_not_isOrbitKey (gridPoint_ne_bot k 2) hno, codeBlock,
      ite_eq_right (fun h ↦ hno h.1), hr, ite_eq_left ⟨hkey, hno⟩]
  · exact fun ⟨_, _, hs⟩ ↦ hs (isSelfVisible_gridPoint k 2)

end Label

namespace Scheme

/-- **Strip freedom of heights** (the invariant asked at a grade `k ≥ 3`, stated here): for grades
`2 ≤ j < k ≤ M`, no height of the layer `j` lies on the strip of a cut of the grade `k` (a height
of the layer `k` that is a value of `Γ`) strictly below the cut. -/
def IsStripFree (G : ℕ → Finset Label.{u}) (Γ : Finset Label.{u}) (M : ℕ) : Prop :=
  ∀ j k, 2 ≤ j → j < k → k ≤ M → ∀ x ∈ G j, ∀ c ∈ G k, c ∈ Γ →
    ¬ (visibilityReplace k k x = c ∧ x < c)

/-- **The current heights are not strip free**: a cut `ω * b + k` of `Γ`, `k ≥ 3`, `b ≤ B'`, has
the grid height `ω * b + 2` of the layer `2` on its strip below it. -/
theorem not_isStripFree_heightSet {Γ : Finset Label.{u}} {B' k b M : ℕ} (hk : 3 ≤ k)
    (hkM : k ≤ M) (hb : b ≤ B') (hc : gridPoint k b ∈ Γ) :
    ¬ IsStripFree (fun j ↦ heightSet Γ B' j) Γ M := fun h ↦
  h 2 k le_rfl (by omega) hkM (gridPoint 2 b) (mem_heightSet.mpr (.inl (gridPoint_mem_grid hb)))
    (gridPoint k b) (mem_heightSet.mpr (.inr ⟨hc, isSelfVisible_gridPoint k b⟩)) hc
    ⟨Label.visibilityReplace_gridPoint_of_lt (by omega) b,
      gridPoint_lt_gridPoint_iff_lex.mpr (.inr ⟨rfl, by omega⟩)⟩

/-- **With the code grid as values the heights are not strip free** above the grade `2`: for
`m ≥ 2` the cut `ω * b + 3` of `codeGrid (m + 1) B` has `ω * b + 2` on its strip. -/
theorem not_isStripFree_codeGrid {m B B' b : ℕ} (hm : 2 ≤ m) (hb : b ≤ B) (hbB' : b ≤ B') :
    ¬ IsStripFree (fun j ↦ heightSet (codeGrid.{u} (m + 1) B) B' j) (codeGrid (m + 1) B)
      (m + 1) :=
  not_isStripFree_heightSet (k := 3) le_rfl (by omega) hbB'
    (Label.mem_codeGrid.mpr (.inr ⟨b, hb, 3, by omega, rfl⟩))

end Scheme


namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m}
  {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-- **The admission reads the truncation at the threshold only**: states agreeing at the cells of
grade at most the threshold are admitted together, at every grade. -/
theorem attachAdmits_congr
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} {K : ℕ} {R R' : Fin (I.attachment g).card → Label.{u}}
    (he : ∀ a, (I.attachment g).toCellScheme.grade a ≤ Q.threshold → R' a = R a)
    (hR : I.attachAdmits g hd Q K R) : I.attachAdmits g hd Q K R' := by
  have hhat (a : Fin (I.attachment g).card) :
      I.attachHatAt g Q.threshold R' a = I.attachHatAt g Q.threshold R a := by
    unfold attachHatAt
    split_ifs with h
    · exact he a h
    · rfl
  intro hk
  have := hR hk
  simp only [hhat]
  exact this

/-- **The state step at the grade `k`**.  Inputs: an anchor `R₀`, a lawful state of the attachment;
a cut `h` self-visible at `k`; a context prescription `w`, lawful below `(univ, k)` on the first
coatom type and agreeing with the anchor capped at `h` at the context cells of grade at most `k`;
and, from the threshold on, the admission of the anchor's truncation at `k` (`hamb`).  Output: a
state `W` of the attachment with four properties:
(a) `W` is `w` at the context cells of grade at most `k`;
(b) `W` is lawful below `(univ, k)`;
(c) `W` is admitted at `k` (`Seed.attachAdmits`, vacuous below the threshold);
(d) `W` agrees with `R₀` capped at `h` at every cell.
**Status of `hamb`**: vacuous below the threshold; at `k = threshold` it is derived from the
anchor's admission (`Seed.exists_stateStep_threshold`, unconditional there); for `k > threshold`
this theorem is CONDITIONAL on `hamb` for a general anchor, and `hamb` is derived only for an
anchor in the catalogue (`Seed.exists_stateStep_of_mem_towerCat`). -/
theorem exists_stateStep (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    {k : ℕ} (hk : 1 ≤ k) {R₀ : Fin (I.attachment g).card → Label.{u}}
    (hR₀ : (I.attachment g).rows.IsLawful R₀) {h : Label.{u}} (hh : IsSelfVisible k h)
    {w : Fin I.left.card → Label.{u}}
    (hw : I.left.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), k) fun x ↦ w x)
    (hwR : ∀ x, I.left.toCellScheme.grade x ≤ k →
      min (w x) h = min (R₀ (I.attachCtxCell g x)) h)
    (hamb : Q.threshold ≤ k → h ≠ ⊥ →
      Q.AdmitsOnClass
        (fun x ↦ if I.left.toCellScheme.grade x ≤ k then R₀ (I.attachCtxCell g x) else ⊥)
        fun y ↦ if d.toCellScheme.grade y ≤ k then R₀ (I.attachDonCell g hd y) else ⊥) :
    ∃ W : Fin (I.attachment g).card → Label.{u},
      (∀ x, I.left.toCellScheme.grade x ≤ k → W (I.attachCtxCell g x) = w x) ∧
      (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k) (fun a ↦ W a) ∧
      I.attachAdmits g hd Q k W ∧
      ∀ a, min (W a) h = min (R₀ a) h := by
  classical
  have h₁ := I.restrictFace_left_attachmentType g
  have h₂ := I.restrictFace_donor_attachmentType g hd
  set u' : Fin I.left.card → Label.{u} :=
    fun x ↦ if I.left.toCellScheme.grade x ≤ k then w x else ⊥ with hu'def
  set u : Fin I.left.card → Label.{u} :=
    fun x ↦ if I.left.toCellScheme.grade x ≤ k then R₀ (I.attachCtxCell g x) else ⊥ with hudef
  set v : Fin d.card → Label.{u} :=
    fun y ↦ if d.toCellScheme.grade y ≤ k then R₀ (I.attachDonCell g hd y) else ⊥ with hvdef
  have hu' : I.left.rows.IsLawful u' := Scheme.isLawful_truncate hw
  have hctx : I.left.rows.IsLawful fun x ↦ R₀ (I.attachCtxCell g x) :=
    isLawful_comp_faceCell h₁ hR₀
  have hdon : d.rows.IsLawful fun y ↦ R₀ (I.attachDonCell g hd y) :=
    isLawful_comp_faceCell h₂ hR₀
  have hu : I.left.rows.IsLawful u := Scheme.isLawful_truncate (hctx.isLawfulBelow _)
  have hv : d.rows.IsLawful v := Scheme.isLawful_truncate (hdon.isLawfulBelow _)
  have hgr₁ (i : Fin p₀.card) :
      I.left.toCellScheme.grade (I.left.faceCell hte i) = p₀.toCellScheme.grade i :=
    Scheme.grade_faceCell (comap_toScheme_of_restrictFace hte) i
  have hgr₂ (i : Fin p₀.card) :
      d.toCellScheme.grade (d.faceCell hdp i) = p₀.toCellScheme.grade i :=
    Scheme.grade_faceCell (comap_toScheme_of_restrictFace hdp) i
  obtain ⟨w', hw', hw'r, hw'c, hadm⟩ := StageType.exists_donorStep hte hdp hdL hn hpair hrel hk hh
    hu' hu hv
    (fun i ↦ by
      change (if d.toCellScheme.grade (d.faceCell hdp i) ≤ k then
          R₀ ((I.attachmentType g).faceCell h₂ (d.faceCell hdp i)) else ⊥) =
        (if I.left.toCellScheme.grade (I.left.faceCell hte i) ≤ k then
          R₀ ((I.attachmentType g).faceCell h₁ (I.left.faceCell hte i)) else ⊥)
      rw [hgr₁, hgr₂, StageType.faceCell_faceCell h₁ h₂ hte hdp i])
    (fun x hx ↦ by
      change min (if I.left.toCellScheme.grade x ≤ k then w x else ⊥) h =
        min (if I.left.toCellScheme.grade x ≤ k then R₀ (I.attachCtxCell g x) else ⊥) h
      rw [ite_eq_left hx, ite_eq_left hx]
      exact hwR x hx)
    (fun x hx ↦ ite_eq_right (not_le.mpr hx)) (fun x hx ↦ ite_eq_right (not_le.mpr hx))
    (fun hN h0 ↦ hamb hN h0)
  obtain ⟨R, hR, hR₁, hR₂⟩ := StageType.exists_joint_extension h₁ h₂ hte hdp
    (I.attachment_cover g) hu' hw' hw'r
  have hRc (x : Fin I.left.card) : R (I.attachCtxCell g x) = u' x := hR₁ x
  have hRd (y : Fin d.card) : R (I.attachDonCell g hd y) = w' y := hR₂ y
  set W : Fin (I.attachment g).card → Label.{u} :=
    fun a ↦ if (I.attachment g).toCellScheme.grade a ≤ k then R a else R₀ a with hWdef
  have hRA : ∀ K, I.attachAdmits g hd Q K R := fun K ↦
    attachAdmits_of_admitsOnClass hd hQ K (by
      rw [show (fun x ↦ R (I.attachCtxCell g x)) = u' from funext hRc,
        show (fun y ↦ R (I.attachDonCell g hd y)) = w' from funext hRd]
      exact hadm)
  refine ⟨W, fun x hx ↦ ?_, ?_, ?_, fun a ↦ ?_⟩
  · -- (a) literal on the context below the grade
    have hgx : (I.attachment g).toCellScheme.grade (I.attachCtxCell g x) ≤ k :=
      (grade_attachCtxCell x).trans_le hx
    change (if _ then R _ else R₀ _) = _
    rw [ite_eq_left hgx, hRc]
    exact ite_eq_left hx
  · -- (b) lawful below the grade
    have e : (fun a : (I.attachment g).toCellScheme.below ((univ : Finset (Fin (m + 2))), k) ↦
        W a) =
        fun a : (I.attachment g).toCellScheme.below ((univ : Finset (Fin (m + 2))), k) ↦ R a.1 := by
      funext a
      exact ite_eq_left (a.2.2 : (I.attachment g).toCellScheme.grade a ≤ k)
    rw [e]
    exact hR.isLawfulBelow _
  · -- (c) admitted at `k`: the admission reads the truncation at the threshold
    by_cases hN : Q.threshold ≤ k
    · exact attachAdmits_congr hd (fun a ha ↦ ite_eq_left (ha.trans hN)) (hRA k)
    · exact fun hk' ↦ absurd hk' hN
  · -- (d) capped agreement with the anchor
    by_cases hak : (I.attachment g).toCellScheme.grade a ≤ k
    · change min (if _ then R a else R₀ a) h = _
      rw [ite_eq_left hak]
      rcases I.attachment_cover g a with hvis | hvis
      · obtain ⟨x, rfl⟩ := StageType.exists_faceCell_eq h₁ hvis
        have hx : I.left.toCellScheme.grade x ≤ k := (grade_attachCtxCell x).symm.trans_le hak
        change min (R (I.attachCtxCell g x)) h = min (R₀ (I.attachCtxCell g x)) h
        rw [hRc]
        change min (if _ then w x else ⊥) h = _
        rw [ite_eq_left hx]
        exact hwR x hx
      · obtain ⟨y, rfl⟩ := StageType.exists_faceCell_eq h₂ hvis
        have hy : d.toCellScheme.grade y ≤ k :=
          (Scheme.grade_faceCell (comap_toScheme_of_restrictFace h₂) y).symm.trans_le hak
        change min (R (I.attachDonCell g hd y)) h = min (R₀ (I.attachDonCell g hd y)) h
        rw [hRd, hw'c y hy]
        change min (if _ then R₀ _ else ⊥) h = _
        rw [ite_eq_left hy]
    · change min (if _ then R a else R₀ a) h = _
      rw [ite_eq_right hak]

/-- **The state step at the threshold** (unconditional at `k = threshold`): at the grade `k` of the
threshold the admission of the anchor's truncation at `k` is the admission of the anchor, so the
premise `hamb` of `Seed.exists_stateStep` holds. -/
theorem exists_stateStep_threshold
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    {k : ℕ} (hkQ : Q.threshold = k) (hk : 1 ≤ k) {R₀ : Fin (I.attachment g).card → Label.{u}}
    (hR₀ : (I.attachment g).rows.IsLawful R₀) (hR₀A : I.attachAdmits g hd Q k R₀)
    {h : Label.{u}} (hh : IsSelfVisible k h) {w : Fin I.left.card → Label.{u}}
    (hw : I.left.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), k) fun x ↦ w x)
    (hwR : ∀ x, I.left.toCellScheme.grade x ≤ k →
      min (w x) h = min (R₀ (I.attachCtxCell g x)) h) :
    ∃ W : Fin (I.attachment g).card → Label.{u},
      (∀ x, I.left.toCellScheme.grade x ≤ k → W (I.attachCtxCell g x) = w x) ∧
      (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k) (fun a ↦ W a) ∧
      I.attachAdmits g hd Q k W ∧
      ∀ a, min (W a) h = min (R₀ a) h := by
  refine exists_stateStep hte hdp hdL hn hd hQ hpair hrel hk hR₀ hh hw hwR fun hN _ ↦ ?_
  have hA := hR₀A hN
  subst hkQ
  have e1 : (fun x ↦ I.attachHatAt g Q.threshold R₀ (I.attachCtxCell g x)) =
      fun x ↦ if I.left.toCellScheme.grade x ≤ Q.threshold then R₀ (I.attachCtxCell g x)
        else ⊥ := by
    funext x; unfold attachHatAt; rw [grade_attachCtxCell]
  have e2 : (fun y ↦ I.attachHatAt g Q.threshold R₀ (I.attachDonCell g hd y)) =
      fun y ↦ if d.toCellScheme.grade y ≤ Q.threshold then R₀ (I.attachDonCell g hd y)
        else ⊥ := by
    funext y; unfold attachHatAt
    rw [show (I.attachment g).toCellScheme.grade (I.attachDonCell g hd y) =
      d.toCellScheme.grade y from Scheme.grade_faceCell (I.comap_donor_attachment_scheme g hd) y]
  rw [← e1, ← e2]
  exact hA

/-- **The state step at every grade for an anchor of the catalogue**: when the anchor is a state
of the catalogue of the replicated scheme (its writing a lawful section,
`Seed.isLawful_replicatedWriting`),
the admission of its truncation at `k` is that of the ambient state of its writing
(`Seed.ambientAdmitted`: the controller above the cap cell carries the reads), so the premise
`hamb` of `Seed.exists_stateStep` holds at every grade.  Above the threshold this is the only
derivation of `hamb`: for an anchor outside the catalogue the state step above the threshold stays
conditional on `hamb`. -/
theorem exists_stateStep_of_mem_towerCat {H : ℕ} {Γ : Finset Label.{u}} {B' : ℕ}
    (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H) (hΓ0 : ⊥ ∈ Γ)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    {k : ℕ} (hk : 1 ≤ k) {R₀ : Fin (I.attachment g).card → Label.{u}}
    (hR₀ : R₀ ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hd Q) (m + 2))
    {h : Label.{u}} (hh : IsSelfVisible k h) {w : Fin I.left.card → Label.{u}}
    (hw : I.left.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), k) fun x ↦ w x)
    (hwR : ∀ x, I.left.toCellScheme.grade x ≤ k →
      min (w x) h = min (R₀ (I.attachCtxCell g x)) h) :
    ∃ W : Fin (I.attachment g).card → Label.{u},
      (∀ x, I.left.toCellScheme.grade x ≤ k → W (I.attachCtxCell g x) = w x) ∧
      (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k) (fun a ↦ W a) ∧
      I.attachAdmits g hd Q k W ∧
      ∀ a, min (W a) h = min (R₀ a) h := by
  have hR₀l : (I.attachment g).rows.IsLawful R₀ := (Scheme.LadderBaseData.mem_towerCat.mp hR₀).2.1
  refine exists_stateStep hte hdp hdL hn hd hQ hpair hrel hk hR₀l hh hw hwR fun hN _ ↦ ?_
  set q : (I.replicated g H Γ (I.attachAdmits g hd Q) B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), k) → Label.{u} :=
    fun z ↦ I.replicatedWriting g H Γ (I.attachAdmits g hd Q) B' R₀ z with hq
  have hql : (I.replicated g H Γ (I.attachAdmits g hd Q) B').rows.IsLawfulBelow
      ((univ : Finset (Fin (m + 2))), k) q :=
    (isLawful_replicatedWriting hH hcard hΓ (fun k R h ↦ I.attachAdmits_succ g hd Q k R h)
      hR₀).isLawfulBelow _
  have hamb := ambientAdmitted (B' := B') hH hcard hΓ0 hd hQ hn k hN q hql
  have hst (a : Fin (I.attachment g).card) :
      ambientState H Γ (I.attachAdmits g hd Q) B' q a =
        if (I.attachment g).toCellScheme.grade a ≤ k then R₀ a else ⊥ := by
    by_cases ha : (I.attachment g).toCellScheme.grade a ≤ k
    · simp only [ambientState, ha, dite_true, ite_true]
      exact replicatedWriting_attachEmb hcard hR₀l a
    · simp only [ambientState, ha, dite_false, ite_false]
  have e1 : (fun x ↦ ambientState H Γ (I.attachAdmits g hd Q) B' q (I.attachCtxCell g x)) =
      fun x ↦ if I.left.toCellScheme.grade x ≤ k then R₀ (I.attachCtxCell g x) else ⊥ := by
    funext x; rw [hst, grade_attachCtxCell]
  have e2 : (fun y ↦ ambientState H Γ (I.attachAdmits g hd Q) B' q (I.attachDonCell g hd y)) =
      fun y ↦ if d.toCellScheme.grade y ≤ k then R₀ (I.attachDonCell g hd y) else ⊥ := by
    funext y
    rw [hst, show (I.attachment g).toCellScheme.grade (I.attachDonCell g hd y) =
      d.toCellScheme.grade y from Scheme.grade_faceCell (I.comap_donor_attachment_scheme g hd) y]
  rw [← e1, ← e2]
  exact hamb

end Seed

namespace TieInstance

/-- The root of the input. -/
local notation "𝕣" => Function.Embedding.refl (Fin 1)

/-- The state step at the input, for the first coatom type given up to equality. -/
theorem exists_stateStep_two_aux {α : Ordinal.{u}} {I : Seed.{u} α 1} {t' : StageType.{u} α 2}
    (hI : I.left = t') {p : StageType.{u} α 1}
    {hte : restrictFace ((𝕣).trans Fin.castSuccEmb) t' = some p} {d : StageType.{u} α 2}
    (hdp : restrictFace Fin.castSuccEmb d = some p) (hdL : d.IsLegal)
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests t' d.toScheme} (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hdp) (hth : Q.threshold = 2)
    {R₀ : Fin (I.attachment 𝕣).card → Label.{u}} (hR₀ : (I.attachment 𝕣).rows.IsLawful R₀)
    (hR₀A : I.attachAdmits 𝕣 hdA (hI ▸ Q) 2 R₀) {h : Label.{u}} (hh : IsSelfVisible 2 h)
    {w : Fin I.left.card → Label.{u}}
    (hw : I.left.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 2) fun x ↦ w x)
    (hwR : ∀ x, I.left.toCellScheme.grade x ≤ 2 →
      min (w x) h = min (R₀ (I.attachCtxCell 𝕣 x)) h) :
    ∃ W : Fin (I.attachment 𝕣).card → Label.{u},
      (∀ x, I.left.toCellScheme.grade x ≤ 2 → W (I.attachCtxCell 𝕣 x) = w x) ∧
      (I.attachment 𝕣).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun a ↦ W a) ∧
      I.attachAdmits 𝕣 hdA (hI ▸ Q) 2 W ∧
      ∀ a, min (W a) h = min (R₀ a) h := by
  subst hI
  exact Seed.exists_stateStep_threshold hte hdp hdL Nat.one_pos hdA hQ hpair hrel hth
    (by omega) hR₀ hR₀A hh hw hwR

/-- **The state step at the top grade `2` of the tie input**: every lawful anchor admitted at `2`
and every context prescription lawful below `(univ, 2)` agreeing with it capped at a cut `h`
self-visible at `2` give a state of the attachment literal on the context, lawful below
`(univ, 2)`, admitted at `2`, and agreeing with the anchor capped at `h`.  The threshold of the
requests is `2`, so the premise on the anchor's truncation holds. -/
theorem exists_stateStep_two (I : Seed.{u} ω 1) (hI : I.left = ctx ω)
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some (don ω))
    {R₀ : Fin (I.attachment 𝕣).card → Label.{u}} (hR₀ : (I.attachment 𝕣).rows.IsLawful R₀)
    (hR₀A : I.attachAdmits 𝕣 hdA (hI ▸ req ω) 2 R₀) {h : Label.{u}} (hh : IsSelfVisible 2 h)
    {w : Fin I.left.card → Label.{u}}
    (hw : I.left.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 2) fun x ↦ w x)
    (hwR : ∀ x, I.left.toCellScheme.grade x ≤ 2 →
      min (w x) h = min (R₀ (I.attachCtxCell 𝕣 x)) h) :
    ∃ W : Fin (I.attachment 𝕣).card → Label.{u},
      (∀ x, I.left.toCellScheme.grade x ≤ 2 → W (I.attachCtxCell 𝕣 x) = w x) ∧
      (I.attachment 𝕣).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun a ↦ W a) ∧
      I.attachAdmits 𝕣 hdA (hI ▸ req ω) 2 W ∧
      ∀ a, min (W a) h = min (R₀ a) h :=
  exists_stateStep_two_aux hI (hte := restrictFace_ctx_root ω) (don_mem_cofaces ω).2
    (don_mem_cofaces ω).1 hdA (correctAt_req ω) (classCalibrated_req ω)
    (hasRelativeLiftOnClass_req ω) (threshold_req ω) hR₀ hR₀A hh hw hwR

end TieInstance

namespace ApexInstance

open AvailableTopDeterminationCounterexample

/-- The root of the input. -/
local notation "𝕘" => (Fin.castSuccEmb : Fin 1 ↪ Fin 2)

/-- The state step at the input, for the first coatom type given up to equality: at the grade `2`
from the threshold `2`, and at every grade from an anchor in the catalogue. -/
theorem exists_stateStep_aux {α : Ordinal.{u}} {I : Seed.{u} α 2} {t' : StageType.{u} α 3}
    (hI : I.left = t') {p : StageType.{u} α 1}
    {hte : restrictFace ((𝕘).trans Fin.castSuccEmb) t' = some p} {d : StageType.{u} α 2}
    (hdp : restrictFace Fin.castSuccEmb d = some p) (hdL : d.IsLegal)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests t' d.toScheme} (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hdp) {k : ℕ}
    (hk : 1 ≤ k) {R₀ : Fin (I.attachment 𝕘).card → Label.{u}}
    (hR₀ : (I.attachment 𝕘).rows.IsLawful R₀) {h : Label.{u}} (hh : IsSelfVisible k h)
    {w : Fin I.left.card → Label.{u}}
    (hw : I.left.rows.IsLawfulBelow ((univ : Finset (Fin 3)), k) fun x ↦ w x)
    (hwR : ∀ x, I.left.toCellScheme.grade x ≤ k →
      min (w x) h = min (R₀ (I.attachCtxCell 𝕘 x)) h)
    (hadm : (Q.threshold = k ∧ I.attachAdmits 𝕘 hdA (hI ▸ Q) k R₀) ∨
      ∃ (H : ℕ) (Γ : Finset Label.{u}) (B' : ℕ), 0 < H ∧ (I.attachmentBase 𝕘).S.card ≤ H ∧
        ⊥ ∈ Γ ∧ (∀ x ∈ Γ, x ≤ gridPoint 2 B') ∧
        R₀ ∈ (I.attachmentBase 𝕘).towerCat Γ (I.attachAdmits 𝕘 hdA (hI ▸ Q)) 4) :
    ∃ W : Fin (I.attachment 𝕘).card → Label.{u},
      (∀ x, I.left.toCellScheme.grade x ≤ k → W (I.attachCtxCell 𝕘 x) = w x) ∧
      (I.attachment 𝕘).rows.IsLawfulBelow ((univ : Finset (Fin 4)), k) (fun a ↦ W a) ∧
      I.attachAdmits 𝕘 hdA (hI ▸ Q) k W ∧
      ∀ a, min (W a) h = min (R₀ a) h := by
  subst hI
  rcases hadm with ⟨hth, hR₀A⟩ | ⟨H, Γ, B', hH, hcard, hΓ0, hΓ, hR₀C⟩
  · exact Seed.exists_stateStep_threshold hte hdp hdL Nat.one_pos hdA hQ hpair hrel hth hk hR₀
      hR₀A hh hw hwR
  · exact Seed.exists_stateStep_of_mem_towerCat hH hcard hΓ0 hΓ hte hdp hdL Nat.one_pos hdA hQ
      hpair hrel hk hR₀C hh hw hwR

/-- **The state step at the grade `2` of the apex input, below its top grade `3`**: with the
bottom requests `req α` (threshold `2`) over the donor labelled `⊥`, every lawful anchor admitted
at `2` and every context prescription lawful below `(univ, 2)` agreeing with it capped at a cut
`h` self-visible at `2` give a state of the attachment literal on the context, lawful below
`(univ, 2)`, admitted at `2`, and agreeing with the anchor capped at `h`. -/
theorem exists_stateStep_two {α : Ordinal.{u}} (I : Seed.{u} α 2) (hI : I.left = topType α)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (bareDonor α))
    {R₀ : Fin (I.attachment 𝕘).card → Label.{u}} (hR₀ : (I.attachment 𝕘).rows.IsLawful R₀)
    (hR₀A : I.attachAdmits 𝕘 hdA (hI ▸ req α) 2 R₀) {h : Label.{u}} (hh : IsSelfVisible 2 h)
    {w : Fin I.left.card → Label.{u}}
    (hw : I.left.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) fun x ↦ w x)
    (hwR : ∀ x, I.left.toCellScheme.grade x ≤ 2 →
      min (w x) h = min (R₀ (I.attachCtxCell 𝕘 x)) h) :
    ∃ W : Fin (I.attachment 𝕘).card → Label.{u},
      (∀ x, I.left.toCellScheme.grade x ≤ 2 → W (I.attachCtxCell 𝕘 x) = w x) ∧
      (I.attachment 𝕘).rows.IsLawfulBelow ((univ : Finset (Fin 4)), 2) (fun a ↦ W a) ∧
      I.attachAdmits 𝕘 hdA (hI ▸ req α) 2 W ∧
      ∀ a, min (W a) h = min (R₀ a) h :=
  exists_stateStep_aux hI (hte := restrictFace_root) bareDonor_mem_cofaces.2
    bareDonor_mem_cofaces.1 hdA (correctAt_req α) (classCalibrated_req α)
    (hasRelativeLiftOnClass_req α) (by omega) hR₀ hh hw hwR (.inl ⟨threshold_req α, hR₀A⟩)

/-- **The state step at the top grade `3` of the apex input, above the threshold `2`**: for an
anchor in the catalogue (values `Γ` containing `⊥` and below the grid point at `2`, height bound
`H` at least the card of the attachment base), the admission of the anchor's truncation at `3` is
the ambient admission of its writing, and the state step holds at `3`. -/
theorem exists_stateStep_three {α : Ordinal.{u}} (I : Seed.{u} α 2) (hI : I.left = topType α)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (bareDonor α))
    {H : ℕ} {Γ : Finset Label.{u}} {B' : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') {R₀ : Fin (I.attachment 𝕘).card → Label.{u}}
    (hR₀ : R₀ ∈ (I.attachmentBase 𝕘).towerCat Γ (I.attachAdmits 𝕘 hdA (hI ▸ req α)) 4)
    {h : Label.{u}} (hh : IsSelfVisible 3 h) {w : Fin I.left.card → Label.{u}}
    (hw : I.left.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 3) fun x ↦ w x)
    (hwR : ∀ x, I.left.toCellScheme.grade x ≤ 3 →
      min (w x) h = min (R₀ (I.attachCtxCell 𝕘 x)) h) :
    ∃ W : Fin (I.attachment 𝕘).card → Label.{u},
      (∀ x, I.left.toCellScheme.grade x ≤ 3 → W (I.attachCtxCell 𝕘 x) = w x) ∧
      (I.attachment 𝕘).rows.IsLawfulBelow ((univ : Finset (Fin 4)), 3) (fun a ↦ W a) ∧
      I.attachAdmits 𝕘 hdA (hI ▸ req α) 3 W ∧
      ∀ a, min (W a) h = min (R₀ a) h :=
  exists_stateStep_aux hI (hte := restrictFace_root) bareDonor_mem_cofaces.2
    bareDonor_mem_cofaces.1 hdA (correctAt_req α) (classCalibrated_req α)
    (hasRelativeLiftOnClass_req α) (by omega)
    (Scheme.LadderBaseData.mem_towerCat.mp hR₀).2.1 hh hw hwR
    (.inr ⟨H, Γ, B', hH, hcard, hΓ0, hΓ, hR₀⟩)

end ApexInstance

end VaughtConjecture
