/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.TowerProfileCompletion
import VaughtConjecture.Extension.UpperDecoderAt

/-!
# Layers of rank-normalized profiles over the tower, at every arity

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade, here at every
arity `m ≥ 2`, `m = 3` included; the modules `VaughtConjecture.Extension.TowerProfileScheme` and
`VaughtConjecture.Extension.TowerProfileCompletion` are the first instance, at `m = 3`, kept as a
test, and the completion does not go through them, beyond the generic lemma
`Scheme.extendsFromBoundary_fieldLayer_of_fill` stated in the second).

Let `I` be a seed on `m + 2` points, with `N` cells in its amalgam.  A **profile** is a labelling of
the cells of the amalgam (`ProfileTower.Prof`).  The **rank-normalized catalogue at the grade `k`**
(`ProfileTower.cat I k`) is the finite set of profiles lawful below both coatoms at the grade `k`
and fixed by the orbit code at `k`.  A **level at the grade `g`** (`ProfileTower.Lvl`) is a scheme,
the old cells (the amalgam), and a **section operator** `σ`: a labelling of the scheme for each
profile.

**The levels** (`ProfileTower.lvl I j`, at the grade `j + 2`).  The base level is the tower `T 2`
with the tower section (`Seed.towerSection`).  The next level of a level `L` at the grade `g`
(`ProfileTower.Lvl.next`) appends one cell of full scope and grade `g + 1` for each profile of the
catalogue at `g + 1`; the row of the cell of a profile `R` (`ProfileTower.Lvl.Φ`) is the section
`σ R` at the cells of `L`, and at the cell of a profile `R'` the agreement height of `R` and `R'` in
the grid `Label.grid (g + 1) (2 N + 2)`, one grid per seed and grade.  The rows depend on the
profiles only: one scheme per seed, rows fixed before any prescription or cap.  The section operator
of the next level (`ProfileTower.Lvl.nextσ`) reads, at the cells of grade at most `g + 1`, the row
of the orbit code of the profile cut at `g + 1` through the upper decoder at the grade `g + 1` for
caps at `g + 2` (`Label.upperDecoderAt`: the larger of the orbit decoder and a gap value that reads
the gaps between codes upward, `VaughtConjecture.Extension.UpperDecoderAt`), and is the profile
itself at the old cells above.

**The invariant** (`ProfileTower.Lvl.Good`): the old cells form a lower embedding of the amalgam
with its rows and faces, every cell of proper scope old; the scheme is well formed, coded and
consistent and carries a cell at every `(univ, j)`, `0 < j ≤ g`; the section operator is lawful on
the profiles lawful on the grade-`g` cut, takes values in the code grid at `g + 1` for profiles
there, is literal at the old cells, agrees capped at every cap self-visible and short at `g + 1` for
profiles agreeing capped there, and is readable at `g + 1` for the orbit-canonical profiles; and the
scheme lifts capped from either coatom into the full face at every grade `j ≤ g`.

* **The base level is good** (`ProfileTower.base_good`, `m ≥ 1`): the tower section, and the lifts
  of `T 2` from `2FL(1)` (`Seed.towerInvariant_succ`, `Seed.twoFaceLift_one`).
* **The next level of a good level at the grade `g` is good, for `g + 1 ≤ m`**
  (`ProfileTower.Lvl.Good.next`).  The row of a profile of the catalogue is lawful below
  `(univ, g + 1)` (`ProfileTower.Lvl.Good.isLawfulBelow_Φ`).  The lift at the grade `g + 1` from
  either coatom (`ProfileTower.Lvl.Good.cappedLift_next`) is the one-grade lift
  `CellScheme.Rows.cappedLift_of_boundaries_short` with the boundary triples of the two coatoms and
  their common face on `m` points, the extension from the boundary at `⊥`
  (`ProfileTower.Lvl.Good.exists_extension_bot`) and at every cap self-visible and short at `g + 1`
  (`ProfileTower.Lvl.Good.exists_extension`: the row of the orbit code of the old labels, read by
  their orbit decoder at the cap, which reads the section literally because it is readable, and
  agrees with the row of the prescribed profile because the section agrees capped).  The section
  operator of the next level keeps the invariant at `g + 2`: lawful through the upper decoder, a
  witness (`ProfileTower.Lvl.Good.next_lawful`); capped agreement at the caps self-visible and short
  at `g + 2` (`ProfileTower.Lvl.Good.next_capAgree`, `Label.min_upperDecoderAt_comp_eq`); readable
  (`ProfileTower.Lvl.Good.next_readable`, `Label.isReadableAt_upperDecoderAt_of_mem`); in the code
  grid (`ProfileTower.Lvl.Good.next_mem`); literal (`ProfileTower.Lvl.Good.next_literal`).
* **Every level up to the grade `m` is good** (`ProfileTower.lvl_good`, `m ≥ 2`).

Compiled in this repository (theorem named), for every seed, with no hypothesis on the seed or the
stage.  The extension from the boundary depends on the prescription and the cap; the rows do not.
The top layer at the grade `m + 1` and the completion below the full grade are in
`VaughtConjecture.Extension.ProfileTowerCompletion`.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`, Layer 3,
3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- A **profile**: a labelling of the cells of the amalgam. -/
abbrev Prof : Type (u + 1) := Fin I.amalgam.card → Label.{u}

/-- The first coatom `C = univ.erase (m + 1)`. -/
abbrev coatC : Finset (Fin (m + 2)) := univ.erase (Fin.last (m + 1))

/-- The second coatom `D = univ.erase m`. -/
abbrev coatD : Finset (Fin (m + 2)) := univ.erase (Fin.castSucc (Fin.last m))

/-- The block bound `2 N + 2` of the grids, for `N` cells of the amalgam. -/
abbrev bound : ℕ := 2 * I.amalgam.card + 2

/-- A profile **lawful on the grade-`k` cut**: lawful below both coatoms at the grade `k`. -/
def IsCutLawful (k : ℕ) (P : Prof I) : Prop :=
  I.amalgam.rows.IsLawfulBelow (coatC, k) (fun d ↦ P d) ∧
    I.amalgam.rows.IsLawfulBelow (coatD, k) (fun d ↦ P d)

open Classical in
/-- The **rank-normalized catalogue at the grade `k`**: the profiles lawful on the grade-`k` cut and
fixed by the orbit code at `k`; their values lie in `codeGrid k (2 N)`. -/
noncomputable def cat (k : ℕ) : Finset (Prof I) :=
  (Fintype.piFinset fun _ ↦ codeGrid k (2 * I.amalgam.card)).filter
    fun P ↦ IsCutLawful I k P ∧ orbitCode k P = P

variable {I}

theorem mem_cat {k : ℕ} {P : Prof I} : P ∈ cat I k ↔ IsCutLawful I k P ∧ orbitCode k P = P := by
  classical
  simp only [cat, Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨fun d ↦ ?_, h⟩⟩
  rw [← congrFun h.2 d]
  exact orbitMap_mem_codeGrid (by simp) _

theorem mem_codeGrid_of_mem_cat {k : ℕ} {P : Prof I} (hP : P ∈ cat I k) (d : Fin I.amalgam.card) :
    P d ∈ codeGrid k (bound I) := by
  rw [← (mem_cat.mp hP).2]
  exact codeGrid_mono (B := 2 * I.amalgam.card) (by simp only [bound]; omega)
    (orbitMap_mem_codeGrid (by simp) _)

theorem bot_mem_cat (k : ℕ) : (fun _ ↦ ⊥ : Prof I) ∈ cat I k :=
  mem_cat.mpr ⟨⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩,
    funext fun _ ↦ orbitCode_eq_bot_iff.mpr rfl⟩

variable (I)

/-- The profile of the cell `i` of the layer at the grade `k`. -/
noncomputable def entry (k : ℕ) (i : Fin (cat I k).card) : Prof I := ((cat I k).equivFin.symm i).1

/-- The splice of a profile at the grade `k`: the profile up to the grade `k`, `⊥` above. -/
noncomputable def hat (k : ℕ) (P : Prof I) : Prof I :=
  I.amalgam.toCellScheme.splice k (fun _ ↦ ⊥) P

/-- **A level** of the construction at the grade `g`: a scheme, a section operator, and the old
cells, every cell of grade at most `g` or of scope other than the ground set. -/
structure Lvl (g : ℕ) where
  /-- The scheme. -/
  S : Scheme.{u} (m + 2) /-- The section operator. -/
  σ : Prof I → Fin S.card → Label.{u} /-- The old cells. -/
  embed : Fin I.amalgam.card ↪o Fin S.card /-- Every cell has grade at most `g` or scope other than
  the ground set. -/
  inv : ∀ d, S.toCellScheme.grade d ≤ g ∨ S.toCellScheme.scope d ≠ univ

variable {I}

/-- No cell of a level at the grade `g` lies above `(univ, g + 1)`. -/
theorem Lvl.not_le {g : ℕ} (L : Lvl I g) (d : Fin L.S.card) :
    ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ L.S.toCellScheme.gradedIndex d := fun hd ↦
  (L.inv d).elim (fun h ↦ absurd hd.2 (by simp only [CellScheme.gradedIndex_snd]; omega))
    fun h ↦ h (univ_subset_iff.mp hd.1)

/-- The row labelling of the layer at the grade `g + 1` over a level: the section of `R` at the
cells of the level, and the agreement heights of `R` with the profiles of the layer. -/
noncomputable def Lvl.Φ {g : ℕ} (L : Lvl I g) (R : Prof I) :
    Fin (L.S.card + (cat I (g + 1)).card) → Label.{u} :=
  Fin.append (L.σ R) fun i ↦ agreementHeight (grid (g + 1) (bound I)) R (entry I (g + 1) i)

/-- The scheme of the next level: the level followed by one cell at `(univ, g + 1)` per profile of
the catalogue at the grade `g + 1`, with the row labelling of its profile. -/
noncomputable abbrev Lvl.nextS {g : ℕ} (L : Lvl I g) : Scheme.{u} (m + 2) :=
  L.S.appendFullCells (g + 1) (cat I (g + 1)).card (fun i ↦ L.Φ (entry I (g + 1) i)) L.not_le

/-- The code of a profile at the grade `g + 1`: the orbit code of its splice. -/
noncomputable abbrev code (k : ℕ) (P : Prof I) : Prof I := orbitCode k (hat I k P)

/-- The section operator of the next level: at the cells of grade at most `g + 1`, the row labelling
of the code of the profile, read by the upper decoder of the splice; above, the section of the
level. -/
noncomputable def Lvl.nextσ {g : ℕ} (L : Lvl I g) (P : Prof I) :
    Fin (L.S.card + (cat I (g + 1)).card) → Label.{u} := fun z ↦
  if (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).grade z ≤ g + 1 then
    upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) P) (L.Φ (code (g + 1) P) z)
  else Fin.append (L.σ P) (fun _ ↦ ⊥) z

/-- **The next level**, at the grade `g + 1`. -/
noncomputable def Lvl.next {g : ℕ} (L : Lvl I g) : Lvl I (g + 1) where
  S := L.nextS
  σ := L.nextσ
  embed := L.embed.trans (Fin.castAddOrderEmb _)
  inv d := by
    induction d using Fin.addCases with
    | left d =>
      rw [Scheme.appendFullCellsScheme_grade_castAdd, Scheme.appendFullCellsScheme_scope_castAdd]
      exact (L.inv d).imp_left fun h ↦ h.trans (Nat.le_succ g)
    | right i => exact .inl (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le

variable (I)

/-- **The base level**, at the grade `2`: the tower `T 2` with its section (`Seed.towerSection`). -/
noncomputable def base : Lvl I 2 where
  S := I.tower 2
  σ := I.towerSection (bound I) 2
  embed := I.towerEmbed 2
  inv := I.tower_grade_le_or 2

/-- **The levels**: the level at the grade `j + 2`. -/
noncomputable def lvl : (j : ℕ) → Lvl I (j + 2)
  | 0 => base I
  | j + 1 => (lvl j).next

/-! ### Good levels
-/

variable {I}

/-- The two points omitted by the coatoms. -/
abbrev Pts : Finset (Fin (m + 2)) := {Fin.last (m + 1), Fin.castSucc (Fin.last m)}

/-- **A good level** at the grade `g`: the old cells form a source of the amalgam, the scheme is
well formed, coded and consistent, the section operator is lawful, in the code grid at `g + 1`,
literal, agrees capped at every cap self-visible and short at `g + 1`, and is readable at `g + 1`
for the orbit-canonical profiles; and the scheme lifts capped from either coatom into the full face
at every grade `j ≤ g`. -/
structure Lvl.Good {g : ℕ} (L : Lvl I g) : Prop where
  lowerEmb : I.amalgam.toCellScheme.IsLowerEmbedding L.S.toCellScheme L.embed
  scope_embed : ∀ d, L.S.toCellScheme.scope (L.embed d) = I.amalgam.toCellScheme.scope d
  comap_rows : L.S.rows.comap lowerEmb = I.amalgam.rows
  mem_range : ∀ z, L.S.toCellScheme.scope z ≠ univ → z ∈ Set.range L.embed
  faces : L.S.toCellScheme.faces = I.amalgam.toCellScheme.faces
  wf : L.S.IsWellFormed
  coded : L.S.IsCoded
  consistent : L.S.rows.IsConsistent
  lawful : ∀ P, IsCutLawful I g P →
    L.S.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g) fun z ↦ L.σ P z
  mem : ∀ P : Prof I, (∀ d, P d ∈ codeGrid (g + 1) (bound I)) →
    ∀ z, L.σ P z ∈ codeGrid (g + 1) (bound I)
  literal : ∀ P d, L.σ P (L.embed d) = P d
  capAgree : ∀ P P' : Prof I, (∀ d, P d ∈ codeGrid (g + 1) (bound I)) → ∀ h : Label.{u},
    IsSelfVisible (g + 1) h → IsShort (g + 1) h → (∀ d, min (P d) h = min (P' d) h) →
    ∀ z, min (L.σ P z) h = min (L.σ P' z) h
  readable : ∀ Q : Prof I, orbitCode (g + 1) Q = Q → (∀ d, Q d ∈ codeGrid (g + 1) (bound I)) →
    ∀ z, IsReadableAt (g + 1) Q (L.σ Q z)
  lift : ∀ x ∈ (Pts : Finset (Fin (m + 2))), ∀ j ≤ g,
    L.S.rows.CappedLift (X := (univ.erase x, j)) (Y := ((univ : Finset (Fin (m + 2))), j))
      ⟨erase_subset _ _, le_rfl⟩
  complete : ∀ j, 0 < j → j ≤ g →
    ∃ z, L.S.toCellScheme.gradedIndex z = ((univ : Finset (Fin (m + 2))), j)

/-- **The base level is good**, for `m ≥ 1`. -/
theorem base_good (hm : 1 ≤ m) : (base I).Good where
  lowerEmb := I.isLowerEmbedding_tower 2
  scope_embed := I.scope_towerEmbed 2
  comap_rows := I.comap_rows_tower 2
  mem_range := I.mem_range_towerEmbed 2
  faces := I.faces_tower 2
  wf := I.isWellFormed_tower 2 (by omega)
  coded := I.isCoded_tower 2
  consistent := I.isConsistent_tower 2
  lawful P hP := Seed.isLawfulBelow_towerSection
    (I.scope_subset_or (x := Fin.last (m + 1)) (y := Fin.castSucc (Fin.last m)) (by simp)
      (by simp) Seed.last_ne_castSucc) 2 (by omega) hP.1 hP.2
  mem P hP z := Seed.towerSection_mem_codeGrid 2 (by omega) hP z
  literal P d := Seed.towerSection_towerEmbed 2 P d
  capAgree P P' hP h hh hs hag z := Seed.min_towerSection_eq hh hs 2 le_rfl hP hag z
  readable Q hQ hQB z := Seed.isReadable_towerSection hQ hQB 2 le_rfl z
  lift x hx j hj :=
    I.towerInvariant_succ (j := 1) hm I.towerInvariant_one I.twoFaceLift_one x hx j hj
  complete _ hj0 hj := I.exists_gradedIndex_eq_univ_tower_of_le hj0 2 hj

/-! ### Old cells of a good level
-/

section Step

variable {g : ℕ} {L : Lvl I g}

theorem entry_mem {k : ℕ} (i : Fin (cat I k).card) : entry I k i ∈ cat I k :=
  ((cat I k).equivFin.symm i).2

theorem exists_entry_eq {k : ℕ} {R : Prof I} (hR : R ∈ cat I k) : ∃ i, entry I k i = R :=
  ⟨(cat I k).equivFin ⟨R, hR⟩, by simp [entry]⟩

theorem Lvl.Good.gradedIndex_embed (hL : L.Good) (d : Fin I.amalgam.card) :
    L.S.toCellScheme.gradedIndex (L.embed d) = I.amalgam.toCellScheme.gradedIndex d :=
  Prod.ext (hL.scope_embed d) (hL.lowerEmb.grade_eq d)

/-- The amalgam is a source prefix of a good level at the pairs off the ground set. -/
theorem Lvl.Good.isSourcePrefix (hL : L.Good) {Y : Finset (Fin (m + 2)) × ℕ} (hY : Y.1 ≠ univ) :
    I.amalgam.toCellScheme.IsSourcePrefix L.S.toCellScheme L.embed Y :=
  ⟨hL.lowerEmb, hL.scope_embed, fun z hz ↦ hL.mem_range z fun he ↦
    hY (univ_subset_iff.mp (he ▸ (hz.1 : L.S.toCellScheme.scope z ⊆ Y.1)))⟩

theorem Lvl.Good.isLawfulBelow_old_iff (hL : L.Good) {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X.1 ≠ univ) {w : Fin L.S.card → Label.{u}} :
    L.S.rows.IsLawfulBelow X (fun z ↦ w z) ↔
      I.amalgam.rows.IsLawfulBelow X (fun d ↦ w (L.embed d)) := by
  have h := hL.isSourcePrefix hX
  rw [← h.isLawfulBelow_iff le_rfl, hL.comap_rows]
  rfl

theorem Lvl.Good.cappedLift_old (hL : L.Good) {X Y : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ I.amalgam.toCellScheme.gradedFaces) (hY : Y ∈ I.amalgam.toCellScheme.gradedFaces)
    (hY1 : Y.1 ≠ univ) (h : X ≤ Y) : L.S.rows.CappedLift h := by
  have hP := hL.isSourcePrefix hY1
  rw [← hP.cappedLift_iff h le_rfl, hL.comap_rows]
  exact I.isBountiful hX hY h

/-- A cell of a level of grade above `g` is old. -/
theorem Lvl.Good.mem_range_of_lt (hL : L.Good) {z : Fin L.S.card}
    (hz : g < L.S.toCellScheme.grade z) : z ∈ Set.range L.embed :=
  hL.mem_range z ((L.inv z).resolve_left (by omega))

/-- **The cover of `(univ, g + 1)`**: a cell of a good level below `(univ, g + 1)` lies below
`(univ, g)` or below one of the coatoms at the grade `g + 1`. -/
theorem Lvl.Good.mem_below_cover (hL : L.Good) {x y : Fin (m + 2)} (hx : x ∈ (Pts : Finset _))
    (hy : y ∈ (Pts : Finset _)) (hxy : x ≠ y) (z : Fin L.S.card)
    (hz : z ∈ L.S.toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
    z ∈ L.S.toCellScheme.below (univ.erase x, g + 1) ∨
      z ∈ L.S.toCellScheme.below (univ, g) ∨ z ∈ L.S.toCellScheme.below (univ.erase y, g + 1) := by
  by_cases hzg : L.S.toCellScheme.grade z ≤ g
  · exact .inr (.inl ⟨subset_univ _, hzg⟩)
  obtain ⟨d, rfl⟩ := hL.mem_range_of_lt (_root_.not_le.mp hzg)
  have hd : I.amalgam.toCellScheme.grade d ≤ g + 1 := by
    have := hz.2
    rwa [hL.gradedIndex_embed] at this
  rcases I.scope_subset_or hx hy hxy d with h | h
  · refine .inl ?_
    rw [CellScheme.mem_below, hL.gradedIndex_embed]; exact ⟨h, hd⟩
  · refine .inr (.inr ?_)
    rw [CellScheme.mem_below, hL.gradedIndex_embed]; exact ⟨h, hd⟩

/-! ### The row labellings of the next layer
-/

@[simp] theorem Lvl.Φ_castAdd (R : Prof I) (e : Fin L.S.card) :
    L.Φ R (Fin.castAdd _ e) = L.σ R e := Fin.append_left _ _ e

@[simp] theorem Lvl.Φ_natAdd (R : Prof I) (i : Fin (cat I (g + 1)).card) :
    L.Φ R (Fin.natAdd _ i) = agreementHeight (grid (g + 1) (bound I)) R (entry I (g + 1) i) :=
  Fin.append_right _ _ i

/-- A profile of the catalogue at `g + 1` has values in the code grid at `g + 1`. -/
theorem mem_codeGrid_of_mem_cat' {k : ℕ} {R : Prof I} (hR : R ∈ cat I k) :
    ∀ d, R d ∈ codeGrid k (bound I) := mem_codeGrid_of_mem_cat hR

theorem Lvl.Good.Φ_mem_codeGrid (hL : L.Good) {R : Prof I}
    (hR : ∀ d, R d ∈ codeGrid (g + 1) (bound I)) (z : Fin (L.S.card + (cat I (g + 1)).card)) :
    L.Φ R z ∈ codeGrid (g + 1) (bound I) := by
  induction z using Fin.addCases with
  | left e => rw [Lvl.Φ_castAdd]; exact hL.mem R hR e
  | right i =>
    rw [Lvl.Φ_natAdd]
    exact grid_subset_codeGrid _ _ (agreementHeight_spec (bot_mem_grid _ _) _ _).1

theorem agreementHeight_self_ceiling' (k : ℕ) (R : Prof I) :
    agreementHeight (grid k (bound I)) R R = gridPoint k (bound I) :=
  agreementHeight_self (gridPoint_mem_grid le_rfl) (fun _ hx ↦ le_gridPoint_of_mem_grid hx) R

/-- Lawfulness below a pair not above `(univ, g + 1)` in the next scheme is lawfulness in the level.
-/
theorem Lvl.isLawfulBelow_nextS_iff {X : Finset (Fin (m + 2)) × ℕ}
    (hX : ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ X)
    {v : Fin (L.S.card + (cat I (g + 1)).card) → Label.{u}} :
    L.nextS.rows.IsLawfulBelow X (fun d ↦ v d) ↔
      L.S.rows.IsLawfulBelow X (fun d ↦ v (Fin.castAdd _ d)) :=
  Scheme.isLawfulBelow_appendFullCells_iff hX

/-- **The row labelling of a profile of the catalogue at `g + 1` is lawful below `(univ, g + 1)`**
in the next scheme. -/
theorem Lvl.Good.isLawfulBelow_Φ (hL : L.Good) {R : Prof I} (hR : R ∈ cat I (g + 1)) :
    L.nextS.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g + 1) fun z ↦ L.Φ R z := by
  classical
  obtain ⟨⟨hC, hD⟩, -⟩ := mem_cat.mp hR
  have hRB := mem_codeGrid_of_mem_cat hR
  have hlow : L.nextS.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g)
      fun z ↦ L.Φ R z := by
    refine (L.isLawfulBelow_nextS_iff (by rintro ⟨-, h⟩; simp only at h; omega)).mpr ?_
    simpa only [Lvl.Φ_castAdd] using hL.lawful R ⟨hC.mono (X := (_, g)) ⟨subset_rfl, by omega⟩,
      hD.mono (X := (_, g)) ⟨subset_rfl, by omega⟩⟩
  have hcoat (x : Fin (m + 2))
      (hRX : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1) fun d ↦ R d) :
      L.nextS.rows.IsLawfulBelow (univ.erase x, g + 1) fun z ↦ L.Φ R z := by
    refine (L.isLawfulBelow_nextS_iff fun h ↦ Seed.ne_univ_erase x
      (univ_subset_iff.mp h.1)).mpr ?_
    simp only [Lvl.Φ_castAdd]
    rw [hL.isLawfulBelow_old_iff (Seed.ne_univ_erase x)]
    exact (Rows.isLawfulBelow_congr (w' := fun d ↦ L.σ R (L.embed d))
      fun d _ ↦ (hL.literal R d).symm).mp hRX
  have hcC := hcoat _ hC
  have hcD := hcoat _ hD
  obtain ⟨ho2, hl2, ha2⟩ := Rows.isLawfulBelow_iff_forall.mp hlow
  obtain ⟨hoC, hlC, haC⟩ := Rows.isLawfulBelow_iff_forall.mp hcC
  obtain ⟨hoD, hlD, haD⟩ := Rows.isLawfulBelow_iff_forall.mp hcD
  have hcases {e : Fin L.S.card}
      (he : Fin.castAdd (cat I (g + 1)).card e ∈
        L.nextS.toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
      Fin.castAdd (cat I (g + 1)).card e ∈ L.nextS.toCellScheme.below (coatC, g + 1) ∨
        Fin.castAdd (cat I (g + 1)).card e ∈
          L.nextS.toCellScheme.below ((univ : Finset (Fin (m + 2))), g) ∨
        Fin.castAdd (cat I (g + 1)).card e ∈ L.nextS.toCellScheme.below (coatD, g + 1) := by
    have he' : e ∈ L.S.toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) := by
      have := he
      rwa [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd] at this
    simp only [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
    exact hL.mem_below_cover (by simp) (by simp) Seed.last_ne_castSucc e he'
  obtain ⟨i₀, hi₀⟩ := exists_entry_eq hR
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun z hz ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · induction z using Fin.addCases with
    | left e =>
      rcases hcases hz with h | h | h
      exacts [hoC _ h, ho2 _ h, hoD _ h]
    | right j =>
      rw [Scheme.appendFullCellsScheme_grade_natAdd, Lvl.Φ_natAdd]
      exact isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid _ _) _ _).1
  · induction s using Fin.addCases with
    | left e =>
      rcases hcases hs with h | h | h
      exacts [hlC _ h, hl2 _ h, hlD _ h]
    | right j =>
      set κ := agreementHeight (grid (g + 1) (bound I)) R (entry I (g + 1) j) with hκ
      have hκm : κ ∈ grid (g + 1) (bound I) := (agreementHeight_spec (bot_mem_grid _ _) _ _).1
      have hκv : IsSelfVisible (g + 1) κ := isSelfVisible_of_mem_grid hκm
      refine ⟨constStepSuppressor (g + 1) κ, id, ⟨antitone_constStepSuppressor _ _,
        isSelfVisible_constStepSuppressor hκv, rfl, monotone_id, fun _ _ _ _ _ ↦ rfl⟩,
        fun t ↦ ?_⟩
      have htk : L.nextS.toCellScheme.grade t ≤ g + 1 := t.2.2.trans_eq
        (congrArg Prod.snd (Scheme.appendFullCellsScheme_gradedIndex_natAdd L.S (g + 1) _ j))
      rw [Scheme.appendFullCells_row_natAdd, constStepSuppressor_of_le _ htk, id, Lvl.Φ_natAdd]
      obtain ⟨t, -⟩ := t
      -- Beta-reduce the capped target at the cell `t`.
      dsimp only
      induction t using Fin.addCases with
      | left e =>
        rw [Lvl.Φ_castAdd, Lvl.Φ_castAdd]
        exact hL.capAgree R (entry I (g + 1) j) hRB κ hκv (isShort_of_mem_grid hκm)
          (agreementHeight_spec (bot_mem_grid _ _) R (entry I (g + 1) j)).2 e
      | right j' =>
        rw [Lvl.Φ_natAdd, Lvl.Φ_natAdd]
        exact agreementHeight_tri (bot_mem_grid _ _) _ _ _
  · induction t using Fin.addCases with
    | left e =>
      rcases hcases ht with h | h | h
      exacts [haC s _ h hst hg, ha2 s _ h hst hg, haD s _ h hst hg]
    | right j =>
      refine ⟨Fin.natAdd _ i₀, by
        rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd,
          Scheme.appendFullCellsScheme_gradedIndex_natAdd], ?_⟩
      rw [Lvl.Φ_natAdd, hi₀, agreementHeight_self_ceiling']
      exact le_gridPoint_of_mem_codeGrid (hL.Φ_mem_codeGrid hRB s)

/-! ### The structure of the next level
-/

theorem Lvl.next_S (L : Lvl I g) : L.next.S = L.nextS := rfl

theorem Lvl.next_embed_apply (L : Lvl I g) (d : Fin I.amalgam.card) :
    L.next.embed d = Fin.castAdd (cat I (g + 1)).card (L.embed d) := rfl

theorem Lvl.Good.next_lowerEmb (hL : L.Good) :
    I.amalgam.toCellScheme.IsLowerEmbedding L.next.S.toCellScheme L.next.embed :=
  (Scheme.isLowerEmbedding_castAdd (S := L.S) (g + 1) (cat I (g + 1)).card
      (fun i ↦ L.Φ (entry I (g + 1) i)) L.not_le).comp hL.lowerEmb

theorem Lvl.Good.next_comap_rows (hL : L.Good) :
    L.next.S.rows.comap hL.next_lowerEmb = I.amalgam.rows := by
  have h := Rows.comap_comap L.nextS.rows
    (Scheme.isLowerEmbedding_castAdd (S := L.S) (g + 1) (cat I (g + 1)).card
      (fun i ↦ L.Φ (entry I (g + 1) i)) L.not_le) hL.lowerEmb
  rw [Scheme.comap_rows_castAdd, hL.comap_rows] at h
  exact h.symm

theorem Lvl.Good.next_scope_embed (hL : L.Good) (d : Fin I.amalgam.card) :
    L.next.S.toCellScheme.scope (L.next.embed d) = I.amalgam.toCellScheme.scope d :=
  (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans (hL.scope_embed d)

theorem Lvl.Good.next_mem_range (hL : L.Good) (z : Fin L.next.S.card)
    (hz : L.next.S.toCellScheme.scope z ≠ univ) : z ∈ Set.range L.next.embed := by
  induction z using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
  | left e =>
    have hz' : L.S.toCellScheme.scope e ≠ univ := by
      have := (Scheme.appendFullCellsScheme_scope_castAdd L.S (g + 1) (cat I (g + 1)).card e)
      exact fun h ↦ hz (this.trans h)
    obtain ⟨d, rfl⟩ := hL.mem_range e hz'
    exact ⟨d, rfl⟩

theorem Lvl.Good.next_wf (hL : L.Good) (hg : g + 1 ≤ m + 2) : L.next.S.IsWellFormed :=
  Scheme.isWellFormed_appendFullCells (M := (cat I (g + 1)).card)
    (r := fun i ↦ L.Φ (entry I (g + 1) i)) (h := L.not_le) hL.wf (by omega) hg

theorem Lvl.Good.next_coded (hL : L.Good) : L.next.S.IsCoded :=
  Scheme.isCoded_appendFullCells (h := L.not_le) hL.coded fun i d ↦
    lt_omega0_sq_of_mem_codeGrid (hL.Φ_mem_codeGrid (mem_codeGrid_of_mem_cat (entry_mem i)) d)

theorem Lvl.Good.next_consistent (hL : L.Good) : L.next.S.rows.IsConsistent := by
  -- The scheme of the next level is the next scheme, by definition.
  change L.nextS.rows.IsConsistent
  intro s
  induction s using Fin.addCases with
  | right i =>
    have hu := Scheme.appendFullCellsScheme_gradedIndex_natAdd L.S (g + 1) (cat I (g + 1)).card i
    have h := hL.isLawfulBelow_Φ (entry_mem (k := g + 1) i)
    -- The graded index of the new cell, in the next scheme.
    change L.nextS.rows.IsLawfulBelow (L.nextS.toCellScheme.gradedIndex (Fin.natAdd _ i))
      (L.nextS.rows.row (Fin.natAdd _ i))
    rw [Scheme.appendFullCells_row_natAdd_eq]
    rw [show L.nextS.toCellScheme.gradedIndex (Fin.natAdd _ i) =
      ((univ : Finset (Fin (m + 2))), g + 1) from hu]
    exact h
  | left s =>
    have hφ := Scheme.isLowerEmbedding_castAdd (S := L.S) (g + 1) (cat I (g + 1)).card
      (fun i ↦ L.Φ (entry I (g + 1) i)) L.not_le
    refine (CellScheme.Rows.isLawfulBelow_comap_iff hφ (hφ.image_below_gradedIndex s)).mp ?_
    rw [Scheme.comap_rows_castAdd]
    convert hL.consistent s using 1
    funext t
    exact congrArg (fun R : L.S.toCellScheme.Rows ↦ R.row s t) Scheme.comap_rows_castAdd

/-- **Lifts below a pair not above `(univ, g + 1)`** are those of the level. -/
theorem Lvl.cappedLift_nextS_iff {X Y : Finset (Fin (m + 2)) × ℕ} (hXY : X ≤ Y)
    (hY : ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ Y) :
    L.nextS.rows.CappedLift hXY ↔ L.S.rows.CappedLift hXY := by
  have h : L.S.toCellScheme.IsSourcePrefix L.nextS.toCellScheme (Fin.castAdd _) Y :=
    ⟨Scheme.isLowerEmbedding_castAdd (S := L.S) (g + 1) (cat I (g + 1)).card
      (fun i ↦ L.Φ (entry I (g + 1) i)) L.not_le,
      Scheme.appendFullCellsScheme_scope_castAdd L.S (g + 1) _,
      fun d hd ↦ ⟨⟨d, Scheme.lt_card_of_mem_below hY hd⟩, rfl⟩⟩
  rw [← h.cappedLift_iff hXY le_rfl, Scheme.comap_rows_castAdd]

/-! ### Extension from the boundary through the next layer
-/

theorem Lvl.Good.Φ_old (hL : L.Good) (R : Prof I) (d : Fin I.amalgam.card) :
    L.Φ R (Fin.castAdd _ (L.embed d)) = R d := by
  rw [Lvl.Φ_castAdd, hL.literal]

/-- The old labels of a labelling of the next scheme up to the grade `g + 1`, a profile above. -/
noncomputable def Lvl.oldLabels (L : Lvl I g) (w : Fin L.nextS.card → Label.{u}) (P : Prof I) :
    Prof I := fun d ↦
  if I.amalgam.toCellScheme.grade d ≤ g + 1 then w (Fin.castAdd _ (L.embed d)) else P d

theorem Lvl.oldLabels_of_le {w : Fin L.nextS.card → Label.{u}} {P : Prof I}
    {d : Fin I.amalgam.card} (hd : I.amalgam.toCellScheme.grade d ≤ g + 1) :
    L.oldLabels w P d = w (Fin.castAdd _ (L.embed d)) := by
  unfold Lvl.oldLabels; exact ite_eq_left hd

theorem Lvl.Good.isLawfulBelow_oldLabels (hL : L.Good) {x : Fin (m + 2)}
    {w : Fin L.nextS.card → Label.{u}} (P : Prof I)
    (hw : L.nextS.rows.IsLawfulBelow (univ.erase x, g + 1) fun z ↦ w z) :
    I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1) fun d ↦ L.oldLabels w P d := by
  have h1 := (L.isLawfulBelow_nextS_iff fun h ↦ Seed.ne_univ_erase x
    (univ_subset_iff.mp h.1)).mp hw
  have h2 := (hL.isLawfulBelow_old_iff (X := (univ.erase x, g + 1)) (Seed.ne_univ_erase x)
    (w := fun e ↦ w (Fin.castAdd _ e))).mp h1
  exact (Rows.isLawfulBelow_congr (R := I.amalgam.rows) (X := (univ.erase x, g + 1))
    fun d hd ↦ (Lvl.oldLabels_of_le hd.2).symm).mp h2

/-- A cell of the next scheme of scope other than the ground set below `(univ, g + 1)` is an old
cell of grade at most `g + 1`. -/
theorem Lvl.Good.exists_old (hL : L.Good) {z : Fin L.nextS.card}
    (hz : z ∈ L.nextS.toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1))
    (hne : L.nextS.toCellScheme.scope z ≠ univ) :
    ∃ d, I.amalgam.toCellScheme.grade d ≤ g + 1 ∧ z = Fin.castAdd _ (L.embed d) := by
  induction z using Fin.addCases with
  | right j => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ j) hne
  | left e =>
    rw [Scheme.appendFullCellsScheme_scope_castAdd] at hne
    obtain ⟨d, rfl⟩ := hL.mem_range e hne
    refine ⟨d, ?_, rfl⟩
    have := hz.2
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, hL.gradedIndex_embed] at this
    exact this

/-- **Extension from the boundary along the row labelling of a profile, at a positive cap
self-visible and short at `g + 1`**: the row labelling of the orbit code `Q` of the old labels, read
by their orbit decoder at the cap; it keeps the cap because the section of `Q` is readable for `Q`
(`Lvl.Good.readable`) and agrees with that of the profile capped at the cap (`Lvl.Good.capAgree`).
-/
theorem Lvl.Good.exists_extension (hL : L.Good) {P : Prof I} (hP : P ∈ cat I (g + 1))
    {h : Label.{u}} (hh : IsSelfVisible (g + 1) h) (hs : IsShort (g + 1) h) (hb : h ≠ ⊥)
    {w : Fin L.nextS.card → Label.{u}}
    (hwC : L.nextS.rows.IsLawfulBelow (coatC, g + 1) fun z ↦ w z)
    (hwD : L.nextS.rows.IsLawfulBelow (coatD, g + 1) fun z ↦ w z)
    (hwP : ∀ d : Fin I.amalgam.card, I.amalgam.toCellScheme.grade d ≤ g + 1 →
      min (w (Fin.castAdd _ (L.embed d))) h = min (P d) h) :
    ∃ r : L.nextS.toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) → Label.{u},
      L.nextS.rows.IsLawfulBelow (univ, g + 1) r ∧
      (∀ z, L.nextS.toCellScheme.scope z.1 ≠ univ → r z = w z) ∧
      ∀ z, min (r z) h = min (L.Φ P z) h := by
  classical
  set W := L.oldLabels w P with hW
  have hWP (d : Fin I.amalgam.card) : min (W d) h = min (P d) h := by
    by_cases hd : I.amalgam.toCellScheme.grade d ≤ g + 1
    · rw [hW, Lvl.oldLabels_of_le hd]; exact hwP d hd
    · rw [hW, Lvl.oldLabels, ite_eq_right hd]
  set Q : Prof I := orbitCode (g + 1) W with hQ
  have hPo := (mem_cat.mp hP).2
  have hQP (d : Fin I.amalgam.card) : min (Q d) h = min (P d) h :=
    min_orbitCode_eq hh hs hPo hWP d
  have hQW (d : Fin I.amalgam.card) : min (Q d) h = min (W d) h := (hQP d).trans (hWP d).symm
  have hQ3 : Q ∈ cat I (g + 1) := mem_cat.mpr
    ⟨⟨(hL.isLawfulBelow_oldLabels P hwC).orbitCode fun d ↦ d.2.2,
      (hL.isLawfulBelow_oldLabels P hwD).orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩
  have hQB := mem_codeGrid_of_mem_cat hQ3
  have hag (z : L.nextS.toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
      min (orbitDecoder (g + 1) W h (L.Φ Q z)) h = min (L.Φ P z) h := by
    obtain ⟨z, -⟩ := z
    induction z using Fin.addCases with
    | left e =>
      rw [min_orbitDecoder_eq_of_isReadableAt hh hQW (by
          rw [Lvl.Φ_castAdd]; exact hL.readable Q orbitCode_orbitCode hQB e),
        Lvl.Φ_castAdd, Lvl.Φ_castAdd]
      exact hL.capAgree Q P hQB h hh hs hQP e
    | right j =>
      rw [Lvl.Φ_natAdd, Lvl.Φ_natAdd,
        min_orbitDecoder_eq (isSelfVisible_of_mem_grid (agreementHeight_spec
          (bot_mem_grid _ _) _ _).1)]
      exact min_agreementHeight_eq_of_isShort hh hs
        (fun d ↦ ⟨hQB d, mem_codeGrid_of_mem_cat hP d⟩) hQP _
  refine ⟨fun z ↦ orbitDecoder (g + 1) W h (L.Φ Q z),
    (hL.isLawfulBelow_Φ hQ3).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_orbitDecoder hh hb) (fun _ ↦ eq_bot_of_orbitDecoder_eq_bot hb), fun z hz ↦ ?_,
    hag⟩
  obtain ⟨d, hd, hdz⟩ := hL.exists_old z.2 hz
  -- The decoded row labelling at the old cell `z`.
  change orbitDecoder (g + 1) W h (L.Φ Q z.1) = w z.1
  rw [hdz, hL.Φ_old, orbitDecoder_orbitCode hQW d, hW, Lvl.oldLabels_of_le hd]

/-- **Extension from the boundary at the cap `⊥`**, through the next layer. -/
theorem Lvl.Good.exists_extension_bot (hL : L.Good) {w : Fin L.nextS.card → Label.{u}}
    (hwC : L.nextS.rows.IsLawfulBelow (coatC, g + 1) fun z ↦ w z)
    (hwD : L.nextS.rows.IsLawfulBelow (coatD, g + 1) fun z ↦ w z) :
    ∃ r : L.nextS.toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) → Label.{u},
      L.nextS.rows.IsLawfulBelow (univ, g + 1) r ∧
      ∀ z, L.nextS.toCellScheme.scope z.1 ≠ univ → r z = w z := by
  set W := L.oldLabels w (fun _ ↦ ⊥) with hW
  set Q : Prof I := orbitCode (g + 1) W with hQ
  have hQ3 : Q ∈ cat I (g + 1) := mem_cat.mpr
    ⟨⟨(hL.isLawfulBelow_oldLabels _ hwC).orbitCode fun d ↦ d.2.2,
      (hL.isLawfulBelow_oldLabels _ hwD).orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩
  have hQW (d : Fin I.amalgam.card) :
      min (Q d) (gridPoint (g + 1) 0) = min (W d) (gridPoint (g + 1) 0) :=
    min_orbitCode_gridPoint_zero d
  refine ⟨fun z ↦ orbitDecoder (g + 1) W (gridPoint (g + 1) 0) (L.Φ Q z),
    (hL.isLawfulBelow_Φ hQ3).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_orbitDecoder (isSelfVisible_gridPoint _ 0) (gridPoint_ne_bot _ 0))
      (fun _ ↦ eq_bot_of_orbitDecoder_eq_bot (gridPoint_ne_bot _ 0)), fun z hz ↦ ?_⟩
  obtain ⟨d, hd, hdz⟩ := hL.exists_old z.2 hz
  -- The decoded row labelling at the old cell `z`.
  change orbitDecoder (g + 1) W (gridPoint (g + 1) 0) (L.Φ Q z.1) = w z.1
  rw [hdz, hL.Φ_old, orbitDecoder_orbitCode hQW d, hW, Lvl.oldLabels_of_le hd]

/-! ### The lift at the grade `g + 1`
-/

/-- The common face of the two coatoms is the face of the amalgam on `m` points. -/
theorem inter_props {x y : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2))))
    (hy : y ∈ (Pts : Finset (Fin (m + 2)))) (hxy : x ≠ y) :
    univ.erase x ∩ univ.erase y ∈ I.amalgam.toCellScheme.faces ∧
      #(univ.erase x ∩ univ.erase y) = m := by
  have heq : univ.erase x ∩ univ.erase y =
      (univ.erase (Fin.last (m + 1))).erase (Fin.castSucc (Fin.last m)) := by
    rcases Seed.pair_cases hx hy hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · ext z
      simp only [mem_inter, mem_erase, mem_univ, and_true]
      exact and_comm
    · ext z
      simp only [mem_inter, mem_erase, mem_univ, and_true]
  rw [heq]
  refine ⟨I.commonFace_mem_faces, ?_⟩
  rw [card_erase_of_mem (mem_erase.mpr ⟨Seed.last_ne_castSucc.symm, mem_univ _⟩),
    card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  omega

/-- Lawfulness below the two coatoms, in either order. -/
theorem lawful_pair {ι : Type*} {D : CellScheme ι (Fin (m + 2))} {R : D.Rows.{u}} {k : ℕ}
    {x y : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2))))
    (hy : y ∈ (Pts : Finset (Fin (m + 2)))) (hxy : x ≠ y) {w : ι → Label.{u}}
    (hwx : R.IsLawfulBelow (univ.erase x, k) fun z ↦ w z)
    (hwy : R.IsLawfulBelow (univ.erase y, k) fun z ↦ w z) :
    R.IsLawfulBelow (coatC, k) (fun z ↦ w z) ∧ R.IsLawfulBelow (coatD, k) fun z ↦ w z := by
  rcases Seed.pair_cases hx hy hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [⟨hwx, hwy⟩, ⟨hwy, hwx⟩]

/-- A cell of the next scheme of graded index `(univ, g + 1)` is a cell of the new layer. -/
theorem Lvl.exists_natAdd_eq (L : Lvl I g) {u : Fin L.nextS.card}
    (hu : L.nextS.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), g + 1)) :
    ∃ i, Fin.natAdd _ i = u := by
  by_cases hlt : (u : ℕ) < L.S.card
  · refine absurd ?_ (L.not_le ⟨u, hlt⟩)
    rw [← Scheme.appendFullCellsScheme_gradedIndex_of_lt hlt]
    exact hu.ge
  · have hu' : (u : ℕ) < L.S.card + (cat I (g + 1)).card := u.2
    exact ⟨⟨u - L.S.card, by omega⟩, Fin.ext (by simp; omega)⟩

/-- **The capped lift at the grade `g + 1`, from either coatom**, in the next scheme, for
`g + 1 ≤ m`: the one-grade lift `CellScheme.Rows.cappedLift_of_boundaries_short` with the lift at
the grade `g` of the level, the boundary lifts of the amalgam through the common face, the extension
from the boundary at `⊥` and at the caps self-visible and short at `g + 1`
(`Lvl.Good.exists_extension`), and the serving cells at `(univ, g + 1)`. -/
theorem Lvl.Good.cappedLift_next (hL : L.Good) (hgm : g + 1 ≤ m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    L.nextS.rows.CappedLift (X := (univ.erase x, g + 1))
      (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  classical
  obtain ⟨y, hy, hxy⟩ := Seed.exists_other hx
  obtain ⟨hOf, hOcard⟩ := inter_props (I := I) hx hy hxy
  have hcard (z : Fin (m + 2)) : #(univ.erase z) = m + 1 := Seed.card_erase z
  have hnot (z : Fin (m + 2)) : ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ (univ.erase z, g + 1) :=
    fun h ↦ Seed.ne_univ_erase z (univ_subset_iff.mp h.1)
  have hlift : L.nextS.rows.CappedLift (X := (univ.erase x, g))
      (Y := ((univ : Finset (Fin (m + 2))), g)) ⟨erase_subset _ _, le_rfl⟩ :=
    (L.cappedLift_nextS_iff _ fun h ↦ absurd h.2 (by simp only; omega)).mpr (hL.lift x hx g le_rfl)
  have hright : L.nextS.rows.CappedLift (X := (univ.erase x ∩ univ.erase y, g + 1))
      (Y := (univ.erase y, g + 1)) ⟨inter_subset_right, le_rfl⟩ :=
    (L.cappedLift_nextS_iff _ (hnot y)).mpr (hL.cappedLift_old
      ⟨hOf, by omega, show g + 1 ≤ #(univ.erase x ∩ univ.erase y) by omega⟩
      ⟨I.erase_mem_faces hy, by omega, show g + 1 ≤ #(univ.erase y) by rw [hcard]; omega⟩
      (Seed.ne_univ_erase y) _)
  obtain ⟨c, hc⟩ := I.exists_gradedIndex_eq (univ.erase x, g + 1)
    ⟨I.erase_mem_faces hx, by omega, show g + 1 ≤ #(univ.erase x) by rw [hcard]; omega⟩
    (Seed.ne_univ_erase x)
  obtain ⟨i₀, -⟩ := exists_entry_eq (bot_mem_cat (I := I) (g + 1))
  have hscope {z : Fin L.nextS.card} (hz : z ∈ L.nextS.toCellScheme.below (univ.erase x, g + 1) ∨
      z ∈ L.nextS.toCellScheme.below (univ.erase y, g + 1)) :
      L.nextS.toCellScheme.scope z ≠ univ := fun he ↦ hz.elim
    (fun h ↦ Seed.ne_univ_erase x (univ_subset_iff.mp (he.ge.trans h.1)))
    fun h ↦ Seed.ne_univ_erase y (univ_subset_iff.mp (he.ge.trans h.1))
  have hbot : L.nextS.rows.ExtendsFromBoundary (univ.erase x, g + 1) (univ.erase y, g + 1)
      ((univ : Finset (Fin (m + 2))), g + 1) ⊥ fun _ ↦ ⊥ := by
    intro w hwU hwV _
    obtain ⟨hwC, hwD⟩ := lawful_pair hx hy hxy hwU hwV
    obtain ⟨r, hr, hrw⟩ := hL.exists_extension_bot hwC hwD
    exact ⟨r, hr, fun d hd ↦ hrw d (hscope hd), fun _ ↦ by simp⟩
  refine Rows.cappedLift_of_boundaries_short (C := univ.erase x) (B := univ) (j := g)
    (U₀ := (univ.erase x, g + 1)) (V₀ := (univ.erase y, g + 1))
    (O₀ := (univ.erase x ∩ univ.erase y, g + 1))
    (U := (univ.erase x, g + 1)) (V := (univ.erase y, g + 1))
    (O := (univ.erase x ∩ univ.erase y, g + 1)) (erase_subset _ _)
    ⟨Fin.castAdd _ (L.embed c), by
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, hL.gradedIndex_embed, hc]⟩ hlift
    le_rfl ⟨inter_subset_left, le_rfl⟩ ⟨inter_subset_right, le_rfl⟩ ⟨subset_univ _, le_rfl⟩
    ⟨subset_univ _, le_rfl⟩ (fun d h1 h2 ↦ ⟨subset_inter h1.1 h2.1, h1.2⟩) (Rows.cappedLift_refl _)
    hright hbot le_rfl ⟨inter_subset_left, le_rfl⟩ ⟨inter_subset_right, le_rfl⟩
    ⟨subset_univ _, le_rfl⟩ ⟨subset_univ _, le_rfl⟩
    (fun d h1 h2 ↦ ⟨subset_inter h1.1 h2.1, h1.2⟩) (Rows.cappedLift_refl _) hright
    ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩ fun u hu ↦ ?_
  obtain ⟨i, rfl⟩ := L.exists_natAdd_eq hu
  have hrowB (d : L.nextS.toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
      L.nextS.rows.rowBelow _ hu d = L.Φ (entry I (g + 1) i) d :=
    Scheme.appendFullCells_row_natAdd i _
  have hmem := hL.Φ_mem_codeGrid (mem_codeGrid_of_mem_cat (entry_mem (k := g + 1) i))
  refine ⟨hL.next_consistent _, fun d ↦ ?_, fun d ↦ ?_, fun h hh hs hb ↦ ?_⟩
  · rw [hrowB]; exact isShort_of_mem_codeGrid (hmem _)
  · rw [hrowB]; exact ne_top_of_mem_codeGrid (hmem _)
  · intro w hwU hwV hwS
    obtain ⟨hwC, hwD⟩ := lawful_pair hx hy hxy hwU hwV
    have hwP (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ g + 1) :
        min (w (Fin.castAdd _ (L.embed d))) h = min (entry I (g + 1) i d) h := by
      have hm : Fin.castAdd (cat I (g + 1)).card (L.embed d) ∈
          L.nextS.toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) := by
        rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd,
          hL.gradedIndex_embed]
        exact ⟨subset_univ _, hd⟩
      have hbd : Fin.castAdd (cat I (g + 1)).card (L.embed d) ∈
            L.nextS.toCellScheme.below (univ.erase x, g + 1) ∨
          Fin.castAdd (cat I (g + 1)).card (L.embed d) ∈
            L.nextS.toCellScheme.below (univ.erase y, g + 1) := by
        simp only [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd,
          hL.gradedIndex_embed]
        rcases I.scope_subset_or hx hy hxy d with h' | h'
        exacts [.inl ⟨h', hd⟩, .inr ⟨h', hd⟩]
      have h1 := hwS ⟨_, hm⟩ hbd
      rwa [hrowB, hL.Φ_old] at h1
    obtain ⟨r, hr, hrw, hrc⟩ := hL.exists_extension (entry_mem (k := g + 1) i) hh hs hb.ne' hwC
      hwD hwP
    refine ⟨r, hr, fun d hd ↦ hrw d (hscope hd), fun d ↦ ?_⟩
    rw [hrowB]
    exact hrc d

/-! ### The section operator of the next level
-/

theorem hat_of_le {k : ℕ} {P : Prof I} {d : Fin I.amalgam.card}
    (hd : I.amalgam.toCellScheme.grade d ≤ k) : hat I k P d = P d :=
  CellScheme.splice_of_le hd

theorem hat_of_lt {k : ℕ} {P : Prof I} {d : Fin I.amalgam.card}
    (hd : k < I.amalgam.toCellScheme.grade d) : hat I k P d = ⊥ :=
  CellScheme.splice_of_lt hd

theorem isCutLawful_hat {k : ℕ} {P : Prof I} (hP : IsCutLawful I k P) :
    IsCutLawful I k (hat I k P) :=
  ⟨(Rows.isLawfulBelow_congr fun _ hd ↦ (hat_of_le hd.2).symm).mp hP.1,
    (Rows.isLawfulBelow_congr fun _ hd ↦ (hat_of_le hd.2).symm).mp hP.2⟩

theorem hat_mem_codeGrid {k K B : ℕ} {P : Prof I} (hP : ∀ d, P d ∈ codeGrid K B)
    (d : Fin I.amalgam.card) : hat I k P d ∈ codeGrid K B := by
  by_cases hd : I.amalgam.toCellScheme.grade d ≤ k
  · rw [hat_of_le hd]; exact hP d
  · rw [hat_of_lt (_root_.not_le.mp hd)]; exact mem_insert_self _ _

theorem min_hat_eq {k : ℕ} {P P' : Prof I} {h : Label.{u}} (hag : ∀ d, min (P d) h = min (P' d) h)
    (d : Fin I.amalgam.card) : min (hat I k P d) h = min (hat I k P' d) h := by
  by_cases hd : I.amalgam.toCellScheme.grade d ≤ k
  · rw [hat_of_le hd, hat_of_le hd]; exact hag d
  · rw [hat_of_lt (_root_.not_le.mp hd), hat_of_lt (_root_.not_le.mp hd)]

/-- The codes lie in the code grid of the bound. -/
theorem code_mem_codeGrid (k : ℕ) (P : Prof I) (d : Fin I.amalgam.card) :
    code k P d ∈ codeGrid k (bound I) :=
  codeGrid_mono (B := 2 * I.amalgam.card) (by simp only [bound]; omega)
    (orbitMap_mem_codeGrid (by simp) _)

/-- A cell of the next scheme of grade above `g + 1` is an old cell of the level. -/
theorem Lvl.Good.exists_old_of_lt (hL : L.Good) {z : Fin (L.S.card + (cat I (g + 1)).card)}
    (hz : ¬ (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).grade z ≤ g + 1) :
    ∃ d, z = Fin.castAdd _ (L.embed d) := by
  induction z using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le hz
  | left e =>
    rw [Scheme.appendFullCellsScheme_grade_castAdd] at hz
    obtain ⟨d, rfl⟩ := hL.mem_range_of_lt (by omega : g < L.S.toCellScheme.grade e)
    exact ⟨d, rfl⟩

theorem Lvl.nextσ_of_le {P : Prof I} {z : Fin (L.S.card + (cat I (g + 1)).card)}
    (hz : (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).grade z ≤ g + 1) :
    L.nextσ P z =
      upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) P) (L.Φ (code (g + 1) P) z) := by
  unfold Lvl.nextσ; exact ite_eq_left hz

theorem Lvl.Good.nextσ_old_of_lt (hL : L.Good) {P : Prof I} {d : Fin I.amalgam.card}
    (hd : ¬ (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).grade
      (Fin.castAdd _ (L.embed d)) ≤ g + 1) :
    L.nextσ P (Fin.castAdd _ (L.embed d)) = P d := by
  unfold Lvl.nextσ
  rw [ite_eq_right hd, Fin.append_left, hL.literal]

/-- **The next section is literal.** -/
theorem Lvl.Good.next_literal (hL : L.Good) (P : Prof I) (d : Fin I.amalgam.card) :
    L.next.σ P (L.next.embed d) = P d := by
  -- The section and the old cells of the next level, by definition.
  change L.nextσ P (Fin.castAdd _ (L.embed d)) = P d
  by_cases hd : (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).grade
      (Fin.castAdd _ (L.embed d)) ≤ g + 1
  · rw [L.nextσ_of_le hd, hL.Φ_old, upperDecoderAt_orbitCode, hat_of_le]
    rw [Scheme.appendFullCellsScheme_grade_castAdd, hL.lowerEmb.grade_eq] at hd
    exact hd
  · exact hL.nextσ_old_of_lt hd

/-- **The next section is lawful.** -/
theorem Lvl.Good.next_lawful (hL : L.Good) (P : Prof I) (hP : IsCutLawful I (g + 1) P) :
    L.next.S.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g + 1)
      fun z ↦ L.next.σ P z := by
  have hQ : code (g + 1) P ∈ cat I (g + 1) := by
    obtain ⟨hC, hD⟩ := isCutLawful_hat hP
    exact mem_cat.mpr ⟨⟨hC.orbitCode fun d ↦ d.2.2, hD.orbitCode fun d ↦ d.2.2⟩,
      orbitCode_orbitCode⟩
  have h := (hL.isLawfulBelow_Φ hQ).map_of_apply_eq_bot (fun z ↦ z.2.2)
    (isWitness_upperDecoderAt (w := hat I (g + 1) P) (B := bound I) (K := g + 2) (by omega))
    (fun _ ↦ eq_bot_of_upperDecoderAt_eq_bot)
  refine (Rows.isLawfulBelow_congr (R := L.nextS.rows)
    (w := fun z ↦ upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) P)
      (L.Φ (code (g + 1) P) z)) (w' := L.nextσ P) fun z hz ↦ ?_).mp h
  exact (L.nextσ_of_le hz.2).symm

/-- **The next section takes values in the code grid at `g + 2`.** -/
theorem Lvl.Good.next_mem (hL : L.Good) (P : Prof I)
    (hP : ∀ d, P d ∈ codeGrid (g + 1 + 1) (bound I)) (z : Fin L.next.S.card) :
    L.next.σ P z ∈ codeGrid (g + 1 + 1) (bound I) := by
  -- The section of the next level, by definition.
  change L.nextσ P z ∈ _
  by_cases hz : (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).grade z ≤ g + 1
  · rw [L.nextσ_of_le hz]
    exact upperDecoderAt_mem_codeGrid_of_mem (by omega) (hat_mem_codeGrid hP)
      (hL.Φ_mem_codeGrid (code_mem_codeGrid _ _) z)
  · obtain ⟨d, rfl⟩ := hL.exists_old_of_lt hz
    rw [hL.nextσ_old_of_lt hz]
    exact hP d

/-- **The next section agrees capped at every cap self-visible and short at `g + 2`**: through
`Label.min_upperDecoderAt_comp_eq`, the row labellings of codes agreeing capped at a cap
self-visible and short at `g + 1` agreeing capped at it (`Lvl.Good.capAgree`, the ultrametric
inequality). -/
theorem Lvl.Good.next_capAgree (hL : L.Good) (P P' : Prof I)
    (hP : ∀ d, P d ∈ codeGrid (g + 1 + 1) (bound I)) (h : Label.{u})
    (hh : IsSelfVisible (g + 1 + 1) h) (hs : IsShort (g + 1 + 1) h)
    (hag : ∀ d, min (P d) h = min (P' d) h) (z : Fin L.next.S.card) :
    min (L.next.σ P z) h = min (L.next.σ P' z) h := by
  -- The section of the next level, by definition.
  change min (L.nextσ P z) h = min (L.nextσ P' z) h
  by_cases hz : (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).grade z ≤ g + 1
  · rw [L.nextσ_of_le hz, L.nextσ_of_le hz]
    refine min_upperDecoderAt_comp_eq (k := g + 1) (K := g + 2) (by omega) hh hs
      (fun d ↦ le_gridPoint_of_mem_codeGrid (hat_mem_codeGrid hP d)) (min_hat_eq hag) L.Φ
      (fun c c' hc hc' Γ hΓv hΓs hcc z ↦ ?_) z
    have hcB (d : Fin I.amalgam.card) : c d ∈ codeGrid (g + 1) (bound I) :=
      codeGrid_mono (by simp only [Fintype.card_fin, bound]; omega) (hc d)
    have hcB' (d : Fin I.amalgam.card) : c' d ∈ codeGrid (g + 1) (bound I) :=
      codeGrid_mono (by simp only [Fintype.card_fin, bound]; omega) (hc' d)
    induction z using Fin.addCases with
    | left e =>
      rw [Lvl.Φ_castAdd, Lvl.Φ_castAdd]
      exact hL.capAgree c c' hcB Γ hΓv hΓs hcc e
    | right i =>
      rw [Lvl.Φ_natAdd, Lvl.Φ_natAdd]
      exact min_agreementHeight_eq_of_isShort hΓv hΓs (fun d ↦ ⟨hcB d, hcB' d⟩) hcc _
  · obtain ⟨d, rfl⟩ := hL.exists_old_of_lt hz
    rw [hL.nextσ_old_of_lt hz, hL.nextσ_old_of_lt hz]
    exact hag d

/-- **The next section is readable at `g + 2`** for the orbit-canonical profiles. -/
theorem Lvl.Good.next_readable (hL : L.Good) (Q : Prof I) (hQ : orbitCode (g + 1 + 1) Q = Q)
    (hQB : ∀ d, Q d ∈ codeGrid (g + 1 + 1) (bound I)) (z : Fin L.next.S.card) :
    IsReadableAt (g + 1 + 1) Q (L.next.σ Q z) := by
  -- The section of the next level, by definition.
  change IsReadableAt (g + 1 + 1) Q (L.nextσ Q z)
  by_cases hz : (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).grade z ≤ g + 1
  · rw [L.nextσ_of_le hz]
    refine isReadableAt_upperDecoderAt_of_mem hQ (by omega) (hat_mem_codeGrid hQB) (fun d ↦ ?_)
      (hL.Φ_mem_codeGrid (code_mem_codeGrid _ _) z)
    by_cases hd : I.amalgam.toCellScheme.grade d ≤ g + 1
    · rw [hat_of_le hd]; exact isReadableAt_apply Q d
    · rw [hat_of_lt (_root_.not_le.mp hd)]; exact .inl rfl
  · obtain ⟨d, rfl⟩ := hL.exists_old_of_lt hz
    rw [hL.nextσ_old_of_lt hz]
    exact isReadableAt_apply Q d

/-- **The next level carries a cell at `(univ, j)` for every `0 < j ≤ g + 1`**: an old cell, or a
cell of the new layer. -/
theorem Lvl.Good.next_complete (hL : L.Good) (j : ℕ) (hj0 : 0 < j) (hj : j ≤ g + 1) :
    ∃ z, L.next.S.toCellScheme.gradedIndex z = ((univ : Finset (Fin (m + 2))), j) := by
  rcases Nat.lt_or_eq_of_le hj with hlt | rfl
  · obtain ⟨e, he⟩ := hL.complete j hj0 (by omega)
    exact ⟨Fin.castAdd _ e, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e).trans he⟩
  · obtain ⟨i₀, -⟩ := exists_entry_eq (bot_mem_cat (I := I) (g + 1))
    exact ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩

/-- **The next level is good**, for `g + 1 ≤ m`. -/
theorem Lvl.Good.next (hL : L.Good) (hgm : g + 1 ≤ m) : L.next.Good where
  lowerEmb := hL.next_lowerEmb
  scope_embed := hL.next_scope_embed
  comap_rows := hL.next_comap_rows
  mem_range := hL.next_mem_range
  faces := hL.faces
  wf := hL.next_wf (by omega)
  coded := hL.next_coded
  consistent := hL.next_consistent
  lawful := hL.next_lawful
  mem := hL.next_mem
  literal := hL.next_literal
  capAgree := hL.next_capAgree
  readable := hL.next_readable
  lift x hx j hj := by
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact (L.cappedLift_nextS_iff _ fun h ↦ absurd h.2 (by simp only; omega)).mpr
        (hL.lift x hx j (by omega))
    · exact hL.cappedLift_next hgm hx
  complete := hL.next_complete

/-- **Extension at the cap `⊥` below the full face**, from the two coatoms at the grade `g` of a
level: a labelling lawful below both coatoms at `g` is, off the ground set, some labelling lawful
below `(univ, g)`. -/
def Lvl.HasBotExtension (L : Lvl I g) : Prop :=
  ∀ w : Fin L.S.card → Label.{u}, L.S.rows.IsLawfulBelow (coatC, g) (fun z ↦ w z) →
    L.S.rows.IsLawfulBelow (coatD, g) (fun z ↦ w z) →
    ∃ r : L.S.toCellScheme.below ((univ : Finset (Fin (m + 2))), g) → Label.{u},
      L.S.rows.IsLawfulBelow (univ, g) r ∧ ∀ z, L.S.toCellScheme.scope z.1 ≠ univ → r z = w z

/-- **The next level of a good level extends at `⊥`** (`Lvl.Good.exists_extension_bot`). -/
theorem Lvl.Good.hasBotExtension_next (hL : L.Good) : L.next.HasBotExtension :=
  fun _ hwC hwD ↦ hL.exists_extension_bot hwC hwD

end Step

/-- **Every level up to the grade `m` is good**, for `m ≥ 2`. -/
theorem lvl_good (hm : 2 ≤ m) : (j : ℕ) → j + 2 ≤ m → (lvl I j).Good
  | 0, _ => base_good (by omega)
  | j + 1, hj => (lvl_good hm j (by omega)).next (by omega)

end VaughtConjecture.ProfileTower
