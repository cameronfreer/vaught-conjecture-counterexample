/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapTransport
import VaughtConjecture.Extension.MultiLayerStep
import VaughtConjecture.Extension.TwoFaceLiftExistsCounterexample

/-!
# Profile catalogues on five points, tested at the configuration of the seedL refutation

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`; here
a catalogue of new cells indexed by profiles of the whole amalgam, tested at the seeds of the
coatom types `TL` and `T5`, where the tower of the step fails); semantic contract, items 2–4.

Let `I` be a seed on five points (`m = 3`), with coatoms `C = {0, 1, 2, 3}` (`coatomC`) and
`D = {0, 1, 2, 4}` (`coatomD`).

**Profiles and catalogues.**  A *profile* (`Profile`) is a labelling of all the cells of the
amalgam of `I`, of every grade, the cells of grade above the grade of the catalogue included.  It
is *normalized* at the bound `N` (`IsNormalized`) when its value at each cell of grade `k` is `⊥`
or a grid point `ω * b + k` with `b ≤ N` (`Label.grid k N`).  The *grade-`j` cut* of the amalgam
is the set of its cells of grade at most `j`; a profile is *lawful on the grade-`j` cut*
(`IsCutLawful`) when it is lawful below `(C, j)` and below `(D, j)`, its values above the grade
`j` being unconstrained.  The *profile catalogue at the grade `j`* (`catalogue I N j`) is the
finite set of normalized profiles lawful on the grade-`j` cut.

**The profile scheme** (`profileScheme I N J`, an instance of `OrderedLayer.multiLayerScheme`).
For `1 ≤ j ≤ J` it has one new cell at `(univ, j)` per entry of the catalogue at the grade `j`
(`mult`, `entry`), and none above the grade `J`.  The row of the new cell of a profile `P` reads
every old cell by `P` and every new cell by the *agreement height* (`Label.agreementHeight`) of `P`
and the profile of that cell in the *cut grid* `Label.grid 3 (N + 1)` (`cutGrid`), computed over
all the cells of the amalgam (`rows_multiOldCell`, `rows_multiNewCell`).  So the readings of the
lower new cells are a function of the profile, and the values of a profile at the cells of higher
grade enter every agreement height.

**Field labellings** (`fieldLabelling`, `isLawfulBelow_fieldLabelling`).  For old labels `L` lawful
below `(C, 3)` and `(D, 3)` and a profile `P` in the catalogues of the grades `1 ≤ j ≤ J`, equal
to `L` up to the grade `J`, the labelling `L` on the old cells and `P`'s agreement heights on the
new cells is lawful below `(univ, 3)`: locality at a new cell is the identity capped at its label,
by the ultrametric inequality (`Label.agreementHeight_tri`), and availability into `(univ, j)` is
given by the cell of `P`.

**The test**, for every seed whose coatom types are `TL` and `T5` (the hypotheses of
`TwoFaceLiftExistsCounterexample.not_twoFaceLiftExists_two_of`, `seedL` among them).  Profiles of
five parameters are `tripleProfile A_C F_C A_D F_D G` (`CaseSplitCounterexample.tripleLabelling`
at the graded indices).  The *tie profile* `(ω + 1, ω + 2, ω + 1, ω + 2, 3)` reads `({3}, 1)` and
`({4}, 1)` alike, as the catalogue entry `b₀` of the refutation does.  A capped lift from `(C, 3)`
at a prescription `(A, ⊤, ⊤)` on `C` with `A ≠ ⊤` reaches its cap at a new cell at `(univ, 2)`
whose profile reads `({3}, 1)` strictly below `({4}, 1)` (`exists_separating_of_lift`, steps 4
and 5 of the refutation).

* **Top layer `2`: the refutation transfers** (`not_exists_lift_two`, `not_cappedLift_two`).
  With catalogues at the grades `1` and `2` only, the position of the step `2FL∃(2)` of the tower,
  the field labelling of the tie profile with `4` at the live cells of grade `3` is lawful below
  `(univ, 3)` (`isLawfulBelow_ambientTwo`), and at the cap `4`, its label at `({0, 1, 2}, 3)`,
  with the prescription `(ω + 1, ⊤, ⊤)` (its label at `({3}, 1)`), no capped lift from `(C, 3)`
  exists, at every inventory bound `N ≥ 1`.  A profile reading `({3}, 1)` strictly below
  `({4}, 1)` has agreement height at most `3` with the tie profile
  (`agreementHeight_tie_lt_capFour`): agreement heights are grid points `ω * b + 3`, and the tie
  value `ω + 1` has finite part `1`; the cap `4` lies between, as `ω * (B - 1) + 4` does in the
  refutation.  No cell of grade at most `2` reads a cell of grade `3`, so the values of profiles
  at `({0, 1, 2}, 3)` cannot raise these agreement heights (they can only lower them).
* **Top layer `3`: the layer at the grade `3` sees the cap** (`not_isLawfulBelow_three`,
  `exists_lift_three`).  With the catalogue at the grade `3`, no labelling lawful below
  `(univ, 3)` carries the labels of the top layer `2` at `(univ, 2)` with a label at least `4` at
  `({0, 1, 2}, 3)`: a new cell `w` at `(univ, 3)` with a label at least that one reads
  `({0, 1, 2}, 3)` at the value `G_w` of its profile there, and a profile of the catalogue at the
  grade `2`, other than the tie profile, agreeing with the profile of `w` capped at `G_w` then
  carries a label at least `4`.  At the configuration of the refutation in this scheme (the
  field labelling of the tie profile, the cap its label `3` at `({0, 1, 2}, 3)`, the prescription
  `(ω + 1, ⊤, ⊤)`) the capped lift exists, for every inventory bound `N ≥ 3`: the field labelling
  of a profile that reads `({3}, 1)` at `ω + 1` and agrees with the tie profile capped at `3`,
  reduced to the block `2` (`Label.reduce`), by the positive-cap transport
  `CellScheme.Rows.IsLawfulBelow.map_of_min_eq`.
* **Top layer `3` at the top of the inventory: the lift fails** (`not_exists_lift_top`,
  `not_cappedLift_three`).  At the field labelling of the top profile
  `(ω * N + 1, ω * N + 2, ω * N + 1, ω * N + 2, ω * (N - 1) + 3)`, the cap `ω * (N - 1) + 3` and
  the prescription `(ω * N + 1, ⊤, ⊤)`, no capped lift exists: a profile reading `({3}, 1)`
  strictly below `({4}, 1)` and reaching the cap would need a normalized value of grade `1` above
  `ω * N + 1` (`agreementHeight_top_lt`).  So the profile scheme with top layer `3` does not lift
  capped from `(C, 3)` into `(univ, 3)`, at any inventory bound `N ≥ 1`.  This is the failure of a
  fixed finite alphabet at its top block, as for the flat catalogue at `m = 0`
  (`SmallArityExamples.not_isBountiful_flatRows`), not the seedL obstruction: there is no room
  above the largest normalized value.

**Status.**  Compiled in this repository (theorem named): the statements above.  Argued, not
formalized: that with profiles normalized by rank (as the canonical codes of the canonical field
layer), which leave room above every normalized value, the failure at the top of the inventory
disappears; and that the transfer at the top layer `2` holds for every grid of agreement heights
self-visible at the grade `2`, since such a grid point at most a label of finite part `1` lies in
a lower block.  Prospective: the consistency and coding of the rows of the profile scheme, a
capped lift of a profile scheme from `(C, 3)` at every ambient labelling, the lifts from `(D, k)`
and at the other grades, and a completion below the full grade by profile catalogues for every
seed.  Nothing here gives a completion for every seed,
`StageType.HasApexCoatomExtensions`, or its use as a hypothesis of the main theorem; the uniform
completion stays open.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

The new cells have the shape of [Kni26, Definition 4.3.14] (cells of full scope indexed by
patterns of the cells below, rows between them given by meet heights); the patterns here are
profiles of the whole amalgam, and neither printed proof of [Kni26, Lemma 4.3.16] or
[Kni26, Lemma 4.3.20] is used.
-/

universe u

namespace VaughtConjecture.ProfileCatalogue

open Finset Label CellScheme OrderedLayer
open Ordinal hiding univ

variable {α : Ordinal.{u}} (I : Seed.{u} α 3) (N : ℕ)

/-! ### Profiles and their catalogues -/

/-- A **profile**: a labelling of all the cells of the amalgam, of every grade. -/
abbrev Profile : Type (u + 1) := Fin I.amalgam.card → Label.{u}

/-- A profile is **normalized** at the bound `N` when its value at every cell of grade `k` lies in
the grid at grade `k` with block bound `N`: `⊥` or a grid point `ω * b + k` with `b ≤ N`. -/
def IsNormalized (P : Profile I) : Prop :=
  ∀ d, P d ∈ grid (I.amalgam.toCellScheme.grade d) N

/-- The **grade-`j` cut** of the amalgam is the set of its cells of grade at most `j`; each lies
below `(C, j)` or below `(D, j)`.  A profile is **lawful on the grade-`j` cut** when it is lawful
below `(C, j)` and below `(D, j)`; its values at the cells of grade above `j` are not
constrained. -/
def IsCutLawful (j : ℕ) (P : Profile I) : Prop :=
  I.amalgam.rows.IsLawfulBelow (coatomC, j) (fun d ↦ P d) ∧
    I.amalgam.rows.IsLawfulBelow (coatomD, j) (fun d ↦ P d)

open Classical in
/-- The **profile catalogue at the grade `j`**: the normalized profiles lawful on the grade-`j`
cut.  It is finite, since the grids are. -/
noncomputable def catalogue (j : ℕ) : Finset (Profile I) :=
  (Fintype.piFinset fun d ↦ grid (I.amalgam.toCellScheme.grade d) N).filter (IsCutLawful I j)

variable {I N}

/-- Membership in the catalogue: normalized and lawful on the cut. -/
theorem mem_catalogue {j : ℕ} {P : Profile I} :
    P ∈ catalogue I N j ↔ IsNormalized I N P ∧ IsCutLawful I j P := by
  classical
  simp [catalogue, IsNormalized, Fintype.mem_piFinset]

variable (I N)

/-- The `i`-th entry of the catalogue at the grade `j`, in the order of `Finset.equivFin`, and the
profile constantly `⊥` past its size. -/
noncomputable def entry (j i : ℕ) : Profile I :=
  if h : i < (catalogue I N j).card then ((catalogue I N j).equivFin.symm ⟨i, h⟩ : Profile I)
  else fun _ ↦ ⊥

variable {I N}

/-- The entries of the catalogue below its size are in it. -/
theorem entry_mem {j i : ℕ} (hi : i < (catalogue I N j).card) :
    entry I N j i ∈ catalogue I N j := by
  rw [entry, dite_eq_left hi]
  exact ((catalogue I N j).equivFin.symm ⟨i, hi⟩).2

/-- Every profile of the catalogue is an entry below its size. -/
theorem exists_entry_eq {j : ℕ} {P : Profile I} (hP : P ∈ catalogue I N j) :
    ∃ i, i < (catalogue I N j).card ∧ entry I N j i = P := by
  refine ⟨(catalogue I N j).equivFin ⟨P, hP⟩, ((catalogue I N j).equivFin ⟨P, hP⟩).2, ?_⟩
  rw [entry, dite_eq_left ((catalogue I N j).equivFin ⟨P, hP⟩).2]
  simp

/-- A profile of the catalogue at a grade is in the catalogue at every lower grade. -/
theorem mem_catalogue_of_le {j j' : ℕ} {P : Profile I} (hP : P ∈ catalogue I N j) (hj : j' ≤ j) :
    P ∈ catalogue I N j' := by
  obtain ⟨hn, hC, hD⟩ := mem_catalogue.mp hP
  exact mem_catalogue.mpr ⟨hn, hC.mono (X := (coatomC, j')) ⟨subset_rfl, hj⟩,
    hD.mono (X := (coatomD, j')) ⟨subset_rfl, hj⟩⟩

variable (I N)

/-! ### The profile scheme -/

/-- The multiplicities of the profile scheme with top layer `J`: one new cell at `(univ, k + 1)`
per entry of the catalogue at the grade `k + 1` for `k + 1 ≤ J`, and none above. -/
noncomputable def mult (J : ℕ) (k : Fin 4) : ℕ :=
  if (k : ℕ) < J then (catalogue I N ((k : ℕ) + 1)).card else 0

/-- The profile of the cell with index `z` of the profile scheme with top layer `J`: the entry of
the catalogue that the new cell of that index carries.  It is not used at the old cells. -/
noncomputable def cellProfile (J z : ℕ) : Profile I :=
  if z < I.amalgam.card + mult I N J 0 then entry I N 1 (z - I.amalgam.card)
  else if z < I.amalgam.card + mult I N J 0 + mult I N J 1 then
    entry I N 2 (z - I.amalgam.card - mult I N J 0)
  else if z < I.amalgam.card + mult I N J 0 + mult I N J 1 + mult I N J 2 then
    entry I N 3 (z - I.amalgam.card - mult I N J 0 - mult I N J 1)
  else entry I N 4 (z - I.amalgam.card - mult I N J 0 - mult I N J 1 - mult I N J 2)

/-- The cut grid: the grid at the grade `3` with block bound `N + 1`. -/
noncomputable abbrev cutGrid : Finset Label.{u} := grid 3 (N + 1)

/-- The rows of the profile scheme: the new cell of an entry `P` reads every old cell by `P` and
every new cell by the agreement height of `P` and its profile in the cut grid. -/
noncomputable def rows (J : ℕ) : MultiRows I (mult I N J) := fun k i z ↦
  if hz : (z : ℕ) < I.amalgam.card then entry I N ((k : ℕ) + 1) i ⟨z, hz⟩
  else agreementHeight (cutGrid N) (entry I N ((k : ℕ) + 1) i) (cellProfile I N J z)

/-- **The profile scheme with top layer `J`**: the amalgam followed by one new cell at
`(univ, j)` per entry of the catalogue at the grade `j`, for `1 ≤ j ≤ min J 4`, with the rows
`rows I N J`. -/
noncomputable abbrev profileScheme (J : ℕ) : Scheme.{u} 5 :=
  multiLayerScheme I (mult I N J) (rows I N J)

variable {I N} {J : ℕ}

/-- There are new cells of grade `k + 1` only for `k < J`. -/
theorem lt_of_lt_mult {k : Fin 4} (i : Fin (mult I N J k)) : (k : ℕ) < J := by
  by_contra h
  have := i.isLt
  simp [mult, h] at this

/-- For `k < J`, the multiplicity at `(univ, k + 1)` is the size of the catalogue there. -/
theorem mult_of_lt {k : Fin 4} (hk : (k : ℕ) < J) :
    mult I N J k = (catalogue I N ((k : ℕ) + 1)).card := by
  unfold mult; exact ite_eq_left hk

/-- The index of a new cell is below the size of its catalogue. -/
theorem lt_card_of_lt_mult {k : Fin 4} (i : Fin (mult I N J k)) :
    (i : ℕ) < (catalogue I N ((k : ℕ) + 1)).card :=
  mult_of_lt (lt_of_lt_mult i) ▸ i.isLt

/-- The profile of a new cell of grade `k + 1` is in the catalogue at the grade `k + 1`. -/
theorem entry_mem_of_lt_mult {k : Fin 4} (i : Fin (mult I N J k)) :
    entry I N ((k : ℕ) + 1) i ∈ catalogue I N ((k : ℕ) + 1) :=
  entry_mem (lt_card_of_lt_mult i)

/-- The new cell of grade `k + 1` with index `i` carries the entry `i` of the catalogue at the
grade `k + 1`. -/
theorem cellProfile_multiNewCell (k : Fin 4) (i : Fin (mult I N J k)) :
    cellProfile I N J (multiNewCell I (mult I N J) k i) = entry I N ((k : ℕ) + 1) i := by
  match k, i with
  | ⟨0, _⟩, i =>
    have hi : (i : ℕ) < mult I N J 0 := i.isLt
    -- The index of the new cell, as a natural number.
    change cellProfile I N J (I.amalgam.card + i) = _
    rw [cellProfile, ite_eq_left (by omega)]
    congr 1; omega
  | ⟨1, _⟩, i =>
    have hi : (i : ℕ) < mult I N J 1 := i.isLt
    -- The index of the new cell, as a natural number.
    change cellProfile I N J (I.amalgam.card + mult I N J 0 + i) = _
    rw [cellProfile, ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 1; omega
  | ⟨2, _⟩, i =>
    have hi : (i : ℕ) < mult I N J 2 := i.isLt
    -- The index of the new cell, as a natural number.
    change cellProfile I N J (I.amalgam.card + mult I N J 0 + mult I N J 1 + i) = _
    rw [cellProfile, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 1; omega
  | ⟨3, _⟩, i =>
    -- The index of the new cell, as a natural number.
    change cellProfile I N J (I.amalgam.card + mult I N J 0 + mult I N J 1 + mult I N J 2 + i) = _
    rw [cellProfile, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    congr 1; omega

/-- The value of a new cell index is at least the number of cells of the amalgam. -/
theorem le_val_multiNewCell (k : Fin 4) (i : Fin (mult I N J k)) :
    I.amalgam.card ≤ (multiNewCell I (mult I N J) k i : ℕ) := by
  match k, i with
  | ⟨0, _⟩, i => exact Nat.le_add_right _ _
  | ⟨1, _⟩, i =>
    -- The index of the new cell, as a natural number.
    change _ ≤ I.amalgam.card + mult I N J 0 + i; omega
  | ⟨2, _⟩, i =>
    -- The index of the new cell, as a natural number.
    change _ ≤ I.amalgam.card + mult I N J 0 + mult I N J 1 + i; omega
  | ⟨3, _⟩, i =>
    -- The index of the new cell, as a natural number.
    change _ ≤ I.amalgam.card + mult I N J 0 + mult I N J 1 + mult I N J 2 + i; omega

/-- **The row of a new cell at an old cell** is its profile there. -/
theorem rows_multiOldCell (k : Fin 4) (i : ℕ) (d : Fin I.amalgam.card) :
    rows I N J k i (multiOldCell I (mult I N J) d) = entry I N ((k : ℕ) + 1) i d := by
  rw [rows, dite_eq_left (show (multiOldCell I (mult I N J) d : ℕ) < I.amalgam.card from d.isLt)]
  rfl

/-- **The row of a new cell at a new cell** is the agreement height of their profiles in the cut
grid. -/
theorem rows_multiNewCell (k : Fin 4) (i : ℕ) (k' : Fin 4) (i' : Fin (mult I N J k')) :
    rows I N J k i (multiNewCell I (mult I N J) k' i') =
      agreementHeight (cutGrid N) (entry I N ((k : ℕ) + 1) i) (entry I N ((k' : ℕ) + 1) i') := by
  rw [rows, dite_eq_right (fun h ↦ absurd h (not_lt.mpr (le_val_multiNewCell k' i'))),
    cellProfile_multiNewCell]

/-! ### Field labellings -/

variable (I N J) in
/-- The **field labelling** of `L` and `P`: `L` at the old cells, and at a new cell the agreement
height of `P` and its profile in the cut grid. -/
noncomputable def fieldLabelling (L P : Profile I) (z : Fin (multiCard I (mult I N J))) :
    Label.{u} :=
  if hz : (z : ℕ) < I.amalgam.card then L ⟨z, hz⟩
  else agreementHeight (cutGrid N) P (cellProfile I N J z)

/-- The field labelling at an old cell. -/
theorem fieldLabelling_multiOldCell (L P : Profile I) (d : Fin I.amalgam.card) :
    fieldLabelling I N J L P (multiOldCell I (mult I N J) d) = L d := by
  rw [fieldLabelling,
    dite_eq_left (show (multiOldCell I (mult I N J) d : ℕ) < I.amalgam.card from d.isLt)]
  rfl

/-- The field labelling at a new cell: the agreement height of `P` and its profile. -/
theorem fieldLabelling_multiNewCell (L P : Profile I) (k : Fin 4) (i : Fin (mult I N J k)) :
    fieldLabelling I N J L P (multiNewCell I (mult I N J) k i) =
      agreementHeight (cutGrid N) P (entry I N ((k : ℕ) + 1) i) := by
  rw [fieldLabelling, dite_eq_right (fun h ↦ absurd h (not_lt.mpr (le_val_multiNewCell k i))),
    cellProfile_multiNewCell]

/-- The members of the cut grid are at most its ceiling `ω * (N + 1) + 3`. -/
theorem agreementHeight_le_ceiling (P Q : Profile I) :
    agreementHeight (cutGrid N) P Q ≤ gridPoint 3 (N + 1) :=
  le_gridPoint_of_mem_grid (agreementHeight_spec (bot_mem_grid 3 _) P Q).1

/-- A profile has the ceiling of the cut grid as agreement height with itself. -/
theorem agreementHeight_self_eq (P : Profile I) :
    agreementHeight (cutGrid N) P P = gridPoint 3 (N + 1) :=
  agreementHeight_self (gridPoint_mem_grid le_rfl) (fun _ hx ↦ le_gridPoint_of_mem_grid hx) P

/-- **The field labelling is lawful below `(univ, 3)`.**  Let `L` be lawful below `(C, 3)` and
`(D, 3)`, at most the ceiling of the cut grid, and equal to `P` at the cells of grade at most
`J`, and let `P` be an entry of the catalogue at every grade `1 ≤ j ≤ J`.  The row of the new
cell of a profile `P'` reads by `P'` and the field labelling reads by `P`: the two agree capped at
the agreement height of `P` and `P'`, the label of that cell, at the old cells by its definition
and at the new cells by the ultrametric inequality
(`Label.agreementHeight_tri`); availability into `(univ, j)` is given by the cell of `P`, whose
label is the ceiling. -/
theorem isLawfulBelow_fieldLabelling {L P : Profile I}
    (hLC : I.amalgam.rows.IsLawfulBelow (coatomC, 3) fun d ↦ L d)
    (hLD : I.amalgam.rows.IsLawfulBelow (coatomD, 3) fun d ↦ L d)
    (hLP : ∀ d, I.amalgam.toCellScheme.grade d ≤ J → L d = P d)
    (hL : ∀ d, L d ≤ gridPoint 3 (N + 1))
    (hP : ∀ j, 1 ≤ j → j ≤ J → P ∈ catalogue I N j) :
    (profileScheme I N J).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
      fun z ↦ fieldLabelling I N J L P z := by
  classical
  have hold (B : Finset (Fin 5)) (hB : B ≠ univ)
      (hLB : I.amalgam.rows.IsLawfulBelow (B, 3) fun d ↦ L d) :
      (profileScheme I N J).rows.IsLawfulBelow (B, 3) fun z ↦ fieldLabelling I N J L P z := by
    refine (isLawfulBelow_multiOldCell_iff hB).mpr ?_
    simpa only [fieldLabelling_multiOldCell] using hLB
  obtain ⟨hoC, hlC, haC⟩ := Rows.isLawfulBelow_iff_forall.mp (hold coatomC (by decide) hLC)
  obtain ⟨hoD, hlD, haD⟩ := Rows.isLawfulBelow_iff_forall.mp (hold coatomD (by decide) hLD)
  have hceil (z : Fin (multiCard I (mult I N J))) :
      fieldLabelling I N J L P z ≤ gridPoint 3 (N + 1) := by
    rcases multiCell_cases (r := rows I N J) z with ⟨d, rfl⟩ | ⟨k, i, rfl⟩
    · rw [fieldLabelling_multiOldCell]; exact hL d
    · rw [fieldLabelling_multiNewCell]; exact agreementHeight_le_ceiling _ _
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun z hz ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · rcases multiCell_cases (r := rows I N J) z with ⟨d, rfl⟩ | ⟨k, i, rfl⟩
    · rcases mem_below_coatom_of_ne_multi hz (scope_multiOldCell_ne d) with h | h
      exacts [hoC _ h, hoD _ h]
    · rw [fieldLabelling_multiNewCell]
      exact (isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid 3 _) _ _).1).mono hz.2
  · rcases multiCell_cases (r := rows I N J) s with ⟨d, rfl⟩ | ⟨k, i, rfl⟩
    · rcases mem_below_coatom_of_ne_multi hs (scope_multiOldCell_ne d) with h | h
      exacts [hlC _ h, hlD _ h]
    · have hkJ := lt_of_lt_mult i
      have hκv : IsSelfVisible ((k : ℕ) + 1)
          (agreementHeight (cutGrid N) P (entry I N ((k : ℕ) + 1) i)) :=
        (isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid 3 _) _ _).1).mono
          (by have := hs.2; rw [gradedIndex_multiNewCell] at this; exact this)
      refine ⟨constStepSuppressor ((k : ℕ) + 1) _, id,
        ⟨antitone_constStepSuppressor _ _, isSelfVisible_constStepSuppressor hκv, rfl,
          monotone_id, fun _ _ _ _ _ ↦ rfl⟩, fun t ↦ ?_⟩
      have htk : (profileScheme I N J).toCellScheme.grade t ≤ (k : ℕ) + 1 :=
        t.2.2.trans_eq (congrArg Prod.snd (gradedIndex_multiNewCell (r := rows I N J) k i))
      rw [row_multiNewCell, constStepSuppressor_of_le _ htk, id]
      obtain ⟨t, ht⟩ := t
      -- Beta-reduce the capped target at the cell `t`.
      dsimp only
      rw [fieldLabelling_multiNewCell]
      rcases multiCell_cases (r := rows I N J) t with ⟨d, rfl⟩ | ⟨k', i', rfl⟩
      · rw [grade_multiOldCell] at htk
        rw [fieldLabelling_multiOldCell, rows_multiOldCell, hLP d (by omega)]
        exact (agreementHeight_spec (bot_mem_grid 3 _) _ _).2 d
      · rw [fieldLabelling_multiNewCell, rows_multiNewCell]
        exact agreementHeight_tri (bot_mem_grid 3 _) _ _ _
  · rcases multiCell_cases (r := rows I N J) t with ⟨d, rfl⟩ | ⟨k, i, rfl⟩
    · rcases mem_below_coatom_of_ne_multi ht (scope_multiOldCell_ne d) with h | h
      exacts [haC s _ h hst hg, haD s _ h hst hg]
    · have hkJ := lt_of_lt_mult i
      obtain ⟨i', hi', he⟩ := exists_entry_eq (hP ((k : ℕ) + 1) (by omega) (by omega))
      have hi'm : i' < mult I N J k := by rwa [mult_of_lt hkJ]
      refine ⟨multiNewCell I (mult I N J) k ⟨i', hi'm⟩, by
        rw [gradedIndex_multiNewCell, gradedIndex_multiNewCell], ?_⟩
      rw [fieldLabelling_multiNewCell]
      -- The profile of the cell `u` is the entry `i'`.
      change _ ≤ agreementHeight (cutGrid N) P (entry I N ((k : ℕ) + 1) i')
      rw [he, agreementHeight_self_eq]
      exact hceil s

/-! ### Grid points -/

/-- Grid points compare lexicographically in block and grade. -/
theorem gridPoint_le_gridPoint_iff {k k' b b' : ℕ} :
    gridPoint.{u} k b ≤ gridPoint k' b' ↔ b < b' ∨ b = b' ∧ k ≤ k' := by
  rw [gridPoint, gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe,
    omega0_mul_add_natCast_le_iff]
  simp only [Nat.cast_lt, Nat.cast_inj]

/-- Grid points compare strictly lexicographically in block and grade. -/
theorem gridPoint_lt_gridPoint_iff {k k' b b' : ℕ} :
    gridPoint.{u} k b < gridPoint k' b' ↔ b < b' ∨ b = b' ∧ k < k' := by
  rw [lt_iff_not_ge, gridPoint_le_gridPoint_iff]
  omega

/-- A grid point of grade `1` is fixed by the visibility replacement at the threshold `3` with
value `1`. -/
theorem visibilityReplace_three_one_gridPoint (b : ℕ) :
    visibilityReplace 3 1 (gridPoint.{u} 1 b) = gridPoint 1 b := by
  rw [gridPoint, visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast]
  simp

/-! ### The seeds of `TL` and `T5`: the test -/

section Test

open TwoFaceLiftExistsCounterexample (TL VisibilityReplaceFixedOfLT exists_cell_TL
  le_of_isLawfulBelow_right)
open CaseSplitCounterexample (T5 tripleLabelling tripleKind liveG liveG_three)

variable (I) in
/-- The **profile of five parameters**: `tripleLabelling AC FC AD FD G` read at the graded
indices of the amalgam, that is `A_C`, `F_C` at the live cells of grade `1`, `2` of `C`, `A_D`,
`F_D` at those of `D`, `G` at the live cells of grade `3`, and `⊥` elsewhere. -/
noncomputable def tripleProfile (AC FC AD FD G : Label.{u}) : Profile I :=
  fun d ↦ tripleLabelling AC FC AD FD G (I.amalgam.toCellScheme.gradedIndex d)

/-- A profile of five parameters at a cell. -/
theorem tripleProfile_apply (AC FC AD FD G : Label.{u}) (d : Fin I.amalgam.card) :
    tripleProfile I AC FC AD FD G d =
      tripleLabelling AC FC AD FD G (I.amalgam.toCellScheme.gradedIndex d) := rfl

/-- `tripleLabelling` at a graded index of a given kind. -/
theorem tripleLabelling_of_kind {AC FC AD FD G : Label.{u}} {X : Finset (Fin 5) × ℕ} {c : Fin 6}
    (h : tripleKind X = c) : tripleLabelling AC FC AD FD G X = ![⊥, AC, FC, AD, FD, G] c := by
  rw [tripleLabelling, h]

/-- The live graded indices of the first coatom have grade `1` or `2`. -/
private theorem liveC_snd : ∀ Y ∈ TwoFaceLiftCounterexample.liveC, Y.2 = 1 ∨ Y.2 = 2 := by decide

/-- The live graded indices of the second coatom have grade `1` or `2`. -/
private theorem liveD_snd : ∀ Y ∈ TwoFaceLiftCounterexample.liveD, Y.2 = 1 ∨ Y.2 = 2 := by decide

/-- The kinds of `tripleKind` have the grades of their parameters. -/
theorem snd_of_tripleKind (X : Finset (Fin 5) × ℕ) :
    (tripleKind X = 1 ∨ tripleKind X = 3 → X.2 = 1) ∧
      (tripleKind X = 2 ∨ tripleKind X = 4 → X.2 = 2) ∧ (tripleKind X = 5 → X.2 = 3) := by
  unfold tripleKind
  by_cases hC : X ∈ TwoFaceLiftCounterexample.liveC
  · rcases liveC_snd X hC with h | h <;> simp [hC, h]
  · by_cases hD : X ∈ TwoFaceLiftCounterexample.liveD
    · rcases liveD_snd X hD with h | h <;> simp [hC, hD, h]
    · by_cases hG : X ∈ liveG
      · simp [hC, hD, hG, liveG_three X hG]
      · simp [hC, hD, hG]

/-- A profile of five parameters is normalized when its parameters are. -/
theorem isNormalized_tripleProfile {AC FC AD FD G : Label.{u}} (hAC : AC ∈ grid 1 N)
    (hFC : FC ∈ grid 2 N) (hAD : AD ∈ grid 1 N) (hFD : FD ∈ grid 2 N) (hG : G ∈ grid 3 N) :
    IsNormalized I N (tripleProfile I AC FC AD FD G) := by
  intro d
  obtain ⟨h13, h24, h5⟩ := snd_of_tripleKind (I.amalgam.toCellScheme.gradedIndex d)
  -- The grade of `d` is the second component of its graded index.
  change tripleLabelling AC FC AD FD G (I.amalgam.toCellScheme.gradedIndex d) ∈
    grid (I.amalgam.toCellScheme.gradedIndex d).2 N
  unfold tripleLabelling
  generalize tripleKind (I.amalgam.toCellScheme.gradedIndex d) = c at h13 h24 h5
  fin_cases c <;> simp_all [bot_mem_grid]

/-! #### The parameters of the test -/

/-- The value `ω + 1` of the tie profile at the live cells of grade `1` of both coatoms. -/
noncomputable abbrev tieA : Label.{u} := gridPoint 1 1

/-- The value `ω + 2` of the tie profile at the live cells of grade `2`. -/
noncomputable abbrev tieF : Label.{u} := gridPoint 2 1

/-- The value `3` of the tie profile at the live cells of grade `3`. -/
noncomputable abbrev tieG : Label.{u} := gridPoint 3 0

/-- The cap `4`, strictly between the largest agreement height `3` of the tie profile with a
profile that separates `({3}, 1)` and `({4}, 1)` and the value `ω + 1` of the tie profile there. -/
noncomputable abbrev capFour : Label.{u} := gridPoint 4 0

variable (I) in
/-- The **tie profile**: `ω + 1` at the live cells of grade `1` of both coatoms (so it reads
`({3}, 1)` and `({4}, 1)` alike), `ω + 2` at those of grade `2`, `3` at those of grade `3`. -/
noncomputable abbrev tieProfile : Profile I := tripleProfile I tieA tieF tieA tieF tieG

variable (I) in
/-- The old labels of the ambient labelling at the top layer `2`: the tie profile, except `4` at
the live cells of grade `3`. -/
noncomputable abbrev twoOld : Profile I := tripleProfile I tieA tieF tieA tieF capFour

variable (I N) in
/-- **The prescription `(A, ⊤, ⊤)` on `C`**: `A` at the live cells of grade `1` of `C` and `⊤` at
the other live cells, read at the graded indices of the profile scheme with top layer `J`. -/
noncomputable def prescription (J : ℕ) (A : Label.{u}) (z : Fin (profileScheme I N J).card) :
    Label.{u} :=
  tripleLabelling A ⊤ ⊤ ⊤ ⊤ ((profileScheme I N J).toCellScheme.gradedIndex z)

/-- The prescription at an old cell. -/
theorem prescription_multiOldCell (A : Label.{u}) (d : Fin I.amalgam.card) :
    prescription I N J A (multiOldCell I (mult I N J) d) =
      tripleLabelling A ⊤ ⊤ ⊤ ⊤ (I.amalgam.toCellScheme.gradedIndex d) := by
  rw [prescription, gradedIndex_multiOldCell]

/-- The old labels of the ambient labelling at the top layer `2` lie below the ceiling. -/
theorem twoOld_le (hN : 1 ≤ N) (d : Fin I.amalgam.card) : twoOld I d ≤ gridPoint 3 (N + 1) := by
  -- The old label at `d` is `tripleLabelling` at the graded index of `d`.
  change tripleLabelling tieA tieF tieA tieF capFour (I.amalgam.toCellScheme.gradedIndex d) ≤ _
  unfold tripleLabelling
  generalize tripleKind _ = c
  fin_cases c <;> simp [gridPoint_le_gridPoint_iff] <;> omega

/-- The tie profile lies below every grid point of grade `3` past the block `0`. -/
theorem tieProfile_lt {b : ℕ} (hb : 1 ≤ b) (d : Fin I.amalgam.card) :
    tieProfile I d < gridPoint 3 b := by
  -- The tie profile at `d` is `tripleLabelling` at the graded index of `d`.
  change tripleLabelling tieA tieF tieA tieF tieG (I.amalgam.toCellScheme.gradedIndex d) < _
  unfold tripleLabelling
  generalize tripleKind _ = c
  fin_cases c <;> simp [bot_lt_iff_ne_bot, gridPoint_ne_bot, gridPoint_lt_gridPoint_iff] <;> omega

/-- **The agreement cut below the cap.**  A profile other than the tie profile has agreement
height with it at most `3`, below the cap `4`: an agreement height at least `4` is a grid point
`ω * b + 3` with `b ≥ 1`, above every value of the tie profile, at which the agreement is
equality. -/
theorem agreementHeight_tie_lt_capFour {Q : Profile I} (hQ : Q ≠ tieProfile I) :
    agreementHeight (cutGrid N) (tieProfile I) Q < capFour := by
  by_contra hge
  rw [not_lt] at hge
  obtain ⟨hmem, hag⟩ := agreementHeight_spec (bot_mem_grid 3 (N + 1)) (tieProfile I) Q
  rcases mem_grid.mp hmem with h0 | ⟨b, -, hb⟩
  · rw [h0] at hge; exact gridPoint_ne_bot 4 0 (le_bot_iff.mp hge)
  · rw [hb, gridPoint_le_gridPoint_iff] at hge
    refine hQ (funext fun d ↦ eq_of_min_eq_of_lt (hag d) ?_)
    rw [hb]; exact tieProfile_lt (by omega) d

/-- The tie profile with the value at the live cells of grade `1` of `D` raised to `ω * 2 + 1`. -/
noncomputable abbrev raisedProfile : Profile I :=
  tripleProfile I tieA tieF (gridPoint 1 2) tieF tieG

/-- The profile of the cells of full scope that read `({3}, 1)` strictly below `({4}, 1)`, used for
the lift at the top layer `3`: `ω + 1` at the live cells of grade `1` of `C`, `ω * 3 + 1`,
`ω * 3 + 2` at the other live cells of grade `1` and `2`, and `ω * 2 + 3` at those of grade `3`. -/
noncomputable abbrev liftProfile : Profile I :=
  tripleProfile I tieA (gridPoint 2 3) (gridPoint 1 3) (gridPoint 2 3) (gridPoint 3 2)

/-- The start `ω * 2` of the block `2`, the threshold of the reduction in the lift. -/
noncomputable abbrev blockTwo : Ordinal.{u} := ω * ((2 : ℕ) : Ordinal.{u})

/-- The start `ω * 2` of the block `2` is a limit. -/
theorem isSuccPrelimit_blockTwo : Order.IsSuccPrelimit blockTwo.{u} :=
  Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _)

/-- The grid points of the blocks `0` and `1` lie below `ω * 2`. -/
theorem gridPoint_lt_blockTwo {k b : ℕ} (hb : b < 2) :
    gridPoint.{u} k b < (blockTwo : Label.{u}) := by
  rw [gridPoint, WithBot.coe_lt_coe, WithTop.coe_lt_coe, blockTwo]
  simpa using omega0_mul_add_natCast_lt (Nat.cast_lt.mpr hb) k 0

/-- The grid points of the blocks from `2` on lie at or above `ω * 2`. -/
theorem blockTwo_le_gridPoint {k b : ℕ} (hb : 2 ≤ b) : (blockTwo : Label.{u}) ≤ gridPoint k b := by
  rw [gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe, blockTwo]
  exact (mul_le_mul_right (Nat.cast_le.mpr hb) ω).trans le_self_add

/-- The reduction to the block `2` keeps a label capped at `3`. -/
theorem min_reduce_tieG (x : Label.{u}) : min (reduce blockTwo x) tieG = min x tieG := by
  by_cases hx : x < (blockTwo : Label.{u})
  · rw [reduce_of_lt hx]
  · rw [reduce_of_le (not_lt.mp hx), min_top_left, min_eq_right]
    exact ((gridPoint_lt_blockTwo (by omega)).trans_le (not_lt.mp hx)).le

/-- The reduction to the block `2` is a witness bounded by the grade `3`. -/
theorem isWitness_reduce_blockTwo : IsWitness (stepSuppressor.{u} 3) (reduce blockTwo) :=
  ⟨(IsWitness.id_step 3).antitone, (IsWitness.id_step 3).isSelfVisible, reduce_bot,
    monotone_reduce _, fun x k _ i _ ↦ reduce_visibilityReplace isSuccPrelimit_blockTwo k i x⟩

/-- **The ambient labelling at the top layer `2` agrees with the prescription capped at `4`**
below `(C, 3)`: they differ only at live cells where both are at least `4`. -/
theorem min_ambientTwo_eq (z : (profileScheme I N 2).toCellScheme.below (coatomC, 3)) :
    min (fieldLabelling I N 2 (twoOld I) (tieProfile I) z) capFour =
      min (prescription I N 2 tieA z) capFour := by
  obtain ⟨d, hd⟩ := exists_eq_multiOldCell (r := rows I N 2) (z := z.1) fun h ↦ by
    have h1 : (profileScheme I N 2).toCellScheme.scope z.1 ⊆ coatomC := z.2.1
    rw [h] at h1
    exact absurd h1 (by decide)
  rw [hd, fieldLabelling_multiOldCell, prescription_multiOldCell]
  -- The old label at `d` is `tripleLabelling` at the graded index of `d`.
  change min (tripleLabelling tieA tieF tieA tieF capFour (I.amalgam.toCellScheme.gradedIndex d))
    capFour = _
  unfold tripleLabelling
  generalize tripleKind _ = c
  fin_cases c <;> simp [gridPoint_le_gridPoint_iff]

/-- The tie profile lies below the ceiling of the cut grid. -/
theorem tieProfile_le (d : Fin I.amalgam.card) : tieProfile I d ≤ gridPoint 3 (N + 1) :=
  (tieProfile_lt (by omega) d).le

/-- The lift profile lies below the ceiling of the cut grid, for `N ≥ 3`. -/
theorem liftProfile_le (hN : 3 ≤ N) (d : Fin I.amalgam.card) :
    liftProfile (I := I) d ≤ gridPoint 3 (N + 1) := by
  -- The lift profile at `d` is `tripleLabelling` at the graded index of `d`.
  change tripleLabelling tieA (gridPoint 2 3) (gridPoint 1 3) (gridPoint 2 3) (gridPoint 3 2)
    (I.amalgam.toCellScheme.gradedIndex d) ≤ _
  unfold tripleLabelling
  generalize tripleKind _ = c
  fin_cases c <;> simp [gridPoint_le_gridPoint_iff] <;> omega

/-- The lift profile and the tie profile agree capped at `3`. -/
theorem min_liftProfile_eq (d : Fin I.amalgam.card) :
    min (liftProfile (I := I) d) tieG = min (tieProfile I d) tieG := by
  -- Both profiles at `d` are `tripleLabelling` at the graded index of `d`.
  change min (tripleLabelling tieA (gridPoint 2 3) (gridPoint 1 3) (gridPoint 2 3) (gridPoint 3 2)
    (I.amalgam.toCellScheme.gradedIndex d)) tieG =
      min (tripleLabelling tieA tieF tieA tieF tieG (I.amalgam.toCellScheme.gradedIndex d)) tieG
  unfold tripleLabelling
  generalize tripleKind _ = c
  fin_cases c <;> simp [gridPoint_le_gridPoint_iff]

/-- The raised profile and the tie profile agree capped at `3`. -/
theorem min_raisedProfile_eq (d : Fin I.amalgam.card) :
    min (raisedProfile (I := I) d) tieG = min (tieProfile I d) tieG := by
  -- Both profiles at `d` are `tripleLabelling` at the graded index of `d`.
  change min (tripleLabelling tieA tieF (gridPoint 1 2) tieF tieG
    (I.amalgam.toCellScheme.gradedIndex d)) tieG =
      min (tripleLabelling tieA tieF tieA tieF tieG (I.amalgam.toCellScheme.gradedIndex d)) tieG
  unfold tripleLabelling
  generalize tripleKind _ = c
  fin_cases c <;> simp [gridPoint_le_gridPoint_iff]

/-- The reduction to the block `2` sends the lift profile to the prescription. -/
theorem reduce_liftProfile (d : Fin I.amalgam.card) :
    reduce blockTwo (liftProfile (I := I) d) =
      tripleLabelling tieA ⊤ ⊤ ⊤ ⊤ (I.amalgam.toCellScheme.gradedIndex d) := by
  -- The lift profile at `d` is `tripleLabelling` at the graded index of `d`.
  change reduce blockTwo (tripleLabelling tieA (gridPoint 2 3) (gridPoint 1 3) (gridPoint 2 3)
    (gridPoint 3 2) (I.amalgam.toCellScheme.gradedIndex d)) = _
  unfold tripleLabelling
  generalize tripleKind _ = c
  fin_cases c
  · exact reduce_bot
  · exact reduce_of_lt (gridPoint_lt_blockTwo (by omega))
  all_goals exact reduce_of_le (blockTwo_le_gridPoint (by omega))

/-- **The ambient labelling at the top layer `3` agrees with the prescription capped at `3`**
below `(C, 3)`. -/
theorem min_ambientThree_eq (z : (profileScheme I N 3).toCellScheme.below (coatomC, 3)) :
    min (fieldLabelling I N 3 (tieProfile I) (tieProfile I) z) tieG =
      min (prescription I N 3 tieA z) tieG := by
  obtain ⟨d, hd⟩ := exists_eq_multiOldCell (r := rows I N 3) (z := z.1) fun h ↦ by
    have h1 : (profileScheme I N 3).toCellScheme.scope z.1 ⊆ coatomC := z.2.1
    rw [h] at h1
    exact absurd h1 (by decide)
  rw [hd, fieldLabelling_multiOldCell, prescription_multiOldCell]
  -- The tie profile at `d` is `tripleLabelling` at the graded index of `d`.
  change min (tripleLabelling tieA tieF tieA tieF tieG (I.amalgam.toCellScheme.gradedIndex d))
    tieG = _
  unfold tripleLabelling
  generalize tripleKind _ = c
  fin_cases c <;> simp [gridPoint_le_gridPoint_iff]

variable (I) in
/-- The **top profile** at the inventory bound `N`: `ω * N + 1` at the live cells of grade `1` of
both coatoms, the largest normalized value there, `ω * N + 2` at those of grade `2`, and
`ω * (N - 1) + 3` at those of grade `3`, the largest normalized value below `ω * N + 1`. -/
noncomputable abbrev topProfile (N : ℕ) : Profile I :=
  tripleProfile I (gridPoint 1 N) (gridPoint 2 N) (gridPoint 1 N) (gridPoint 2 N)
    (gridPoint 3 (N - 1))

/-- The top profile lies below the ceiling of the cut grid. -/
theorem topProfile_le (d : Fin I.amalgam.card) : topProfile I N d ≤ gridPoint 3 (N + 1) := by
  -- The top profile at `d` is `tripleLabelling` at the graded index of `d`.
  change tripleLabelling (gridPoint 1 N) (gridPoint 2 N) (gridPoint 1 N) (gridPoint 2 N)
    (gridPoint 3 (N - 1)) (I.amalgam.toCellScheme.gradedIndex d) ≤ _
  unfold tripleLabelling
  generalize tripleKind _ = c
  fin_cases c <;> simp [gridPoint_le_gridPoint_iff]

/-- **The ambient labelling of the top profile agrees with the prescription `(ω * N + 1, ⊤, ⊤)`
capped at `ω * (N - 1) + 3`** below `(C, 3)`. -/
theorem min_ambientTop_eq (hN : 1 ≤ N)
    (z : (profileScheme I N 3).toCellScheme.below (coatomC, 3)) :
    min (fieldLabelling I N 3 (topProfile I N) (topProfile I N) z) (gridPoint 3 (N - 1)) =
      min (prescription I N 3 (gridPoint 1 N) z) (gridPoint 3 (N - 1)) := by
  obtain ⟨d, hd⟩ := exists_eq_multiOldCell (r := rows I N 3) (z := z.1) fun h ↦ by
    have h1 : (profileScheme I N 3).toCellScheme.scope z.1 ⊆ coatomC := z.2.1
    rw [h] at h1
    exact absurd h1 (by decide)
  rw [hd, fieldLabelling_multiOldCell, prescription_multiOldCell]
  -- The top profile at `d` is `tripleLabelling` at the graded index of `d`.
  change min (tripleLabelling (gridPoint 1 N) (gridPoint 2 N) (gridPoint 1 N) (gridPoint 2 N)
    (gridPoint 3 (N - 1)) (I.amalgam.toCellScheme.gradedIndex d)) (gridPoint 3 (N - 1)) = _
  unfold tripleLabelling
  generalize tripleKind _ = c
  have h₁ : gridPoint.{u} 3 (N - 1) ≤ gridPoint 1 N := gridPoint_le_gridPoint_iff.mpr (by omega)
  have h₂ : gridPoint.{u} 3 (N - 1) ≤ gridPoint 2 N := gridPoint_le_gridPoint_iff.mpr (by omega)
  fin_cases c <;> simp [min_eq_right h₁, min_eq_right h₂]

/-- **The agreement cut below the top cap.**  A normalized profile `Q` reading `({3}, 1)` strictly
below `({4}, 1)` has agreement height with the top profile below `ω * (N - 1) + 3`: an agreement
height at least `ω * (N - 1) + 3` either lies above `ω * N + 1`, and then `Q` is `ω * N + 1` at both
cells, or is `ω * (N - 1) + 3` itself, and then `Q` at `({3}, 1)` is a normalized value of grade `1`
at least `ω * (N - 1) + 3`, which is `ω * N + 1`, the largest one. -/
theorem agreementHeight_top_lt (hN : 1 ≤ N) {Q : Profile I} (hQ : IsNormalized I N Q)
    {d₁ d₂ : Fin I.amalgam.card}
    (hd₁ : I.amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1))
    (hd₂ : I.amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1))
    (hsep : Q d₁ < Q d₂) :
    agreementHeight (cutGrid N) (topProfile I N) Q < gridPoint 3 (N - 1) := by
  obtain ⟨hmem, hag⟩ := agreementHeight_spec (bot_mem_grid 3 (N + 1)) (topProfile I N) Q
  have ht₁ : topProfile I N d₁ = gridPoint 1 N := by
    rw [topProfile, tripleProfile_apply, hd₁, tripleLabelling_of_kind (c := 1) (by decide)]; rfl
  have ht₂ : topProfile I N d₂ = gridPoint 1 N := by
    rw [topProfile, tripleProfile_apply, hd₂, tripleLabelling_of_kind (c := 3) (by decide)]; rfl
  have hQ₁ : Q d₁ ∈ grid 1 N := by
    have := hQ d₁; rwa [show I.amalgam.toCellScheme.grade d₁ = 1 from congrArg Prod.snd hd₁] at this
  have hQ₂ : Q d₂ ∈ grid 1 N := by
    have := hQ d₂; rwa [show I.amalgam.toCellScheme.grade d₂ = 1 from congrArg Prod.snd hd₂] at this
  by_contra hge
  rw [not_lt] at hge
  by_cases hlt : gridPoint 1 N < agreementHeight (cutGrid N) (topProfile I N) Q
  · have e₁ := eq_of_min_eq_of_lt (hag d₁) (ht₁ ▸ hlt)
    have e₂ := eq_of_min_eq_of_lt (hag d₂) (ht₂ ▸ hlt)
    rw [e₁, e₂, ht₁, ht₂] at hsep
    exact lt_irrefl _ hsep
  · rw [not_lt] at hlt
    have h₁ := hag d₁
    rw [ht₁, min_eq_right hlt] at h₁
    have hcQ := min_eq_right_iff.mp h₁.symm
    rcases mem_grid.mp hmem with h0 | ⟨b, -, hb⟩
    · rw [h0] at hge; exact gridPoint_ne_bot 3 (N - 1) (le_bot_iff.mp hge)
    rcases mem_grid.mp hQ₁ with h0 | ⟨b₁, hb₁, hb₁e⟩
    · rw [h0, hb] at hcQ; exact gridPoint_ne_bot 3 b (le_bot_iff.mp hcQ)
    rw [hb, gridPoint_le_gridPoint_iff] at hge
    rw [hb, hb₁e, gridPoint_le_gridPoint_iff] at hcQ
    have hN₁ : b₁ = N := by omega
    rw [hb₁e, hN₁] at hsep
    exact absurd (hsep.trans_le (le_gridPoint_of_mem_grid hQ₂)) (lt_irrefl _)

section Seeds

variable (hIL : I.left = TL α) (hIR : I.right = T5 α)
include hIL hIR

/-- **A profile of five parameters is in the catalogue at the grades `j ≤ 3`** when its parameters
are normalized and satisfy the couplings of `TL` (`G ≤ F_C`, `VisibilityReplaceFixedOfLT A_C G`)
and of `T5` (`G ≤ A_D`, `G ≤ F_D`). -/
theorem tripleProfile_mem_catalogue {j : ℕ} (hj : j ≤ 3) {AC FC AD FD G : Label.{u}}
    (hAC : AC ∈ grid 1 N) (hFC : FC ∈ grid 2 N) (hAD : AD ∈ grid 1 N) (hFD : FD ∈ grid 2 N)
    (hG : G ∈ grid 3 N) (hGFC : G ≤ FC) (hcC : VisibilityReplaceFixedOfLT AC G) (hGAD : G ≤ AD)
    (hGFD : G ≤ FD) : tripleProfile I AC FC AD FD G ∈ catalogue I N j := by
  obtain ⟨hC, hD⟩ := TwoFaceLiftExistsCounterexample.isLawfulBelow_tripleLabelling hIL hIR
    (isSelfVisible_of_mem_grid hAC) (isSelfVisible_of_mem_grid hFC)
    (isSelfVisible_of_mem_grid hAD) (isSelfVisible_of_mem_grid hFD)
    (isSelfVisible_of_mem_grid hG) hGFC hcC hGAD hGFD
  exact mem_catalogue.mpr ⟨isNormalized_tripleProfile hAC hFC hAD hFD hG,
    hC.mono (X := (coatomC, j)) ⟨subset_rfl, hj⟩, hD.mono (X := (coatomD, j)) ⟨subset_rfl, hj⟩⟩

/-- The tie profile is in the catalogue at the grades `j ≤ 3`. -/
theorem tieProfile_mem_catalogue (hN : 1 ≤ N) {j : ℕ} (hj : j ≤ 3) :
    tieProfile I ∈ catalogue I N j :=
  tripleProfile_mem_catalogue hIL hIR hj (gridPoint_mem_grid hN) (gridPoint_mem_grid hN)
    (gridPoint_mem_grid hN) (gridPoint_mem_grid hN) (gridPoint_mem_grid (Nat.zero_le N))
    (gridPoint_le_gridPoint_iff.mpr (by omega))
    (fun _ ↦ visibilityReplace_three_one_gridPoint 1)
    (gridPoint_le_gridPoint_iff.mpr (by omega)) (gridPoint_le_gridPoint_iff.mpr (by omega))

/-- The cells `({3}, 1)`, `({0, 1, 2, 3}, 2)`, `({0, 1, 2}, 3)` and `({4}, 1)` of the amalgam. -/
theorem exists_test_cells : ∃ d₁ sC gE d₂ : Fin I.amalgam.card,
    I.amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1) ∧
      I.amalgam.toCellScheme.gradedIndex sC = (({0, 1, 2, 3} : Finset (Fin 5)), 2) ∧
      I.amalgam.toCellScheme.gradedIndex gE = (({0, 1, 2} : Finset (Fin 5)), 3) ∧
      I.amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1) := by
  obtain ⟨d₁, h₁⟩ := exists_cell_TL (hIL ▸ I.restrictFace_left) 3
  obtain ⟨sC, hs⟩ := exists_cell_TL (hIL ▸ I.restrictFace_left) 15
  obtain ⟨gE, hg⟩ := exists_cell_TL (hIL ▸ I.restrictFace_left) 16
  obtain ⟨d₂, h₂⟩ := CaseSplitCounterexample.exists_cell (hIR ▸ I.restrictFace_right) 3
  exact ⟨d₁, sC, gE, d₂, h₁.trans (by decide +kernel), hs.trans (by decide +kernel),
    hg.trans (by decide +kernel), h₂.trans (by decide +kernel)⟩

/-- **The prescription `(ω * b + 1, ⊤, ⊤)` on `C` is lawful below `(C, 3)`**: the value
`ω * b + 1` has finite part `1`, so the coupling of `TL` holds. -/
theorem isLawfulBelow_prescription (J b : ℕ) :
    (profileScheme I N J).rows.IsLawfulBelow (coatomC, 3)
      fun z ↦ prescription I N J (gridPoint 1 b) z := by
  refine (isLawfulBelow_multiOldCell_iff (by decide)).mpr ?_
  simp only [prescription_multiOldCell]
  exact (TwoFaceLiftExistsCounterexample.isLawfulBelow_tripleLabelling hIL hIR
    (isSelfVisible_gridPoint 1 b) (isSelfVisible_top 2) (isSelfVisible_top 1)
    (isSelfVisible_top 2) (isSelfVisible_top 3) le_rfl
    (fun _ ↦ visibilityReplace_three_one_gridPoint b) le_rfl le_rfl).1

/-- **A lift at the prescription `(A, ⊤, ⊤)` reaches its cap at a new cell at `(univ, 2)` whose
profile reads `({3}, 1)` strictly below `({4}, 1)`.**  In the profile scheme with top layer
`J ≥ 2` (inventory bound `N ≥ 1`), let `w` be lawful below `(univ, 3)`, equal to the prescription
`(A, ⊤, ⊤)` below `(C, 3)` with `A ≠ ⊤`, and equal to a labelling `q` capped at `h`.  Then some new
cell at `(univ, 2)` has a profile `Q` with `Q ({3}, 1) < Q ({4}, 1)` and `h ≤ q` there.

This is the argument of `TwoFaceLiftExistsCounterexample.not_twoFaceLiftExists_two_of` (steps 4
and 5) and of `ThinCompletion.exists_separating_cell`, in the profile scheme: `w` is `⊤` at
`({0, 1, 2}, 3)`, hence at `({4}, 1)` by the coupling of `T5`, and `⊤` at
`({0, 1, 2, 3}, 2)`, hence, by availability, at a new cell `u` at `(univ, 2)`; locality at `u`
reads `({3}, 1)` (label `A`) strictly below `({4}, 1)` (label `⊤`); and `w u = ⊤` with the capped
agreement gives `h ≤ q u`. -/
theorem exists_separating_of_lift (hJ : 2 ≤ J) (hN : 1 ≤ N) {A h : Label.{u}} (hA : A ≠ ⊤)
    {q : Fin (profileScheme I N J).card → Label.{u}}
    {w : (profileScheme I N J).toCellScheme.below ((univ : Finset (Fin 5)), 3) → Label.{u}}
    (hw : (profileScheme I N J).rows.IsLawfulBelow (univ, 3) w)
    (hag : ∀ z, min (w z) h = min (q z) h)
    (hres : ∀ z : (profileScheme I N J).toCellScheme.below (coatomC, 3),
      w (Set.inclusion ((profileScheme I N J).toCellScheme.below_mono
        (show ((coatomC, 3) : Finset (Fin 5) × ℕ) ≤ (univ, 3) from ⟨subset_univ _, le_rfl⟩))
        z) = prescription I N J A z) :
    ∃ (d₁ d₂ : Fin I.amalgam.card) (i : Fin (mult I N J 1)),
      I.amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1) ∧
      I.amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1) ∧
      entry I N 2 i d₁ < entry I N 2 i d₂ ∧ h ≤ q (multiNewCell I (mult I N J) 1 i) := by
  classical
  obtain ⟨d₁, sC, gE, d₂, hd₁, hsC, hgE, hd₂⟩ := exists_test_cells hIL hIR
  have hWl := Rows.isLawfulBelow_extendBot.mpr hw
  obtain ⟨-, hloc, havail⟩ := Rows.isLawfulBelow_iff_forall.mp hWl
  set W := Rows.extendBot ((univ : Finset (Fin 5)), 3) w with hW
  have hWC (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.gradedIndex d ≤ (coatomC, 3)) :
      W (multiOldCell I (mult I N J) d) =
        tripleLabelling A ⊤ ⊤ ⊤ ⊤ (I.amalgam.toCellScheme.gradedIndex d) := by
    have hm : multiOldCell I (mult I N J) d ∈
        (profileScheme I N J).toCellScheme.below (coatomC, 3) := multiOldCell_mem_below hd
    have := hres ⟨_, hm⟩
    rw [prescription_multiOldCell] at this
    rw [hW, Rows.extendBot_of_mem w ((profileScheme I N J).toCellScheme.below_mono
      (show ((coatomC, 3) : Finset (Fin 5) × ℕ) ≤ (univ, 3) from ⟨subset_univ _, le_rfl⟩) hm)]
    exact this
  have hWd₁ : W (multiOldCell I (mult I N J) d₁) = A := by
    rw [hWC d₁ (by rw [hd₁]; decide), hd₁, tripleLabelling_of_kind (c := 1) (by decide)]; rfl
  have hWsC : W (multiOldCell I (mult I N J) sC) = ⊤ := by
    rw [hWC sC (by rw [hsC]; decide), hsC, tripleLabelling_of_kind (c := 2) (by decide)]; rfl
  have hWg : W (multiOldCell I (mult I N J) gE) = ⊤ := by
    rw [hWC gE (by rw [hgE]; decide), hgE, tripleLabelling_of_kind (c := 5) (by decide)]; rfl
  have hWd₂ : W (multiOldCell I (mult I N J) d₂) = ⊤ := by
    have hWD : I.amalgam.rows.IsLawfulBelow (coatomD, 2 + 1)
        fun d ↦ W (multiOldCell I (mult I N J) d) :=
      (isLawfulBelow_multiOldCell_iff (r := rows I N J) (w := W) (by decide)).mp
        (hWl.mono (X := (coatomD, 3)) ⟨subset_univ _, le_rfl⟩)
    exact top_le_iff.mp (hWg ▸ le_of_isLawfulBelow_right hIR
      (w := fun d ↦ W (multiOldCell I (mult I N J) d)) hWD hd₂ hgE)
  -- The cell of the tie profile at `(univ, 2)`, and availability from `({0, 1, 2, 3}, 2)`.
  obtain ⟨i₀, hi₀, -⟩ := exists_entry_eq (tieProfile_mem_catalogue hIL hIR hN (j := 2) (by omega))
  have hi₀m : i₀ < mult I N J 1 := by rwa [mult_of_lt (by simp only [Fin.val_one]; omega)]
  obtain ⟨u, hu, hle⟩ := havail (multiOldCell I (mult I N J) sC) _
    (multiNewCell_mem_below (r := rows I N J) ⟨i₀, hi₀m⟩ (by decide))
    (by rw [scope_multiNewCell]; exact subset_univ _)
    (by rw [grade_multiOldCell, grade_multiNewCell]; exact congrArg Prod.snd hsC)
  rw [gradedIndex_multiNewCell] at hu
  obtain ⟨k, i, hk, rfl⟩ := exists_eq_multiNewCell hu
  obtain rfl : k = 1 := Fin.ext (by simp only [Fin.val_one] at hk ⊢; omega)
  have hWu : W (multiNewCell I (mult I N J) 1 i) = ⊤ := top_le_iff.mp (hWsC ▸ hle)
  have hum : multiNewCell I (mult I N J) 1 i ∈
      (profileScheme I N J).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
    multiNewCell_mem_below i (by decide)
  have hmem (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d = 1) :
      multiOldCell I (mult I N J) d ∈ (profileScheme I N J).toCellScheme.below
        ((profileScheme I N J).toCellScheme.gradedIndex (multiNewCell I (mult I N J) 1 i)) := by
    rw [CellScheme.mem_below, gradedIndex_multiOldCell, gradedIndex_multiNewCell]
    -- The second component of the graded index of `d` is its grade.
    exact ⟨subset_univ _, by change I.amalgam.toCellScheme.grade d ≤ _; simp [hd]⟩
  have hg₁ : I.amalgam.toCellScheme.grade d₁ = 1 := congrArg Prod.snd hd₁
  have hg₂ : I.amalgam.toCellScheme.grade d₂ = 1 := congrArg Prod.snd hd₂
  refine ⟨d₁, d₂, i, hd₁, hd₂, ?_, ?_⟩
  · -- Locality at `u`: its profile reads `({3}, 1)` strictly below `({4}, 1)`.
    by_contra hns
    rw [not_lt] at hns
    have h21 := (hloc _ hum).le_of_le (d := ⟨_, hmem d₂ hg₂⟩) (d' := ⟨_, hmem d₁ hg₁⟩)
      (by rw [row_multiNewCell, row_multiNewCell, rows_multiOldCell, rows_multiOldCell]
          exact hns)
      (by
        -- The grades of the two old cells, read in the profile scheme.
        change (profileScheme I N J).toCellScheme.grade (multiOldCell I (mult I N J) d₁) ≤
          (profileScheme I N J).toCellScheme.grade (multiOldCell I (mult I N J) d₂)
        rw [grade_multiOldCell, grade_multiOldCell, hg₁, hg₂])
    simp only [hWu, hWd₁, hWd₂, min_top_right] at h21
    exact hA (top_le_iff.mp h21)
  · -- The capped agreement at `u`.
    have hcap := hag ⟨_, hum⟩
    rw [show w ⟨_, hum⟩ = ⊤ from (Rows.extendBot_of_mem w hum).symm.trans hWu,
      min_top_left] at hcap
    exact min_eq_right_iff.mp hcap.symm

/-! #### The top layer `2`: the lift fails -/

/-- **The ambient labelling at the top layer `2` is lawful below `(univ, 3)`**: the field labelling
of `twoOld` and the tie profile. -/
theorem isLawfulBelow_ambientTwo (hN : 1 ≤ N) :
    (profileScheme I N 2).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
      fun z ↦ fieldLabelling I N 2 (twoOld I) (tieProfile I) z := by
  have hL := TwoFaceLiftExistsCounterexample.isLawfulBelow_tripleLabelling hIL hIR
    (isSelfVisible_gridPoint 1 1) (isSelfVisible_gridPoint 2 1) (isSelfVisible_gridPoint 1 1)
    (isSelfVisible_gridPoint 2 1) ((isSelfVisible_gridPoint 4 0).mono (by omega))
    (gridPoint_le_gridPoint_iff.mpr (by omega)) (fun _ ↦ visibilityReplace_three_one_gridPoint 1)
    (gridPoint_le_gridPoint_iff.mpr (by omega)) (gridPoint_le_gridPoint_iff.mpr (by omega))
  exact isLawfulBelow_fieldLabelling hL.1 hL.2
    (fun d hd ↦ CaseSplitCounterexample.tripleLabelling_eq_of_le_two hd _ _ _ _ _ _)
    (twoOld_le hN) fun j _ hj ↦ tieProfile_mem_catalogue hIL hIR hN (by omega)

/-- **At the top layer `2`, no capped lift exists at the configuration of the seedL
refutation.**  At the ambient labelling `fieldLabelling I N 2 (twoOld I) (tieProfile I)` (lawful,
`isLawfulBelow_ambientTwo`), with the cap `4`, its label at `({0, 1, 2}, 3)`, and the prescription
`(ω + 1, ⊤, ⊤)` on `C`, the ambient label at `({3}, 1)` (lawful, `isLawfulBelow_prescription`; equal
to the ambient labelling capped at `4`, `min_ambientTwo_eq`), no labelling lawful below
`(univ, 3)` restricts to the prescription and agrees with the ambient labelling capped at `4`:
the cell given by `exists_separating_of_lift` has a profile other than the tie profile, whose
agreement height with the tie profile, its ambient label, is at most `3`
(`agreementHeight_tie_lt_capFour`). -/
theorem not_exists_lift_two (hN : 1 ≤ N) :
    ¬ ∃ w : (profileScheme I N 2).toCellScheme.below ((univ : Finset (Fin 5)), 3) → Label.{u},
      (profileScheme I N 2).rows.IsLawfulBelow (univ, 3) w ∧
      (∀ z, min (w z) capFour =
        min (fieldLabelling I N 2 (twoOld I) (tieProfile I) z) capFour) ∧
      ∀ z : (profileScheme I N 2).toCellScheme.below (coatomC, 3),
        w (Set.inclusion ((profileScheme I N 2).toCellScheme.below_mono
          (show ((coatomC, 3) : Finset (Fin 5) × ℕ) ≤ (univ, 3) from ⟨subset_univ _, le_rfl⟩))
          z) = prescription I N 2 tieA z := by
  rintro ⟨w, hw, hag, hres⟩
  obtain ⟨d₁, d₂, i, hd₁, hd₂, hsep, hcap⟩ :=
    exists_separating_of_lift hIL hIR le_rfl hN (gridPoint_ne_top 1 1) hw hag hres
  rw [fieldLabelling_multiNewCell] at hcap
  have hne : entry I N 2 i ≠ tieProfile I := by
    intro h
    rw [h] at hsep
    -- The tie profile at the two cells is `tripleLabelling` at their graded indices.
    change tripleLabelling tieA tieF tieA tieF tieG (I.amalgam.toCellScheme.gradedIndex d₁) <
      tripleLabelling tieA tieF tieA tieF tieG (I.amalgam.toCellScheme.gradedIndex d₂) at hsep
    rw [hd₁, hd₂, tripleLabelling_of_kind (c := 1) (by decide),
      tripleLabelling_of_kind (c := 3) (by decide)] at hsep
    exact lt_irrefl _ hsep
  exact absurd (agreementHeight_tie_lt_capFour hne) (not_lt.mpr hcap)

/-- **The profile scheme with top layer `2` does not lift capped from `(C, 3)` to
`(univ, 3)`**, for every inventory bound `N ≥ 1`: the configuration of `not_exists_lift_two`. -/
theorem not_cappedLift_two (hN : 1 ≤ N) :
    ¬ (profileScheme I N 2).rows.CappedLift (X := (coatomC, 3))
      (Y := ((univ : Finset (Fin 5)), 3)) ⟨subset_univ _, le_rfl⟩ := by
  intro h
  obtain ⟨w, hw, hcap, hres⟩ := (Rows.cappedLift_iff_forall_exists _).mp h capFour
    ((isSelfVisible_gridPoint 4 0).mono (by omega)) (fun z ↦ prescription I N 2 tieA z)
    (fun z ↦ fieldLabelling I N 2 (twoOld I) (tieProfile I) z)
    (isLawfulBelow_prescription hIL hIR 2 1)
    (isLawfulBelow_ambientTwo hIL hIR hN) fun z ↦ min_ambientTwo_eq z
  exact not_exists_lift_two hIL hIR hN ⟨w, hw, hcap, hres⟩


/-! #### The top layer `3` -/

/-- **The layer at the grade `3` excludes the ambient labelling of the top layer `2`.**  In the
profile scheme with top layer `3` (inventory bound `N ≥ 2`), no labelling lawful below
`(univ, 3)` has a label at least `4` at the cell `({0, 1, 2}, 3)` and, at every new cell of
grade `2`, the label of `ambientTwo`: the agreement height of its profile with the tie profile.

Availability from `({0, 1, 2}, 3)` gives a new cell `w` at `(univ, 3)` with label at least `4`;
locality at `w` reads `({0, 1, 2}, 3)` at the value `G_w` of its profile `P_w` there, and reads
every new cell of grade `2` at the agreement height of its profile with `P_w`.  A profile `Q` of
the catalogue at the grade `2` other than the tie profile with agreement height at least `G_w`
with `P_w` exists: `P_w` itself if it is not the tie profile, and the raised profile if it is.  The
witness of the locality at `w` then gives the cell of `Q` a label at least `4`, while its label is
its agreement height with the tie profile, at most `3` (`agreementHeight_tie_lt_capFour`). -/
theorem not_isLawfulBelow_three (hN : 2 ≤ N) {W : Fin (profileScheme I N 3).card → Label.{u}}
    (hW : (profileScheme I N 3).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ W z)
    (hg : ∀ d, I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2} : Finset (Fin 5)), 3) →
      capFour ≤ W (multiOldCell I (mult I N 3) d))
    (hnew : ∀ i : Fin (mult I N 3 1), W (multiNewCell I (mult I N 3) 1 i) =
      agreementHeight (cutGrid N) (tieProfile I) (entry I N 2 i)) : False := by
  classical
  obtain ⟨d₁, -, gE, d₂, hd₁, -, hgE, hd₂⟩ := exists_test_cells hIL hIR
  obtain ⟨-, hloc, havail⟩ := Rows.isLawfulBelow_iff_forall.mp hW
  -- The cell of the tie profile at `(univ, 3)`, and availability from `({0, 1, 2}, 3)`.
  obtain ⟨i₀, hi₀, -⟩ := exists_entry_eq
    (tieProfile_mem_catalogue hIL hIR (by omega : 1 ≤ N) (j := 3) le_rfl)
  have hi₀m : i₀ < mult I N 3 2 := by rwa [mult_of_lt (by decide)]
  obtain ⟨w, hw, hle⟩ := havail (multiOldCell I (mult I N 3) gE) _
    (multiNewCell_mem_below (r := rows I N 3) ⟨i₀, hi₀m⟩ (by decide))
    (by rw [scope_multiNewCell]; exact subset_univ _)
    (by rw [grade_multiOldCell, grade_multiNewCell]; exact congrArg Prod.snd hgE)
  rw [gradedIndex_multiNewCell] at hw
  obtain ⟨k, i, hk, rfl⟩ := exists_eq_multiNewCell hw
  have hk' : (k : ℕ) + 1 = 3 := hk
  have hP3 : entry I N ((k : ℕ) + 1) i ∈ catalogue I N 3 := by
    have h := entry_mem_of_lt_mult i
    rw [hk'] at h ⊢
    exact h
  obtain ⟨γ, σ, hwit, heq⟩ := hloc _ (multiNewCell_mem_below i (by omega))
  -- Locality at `w`, at the cell `({0, 1, 2}, 3)`.
  have hgm : multiOldCell I (mult I N 3) gE ∈ (profileScheme I N 3).toCellScheme.below
      ((profileScheme I N 3).toCellScheme.gradedIndex (multiNewCell I (mult I N 3) k i)) := by
    rw [CellScheme.mem_below, gradedIndex_multiOldCell, gradedIndex_multiNewCell, hgE]
    exact ⟨subset_univ _, by omega⟩
  have hg3 := heq ⟨_, hgm⟩
  rw [row_multiNewCell] at hg3
  beta_reduce at hg3
  rw [rows_multiOldCell, min_eq_left hle, grade_multiOldCell,
    show I.amalgam.toCellScheme.grade gE = 3 from congrArg Prod.snd hgE] at hg3
  -- A profile of the catalogue at the grade `2`, not the tie profile, close to `P_w`.
  obtain ⟨Q, hQ, hQge, hQne⟩ : ∃ Q ∈ catalogue I N 2,
      entry I N ((k : ℕ) + 1) i gE ≤ agreementHeight (cutGrid N) (entry I N ((k : ℕ) + 1) i) Q ∧
        Q ≠ tieProfile I := by
    by_cases hPt : entry I N ((k : ℕ) + 1) i = tieProfile I
    · refine ⟨raisedProfile, tripleProfile_mem_catalogue hIL hIR (by omega)
        (gridPoint_mem_grid (by omega)) (gridPoint_mem_grid (by omega))
        (gridPoint_mem_grid hN) (gridPoint_mem_grid (by omega)) (gridPoint_mem_grid (by omega))
        (gridPoint_le_gridPoint_iff.mpr (by omega))
        (fun _ ↦ visibilityReplace_three_one_gridPoint 1)
        (gridPoint_le_gridPoint_iff.mpr (by omega)) (gridPoint_le_gridPoint_iff.mpr (by omega)),
        ?_, fun h ↦ ?_⟩
      · rw [hPt]
        -- The tie profile at `({0, 1, 2}, 3)` is `3`.
        change tripleLabelling tieA tieF tieA tieF tieG (I.amalgam.toCellScheme.gradedIndex gE) ≤ _
        rw [hgE, tripleLabelling_of_kind (c := 5) (by decide)]
        exact le_agreementHeight (gridPoint_mem_grid (by omega)) fun d ↦
          (min_raisedProfile_eq d).symm
      · have h₂ := congrFun h d₂
        -- Both profiles at `({4}, 1)` are `tripleLabelling` at its graded index.
        change tripleLabelling tieA tieF (gridPoint 1 2) tieF tieG
          (I.amalgam.toCellScheme.gradedIndex d₂) =
            tripleLabelling tieA tieF tieA tieF tieG (I.amalgam.toCellScheme.gradedIndex d₂) at h₂
        rw [hd₂, tripleLabelling_of_kind (c := 3) (by decide),
          tripleLabelling_of_kind (c := 3) (by decide)] at h₂
        exact absurd (le_of_eq h₂) (not_le.mpr (gridPoint_lt_gridPoint.mpr (by omega)))
    · refine ⟨_, mem_catalogue_of_le hP3 (by omega), ?_, hPt⟩
      rw [agreementHeight_self_eq]
      have hmem := (mem_catalogue.mp hP3).1 gE
      rw [show I.amalgam.toCellScheme.grade gE = 3 from congrArg Prod.snd hgE] at hmem
      exact (le_gridPoint_of_mem_grid hmem).trans (gridPoint_le_gridPoint.mpr (by omega))
  -- Locality at `w`, at the cell of `Q` at `(univ, 2)`.
  obtain ⟨i₂, hi₂, he₂⟩ := exists_entry_eq hQ
  have hi₂m : i₂ < mult I N 3 1 := by rwa [mult_of_lt (by decide)]
  have hum : multiNewCell I (mult I N 3) 1 ⟨i₂, hi₂m⟩ ∈ (profileScheme I N 3).toCellScheme.below
      ((profileScheme I N 3).toCellScheme.gradedIndex (multiNewCell I (mult I N 3) k i)) := by
    rw [CellScheme.mem_below, gradedIndex_multiNewCell, gradedIndex_multiNewCell]
    exact ⟨subset_rfl, by simp only [Fin.isValue, Fin.val_one]; omega⟩
  have hu2 := heq ⟨_, hum⟩
  rw [row_multiNewCell] at hu2
  beta_reduce at hu2
  rw [rows_multiNewCell, grade_multiNewCell, hnew] at hu2
  have he₂' : entry I N (((1 : Fin 4) : ℕ) + 1) i₂ = Q := he₂
  have he₂'' : entry I N 2 ((⟨i₂, hi₂m⟩ : Fin (mult I N 3 1)) : ℕ) = Q := he₂
  rw [he₂', he₂''] at hu2
  -- The chain `4 ≤ W g ≤ W u = agreementHeight (tie, Q) < 4`.
  have hchain : capFour ≤ agreementHeight (cutGrid N) (tieProfile I) Q :=
    calc capFour ≤ W (multiOldCell I (mult I N 3) gE) := hg gE hgE
      _ = min (σ (entry I N ((k : ℕ) + 1) i gE)) (γ 3) := hg3
      _ ≤ min (σ (agreementHeight (cutGrid N) (entry I N ((k : ℕ) + 1) i) Q))
          (γ (((1 : Fin 4) : ℕ) + 1)) :=
        min_le_min (hwit.monotone hQge) (hwit.antitone (by simp))
      _ = min (agreementHeight (cutGrid N) (tieProfile I) Q)
          (W (multiNewCell I (mult I N 3) k i)) := hu2.symm
      _ ≤ _ := min_le_left _ _
  exact absurd (agreementHeight_tie_lt_capFour hQne) (not_lt.mpr hchain)

/-- **The ambient labelling at the top layer `3` is lawful below `(univ, 3)`.** -/
theorem isLawfulBelow_ambientThree (hN : 1 ≤ N) :
    (profileScheme I N 3).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
      fun z ↦ fieldLabelling I N 3 (tieProfile I) (tieProfile I) z := by
  have hL := (mem_catalogue.mp (tieProfile_mem_catalogue hIL hIR hN (j := 3) le_rfl)).2
  exact isLawfulBelow_fieldLabelling hL.1 hL.2 (fun _ _ ↦ rfl) tieProfile_le
    fun j _ hj ↦ tieProfile_mem_catalogue hIL hIR hN hj

/-- **At the top layer `3`, the capped lift exists at the configuration of the seedL
refutation.**  At the ambient labelling `fieldLabelling I N 3 (tieProfile I) (tieProfile I)`
(lawful below `(univ, 3)`, `isLawfulBelow_ambientThree`), whose label at the cell `({0, 1, 2}, 3)`
is the cap `3` and at `({3}, 1)` and `({4}, 1)` the tie `ω + 1`, with the prescription
`(ω + 1, ⊤, ⊤)` on `C` (lawful, `isLawfulBelow_prescription`, equal to the ambient labelling capped
at `3` below `(C, 3)`, `min_ambientThree_eq`), some labelling lawful below `(univ, 3)` restricts to
the prescription and agrees with the ambient labelling capped at `3`, for every inventory bound
`N ≥ 3`.

The lift is the field labelling of the lift profile (`ω + 1` at the live cells of grade `1` of `C`,
values in the blocks `2` and `3` at the other live cells), reduced to the block `2`
(`Label.reduce`, a witness bounded by the grade `3`, `isWitness_reduce_blockTwo`): on the old cells
it is the prescription (`reduce_liftProfile`); the lift profile agrees with the tie profile capped
at `3`, so their agreement heights with every profile agree capped at `3`
(`Label.agreementHeight_tri`), which is the capped agreement at the new cells; lawfulness is the
positive-cap transport `CellScheme.Rows.IsLawfulBelow.map_of_min_eq`. -/
theorem exists_lift_three (hN : 3 ≤ N) :
    ∃ w : (profileScheme I N 3).toCellScheme.below ((univ : Finset (Fin 5)), 3) → Label.{u},
      (profileScheme I N 3).rows.IsLawfulBelow (univ, 3) w ∧
      (∀ z, min (w z) tieG =
        min (fieldLabelling I N 3 (tieProfile I) (tieProfile I) z) tieG) ∧
      ∀ z : (profileScheme I N 3).toCellScheme.below (coatomC, 3),
        w (Set.inclusion ((profileScheme I N 3).toCellScheme.below_mono
          (show ((coatomC, 3) : Finset (Fin 5) × ℕ) ≤ (univ, 3) from ⟨subset_univ _, le_rfl⟩))
          z) = prescription I N 3 tieA z := by
  have hlift (j : ℕ) (hj : j ≤ 3) : liftProfile (I := I) ∈ catalogue I N j :=
    tripleProfile_mem_catalogue hIL hIR hj (gridPoint_mem_grid (by omega))
      (gridPoint_mem_grid hN) (gridPoint_mem_grid hN) (gridPoint_mem_grid hN)
      (gridPoint_mem_grid (by omega)) (gridPoint_le_gridPoint_iff.mpr (by omega))
      (fun _ ↦ visibilityReplace_three_one_gridPoint 1)
      (gridPoint_le_gridPoint_iff.mpr (by omega)) (gridPoint_le_gridPoint_iff.mpr (by omega))
  have hL := (mem_catalogue.mp (hlift 3 le_rfl)).2
  have hr := isLawfulBelow_fieldLabelling (J := 3) hL.1 hL.2 (fun _ _ ↦ rfl) (liftProfile_le hN)
    fun j _ hj ↦ hlift j hj
  have hq := isLawfulBelow_ambientThree hIL hIR (N := N) (by omega)
  have hκ : tieG ≤ agreementHeight (cutGrid N) (liftProfile (I := I)) (tieProfile I) :=
    le_agreementHeight (gridPoint_mem_grid (by omega)) min_liftProfile_eq
  have hag (z : Fin (profileScheme I N 3).card) :
      min (reduce blockTwo (fieldLabelling I N 3 liftProfile liftProfile z)) tieG =
        min (fieldLabelling I N 3 (tieProfile I) (tieProfile I) z) tieG := by
    rw [min_reduce_tieG]
    rcases multiCell_cases (r := rows I N 3) z with ⟨d, rfl⟩ | ⟨k, i, rfl⟩
    · rw [fieldLabelling_multiOldCell, fieldLabelling_multiOldCell]
      exact min_liftProfile_eq d
    · rw [fieldLabelling_multiNewCell, fieldLabelling_multiNewCell]
      calc min (agreementHeight (cutGrid N) liftProfile (entry I N ((k : ℕ) + 1) i)) tieG
          = min (min (agreementHeight (cutGrid N) liftProfile (entry I N ((k : ℕ) + 1) i))
              (agreementHeight (cutGrid N) liftProfile (tieProfile I))) tieG := by
            rw [min_assoc, min_eq_right hκ]
        _ = min (min (agreementHeight (cutGrid N) (tieProfile I) (entry I N ((k : ℕ) + 1) i))
              (agreementHeight (cutGrid N) liftProfile (tieProfile I))) tieG := by
            rw [agreementHeight_tri (bot_mem_grid 3 _)]
        _ = _ := by rw [min_assoc, min_eq_right hκ]
  refine ⟨fun z ↦ reduce blockTwo (fieldLabelling I N 3 liftProfile liftProfile z),
    hr.map_of_min_eq hq (fun z ↦ z.2.2) isWitness_reduce_blockTwo (gridPoint_ne_bot 3 0)
      fun z ↦ hag z, fun z ↦ hag z, fun z ↦ ?_⟩
  obtain ⟨d, hd⟩ := exists_eq_multiOldCell (r := rows I N 3) (z := z.1) fun h ↦ by
    have h1 : (profileScheme I N 3).toCellScheme.scope z.1 ⊆ coatomC := z.2.1
    rw [h] at h1
    exact absurd h1 (by decide)
  -- The lift at the cell `z` of `(C, 3)`, an old cell.
  change reduce blockTwo (fieldLabelling I N 3 liftProfile liftProfile z.1) = _
  rw [hd, fieldLabelling_multiOldCell, prescription_multiOldCell]
  exact reduce_liftProfile d

/-! #### The top layer `3` at the top of the inventory: the lift fails -/

/-- The top profile is in the catalogue at the grades `j ≤ 3`. -/
theorem topProfile_mem_catalogue (hN : 1 ≤ N) {j : ℕ} (hj : j ≤ 3) :
    topProfile I N ∈ catalogue I N j :=
  tripleProfile_mem_catalogue hIL hIR hj (gridPoint_mem_grid le_rfl) (gridPoint_mem_grid le_rfl)
    (gridPoint_mem_grid le_rfl) (gridPoint_mem_grid le_rfl) (gridPoint_mem_grid (by omega))
    (gridPoint_le_gridPoint_iff.mpr (by omega)) (fun _ ↦ visibilityReplace_three_one_gridPoint N)
    (gridPoint_le_gridPoint_iff.mpr (by omega)) (gridPoint_le_gridPoint_iff.mpr (by omega))

/-- **The ambient labelling of the top profile is lawful below `(univ, 3)`.** -/
theorem isLawfulBelow_ambientTop (hN : 1 ≤ N) :
    (profileScheme I N 3).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
      fun z ↦ fieldLabelling I N 3 (topProfile I N) (topProfile I N) z := by
  have hL := (mem_catalogue.mp (topProfile_mem_catalogue hIL hIR hN (j := 3) le_rfl)).2
  exact isLawfulBelow_fieldLabelling hL.1 hL.2 (fun _ _ ↦ rfl) topProfile_le
    fun j _ hj ↦ topProfile_mem_catalogue hIL hIR hN hj

/-- **At the top layer `3`, no capped lift exists at the top of the inventory.**  At the ambient
labelling of the top profile (lawful, `isLawfulBelow_ambientTop`), with the cap
`ω * (N - 1) + 3`, its label at `({0, 1, 2}, 3)`, and the prescription `(ω * N + 1, ⊤, ⊤)` on `C`,
its label at `({3}, 1)` (lawful, `isLawfulBelow_prescription`; equal to the ambient labelling
capped at the cap, `min_ambientTop_eq`), no labelling lawful below `(univ, 3)` restricts to the
prescription and agrees with the ambient labelling capped at the cap: the cell given by
`exists_separating_of_lift` would need a normalized value of grade `1` above `ω * N + 1`
(`agreementHeight_top_lt`). -/
theorem not_exists_lift_top (hN : 1 ≤ N) :
    ¬ ∃ w : (profileScheme I N 3).toCellScheme.below ((univ : Finset (Fin 5)), 3) → Label.{u},
      (profileScheme I N 3).rows.IsLawfulBelow (univ, 3) w ∧
      (∀ z, min (w z) (gridPoint 3 (N - 1)) =
        min (fieldLabelling I N 3 (topProfile I N) (topProfile I N) z) (gridPoint 3 (N - 1))) ∧
      ∀ z : (profileScheme I N 3).toCellScheme.below (coatomC, 3),
        w (Set.inclusion ((profileScheme I N 3).toCellScheme.below_mono
          (show ((coatomC, 3) : Finset (Fin 5) × ℕ) ≤ (univ, 3) from ⟨subset_univ _, le_rfl⟩))
          z) = prescription I N 3 (gridPoint 1 N) z := by
  rintro ⟨w, hw, hag, hres⟩
  obtain ⟨d₁, d₂, i, hd₁, hd₂, hsep, hcap⟩ :=
    exists_separating_of_lift hIL hIR (by omega) hN (gridPoint_ne_top 1 N) hw hag hres
  rw [fieldLabelling_multiNewCell] at hcap
  exact absurd (agreementHeight_top_lt hN (mem_catalogue.mp (entry_mem_of_lt_mult i)).1 hd₁ hd₂
    hsep) (not_lt.mpr hcap)

/-- **The profile scheme with top layer `3` does not lift capped from `(C, 3)` to
`(univ, 3)`**, for every inventory bound `N ≥ 1`: the configuration of `not_exists_lift_top`. -/
theorem not_cappedLift_three (hN : 1 ≤ N) :
    ¬ (profileScheme I N 3).rows.CappedLift (X := (coatomC, 3))
      (Y := ((univ : Finset (Fin 5)), 3)) ⟨subset_univ _, le_rfl⟩ := by
  intro h
  obtain ⟨w, hw, hcap, hres⟩ := (Rows.cappedLift_iff_forall_exists _).mp h (gridPoint 3 (N - 1))
    (isSelfVisible_gridPoint 3 _) (fun z ↦ prescription I N 3 (gridPoint 1 N) z)
    (fun z ↦ fieldLabelling I N 3 (topProfile I N) (topProfile I N) z)
    (isLawfulBelow_prescription hIL hIR 3 N) (isLawfulBelow_ambientTop hIL hIR hN)
    fun z ↦ min_ambientTop_eq hN z
  exact not_exists_lift_top hIL hIR hN ⟨w, hw, hcap, hres⟩

end Seeds

end Test

end VaughtConjecture.ProfileCatalogue
