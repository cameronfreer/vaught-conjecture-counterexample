/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ProfileScheme
import VaughtConjecture.Extension.CanonicalMultiScheme

/-!
# The rank-normalized profile scheme on five points, and its lift at the grade three

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`).

Let `I` be any seed on five points.  The **rank-normalized catalogue at the grade `j`**
(`rankCat I j`) is the set of profiles (labellings of all the cells of the amalgam) lawful on the
grade-`j` cut and fixed by the orbit code at the grade `3` (`Label.orbitCode`), which places the
values of a labelling by the ranks of their keys and keeps their finite parts below `3`; such
profiles take their values in `Label.codeGrid 3 (2 N)` for `N` cells.  The **rank-normalized profile
scheme** `rankScheme I J` is the profile scheme of `VaughtConjecture.Extension.ProfileScheme` over
these catalogues, with agreement heights in `Label.grid 3 (2 N + 2)`.

**Extension from the boundary at the grade `3`** (`exists_extension`, `exists_extension_bot`).  For
a top layer `J ≤ 3`, a profile `P` of the catalogue at the grade `3`, a cap `h` self-visible and
short at `3` other than `⊥`, and a labelling `w` lawful below `(C, 3)` and `(D, 3)` agreeing with
`P` capped at `h` at the old cells, the field labelling of the orbit code of `w`, read by the orbit
decoder of `w` at `h`, is lawful below `(univ, 3)`, equal to `w` at the old cells, and agrees with
the field labelling of `P` capped at `h` at every cell below `(univ, 3)`.  The ingredients are the
relative room of the orbit code (`Label.min_orbitCode_eq`), the transfer of capped agreement to
agreement heights at short caps (`Label.min_agreementHeight_eq_of_isShort`), the literal reading and
the cap of the orbit decoder (`Label.orbitDecoder_orbitCode`, `Label.min_orbitDecoder_eq`), and the
positive-cap transport (`CellScheme.Rows.IsLawfulBelow.map_of_min_eq`).  This holds for every seed
on five points.

**Consequences** (every seed on five points; compiled in this repository (theorem named)):

* the rows of the cells at `(univ, 3)` are lawful below `(univ, 3)`, short at `3` and never the
  formal top (`isLawfulBelow_rowBelow_three`, `isShort_ne_top_rowBelow`), and the rows extend from
  the boundary along each of them at every short positive cap (`extendsFromBoundary_row`) and at `⊥`
  (`extendsFromBoundary_bot`);
* **the capped lift at the grade `3` from the lift at the grade `2`** (`cappedLift_three_of_two`):
  in `rankScheme I 3`, if the rows lift capped from `(C, 2)` (resp. `(D, 2)`) into `(univ, 2)`, they
  lift capped from `(C, 3)` (resp. `(D, 3)`) into `(univ, 3)`, by the one-grade lift
  `CellScheme.Rows.cappedLift_of_boundaries_short`; the lift at the grade `2` is a hypothesis;
* **configured lifts** (`exists_lift_fieldLabelling`): at every ambient labelling that is the field
  labelling of a profile of the catalogue at the grade `3`, at every short positive cap, every
  prescription on a coatom agreeing with it capped lifts.  In particular the failure at the top of a
  bounded value set of `ProfileCatalogue.not_cappedLift_three` has no counterpart at these ambient
  labellings.  These are lifts at particular ambient labellings, not the capped lift at every
  ambient labelling.

**Not proved here.**  The lifts at the grades `1` and `2`: the rows of the cells at `(univ, 2)` read
the new cells of grade `1` and `2` at grid points of finite part `3`, so they are not short at `2`,
and the one-grade lift does not apply as stated; the other fields of `Seed.MultiLayerStep`
(positivity at `(univ, 4)`, coding, consistency at the grades `1, 2`, `exists_isLawful`).  So no
completion below the full grade is claimed for any seed.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`, Layer 3,
3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.RankProfile

open Finset Label CellScheme OrderedLayer ProfileScheme
open ProfileCatalogue (Profile IsCutLawful)

variable {α : Ordinal.{u}} (I : Seed.{u} α 3)

/-! ### The rank-normalized catalogues
-/

open Classical in
/-- The **rank-normalized catalogue at the grade `j`**: the profiles lawful on the grade-`j` cut and
fixed by the orbit code at the grade `3` (`Label.orbitCode`), which places the values by the ranks
of their keys; their values lie in the code grid `Label.codeGrid 3 (2 N)` for `N` cells. -/
noncomputable def rankCat (j : ℕ) : Finset (Profile I) :=
  (Fintype.piFinset fun _ ↦ codeGrid 3 (2 * I.amalgam.card)).filter
    fun P ↦ IsCutLawful I j P ∧ orbitCode 3 P = P

/-- The block bound `2 N + 2` of the cut grid, for `N` cells of the amalgam. -/
abbrev gridBound : ℕ := 2 * I.amalgam.card + 2

/-- **The rank-normalized profile scheme with top layer `J`**. -/
noncomputable abbrev rankScheme (J : ℕ) : Scheme.{u} 5 := scheme (rankCat I) (gridBound I) J

variable {I}

/-- Membership in the rank-normalized catalogue. -/
theorem mem_rankCat {j : ℕ} {P : Profile I} :
    P ∈ rankCat I j ↔ IsCutLawful I j P ∧ orbitCode 3 P = P := by
  classical
  simp only [rankCat, Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨fun d ↦ ?_, h⟩⟩
  rw [← congrFun h.2 d]
  exact orbitMap_mem_codeGrid (by simp) _

/-- A profile of the rank-normalized catalogue takes its values in the code grid. -/
theorem mem_codeGrid_of_mem_rankCat {j : ℕ} {P : Profile I} (hP : P ∈ rankCat I j)
    (d : Fin I.amalgam.card) : P d ∈ codeGrid 3 (gridBound I) := by
  rw [← (mem_rankCat.mp hP).2]
  exact orbitMap_mem_codeGrid (by simp) _

/-- A profile of the rank-normalized catalogue lies below the ceiling of the cut grid. -/
theorem le_ceiling_of_mem_rankCat {j : ℕ} {P : Profile I} (hP : P ∈ rankCat I j)
    (d : Fin I.amalgam.card) : P d ≤ gridPoint 3 (gridBound I) :=
  le_gridPoint_of_mem_codeGrid (mem_codeGrid_of_mem_rankCat hP d)

/-- The catalogues decrease with the grade. -/
theorem mem_rankCat_of_le {j j' : ℕ} {P : Profile I} (hP : P ∈ rankCat I j) (hj : j' ≤ j) :
    P ∈ rankCat I j' := by
  obtain ⟨⟨hC, hD⟩, ho⟩ := mem_rankCat.mp hP
  exact mem_rankCat.mpr ⟨⟨hC.mono (X := (coatomC, j')) ⟨subset_rfl, hj⟩,
    hD.mono (X := (coatomD, j')) ⟨subset_rfl, hj⟩⟩, ho⟩

/-- The profile constantly `⊥` is in every catalogue. -/
theorem bot_mem_rankCat (j : ℕ) : (fun _ ↦ ⊥ : Profile I) ∈ rankCat I j :=
  mem_rankCat.mpr ⟨⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩,
    funext fun _ ↦ orbitCode_eq_bot_iff.mpr rfl⟩

/-! ### Rows and field labellings
-/

variable {cat : ℕ → Finset (Profile I)} {B J : ℕ}

/-- The row of a new cell is the field labelling of its profile with itself. -/
theorem rows_eq_fieldLabelling (k : Fin 4) (i : ℕ) (z : Fin (multiCard I (mult cat J))) :
    rows cat B J k i z =
      fieldLabelling cat B J (entry cat ((k : ℕ) + 1) i) (entry cat ((k : ℕ) + 1) i) z := rfl

/-- The row of a new cell, read below its graded index, is the field labelling of its profile. -/
theorem rowBelow_multiNewCell (k : Fin 4) (i : Fin (mult cat J k)) {Y : Finset (Fin 5) × ℕ}
    (hu : (scheme cat B J).toCellScheme.gradedIndex (multiNewCell I (mult cat J) k i) = Y)
    (d : (scheme cat B J).toCellScheme.below Y) :
    (scheme cat B J).rows.rowBelow (multiNewCell I (mult cat J) k i) hu d =
      fieldLabelling cat B J (entry cat ((k : ℕ) + 1) i) (entry cat ((k : ℕ) + 1) i) d :=
  row_multiNewCell k i _

/-- A cell below `(univ, k)` of scope other than the ground set is an old cell of grade at most `k`.
-/
theorem exists_old_of_mem_below {K : ℕ} {z : Fin (scheme cat B J).card}
    (hz : z ∈ (scheme cat B J).toCellScheme.below ((univ : Finset (Fin 5)), K))
    (hne : (scheme cat B J).toCellScheme.scope z ≠ univ) :
    ∃ d, z = multiOldCell I (mult cat J) d ∧ I.amalgam.toCellScheme.grade d ≤ K := by
  obtain ⟨d, rfl⟩ := exists_eq_multiOldCell hne
  refine ⟨d, rfl, ?_⟩
  have := hz.2
  rwa [gradedIndex_multiOldCell] at this

/-! ### Extension from the boundary at the grade `3`
-/

/-- **Extension from the boundary along the field labelling of a profile, at a short cap.**  In the
rank-normalized profile scheme with top layer `J ≤ 3`, let `P` be a profile of the catalogues of the
grades `1, …, 3`, `h` a cap self-visible and short at `3` other than `⊥`, and `w` a labelling lawful
below `(C, 3)` and `(D, 3)` that agrees with `P` capped at `h` at the old cells of grade at most
`3`.  Then some labelling lawful below `(univ, 3)` equals `w` at the old cells and agrees with the
field labelling of `P` capped at `h` at every cell below `(univ, 3)`.

The extension is the field labelling of the orbit code `Q` of `w` (completed by `P` at the cells of
grade above `3`), read by the orbit decoder of `w` at `h`: `Q` agrees with `P` capped at `h` by the
relative room of the orbit code (`Label.min_orbitCode_eq`), hence so do the agreement heights
(`Label.min_agreementHeight_eq_of_isShort`); the decoder reads `Q` literally as `w`
(`Label.orbitDecoder_orbitCode`) and keeps the cap at the agreement heights
(`Label.min_orbitDecoder_eq`); lawfulness is the positive-cap transport
`CellScheme.Rows.IsLawfulBelow.map_of_min_eq`, with the field labelling of `P` as companion. -/
theorem exists_extension (hJ : J ≤ 3) {P : Profile I} (hP : P ∈ rankCat I 3) {h : Label.{u}}
    (hh : IsSelfVisible 3 h) (hs : IsShort 3 h) (hb : h ≠ ⊥)
    {w : Fin (rankScheme I J).card → Label.{u}}
    (hwC : (rankScheme I J).rows.IsLawfulBelow (coatomC, 3) fun z ↦ w z)
    (hwD : (rankScheme I J).rows.IsLawfulBelow (coatomD, 3) fun z ↦ w z)
    (hwP : ∀ d : Fin I.amalgam.card, I.amalgam.toCellScheme.grade d ≤ 3 →
      min (w (multiOldCell I (mult (rankCat I) J) d)) h = min (P d) h) :
    ∃ r : (rankScheme I J).toCellScheme.below ((univ : Finset (Fin 5)), 3) → Label.{u},
      (rankScheme I J).rows.IsLawfulBelow (univ, 3) r ∧
      (∀ z, (rankScheme I J).toCellScheme.scope z.1 ≠ univ → r z = w z) ∧
      ∀ z, min (r z) h = min (fieldLabelling (rankCat I) (gridBound I) J P P z) h := by
  classical
  -- The old labels: `w` up to the grade `3`, `P` above.
  set W : Profile I := fun d ↦
    if I.amalgam.toCellScheme.grade d ≤ 3 then w (multiOldCell I (mult (rankCat I) J) d)
    else P d with hW
  have hWw (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 3) :
      W d = w (multiOldCell I (mult (rankCat I) J) d) := by rw [hW]; exact ite_eq_left hd
  have hWlaw (X : Finset (Fin 5)) (hX : X ≠ univ)
      (hwX : (rankScheme I J).rows.IsLawfulBelow (X, 3) fun z ↦ w z) :
      I.amalgam.rows.IsLawfulBelow (X, 3) fun d ↦ W d := by
    have h1 := (isLawfulBelow_multiOldCell_iff hX).mp hwX
    exact (Rows.isLawfulBelow_congr (R := I.amalgam.rows) (X := (X, 3))
      fun d hd ↦ (hWw d hd.2).symm).mp h1
  have hWC := hWlaw coatomC (by decide) hwC
  have hWD := hWlaw coatomD (by decide) hwD
  have hWP (d : Fin I.amalgam.card) : min (W d) h = min (P d) h := by
    by_cases hd : I.amalgam.toCellScheme.grade d ≤ 3
    · rw [hWw d hd]; exact hwP d hd
    · rw [hW]; simp only [ite_eq_right hd]
  -- Its orbit code `Q`, a profile of the catalogues, agreeing with `P` and `W` capped at `h`.
  set Q : Profile I := orbitCode 3 W with hQ
  have hPo := (mem_rankCat.mp hP).2
  have hQP (d : Fin I.amalgam.card) : min (Q d) h = min (P d) h :=
    min_orbitCode_eq hh hs hPo hWP d
  have hQW (d : Fin I.amalgam.card) : min (Q d) h = min (W d) h := (hQP d).trans (hWP d).symm
  have hQ3 : Q ∈ rankCat I 3 := mem_rankCat.mpr ⟨⟨hWC.orbitCode fun d ↦ d.2.2,
    hWD.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩
  have hcat (R : Profile I) (hR : R ∈ rankCat I 3) (j : ℕ) (_ : 1 ≤ j) (hj : j ≤ J) :
      R ∈ rankCat I j := mem_rankCat_of_le hR (hj.trans hJ)
  -- The two field labellings, lawful below `(univ, 3)`.
  have hfield (R : Profile I) (hR : R ∈ rankCat I 3) :
      (rankScheme I J).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
        fun z ↦ fieldLabelling (rankCat I) (gridBound I) J R R z :=
    isLawfulBelow_fieldLabelling le_rfl (mem_rankCat.mp hR).1.1 (mem_rankCat.mp hR).1.2
      (fun _ _ ↦ rfl) (le_ceiling_of_mem_rankCat hR) (hcat R hR)
  have hval (d : Fin I.amalgam.card) :
      Q d ∈ codeGrid 3 (gridBound I) ∧ P d ∈ codeGrid 3 (gridBound I) :=
    ⟨mem_codeGrid_of_mem_rankCat hQ3 d, mem_codeGrid_of_mem_rankCat hP d⟩
  -- The capped agreement of the decoded field labelling of `Q` with that of `P`.
  have hag (z : (rankScheme I J).toCellScheme.below ((univ : Finset (Fin 5)), 3)) :
      min (orbitDecoder 3 W h (fieldLabelling (rankCat I) (gridBound I) J Q Q z)) h =
        min (fieldLabelling (rankCat I) (gridBound I) J P P z) h := by
    rcases multiCell_cases (r := rows (rankCat I) (gridBound I) J) z.1 with ⟨d, hd⟩ | ⟨k, i, hk⟩
    · rw [hd, fieldLabelling_multiOldCell, fieldLabelling_multiOldCell,
        orbitDecoder_orbitCode hQW d]
      exact hWP d
    · rw [hk, fieldLabelling_multiNewCell, fieldLabelling_multiNewCell,
        min_orbitDecoder_eq (isSelfVisible_of_mem_grid (agreementHeight_spec
          (bot_mem_grid 3 _) _ _).1)]
      exact min_agreementHeight_eq_of_isShort hh hs hval hQP _
  refine ⟨fun z ↦ orbitDecoder 3 W h (fieldLabelling (rankCat I) (gridBound I) J Q Q z),
    (hfield Q hQ3).map_of_min_eq (hfield P hP) (fun z ↦ z.2.2) (isWitness_orbitDecoder hh hb) hb
      hag, fun z hz ↦ ?_, hag⟩
  obtain ⟨d, hd, hd3⟩ := exists_old_of_mem_below z.2 hz
  -- The decoded field labelling at the old cell `z`.
  change orbitDecoder 3 W h (fieldLabelling (rankCat I) (gridBound I) J Q Q z.1) = w z.1
  rw [hd, fieldLabelling_multiOldCell, orbitDecoder_orbitCode hQW d, hWw d hd3]

/-- **Extension from the boundary at the cap `⊥`.**  In the rank-normalized profile scheme with top
layer `J ≤ 3`, every labelling lawful below `(C, 3)` and `(D, 3)` extends, unchanged at the old
cells, to a labelling lawful below `(univ, 3)`: the field labelling of its orbit code, read by its
orbit decoder at the least grid point `3`. -/
theorem exists_extension_bot (hJ : J ≤ 3) {w : Fin (rankScheme I J).card → Label.{u}}
    (hwC : (rankScheme I J).rows.IsLawfulBelow (coatomC, 3) fun z ↦ w z)
    (hwD : (rankScheme I J).rows.IsLawfulBelow (coatomD, 3) fun z ↦ w z) :
    ∃ r : (rankScheme I J).toCellScheme.below ((univ : Finset (Fin 5)), 3) → Label.{u},
      (rankScheme I J).rows.IsLawfulBelow (univ, 3) r ∧
      ∀ z, (rankScheme I J).toCellScheme.scope z.1 ≠ univ → r z = w z := by
  classical
  set W : Profile I := fun d ↦
    if I.amalgam.toCellScheme.grade d ≤ 3 then w (multiOldCell I (mult (rankCat I) J) d)
    else ⊥ with hW
  have hWw (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 3) :
      W d = w (multiOldCell I (mult (rankCat I) J) d) := by rw [hW]; exact ite_eq_left hd
  have hWlaw (X : Finset (Fin 5)) (hX : X ≠ univ)
      (hwX : (rankScheme I J).rows.IsLawfulBelow (X, 3) fun z ↦ w z) :
      I.amalgam.rows.IsLawfulBelow (X, 3) fun d ↦ W d := by
    have h1 := (isLawfulBelow_multiOldCell_iff hX).mp hwX
    exact (Rows.isLawfulBelow_congr (R := I.amalgam.rows) (X := (X, 3))
      fun d hd ↦ (hWw d hd.2).symm).mp h1
  set Q : Profile I := orbitCode 3 W with hQ
  have hQ3 : Q ∈ rankCat I 3 := mem_rankCat.mpr ⟨⟨(hWlaw coatomC (by decide) hwC).orbitCode
    fun d ↦ d.2.2, (hWlaw coatomD (by decide) hwD).orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩
  have hQW (d : Fin I.amalgam.card) : min (Q d) (gridPoint 3 0) = min (W d) (gridPoint 3 0) :=
    min_orbitCode_gridPoint_zero d
  have hfield := isLawfulBelow_fieldLabelling (cat := rankCat I) (B := gridBound I) (J := J)
    le_rfl (mem_rankCat.mp hQ3).1.1 (mem_rankCat.mp hQ3).1.2 (fun _ _ ↦ rfl)
    (le_ceiling_of_mem_rankCat hQ3) fun j _ hj ↦ mem_rankCat_of_le hQ3 (hj.trans hJ)
  have hag (z : (rankScheme I J).toCellScheme.below ((univ : Finset (Fin 5)), 3)) :
      min (orbitDecoder 3 W (gridPoint 3 0)
        (fieldLabelling (rankCat I) (gridBound I) J Q Q z)) (gridPoint 3 0) =
        min (fieldLabelling (rankCat I) (gridBound I) J Q Q z) (gridPoint 3 0) := by
    rcases multiCell_cases (r := rows (rankCat I) (gridBound I) J) z.1 with ⟨d, hd⟩ | ⟨k, i, hk⟩
    · rw [hd, fieldLabelling_multiOldCell, orbitDecoder_orbitCode hQW d]
      exact (hQW d).symm
    · rw [hk, fieldLabelling_multiNewCell]
      exact min_orbitDecoder_eq (isSelfVisible_of_mem_grid (agreementHeight_spec
        (bot_mem_grid 3 _) _ _).1)
  refine ⟨fun z ↦ orbitDecoder 3 W (gridPoint 3 0)
    (fieldLabelling (rankCat I) (gridBound I) J Q Q z),
    hfield.map_of_min_eq hfield (fun z ↦ z.2.2)
      (isWitness_orbitDecoder (isSelfVisible_gridPoint 3 0) (gridPoint_ne_bot 3 0))
      (gridPoint_ne_bot 3 0) hag, fun z hz ↦ ?_⟩
  obtain ⟨d, hd, hd3⟩ := exists_old_of_mem_below z.2 hz
  -- The decoded field labelling at the old cell `z`.
  change orbitDecoder 3 W (gridPoint 3 0) (fieldLabelling (rankCat I) (gridBound I) J Q Q z.1) =
    w z.1
  rw [hd, fieldLabelling_multiOldCell, orbitDecoder_orbitCode hQW d, hWw d hd3]

/-! ### The serving rows at `(univ, 3)` and the lift at the grade `3`
-/

/-- The cells at `(univ, 3)`: new cells of grade `3`, whose profile is in the catalogue at the grade
`3`. -/
theorem exists_profile_of_gradedIndex {u : Fin (rankScheme I J).card}
    (hu : (rankScheme I J).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), 3)) :
    ∃ (i : Fin (mult (rankCat I) J 2)), u = multiNewCell I (mult (rankCat I) J) 2 i := by
  obtain ⟨k, i, hk, rfl⟩ := exists_eq_multiNewCell hu
  obtain rfl : k = 2 := Fin.ext (by omega)
  exact ⟨i, rfl⟩

/-- A row lawful below a pair equal to the graded index of its cell is consistent there. -/
theorem isLawfulBelow_row_of_rowBelow {n : ℕ} {S : Scheme.{u} n} {u : Fin S.card}
    {Y : Finset (Fin n) × ℕ} (hu : S.toCellScheme.gradedIndex u = Y)
    (h : S.rows.IsLawfulBelow Y (S.rows.rowBelow u hu)) :
    S.rows.IsLawfulBelow (S.toCellScheme.gradedIndex u) (S.rows.row u) := by
  subst hu
  exact h

/-- **The row of a cell at `(univ, 3)` is lawful below `(univ, 3)`** (consistency), for a top layer
`J ≤ 3`. -/
theorem isLawfulBelow_rowBelow_three (hJ : J ≤ 3) (i : Fin (mult (rankCat I) J 2))
    (hu : (rankScheme I J).toCellScheme.gradedIndex (multiNewCell I (mult (rankCat I) J) 2 i) =
      ((univ : Finset (Fin 5)), 3)) :
    (rankScheme I J).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
      ((rankScheme I J).rows.rowBelow _ hu) := by
  have hP : entry (rankCat I) 3 i ∈ rankCat I 3 := entry_mem_of_lt_mult i
  have h := isLawfulBelow_fieldLabelling (cat := rankCat I) (B := gridBound I) (J := J) le_rfl
    (mem_rankCat.mp hP).1.1 (mem_rankCat.mp hP).1.2 (fun _ _ ↦ rfl)
    (le_ceiling_of_mem_rankCat hP) fun j _ hj ↦ mem_rankCat_of_le hP (hj.trans hJ)
  convert h using 1
  funext d
  exact rowBelow_multiNewCell 2 i hu d

/-- The row of a cell at `(univ, 3)` is short at `3` and never the formal top. -/
theorem isShort_ne_top_rowBelow (i : Fin (mult (rankCat I) J 2))
    (hu : (rankScheme I J).toCellScheme.gradedIndex (multiNewCell I (mult (rankCat I) J) 2 i) =
      ((univ : Finset (Fin 5)), 3))
    (d : (rankScheme I J).toCellScheme.below ((univ : Finset (Fin 5)), 3)) :
    IsShort 3 ((rankScheme I J).rows.rowBelow _ hu d) ∧
      (rankScheme I J).rows.rowBelow _ hu d ≠ ⊤ := by
  have hP : entry (rankCat I) 3 i ∈ rankCat I 3 := entry_mem_of_lt_mult i
  rw [rowBelow_multiNewCell]
  rcases multiCell_cases (r := rows (rankCat I) (gridBound I) J) d.1 with ⟨e, he⟩ | ⟨k, j, hk⟩
  · rw [he, fieldLabelling_multiOldCell]
    exact ⟨isShort_of_mem_codeGrid (mem_codeGrid_of_mem_rankCat hP e),
      ne_top_of_mem_codeGrid (mem_codeGrid_of_mem_rankCat hP e)⟩
  · rw [hk, fieldLabelling_multiNewCell]
    have hm := (agreementHeight_spec (bot_mem_grid 3 (gridBound I)) (entry (rankCat I) 3 i)
      (entry (rankCat I) ((k : ℕ) + 1) j)).1
    exact ⟨isShort_of_mem_grid hm, ne_top_of_mem_grid hm⟩

/-- The two orders of the coatoms at the grade `3`. -/
def IsCoatomPair (U V : Finset (Fin 5) × ℕ) : Prop :=
  (U = (coatomC, 3) ∧ V = (coatomD, 3)) ∨ (U = (coatomD, 3) ∧ V = (coatomC, 3))

/-- The two coatoms, in either order, as `C` and `D`. -/
theorem IsCoatomPair.lawful {U V : Finset (Fin 5) × ℕ} (hUV : IsCoatomPair U V)
    {w : Fin (rankScheme I J).card → Label.{u}}
    (hwU : (rankScheme I J).rows.IsLawfulBelow U fun z ↦ w z)
    (hwV : (rankScheme I J).rows.IsLawfulBelow V fun z ↦ w z) :
    (rankScheme I J).rows.IsLawfulBelow (coatomC, 3) (fun z ↦ w z) ∧
      (rankScheme I J).rows.IsLawfulBelow (coatomD, 3) fun z ↦ w z := by
  rcases hUV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [⟨hwU, hwV⟩, ⟨hwV, hwU⟩]

/-- An old cell of grade at most `3` lies below one of the coatoms of a pair. -/
theorem IsCoatomPair.mem {U V : Finset (Fin 5) × ℕ} (hUV : IsCoatomPair U V)
    (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 3) :
    multiOldCell I (mult (rankCat I) J) d ∈ (rankScheme I J).toCellScheme.below U ∨
      multiOldCell I (mult (rankCat I) J) d ∈ (rankScheme I J).toCellScheme.below V := by
  have h := mem_below_coatom_of_ne_multi (r := rows (rankCat I) (gridBound I) J)
    (multiOldCell_mem_below (X := ((univ : Finset (Fin 5)), 3)) ⟨subset_univ _, hd⟩)
    (scope_multiOldCell_ne d)
  rcases hUV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [h, h.symm]

/-- The cells on the boundary of a pair have scope other than the ground set. -/
theorem IsCoatomPair.scope_ne {U V : Finset (Fin 5) × ℕ} (hUV : IsCoatomPair U V)
    {z : Fin (rankScheme I J).card}
    (hz : z ∈ (rankScheme I J).toCellScheme.below U ∨ z ∈ (rankScheme I J).toCellScheme.below V) :
    (rankScheme I J).toCellScheme.scope z ≠ univ := by
  intro h
  have hsub : ∀ X : Finset (Fin 5) × ℕ, z ∈ (rankScheme I J).toCellScheme.below X →
      (univ : Finset (Fin 5)) ⊆ X.1 := fun X hX ↦ h ▸ hX.1
  rcases hUV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hz with hz | hz <;>
    exact absurd (hsub _ hz) (by decide)

/-- **Extension from the boundary along a serving row at `(univ, 3)`**, at every cap self-visible
and short at `3` other than `⊥` (`exists_extension`), for either order of the coatoms. -/
theorem extendsFromBoundary_row (hJ : J ≤ 3) {U V : Finset (Fin 5) × ℕ} (hUV : IsCoatomPair U V)
    (i : Fin (mult (rankCat I) J 2))
    (hu : (rankScheme I J).toCellScheme.gradedIndex (multiNewCell I (mult (rankCat I) J) 2 i) =
      ((univ : Finset (Fin 5)), 3))
    {h : Label.{u}} (hh : IsSelfVisible 3 h) (hs : IsShort 3 h) (hb : ⊥ < h) :
    (rankScheme I J).rows.ExtendsFromBoundary U V ((univ : Finset (Fin 5)), 3) h
      ((rankScheme I J).rows.rowBelow _ hu) := by
  intro w hwU hwV hwS
  have hP : entry (rankCat I) 3 i ∈ rankCat I 3 := entry_mem_of_lt_mult i
  obtain ⟨hwC, hwD⟩ := hUV.lawful hwU hwV
  have hwP (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 3) :
      min (w (multiOldCell I (mult (rankCat I) J) d)) h = min (entry (rankCat I) 3 i d) h := by
    have h1 := hwS ⟨_, multiOldCell_mem_below (X := ((univ : Finset (Fin 5)), 3))
      ⟨subset_univ _, hd⟩⟩ (hUV.mem d hd)
    rw [rowBelow_multiNewCell] at h1
    -- The field labelling of the profile at the old cell `d`.
    change _ = min (fieldLabelling (rankCat I) (gridBound I) J (entry (rankCat I) 3 i)
      (entry (rankCat I) 3 i) (multiOldCell I (mult (rankCat I) J) d)) h at h1
    rwa [fieldLabelling_multiOldCell] at h1
  obtain ⟨r, hr, hrw, hrc⟩ := exists_extension hJ hP hh hs hb.ne' hwC hwD hwP
  refine ⟨r, hr, fun d hd ↦ hrw d (hUV.scope_ne hd), fun d ↦ ?_⟩
  rw [rowBelow_multiNewCell]
  exact hrc d

/-- **Extension from the boundary at the cap `⊥`**, for either order of the coatoms. -/
theorem extendsFromBoundary_bot (hJ : J ≤ 3) {U V : Finset (Fin 5) × ℕ} (hUV : IsCoatomPair U V) :
    (rankScheme I J).rows.ExtendsFromBoundary U V ((univ : Finset (Fin 5)), 3) ⊥ fun _ ↦ ⊥ := by
  intro w hwU hwV _
  obtain ⟨hwC, hwD⟩ := hUV.lawful hwU hwV
  obtain ⟨r, hr, hrw⟩ := exists_extension_bot hJ hwC hwD
  exact ⟨r, hr, fun d hd ↦ hrw d (hUV.scope_ne hd), fun _ ↦ by simp⟩

/-- **The capped lift at the grade `3` from the lift at the grade `2`**, from either coatom, in the
rank-normalized profile scheme with top layer `3`, for every seed on five points.  It is the
one-grade lift `CellScheme.Rows.cappedLift_of_boundaries_short`: the boundary lifts are those of the
amalgam (`OrderedLayer.cappedLift_multiOld`), the extension from the boundary at `⊥` is
`extendsFromBoundary_bot`, and every cell at `(univ, 3)` serves the positive caps
(`isLawfulBelow_rowBelow_three`, `isShort_ne_top_rowBelow`, `extendsFromBoundary_row`).  The lift at
the grade `2` is a hypothesis. -/
theorem cappedLift_three_of_two {U V : Finset (Fin 5) × ℕ} (hUV : IsCoatomPair U V)
    (hlift : (rankScheme I 3).rows.CappedLift (X := (U.1, 2)) (Y := ((univ : Finset (Fin 5)), 2))
      ⟨subset_univ _, le_rfl⟩) :
    (rankScheme I 3).rows.CappedLift (X := U) (Y := ((univ : Finset (Fin 5)), 3))
      ⟨subset_univ _, by rcases hUV with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact le_rfl⟩ := by
  classical
  have hfaces (X : Finset (Fin 5)) (hX : X ∈ I.amalgam.toCellScheme.faces) (hX3 : 3 ≤ #X) :
      (X, 3) ∈ (rankScheme I 3).toCellScheme.gradedFaces := ⟨hX, by omega, hX3⟩
  have hO : ((coatomC ∩ coatomD : Finset (Fin 5)), 3) ∈
      (rankScheme I 3).toCellScheme.gradedFaces :=
    hfaces _ I.inter_coatoms_mem_faces (by decide)
  have hCf : ((coatomC : Finset (Fin 5)), 3) ∈ (rankScheme I 3).toCellScheme.gradedFaces :=
    hfaces _ (coatomC_mem_faces I) (by decide)
  have hDf : ((coatomD : Finset (Fin 5)), 3) ∈ (rankScheme I 3).toCellScheme.gradedFaces :=
    hfaces _ (coatomD_mem_faces I) (by decide)
  -- A cell at `(univ, 3)`: the profile constantly `⊥`.
  obtain ⟨i₀, hi₀, -⟩ := exists_entry_eq (bot_mem_rankCat (I := I) 3)
  have hi₀m : i₀ < mult (rankCat I) 3 2 := by rwa [mult_of_lt (by decide)]
  have hY : ∃ t, (rankScheme I 3).toCellScheme.gradedIndex t = ((univ : Finset (Fin 5)), 3) :=
    ⟨multiNewCell I (mult (rankCat I) 3) 2 ⟨i₀, hi₀m⟩, gradedIndex_multiNewCell _ _⟩
  have hrow : ∀ u (hu : (rankScheme I 3).toCellScheme.gradedIndex u =
      ((univ : Finset (Fin 5)), 3)),
      (rankScheme I 3).rows.IsLawfulBelow ((rankScheme I 3).toCellScheme.gradedIndex u)
        ((rankScheme I 3).rows.row u) ∧
      (∀ d, IsShort 3 ((rankScheme I 3).rows.rowBelow u hu d)) ∧
      (∀ d, (rankScheme I 3).rows.rowBelow u hu d ≠ ⊤) ∧
      ∀ h, IsSelfVisible 3 h → IsShort 3 h → ⊥ < h →
        (rankScheme I 3).rows.ExtendsFromBoundary U V ((univ : Finset (Fin 5)), 3) h
          ((rankScheme I 3).rows.rowBelow u hu) := by
    intro u hu
    obtain ⟨i, rfl⟩ := exists_profile_of_gradedIndex hu
    exact ⟨isLawfulBelow_row_of_rowBelow hu (isLawfulBelow_rowBelow_three le_rfl i hu),
      fun d ↦ (isShort_ne_top_rowBelow i hu d).1,
      fun d ↦ (isShort_ne_top_rowBelow i hu d).2,
      fun h hh hs hb ↦ extendsFromBoundary_row le_rfl hUV i hu hh hs hb⟩
  rcases hUV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨c, hc⟩ := I.exists_gradedIndex_eq _ hCf (by decide)
    exact Rows.cappedLift_of_boundaries_short (j := 2) (U₀ := (coatomC, 3)) (V₀ := (coatomD, 3))
      (O₀ := (coatomC ∩ coatomD, 3)) (U := (coatomC, 3)) (V := (coatomD, 3))
      (O := (coatomC ∩ coatomD, 3)) (subset_univ _)
      ⟨multiOldCell I _ c, (gradedIndex_multiOldCell c).trans hc⟩ hlift le_rfl
      ⟨inter_subset_left, le_rfl⟩ ⟨inter_subset_right, le_rfl⟩ ⟨subset_univ _, le_rfl⟩
      ⟨subset_univ _, le_rfl⟩ (fun d h1 h2 ↦ ⟨subset_inter h1.1 h2.1, h1.2⟩)
      (Rows.cappedLift_refl _) (cappedLift_multiOld hO hDf (by decide) _)
      (extendsFromBoundary_bot le_rfl (.inl ⟨rfl, rfl⟩)) le_rfl
      ⟨inter_subset_left, le_rfl⟩ ⟨inter_subset_right, le_rfl⟩ ⟨subset_univ _, le_rfl⟩
      ⟨subset_univ _, le_rfl⟩ (fun d h1 h2 ↦ ⟨subset_inter h1.1 h2.1, h1.2⟩)
      (Rows.cappedLift_refl _) (cappedLift_multiOld hO hDf (by decide) _) hY hrow
  · obtain ⟨c, hc⟩ := I.exists_gradedIndex_eq _ hDf (by decide)
    exact Rows.cappedLift_of_boundaries_short (j := 2) (U₀ := (coatomD, 3)) (V₀ := (coatomC, 3))
      (O₀ := (coatomC ∩ coatomD, 3)) (U := (coatomD, 3)) (V := (coatomC, 3))
      (O := (coatomC ∩ coatomD, 3)) (subset_univ _)
      ⟨multiOldCell I _ c, (gradedIndex_multiOldCell c).trans hc⟩ hlift le_rfl
      ⟨inter_subset_right, le_rfl⟩ ⟨inter_subset_left, le_rfl⟩ ⟨subset_univ _, le_rfl⟩
      ⟨subset_univ _, le_rfl⟩ (fun d h1 h2 ↦ ⟨subset_inter h2.1 h1.1, h1.2⟩)
      (Rows.cappedLift_refl _) (cappedLift_multiOld hO hCf (by decide) _)
      (extendsFromBoundary_bot le_rfl (.inr ⟨rfl, rfl⟩)) le_rfl
      ⟨inter_subset_right, le_rfl⟩ ⟨inter_subset_left, le_rfl⟩ ⟨subset_univ _, le_rfl⟩
      ⟨subset_univ _, le_rfl⟩ (fun d h1 h2 ↦ ⟨subset_inter h2.1 h1.1, h1.2⟩)
      (Rows.cappedLift_refl _) (cappedLift_multiOld hO hCf (by decide) _) hY hrow

/-! ### Configured lifts at every field labelling
-/

/-- **Extension from the boundary along the field labelling of any profile of the catalogue at the
grade `3`**, at every cap self-visible and short at `3` other than `⊥`, for either order of the
coatoms (`exists_extension`). -/
theorem extendsFromBoundary_fieldLabelling (hJ : J ≤ 3) {U V : Finset (Fin 5) × ℕ}
    (hUV : IsCoatomPair U V) {P : Profile I} (hP : P ∈ rankCat I 3) {h : Label.{u}}
    (hh : IsSelfVisible 3 h) (hs : IsShort 3 h) (hb : h ≠ ⊥) :
    (rankScheme I J).rows.ExtendsFromBoundary U V ((univ : Finset (Fin 5)), 3) h
      fun z ↦ fieldLabelling (rankCat I) (gridBound I) J P P z := by
  intro w hwU hwV hwS
  obtain ⟨hwC, hwD⟩ := hUV.lawful hwU hwV
  have hwP (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 3) :
      min (w (multiOldCell I (mult (rankCat I) J) d)) h = min (P d) h := by
    have h1 := hwS ⟨_, multiOldCell_mem_below (X := ((univ : Finset (Fin 5)), 3))
      ⟨subset_univ _, hd⟩⟩ (hUV.mem d hd)
    -- The field labelling of `P` at the old cell `d`.
    change _ = min (fieldLabelling (rankCat I) (gridBound I) J P P
      (multiOldCell I (mult (rankCat I) J) d)) h at h1
    rwa [fieldLabelling_multiOldCell] at h1
  obtain ⟨r, hr, hrw, hrc⟩ := exists_extension hJ hP hh hs hb hwC hwD hwP
  exact ⟨r, hr, fun d hd ↦ hrw d (hUV.scope_ne hd), hrc⟩

/-- **The configured lift at every field labelling** (top layer `J ≤ 3`, every seed on five points).
For every profile `P` of the catalogue at the grade `3`, every cap `h` self-visible and short at `3`
other than `⊥`, and every prescription `f` lawful below `(C, 3)` (or `(D, 3)`) that agrees with the
field labelling of `P` capped at `h`, some labelling lawful below `(univ, 3)` restricts to `f` and
agrees with the field labelling of `P` capped at `h`: the lift through the coatom and the common
face (`CellScheme.Rows.exists_lift_of_boundary`) followed by the extension from the boundary
(`extendsFromBoundary_fieldLabelling`).  It is a lift at the ambient labellings that are field
labellings of profiles of the catalogue, at the short caps, not the capped lift at every ambient
labelling. -/
theorem exists_lift_fieldLabelling (hJ : J ≤ 3) {U V : Finset (Fin 5) × ℕ}
    (hUV : IsCoatomPair U V) {P : Profile I} (hP : P ∈ rankCat I 3) {h : Label.{u}}
    (hh : IsSelfVisible 3 h) (hs : IsShort 3 h) (hb : h ≠ ⊥)
    {f : (rankScheme I J).toCellScheme.below U → Label.{u}}
    (hf : (rankScheme I J).rows.IsLawfulBelow U f)
    (hfS : ∀ e, min (f e) h = min (fieldLabelling (rankCat I) (gridBound I) J P P e) h) :
    ∃ r : (rankScheme I J).toCellScheme.below ((univ : Finset (Fin 5)), 3) → Label.{u},
      (rankScheme I J).rows.IsLawfulBelow (univ, 3) r ∧
      (∀ e : (rankScheme I J).toCellScheme.below U, r ⟨e.1, (rankScheme I J).toCellScheme.below_mono
        (show U ≤ ((univ : Finset (Fin 5)), 3) by
          rcases hUV with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact ⟨subset_univ _, le_rfl⟩) e.2⟩ = f e) ∧
      ∀ d, min (r d) h = min (fieldLabelling (rankCat I) (gridBound I) J P P d) h := by
  have hcat (j : ℕ) (_ : 1 ≤ j) (hj : j ≤ J) : P ∈ rankCat I j := mem_rankCat_of_le hP (hj.trans hJ)
  have hS := isLawfulBelow_fieldLabelling (cat := rankCat I) (B := gridBound I) (J := J) le_rfl
    (mem_rankCat.mp hP).1.1 (mem_rankCat.mp hP).1.2 (fun _ _ ↦ rfl)
    (le_ceiling_of_mem_rankCat hP) hcat
  have hO : ((coatomC ∩ coatomD : Finset (Fin 5)), 3) ∈
      (rankScheme I J).toCellScheme.gradedFaces := ⟨I.inter_coatoms_mem_faces, by omega, by decide⟩
  have hCf : ((coatomC : Finset (Fin 5)), 3) ∈ (rankScheme I J).toCellScheme.gradedFaces :=
    ⟨coatomC_mem_faces I, by omega, by decide⟩
  have hDf : ((coatomD : Finset (Fin 5)), 3) ∈ (rankScheme I J).toCellScheme.gradedFaces :=
    ⟨coatomD_mem_faces I, by omega, by decide⟩
  rcases hUV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Rows.exists_lift_of_boundary (O := (coatomC ∩ coatomD, 3)) (U := (coatomC, 3))
      (V := (coatomD, 3)) (Y := ((univ : Finset (Fin 5)), 3)) le_rfl ⟨inter_subset_left, le_rfl⟩
      ⟨inter_subset_right, le_rfl⟩ ⟨subset_univ _, le_rfl⟩
      ⟨subset_univ _, le_rfl⟩ (fun d h1 h2 ↦ ⟨subset_inter h1.1 h2.1, h1.2⟩)
      (Rows.cappedLift_refl _) (cappedLift_multiOld hO hDf (by decide) _) hh hS
      (extendsFromBoundary_fieldLabelling hJ (.inl ⟨rfl, rfl⟩) hP hh hs hb) hf hfS
  · exact Rows.exists_lift_of_boundary (O := (coatomC ∩ coatomD, 3)) (U := (coatomD, 3))
      (V := (coatomC, 3)) (Y := ((univ : Finset (Fin 5)), 3)) le_rfl ⟨inter_subset_right, le_rfl⟩
      ⟨inter_subset_left, le_rfl⟩ ⟨subset_univ _, le_rfl⟩
      ⟨subset_univ _, le_rfl⟩ (fun d h1 h2 ↦ ⟨subset_inter h2.1 h1.1, h1.2⟩)
      (Rows.cappedLift_refl _) (cappedLift_multiOld hO hCf (by decide) _) hh hS
      (extendsFromBoundary_fieldLabelling hJ (.inr ⟨rfl, rfl⟩) hP hh hs hb) hf hfS

end VaughtConjecture.RankProfile
