/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ProfileCatalogue

/-!
# Profile schemes over an arbitrary family of catalogues

The construction of `VaughtConjecture.Extension.ProfileCatalogue`, with the catalogue at each grade
and the block bound of the cut grid as parameters: for a family `cat` of finite sets of profiles
(labellings of the cells of the amalgam) and a bound `B`, the scheme `scheme cat B J` has one new
cell at `(univ, j)` per entry of `cat j`, `j ≤ J`, whose row reads the old cells by its profile and
the new cells by agreement heights of whole profiles in `Label.grid 3 B`.  The field labellings
of such a scheme are lawful below `(univ, K)`, `K ≤ 3` (`isLawfulBelow_fieldLabelling`).

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.ProfileScheme

open Finset Label CellScheme OrderedLayer
open ProfileCatalogue (Profile IsCutLawful)

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} (cat : ℕ → Finset (Profile I)) (B : ℕ)

/-- The `i`-th entry of the catalogue `cat j`, in the order of `Finset.equivFin`, and the profile
constantly `⊥` past its size. -/
noncomputable def entry (j i : ℕ) : Profile I :=
  if h : i < (cat j).card then ((cat j).equivFin.symm ⟨i, h⟩ : Profile I) else fun _ ↦ ⊥

variable {cat} in
/-- The entries of a catalogue below its size are in it. -/
theorem entry_mem {j i : ℕ} (hi : i < (cat j).card) : entry cat j i ∈ cat j := by
  rw [entry, dite_eq_left hi]
  exact ((cat j).equivFin.symm ⟨i, hi⟩).2

variable {cat} in
/-- Every profile of a catalogue is an entry below its size. -/
theorem exists_entry_eq {j : ℕ} {P : Profile I} (hP : P ∈ cat j) :
    ∃ i, i < (cat j).card ∧ entry cat j i = P := by
  refine ⟨(cat j).equivFin ⟨P, hP⟩, ((cat j).equivFin ⟨P, hP⟩).2, ?_⟩
  rw [entry, dite_eq_left ((cat j).equivFin ⟨P, hP⟩).2]
  simp

/-! ### The profile scheme -/

/-- The multiplicities of the profile scheme with top layer `J`: one new cell at `(univ, k + 1)`
per entry of the catalogue at the grade `k + 1` for `k + 1 ≤ J`, and none above. -/
noncomputable def mult (J : ℕ) (k : Fin 4) : ℕ :=
  if (k : ℕ) < J then (cat ((k : ℕ) + 1)).card else 0

/-- The profile of the cell with index `z` of the profile scheme with top layer `J`: the entry of
the catalogue that the new cell of that index carries.  It is not used at the old cells. -/
noncomputable def cellProfile (J z : ℕ) : Profile I :=
  if z < I.amalgam.card + mult cat J 0 then entry cat 1 (z - I.amalgam.card)
  else if z < I.amalgam.card + mult cat J 0 + mult cat J 1 then
    entry cat 2 (z - I.amalgam.card - mult cat J 0)
  else if z < I.amalgam.card + mult cat J 0 + mult cat J 1 + mult cat J 2 then
    entry cat 3 (z - I.amalgam.card - mult cat J 0 - mult cat J 1)
  else entry cat 4 (z - I.amalgam.card - mult cat J 0 - mult cat J 1 - mult cat J 2)

/-- The rows of the profile scheme: the new cell of an entry `P` reads every old cell by `P` and
every new cell by the agreement height of `P` and its profile in the cut grid. -/
noncomputable def rows (J : ℕ) : MultiRows I (mult cat J) := fun k i z ↦
  if hz : (z : ℕ) < I.amalgam.card then entry cat ((k : ℕ) + 1) i ⟨z, hz⟩
  else agreementHeight (grid 3 B) (entry cat ((k : ℕ) + 1) i) (cellProfile cat J z)

/-- **The profile scheme with top layer `J`**: the amalgam followed by one new cell at
`(univ, j)` per entry of the catalogue at the grade `j`, for `1 ≤ j ≤ min J 4`, with the rows
`rows cat B J`. -/
noncomputable abbrev scheme (J : ℕ) : Scheme.{u} 5 :=
  multiLayerScheme I (mult cat J) (rows cat B J)

variable {cat B} {J : ℕ}

/-- There are new cells of grade `k + 1` only for `k < J`. -/
theorem lt_of_lt_mult {k : Fin 4} (i : Fin (mult cat J k)) : (k : ℕ) < J := by
  by_contra h
  have := i.isLt
  simp [mult, h] at this

/-- For `k < J`, the multiplicity at `(univ, k + 1)` is the size of the catalogue there. -/
theorem mult_of_lt {k : Fin 4} (hk : (k : ℕ) < J) :
    mult cat J k = (cat ((k : ℕ) + 1)).card := by
  unfold mult; exact ite_eq_left hk

/-- The index of a new cell is below the size of its catalogue. -/
theorem lt_card_of_lt_mult {k : Fin 4} (i : Fin (mult cat J k)) :
    (i : ℕ) < (cat ((k : ℕ) + 1)).card :=
  mult_of_lt (lt_of_lt_mult i) ▸ i.isLt

/-- The profile of a new cell of grade `k + 1` is in the catalogue at the grade `k + 1`. -/
theorem entry_mem_of_lt_mult {k : Fin 4} (i : Fin (mult cat J k)) :
    entry cat ((k : ℕ) + 1) i ∈ cat ((k : ℕ) + 1) :=
  entry_mem (lt_card_of_lt_mult i)

/-- The new cell of grade `k + 1` with index `i` carries the entry `i` of the catalogue at the
grade `k + 1`. -/
theorem cellProfile_multiNewCell (k : Fin 4) (i : Fin (mult cat J k)) :
    cellProfile cat J (multiNewCell I (mult cat J) k i) = entry cat ((k : ℕ) + 1) i := by
  match k, i with
  | ⟨0, _⟩, i =>
    have hi : (i : ℕ) < mult cat J 0 := i.isLt
    -- The index of the new cell, as a natural number.
    change cellProfile cat J (I.amalgam.card + i) = _
    rw [cellProfile, ite_eq_left (by omega)]
    congr 1; omega
  | ⟨1, _⟩, i =>
    have hi : (i : ℕ) < mult cat J 1 := i.isLt
    -- The index of the new cell, as a natural number.
    change cellProfile cat J (I.amalgam.card + mult cat J 0 + i) = _
    rw [cellProfile, ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 1; omega
  | ⟨2, _⟩, i =>
    have hi : (i : ℕ) < mult cat J 2 := i.isLt
    -- The index of the new cell, as a natural number.
    change cellProfile cat J (I.amalgam.card + mult cat J 0 + mult cat J 1 + i) = _
    rw [cellProfile, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 1; omega
  | ⟨3, _⟩, i =>
    -- The index of the new cell, as a natural number.
    change cellProfile cat J (I.amalgam.card + mult cat J 0 + mult cat J 1 + mult cat J 2 + i) = _
    rw [cellProfile, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    congr 1; omega

/-- The value of a new cell index is at least the number of cells of the amalgam. -/
theorem le_val_multiNewCell (k : Fin 4) (i : Fin (mult cat J k)) :
    I.amalgam.card ≤ (multiNewCell I (mult cat J) k i : ℕ) := by
  match k, i with
  | ⟨0, _⟩, i => exact Nat.le_add_right _ _
  | ⟨1, _⟩, i =>
    -- The index of the new cell, as a natural number.
    change _ ≤ I.amalgam.card + mult cat J 0 + i; omega
  | ⟨2, _⟩, i =>
    -- The index of the new cell, as a natural number.
    change _ ≤ I.amalgam.card + mult cat J 0 + mult cat J 1 + i; omega
  | ⟨3, _⟩, i =>
    -- The index of the new cell, as a natural number.
    change _ ≤ I.amalgam.card + mult cat J 0 + mult cat J 1 + mult cat J 2 + i; omega

/-- **The row of a new cell at an old cell** is its profile there. -/
theorem rows_multiOldCell (k : Fin 4) (i : ℕ) (d : Fin I.amalgam.card) :
    rows cat B J k i (multiOldCell I (mult cat J) d) = entry cat ((k : ℕ) + 1) i d := by
  rw [rows, dite_eq_left (show (multiOldCell I (mult cat J) d : ℕ) < I.amalgam.card from d.isLt)]
  rfl

/-- **The row of a new cell at a new cell** is the agreement height of their profiles in the cut
grid. -/
theorem rows_multiNewCell (k : Fin 4) (i : ℕ) (k' : Fin 4) (i' : Fin (mult cat J k')) :
    rows cat B J k i (multiNewCell I (mult cat J) k' i') =
      agreementHeight (grid 3 B) (entry cat ((k : ℕ) + 1) i) (entry cat ((k' : ℕ) + 1) i') := by
  rw [rows, dite_eq_right (fun h ↦ absurd h (not_lt.mpr (le_val_multiNewCell k' i'))),
    cellProfile_multiNewCell]

/-! ### Field labellings -/

variable (cat B J) in
/-- The **field labelling** of `L` and `P`: `L` at the old cells, and at a new cell the agreement
height of `P` and its profile in the cut grid. -/
noncomputable def fieldLabelling (L P : Profile I) (z : Fin (multiCard I (mult cat J))) :
    Label.{u} :=
  if hz : (z : ℕ) < I.amalgam.card then L ⟨z, hz⟩
  else agreementHeight (grid 3 B) P (cellProfile cat J z)

/-- The field labelling at an old cell. -/
theorem fieldLabelling_multiOldCell (L P : Profile I) (d : Fin I.amalgam.card) :
    fieldLabelling cat B J L P (multiOldCell I (mult cat J) d) = L d := by
  rw [fieldLabelling,
    dite_eq_left (show (multiOldCell I (mult cat J) d : ℕ) < I.amalgam.card from d.isLt)]
  rfl

/-- The field labelling at a new cell: the agreement height of `P` and its profile. -/
theorem fieldLabelling_multiNewCell (L P : Profile I) (k : Fin 4) (i : Fin (mult cat J k)) :
    fieldLabelling cat B J L P (multiNewCell I (mult cat J) k i) =
      agreementHeight (grid 3 B) P (entry cat ((k : ℕ) + 1) i) := by
  rw [fieldLabelling, dite_eq_right (fun h ↦ absurd h (not_lt.mpr (le_val_multiNewCell k i))),
    cellProfile_multiNewCell]

/-- The members of the cut grid are at most its ceiling `ω * B + 3`. -/
theorem agreementHeight_le_ceiling (P Q : Profile I) :
    agreementHeight (grid 3 B) P Q ≤ gridPoint 3 B :=
  le_gridPoint_of_mem_grid (agreementHeight_spec (bot_mem_grid 3 _) P Q).1

/-- A profile has the ceiling of the cut grid as agreement height with itself. -/
theorem agreementHeight_self_eq (P : Profile I) :
    agreementHeight (grid 3 B) P P = gridPoint 3 B :=
  agreementHeight_self (gridPoint_mem_grid le_rfl) (fun _ hx ↦ le_gridPoint_of_mem_grid hx) P

/-- **The field labelling is lawful below `(univ, K)`, `K ≤ 3`.**  Let `L` be lawful below `(C, K)`
and `(D, K)`, at most the ceiling of the cut grid, and equal to `P` at the cells of grade at most
`J`, and let `P` be an entry of the catalogue at every grade `1 ≤ j ≤ J`.  The row of the new
cell of a profile `P'` reads by `P'` and the field labelling reads by `P`: the two agree capped at
the agreement height of `P` and `P'`, the label of that cell, at the old cells by its definition
and at the new cells by the ultrametric inequality
(`Label.agreementHeight_tri`); availability into `(univ, j)` is given by the cell of `P`, whose
label is the ceiling. -/
theorem isLawfulBelow_fieldLabelling {K : ℕ} (hK : K ≤ 3) {L P : Profile I}
    (hLC : I.amalgam.rows.IsLawfulBelow (coatomC, K) fun d ↦ L d)
    (hLD : I.amalgam.rows.IsLawfulBelow (coatomD, K) fun d ↦ L d)
    (hLP : ∀ d, I.amalgam.toCellScheme.grade d ≤ J → L d = P d)
    (hL : ∀ d, L d ≤ gridPoint 3 B)
    (hP : ∀ j, 1 ≤ j → j ≤ J → P ∈ cat j) :
    (scheme cat B J).rows.IsLawfulBelow ((univ : Finset (Fin 5)), K)
      fun z ↦ fieldLabelling cat B J L P z := by
  classical
  have hold (X : Finset (Fin 5)) (hX : X ≠ univ)
      (hLB : I.amalgam.rows.IsLawfulBelow (X, K) fun d ↦ L d) :
      (scheme cat B J).rows.IsLawfulBelow (X, K) fun z ↦ fieldLabelling cat B J L P z := by
    refine (isLawfulBelow_multiOldCell_iff hX).mpr ?_
    simpa only [fieldLabelling_multiOldCell] using hLB
  obtain ⟨hoC, hlC, haC⟩ := Rows.isLawfulBelow_iff_forall.mp (hold coatomC (by decide) hLC)
  obtain ⟨hoD, hlD, haD⟩ := Rows.isLawfulBelow_iff_forall.mp (hold coatomD (by decide) hLD)
  have hceil (z : Fin (multiCard I (mult cat J))) :
      fieldLabelling cat B J L P z ≤ gridPoint 3 B := by
    rcases multiCell_cases (r := rows cat B J) z with ⟨d, rfl⟩ | ⟨k, i, rfl⟩
    · rw [fieldLabelling_multiOldCell]; exact hL d
    · rw [fieldLabelling_multiNewCell]; exact agreementHeight_le_ceiling _ _
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun z hz ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · rcases multiCell_cases (r := rows cat B J) z with ⟨d, rfl⟩ | ⟨k, i, rfl⟩
    · rcases mem_below_coatom_of_ne_multi hz (scope_multiOldCell_ne d) with h | h
      exacts [hoC _ h, hoD _ h]
    · rw [fieldLabelling_multiNewCell]
      exact (isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid 3 _) _ _).1).mono
        (hz.2.trans hK)
  · rcases multiCell_cases (r := rows cat B J) s with ⟨d, rfl⟩ | ⟨k, i, rfl⟩
    · rcases mem_below_coatom_of_ne_multi hs (scope_multiOldCell_ne d) with h | h
      exacts [hlC _ h, hlD _ h]
    · have hkJ := lt_of_lt_mult i
      have hκv : IsSelfVisible ((k : ℕ) + 1)
          (agreementHeight (grid 3 B) P (entry cat ((k : ℕ) + 1) i)) :=
        (isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid 3 _) _ _).1).mono
          (by have := hs.2; rw [gradedIndex_multiNewCell] at this; exact this.trans hK)
      refine ⟨constStepSuppressor ((k : ℕ) + 1) _, id,
        ⟨antitone_constStepSuppressor _ _, isSelfVisible_constStepSuppressor hκv, rfl,
          monotone_id, fun _ _ _ _ _ ↦ rfl⟩, fun t ↦ ?_⟩
      have htk : (scheme cat B J).toCellScheme.grade t ≤ (k : ℕ) + 1 :=
        t.2.2.trans_eq (congrArg Prod.snd (gradedIndex_multiNewCell (r := rows cat B J) k i))
      rw [row_multiNewCell, constStepSuppressor_of_le _ htk, id]
      obtain ⟨t, ht⟩ := t
      -- Beta-reduce the capped target at the cell `t`.
      dsimp only
      rw [fieldLabelling_multiNewCell]
      rcases multiCell_cases (r := rows cat B J) t with ⟨d, rfl⟩ | ⟨k', i', rfl⟩
      · rw [grade_multiOldCell] at htk
        rw [fieldLabelling_multiOldCell, rows_multiOldCell, hLP d (by omega)]
        exact (agreementHeight_spec (bot_mem_grid 3 _) _ _).2 d
      · rw [fieldLabelling_multiNewCell, rows_multiNewCell]
        exact agreementHeight_tri (bot_mem_grid 3 _) _ _ _
  · rcases multiCell_cases (r := rows cat B J) t with ⟨d, rfl⟩ | ⟨k, i, rfl⟩
    · rcases mem_below_coatom_of_ne_multi ht (scope_multiOldCell_ne d) with h | h
      exacts [haC s _ h hst hg, haD s _ h hst hg]
    · have hkJ := lt_of_lt_mult i
      obtain ⟨i', hi', he⟩ := exists_entry_eq (hP ((k : ℕ) + 1) (by omega) (by omega))
      have hi'm : i' < mult cat J k := by rwa [mult_of_lt hkJ]
      refine ⟨multiNewCell I (mult cat J) k ⟨i', hi'm⟩, by
        rw [gradedIndex_multiNewCell, gradedIndex_multiNewCell], ?_⟩
      rw [fieldLabelling_multiNewCell]
      -- The profile of the cell `u` is the entry `i'`.
      change _ ≤ agreementHeight (grid 3 B) P (entry cat ((k : ℕ) + 1) i')
      rw [he, agreementHeight_self_eq]
      exact hceil s

end VaughtConjecture.ProfileScheme
