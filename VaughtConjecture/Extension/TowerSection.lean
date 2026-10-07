/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Tower
import VaughtConjecture.Extension.UpperDecoder

/-!
# A section through the tower, decoded upward, with capped agreement

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`; here
one labelling of the lower layers of the tower for each labelling of the amalgam, fixed before any
cap).

Let `I` be a seed and `B` a block bound.  The **tower section** `Seed.towerSection I B j w` of a
labelling `w` of the amalgam is the labelling of the cells of `T j = I.tower j` built layer by
layer: `w` at the old cells, and at the new cells of the layer at the grade `j + 1` the field row
of the orbit code of the splice at `j + 1` of the section below, read by the upper decoder
(`Label.upperDecoder`), which reads the gaps between codes upward
(`Seed.layerSection`).  It is one function of `w`: it depends on no cap, prescription or ambient
labelling.

* **Literal** (`Seed.towerSection_towerEmbed`): it reads every old cell by `w`.
* **Lawful** (`Seed.isLawfulBelow_towerSection`): for `j ≤ 3`, if `w` is lawful below the two
  coatoms at the grade `j`, the section is lawful below `(univ, j)` in `T j`.  At each layer the
  section below and the old cells of the grade are glued (`CellScheme.Rows.IsLawfulBelow.glue₃`,
  as in `Seed.exists_isLawfulBelow_tower`), and the decoded field row is lawful by transport
  through the upper decoder, a witness that sends only bottom to bottom
  (`Scheme.isLawfulBelow_fieldLayer_upperDecoder`).
* **In the code grid** (`Seed.towerSection_mem_codeGrid`): for `j ≤ 3`, if `w` takes its values
  in `Label.codeGrid 3 B`, so does its section; in particular the section is short at `3` and
  never the formal top.
* **Capped agreement** (`Seed.min_towerSection_eq`): for `j ≤ 2`, if `w` takes its values in
  `Label.codeGrid 3 B` and `w'` agrees with `w` capped at a cap `h` self-visible and short at `3`,
  their sections agree capped at `h` at every cell of `T j`
  (`Label.min_upperDecoder_agreementHeight_eq` at each layer, the layers having grades `1, 2 < 3`).

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

/-! ### The decoded field row is lawful -/

namespace Scheme

variable {n : ℕ} (S : Scheme.{u} n) (k B : ℕ)
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- **The decoded field row is lawful below `(univ, k)`**: for `p` lawful below `(univ, k)` in `S`
and `k ≤ 3`, the field row of the orbit code of the splice of `p`, read by the upper decoder, is
lawful below `(univ, k)` in the field layer (the transport `IsLawfulBelow.map_of_apply_eq_bot`
through the upper decoder, a witness bounded by `k` sending only bottom to bottom). -/
theorem isLawfulBelow_fieldLayer_upperDecoder (hk : k ≤ 3) {p : Fin S.card → Label.{u}}
    (hp : S.rows.IsLawfulBelow (univ, k) fun d ↦ p d) :
    (S.fieldLayer k hS).rows.IsLawfulBelow (univ, k) fun x ↦
      upperDecoder k B (S.toCellScheme.splice k (fun _ ↦ ⊥) p)
        (S.fieldRow k (orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) p)) x) :=
  ((isLawful_fieldRow (hS := hS) (orbitCode_splice_bot_mem_catalogue hp)).isLawfulBelow _)
    |>.map_of_apply_eq_bot (fun x ↦ x.2.2) (isWitness_upperDecoder hk)
      fun _ ↦ eq_bot_of_upperDecoder_eq_bot

end Scheme

/-! ### The tower section -/

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (B : ℕ)

/-- The splice at the grade `j + 1` of a labelling of the cells of `T j`, bottom above. -/
noncomputable abbrev layerSplice (j : ℕ) (p : Fin (I.tower j).card → Label.{u}) :
    Fin (I.tower j).card → Label.{u} :=
  (I.tower j).toCellScheme.splice (j + 1) (fun _ ↦ ⊥) p

/-- The **decoded layer**: at the new cell `i` of the layer at the grade `j + 1`, the agreement
height of the orbit code of the splice of `p` with the catalogue entry of `i`, read by the upper
decoder. -/
noncomputable def layerSection (j : ℕ) (p : Fin (I.tower j).card → Label.{u})
    (i : Fin ((I.tower j).catalogue (j + 1)).card) : Label.{u} :=
  upperDecoder (j + 1) B (I.layerSplice j p)
    (agreementHeight ((I.tower j).fieldGrid (j + 1)) (orbitCode (j + 1) (I.layerSplice j p))
      ((I.tower j).catalogueEntry (j + 1) i))

/-- The **tower section** of a labelling `w` of the amalgam: `w` at `T 0`, and at `T (j + 1)`
the section at `T j` followed by its decoded layer. -/
noncomputable def towerSection : (j : ℕ) → (Fin I.amalgam.card → Label.{u}) →
    Fin (I.tower j).card → Label.{u}
  | 0, w => w
  | j + 1, w => Fin.append (towerSection j w) (I.layerSection B j (towerSection j w))

variable {I B}

/-- The tower section at an old cell of the layer `j + 1`. -/
@[simp] theorem towerSection_castAdd (j : ℕ) (w : Fin I.amalgam.card → Label.{u})
    (x : Fin (I.tower j).card) :
    I.towerSection B (j + 1) w (Fin.castAdd _ x) = I.towerSection B j w x :=
  Fin.append_left _ _ x

/-- The tower section at a new cell of the layer `j + 1`. -/
@[simp] theorem towerSection_natAdd (j : ℕ) (w : Fin I.amalgam.card → Label.{u})
    (i : Fin ((I.tower j).catalogue (j + 1)).card) :
    I.towerSection B (j + 1) w (Fin.natAdd _ i) = I.layerSection B j (I.towerSection B j w) i :=
  Fin.append_right _ _ i

/-- **The tower section is literal**: it reads every old cell by `w`. -/
theorem towerSection_towerEmbed : (j : ℕ) → (w : Fin I.amalgam.card → Label.{u}) →
    (d : Fin I.amalgam.card) → I.towerSection B j w (I.towerEmbed j d) = w d
  | 0, _, _ => rfl
  | j + 1, w, d => (towerSection_castAdd j w _).trans (towerSection_towerEmbed j w d)

variable (I B) in
/-- The labelling of the cells of `T (j + 1)` given by a labelling of the cells of `T j` and its
decoded layer. -/
noncomputable abbrev withLayer (j : ℕ) (p : Fin (I.tower j).card → Label.{u}) :
    Fin (I.tower (j + 1)).card → Label.{u} :=
  Fin.append p (I.layerSection B j p)

/-- **The decoded layer is lawful**: if a labelling of the cells of `T j` is lawful below
`(univ, j + 1)`, then with its decoded layer it is lawful below `(univ, j + 1)` in `T (j + 1)`,
for `j + 1 ≤ 3`. -/
theorem isLawfulBelow_withLayer {j : ℕ} (hj : j + 1 ≤ 3)
    {p : Fin (I.tower j).card → Label.{u}}
    (hp : (I.tower j).rows.IsLawfulBelow (univ, j + 1) fun d ↦ p d) :
    (I.tower (j + 1)).rows.IsLawfulBelow (univ, j + 1) fun x ↦ I.withLayer B j p x := by
  set W : Fin (I.tower (j + 1)).card → Label.{u} := fun z ↦
    upperDecoder (j + 1) B (I.layerSplice j p)
      ((I.tower j).fieldRow (j + 1) (orbitCode (j + 1) (I.layerSplice j p)) z) with hW
  have h : (I.tower (j + 1)).rows.IsLawfulBelow (univ, j + 1) fun x ↦ W x :=
    Scheme.isLawfulBelow_fieldLayer_upperDecoder (I.tower j) (j + 1) B
      (hS := I.not_univ_succ_le_tower j) hj hp
  refine (Rows.isLawfulBelow_congr fun x hx ↦ ?_).mp h
  induction x using Fin.addCases with
  | left e =>
    -- The two labellings at the old cell `e`, in the cells of `T j` followed by the layer.
    change upperDecoder (j + 1) B (I.layerSplice j p)
        ((I.tower j).fieldRow (j + 1) (orbitCode (j + 1) (I.layerSplice j p)) (Fin.castAdd _ e)) =
      Fin.append p (I.layerSection B j p) (Fin.castAdd _ e)
    rw [Scheme.fieldRow_castAdd, upperDecoder_orbitCode, Fin.append_left]
    exact CellScheme.splice_of_le
      ((Scheme.appendFullCellsScheme_grade_castAdd (I.tower j) (j + 1) _ e).symm.trans_le hx.2)
  | right i =>
    -- The two labellings at the new cell `i`, in the cells of `T j` followed by the layer.
    change upperDecoder (j + 1) B (I.layerSplice j p)
        ((I.tower j).fieldRow (j + 1) (orbitCode (j + 1) (I.layerSplice j p)) (Fin.natAdd _ i)) =
      Fin.append p (I.layerSection B j p) (Fin.natAdd _ i)
    rw [Scheme.fieldRow_natAdd, Fin.append_right]
    rfl

/-- **The tower section is lawful.**  Let `univ.erase x` and `univ.erase y` cover the cells of the
amalgam, and `w` be lawful below `(univ.erase x, j)` and `(univ.erase y, j)`, with `j ≤ 3`.  Then
the tower section of `w` is lawful below `(univ, j)` in `T j`. -/
theorem isLawfulBelow_towerSection {x y : Fin (m + 2)}
    (hcov : ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase x ∨
      I.amalgam.toCellScheme.scope d ⊆ univ.erase y) :
    (j : ℕ) → j ≤ 3 → {w : Fin I.amalgam.card → Label.{u}} →
    I.amalgam.rows.IsLawfulBelow (univ.erase x, j) (fun d ↦ w d) →
    I.amalgam.rows.IsLawfulBelow (univ.erase y, j) (fun d ↦ w d) →
    (I.tower j).rows.IsLawfulBelow (univ, j) fun t ↦ I.towerSection B j w t
  | 0, _, w, _, _ => by
    refine (Rows.isLawfulBelow_congr (w := fun _ ↦ ⊥) fun d hd ↦ absurd hd.2 ?_).mp
      (Rows.isLawfulBelow_const_bot _)
    have := I.amalgam.isWellFormed.isWellFormed.grade_pos d
    simp only [CellScheme.gradedIndex_snd]
    -- The cells of `T 0` are those of the amalgam, of positive grade.
    change ¬ I.amalgam.toCellScheme.grade d ≤ 0
    omega
  | j + 1, hj, w, hwx, hwy => by
    have hr₀ := isLawfulBelow_towerSection hcov j (by omega)
      (hwx.mono (X := (univ.erase x, j)) ⟨subset_rfl, Nat.le_succ j⟩)
      (hwy.mono (X := (univ.erase y, j)) ⟨subset_rfl, Nat.le_succ j⟩)
    set g := I.towerSection B j w with hg_def
    have hgw (d : Fin I.amalgam.card) : g (I.towerEmbed j d) = w d := towerSection_towerEmbed j w d
    have hgx : (I.tower j).rows.IsLawfulBelow (univ.erase x, j + 1) fun e ↦ g e := by
      rw [I.isLawfulBelow_tower_iff (ne_univ_erase x)]
      simpa only [hgw] using hwx
    have hgy : (I.tower j).rows.IsLawfulBelow (univ.erase y, j + 1) fun e ↦ g e := by
      rw [I.isLawfulBelow_tower_iff (ne_univ_erase y)]
      simpa only [hgw] using hwy
    have hg : (I.tower j).rows.IsLawfulBelow (univ, j + 1) fun e ↦ g e := by
      refine Rows.IsLawfulBelow.glue₃ hgx hr₀ hgy fun e he ↦ ?_
      by_cases hej : (I.tower j).toCellScheme.grade e ≤ j
      · exact .inr (.inl ⟨subset_univ _, hej⟩)
      · obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed j e ((I.tower_grade_le_or j e).resolve_left hej)
        have hd : I.amalgam.toCellScheme.grade d ≤ j + 1 :=
          (I.grade_towerEmbed j d).symm.trans_le he.2
        rcases hcov d with h | h
        · exact .inl (I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩)
        · exact .inr (.inr (I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩))
    exact isLawfulBelow_withLayer hj hg

/-- The splice of a labelling with values in the code grid has values in the code grid. -/
theorem layerSplice_mem_codeGrid {j : ℕ} {p : Fin (I.tower j).card → Label.{u}}
    (hp : ∀ t, p t ∈ codeGrid 3 B) (t : Fin (I.tower j).card) :
    I.layerSplice j p t ∈ codeGrid 3 B := by
  by_cases ht : (I.tower j).toCellScheme.grade t ≤ j + 1
  · rw [layerSplice, CellScheme.splice_of_le ht]; exact hp t
  · rw [layerSplice, CellScheme.splice_of_lt (not_le.mp ht)]; exact mem_insert_self _ _

/-- **The tower section takes values in the code grid** when `w` does, for `j ≤ 3`. -/
theorem towerSection_mem_codeGrid : (j : ℕ) → j ≤ 3 → {w : Fin I.amalgam.card → Label.{u}} →
    (∀ d, w d ∈ codeGrid 3 B) → ∀ t, I.towerSection B j w t ∈ codeGrid 3 B
  | 0, _, _, hw, t => hw t
  | j + 1, hj, w, hw, t => by
    induction t using Fin.addCases with
    | left t => rw [towerSection_castAdd]; exact towerSection_mem_codeGrid j (by omega) hw t
    | right i =>
      rw [towerSection_natAdd]
      exact upperDecoder_mem_codeGrid hj
        (layerSplice_mem_codeGrid (towerSection_mem_codeGrid j (by omega) hw))
        (agreementHeight_spec (bot_mem_grid _ _) _ _).1

/-- **Capped agreement of the tower sections**, for `j ≤ 2`: if `w` takes its values in the code
grid `codeGrid 3 B` and `w'` agrees with `w` capped at a cap `h` self-visible and short at `3`,
their tower sections agree capped at `h` at every cell of `T j`. -/
theorem min_towerSection_eq {h : Label.{u}} (hh : IsSelfVisible 3 h) (hs : IsShort 3 h) :
    (j : ℕ) → j ≤ 2 → {w w' : Fin I.amalgam.card → Label.{u}} → (∀ d, w d ∈ codeGrid 3 B) →
    (∀ d, min (w d) h = min (w' d) h) →
    ∀ t, min (I.towerSection B j w t) h = min (I.towerSection B j w' t) h
  | 0, _, _, _, _, hag, t => hag t
  | j + 1, hj, w, w', hw, hag, t => by
    have ih := min_towerSection_eq hh hs j (by omega) hw hag
    induction t using Fin.addCases with
    | left t => rw [towerSection_castAdd, towerSection_castAdd]; exact ih t
    | right i =>
      rw [towerSection_natAdd, towerSection_natAdd]
      have hsp (t : Fin (I.tower j).card) :
          min (I.layerSplice j (I.towerSection B j w) t) h =
            min (I.layerSplice j (I.towerSection B j w') t) h := by
        by_cases ht : (I.tower j).toCellScheme.grade t ≤ j + 1
        · rw [layerSplice, layerSplice, CellScheme.splice_of_le ht, CellScheme.splice_of_le ht]
          exact ih t
        · rw [layerSplice, layerSplice, CellScheme.splice_of_lt (not_le.mp ht),
            CellScheme.splice_of_lt (not_le.mp ht)]
      exact min_upperDecoder_agreementHeight_eq (by omega)
        (by simp only [Fintype.card_fin]; omega) hh hs
        (fun t ↦ le_gridPoint_of_mem_codeGrid
          (layerSplice_mem_codeGrid (towerSection_mem_codeGrid j (by omega) hw) t)) hsp _

end Seed

end VaughtConjecture
