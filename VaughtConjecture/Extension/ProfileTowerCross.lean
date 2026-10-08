/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ProfileTowerLayers

/-!
# Readers of a cell from the layers above it, in the profile tower

Roadmap, Layer 3, 3.1, (R6); the cross-layer non-domination of the cells of full scope of the
profile tower.

A cell `u` of the layer at the grade `j` reads a cell `c` of a lower layer through the section of
the level below: the upper decoder of the reading of `c` by the code at `j` of the profile of `u`,
down to the layer of `c`, where it is the agreement height of a code with the profile of `c`.
Compiled in this repository (theorem named):

* **The bottoms of a code** (`ProfileTower.code_eq_bot_iff`): the code at `k` of `P` is `⊥` exactly
  where `P` is, or above the grade `k`.
* **Differing bottoms give agreement height `⊥`** (`Label.agreementHeight_eq_bot_of_not_iff`).
* **The section is `⊥` at a cell whose rows differ in bottoms from the profile**
  (`ProfileTower.lvl_section_eq_bot`): in every good level, the section of `P` at a cell `c` of
  full scope and grade at least `3` is `⊥` as soon as some old cell of grade at most that of `c` is
  `⊥` in exactly one of `P` and the row of `c` (the upper decoder fixes `⊥`).
* **The rows of a cell are those of a profile** (`ProfileTower.lvl_exists_rowAt_eq`): a cell of
  full scope and grade `g ≥ 3` reads the old cells of grade at most `g` as some profile of the
  catalogue at `g`.
* **Cross separation** (`ProfileTower.CrossSeparating`, a named condition on the catalogues): for
  every profile `R_c` of the catalogue at `N` and every live old cell `a` of grade `j` avoiding the
  last point, some profile of the catalogue at `j` is not `⊥` at `a` and differs from `R_c` in
  bottoms at a cell of grade at most `N`.
* **Cross-layer readers** (`ProfileTower.CrossLayerReaders`, `ProfileTower.crossLayerReaders_lvl`):
  under cross separation, every cell `c` of full scope and grade `N ≥ 3` of a level, and every
  such old cell `a` of grade `j > N` up to the grade of the level, have a cell of graded index
  `(univ, j)` reading `c` as `⊥` and `a` not as `⊥`.

The change of bottoms is asked at a cell of grade at most `N`: the splice of the codes at the grades
from `j` down to `N` makes every cell above `N` bottom on the side of the reader, so a difference
there only arises from the profile of `c`.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme
open scoped Ordinal

namespace Label

variable {ι : Type*} [Fintype ι] {G : Finset Label.{u}} {a b : ι → Label.{u}}

/-- **Differing bottoms give agreement height `⊥`**: if exactly one of `a d`, `b d` is `⊥`, the
agreement height of `a` and `b` is `⊥`. -/
theorem agreementHeight_eq_bot_of_not_iff (hG : ⊥ ∈ G) {d : ι} (h : ¬ (a d = ⊥ ↔ b d = ⊥)) :
    agreementHeight G a b = ⊥ := by
  by_contra hne
  have hspec := (agreementHeight_spec hG a b).2 d
  apply h
  constructor
  · intro had
    rw [had, min_bot_left] at hspec
    exact (min_eq_bot.mp hspec.symm).resolve_right hne
  · intro hbd
    rw [hbd, min_bot_left, min_eq_bot] at hspec
    exact hspec.resolve_right hne

end Label

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The bottoms of a code**: the code at `k` of `P` is `⊥` exactly where `P` is or above `k`. -/
theorem code_eq_bot_iff {k : ℕ} {P : Prof I} {d : Fin I.amalgam.card} :
    code k P d = ⊥ ↔ P d = ⊥ ∨ k < I.amalgam.toCellScheme.grade d := by
  rw [code, orbitCode_eq_bot_iff]
  by_cases hd : I.amalgam.toCellScheme.grade d ≤ k
  · rw [hat_of_le hd]
    exact ⟨Or.inl, fun h ↦ h.resolve_right (not_lt.mpr hd)⟩
  · rw [hat_of_lt (not_le.mp hd)]
    exact ⟨fun _ ↦ Or.inr (not_le.mp hd), fun _ ↦ rfl⟩

/-- The row of the cell of a profile of the next layer at an old cell of grade at most the layer
is the profile. -/
theorem Lvl.Good.rowAt_nextS_natAdd_embed {g : ℕ} {L : Lvl I g} (hL : L.Good)
    (k : Fin (cat I (g + 1)).card) {d : Fin I.amalgam.card}
    (hd : I.amalgam.toCellScheme.grade d ≤ g + 1) :
    L.nextS.rowAt (Fin.natAdd _ k) (Fin.castAdd _ (L.embed d)) = entry I (g + 1) k d := by
  have hd' : Fin.castAdd (cat I (g + 1)).card (L.embed d) ∈ L.nextS.toCellScheme.below
      (L.nextS.toCellScheme.gradedIndex (Fin.natAdd L.S.card k)) := by
    rw [CellScheme.mem_below]
    change (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).gradedIndex _ ≤
      (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).gradedIndex _
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd,
      Scheme.appendFullCellsScheme_gradedIndex_natAdd, hL.gradedIndex_embed]
    exact ⟨subset_univ _, hd⟩
  rw [Scheme.rowAt_of_mem hd', Scheme.appendFullCells_row_natAdd]
  change L.Φ (entry I (g + 1) k) (Fin.castAdd _ (L.embed d)) = _
  exact hL.Φ_old _ d

/-- The row of the cell of a profile of the next layer at an old cell of the level is the section
of the profile there. -/
theorem Lvl.rowAt_nextS_natAdd_castAdd {g : ℕ} (L : Lvl I g) (k : Fin (cat I (g + 1)).card)
    {z : Fin L.S.card} (hz : L.S.toCellScheme.grade z ≤ g + 1) :
    L.nextS.rowAt (Fin.natAdd _ k) (Fin.castAdd _ z) = L.σ (entry I (g + 1) k) z := by
  have hz' : Fin.castAdd (cat I (g + 1)).card z ∈ L.nextS.toCellScheme.below
      (L.nextS.toCellScheme.gradedIndex (Fin.natAdd L.S.card k)) := by
    rw [CellScheme.mem_below]
    change (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).gradedIndex _ ≤
      (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).gradedIndex _
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd,
      Scheme.appendFullCellsScheme_gradedIndex_natAdd]
    exact ⟨subset_univ _, hz⟩
  rw [Scheme.rowAt_of_mem hz', Scheme.appendFullCells_row_natAdd]
  exact Lvl.Φ_castAdd _ _

/-- **The section is `⊥` at a cell whose rows differ in bottoms from the profile**, in every good
level. -/
theorem lvl_section_eq_bot (hm : 2 ≤ m) : ∀ i, i + 2 ≤ m → ∀ (c : Fin (lvl I i).S.card)
    (P : Prof I), (lvl I i).S.toCellScheme.scope c = univ →
    3 ≤ (lvl I i).S.toCellScheme.grade c →
    (∃ d, I.amalgam.toCellScheme.grade d ≤ (lvl I i).S.toCellScheme.grade c ∧
      ¬ (P d = ⊥ ↔ (lvl I i).S.rowAt c ((lvl I i).embed d) = ⊥)) →
    (lvl I i).σ P c = ⊥
  | 0, _ => fun c _ hc h3 _ ↦ by
      rcases (base I).inv c with h | h
      · exact absurd (h3.trans h) (by omega)
      · exact absurd hc h
  | i + 1, hi => fun c P ↦ by
      have hL := lvl_good (I := I) hm i (by omega)
      change Fin ((lvl I i).S.card + (cat I (i + 2 + 1)).card) at c
      induction c using Fin.addCases with
      | right k =>
        intro _ _ hd
        have hgk : (lvl I (i + 1)).S.toCellScheme.grade (Fin.natAdd _ k) = i + 2 + 1 :=
          Scheme.appendFullCellsScheme_grade_natAdd _ _ _ k
        rw [hgk] at hd
        obtain ⟨d, hdg, hd⟩ := hd
        change (lvl I i).nextσ P (Fin.natAdd _ k) = ⊥
        rw [Lvl.nextσ_of_le (by rw [Scheme.appendFullCellsScheme_grade_natAdd]),
          Lvl.Φ_natAdd]
        rw [agreementHeight_eq_bot_of_not_iff (bot_mem_grid _ _) (d := d), upperDecoderAt_bot]
        intro hiff
        apply hd
        rw [code_eq_bot_iff, or_iff_left (not_lt.mpr hdg)] at hiff
        change P d = ⊥ ↔ (lvl I i).nextS.rowAt (Fin.natAdd _ k)
          (Fin.castAdd _ ((lvl I i).embed d)) = ⊥
        rw [hL.rowAt_nextS_natAdd_embed k hdg]
        exact hiff
      | left c =>
        intro hc h3 hd
        have hsc : (lvl I (i + 1)).S.toCellScheme.scope (Fin.castAdd _ c) =
            (lvl I i).S.toCellScheme.scope c := Scheme.appendFullCellsScheme_scope_castAdd _ _ _ c
        have hgc : (lvl I (i + 1)).S.toCellScheme.grade (Fin.castAdd _ c) =
            (lvl I i).S.toCellScheme.grade c := Scheme.appendFullCellsScheme_grade_castAdd _ _ _ c
        rw [hsc] at hc
        rw [hgc] at h3 hd
        have hcg : (lvl I i).S.toCellScheme.grade c ≤ i + 2 :=
          ((lvl I i).inv c).resolve_right (not_not.mpr hc)
        change (lvl I i).nextσ P (Fin.castAdd _ c) = ⊥
        rw [Lvl.nextσ_of_le (by rw [Scheme.appendFullCellsScheme_grade_castAdd]; omega),
          Lvl.Φ_castAdd]
        obtain ⟨d, hdg, hd⟩ := hd
        rw [lvl_section_eq_bot hm i (by omega) c _ hc h3 ⟨d, hdg, fun hiff ↦ hd ?_⟩,
          upperDecoderAt_bot]
        rw [code_eq_bot_iff, or_iff_left (by omega)] at hiff
        change P d = ⊥ ↔ (lvl I i).nextS.rowAt (Fin.castAdd _ c)
          (Fin.castAdd _ ((lvl I i).embed d)) = ⊥
        rw [Scheme.rowAt_appendFullCells_castAdd]
        exact hiff

/-- **The rows of a cell of full scope are those of a profile**: a cell of full scope and grade
`g ≥ 3` of a good level reads the old cells of grade at most `g` as some profile of the catalogue
at `g`. -/
theorem lvl_exists_rowAt_eq (hm : 2 ≤ m) : ∀ i, i + 2 ≤ m → ∀ c : Fin (lvl I i).S.card,
    (lvl I i).S.toCellScheme.scope c = univ → 3 ≤ (lvl I i).S.toCellScheme.grade c →
    ∃ R ∈ cat I ((lvl I i).S.toCellScheme.grade c), ∀ d,
      I.amalgam.toCellScheme.grade d ≤ (lvl I i).S.toCellScheme.grade c →
        (lvl I i).S.rowAt c ((lvl I i).embed d) = R d
  | 0, _ => fun c hc h3 ↦ by
      rcases (base I).inv c with h | h
      · exact absurd (h3.trans h) (by omega)
      · exact absurd hc h
  | i + 1, hi => fun c ↦ by
      have hL := lvl_good (I := I) hm i (by omega)
      change Fin ((lvl I i).S.card + (cat I (i + 2 + 1)).card) at c
      induction c using Fin.addCases with
      | right k =>
        intro _ _
        have hgk : (lvl I (i + 1)).S.toCellScheme.grade (Fin.natAdd _ k) = i + 2 + 1 :=
          Scheme.appendFullCellsScheme_grade_natAdd _ _ _ k
        rw [hgk]
        exact ⟨entry I (i + 2 + 1) k, entry_mem k, fun d hd ↦
          hL.rowAt_nextS_natAdd_embed k hd⟩
      | left c =>
        intro hc h3
        have hsc : (lvl I (i + 1)).S.toCellScheme.scope (Fin.castAdd _ c) =
            (lvl I i).S.toCellScheme.scope c := Scheme.appendFullCellsScheme_scope_castAdd _ _ _ c
        have hgc : (lvl I (i + 1)).S.toCellScheme.grade (Fin.castAdd _ c) =
            (lvl I i).S.toCellScheme.grade c := Scheme.appendFullCellsScheme_grade_castAdd _ _ _ c
        rw [hsc] at hc
        rw [hgc] at h3 ⊢
        obtain ⟨R, hR, hRd⟩ := lvl_exists_rowAt_eq hm i (by omega) c hc h3
        refine ⟨R, hR, fun d hd ↦ ?_⟩
        change (lvl I i).nextS.rowAt (Fin.castAdd _ c) (Fin.castAdd _ ((lvl I i).embed d)) = _
        rw [Scheme.rowAt_appendFullCells_castAdd]
        exact hRd d hd

variable (I) in
/-- **Cross separation** from the grade `N` to the grade `j`: for every profile `R_c` of the
catalogue at `N` and every old cell `a` of grade `j` reading itself other than `⊥` and avoiding the
last point, some profile of the catalogue at `j` is not `⊥` at `a` and differs from `R_c` in
bottoms at a cell of grade at most `N`. -/
def CrossSeparating (N j : ℕ) : Prop :=
  ∀ R_c ∈ cat I N, ∀ a : Fin I.amalgam.card, I.amalgam.toCellScheme.grade a = j →
    I.amalgam.toScheme.rowAt a a ≠ ⊥ → Fin.last (m + 1) ∉ I.amalgam.toCellScheme.scope a →
      ∃ R ∈ cat I j, R a ≠ ⊥ ∧ ∃ d, I.amalgam.toCellScheme.grade d ≤ N ∧
        ¬ (R d = ⊥ ↔ R_c d = ⊥)

variable (I) in
/-- **Cross-layer readers** in a scheme `S` with old cells `e`, up to the grade `K`: every cell `c`
of full scope and grade `N ≥ 3` and every old cell `a` of grade `N < j ≤ K` reading itself other
than `⊥` and avoiding the last point, with cross separation from `N` to `j`, have a cell of graded
index `(univ, j)` reading `c` in a block strictly below its reading of `e a`. -/
def CrossLayerReaders (S : Scheme.{u} (m + 2)) (e : Fin I.amalgam.card → Fin S.card) (K : ℕ) :
    Prop :=
  ∀ c, S.toCellScheme.scope c = univ → 3 ≤ S.toCellScheme.grade c →
    ∀ a, S.toCellScheme.grade c < I.amalgam.toCellScheme.grade a →
      I.amalgam.toCellScheme.grade a ≤ K → I.amalgam.toScheme.rowAt a a ≠ ⊥ →
      Fin.last (m + 1) ∉ I.amalgam.toCellScheme.scope a →
      CrossSeparating I (S.toCellScheme.grade c) (I.amalgam.toCellScheme.grade a) →
        ∃ u, S.toCellScheme.gradedIndex u =
            ((univ : Finset (Fin (m + 2))), I.amalgam.toCellScheme.grade a) ∧
          LowerBlock (S.rowAt u c) (S.rowAt u (e a))

/-- **Appending cells of full scope keeps the cross-layer readers of the old cells.** -/
theorem crossLayerReaders_castAdd {S : Scheme.{u} (m + 2)} {e : Fin I.amalgam.card → Fin S.card}
    {K k M : ℕ} {r : Fin M → Fin (S.card + M) → Label.{u}}
    {h : ∀ d, ¬ ((univ : Finset (Fin (m + 2))), k) ≤ S.toCellScheme.gradedIndex d}
    (hS : CrossLayerReaders I S e K) (c : Fin S.card)
    (hc : S.toCellScheme.scope c = univ) (h3 : 3 ≤ S.toCellScheme.grade c)
    (a : Fin I.amalgam.card) (hca : S.toCellScheme.grade c < I.amalgam.toCellScheme.grade a)
    (haK : I.amalgam.toCellScheme.grade a ≤ K) (hlive : I.amalgam.toScheme.rowAt a a ≠ ⊥)
    (hlast : Fin.last (m + 1) ∉ I.amalgam.toCellScheme.scope a)
    (hsep : CrossSeparating I (S.toCellScheme.grade c) (I.amalgam.toCellScheme.grade a)) :
    ∃ u, (S.appendFullCells k M r h).toCellScheme.gradedIndex u =
        ((univ : Finset (Fin (m + 2))), I.amalgam.toCellScheme.grade a) ∧
      LowerBlock ((S.appendFullCells k M r h).rowAt u (Fin.castAdd M c))
        ((S.appendFullCells k M r h).rowAt u (Fin.castAdd M (e a))) := by
  obtain ⟨u, hu, hlb⟩ := hS c hc h3 a hca haK hlive hlast hsep
  refine ⟨Fin.castAdd M u, ?_, ?_⟩
  · rw [← hu]
    exact Scheme.appendFullCellsScheme_gradedIndex_castAdd S k M u
  · rw [Scheme.rowAt_appendFullCells_castAdd, Scheme.rowAt_appendFullCells_castAdd]
    exact hlb

/-- **Cross-layer readers in every good level**, up to its grade. -/
theorem crossLayerReaders_lvl (hm : 2 ≤ m) :
    ∀ i, i + 2 ≤ m → CrossLayerReaders I (lvl I i).S (lvl I i).embed (i + 2)
  | 0, _ => fun c hc h3 ↦ by
      rcases (base I).inv c with h | h
      · exact absurd (h3.trans h) (by omega)
      · exact absurd hc h
  | i + 1, hi => fun c ↦ by
      have hL := lvl_good (I := I) hm i (by omega)
      have hS := crossLayerReaders_lvl hm i (by omega)
      change Fin ((lvl I i).S.card + (cat I (i + 2 + 1)).card) at c
      induction c using Fin.addCases with
      | right k =>
        intro _ _ a hca haK
        have hgk : (lvl I (i + 1)).S.toCellScheme.grade (Fin.natAdd _ k) = i + 2 + 1 :=
          Scheme.appendFullCellsScheme_grade_natAdd _ _ _ k
        omega
      | left c =>
        intro hc h3 a hca haK hlive hlast hsep
        have hsc : (lvl I (i + 1)).S.toCellScheme.scope (Fin.castAdd _ c) =
            (lvl I i).S.toCellScheme.scope c := Scheme.appendFullCellsScheme_scope_castAdd _ _ _ c
        have hgc : (lvl I (i + 1)).S.toCellScheme.grade (Fin.castAdd _ c) =
            (lvl I i).S.toCellScheme.grade c := Scheme.appendFullCellsScheme_grade_castAdd _ _ _ c
        rw [hsc] at hc
        rw [hgc] at h3 hca hsep
        have hcg : (lvl I i).S.toCellScheme.grade c ≤ i + 2 :=
          ((lvl I i).inv c).resolve_right (not_not.mpr hc)
        rcases Nat.lt_or_ge (I.amalgam.toCellScheme.grade a) (i + 2 + 1) with hlt | hge
        · exact crossLayerReaders_castAdd (k := i + 2 + 1) (M := (cat I (i + 2 + 1)).card)
            (r := fun i' ↦ (lvl I i).Φ (entry I (i + 2 + 1) i')) (h := (lvl I i).not_le) hS c hc
            h3 a hca (by omega) hlive hlast hsep
        · have hag : I.amalgam.toCellScheme.grade a = i + 2 + 1 := by omega
          obtain ⟨R_c, hR_c, hrow⟩ := lvl_exists_rowAt_eq hm i (by omega) c hc h3
          rw [hag] at hsep
          obtain ⟨R, hR, hRa, d, hdg, hd⟩ := hsep R_c hR_c a hag hlive hlast
          obtain ⟨k, rfl⟩ := exists_entry_eq hR
          refine ⟨Fin.natAdd _ k, ?_, ?_⟩
          · rw [hag]
            exact Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ k
          · change LowerBlock ((lvl I i).nextS.rowAt (Fin.natAdd _ k) (Fin.castAdd _ c))
              ((lvl I i).nextS.rowAt (Fin.natAdd _ k) (Fin.castAdd _ ((lvl I i).embed a)))
            rw [(lvl I i).rowAt_nextS_natAdd_castAdd k (by omega),
              hL.rowAt_nextS_natAdd_embed k hag.le,
              lvl_section_eq_bot hm i (by omega) c _ hc h3 ⟨d, hdg, fun hiff ↦ hd ?_⟩]
            · exact ⟨bot_lt_iff_ne_bot.mpr hRa, fun μ i' j' _ h ↦
                absurd h.symm (WithBot.coe_ne_bot)⟩
            · rw [hrow d hdg] at hiff
              exact hiff

end ProfileTower

end VaughtConjecture
