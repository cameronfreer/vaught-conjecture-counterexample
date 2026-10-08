/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ProfileTowerReaders
import VaughtConjecture.Extension.ProfileTowerCompletion
import VaughtConjecture.Extension.BotKeeping

/-!
# Readers of a cell within its layer, through the levels of the profile tower

Roadmap, Layer 3, 3.1, (R6); the same-layer non-domination of the cells of full scope of the
profile tower (`ProfileTower.lvl`) and of its top layer (`ProfileTower.Lvl.top`).

A cell of full scope and grade `g ≥ 3` of a level is the cell of a profile `R_c` of the catalogue
at `g` (`ProfileTower.Lvl.nextS`), kept with its rows by the later layers.  Compiled in this
repository (theorem named):

* **Layer separation** (`ProfileTower.LayerSeparating`, a named condition on the catalogue at a
  grade): for every profile `R_c` of the catalogue and every old cell `a` of that grade, reading
  itself other than `⊥` and avoiding the last point, some profile of the catalogue is at least
  `ω * β` at `a` where `R_c` is below.
* **Same-layer readers** (`ProfileTower.SameLayerReaders`, `ProfileTower.sameLayerReaders_lvl`,
  `ProfileTower.Lvl.sameLayerReaders_top`): in every good level, and in the top layer at the grades
  at most `m`, every cell `c` of full scope and grade `g ≥ 3` with layer separation at `g` has, for
  each such old cell `a`, a cell of graded index `(univ, g)` reading `c` in a block strictly below
  its reading of `a` (`ProfileTower.Lvl.Good.lowerBlock_rowAt_nextS` in the layer of `c`; the rows
  of the old cells are kept by the later layers, `Scheme.rowAt_appendFullCells_castAdd`).

Layer separation is not automatic: the catalogue consists of orbit codes, never `⊤`, and a profile
largest at `a` among the catalogue leaves no profile above it there.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme
open scoped Ordinal

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ}

variable (I : Seed.{u} α m) in
/-- **Layer separation at the grade `g`**: for every profile `R_c` of the catalogue at `g` and
every old cell `a` of grade `g` reading itself other than `⊥` and avoiding the last point, some
profile of the catalogue is at least `ω * β` at `a`, where `R_c` is below `ω * β`. -/
def LayerSeparating (g : ℕ) : Prop :=
  ∀ (i : Fin (cat I g).card) (a : Fin I.amalgam.card), I.amalgam.toCellScheme.grade a = g →
    I.amalgam.toScheme.rowAt a a ≠ ⊥ → Fin.last (m + 1) ∉ I.amalgam.toCellScheme.scope a →
      ∃ R ∈ cat I g, ∃ β : Ordinal.{u}, entry I g i a < ((ω * β : Ordinal.{u}) : Label.{u}) ∧
        ((ω * β : Ordinal.{u}) : Label.{u}) ≤ R a

variable {I : Seed.{u} α m}

variable (I) in
/-- **Same-layer readers** in a scheme `S` with old cells `e`: every cell `c` of full scope and
grade `3 ≤ g ≤ m` with layer separation at `g` has, for every old cell `a` of grade `g` reading
itself other than `⊥` and avoiding the last point, a cell of graded index `(univ, g)` reading `c`
in a block strictly below its reading of `e a`. -/
def SameLayerReaders (S : Scheme.{u} (m + 2)) (e : Fin I.amalgam.card → Fin S.card) : Prop :=
  ∀ c, S.toCellScheme.scope c = univ → 3 ≤ S.toCellScheme.grade c →
    S.toCellScheme.grade c ≤ m → LayerSeparating I (S.toCellScheme.grade c) →
    ∀ a, I.amalgam.toCellScheme.grade a = S.toCellScheme.grade c →
      I.amalgam.toScheme.rowAt a a ≠ ⊥ → Fin.last (m + 1) ∉ I.amalgam.toCellScheme.scope a →
        ∃ u, S.toCellScheme.gradedIndex u =
            ((univ : Finset (Fin (m + 2))), S.toCellScheme.grade c) ∧
          LowerBlock (S.rowAt u c) (S.rowAt u (e a))

/-- **Appending cells of full scope keeps the same-layer readers of the old cells.** -/
theorem sameLayerReaders_castAdd {S : Scheme.{u} (m + 2)} {e : Fin I.amalgam.card → Fin S.card}
    {k M : ℕ} {r : Fin M → Fin (S.card + M) → Label.{u}}
    {h : ∀ d, ¬ ((univ : Finset (Fin (m + 2))), k) ≤ S.toCellScheme.gradedIndex d}
    (hS : SameLayerReaders I S e) (c : Fin S.card) :
    (S.appendFullCells k M r h).toCellScheme.scope (Fin.castAdd M c) = univ →
    3 ≤ (S.appendFullCells k M r h).toCellScheme.grade (Fin.castAdd M c) →
    (S.appendFullCells k M r h).toCellScheme.grade (Fin.castAdd M c) ≤ m →
    LayerSeparating I ((S.appendFullCells k M r h).toCellScheme.grade (Fin.castAdd M c)) →
    ∀ a, I.amalgam.toCellScheme.grade a =
        (S.appendFullCells k M r h).toCellScheme.grade (Fin.castAdd M c) →
      I.amalgam.toScheme.rowAt a a ≠ ⊥ → Fin.last (m + 1) ∉ I.amalgam.toCellScheme.scope a →
        ∃ u, (S.appendFullCells k M r h).toCellScheme.gradedIndex u =
            ((univ : Finset (Fin (m + 2))),
              (S.appendFullCells k M r h).toCellScheme.grade (Fin.castAdd M c)) ∧
          LowerBlock ((S.appendFullCells k M r h).rowAt u (Fin.castAdd M c))
            ((S.appendFullCells k M r h).rowAt u (Fin.castAdd M (e a))) := by
  have hsc : (S.appendFullCells k M r h).toCellScheme.scope (Fin.castAdd M c) =
      S.toCellScheme.scope c := Scheme.appendFullCellsScheme_scope_castAdd S k M c
  have hgr : (S.appendFullCells k M r h).toCellScheme.grade (Fin.castAdd M c) =
      S.toCellScheme.grade c := Scheme.appendFullCellsScheme_grade_castAdd S k M c
  rw [hsc, hgr]
  intro hc h3 hcm hsep a ha hlive hlast
  obtain ⟨u, hu, hlb⟩ := hS c hc h3 hcm hsep a ha hlive hlast
  refine ⟨Fin.castAdd M u, ?_, ?_⟩
  · rw [← hu]
    exact Scheme.appendFullCellsScheme_gradedIndex_castAdd S k M u
  · rw [Scheme.rowAt_appendFullCells_castAdd, Scheme.rowAt_appendFullCells_castAdd]
    exact hlb

/-- **Same-layer readers in every good level.** -/
theorem sameLayerReaders_lvl (hm : 2 ≤ m) :
    ∀ j, j + 2 ≤ m → SameLayerReaders I (lvl I j).S (lvl I j).embed
  | 0, _ => fun c hc h3 _ ↦ by
      rcases (base I).inv c with h | h
      · exact absurd (h3.trans h) (by omega)
      · exact absurd hc h
  | j + 1, hj => fun c ↦ by
      have hL := lvl_good (I := I) hm j (by omega)
      have hS := sameLayerReaders_lvl hm j (by omega)
      change Fin ((lvl I j).S.card + (cat I (j + 2 + 1)).card) at c
      induction c using Fin.addCases with
      | left c =>
        exact sameLayerReaders_castAdd (k := j + 2 + 1) (M := (cat I (j + 2 + 1)).card)
          (r := fun i ↦ (lvl I j).Φ (entry I (j + 2 + 1) i)) (h := (lvl I j).not_le) hS c
      | right i =>
        intro _ _ _ hsep a ha hlive hlast
        have hgi : (lvl I (j + 1)).S.toCellScheme.grade (Fin.natAdd _ i) = j + 2 + 1 :=
          Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i
        rw [hgi] at hsep ha ⊢
        obtain ⟨R, hR, β, hlow, hhigh⟩ := hsep i a ha hlive hlast
        obtain ⟨i', rfl⟩ := exists_entry_eq hR
        refine ⟨Fin.natAdd _ i', Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i', ?_⟩
        exact hL.lowerBlock_rowAt_nextS i' i ha.le hlow hhigh

/-- **Same-layer readers in the top layer**, at the grades at most `m`. -/
theorem Lvl.sameLayerReaders_top (N : Lvl I m) (hN : SameLayerReaders I N.S N.embed) :
    SameLayerReaders I N.top N.topEmbed := fun c ↦ by
  change Fin (N.S.card + (N.S.catalogue (m + 1)).card) at c
  induction c using Fin.addCases with
  | left c =>
    exact sameLayerReaders_castAdd (k := m + 1) (M := (N.S.catalogue (m + 1)).card)
      (r := fun i ↦ N.S.fieldRow (m + 1) (N.S.catalogueEntry (m + 1) i)) (h := N.not_le) hN c
  | right i =>
    intro _ _ hcm
    have : N.top.toCellScheme.grade (Fin.natAdd _ i) = m + 1 :=
      Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i
    omega

end ProfileTower

end VaughtConjecture
