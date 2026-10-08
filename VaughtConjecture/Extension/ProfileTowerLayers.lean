/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ProfileTowerReaders
import VaughtConjecture.Extension.ProfileTowerCompletion
import VaughtConjecture.Extension.BotKeeping
import VaughtConjecture.Extension.ProfileBotKeeping

/-!
# Readers of a cell within its layer, through the levels of the profile tower

Roadmap, Layer 3, 3.1, (R6); the same-layer non-domination of the cells of full scope of the
profile tower (`ProfileTower.lvl`) and of its top layer (`ProfileTower.Lvl.top`).

A cell of full scope and grade `g ≥ 3` of a level is the cell of a profile `R_c` of the catalogue
at `g` (`ProfileTower.Lvl.nextS`), kept with its rows by the later layers.  Compiled in this
repository (theorem named):

* **Layer separation** (`ProfileTower.LayerSeparating`, a named condition on the catalogue at a
  grade): for every profile `R_c` of the catalogue and every old cell `a` of that grade, reading
  itself other than `⊥` and avoiding the last point, some profile `R` of the catalogue is at least
  `ω * β` at `a` and agrees with `R_c` only below `ω * β`.  Its strict form (`R_c` itself below
  `ω * β` at `a`, `ProfileTower.LayerSeparatingStrict`) implies it
  (`ProfileTower.LayerSeparatingStrict.layerSeparating`) and is refuted at every grade carrying
  such a cell (`ProfileTower.not_layerSeparatingStrict`: the profile largest at `a`).
* **Same-layer readers** (`ProfileTower.SameLayerReaders`, `ProfileTower.sameLayerReaders_lvl`,
  `ProfileTower.Lvl.sameLayerReaders_top`): in every good level, and in the top layer at the grades
  at most `m`, every cell `c` of full scope and grade `g ≥ 3` with layer separation at `g` has, for
  each such old cell `a`, a cell of graded index `(univ, g)` reading `c` in a block strictly below
  its reading of `a` (`ProfileTower.Lvl.Good.lowerBlock_rowAt_nextS` in the layer of `c`; the rows
  of the old cells are kept by the later layers, `Scheme.rowAt_appendFullCells_castAdd`).

Layer separation is not established here.  At a profile `R_c` largest at `a` among the catalogue
it asks for another profile with the same block at `a` disagreeing with `R_c` below that block.

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
/-- **Strict layer separation at the grade `g`**: for every profile `R_c` of the catalogue at `g`
and every old cell `a` of grade `g` reading itself other than `⊥` and avoiding the last point, some
profile of the catalogue is at least `ω * β` at `a`, where `R_c` is below `ω * β`.  It fails as
soon as such a cell exists (`ProfileTower.not_layerSeparatingStrict`). -/
def LayerSeparatingStrict (g : ℕ) : Prop :=
  ∀ (i : Fin (cat I g).card) (a : Fin I.amalgam.card), I.amalgam.toCellScheme.grade a = g →
    I.amalgam.toScheme.rowAt a a ≠ ⊥ → Fin.last (m + 1) ∉ I.amalgam.toCellScheme.scope a →
      ∃ R ∈ cat I g, ∃ β : Ordinal.{u}, entry I g i a < ((ω * β : Ordinal.{u}) : Label.{u}) ∧
        ((ω * β : Ordinal.{u}) : Label.{u}) ≤ R a

variable (I : Seed.{u} α m) in
/-- **Layer separation at the grade `g`**: for every profile `R_c` of the catalogue at `g` and
every old cell `a` of grade `g` reading itself other than `⊥` and avoiding the last point, some
profile `R` of the catalogue is at least `ω * β` at `a` and agrees with `R_c` (capped, in the grid
of the layer) only below `ω * β`.  This is what a reader in the layer of the cell of `R_c` needs
(`ProfileTower.Lvl.Good.lowerBlock_rowAt_nextS_of_agreementHeight`). -/
def LayerSeparating (g : ℕ) : Prop :=
  ∀ (i : Fin (cat I g).card) (a : Fin I.amalgam.card), I.amalgam.toCellScheme.grade a = g →
    I.amalgam.toScheme.rowAt a a ≠ ⊥ → Fin.last (m + 1) ∉ I.amalgam.toCellScheme.scope a →
      ∃ R ∈ cat I g, ∃ β : Ordinal.{u},
        agreementHeight (grid g (bound I)) R (entry I g i) < ((ω * β : Ordinal.{u}) : Label.{u}) ∧
        ((ω * β : Ordinal.{u}) : Label.{u}) ≤ R a

/-- **Strict layer separation gives layer separation.** -/
theorem LayerSeparatingStrict.layerSeparating {I : Seed.{u} α m} {g : ℕ}
    (h : LayerSeparatingStrict I g) : LayerSeparating I g := fun i a ha hlive hlast ↦ by
  obtain ⟨R, hR, β, hlow, hhigh⟩ := h i a ha hlive hlast
  exact ⟨R, hR, β, agreementHeight_lt_of_lt_le (bot_mem_grid _ _) hlow hhigh, hhigh⟩

/-- **Strict layer separation fails** at every grade carrying an old cell reading itself other
than `⊥` and avoiding the last point: the catalogue is finite, and its profile largest at that cell
has no profile of the catalogue above it there. -/
theorem not_layerSeparatingStrict {I : Seed.{u} α m} {g : ℕ} {a : Fin I.amalgam.card}
    (ha : I.amalgam.toCellScheme.grade a = g) (hlive : I.amalgam.toScheme.rowAt a a ≠ ⊥)
    (hlast : Fin.last (m + 1) ∉ I.amalgam.toCellScheme.scope a) : ¬ LayerSeparatingStrict I g := by
  intro h
  obtain ⟨Rmax, hRmax, hmax⟩ := (cat I g).exists_max_image (fun R ↦ R a) ⟨_, bot_mem_cat (I := I) g⟩
  obtain ⟨i, hi⟩ := exists_entry_eq hRmax
  obtain ⟨R, hR, β, hlow, hhigh⟩ := h i a ha hlive hlast
  rw [hi] at hlow
  exact absurd ((hlow.trans_le hhigh).trans_le (hmax R hR)) (lt_irrefl _)

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
        obtain ⟨R, hR, β, hag, hhigh⟩ := hsep i a ha hlive hlast
        obtain ⟨i', rfl⟩ := exists_entry_eq hR
        refine ⟨Fin.natAdd _ i', Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i', ?_⟩
        exact hL.lowerBlock_rowAt_nextS_of_agreementHeight i' i ha.le hag hhigh

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

/-- **Appending one cell of full scope above the grade `m` keeps the same-layer readers.** -/
theorem sameLayerReaders_appendFullCell {S : Scheme.{u} (m + 2)}
    {e : Fin I.amalgam.card → Fin S.card} {k : ℕ} {r : Fin (S.card + 1) → Label.{u}}
    {h : ∀ d, ¬ ((univ : Finset (Fin (m + 2))), k) ≤ S.toCellScheme.gradedIndex d} (hk : m < k)
    (hS : SameLayerReaders I S e) :
    SameLayerReaders I (S.appendFullCell k r h) fun a ↦ (e a).castSucc := fun c ↦ by
  induction c using Fin.lastCases with
  | last =>
    intro _ _ hcm
    have : (S.appendFullCell k r h).toCellScheme.grade (Fin.last _) = k :=
      Scheme.appendFullCellScheme_grade_last S k
    omega
  | cast c =>
    have hsc : (S.appendFullCell k r h).toCellScheme.scope c.castSucc = S.toCellScheme.scope c :=
      Scheme.appendFullCellScheme_scope_castSucc S k c
    have hgr : (S.appendFullCell k r h).toCellScheme.grade c.castSucc = S.toCellScheme.grade c :=
      Scheme.appendFullCellScheme_grade_castSucc S k c
    rw [hsc, hgr]
    intro hc h3 hcm hsep a ha hlive hlast
    obtain ⟨u, hu, hlb⟩ := hS c hc h3 hcm hsep a ha hlive hlast
    refine ⟨u.castSucc, ?_, ?_⟩
    · rw [← hu]
      exact Scheme.appendFullCellScheme_gradedIndex_castSucc S k u
    · rw [Scheme.rowAt_appendFullCell_castSucc, Scheme.rowAt_appendFullCell_castSucc]
      exact hlb

variable (I) in
/-- **The completion of the profile tower** of a seed on `j + 5` points: the completion below the
full grade over the good level at the grade `j + 3` (`ProfileTower.Lvl.Good.completion`); its
scheme is the top layer of that level. -/
noncomputable def towerCompletion {j : ℕ} (I : Seed.{u} α (j + 3)) :
    CompletionBelowFullGrade I :=
  ((lvl_good (I := I) (by omega) j (by omega)).next (by omega)).completion
    (lvl_good (I := I) (by omega) j (by omega)).hasBotExtension_next (by omega)

/-- The scheme of the completion of the profile tower is the top layer of its last level. -/
theorem towerCompletion_scheme {j : ℕ} (I : Seed.{u} α (j + 3)) :
    (towerCompletion I).scheme = (lvl I (j + 1)).top := rfl

/-- **Same-layer readers in the completion of the profile tower**, with the apex. -/
theorem sameLayerReaders_towerCompletion {j : ℕ} (I : Seed.{u} α (j + 3))
    (hα : Order.IsSuccPrelimit α) :
    SameLayerReaders I ((towerCompletion I).completion hα).toScheme
      fun a ↦ ((towerCompletion I).embed a).castSucc :=
  sameLayerReaders_appendFullCell (h := (towerCompletion I).isLegalBelowFullGrade.not_le)
    (by omega)
    ((lvl I (j + 1)).sameLayerReaders_top (sameLayerReaders_lvl (by omega) (j + 1) (by omega)))

/-- **A bot-keeping completion with the profile tower exposed**: every seed on `j + 5` points has a
bot-keeping completion below the full grade (as `Seed.exists_botKeeping`) on the scheme of the
completion of the profile tower, whose completions at every limit stage have the same-layer
readers.  The labelling is that of `ProfileTower.exists_botKeeping_of_three_le`; the scheme and
the old cells are those of `ProfileTower.towerCompletion`. -/
theorem exists_botKeeping_tower {j : ℕ} (I : Seed.{u} α (j + 3)) :
    ∃ F : CompletionBelowFullGrade I, F.BotKeeping ∧ F.scheme = (lvl I (j + 1)).top ∧
      ∀ hα : Order.IsSuccPrelimit α,
        SameLayerReaders I (F.completion hα).toScheme fun a ↦ (F.embed a).castSucc := by
  have hL := lvl_good (I := I) (by omega) j (by omega)
  have hN := hL.next (by omega)
  have hS := hL.sectionBotKeeping_next (lvl_sectionBotKeeping I (by omega) j (by omega))
  obtain ⟨p, hp, hpe, hpb⟩ := hN.exists_botKeeping hS
  obtain ⟨r, hr, hrp, hrb⟩ :=
    Scheme.exists_botKeeping_fieldLayer (hS := (lvl I j).next.not_le) hp hpb
  set F₀ := towerCompletion I
  refine ⟨{ F₀ with label := r, isLawful := hr, label_embed := fun d ↦ ?_ }, hrb, rfl,
    fun hα ↦ ?_⟩
  · change r (Fin.castAdd _ ((lvl I j).next.embed d)) = I.amalgam.label d
    rw [hrp]
    exact hpe d
  · exact sameLayerReaders_appendFullCell (h := (towerCompletion I).isLegalBelowFullGrade.not_le)
      (by omega)
      ((lvl I (j + 1)).sameLayerReaders_top (sameLayerReaders_lvl (by omega) (j + 1) (by omega)))

end ProfileTower

end VaughtConjecture
