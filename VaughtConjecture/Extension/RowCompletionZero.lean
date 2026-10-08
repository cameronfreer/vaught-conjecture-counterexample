/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AdmittedTower

/-!
# The completion on the catalogues of a predicate from every grade

The engine part of `VaughtConjecture.MainTheorem.H3Small` (branch `research/work-h3-small`),
copied with its declarations unchanged: the level at the grade `0` (`ProfileTower.base₀`), the
levels on a family from the grade `0` (`ProfileTower.lvlOn₀`), and the completion on the catalogues
of a predicate from every grade `N` (`Seed.exists_rowCompletion₀`), for every seed on at least
three points.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ}

variable (I : Seed.{u} α m) in
/-- **The level at the grade `0`**: the amalgam with the identity section. -/
noncomputable def base₀ : Lvl I 0 where
  S := I.tower 0
  σ := I.towerSection (bound I) 0
  embed := I.towerEmbed 0
  inv := I.tower_grade_le_or 0

variable {I : Seed.{u} α m}

/-- **The level at the grade `0` is good.** -/
theorem base₀_good : (base₀ I).Good where
  lowerEmb := I.isLowerEmbedding_tower 0
  scope_embed := I.scope_towerEmbed 0
  comap_rows := I.comap_rows_tower 0
  mem_range := I.mem_range_towerEmbed 0
  faces := I.faces_tower 0
  wf := I.isWellFormed_tower 0 (by omega)
  coded := I.isCoded_tower 0
  consistent := I.isConsistent_tower 0
  lawful P hP := Seed.isLawfulBelow_towerSection (B := bound I)
    (I.scope_subset_or (x := Fin.last (m + 1)) (y := Fin.castSucc (Fin.last m)) (by simp)
      (by simp) Seed.last_ne_castSucc) 0 (by omega) hP.1 hP.2
  mem _ hP z := hP z
  literal P d := Seed.towerSection_towerEmbed (B := bound I) 0 P d
  capAgree _ _ _ _ _ _ hag z := hag z
  readable Q _ _ z := isReadableAt_apply Q z
  lift := I.towerInvariant_zero
  complete _ hj0 hj := absurd hj (by omega)

/-! ### The levels on a family of catalogues from the grade `0` -/

variable (I) in
/-- **The levels on `D` from the grade `0`**: the level at the grade `j`, the level at the grade
`0`, then the next levels on `D`. -/
noncomputable def lvlOn₀ (D : ℕ → Finset (Prof I)) : (j : ℕ) → Lvl I j
  | 0 => base₀ I
  | j + 1 => (lvlOn₀ D j).nextOn (D (j + 1))

/-- **The levels on `D` from the grade `0` are good relative to `D`** up to the grade `m`, under
the downward clause and the lift provisions at the grades `0 < k ≤ m`. -/
theorem lvlOn₀_goodOn {D : ℕ → Finset (Prof I)} (hD : ∀ k, D k ⊆ cat I k)
    (hdown : ∀ k, ∀ R ∈ D (k + 1), code k R ∈ D k)
    (hbot : ∀ k, 0 < k → k ≤ m → ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      BotLiftProvisionIn (D k) k x)
    (hcap : ∀ k, 0 < k → k ≤ m → ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      CapLiftProvisionIn (D k) k x) :
    (j : ℕ) → j ≤ m → (lvlOn₀ I D j).GoodOn D
  | 0, _ => base₀_good.toGoodOn D
  | j + 1, hj => (lvlOn₀_goodOn hD hdown hbot hcap j (by omega)).nextOn (by omega) (hD _)
      (hdown _) (hbot _ (by omega) (by omega)) (hcap _ (by omega) (by omega))

/-- The rows of a level **read the catalogues of `D` at every grade**: the row of every cell of
full scope, read at the old cells, is the splice at its grade `j` of a profile of `D j`. -/
def Lvl.RowsInAll {g : ℕ} (D : ℕ → Finset (Prof I)) (L : Lvl I g) : Prop :=
  ∀ z j, L.S.toCellScheme.gradedIndex z = ((univ : Finset (Fin (m + 2))), j) →
    ∃ R ∈ D j, ∀ d, L.S.rowAt z (L.embed d) = hat I j R d

/-- **The next level on `D (g + 1)` reads the catalogues of `D` at every grade** when the level
does. -/
theorem Lvl.GoodOn.rowsInAll_nextOn {g : ℕ} {L : Lvl I g} {D : ℕ → Finset (Prof I)}
    (hL : L.GoodOn D) (hrows : L.RowsInAll D) : (L.nextOn (D (g + 1))).RowsInAll D := by
  intro z j hz
  induction z using Fin.addCases with
  | left e =>
    have he : L.S.toCellScheme.gradedIndex e = ((univ : Finset (Fin (m + 2))), j) :=
      (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e).symm.trans hz
    obtain ⟨R, hR, hrow⟩ := hrows e j he
    exact ⟨R, hR, fun d ↦ (rowAt_appendFullCells_castAdd
      (r := fun i ↦ L.ΦOn (D (g + 1)) (entryOn (D (g + 1)) i)) (h := L.not_le) e
      (L.embed d)).trans (hrow d)⟩
  | right i =>
    have hji : j = g + 1 := by
      have := congrArg Prod.snd hz
      change ((L.S.appendFullCellsScheme (g + 1) (D (g + 1)).card).gradedIndex
        (Fin.natAdd _ i)).2 = _ at this
      rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd] at this
      exact this.symm
    subst hji
    obtain ⟨R, hR, hrow⟩ := hL.rowAt_nextSOn (C := D (g + 1)) hz
    exact ⟨R, hR, hrow⟩

/-- **The levels on `D` from the grade `0` read the catalogues of `D` at every grade.** -/
theorem lvlOn₀_rowsInAll {D : ℕ → Finset (Prof I)} (hD : ∀ k, D k ⊆ cat I k)
    (hdown : ∀ k, ∀ R ∈ D (k + 1), code k R ∈ D k)
    (hbot : ∀ k, 0 < k → k ≤ m → ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      BotLiftProvisionIn (D k) k x)
    (hcap : ∀ k, 0 < k → k ≤ m → ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      CapLiftProvisionIn (D k) k x) :
    (j : ℕ) → j ≤ m → (lvlOn₀ I D j).RowsInAll D
  | 0, _ => fun z j hz ↦ by
    -- The level at the grade `0` has no cell of full scope.
    exfalso
    have h := (base₀ I).inv z
    have hpos := (base₀_good (I := I)).wf.isWellFormed.grade_pos z
    have hg : (base₀ I).S.toCellScheme.grade z = j := congrArg Prod.snd hz
    have hs : (base₀ I).S.toCellScheme.scope z = univ := congrArg Prod.fst hz
    rcases h with h | h
    · omega
    · exact h hs
  | j + 1, hj => (lvlOn₀_goodOn hD hdown hbot hcap j (by omega)).rowsInAll_nextOn
      (lvlOn₀_rowsInAll hD hdown hbot hcap j (by omega))

end VaughtConjecture.ProfileTower

/-! ### The completion on the catalogues of a predicate from every grade -/

namespace VaughtConjecture

open Finset Label ProfileTower

/-- **The completion on the catalogues of a predicate from every grade `N`**: for a seed on
`m + 2 ≥ 3` points and a predicate `Rw` on states with the lift provisions at every grade
`N ≤ k ≤ m + 1` from either coatom, the downward clause at the grades `≥ N` and, when
`N ≤ m + 1`, the code of the glued labelling at `m + 1` in the catalogue, some completion below the
full grade has the row of every cell of full scope at a grade `≥ N` satisfying `Rw` (read at the
old cells).  As `Seed.exists_rowCompletion`, with the levels on the family of `Rw` started at the
grade `0` (the amalgam with the identity section, `ProfileTower.lvlOn₀`), so that neither `N ≥ 3`
nor `m ≥ 2` is asked. -/
theorem Seed.exists_rowCompletion₀ {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)
    (hm : 0 < m) {N : ℕ} {Rw : I.State → Prop}
    (hbotP : ∀ k, N ≤ k → k ≤ m + 1 → ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      BotLiftProvisionOf Rw k x)
    (hcapP : ∀ k, N ≤ k → k ≤ m + 1 → ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      CapLiftProvisionOf Rw k x)
    (hdown : ∀ k, N ≤ k → ∀ R ∈ rowCat Rw (k + 1), code k R ∈ rowCat Rw k)
    (hlab : N ≤ m + 1 → Rw (hat I (m + 1) (code (m + 1) fun d ↦ I.amalgam.label d))) :
    ∃ F : CompletionBelowFullGrade I, F.HasAdmittedRows N Rw := by
  classical
  set D := rowFamily I N Rw
  have hD (k : ℕ) : D k ⊆ cat I k := rowCat_subset _ k
  have hdD := rowFamily_down hdown
  have hprov (k : ℕ) (hk0 : 0 < k) (hkm : k ≤ m + 1) (x : Fin (m + 2))
      (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :=
    rowFamily_lift hm hbotP hcapP hk0 hkm hx
  have hL := lvlOn₀_goodOn hD hdD (fun k hk hkm x hx ↦ (hprov k hk (by omega) x hx).1)
    (fun k hk hkm x hx ↦ (hprov k hk (by omega) x hx).2) m le_rfl
  have hR := lvlOn₀_rowsInAll hD hdD (fun k hk hkm x hx ↦ (hprov k hk (by omega) x hx).1)
    (fun k hk hkm x hx ↦ (hprov k hk (by omega) x hx).2) m le_rfl
  set Rt : I.State → Prop := fun s ↦ N ≤ m + 1 → Rw s
  have hdtop : ∀ R ∈ rowCat Rt (m + 1), code m R ∈ D m := hdD m
  have hbot (x) (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
      BotLiftProvisionOf Rt (m + 1) x := (hprov _ (by omega) le_rfl x hx).1
  have hcap (x) (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
      CapLiftProvisionOf Rt (m + 1) x := (hprov _ (by omega) le_rfl x hx).2
  have hlab' : code (m + 1) (fun d ↦ I.amalgam.label d) ∈ rowCat Rt (m + 1) := by
    have hW : IsCutLawful I (m + 1) fun d ↦ I.amalgam.label d :=
      ⟨I.amalgam.isLawful.isLawfulBelow _, I.amalgam.isLawful.isLawfulBelow _⟩
    exact mem_rowCat.mpr ⟨code_mem_cat_of_isCutLawful hW, hlab⟩
  set L := lvlOn₀ I D m
  refine ⟨hL.admittedTopCompletion Rt hdtop hbot hcap hlab', fun u k hu hk ↦ ?_⟩
  -- The rows of the completion: the top layer, then the layers of the levels.
  change Rw fun d ↦ (L.nextSOn (rowCat Rt (m + 1))).rowAt u
    (L.embedOn (rowCat Rt (m + 1)) d)
  induction u using Fin.addCases with
  | right i =>
    obtain ⟨R, hR', hrow⟩ := hL.rowAt_nextSOn (C := rowCat Rt (m + 1))
      (u := Fin.natAdd _ i) (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i)
    have hki : k = m + 1 := by
      have := congrArg Prod.snd hu
      change ((L.S.appendFullCellsScheme (m + 1) (rowCat Rt (m + 1)).card).gradedIndex
        (Fin.natAdd _ i)).2 = _ at this
      rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd] at this
      exact this.symm
    rw [funext hrow]
    exact (mem_rowCat.mp hR').2 (hki ▸ hk)
  | left e =>
    have he : L.S.toCellScheme.gradedIndex e = ((univ : Finset (Fin (m + 2))), k) :=
      (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e).symm.trans hu
    obtain ⟨R, hR', hrow⟩ := hR e k he
    have hrow' (d : Fin I.amalgam.card) :
        (L.nextSOn (rowCat Rt (m + 1))).rowAt (Fin.castAdd _ e)
          (L.embedOn (rowCat Rt (m + 1)) d) = hat I k R d :=
      (rowAt_appendFullCells_castAdd
        (r := fun i ↦ L.ΦOn (rowCat Rt (m + 1)) (entryOn (rowCat Rt (m + 1)) i))
        (h := L.not_le) e (L.embed d)).trans (hrow d)
    rw [funext hrow']
    have hR'' : R ∈ rowCat Rw k := by
      have := hR'
      simp only [D, rowFamily_of_le Rw hk] at this
      exact this
    exact (mem_rowCat.mp hR'').2

end VaughtConjecture
