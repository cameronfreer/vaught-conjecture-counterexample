/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.H3Class

/-!
# The admitted completion at every grade of the cap, and the small caps (work file for `h3`)

Work file (placement later).  `H3.exists_coface_classCompletion` separates the caps with `k ≥ 2`
and grade `N ≥ 3` from the others, the **small caps**.  At a marked-cap context the grade of the
cap satisfies `n + 1 < N ≤ k + 1`, so the small caps are the caps of grade `N = 2` over the empty
root (`n = 0`), with `k ≥ 1`; the conditions on the root cells are then vacuous.

**Why the engine asked `N ≥ 3` and `m ≥ 2`.**  The levels of `Seed.exists_rowCompletion`
(`ProfileTower.lvlOn`) start at the level at the grade `2` (the tower `T 2` with its section,
decoded at the cap grade `3`), whose rows of full scope at the grades `1` and `2` read every
profile of the catalogue; restricted catalogues enter only from the grade `3`, and the level at
the grade `2` must lie below the top grade.  Nothing else in the layers asks for it: the next level
on a catalogue (`ProfileTower.Lvl.GoodOn.nextOn`) and the admitted top
(`ProfileTower.Lvl.GoodOn.admittedTopCompletion`) hold over a level at any grade.

Compiled in this file (theorem named):

* **The level at the grade `0`** (`ProfileTower.base₀`, `ProfileTower.base₀_good`): the amalgam
  with the identity section is a good level, for every seed.
* **The levels on a family from the grade `0`** (`ProfileTower.lvlOn₀`,
  `ProfileTower.lvlOn₀_goodOn`, `ProfileTower.lvlOn₀_rowsInAll`): good relative to the family up to
  the grade `m`, and reading its catalogues at every grade.
* **The completion on the catalogues of a predicate from every grade**
  (`Seed.exists_rowCompletion₀`): `Seed.exists_rowCompletion` for every `N` and every seed on at
  least three points; so `Seed.exists_classCompletion₀` and
  `H3.exists_classCompletion_of_fills₀`, the engine of the class admission with no restriction on
  `k` or `N`.  The small caps need the same inputs as the others.
* **The lift provisions from the donor coatom when the cap has the top grade**
  (`H3.donorLiftProvisions_of_lt`, `k < N`): the common face of the coatoms has `k` points, so it
  carries no cell of grade `N`; in particular for `k = 1`.
* **SCAFFOLD** `H3.exists_classCompletion_small`: the small caps, with two `sorry`s, (S1) the lift
  provisions from the donor coatom at `N = 2`, `k ≥ 2`, and (S4) the band of the fill at the
  positive caps at `N = 2`.
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

open CapRequests in
/-- **The admitted completion from the grade of the cap, at every grade of the cap**: as
`Seed.exists_classCompletion`, for a seed on `m + 2 ≥ 3` points and a cap of any grade (through
`Seed.exists_rowCompletion₀`). -/
theorem Seed.exists_classCompletion₀ {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (hm : 0 < m)
    {r : CapRequests (Fin I.amalgam.card)} (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    {B : Set (Fin I.amalgam.card)}
    (hB : ∀ d ∈ B, I.amalgam.toCellScheme.grade d < I.amalgam.toCellScheme.grade r.cap)
    {xp : Fin (m + 2)}
    (hdon : ∀ x ∈ (Pts : Finset (Fin (m + 2))), x ≠ xp → ∀ k,
      I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 →
        BotLiftProvisionOf (r.Admits B ∅) k x ∧ CapLiftProvisionOf (r.Admits B ∅) k x)
    (hbot : ∀ k, I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 → CapFillBotAtIn r B xp k)
    (hpos : ∀ k, I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 → CapFillPosAtIn r B xp k)
    (hlab : r.IsCorrect (hat I (m + 1) (code (m + 1) fun d ↦ I.amalgam.label d))) :
    ∃ F : CompletionBelowFullGrade I,
      F.HasAdmittedRows (I.amalgam.toCellScheme.grade r.cap) (r.Admits B ∅) := by
  have hNN : r.N ≤ I.amalgam.toCellScheme.grade r.cap := hgr.le_grade_cap
  have hBk {k : ℕ} (hk : I.amalgam.toCellScheme.grade r.cap ≤ k) :
      ∀ d ∈ B, I.amalgam.toCellScheme.grade d ≤ k := fun d hd ↦ ((hB d hd).trans_le hk).le
  refine I.exists_rowCompletion₀ hm (fun k hk hkm x hx ↦ ?_) (fun k hk hkm x hx ↦ ?_)
    (fun k hk R hR ↦ code_mem_rowCat_admits_of_mem_rowCat hgr (hBk hk) hR) fun _ ↦ hlab.admits
  · by_cases hxe : x = xp
    · subst hxe
      exact botLiftProvisionOf_admits_private hgr (hBk hk) (hbot k hk hkm)
    · exact (hdon x hx hxe k hk hkm).1
  · by_cases hxe : x = xp
    · subst hxe
      exact capLiftProvisionOf_admits_private hgr (hNN.trans hk) (hpos k hk hkm)
    · exact (hdon x hx hxe k hk hkm).2

namespace CapRequests

open CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {B : Set (Fin I.amalgam.card)}

/-- The lift provision at `⊥` for the correct states gives the one for the admitted states. -/
theorem botLiftProvisionOf_admits_of_isCorrect {ZA : Set (Fin I.amalgam.card)} {k : ℕ}
    {x : Fin (m + 2)} (h : BotLiftProvisionOf r.IsCorrect k x) :
    BotLiftProvisionOf (r.Admits B ZA) k x := fun f hf ↦ by
  obtain ⟨W, hW, hWf, hWc⟩ := h f hf
  exact ⟨W, hW, hWf, mem_rowCat.mpr ⟨(mem_rowCat.mp hWc).1, (mem_rowCat.mp hWc).2.admits⟩⟩

/-- **The lift provision at the positive caps for the correct states gives the one for the states
admitted in the class with no prescribed bottoms**, when the cells of the class have grades at
most `k`: a profile of the catalogue in the class is correct; one out of the class is matched by
any fill along it at the cap `h ≠ ⊥`, which is out of the class too. -/
theorem capLiftProvisionOf_admits_empty_of_isCorrect
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade) (hm : 0 < m) {k : ℕ} (hk : 0 < k)
    (hkm : k ≤ m + 1) (hNk : r.N ≤ k) {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2))))
    (hB : ∀ d ∈ B, I.amalgam.toCellScheme.grade d ≤ k)
    (h : CapLiftProvisionOf r.IsCorrect k x) : CapLiftProvisionOf (r.Admits B ∅) k x := by
  intro c hc hcs hcb P hP f hf hfP
  obtain ⟨hPcat, hPa⟩ := mem_rowCat.mp hP
  by_cases hcl : InBottomClass B ∅ (hat I k P)
  · obtain ⟨W, hW, hWf, hWP, hWc⟩ :=
      h c hc hcs hcb P (mem_rowCat.mpr ⟨hPcat, hPa hcl⟩) f hf hfP
    exact ⟨W, hW, hWf, hWP, mem_rowCat.mpr ⟨(mem_rowCat.mp hWc).1, (mem_rowCat.mp hWc).2.admits⟩⟩
  obtain ⟨d, hdB, hd⟩ : ∃ d ∈ B, hat I k P d = ⊥ := by
    by_contra hne
    push Not at hne
    exact hcl (inBottomClass_empty_iff.mpr hne)
  obtain ⟨W, hW, hWf, hWP⟩ :=
    exists_isCutLawful_of_coatom_le hm hk hkm hx hc (mem_cat.mp hPcat).1 hf hfP
  refine ⟨W, hW, hWf, hWP, orbitCode_mem_rowCat_admits hgr hNk hW fun hcl' ↦ absurd ?_
    (inBottomClass_empty_iff.mp hcl' d hdB)⟩
  rw [hat_of_le (hB d hdB)] at hd ⊢
  have e := hWP d
  rw [hd, min_bot_left, min_eq_bot] at e
  exact e.resolve_right hcb.ne'

end CapRequests

namespace H3

open StageType

variable {α : Ordinal.{u}} {n k : ℕ}

section Class

variable {t' : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {tb : StageType.{u} α (k + 1)}
  (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces)
  {g : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)}

/-- **The completion with rows admitted in the class, from the fills and the donor lift
provisions, at every grade of the cap**: `H3.exists_classCompletion_of_fills` without `k ≥ 2` and
`N ≥ 3` (through `Seed.exists_classCompletion₀`).  At a marked-cap context the grade `N` of the
cap satisfies `n + 1 < N ≤ k + 1`, so `k ≥ 1`. -/
theorem exists_classCompletion_of_fills₀ (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hdon : ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
      ProfileTower.BotLiftProvisionOf
          ((requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)).Admits
            (classCells ht' hp htb hd) ∅) k' (Fin.castSucc (Fin.last k)) ∧
        ProfileTower.CapLiftProvisionOf
          ((requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)).Admits
            (classCells ht' hp htb hd) ∅) k' (Fin.castSucc (Fin.last k)))
    (hraise : ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
      CapRequests.DonorRaiseBotAtIn (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega))
        (classCells ht' hp htb hd) (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k')
    (hband : ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
      CapRequests.CapFillPosBandAt (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega))
        (Fin.last (k + 1)) k') :
    ∃ F : CompletionBelowFullGrade (seed ht' hp htb),
      F.HasAdmittedRows (t'.toCellScheme.grade c)
        ((requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)).Admits
          (classCells ht' hp htb hd) ∅) := by
  have hrc : t'.toCellScheme.grade r ≤ t'.toCellScheme.grade c := by
    have h := hctx.2.1.2.1
    rw [CellScheme.mem_below] at h
    exact (Prod.le_def.mp h).2
  have hn := hctx.2.2.1
  have hck : t'.toCellScheme.grade c ≤ k + 1 := t'.grade_le c
  have hk0 : 0 < k := by omega
  have hgr := isGraded_requests ht' hp htb hd (r := r) (by omega) hrc hn
  have hL := restrictFace_left_seed ht' hp htb
  have hA := restrictFace_donor_seed ht' hp htb hd
  have hcapg : (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL c) =
      t'.toCellScheme.grade c := grade_faceCell hL c
  have hcapg' : (seed ht' hp htb).amalgam.toCellScheme.grade
      (requests ht' hp htb hd c r (by omega)).cap = t'.toCellScheme.grade c := hcapg
  have hcapC : (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL c) =
      univ.erase (Fin.last (k + 1)) := by
    rw [scope_faceCell, hctx.1.1]
    exact Coatom.univ_map_left
  have hmarkC : (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL r) ⊆
      univ.erase (Fin.last (k + 1)) := by
    rw [scope_faceCell, ← Coatom.univ_map_left]
    exact map_subset_map.mpr (subset_univ _)
  have hTlab (y) (hy : y ∈ (requests ht' hp htb hd c r (by omega)).T) :
      (seed ht' hp htb).amalgam.label y = ⊤ ∧
        ¬ (seed ht' hp htb).amalgam.toCellScheme.scope y ⊆ univ.erase (Fin.last (k + 1)) := by
    obtain ⟨j, hj, hjl, rfl⟩ := hy
    refine ⟨(label_faceCell hA j).trans hj, fun hsub ↦ ?_⟩
    have hmem : Fin.last (k + 1) ∈
        (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hA j) := by
      rw [scope_faceCell]
      exact mem_map.mpr ⟨Fin.last n, hjl, by simp⟩
    simpa using hsub hmem
  have hglued : (requests ht' hp htb hd c r (by omega)).IsCorrect
      fun e ↦ (seed ht' hp htb).amalgam.label e :=
    CapRequests.isCorrect_of_forall (fun z hz ↦ absurd hz (Set.notMem_empty _))
      (fun f hf ↦ absurd hf (Set.notMem_empty _))
      fun y hy ↦ by rw [(hTlab y hy).1]; exact le_top
  have hlab := (hglued.code hgr (k + 1)).hat hgr (k + 1)
  have hB : ∀ e ∈ classCells ht' hp htb hd, (seed ht' hp htb).amalgam.toCellScheme.grade e <
      (seed ht' hp htb).amalgam.toCellScheme.grade (requests ht' hp htb hd c r (by omega)).cap :=
    fun e he ↦ by rw [hcapg']; exact grade_lt_of_mem_classCells ht' hp htb hd hn he
  have h := (seed ht' hp htb).exists_classCompletion₀ hk0 hgr hB (xp := Fin.last (k + 1))
    (fun x hx hxe k' hk' hkm ↦ by
      have hx' : x = Fin.castSucc (Fin.last k) := by
        simp only [ProfileTower.Pts, mem_insert, mem_singleton] at hx
        exact hx.resolve_left hxe
      subst hx'
      exact hdon k' (hcapg' ▸ hk') hkm)
    (fun k' hk' hkm ↦ CapRequests.capFillBotAtIn_of_donorRaiseBotAtIn hgr hk0 (by simp)
      (by simp) Seed.last_ne_castSucc.symm (by rw [hcapg'] at hk'; omega) hkm hcapC.le hmarkC
      (fun y hy ↦ (hTlab y hy).2) rfl rfl (fun e he ↦ ((hB e he).trans_le hk').le)
      (hraise k' (hcapg' ▸ hk') hkm))
    (fun k' hk' hkm ↦ CapRequests.capFillPosAtIn_of_capFillPosAt hk0 (by simp)
      (by rw [hcapg'] at hk'; omega) hkm (fun e he ↦ ((hB e he).trans_le hk').le)
      (CapRequests.capFillPosAt_of_band hgr hk0 (by simp) hcapC hk' hkm
        (hband k' (hcapg' ▸ hk') hkm))) hlab
  rwa [hcapg'] at h

/-- **The lift provisions from the donor coatom when the cap has the top grade** (`k < N`, so
`N = k + 1`): the common face of the two coatoms has `k` points, so it carries no cell of grade at
least `N`, and the lift provisions from the donor coatom hold for the correct states
(`CapRequests.botLiftProvisionOf_donor_le`, `CapRequests.capLiftProvisionOf_donor_le`), hence for
the states admitted in the class. -/
theorem donorLiftProvisions_of_lt (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hkN : k < t'.toCellScheme.grade c) :
    ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
      ProfileTower.BotLiftProvisionOf
          ((requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)).Admits
            (classCells ht' hp htb hd) ∅) k' (Fin.castSucc (Fin.last k)) ∧
        ProfileTower.CapLiftProvisionOf
          ((requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)).Admits
            (classCells ht' hp htb hd) ∅) k' (Fin.castSucc (Fin.last k)) := by
  intro k' hk' hkm
  have hrc : t'.toCellScheme.grade r ≤ t'.toCellScheme.grade c := by
    have h := hctx.2.1.2.1
    rw [CellScheme.mem_below] at h
    exact (Prod.le_def.mp h).2
  have hn := hctx.2.2.1
  have hck : t'.toCellScheme.grade c ≤ k + 1 := t'.grade_le c
  have hk0 : 0 < k := by omega
  have hgr := isGraded_requests ht' hp htb hd (r := r) (by omega) hrc hn
  have hL := restrictFace_left_seed ht' hp htb
  have hcapg' : (seed ht' hp htb).amalgam.toCellScheme.grade
      (requests ht' hp htb hd c r (by omega)).cap = t'.toCellScheme.grade c := grade_faceCell hL c
  have hcapC : (seed ht' hp htb).amalgam.toCellScheme.scope
      (requests ht' hp htb hd c r (by omega)).cap = univ.erase (Fin.last (k + 1)) := by
    change (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL c) = _
    rw [scope_faceCell, hctx.1.1]
    exact Coatom.univ_map_left
  have hB : ∀ e ∈ classCells ht' hp htb hd,
      (seed ht' hp htb).amalgam.toCellScheme.grade e ≤ k' := fun e he ↦
    (grade_lt_of_mem_classCells ht' hp htb hd hn he).le.trans hk'
  have hface : ∀ e, (seed ht' hp htb).amalgam.toCellScheme.scope e ⊆
      univ.erase (Fin.last (k + 1)) ∩ univ.erase (Fin.castSucc (Fin.last k)) →
      (seed ht' hp htb).amalgam.toCellScheme.grade e <
        (seed ht' hp htb).amalgam.toCellScheme.grade
          (requests ht' hp htb hd c r (by omega)).cap := fun e he ↦ by
    have h1 := (seed ht' hp htb).amalgam.isWellFormed.isWellFormed.grade_le_card e
    have h2 := card_le_card he
    have h3 : #(univ.erase (Fin.last (k + 1)) ∩ univ.erase (Fin.castSucc (Fin.last k))) = k := by
      have e3 : univ.erase (Fin.last (k + 1)) ∩ univ.erase (Fin.castSucc (Fin.last k)) =
          (univ.erase (Fin.last (k + 1))).erase (Fin.castSucc (Fin.last k)) := by
        ext z
        simp only [mem_inter, mem_erase, mem_univ, and_true]
        tauto
      rw [e3, card_erase_of_mem (by simp [Fin.castSucc_ne_last]), card_erase_of_mem (mem_univ _),
        card_univ, Fintype.card_fin]
      omega
    rw [hcapg']
    omega
  have hxp : Fin.last (k + 1) ∈ (ProfileTower.Pts : Finset (Fin (k + 2))) := by simp
  have hxd : Fin.castSucc (Fin.last k) ∈ (ProfileTower.Pts : Finset (Fin (k + 2))) := by simp
  have hkk' : (seed ht' hp htb).amalgam.toCellScheme.grade
      (requests ht' hp htb hd c r (by omega)).cap ≤ k' := hcapg'.trans_le hk'
  refine ⟨CapRequests.botLiftProvisionOf_admits_of_isCorrect
    (CapRequests.botLiftProvisionOf_donor_le hk0 hcapC hkk' hkm hface hxp hxd
      Seed.last_ne_castSucc.symm hgr),
    CapRequests.capLiftProvisionOf_admits_empty_of_isCorrect hgr hk0 (by omega) hkm
      (hgr.le_grade_cap.trans hkk') hxd hB
      (CapRequests.capLiftProvisionOf_donor_le hk0 hgr hcapC hkk' hkm hface hxp hxd
        Seed.last_ne_castSucc.symm)⟩

end Class

/-! ### The small caps -/

set_option warningAsError false in
/-- **SCAFFOLD (`sorry`), (S5): the small caps.**  The hypotheses of
`H3.exists_coface_classCompletion` with a donor coface `tb` carrying the donor raise in the class
form, when `k ≤ 1` or the cap has grade at most `2`.  At a marked-cap context `n + 1 < N ≤ k + 1`
for the grade `N` of the cap, so these are the caps of grade `N = 2` over the empty root (`n = 0`),
`k ≥ 1`; none is excluded.  Through `H3.exists_classCompletion_of_fills₀` (no restriction on `k`
or `N`), the open inputs are those of the other caps: (S1) the lift provisions from the donor
coatom, compiled here when `k = 1` (`H3.donorLiftProvisions_of_lt`: the cap has the top grade),
and (S4) the band of the fill at the positive caps. -/
theorem exists_classCompletion_small (hα : Order.IsSuccLimit α) {t' : StageType.{u} α (k + 1)}
    {p : StageType.{u} α k} (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p)
    {g : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace (g.trans Fin.castSuccEmb) t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : d ∈ t.cofaces) {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hoff : t'.RootOffsetsBelow (g.trans Fin.castSuccEmb) (t'.toCellScheme.grade c))
    (hbot : t'.RootBottomRespected (g.trans Fin.castSuccEmb) c)
    {tb : StageType.{u} α (k + 1)} (htb : tb ∈ p.cofaces)
    (htbd : restrictFace (extendByLast g) tb = some d)
    (hraise : ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
      CapRequests.DonorRaiseBotAtIn
        (requests ht' hp htb htbd c r (by have := hctx.2.2.1; omega))
        (classCells ht' hp htb htbd) (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k')
    (hsmall : ¬ (2 ≤ k ∧ 3 ≤ t'.toCellScheme.grade c)) :
    ∃ F : CompletionBelowFullGrade (seed ht' hp htb),
      F.HasAdmittedRows (t'.toCellScheme.grade c)
        ((requests ht' hp htb htbd c r (by have := hctx.2.2.1; omega)).Admits
          (classCells ht' hp htb htbd) ∅) := by
  have hn := hctx.2.2.1
  have hck : t'.toCellScheme.grade c ≤ k + 1 := t'.grade_le c
  have hN2 : t'.toCellScheme.grade c = 2 := by omega
  refine exists_classCompletion_of_fills₀ ht' hp htb htbd hctx ?_ hraise ?_
  · rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · exact donorLiftProvisions_of_lt ht' hp htb htbd hctx (by omega)
    · -- (S1) at the cap of grade `2`, `k ≥ 2`: the lift provisions from the donor coatom
      sorry
  · -- (S4) at the cap of grade `2`: the band of the fill at the positive caps
    sorry

end H3

end VaughtConjecture
