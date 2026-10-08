/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.H3TopLift
import VaughtConjecture.Extension.UnionFillCounterexample

/-!
# The top grade of the donor coatom fails for a legal seed on four points (work file for `h3`)

Work file (branch `research/work-toplift`, placement later).  **`CapRequests.DonorTopLiftAt` is
not a property of every seed**: for the seed of the legal type `T` of
`VaughtConjecture.Extension.UnionFillCounterexample` with itself (four points), requests with no
requested cells, the private coatom `{0, 1, 2}`, the donor coatom `{0, 1, 3}` and the cut grade
`2` (`K = 1`), it fails (`TopLiftCounterexample.not_donorTopLiftAt_seed`).

The data: the cap `h = 2`; the profile `P` reading `labelling 2 2` of `T` on both coatoms (cut
lawful); the prescription `f` reading `labelling ⊤ ⊤` on the private coatom (lawful there, `⊤` at
the cap); the labelling `v` reading `labelling 2 ⊤` (lawful below the donor coatom at the grade
`1`, equal to `f` on the common face there, agreeing with `P` capped at `2`).  A lift `v'` lawful
below the donor coatom at the grade `2` would carry `⊤` at the cell of the common face at
`({0, 1}, 2)` and `2` at the cell at `({3}, 1)`, while the coupling row of `T` asks the first at
most the second.  This is the failure of the union fill
(`UnionFillCounterexample.not_unionFill_seed`) with the data of the band.  So `DonorTopLiftAt`
at a cut grade between `2` and the top must use more of the context than the band data (it holds
at the cut grade `1` and on three points, module `VaughtConjecture.MainTheorem.H3TopLift`).
-/

universe u

namespace VaughtConjecture.TopLiftCounterexample

open Finset Label CellScheme ProfileTower UnionFillCounterexample

variable {α : Ordinal.{u}}

/-- The graded indices of the live cells of `T`, carried to `Fin 4` along `Coatom.left 2`. -/
def liveL : Finset (Finset (Fin 4) × ℕ) :=
  {({2}, 1), ({1, 2}, 1), ({0, 1, 2}, 1), ({0, 1}, 2), ({0, 1, 2}, 2)}

/-- The graded indices of the live cells of `T` along either coatom. -/
def liveAll : Finset (Finset (Fin 4) × ℕ) := livePairs ∪ liveL

/-- The labelling `labelling A F` of `T`, read off graded indices in `Fin 4` along both coatoms. -/
noncomputable def lab (A F : Label.{u}) (X : Finset (Fin 4) × ℕ) : Label.{u} :=
  if X ∈ liveAll then (if X.2 = 1 then A else F) else ⊥

private theorem mem_liveAll_right : ∀ d : Fin 9,
    (Prod.map (Finset.map (Coatom.right 2)) id (cells.gradedIndex d) ∈ liveAll ↔
      live d = true) := by
  decide +kernel

private theorem mem_liveAll_left : ∀ d : Fin 9,
    (Prod.map (Finset.map (Coatom.left 2)) id (cells.gradedIndex d) ∈ liveAll ↔
      live d = true) := by
  decide +kernel

private theorem lab_map_right (A F : Label.{u}) (d : Fin 9) :
    lab A F (Prod.map (Finset.map (Coatom.right 2)) id (cells.gradedIndex d)) =
      labelling A F d := by
  unfold lab labelling
  by_cases hl : live d = true
  · rw [ite_eq_left ((mem_liveAll_right d).mpr hl), ite_eq_left hl]; rfl
  · rw [ite_eq_right (mt (mem_liveAll_right d).mp hl), ite_eq_right hl]

private theorem lab_map_left (A F : Label.{u}) (d : Fin 9) :
    lab A F (Prod.map (Finset.map (Coatom.left 2)) id (cells.gradedIndex d)) =
      labelling A F d := by
  unfold lab labelling
  by_cases hl : live d = true
  · rw [ite_eq_left ((mem_liveAll_left d).mpr hl), ite_eq_left hl]; rfl
  · rw [ite_eq_right (mt (mem_liveAll_left d).mp hl), ite_eq_right hl]

private theorem comap_seed_right' :
    (seed α).amalgam.toScheme.comap (Coatom.right 2) = (T α).toScheme := by
  obtain ⟨_, he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp (seed α).restrictFace_right
  exact congrArg StageType.toScheme he

private theorem comap_seed_left' :
    (seed α).amalgam.toScheme.comap (Coatom.left 2) = (T α).toScheme := by
  obtain ⟨_, he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp (seed α).restrictFace_left
  exact congrArg StageType.toScheme he

private theorem not_univ_three_le' {k : ℕ} (hk : k < 3) {B : Finset (Fin 3)} :
    ¬ ((univ : Finset (Fin 3)), 3) ≤ (B, k) := fun h ↦ absurd h.2 (by simpa using hk)

/-- A labelling of `T` agreeing below `X` with `labelling A F` is lawful below `X`. -/
private theorem isLawfulBelow_T_of_eq {A F : Label.{u}} (hA : IsSelfVisible 1 A)
    (hF : IsSelfVisible 2 F) (hFA : F ≤ A) {X : Finset (Fin 3) × ℕ}
    (hX : ¬ ((univ : Finset (Fin 3)), 3) ≤ X) (x : Fin (T α).toScheme.card → Label.{u})
    (hx : ∀ d : Fin 9, cells.gradedIndex d ≤ X → x (Fin.castSucc d) = labelling A F d) :
    (T α).toScheme.rows.IsLawfulBelow X (fun i ↦ x i) := by
  refine (isLawfulBelow_T_iff hX).mpr ?_
  convert (isLawful_labelling hA hF hFA).isLawfulBelow X using 1
  funext d
  exact hx d.1 d.2

/-- **Lawfulness along the second coatom**: a labelling of the amalgam equal to `lab A F` on the
cells below the image of `X` is lawful there. -/
theorem isLawfulBelow_right {A F : Label.{u}} (hA : IsSelfVisible 1 A) (hF : IsSelfVisible 2 F)
    (hFA : F ≤ A) {X : Finset (Fin 3) × ℕ} (hX : ¬ ((univ : Finset (Fin 3)), 3) ≤ X)
    (x : Fin (seed α).amalgam.card → Label.{u})
    (hx : ∀ d ∈ (seed α).amalgam.toCellScheme.below (Prod.map (Finset.map (Coatom.right 2)) id X),
      x d = lab A F ((seed α).amalgam.toCellScheme.gradedIndex d)) :
    (seed α).amalgam.rows.IsLawfulBelow (Prod.map (Finset.map (Coatom.right 2)) id X)
      (fun d ↦ x d) := by
  have hgi (i : Fin ((seed α).amalgam.toScheme.comap (Coatom.right 2)).card) :
      (seed α).amalgam.toCellScheme.gradedIndex
          ((seed α).amalgam.toScheme.cellMap (Coatom.right 2) i) =
        Prod.map (Finset.map (Coatom.right 2)) id
          (((seed α).amalgam.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i) :=
    ((seed α).amalgam.toScheme.map_comap_gradedIndex (Coatom.right 2) i).symm
  have key : ∀ y : Fin ((seed α).amalgam.toScheme.comap (Coatom.right 2)).card → Label.{u},
      (∀ i, ((seed α).amalgam.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i ≤ X →
        y i = lab A F (Prod.map (Finset.map (Coatom.right 2)) id
          (((seed α).amalgam.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i))) →
      ((seed α).amalgam.toScheme.comap (Coatom.right 2)).rows.IsLawfulBelow X (fun i ↦ y i) := by
    rw [comap_seed_right']
    intro y hy
    refine isLawfulBelow_T_of_eq hA hF hFA hX y fun d hd ↦ ?_
    have h1 := hy (Fin.castSucc d) (by rw [gradedIndex_T_castSucc]; exact hd)
    rw [h1, gradedIndex_T_castSucc, lab_map_right]
  have hk := key (fun i ↦ x ((seed α).amalgam.toScheme.cellMap (Coatom.right 2) i))
    (fun i hi ↦ by
      have hmem : (seed α).amalgam.toScheme.cellMap (Coatom.right 2) i ∈
          (seed α).amalgam.toCellScheme.below (Prod.map (Finset.map (Coatom.right 2)) id X) := by
        rw [CellScheme.mem_below, hgi]
        exact ⟨Finset.map_subset_map.mpr hi.1, hi.2⟩
      exact (hx _ hmem).trans (congrArg (lab A F) (hgi i)))
  exact (Scheme.isLawfulBelow_comap_cellMap_iff (seed α).amalgam.toScheme (Coatom.right 2) X x).mp
    hk

/-- **Lawfulness along the first coatom**, as `TopLiftCounterexample.isLawfulBelow_right`. -/
theorem isLawfulBelow_left {A F : Label.{u}} (hA : IsSelfVisible 1 A) (hF : IsSelfVisible 2 F)
    (hFA : F ≤ A) {X : Finset (Fin 3) × ℕ} (hX : ¬ ((univ : Finset (Fin 3)), 3) ≤ X)
    (x : Fin (seed α).amalgam.card → Label.{u})
    (hx : ∀ d ∈ (seed α).amalgam.toCellScheme.below (Prod.map (Finset.map (Coatom.left 2)) id X),
      x d = lab A F ((seed α).amalgam.toCellScheme.gradedIndex d)) :
    (seed α).amalgam.rows.IsLawfulBelow (Prod.map (Finset.map (Coatom.left 2)) id X)
      (fun d ↦ x d) := by
  have hgi (i : Fin ((seed α).amalgam.toScheme.comap (Coatom.left 2)).card) :
      (seed α).amalgam.toCellScheme.gradedIndex
          ((seed α).amalgam.toScheme.cellMap (Coatom.left 2) i) =
        Prod.map (Finset.map (Coatom.left 2)) id
          (((seed α).amalgam.toScheme.comap (Coatom.left 2)).toCellScheme.gradedIndex i) :=
    ((seed α).amalgam.toScheme.map_comap_gradedIndex (Coatom.left 2) i).symm
  have key : ∀ y : Fin ((seed α).amalgam.toScheme.comap (Coatom.left 2)).card → Label.{u},
      (∀ i, ((seed α).amalgam.toScheme.comap (Coatom.left 2)).toCellScheme.gradedIndex i ≤ X →
        y i = lab A F (Prod.map (Finset.map (Coatom.left 2)) id
          (((seed α).amalgam.toScheme.comap (Coatom.left 2)).toCellScheme.gradedIndex i))) →
      ((seed α).amalgam.toScheme.comap (Coatom.left 2)).rows.IsLawfulBelow X (fun i ↦ y i) := by
    rw [comap_seed_left']
    intro y hy
    refine isLawfulBelow_T_of_eq hA hF hFA hX y fun d hd ↦ ?_
    have h1 := hy (Fin.castSucc d) (by rw [gradedIndex_T_castSucc]; exact hd)
    rw [h1, gradedIndex_T_castSucc, lab_map_left]
  have hk := key (fun i ↦ x ((seed α).amalgam.toScheme.cellMap (Coatom.left 2) i))
    (fun i hi ↦ by
      have hmem : (seed α).amalgam.toScheme.cellMap (Coatom.left 2) i ∈
          (seed α).amalgam.toCellScheme.below (Prod.map (Finset.map (Coatom.left 2)) id X) := by
        rw [CellScheme.mem_below, hgi]
        exact ⟨Finset.map_subset_map.mpr hi.1, hi.2⟩
      exact (hx _ hmem).trans (congrArg (lab A F) (hgi i)))
  exact (Scheme.isLawfulBelow_comap_cellMap_iff (seed α).amalgam.toScheme (Coatom.left 2) X x).mp
    hk

/-- The labels of grade at most `1` do not depend on the label of grade `2`. -/
private theorem lab_one (A F F' : Label.{u}) {X : Finset (Fin 4) × ℕ} (hX : X.2 ≤ 1) :
    lab A F X = lab A F' X := by
  unfold lab
  by_cases hl : X ∈ liveAll
  · rw [ite_eq_left hl, ite_eq_left hl]
    have key : ∀ Y ∈ liveAll, 1 ≤ Y.2 := by decide
    rw [ite_eq_left (le_antisymm hX (key X hl)), ite_eq_left (le_antisymm hX (key X hl))]
  · rw [ite_eq_right hl, ite_eq_right hl]

/-- A live graded index of grade `1` meets the points `2` or `3`. -/
private theorem lab_common (A F : Label.{u}) {X : Finset (Fin 4) × ℕ} (hX : X.2 ≤ 1)
    (h2 : (2 : Fin 4) ∉ X.1) (h3 : (3 : Fin 4) ∉ X.1) : lab A F X = ⊥ := by
  unfold lab
  refine ite_eq_right fun hl ↦ ?_
  have key : ∀ Y ∈ liveAll, Y.2 ≤ 1 → (2 : Fin 4) ∈ Y.1 ∨ (3 : Fin 4) ∈ Y.1 := by decide
  rcases key X hl hX with h | h
  exacts [h2 h, h3 h]

/-- **The coupling in `T`** (as `UnionFillCounterexample`): below `(univ, 2)` the label of the
cell at `({0, 1}, 2)` is at most that of the cell at `({2}, 1)`. -/
private theorem le_T (y : Fin (T α).toScheme.card → Label.{u})
    (hy : (T α).toScheme.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun i ↦ y i))
    (i j : Fin (T α).toScheme.card)
    (hi : (T α).toScheme.toCellScheme.gradedIndex i = (({0, 1} : Finset (Fin 3)), 2))
    (hj : (T α).toScheme.toCellScheme.gradedIndex j = (({2} : Finset (Fin 3)), 1)) :
    y i ≤ y j := by
  have hy' := (isLawfulBelow_T_iff (α := α) (w := y) (not_univ_three_le' (by omega))).mp hy
  obtain ⟨A, F, -, -, hFA, hAF⟩ := (isLawfulBelow_iff (x := fun e ↦ y (Fin.castSucc e))).mp hy'
  have hcases (k : Fin (T α).toScheme.card) :
      k = Fin.last 9 ∨ ∃ d : Fin 9, k = Fin.castSucc d := by
    change Fin (9 + 1) at k
    induction k using Fin.lastCases with
    | last => exact .inl rfl
    | cast d => exact .inr ⟨d, rfl⟩
  rcases hcases i with rfl | ⟨d, rfl⟩
  · exact absurd (gradedIndex_T_last (α := α) ▸ hi) (by decide)
  rcases hcases j with rfl | ⟨e, rfl⟩
  · exact absurd (gradedIndex_T_last (α := α) ▸ hj) (by decide)
  have hd : d = 6 := gradedIndex_injective (((gradedIndex_T_castSucc (α := α) d).symm.trans
    hi).trans rfl)
  have he : e = 2 := gradedIndex_injective (((gradedIndex_T_castSucc (α := α) e).symm.trans
    hj).trans rfl)
  subst hd he
  have h6 := hAF (6 : Fin 9) ⟨subset_univ _, le_rfl⟩
  have h2 := hAF (2 : Fin 9) ⟨subset_univ _, by decide⟩
  have l6 : labelling A F (6 : Fin 9) = F := by simp [labelling, live, cellGrade]
  have l2 : labelling A F (2 : Fin 9) = A := by simp [labelling, live, cellGrade]
  rw [l6] at h6
  rw [l2] at h2
  exact h6.trans_le (hFA.trans_eq h2.symm)

/-- **The coupling of `T` read along the second coatom**: in a labelling of the amalgam lawful
below `({0, 1, 3}, 2)`, the cell at `({0, 1}, 2)` is at most the cell at `({3}, 1)`. -/
theorem le_cellMap_right (x : Fin (seed α).amalgam.card → Label.{u})
    (hx : (seed α).amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 2)), 2)
      (fun d ↦ x d))
    (i j : Fin ((seed α).amalgam.toScheme.comap (Coatom.right 2)).card)
    (hi : ((seed α).amalgam.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i =
      (({0, 1} : Finset (Fin 3)), 2))
    (hj : ((seed α).amalgam.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex j =
      (({2} : Finset (Fin 3)), 1)) :
    x ((seed α).amalgam.toScheme.cellMap (Coatom.right 2) i) ≤
      x ((seed α).amalgam.toScheme.cellMap (Coatom.right 2) j) := by
  have hpair2 : Prod.map (Finset.map (Coatom.right 2)) id ((univ : Finset (Fin 3)), 2) =
      (univ.erase (Fin.castSucc (Fin.last 2)), 2) := Prod.ext Coatom.univ_map_right rfl
  have hc := (Scheme.isLawfulBelow_comap_cellMap_iff (seed α).amalgam.toScheme (Coatom.right 2)
    ((univ : Finset (Fin 3)), 2) x).mpr (by rw [hpair2]; exact hx)
  have key : ∀ y : Fin ((seed α).amalgam.toScheme.comap (Coatom.right 2)).card → Label.{u},
      ((seed α).amalgam.toScheme.comap (Coatom.right 2)).rows.IsLawfulBelow
        ((univ : Finset (Fin 3)), 2) (fun i ↦ y i) →
      ∀ i j, ((seed α).amalgam.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i =
          (({0, 1} : Finset (Fin 3)), 2) →
        ((seed α).amalgam.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex j =
          (({2} : Finset (Fin 3)), 1) → y i ≤ y j := by
    rw [comap_seed_right']
    exact le_T
  exact key (fun i ↦ x ((seed α).amalgam.toScheme.cellMap (Coatom.right 2) i)) hc i j hi
    hj

/-- **`CapRequests.DonorTopLiftAt` fails for the seed of `T` with itself**, at the cut grade `2`,
for requests with no requested cells: the data of the module docstring. -/
theorem not_donorTopLiftAt_seed :
    ∃ r : CapRequests (Fin (seed α).amalgam.card),
      ¬ CapRequests.DonorTopLiftAt r (Fin.last 3) (Fin.castSucc (Fin.last 2)) 1 := by
  classical
  have hgiR (i : Fin ((seed α).amalgam.toScheme.comap (Coatom.right 2)).card) :
      (seed α).amalgam.toCellScheme.gradedIndex
          ((seed α).amalgam.toScheme.cellMap (Coatom.right 2) i) =
        Prod.map (Finset.map (Coatom.right 2)) id
          (((seed α).amalgam.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i) :=
    ((seed α).amalgam.toScheme.map_comap_gradedIndex (Coatom.right 2) i).symm
  have hgiL (i : Fin ((seed α).amalgam.toScheme.comap (Coatom.left 2)).card) :
      (seed α).amalgam.toCellScheme.gradedIndex
          ((seed α).amalgam.toScheme.cellMap (Coatom.left 2) i) =
        Prod.map (Finset.map (Coatom.left 2)) id
          (((seed α).amalgam.toScheme.comap (Coatom.left 2)).toCellScheme.gradedIndex i) :=
    ((seed α).amalgam.toScheme.map_comap_gradedIndex (Coatom.left 2) i).symm
  obtain ⟨i6, hi6⟩ : ∃ i : Fin ((seed α).amalgam.toScheme.comap (Coatom.right 2)).card,
      ((seed α).amalgam.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i =
        (({0, 1} : Finset (Fin 3)), 2) := by
    rw [comap_seed_right']; exact ⟨Fin.castSucc (6 : Fin 9), gradedIndex_T_castSucc 6⟩
  obtain ⟨i2, hi2⟩ : ∃ i : Fin ((seed α).amalgam.toScheme.comap (Coatom.right 2)).card,
      ((seed α).amalgam.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i =
        (({2} : Finset (Fin 3)), 1) := by
    rw [comap_seed_right']; exact ⟨Fin.castSucc (2 : Fin 9), gradedIndex_T_castSucc 2⟩
  obtain ⟨j2, hj2⟩ : ∃ i : Fin ((seed α).amalgam.toScheme.comap (Coatom.left 2)).card,
      ((seed α).amalgam.toScheme.comap (Coatom.left 2)).toCellScheme.gradedIndex i =
        (({2} : Finset (Fin 3)), 1) := by
    rw [comap_seed_left']; exact ⟨Fin.castSucc (2 : Fin 9), gradedIndex_T_castSucc 2⟩
  set d6 := (seed α).amalgam.toScheme.cellMap (Coatom.right 2) i6
  set d2 := (seed α).amalgam.toScheme.cellMap (Coatom.right 2) i2
  set c := (seed α).amalgam.toScheme.cellMap (Coatom.left 2) j2
  have hd6 : (seed α).amalgam.toCellScheme.gradedIndex d6 = (({0, 1} : Finset (Fin 4)), 2) := by
    rw [hgiR, hi6]; exact Prod.ext (by decide +kernel) rfl
  have hd2 : (seed α).amalgam.toCellScheme.gradedIndex d2 = (({3} : Finset (Fin 4)), 1) := by
    rw [hgiR, hi2]; exact Prod.ext (by decide +kernel) rfl
  have hc : (seed α).amalgam.toCellScheme.gradedIndex c = (({2} : Finset (Fin 4)), 1) := by
    rw [hgiL, hj2]; exact Prod.ext (by decide +kernel) rfl
  refine ⟨⟨c, 1, 0, one_pos, ∅, ∅, ∅, id, fun _ ↦ 0, c⟩, fun htop ↦ ?_⟩
  have hv2 : IsSelfVisible 2 (rowValue : Label.{u}) := isSelfVisible_gridPoint 2 0
  have hv1 : IsSelfVisible 1 (rowValue : Label.{u}) := hv2.mono (by omega)
  have hpairL : Prod.map (Finset.map (Coatom.left 2)) id ((univ : Finset (Fin 3)), 2) =
      (univ.erase (Fin.last 3), 2) := Prod.ext Coatom.univ_map_left rfl
  have hpairR : Prod.map (Finset.map (Coatom.right 2)) id ((univ : Finset (Fin 3)), 2) =
      (univ.erase (Fin.castSucc (Fin.last 2)), 2) := Prod.ext Coatom.univ_map_right rfl
  have hpairR1 : Prod.map (Finset.map (Coatom.right 2)) id ((univ : Finset (Fin 3)), 1) =
      (univ.erase (Fin.castSucc (Fin.last 2)), 1) := Prod.ext Coatom.univ_map_right rfl
  set gi := (seed α).amalgam.toCellScheme.gradedIndex
  set P : Fin (seed α).amalgam.card → Label.{u} := fun d ↦ lab rowValue rowValue (gi d)
  set f : Fin (seed α).amalgam.card → Label.{u} := fun d ↦ lab ⊤ ⊤ (gi d)
  set v : Fin (seed α).amalgam.card → Label.{u} := fun d ↦ lab rowValue ⊤ (gi d)
  have hPC : (seed α).amalgam.rows.IsLawfulBelow (univ.erase (Fin.last 3), 2) (fun d ↦ P d) := by
    have := isLawfulBelow_left hv1 hv2 le_rfl (X := ((univ : Finset (Fin 3)), 2))
      (not_univ_three_le' (by omega)) P fun _ _ ↦ rfl
    rwa [hpairL] at this
  have hPD : (seed α).amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 2)), 2)
      (fun d ↦ P d) := by
    have := isLawfulBelow_right hv1 hv2 le_rfl (X := ((univ : Finset (Fin 3)), 2))
      (not_univ_three_le' (by omega)) P fun _ _ ↦ rfl
    rwa [hpairR] at this
  have hf : (seed α).amalgam.rows.IsLawfulBelow (univ.erase (Fin.last 3), 1 + 1)
      (fun d ↦ f d) := by
    have := isLawfulBelow_left (A := ⊤) (F := ⊤) (isSelfVisible_top 1) (isSelfVisible_top 2)
      le_rfl (X := ((univ : Finset (Fin 3)), 2)) (not_univ_three_le' (by omega)) f fun _ _ ↦ rfl
    rwa [hpairL] at this
  have hv : (seed α).amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 2)), 1)
      (fun d ↦ v d) := by
    have := isLawfulBelow_right (A := rowValue) (F := ⊥) hv1 (isSelfVisible_bot 2) bot_le
      (X := ((univ : Finset (Fin 3)), 1)) (not_univ_three_le' (by omega)) v
      fun d hd ↦ lab_one _ _ _ hd.2
    rwa [hpairR1] at this
  have hmin (A F A' F' : Label.{u}) (hA : min A rowValue = min A' rowValue)
      (hF : min F rowValue = min F' rowValue) (X : Finset (Fin 4) × ℕ) :
      min (lab A F X) rowValue = min (lab A' F' X) rowValue := by
    unfold lab
    split_ifs
    exacts [hA, hF, rfl]
  have htopv : min (⊤ : Label.{u}) rowValue = min rowValue rowValue := by simp
  obtain ⟨v', hv', hv'v, hv'f, -⟩ := htop rowValue hv2 (isShort_gridPoint 2 0)
    (bot_lt_iff_ne_bot.mpr (gridPoint_ne_bot 2 0)) P ⟨hPC, hPD⟩
    ⟨fun _ h ↦ absurd h (Set.notMem_empty _), fun _ h ↦ absurd h (Set.notMem_empty _),
      fun _ h ↦ absurd h (Set.notMem_empty _)⟩
    f hf (fun d _ ↦ hmin _ _ _ _ htopv htopv _)
    (by
      change rowValue < lab ⊤ ⊤ (gi c)
      rw [hc]
      unfold lab
      rw [ite_eq_left (by decide), ite_eq_left rfl]
      exact lt_top_iff_ne_top.mpr (gridPoint_ne_top 2 0))
    v hv (fun d hdC hdD ↦ by
      change lab rowValue ⊤ (gi d) = lab ⊤ ⊤ (gi d)
      have h2 : (2 : Fin 4) ∉ (gi d).1 := fun h ↦ by
        have := hdD.1 h
        simp at this
      have h3 : (3 : Fin 4) ∉ (gi d).1 := fun h ↦ by
        have := hdC.1 h
        simp at this
      rw [lab_common _ _ hdD.2 h2 h3, lab_common _ _ hdD.2 h2 h3])
    (fun d ↦ hmin _ _ _ _ rfl htopv _)
  have hcoup := le_cellMap_right v' hv' i6 i2 hi6 hi2
  have hd6C : d6 ∈ (seed α).amalgam.toCellScheme.below (univ.erase (Fin.last 3), 1 + 1) := by
    change gi d6 ≤ _
    rw [hd6]
    exact ⟨by decide, le_rfl⟩
  have hd6D : d6 ∈ (seed α).amalgam.toCellScheme.below
      (univ.erase (Fin.castSucc (Fin.last 2)), 1 + 1) := by
    change gi d6 ≤ _
    rw [hd6]
    exact ⟨by decide, le_rfl⟩
  have hd2D : d2 ∈ (seed α).amalgam.toCellScheme.below
      (univ.erase (Fin.castSucc (Fin.last 2)), 1) := by
    change gi d2 ≤ _
    rw [hd2]
    exact ⟨by decide, le_rfl⟩
  have e6 : v' d6 = ⊤ := by
    rw [hv'f d6 hd6C hd6D]
    change lab ⊤ ⊤ (gi d6) = ⊤
    rw [hd6]
    unfold lab
    rw [ite_eq_left (by decide), ite_eq_right (by decide)]
  have e2 : v' d2 = rowValue := by
    rw [hv'v d2 hd2D]
    change lab rowValue ⊤ (gi d2) = rowValue
    rw [hd2]
    unfold lab
    rw [ite_eq_left (by decide), ite_eq_left rfl]
  rw [e6, e2] at hcoup
  exact gridPoint_ne_top 2 0 (top_le_iff.mp hcoup)

end VaughtConjecture.TopLiftCounterexample
