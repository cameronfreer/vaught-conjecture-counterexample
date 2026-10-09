/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CellMirror
import VaughtConjecture.Extension.FieldLayer

/-!
# The replicated scheme: copies of the full-scope cells at the mixed faces

Roadmap, Layer 3 ((R3) and (R4), the replication of the full-scope cells into the mixed faces).

For a scheme `T` on `n` points and a finite set `𝒰` of faces (the **mixed faces**) no one of
which lies inside the scope of a cell of proper scope, the **replicated scheme**
(`Scheme.mirror hmix`) has the cells of `T`, in their order, followed by one **copy** of each
cell `f` of full scope at each mixed face `U` with `grade f ≤ |U|`: of scope `U`, of the grade of
`f`, reading the row of `f` (`CellScheme.Mirror`).  Every cell reads the row of its original at the
originals of the cells below it; the old cells keep their rows.

* **Laws** (`Scheme.isWellFormed_mirror`, `Scheme.isCoded_mirror`, `Scheme.isConsistent_mirror`):
  the replicated scheme is well formed (the mixed faces being faces), coded and consistent when `T`
  is; consistency is that of the mirrored rows, the mirroring being saturated (a copy of every cell
  of full scope of the same grade at the face of every copy).
* **Completeness at the mixed faces** (`Scheme.exists_gradedIndex_mirror`): if `T` has a cell of
  full scope at the grade `j ≤ |U|`, the mixed face `U` has a copy at the grade `j`.
* **The old cells** (`Scheme.gradedIndex_mirror_castAdd`, `Scheme.rowAt_mirror_castAdd`): an old
  cell keeps its graded index, and old cells read old cells as in `T`; the copies have proper
  scope (`Scheme.scope_mirror_natAdd`), so the cells of full scope are the old ones.

## References

Lawful sections and consistency are [Kni26, Definitions 2.5.4 and 2.5.12].
-/

universe u

namespace VaughtConjecture.Scheme

open Finset

variable {n : ℕ} (T : Scheme.{u} n) (𝒰 : Finset (Finset (Fin n)))

/-- The **copies**: a mixed face and a cell of full scope of grade at most its size. -/
abbrev CopyIdx : Type :=
  {p : Finset (Fin n) × Fin T.card //
    p.1 ∈ 𝒰 ∧ T.toCellScheme.scope p.2 = univ ∧ T.toCellScheme.grade p.2 ≤ #p.1}

noncomputable instance : Fintype (T.CopyIdx 𝒰) := Fintype.ofFinite _

/-- The number of copies. -/
noncomputable abbrev copyCount : ℕ := Fintype.card (T.CopyIdx 𝒰)

/-- The enumeration of the copies. -/
noncomputable def copyEquiv : T.CopyIdx 𝒰 ≃ Fin (T.copyCount 𝒰) := Fintype.equivFin _

/-- The original of a cell of the replicated scheme. -/
noncomputable def mirrorOrig : Fin (T.card + T.copyCount 𝒰) → Fin T.card :=
  Fin.append id fun j ↦ ((T.copyEquiv 𝒰).symm j).1.2

/-- The scope of a cell of the replicated scheme. -/
noncomputable def mirrorScope : Fin (T.card + T.copyCount 𝒰) → Finset (Fin n) :=
  Fin.append T.toCellScheme.scope fun j ↦ ((T.copyEquiv 𝒰).symm j).1.1

@[simp] theorem mirrorOrig_castAdd (c : Fin T.card) :
    T.mirrorOrig 𝒰 (Fin.castAdd _ c) = c := Fin.append_left _ _ c

@[simp] theorem mirrorOrig_natAdd (j : Fin (T.copyCount 𝒰)) :
    T.mirrorOrig 𝒰 (Fin.natAdd _ j) = ((T.copyEquiv 𝒰).symm j).1.2 := Fin.append_right _ _ j

@[simp] theorem mirrorScope_castAdd (c : Fin T.card) :
    T.mirrorScope 𝒰 (Fin.castAdd _ c) = T.toCellScheme.scope c := Fin.append_left _ _ c

@[simp] theorem mirrorScope_natAdd (j : Fin (T.copyCount 𝒰)) :
    T.mirrorScope 𝒰 (Fin.natAdd _ j) = ((T.copyEquiv 𝒰).symm j).1.1 := Fin.append_right _ _ j

variable {T 𝒰}

/-- **The mirroring of `T` by its copies**, when no mixed face lies inside the scope of a cell of
proper scope. -/
noncomputable def mirrorData
    (hmix : ∀ c, T.toCellScheme.scope c ≠ univ → ∀ U ∈ 𝒰, ¬ U ⊆ T.toCellScheme.scope c) :
    T.toCellScheme.Mirror (Fin (T.card + T.copyCount 𝒰)) where
  orig := T.mirrorOrig 𝒰
  scope := T.mirrorScope 𝒰
  scope_subset k := by
    induction k using Fin.addCases with
    | left c => rw [mirrorScope_castAdd, mirrorOrig_castAdd]
    | right j =>
      rw [mirrorScope_natAdd, mirrorOrig_natAdd, ((T.copyEquiv 𝒰).symm j).2.2.1]
      exact subset_univ _
  le_orig k t h := by
    obtain ⟨hs, hg⟩ := h
    simp only at hs hg
    change (T.toCellScheme.scope (T.mirrorOrig 𝒰 t), T.toCellScheme.grade (T.mirrorOrig 𝒰 t)) ≤
      (T.toCellScheme.scope (T.mirrorOrig 𝒰 k), T.toCellScheme.grade (T.mirrorOrig 𝒰 k))
    refine ⟨?_, hg⟩
    induction k using Fin.addCases with
    | right j =>
      rw [mirrorOrig_natAdd, ((T.copyEquiv 𝒰).symm j).2.2.1]
      exact subset_univ _
    | left c =>
      rw [mirrorOrig_castAdd]
      rw [mirrorScope_castAdd] at hs
      induction t using Fin.addCases with
      | left c' =>
        rw [mirrorScope_castAdd] at hs
        rw [mirrorOrig_castAdd]
        exact hs
      | right j =>
        rw [mirrorScope_natAdd] at hs
        by_cases hc : T.toCellScheme.scope c = univ
        · rw [hc]; exact subset_univ _
        · exact absurd hs (hmix c hc _ ((T.copyEquiv 𝒰).symm j).2.1)

variable (hmix : ∀ c, T.toCellScheme.scope c ≠ univ → ∀ U ∈ 𝒰, ¬ U ⊆ T.toCellScheme.scope c)

/-- **The replicated scheme**: the cells of `T` followed by the copies, every cell reading the row
of its original. -/
noncomputable abbrev mirror : Scheme.{u} n where
  card := T.card + T.copyCount 𝒰
  toCellScheme := (mirrorData hmix).cells
  rows := (mirrorData hmix).rows T.rows

/-- The mirroring is saturated: a copy of every cell of the same graded index at the scope of
every cell. -/
theorem saturated_mirrorData (Y : Finset (Fin n) × ℕ) : (mirrorData hmix).Saturated Y := by
  intro t _ u₀ hu₀
  induction t using Fin.addCases with
  | left c =>
    refine ⟨Fin.castAdd _ u₀, mirrorOrig_castAdd _ _ u₀, ?_⟩
    change T.mirrorScope 𝒰 _ = T.mirrorScope 𝒰 _
    rw [mirrorScope_castAdd, mirrorScope_castAdd]
    have h := congrArg Prod.fst hu₀
    change T.toCellScheme.scope u₀ = T.toCellScheme.scope (T.mirrorOrig 𝒰 (Fin.castAdd _ c)) at h
    rwa [mirrorOrig_castAdd] at h
  | right j =>
    set p := (T.copyEquiv 𝒰).symm j with hp
    have hs : T.toCellScheme.scope (T.mirrorOrig 𝒰 (Fin.natAdd _ j)) = univ := by
      rw [mirrorOrig_natAdd]; exact p.2.2.1
    have hsc : T.toCellScheme.scope u₀ = univ := (congrArg Prod.fst hu₀).trans hs
    have hgr : T.toCellScheme.grade u₀ = T.toCellScheme.grade p.1.2 := by
      have h := congrArg Prod.snd hu₀
      change T.toCellScheme.grade u₀ = T.toCellScheme.grade (T.mirrorOrig 𝒰 (Fin.natAdd _ j)) at h
      rwa [mirrorOrig_natAdd] at h
    let q : T.CopyIdx 𝒰 := ⟨(p.1.1, u₀), p.2.1, hsc, hgr ▸ p.2.2.2⟩
    refine ⟨Fin.natAdd _ (T.copyEquiv 𝒰 q), ?_, ?_⟩
    · change T.mirrorOrig 𝒰 _ = u₀
      rw [mirrorOrig_natAdd, Equiv.symm_apply_apply]
    · change T.mirrorScope 𝒰 _ = T.mirrorScope 𝒰 _
      rw [mirrorScope_natAdd, mirrorScope_natAdd, Equiv.symm_apply_apply]

variable {hmix}

/-- **The replicated scheme is consistent** when `T` is. -/
theorem isConsistent_mirror (hT : T.rows.IsConsistent) : (mirror hmix).rows.IsConsistent :=
  (mirrorData hmix).isConsistent_rows hT (saturated_mirrorData hmix)

/-- **The replicated scheme is coded** when `T` is. -/
theorem isCoded_mirror (hT : T.IsCoded) : (mirror hmix).IsCoded := fun _ _ ↦ hT _ _

/-- **The replicated scheme is well formed** when `T` is and the mixed faces are faces. -/
theorem isWellFormed_mirror (hT : T.IsWellFormed) (h𝒰 : ∀ U ∈ 𝒰, U ∈ T.toCellScheme.faces) :
    (mirror hmix).IsWellFormed := by
  refine ⟨hT.ground_eq, ⟨inferInstance, hT.isWellFormed.isPlan, fun k ↦ ?_⟩⟩
  change (T.mirrorScope 𝒰 k, T.toCellScheme.grade (T.mirrorOrig 𝒰 k)) ∈ T.toCellScheme.gradedFaces
  induction k using Fin.addCases with
  | left c =>
    rw [mirrorScope_castAdd, mirrorOrig_castAdd]
    exact hT.isWellFormed.gradedIndex_mem c
  | right j =>
    rw [mirrorScope_natAdd, mirrorOrig_natAdd]
    set p := (T.copyEquiv 𝒰).symm j
    exact ⟨h𝒰 _ p.2.1, hT.isWellFormed.grade_pos _, p.2.2.2⟩

/-- **Completeness at the mixed faces**: a cell of full scope of `T` at a grade `j ≤ |U|` has a copy
at the graded index `(U, j)`. -/
theorem exists_gradedIndex_mirror {U : Finset (Fin n)} (hU : U ∈ 𝒰) {j : ℕ} (hj : j ≤ #U)
    {f : Fin T.card} (hf : T.toCellScheme.gradedIndex f = (univ, j)) :
    ∃ k, (mirror hmix).toCellScheme.gradedIndex k = (U, j) := by
  have hs : T.toCellScheme.scope f = univ := congrArg Prod.fst hf
  have hg : T.toCellScheme.grade f = j := congrArg Prod.snd hf
  let q : T.CopyIdx 𝒰 := ⟨(U, f), hU, hs, hg ▸ hj⟩
  refine ⟨Fin.natAdd _ (T.copyEquiv 𝒰 q), ?_⟩
  change (T.mirrorScope 𝒰 _, T.toCellScheme.grade (T.mirrorOrig 𝒰 _)) = _
  rw [mirrorScope_natAdd, mirrorOrig_natAdd, Equiv.symm_apply_apply]
  exact Prod.ext rfl hg

/-- An old cell keeps its graded index. -/
theorem gradedIndex_mirror_castAdd (c : Fin T.card) :
    (mirror hmix).toCellScheme.gradedIndex (Fin.castAdd _ c) = T.toCellScheme.gradedIndex c := by
  change (T.mirrorScope 𝒰 _, T.toCellScheme.grade (T.mirrorOrig 𝒰 _)) = _
  rw [mirrorScope_castAdd, mirrorOrig_castAdd]
  rfl

/-- A copy has the scope of its mixed face. -/
theorem scope_mirror_natAdd (j : Fin (T.copyCount 𝒰)) :
    (mirror hmix).toCellScheme.scope (Fin.natAdd _ j) = ((T.copyEquiv 𝒰).symm j).1.1 :=
  mirrorScope_natAdd _ _ j

/-- **Old cells read old cells as in `T`.** -/
theorem rowAt_mirror_castAdd (z x : Fin T.card) :
    (mirror hmix).rowAt (Fin.castAdd _ z) (Fin.castAdd _ x) = T.rowAt z x := by
  have hiff : Fin.castAdd (T.copyCount 𝒰) x ∈ (mirror hmix).toCellScheme.below
      ((mirror hmix).toCellScheme.gradedIndex (Fin.castAdd _ z)) ↔
      x ∈ T.toCellScheme.below (T.toCellScheme.gradedIndex z) := by
    rw [CellScheme.mem_below, CellScheme.mem_below, gradedIndex_mirror_castAdd,
      gradedIndex_mirror_castAdd]
  by_cases hx : x ∈ T.toCellScheme.below (T.toCellScheme.gradedIndex z)
  · rw [rowAt_of_mem (hiff.mpr hx), rowAt_of_mem hx]
    change T.rows.row (T.mirrorOrig 𝒰 _) ⟨T.mirrorOrig 𝒰 _, _⟩ = _
    exact T.rows.row_congr (mirrorOrig_castAdd _ _ z) (mirrorOrig_castAdd _ _ x)
  · rw [rowAt_of_notMem (mt hiff.mp hx), rowAt_of_notMem hx]

end VaughtConjecture.Scheme
