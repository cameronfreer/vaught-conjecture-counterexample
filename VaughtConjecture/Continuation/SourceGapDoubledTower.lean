/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapDoubledReading
import VaughtConjecture.Continuation.SourceGapReadingInstance

/-!
# The doubled completion at every arity

Roadmap, Layer 3 ((R2) of the table of 3.4, the reading of the new tops at the cells labelled `⊤`);
the doublings of `VaughtConjecture.Continuation.SourceGapDoubling`, stacked at every grade.  The
case of the arity one is `VaughtConjecture.Continuation.SourceGapDoubledCompletion` and
`VaughtConjecture.Continuation.SourceGapDoubledReading`, kept as a test; nothing here goes through
it.

Let `I : Seed α m` be a seed on `m + 2` points whose two coatom types are equal
(`I.left = I.right`, a legal stage type `T` on `m + 1` points).  **The doubled tower**
(`Seed.doubledTower`) starts at the amalgam (a doubling of `T`, `Seed.isDoubling_amalgam`) and
appends, at each grade `j + 1`, **the copy layer** (`Scheme.copyLayer`): one cell of full scope
for each cell of `T` of graded index `(univ, j + 1)`, whose row is the row of that cell read
through the cell map reached so far.  It is defined by recursion together with the property that
every cell has grade at most `j` or scope other than the ground set, which makes the next layer
defined (as for the tower of field layers, `Seed.tower`).  There is no catalogue: at every grade
the cells of full scope are the copies of the cells of full scope of `T`.

**What is arity-specific in the arity one, and what is not.**  The two arguments that exclude the
mixed labelling and give bountifulness hold at every arity already
(`VaughtConjecture.Continuation.SourceGapDoubling`): the symmetry of the labellings lawful below a
full pair (`Scheme.IsDoubling.eq_of_isLawfulBelow`) needs only a cell of full scope at every grade
below, and the lift from a coatom to the full face by the symmetric fill
(`Scheme.IsDoubling.cappedLift_coatom`) needs only, in addition, the copies along the coatom.
Neither reads a lower layer, so no induction on the levels enters the lifts (unlike the lifting
invariant of the tower of field layers, `Seed.TowerInvariant`): the only arity-specific part of
the arity one was the number of layers (two), and the recursion on the grade replaces it.

**Results** (compiled in this repository, every arity `m`).

* `Seed.isDoubling_doubledTower`: every scheme of the doubled tower is a doubling of `T`.
* `Seed.exists_full_doubledTower`: after the grade `j`, a cell of full scope at every grade
  `1, …, min j (m + 1)` (the completeness of `T`).
* `Seed.cappedLift_doubledTower_left`, `Seed.cappedLift_doubledTower_right`: at the grade
  `m + 1`, the lifts from each coatom to the full face at every grade, by the symmetric fill.
* `Seed.isLegalBelowFullGrade_doubledTower`: the scheme reached after the grade `m + 1` is legal
  below the full grade `m + 2`.
* `Seed.doubledTowerCompletion : CompletionBelowFullGrade I`, with the labelling of `T` through
  the cell map; **lawfulness is preserved**: the pullback of every lawful labelling of `T` is
  lawful (`Seed.isLawful_comp_doubledTower`), and every labelling lawful below `(univ, j)` takes
  one value on the cells over one cell of `T` (`Seed.eq_of_isLawfulBelow_doubledTower`, the
  exclusion of the mixed labelling at every arity).
* `Seed.exists_completion_isDoubling`: the three preceding items as one statement — one
  completion for the seed, chosen before any labelling, a doubling of `T`, with lawfulness
  preserved and the labellings lawful below a full pair symmetric.
* `Seed.doubledTowerCoface`: the completion with the apex, a legal one-point coface of `T` whose
  face along `extendByLast Fin.castSuccEmb` is `T` again; it reads each new top along every root
  missing a point at every cell of full scope (`Seed.readsEachNewTop_doubledTowerCoface`).
* `StageType.exists_coatomStep_self_succ`: **the top-reading coatom step when the donor is the
  context, at every arity**: for every legal `t'` on `m + 1` points with a face along
  `Fin.castSuccEmb`, and every root `h = g.trans Fin.castSuccEmb`, one legal one-point coface
  `D'` of `t'` has face `t'` along `extendByLast Fin.castSuccEmb` and reads each new top along `h`
  at every cell of full scope.  The arity one is `StageType.exists_coatomStep_self` (checked
  against it by an `example`).
* `StageType.exists_readsEachNewTop_E` (a positive instance at the arity two, feasibility only):
  the legal display `ReadingInstance.E α` on three points gets a reading coface on four points.

**The symmetry hypothesis** is the hypothesis of the arity one: the donor is the context, along
`Fin.castSuccEmb`.  Donors other than the context are not treated here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Scheme

variable {m : ℕ} (T : Scheme.{u} (m + 1))

/-- The cell map after appending the copies at grade `k`: the given map on the old cells, and the
cell of `T` of each new cell. -/
noncomputable def copyCell {N : ℕ} (π : Fin N → Fin T.card) (k : ℕ) :
    Fin (N + (T.fullCells k).card) → Fin T.card :=
  Fin.append π (T.fullCell k)

/-- The row of the copy at grade `k` of the cell `i` of `T`: the row of that cell read through the
cell map. -/
noncomputable def copyRow {N : ℕ} (π : Fin N → Fin T.card) (k : ℕ)
    (i : Fin (T.fullCells k).card) (x : Fin (N + (T.fullCells k).card)) : Label.{u} :=
  T.rowAt (T.fullCell k i) (T.copyCell π k x)

/-- **The copy layer** at grade `k` over a scheme `S` with a cell map `π` to `T`: one cell of full
scope and grade `k` for each cell of `T` of graded index `(univ, k)`, with the row of that cell
read through `π`. -/
noncomputable abbrev copyLayer (S : Scheme.{u} (m + 2)) (π : Fin S.card → Fin T.card) (k : ℕ)
    (h : ∀ d, ¬ ((univ : Finset (Fin (m + 2))), k) ≤ S.toCellScheme.gradedIndex d) :
    Scheme.{u} (m + 2) :=
  S.appendFullCells k (T.fullCells k).card (T.copyRow π k) h

variable {T}

/-- **The copy layer of a doubling is a doubling.** -/
theorem IsDoubling.copyLayer {S : Scheme.{u} (m + 2)} {π : Fin S.card → Fin T.card}
    (hS : S.IsDoubling T π) (k : ℕ)
    (h : ∀ d, ¬ ((univ : Finset (Fin (m + 2))), k) ≤ S.toCellScheme.gradedIndex d) :
    (T.copyLayer S π k h).IsDoubling T (T.copyCell π k) :=
  hS.appendFullCells (gradedIndex_fullCell k) (fun _ hc ↦ exists_fullCell_eq hc) fun _ _ ↦ rfl

/-- **The copy layer of a consistent doubling of a consistent scheme is consistent**: the new rows
are pullbacks of lawful rows of `T`. -/
theorem IsDoubling.isConsistent_copyLayer {S : Scheme.{u} (m + 2)} {π : Fin S.card → Fin T.card}
    (hD : S.IsDoubling T π) (hT : T.rows.IsConsistent) (hS : S.rows.IsConsistent) (k : ℕ)
    (h : ∀ d, ¬ ((univ : Finset (Fin (m + 2))), k) ≤ S.toCellScheme.gradedIndex d) :
    (T.copyLayer S π k h).rows.IsConsistent :=
  isConsistent_appendFullCells hS fun i ↦
    (hD.copyLayer k h).isLawful_comp (isLawful_rowAt hT (gradedIndex_fullCell k i))

end Scheme

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (hLR : I.left = I.right)

/-- A scheme on `m + 2` points whose cells all have grade at most `j` or scope other than the
ground set lies above no cell at `(univ, j + 1)`. -/
private theorem not_univ_succ_le_of_grade_le_or {S : Scheme.{u} (m + 2)} {j : ℕ}
    (hS : ∀ d, S.toCellScheme.grade d ≤ j ∨ S.toCellScheme.scope d ≠ univ) (d : Fin S.card) :
    ¬ ((univ : Finset (Fin (m + 2))), j + 1) ≤ S.toCellScheme.gradedIndex d := fun hd ↦
  (hS d).elim (fun h ↦ absurd hd.2 (by simp only [CellScheme.gradedIndex_snd]; omega))
    fun h ↦ h (univ_subset_iff.mp hd.1)

/-- The doubled tower with its cell map, together with the property that makes the next layer
defined: every cell of the scheme at the grade `j` has grade at most `j` or scope other than the
ground set. -/
noncomputable def doubledAux : (j : ℕ) →
    {p : (S : Scheme.{u} (m + 2)) × (Fin S.card → Fin I.left.card) //
      ∀ d, p.1.toCellScheme.grade d ≤ j ∨ p.1.toCellScheme.scope d ≠ univ}
  | 0 => ⟨⟨I.amalgam.toScheme, I.doublingCell hLR⟩, fun d ↦ .inr (I.scope_ne_univ d)⟩
  | j + 1 => ⟨⟨I.left.toScheme.copyLayer (doubledAux j).1.1 (doubledAux j).1.2 (j + 1)
      (not_univ_succ_le_of_grade_le_or (doubledAux j).2),
      I.left.toScheme.copyCell (doubledAux j).1.2 (j + 1)⟩, fun d ↦ by
        induction d using Fin.addCases with
        | left d =>
          rw [Scheme.appendFullCellsScheme_grade_castAdd,
            Scheme.appendFullCellsScheme_scope_castAdd]
          exact ((doubledAux j).2 d).imp_left fun h ↦ h.trans (Nat.le_succ j)
        | right i => exact .inl (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le⟩

/-- **The doubled tower**: the scheme reached after the grade `j`.  It is the amalgam at `j = 0`,
and the copy layer at the grade `j + 1` of the scheme reached after `j`
(`Seed.doubledTower_succ`). -/
noncomputable abbrev doubledTower (j : ℕ) : Scheme.{u} (m + 2) := (I.doubledAux hLR j).1.1

/-- The cell map of the doubled tower. -/
noncomputable abbrev doubledTowerCell (j : ℕ) : Fin (I.doubledTower hLR j).card → Fin I.left.card :=
  (I.doubledAux hLR j).1.2

/-- Every cell of the scheme reached after the grade `j` has grade at most `j` or scope other than
the ground set. -/
theorem doubledTower_grade_le_or (j : ℕ) (d : Fin (I.doubledTower hLR j).card) :
    (I.doubledTower hLR j).toCellScheme.grade d ≤ j ∨
      (I.doubledTower hLR j).toCellScheme.scope d ≠ univ :=
  (I.doubledAux hLR j).2 d

/-- No cell of the scheme reached after the grade `j` lies above `(univ, j + 1)`. -/
theorem not_univ_succ_le_doubledTower (j : ℕ) (d : Fin (I.doubledTower hLR j).card) :
    ¬ ((univ : Finset (Fin (m + 2))), j + 1) ≤ (I.doubledTower hLR j).toCellScheme.gradedIndex d :=
  not_univ_succ_le_of_grade_le_or (I.doubledTower_grade_le_or hLR j) d

/-- **The tower equation** of the doubled tower. -/
theorem doubledTower_succ (j : ℕ) :
    I.doubledTower hLR (j + 1) = I.left.toScheme.copyLayer (I.doubledTower hLR j)
      (I.doubledTowerCell hLR j) (j + 1) (I.not_univ_succ_le_doubledTower hLR j) := rfl

/-- **Every scheme of the doubled tower is a doubling of `T`.** -/
theorem isDoubling_doubledTower : (j : ℕ) →
    (I.doubledTower hLR j).IsDoubling I.left.toScheme (I.doubledTowerCell hLR j)
  | 0 => I.isDoubling_amalgam hLR
  | j + 1 => (isDoubling_doubledTower j).copyLayer (j + 1) (I.not_univ_succ_le_doubledTower hLR j)

/-! ### The old cells -/

/-- The **old cells** of the doubled tower: the cells of the amalgam, along `Fin.castAdd` once for
each layer. -/
noncomputable def doubledTowerEmbed : (j : ℕ) →
    Fin I.amalgam.card ↪o Fin (I.doubledTower hLR j).card
  | 0 => RelEmbedding.refl _
  | j + 1 => (doubledTowerEmbed j).trans
      (Fin.castAddOrderEmb (I.left.toScheme.fullCells (j + 1)).card)

/-- The old cells form a lower embedding. -/
theorem isLowerEmbedding_doubledTower : (j : ℕ) →
    I.amalgam.toCellScheme.IsLowerEmbedding (I.doubledTower hLR j).toCellScheme
      (I.doubledTowerEmbed hLR j)
  | 0 => IsLowerEmbedding.id _
  | j + 1 => (Scheme.isLowerEmbedding_castAdd (j + 1) _ _
      (I.not_univ_succ_le_doubledTower hLR j)).comp
      (isLowerEmbedding_doubledTower j)

/-- The old cells keep their scopes. -/
theorem scope_doubledTowerEmbed : (j : ℕ) → (d : Fin I.amalgam.card) →
    (I.doubledTower hLR j).toCellScheme.scope (I.doubledTowerEmbed hLR j d) =
      I.amalgam.toCellScheme.scope d
  | 0, _ => rfl
  | j + 1, d =>
    (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans (scope_doubledTowerEmbed j d)

/-- The old cells keep their graded indices. -/
theorem gradedIndex_doubledTowerEmbed (j : ℕ) (d : Fin I.amalgam.card) :
    (I.doubledTower hLR j).toCellScheme.gradedIndex (I.doubledTowerEmbed hLR j d) =
      I.amalgam.toCellScheme.gradedIndex d :=
  Prod.ext (I.scope_doubledTowerEmbed hLR j d) ((I.isLowerEmbedding_doubledTower hLR j).grade_eq d)

/-- **Every cell of scope other than the ground set is old.** -/
theorem exists_doubledTowerEmbed_eq : (j : ℕ) → {z : Fin (I.doubledTower hLR j).card} →
    (I.doubledTower hLR j).toCellScheme.scope z ≠ univ → ∃ a, I.doubledTowerEmbed hLR j a = z
  | 0, z, _ => ⟨z, rfl⟩
  | j + 1, z, hz => by
    change Fin (I.left.toScheme.copyLayer (I.doubledTower hLR j) (I.doubledTowerCell hLR j) (j + 1)
      (I.not_univ_succ_le_doubledTower hLR j)).card at z
    induction z using Fin.addCases with
    | left z =>
      obtain ⟨a, rfl⟩ := exists_doubledTowerEmbed_eq j (z := z)
        ((Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).symm.trans_ne hz)
      exact ⟨a, rfl⟩
    | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz

/-- The cell map at an old cell is the cell map of the amalgam. -/
theorem doubledTowerCell_embed : (j : ℕ) → (d : Fin I.amalgam.card) →
    I.doubledTowerCell hLR j (I.doubledTowerEmbed hLR j d) = I.doublingCell hLR d
  | 0, _ => rfl
  | j + 1, d => by
    change Fin.append (I.doubledTowerCell hLR j) (I.left.toScheme.fullCell (j + 1))
      (Fin.castAdd _ (I.doubledTowerEmbed hLR j d)) = _
    rw [Fin.append_left]
    exact doubledTowerCell_embed j d

/-- The faces of every scheme of the doubled tower are those of the amalgam. -/
theorem faces_doubledTower : (j : ℕ) →
    (I.doubledTower hLR j).toCellScheme.faces = I.amalgam.toCellScheme.faces
  | 0 => rfl
  | j + 1 => faces_doubledTower j

/-- The rows pull back to those of the amalgam along the old cells. -/
theorem comap_rows_doubledTower : (j : ℕ) →
    (I.doubledTower hLR j).rows.comap (I.isLowerEmbedding_doubledTower hLR j) = I.amalgam.rows
  | 0 => rfl
  | j + 1 => by
    change ((I.left.toScheme.copyLayer (I.doubledTower hLR j) (I.doubledTowerCell hLR j) (j + 1)
      (I.not_univ_succ_le_doubledTower hLR j)).rows.comap
      (Scheme.isLowerEmbedding_castAdd (j + 1) _ _ (I.not_univ_succ_le_doubledTower hLR j))).comap
      (I.isLowerEmbedding_doubledTower hLR j) = _
    rw [Scheme.comap_rows_castAdd, comap_rows_doubledTower j]

/-- The graded faces of every scheme of the doubled tower are those of the amalgam. -/
theorem mem_gradedFaces_doubledTower {j : ℕ} {X : Finset (Fin (m + 2)) × ℕ} :
    X ∈ (I.doubledTower hLR j).toCellScheme.gradedFaces ↔
      X ∈ I.amalgam.toCellScheme.gradedFaces := by
  simp only [mem_gradedFaces, I.faces_doubledTower hLR j]

/-! ### Structural laws -/

/-- Every scheme of the doubled tower up to the grade `m + 2` is well formed. -/
theorem isWellFormed_doubledTower : (j : ℕ) → j ≤ m + 2 → (I.doubledTower hLR j).IsWellFormed
  | 0, _ => I.amalgam.isWellFormed
  | j + 1, hj => Scheme.isWellFormed_appendFullCells (h := (I.not_univ_succ_le_doubledTower hLR j))
      (isWellFormed_doubledTower j (by omega))
      (Nat.succ_pos j) hj

/-- Every scheme of the doubled tower is coded. -/
theorem isCoded_doubledTower : (j : ℕ) → (I.doubledTower hLR j).IsCoded
  | 0 => I.amalgam.isCoded
  | j + 1 => Scheme.isCoded_appendFullCells (h := (I.not_univ_succ_le_doubledTower hLR j))
      (isCoded_doubledTower j)
      fun _ _ ↦ I.left.isCoded.rowAt_lt _ _

/-- Every scheme of the doubled tower is consistent. -/
theorem isConsistent_doubledTower : (j : ℕ) → (I.doubledTower hLR j).rows.IsConsistent
  | 0 => I.isConsistent
  | j + 1 => (I.isDoubling_doubledTower hLR j).isConsistent_copyLayer
      I.isLegal_left.isConsistent (isConsistent_doubledTower j) (j + 1)
      (I.not_univ_succ_le_doubledTower hLR j)

/-- **The cells of full scope of the doubled tower**: after the grade `j`, one at every grade
`1, …, j` up to `m + 1`, by the completeness of `T`. -/
theorem exists_full_doubledTower : (j : ℕ) → ∀ {i : ℕ}, 0 < i → i ≤ j → i ≤ m + 1 →
    ∃ a, (I.doubledTower hLR j).toCellScheme.gradedIndex a = ((univ : Finset (Fin (m + 2))), i)
  | 0, _, hi, hij, _ => absurd hij (by omega)
  | j + 1, i, hi, hij, him => by
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · obtain ⟨a, ha⟩ := exists_full_doubledTower j hi (by omega) him
      exact ⟨Fin.castAdd _ a, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans ha⟩
    · obtain rfl : i = j + 1 := by omega
      obtain ⟨c, hc⟩ := I.isLegal_left.isComplete ((univ : Finset (Fin (m + 1))), j + 1)
        ⟨I.left.univ_mem_faces, hi, by simpa using him⟩
      obtain ⟨k, rfl⟩ := Scheme.exists_fullCell_eq hc
      exact ⟨Fin.natAdd _ k, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ k⟩

/-! ### The doubled completion: the scheme reached after the grade `m + 1` -/

/-- Every cell of the scheme reached after the grade `m + 1` has positive grade. -/
theorem grade_pos_doubledTower (d : Fin (I.doubledTower hLR (m + 1)).card) :
    0 < (I.doubledTower hLR (m + 1)).toCellScheme.grade d :=
  ((I.isWellFormed_doubledTower hLR (m + 1) (by omega)).isWellFormed.gradedIndex_mem d).2.1

/-- Every cell of the scheme reached after the grade `m + 1` has grade below `m + 2`. -/
theorem grade_lt_doubledTower (d : Fin (I.doubledTower hLR (m + 1)).card) :
    (I.doubledTower hLR (m + 1)).toCellScheme.grade d < m + 2 := by
  rcases I.doubledTower_grade_le_or hLR (m + 1) d with h | h
  · omega
  · obtain ⟨a, rfl⟩ := I.exists_doubledTowerEmbed_eq hLR (m + 1) h
    rw [(I.isLowerEmbedding_doubledTower hLR (m + 1)).grade_eq]
    exact I.grade_lt a

/-- **The lift along a coatom to the full face**, at every grade, by the symmetric fill: the
copies along a section `f` of the collapse are the old cells of the face of the amalgam along
`f`. -/
private theorem cappedLift_doubledTower_of_face {f : Fin (m + 1) ↪ Fin (m + 2)}
    (hf : ∀ i, Scheme.collapseLast m (f i) = i)
    (hL : restrictFace f I.amalgam = some I.left)
    (hcell : ∀ z, I.doublingCell hLR (faceCell hL z) = z)
    (hsub : ∀ {d : Fin I.amalgam.card}, I.amalgam.toCellScheme.scope d ⊆ univ.map f →
      faceCell hL (I.doublingCell hLR d) = d)
    (hne : univ.map f ≠ univ) {j : ℕ} (hj : j ≤ m + 1) :
    (I.doubledTower hLR (m + 1)).rows.CappedLift (X := (univ.map f, j))
      (Y := ((univ : Finset (Fin (m + 2))), j)) ⟨subset_univ _, le_rfl⟩ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact (I.isWellFormed_doubledTower hLR (m + 1) (by omega)).isWellFormed.cappedLift _
      (Or.inl rfl) _
  refine (I.isDoubling_doubledTower hLR (m + 1)).cappedLift_coatom hf
    (cp := fun z ↦ I.doubledTowerEmbed hLR (m + 1) (faceCell hL z))
    (fun z ↦ by rw [doubledTowerCell_embed, hcell])
    (fun z ↦ by
      rw [gradedIndex_doubledTowerEmbed]
      exact Prod.ext (scope_faceCell _ _) (grade_faceCell _ _))
    (fun d hd ↦ ?_)
    (fun i hi hij ↦ I.exists_full_doubledTower hLR (m + 1) hi (hij.trans hj) (hij.trans hj))
    (I.grade_pos_doubledTower hLR)
  obtain ⟨a, rfl⟩ := I.exists_doubledTowerEmbed_eq hLR (m + 1) (z := d) fun he ↦
    hne (subset_antisymm (subset_univ _) (he ▸ hd))
  have ha : I.amalgam.toCellScheme.scope a ⊆ univ.map f := by
    rw [← I.scope_doubledTowerEmbed hLR (m + 1) a]
    exact hd
  rw [doubledTowerCell_embed, hsub ha]

/-- **The lift from the first coatom to the full face**, at every grade, by the symmetric fill. -/
theorem cappedLift_doubledTower_left {j : ℕ} (hj : j ≤ m + 1) :
    (I.doubledTower hLR (m + 1)).rows.CappedLift (X := (univ.erase (Fin.last (m + 1)), j))
      (Y := ((univ : Finset (Fin (m + 2))), j)) ⟨erase_subset _ _, le_rfl⟩ := by
  have h := I.cappedLift_doubledTower_of_face hLR collapseLast_left I.restrictFace_left
    (I.doublingCell_faceCell_left hLR) (I.faceCell_left_of_subset hLR) Coatom.univ_map_left_ne hj
  rw [Coatom.univ_map_left] at h
  exact h

/-- **The lift from the second coatom to the full face**, at every grade, by the symmetric
fill. -/
theorem cappedLift_doubledTower_right {j : ℕ} (hj : j ≤ m + 1) :
    (I.doubledTower hLR (m + 1)).rows.CappedLift
      (X := (univ.erase (Fin.castSucc (Fin.last m)), j))
      (Y := ((univ : Finset (Fin (m + 2))), j)) ⟨erase_subset _ _, le_rfl⟩ := by
  have h := I.cappedLift_doubledTower_of_face hLR collapseLast_right
    (I.restrictFace_right_left hLR) (I.doublingCell_faceCell_right hLR)
    (I.faceCell_right_of_subset hLR) Coatom.univ_map_right_ne hj
  rw [Coatom.univ_map_right] at h
  exact h

/-- **Lifts off the full face** are those of the amalgam. -/
theorem cappedLift_doubledTower_of_ne_univ {X Y : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ (I.doubledTower hLR (m + 1)).toCellScheme.gradedFaces)
    (hY : Y ∈ (I.doubledTower hLR (m + 1)).toCellScheme.gradedFaces) (hXY : X ≤ Y)
    (hYne : Y.1 ≠ univ) : (I.doubledTower hLR (m + 1)).rows.CappedLift hXY := by
  have h : I.amalgam.toCellScheme.IsSourcePrefix (I.doubledTower hLR (m + 1)).toCellScheme
      (I.doubledTowerEmbed hLR (m + 1)) Y :=
    ⟨I.isLowerEmbedding_doubledTower hLR (m + 1), I.scope_doubledTowerEmbed hLR (m + 1),
      fun d hd ↦ I.exists_doubledTowerEmbed_eq hLR (m + 1) (z := d) fun he ↦ hYne
        (subset_antisymm (subset_univ _) (he ▸ hd.1))⟩
  refine h.cappedLift_of_isBountiful ?_ ((I.mem_gradedFaces_doubledTower hLR).mp hX)
    ((I.mem_gradedFaces_doubledTower hLR).mp hY) hXY le_rfl
  rw [I.comap_rows_doubledTower hLR (m + 1)]
  exact I.isBountiful

/-- **The doubled completion is bountiful**, by the coatoms. -/
theorem isBountiful_doubledTower : (I.doubledTower hLR (m + 1)).rows.IsBountiful := by
  have hle (z : Fin (m + 2)) (j : ℕ) (hj : j ≤ #(univ.erase z)) : j ≤ m + 1 := by
    rw [card_erase_of_mem (mem_univ z)] at hj
    simpa using hj
  have hF : (I.doubledTower hLR (m + 1)).toCellScheme.faces = I.amalgam.toCellScheme.faces :=
    I.faces_doubledTower hLR (m + 1)
  exact Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last (m + 1))
    (b := Fin.castSucc (Fin.last m)) (mem_univ _) (mem_univ _)
    (fun B hB hne ↦ I.subset_or_subset B (hF ▸ hB) hne)
    (hF ▸ I.erase_last_mem_faces) (hF ▸ I.erase_castSucc_mem_faces)
    (fun X Y hX hY hXY hYne ↦ I.cappedLift_doubledTower_of_ne_univ hLR hX hY hXY hYne)
    (fun j hj ↦ I.cappedLift_doubledTower_left hLR (hle _ j hj))
    (fun j hj ↦ I.cappedLift_doubledTower_right hLR (hle _ j hj))

/-- **The doubled completion is legal below the full grade**, at every arity. -/
theorem isLegalBelowFullGrade_doubledTower :
    (I.doubledTower hLR (m + 1)).IsLegalBelowFullGrade where
  isWellFormed := I.isWellFormed_doubledTower hLR (m + 1) (by omega)
  isCoded := I.isCoded_doubledTower hLR (m + 1)
  isConsistent := I.isConsistent_doubledTower hLR (m + 1)
  isBountiful := I.isBountiful_doubledTower hLR
  grade_lt := I.grade_lt_doubledTower hLR
  exists_gradedIndex_eq X hX hX2 := by
    obtain ⟨C, j⟩ := X
    by_cases hC : C = univ
    · subst hC
      exact I.exists_full_doubledTower hLR (m + 1) hX.2.1 (by simp only at hX2; omega)
        (by simp only at hX2; omega)
    · have hX' : (C, j) ∈ I.amalgam.toCellScheme.gradedFaces := by
        exact (I.mem_gradedFaces_doubledTower hLR).mp hX
      obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq _ hX' hC
      exact ⟨I.doubledTowerEmbed hLR (m + 1) d,
        (I.gradedIndex_doubledTowerEmbed hLR (m + 1) d).trans hd⟩

/-- **Lawfulness is preserved**: the pullback through the cell map of a lawful labelling of `T` is
a lawful labelling of the doubled completion. -/
theorem isLawful_comp_doubledTower {w : Fin I.left.card → Label.{u}}
    (hw : I.left.rows.IsLawful w) :
    (I.doubledTower hLR (m + 1)).rows.IsLawful (w ∘ I.doubledTowerCell hLR (m + 1)) :=
  (I.isDoubling_doubledTower hLR (m + 1)).isLawful_comp hw

/-- **The doubled completion below the full grade**, at every arity, with the labelling of `T`
through the cell map. -/
noncomputable def doubledTowerCompletion : CompletionBelowFullGrade I where
  scheme := I.doubledTower hLR (m + 1)
  embed := I.doubledTowerEmbed hLR (m + 1)
  isLowerEmbedding := I.isLowerEmbedding_doubledTower hLR (m + 1)
  scope_embed := I.scope_doubledTowerEmbed hLR (m + 1)
  comap_rows := I.comap_rows_doubledTower hLR (m + 1)
  mem_range_embed z hz := by
    obtain ⟨a, rfl⟩ := I.exists_doubledTowerEmbed_eq hLR (m + 1) hz
    exact ⟨a, rfl⟩
  faces_eq := I.faces_doubledTower hLR (m + 1)
  isLegalBelowFullGrade := I.isLegalBelowFullGrade_doubledTower hLR
  label := I.left.label ∘ I.doubledTowerCell hLR (m + 1)
  isLawful := I.isLawful_comp_doubledTower hLR I.left.isLawful
  label_embed d := by
    change I.left.label (I.doubledTowerCell hLR (m + 1) (I.doubledTowerEmbed hLR (m + 1) d)) = _
    rw [doubledTowerCell_embed, I.label_amalgam hLR]

/-- The labels of the doubled completion lie at the stage. -/
theorem atStage_doubledTowerCompletion (d : Fin (I.doubledTowerCompletion hLR).scheme.card) :
    AtStage α ((I.doubledTowerCompletion hLR).label d) :=
  I.left.atStage _

/-- **The exclusion of the mixed labelling at every arity**: a labelling lawful below `(univ, j)`,
`j ≤ m + 1`, takes one value on the cells over one cell of `T`; in particular on the two copies of
a cell of `T` along the two coatoms. -/
theorem eq_of_isLawfulBelow_doubledTower {j : ℕ} (hj : j ≤ m + 1)
    {w : Fin (I.doubledTower hLR (m + 1)).card → Label.{u}}
    (hw : (I.doubledTower hLR (m + 1)).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
      fun d ↦ w d)
    {d d' : Fin (I.doubledTower hLR (m + 1)).card}
    (hd : d ∈ (I.doubledTower hLR (m + 1)).toCellScheme.below ((univ : Finset (Fin (m + 2))), j))
    (hd' : d' ∈ (I.doubledTower hLR (m + 1)).toCellScheme.below ((univ : Finset (Fin (m + 2))), j))
    (hπ : I.doubledTowerCell hLR (m + 1) d = I.doubledTowerCell hLR (m + 1) d') : w d = w d' :=
  (I.isDoubling_doubledTower hLR (m + 1)).eq_of_isLawfulBelow hw
    (fun e he ↦ I.exists_full_doubledTower hLR (m + 1) (I.grade_pos_doubledTower hLR e)
      (he.2.trans hj) (he.2.trans hj)) hd hd' hπ

include hLR in
/-- **The doubled completion, with lawfulness preserved** (one completion for the seed, chosen
before any labelling): a completion below the full grade that is a doubling of `T` along a cell
map `π`, labelled by `T` through `π`, through which every lawful labelling of `T` pulls back to a
lawful labelling, and on which every labelling lawful below `(univ, j)`, `j ≤ m + 1`, takes one
value on the cells over one cell of `T`. -/
theorem exists_completion_isDoubling :
    ∃ (F : CompletionBelowFullGrade I) (π : Fin F.scheme.card → Fin I.left.card),
      F.scheme.IsDoubling I.left.toScheme π ∧ F.label = I.left.label ∘ π ∧
      (∀ w : Fin I.left.card → Label.{u}, I.left.rows.IsLawful w →
        F.scheme.rows.IsLawful (w ∘ π)) ∧
      ∀ j ≤ m + 1, ∀ w : Fin F.scheme.card → Label.{u},
        F.scheme.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) (fun d ↦ w d) →
        ∀ d d', d ∈ F.scheme.toCellScheme.below ((univ : Finset (Fin (m + 2))), j) →
          d' ∈ F.scheme.toCellScheme.below ((univ : Finset (Fin (m + 2))), j) →
          π d = π d' → w d = w d' :=
  ⟨I.doubledTowerCompletion hLR, I.doubledTowerCell hLR (m + 1),
    I.isDoubling_doubledTower hLR (m + 1), rfl, fun _ hw ↦ I.isLawful_comp_doubledTower hLR hw,
    fun _ hj _ hw _ _ hd hd' hπ ↦ I.eq_of_isLawfulBelow_doubledTower hLR hj hw hd hd' hπ⟩

/-! ### The doubled coface -/

/-- The doubled completion with the labels of `T`, as a stage type. -/
noncomputable abbrev doubledTowerLabelled : StageType.{u} α (m + 2) :=
  (I.doubledTowerCompletion hLR).withLabel (I.doubledTowerCompletion hLR).isLawful
    (I.atStage_doubledTowerCompletion hLR)

/-- The **doubled coface** at every arity: the doubled completion, with the labels of `T`, and the
apex. -/
noncomputable def doubledTowerCoface : StageType.{u} α (m + 2) :=
  (I.doubledTowerLabelled hLR).addApex (I.doubledTowerCompletion hLR).isLegalBelowFullGrade
    (Nat.succ_pos _)

theorem isLegal_doubledTowerCoface : (I.doubledTowerCoface hLR).IsLegal :=
  StageType.isLegal_addApex _ _

theorem restrictFace_left_doubledTowerCoface :
    restrictFace Fin.castSuccEmb (I.doubledTowerCoface hLR) = some I.left :=
  (StageType.restrictFace_addApex _ _ _ Coatom.univ_map_left_ne).trans
    (((I.doubledTowerCompletion hLR).restrictFace_withLabel _ _
      (I.doubledTowerCompletion hLR).label_embed _ Coatom.univ_map_left_ne).trans
      I.restrictFace_left)

theorem restrictFace_right_doubledTowerCoface :
    restrictFace (extendByLast Fin.castSuccEmb) (I.doubledTowerCoface hLR) = some I.left :=
  (StageType.restrictFace_addApex _ _ _ Coatom.univ_map_right_ne).trans
    (((I.doubledTowerCompletion hLR).restrictFace_withLabel _ _
      (I.doubledTowerCompletion hLR).label_embed _ Coatom.univ_map_right_ne).trans
      (I.restrictFace_right_left hLR))

theorem mem_cofaces_doubledTowerCoface : I.doubledTowerCoface hLR ∈ I.left.cofaces :=
  ⟨I.isLegal_doubledTowerCoface hLR, I.restrictFace_left_doubledTowerCoface hLR⟩

theorem rowAt_doubledTowerCoface_castSucc (a d : Fin (I.doubledTower hLR (m + 1)).card) :
    (I.doubledTowerCoface hLR).rowAt a.castSucc d.castSucc =
      (I.doubledTower hLR (m + 1)).rowAt a d :=
  StageType.rowAt_addApex_castSucc (t := I.doubledTowerLabelled hLR) _ _ a d

theorem gradedIndex_doubledTowerCoface_castSucc (d : Fin (I.doubledTower hLR (m + 1)).card) :
    (I.doubledTowerCoface hLR).toCellScheme.gradedIndex d.castSucc =
      (I.doubledTower hLR (m + 1)).toCellScheme.gradedIndex d :=
  StageType.gradedIndex_addApex_castSucc (t := I.doubledTowerLabelled hLR) _ _ d

theorem label_doubledTowerCoface_castSucc (d : Fin (I.doubledTower hLR (m + 1)).card) :
    (I.doubledTowerCoface hLR).label d.castSucc =
      I.left.label (I.doubledTowerCell hLR (m + 1) d) :=
  StageType.addApex_label_castSucc (t := I.doubledTowerLabelled hLR) _ _ d

theorem gradedIndex_doubledTowerCoface_last :
    (I.doubledTowerCoface hLR).toCellScheme.gradedIndex (Fin.last _) =
      ((univ : Finset (Fin (m + 2))), m + 2) :=
  StageType.gradedIndex_addApex_last (t := I.doubledTowerLabelled hLR) _ _

/-- **The doubled coface reads each new top**, at every arity, along every root missing a point,
at every cell of full scope. -/
theorem readsEachNewTop_doubledTowerCoface {n : ℕ} (h : Fin n ↪ Fin (m + 1))
    (hh : ∃ y, y ∉ Set.range h) :
    ReadsEachNewTop (I.restrictFace_left_doubledTowerCoface hLR) h := by
  have hD := I.isDoubling_doubledTower hLR (m + 1)
  have h₁ := I.restrictFace_left_doubledTowerCoface hLR
  intro x hx _ hxt
  -- the new top is not the apex: the root misses a point
  induction x using Fin.lastCases with
  | last =>
    obtain ⟨y, hy⟩ := hh
    have hsub := Scheme.mem_visibleCells.mp hx
    have hmem : y.castSucc ∈ (I.doubledTowerCoface hLR).toCellScheme.scope (Fin.last _) := by
      rw [show (I.doubledTowerCoface hLR).toCellScheme.scope (Fin.last _) = univ from
        congrArg Prod.fst (I.gradedIndex_doubledTowerCoface_last hLR)]
      exact mem_univ _
    obtain ⟨z, hz⟩ := hsub hmem
    induction z using Fin.lastCases with
    | last =>
      rw [extendByLast_last] at hz
      exact absurd hz (Fin.castSucc_lt_last y).ne'
    | cast z =>
      rw [extendByLast_castSucc] at hz
      exact (hy ⟨z, Fin.castSucc_injective _ hz⟩).elim
  | cast x =>
    set c := I.doubledTowerCell hLR (m + 1) x
    set v := I.doubledTowerEmbed hLR (m + 1) (faceCell I.restrictFace_left c)
    have hv : Fin.last (m + 1) ∉ (I.doubledTowerCoface hLR).toCellScheme.scope v.castSucc := by
      have e1 : (I.doubledTowerCoface hLR).toCellScheme.scope v.castSucc =
          I.amalgam.toCellScheme.scope (faceCell I.restrictFace_left c) :=
        congrArg Prod.fst ((I.gradedIndex_doubledTowerCoface_castSucc hLR v).trans
          (I.gradedIndex_doubledTowerEmbed hLR (m + 1) _))
      rw [e1]
      exact last_notMem_scope_faceCell I.restrictFace_left c
    obtain ⟨s, hs⟩ := exists_faceCell_eq_of_last_notMem h₁ hv
    have hvc : I.doubledTowerCell hLR (m + 1) v = c := by
      rw [doubledTowerCell_embed, doublingCell_faceCell_left]
    have hgv : (I.doubledTower hLR (m + 1)).toCellScheme.grade v =
        I.left.toCellScheme.grade c := by
      rw [← hD.grade_eq, hvc]
    have hgx : (I.doubledTower hLR (m + 1)).toCellScheme.grade x =
        I.left.toCellScheme.grade c :=
      (hD.grade_eq x).symm
    have hgs : I.left.toCellScheme.grade s = I.left.toCellScheme.grade c := by
      rw [← grade_faceCell h₁, hs]
      exact (congrArg Prod.snd (I.gradedIndex_doubledTowerCoface_castSucc hLR v)).trans hgv
    have hls : I.left.label s = I.left.label c := by
      rw [← label_faceCell h₁, hs, label_doubledTowerCoface_castSucc, hvc]
    have hlx : (I.doubledTowerCoface hLR).label x.castSucc = I.left.label c :=
      I.label_doubledTowerCoface_castSucc hLR x
    refine ⟨s, s, by rw [hls, ← hlx, hxt], by rw [hls, ← hlx, hxt], le_rfl, ?_, fun a ha ↦ ?_⟩
    · rw [hgs]
      exact ((congrArg Prod.snd (I.gradedIndex_doubledTowerCoface_castSucc hLR x)).trans hgx).le
    · -- a cell of full scope at the grade of `c` reads both copies as `T` reads `c`
      induction a using Fin.lastCases with
      | last =>
        have h2 := congrArg Prod.snd ((I.gradedIndex_doubledTowerCoface_last hLR).symm.trans ha)
        have h3 := I.left.isWellFormed.isWellFormed.gradedIndex_mem s
        have h4 : #(I.left.toCellScheme.scope s) ≤ m + 1 := (card_le_univ _).trans (by simp)
        simp only at h2
        have h5 : I.left.toCellScheme.grade s ≤ m + 1 := h3.2.2.trans h4
        omega
      | cast a =>
        rw [hs, show (I.doubledTowerCoface hLR).rowAt a.castSucc v.castSucc = _ from
          I.rowAt_doubledTowerCoface_castSucc hLR a v,
          show (I.doubledTowerCoface hLR).rowAt a.castSucc x.castSucc = _ from
          I.rowAt_doubledTowerCoface_castSucc hLR a x]
        have ha' : (I.doubledTower hLR (m + 1)).toCellScheme.gradedIndex a =
            ((univ : Finset (Fin (m + 2))), I.left.toCellScheme.grade c) := by
          rw [← hgs]
          exact (I.gradedIndex_doubledTowerCoface_castSucc hLR a).symm.trans ha
        have hvb : v ∈ (I.doubledTower hLR (m + 1)).toCellScheme.below
            ((I.doubledTower hLR (m + 1)).toCellScheme.gradedIndex a) := by
          rw [CellScheme.mem_below, ha']
          exact ⟨subset_univ _, hgv.le⟩
        have hxb : x ∈ (I.doubledTower hLR (m + 1)).toCellScheme.below
            ((I.doubledTower hLR (m + 1)).toCellScheme.gradedIndex a) := by
          change (I.doubledTower hLR (m + 1)).toCellScheme.gradedIndex x ≤ _
          rw [ha']
          exact ⟨subset_univ _, hgx.le⟩
        rw [hD.rowAt_eq _ _ hvb, hD.rowAt_eq _ _ hxb, hvc]

end Seed

namespace StageType

variable {α : Ordinal.{u}}

/-- **The top-reading coatom step when the donor is the context, at every arity** (at the coatom
`Fin.castSuccEmb` and the donor `d' = t'`): for every legal stage type `t'` on `m + 1` points with
face `p` along `Fin.castSuccEmb`, and every root `h = g.trans Fin.castSuccEmb`, one legal
one-point coface `D'` of `t'` has face `t'` along `extendByLast Fin.castSuccEmb` and reads each
new top along `h` at every cell of full scope, hence at its tops.  No hypothesis on the stage or
on the context is used. -/
theorem exists_coatomStep_self_succ {m : ℕ} {t' : StageType.{u} α (m + 1)} (ht' : t'.IsLegal)
    {p : StageType.{u} α m} (hp : restrictFace Fin.castSuccEmb t' = some p) {n : ℕ}
    (g : Fin n ↪ Fin m) {h : Fin n ↪ Fin (m + 1)} (hg : g.trans Fin.castSuccEmb = h) :
    ∃ (D' : StageType.{u} α (m + 2)) (hD' : D' ∈ t'.cofaces),
      restrictFace (extendByLast Fin.castSuccEmb) D' = some t' ∧ ReadsEachNewTop hD'.2 h ∧
        ReadsEachNewTopAtTops hD'.2 h := by
  set I := Seed.ofCoatoms ht' ht' hp hp
  have hLR : I.left = I.right := rfl
  have hmiss : ∃ y, y ∉ Set.range h := ⟨Fin.last m, fun ⟨i, hi⟩ ↦ by
    rw [← hg] at hi
    exact (Fin.castSucc_lt_last (g i)).ne hi⟩
  have hr := I.readsEachNewTop_doubledTowerCoface hLR h hmiss
  exact ⟨I.doubledTowerCoface hLR, I.mem_cofaces_doubledTowerCoface hLR,
    I.restrictFace_right_doubledTowerCoface hLR, hr, hr.atTops⟩

/-- The arity one of `StageType.exists_coatomStep_self_succ` is the statement of
`StageType.exists_coatomStep_self` (a test of the stacking against the two-layer construction). -/
example {t' : StageType.{u} α 2} (ht' : t'.IsLegal) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {n : ℕ} (g : Fin n ↪ Fin 1)
    {h : Fin n ↪ Fin 2} (hg : g.trans Fin.castSuccEmb = h) :
    ∃ (D' : StageType.{u} α 3) (hD' : D' ∈ t'.cofaces),
      restrictFace (extendByLast Fin.castSuccEmb) D' = some t' ∧ ReadsEachNewTop hD'.2 h ∧
        ReadsEachNewTopAtTops hD'.2 h :=
  exists_coatomStep_self_succ ht' hp g hg

/-- **A positive instance at the arity two** (feasibility only): the legal display
`ReadingInstance.E α` on three points has a face along `Fin.castSuccEmb`, so the doubled coface of
the seed of `E α` with itself is a legal one-point coface on four points, with face `E α` along
`extendByLast Fin.castSuccEmb`, reading each new top along the root `Fin.castSuccEmb`. -/
theorem exists_readsEachNewTop_E (α : Ordinal.{u}) :
    ∃ (D' : StageType.{u} α 4) (hD' : D' ∈ (ReadingInstance.E α).cofaces),
      restrictFace (extendByLast (Fin.castSuccEmb : Fin 2 ↪ Fin 3)) D' =
        some (ReadingInstance.E α) ∧
      ReadsEachNewTop hD'.2 (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ∧
      ReadsEachNewTopAtTops hD'.2 (Fin.castSuccEmb : Fin 2 ↪ Fin 3) := by
  have hf : univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ∈
      (ReadingInstance.E α).toCellScheme.faces := by
    -- the faces of the display are `ReadingInstance.plan3`
    change _ ∈ ReadingInstance.plan3
    decide
  exact exists_coatomStep_self_succ (ReadingInstance.isLegal_E α)
    (restrictFace_of_mem _ _ hf) (Function.Embedding.refl _) rfl

end StageType

end VaughtConjecture
