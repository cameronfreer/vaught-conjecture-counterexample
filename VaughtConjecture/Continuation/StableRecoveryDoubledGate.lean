/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapDoubledCompletion
import VaughtConjecture.Continuation.StableRecoveryGatedReading
import VaughtConjecture.Extension.GatedExtensionCounterexample
import VaughtConjecture.Realization.Families

/-!
# The doubled coface as a gated reading extension

Roadmap, Layer 4, output 3 of higher-stage reconstruction, Layer 3, 3.3 (the private cap and the
decoder of (R4)); the doubled completion of
`VaughtConjecture.Continuation.SourceGapDoubledCompletion` and the gated reading extensions of
`VaughtConjecture.Continuation.StableRecoveryGatedReading`.

Let `T⁺` be a legal stage type on two points with face `p` along `Fin.castSuccEmb`.  The seed of
`T⁺` with itself has equal coatom types, and its doubled completion with the labels of `T⁺` and
the apex added is **the doubled coface** `Seed.doubledApex`: a legal one-point coface of `T⁺` whose
face along `extendByLast Fin.castSuccEmb` is `T⁺` again.  So it is a candidate gated reading
extension (`StageType.IsGatedReadingExtension`) for the input `T⁺`, `f = Fin.castSuccEmb`, and the
donor `D = T⁺` (the self-donor).

**Copies.**  The cell of the doubled coface at a position `k` of either face is the copy of the
cell of `T⁺` at that position (`Seed.cellMap_doubledApex_left`,
`Seed.cellMap_doubledApex_right`), and a cell of full scope reads every cell as the cell of `T⁺`
under it reads the cell under that one (`Seed.rowAt_doubledApex_castSucc`).

**Rigidity** (`Seed.label_doubledApex_eq`).  Every stage type on the scheme of the doubled coface
with face `T⁺` along the first coatom labels every cell other than the apex as `T⁺` labels the cell
under it: a labelling lawful below the full pair is symmetric (the exclusion of the mixed
labelling).  So the gate is labelled alike in every such stage type.

**The reading transfers to `T⁺` itself** (`StageType.ReadsOwnCellThroughCap`).  A cell `c` of
`T⁺` reads a cell `j` of `T⁺` through the cap `b` when its row is `⊥` at `j` if `j` is labelled
`⊥`, reads `j` as `b` if `j` is labelled `⊤`, and reads `j` at `ω · c' + n` if `j` is labelled
`μ + n` (with `n` below the grade of `b`).  The copy of full scope over `c` reads the copy of `j`
along the second coatom through the copy of `b` along the first exactly when `c` reads `j` through
`b` in `T⁺` (the reference cell is the copy of `j` along the first coatom).

* `Seed.isGatedReadingExtension_doubledApex`: a gate, readers and a ceiling at `(univ, 2)` in
  `T⁺` whose readers read every new cell of `T⁺` through `b`, and a gate not labelled `⊥`, give a
  gated reading extension on the doubled coface, with the gate labelled as in `T⁺` by every stage
  type on it with face `T⁺`.
* `Seed.IsGatedReadingExtension.exists_readsOwnCellThroughCap_doubledApex`: conversely, a gated
  reading extension on the doubled coface (cap of grade `2`) gives a cell of `T⁺` at `(univ, 2)`
  reading every new cell of `T⁺` through `b`.
* `StageType.exists_isGatedReadingExtension_doubledApex_addApex`: **every type with an apex** is an
  instance: the apex reads every cell through its block coding, so it is its own gate, reader and
  ceiling, and the doubled coface is a gated reading extension whose gate is labelled `⊤` by every
  stage type on it with face `T⁺`.
* `GatedExtensionCounterexample.not_isGatedReadingExtension_doubledApex`: at the private type `P`
  (two cells of full scope, both `⊤`, their rows ordering them oppositely), no cell of full scope
  reads both as it reads the cap, so the doubled coface is a gated reading extension for no gate
  and readers, at either cap.  The failing clause is `readers`, the reading of a new cell labelled
  `⊤` as the cap.  `StageType.not_hasDoubledGatedReadings`: the requirement that the doubled
  coface be a gated reading extension at every legal self-donor input with a graded cap
  (`StageType.HasDoubledGatedReadings`) is false at every stage.  This refutes the doubling design
  as a universal source of gated readings, not (R4): it says nothing of other extensions of `P`.

**Recovery at the self-donor needs no reading** (`Seed.isStableRecoveryScheme_doubledApex`).  By
rigidity, the doubled coface is a stable recovery scheme (`StageType.IsStableRecoveryScheme`) for
`T⁺`, `Fin.castSuccEmb`, `D = T⁺` and every `γ`, with no gate, reader or cap: every stage type on
it with face `T⁺` has face exactly `T⁺` along the second coatom.  So at `P` the doubling recovers,
and only the reading clause of the gated form fails.

**Two blocks** (`Seed.IsGatedReadingExtension.not_lt_omega0_doubledApex`).  In a gated reading
extension on the doubled coface, a reader over a cell of `T⁺` labelled at least `μ₂ + N` does not
read two new cells of blocks `μ₁ < μ₂` both in the natural strip: the doubled coface itself
labels the reader at least `μ₂ + N`.  So, unlike the leaf-and-marked completion (whose ceilings
and gate are labelled below `μ₂ + 4` by every stage type with face `T⁺`), the doubling labels a
gate over the cap `b` as `T⁺` labels `b`, at least `λ_ξ + N`, in every stage type with face `T⁺`
(rigidity), and its reader over the cap does not read both new cells in the natural strip.  For a
type with an apex the gate is labelled `⊤`.  No type with an apex whose new cells lie in two blocks
is constructed here.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

/-! ### Rows after appending a cell of full scope -/

namespace Scheme

variable {n j : ℕ} {S : Scheme.{u} n} {r : Fin (S.card + 1) → Label.{u}}
  {h : ∀ d, ¬ ((univ : Finset (Fin n)), j) ≤ S.toCellScheme.gradedIndex d}

/-- Old cells are read after appending one cell of full scope as before. -/
private theorem rowAt_appendFullCell_castSucc' (a d : Fin S.card) :
    (S.appendFullCell j r h).rowAt a.castSucc d.castSucc = S.rowAt a d := by
  have hiff : d.castSucc ∈ (S.appendFullCell j r h).toCellScheme.below
      ((S.appendFullCell j r h).toCellScheme.gradedIndex a.castSucc) ↔
      d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex a) := by
    rw [CellScheme.mem_below, CellScheme.mem_below, appendFullCell_toCellScheme,
      appendFullCellScheme_gradedIndex_castSucc, appendFullCellScheme_gradedIndex_castSucc]
  by_cases hd : d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex a)
  · rw [rowAt_of_mem (hiff.mpr hd), rowAt_of_mem hd]
    exact congrArg (fun R : S.toCellScheme.Rows ↦ R.row a ⟨d, hd⟩)
      (comap_rows_castSucc (S := S) (j := j) (r := r) (h := h))
  · rw [rowAt_of_notMem (mt hiff.mp hd), rowAt_of_notMem hd]

end Scheme

/-! ### Reading through the cap inside a stage type -/

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ}

/-- A cell `c` of a stage type `T` **reads its cell `j` through the cap `b`**, as `j` is labelled
in `T`: the row of `c` is `⊥` at `j` if `j` is labelled `⊥`; it reads `j` as it reads `b` if `j`
is labelled `⊤`; and if `j` is labelled `μ + n` with `μ` zero or a limit, then `n` is below the
grade of `b` and the row of `c` reads `j` at `ω · c' + n` for some `c'`. -/
def ReadsOwnCellThroughCap (T : StageType.{u} α n) (c b j : Fin T.card) : Prop :=
  (T.label j = ⊥ → T.rowAt c j = ⊥) ∧ (T.label j = ⊤ → T.rowAt c j = T.rowAt c b) ∧
    ∀ (μ : Ordinal.{u}) (k : ℕ), Order.IsSuccPrelimit μ →
      T.label j = ((μ + k : Ordinal.{u}) : Label.{u}) →
        k < T.toCellScheme.grade b ∧ ∃ c' : Ordinal.{u},
          T.rowAt c j = ((ω * c' + k : Ordinal.{u}) : Label.{u})

end StageType

/-! ### The doubled coface -/

namespace Seed

variable {α : Ordinal.{u}} (I : Seed.{u} α 1) (hLR : I.left = I.right) (hI : I.left.IsLegal)

/-- The doubled completion with the labels of `T` through the cell map. -/
private noncomputable abbrev doubledWithLabel : StageType.{u} α (1 + 2) :=
  (I.doubledCompletion hLR hI).withLabel (I.doubledCompletion hLR hI).isLawful
    (I.atStage_doubledCompletion hLR hI)

/-- The **doubled coface**: the doubled completion, with the labels of `T` through the cell map,
and the apex. -/
noncomputable def doubledApex : StageType.{u} α 3 :=
  (I.doubledWithLabel hLR hI).addApex (I.doubledCompletion hLR hI).isLegalBelowFullGrade
    (Nat.succ_pos _)

/-- The doubled coface is legal. -/
theorem isLegal_doubledApex : (I.doubledApex hLR hI).IsLegal :=
  StageType.isLegal_addApex _ _

/-- The face of the doubled coface along the first coatom is `T`. -/
theorem restrictFace_left_doubledApex :
    restrictFace Fin.castSuccEmb (I.doubledApex hLR hI) = some I.left :=
  (StageType.restrictFace_addApex _ _ _ Coatom.univ_map_left_ne).trans
    (((I.doubledCompletion hLR hI).restrictFace_withLabel _ _
      (I.doubledCompletion hLR hI).label_embed _ Coatom.univ_map_left_ne).trans
      I.restrictFace_left)

/-- The face of the doubled coface along the second coatom is `T`. -/
theorem restrictFace_right_doubledApex :
    restrictFace (extendByLast Fin.castSuccEmb) (I.doubledApex hLR hI) = some I.left :=
  (StageType.restrictFace_addApex _ _ _ Coatom.univ_map_right_ne).trans
    (((I.doubledCompletion hLR hI).restrictFace_withLabel _ _
      (I.doubledCompletion hLR hI).label_embed _ Coatom.univ_map_right_ne).trans
      (I.restrictFace_right_left hLR))

/-- The doubled coface is a coface of `T`. -/
theorem mem_cofaces_doubledApex : I.doubledApex hLR hI ∈ I.left.cofaces :=
  ⟨I.isLegal_doubledApex hLR hI, I.restrictFace_left_doubledApex hLR hI⟩

/-- The old cells are read in the doubled coface as in the doubled completion. -/
theorem rowAt_doubledApex_castSucc' (a d : Fin (I.doubled hLR).card) :
    (I.doubledApex hLR hI).rowAt a.castSucc d.castSucc = (I.doubled hLR).rowAt a d :=
  Scheme.rowAt_appendFullCell_castSucc'
    (h := (I.doubledCompletion hLR hI).isLegalBelowFullGrade.not_le) a d

/-- The old cells keep their graded indices. -/
theorem gradedIndex_doubledApex_castSucc (d : Fin (I.doubled hLR).card) :
    (I.doubledApex hLR hI).toCellScheme.gradedIndex d.castSucc =
      (I.doubled hLR).toCellScheme.gradedIndex d :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc _ _ _

/-- The apex has graded index `(univ, 3)`. -/
theorem gradedIndex_doubledApex_last :
    (I.doubledApex hLR hI).toCellScheme.gradedIndex (Fin.last _) =
      ((univ : Finset (Fin 3)), 3) :=
  Scheme.appendFullCellScheme_gradedIndex_last _ _

/-- The labels of the old cells are those of `T` through the cell map. -/
theorem label_doubledApex_castSucc (d : Fin (I.doubled hLR).card) :
    (I.doubledApex hLR hI).label d.castSucc = I.left.label (I.doubledCell hLR d) :=
  StageType.addApex_label_castSucc (t := I.doubledWithLabel hLR hI) _ _ d

/-- **Rows of the doubled coface**: below a cell other than the apex, a cell other than the apex
is read as `T` reads the cell under it at the cell under the reading cell. -/
theorem rowAt_doubledApex_castSucc {a d : Fin (I.doubled hLR).card}
    (hd : d ∈ (I.doubled hLR).toCellScheme.below ((I.doubled hLR).toCellScheme.gradedIndex a)) :
    (I.doubledApex hLR hI).rowAt a.castSucc d.castSucc =
      I.left.rowAt (I.doubledCell hLR a) (I.doubledCell hLR d) := by
  rw [rowAt_doubledApex_castSucc', (I.isDoubling_doubled hLR).rowAt_eq a d hd]

/-- The cells of the doubled coface visible through a coatom are old cells. -/
private theorem mem_range_old_castSucc {f : Fin 2 ↪ Fin 3} (hf : univ.map f ≠ univ)
    (z : Fin (I.doubledApex hLR hI).card)
    (hz : ((I.doubledApex hLR hI).toCellScheme.scope z : Set (Fin 3)) ⊆ Set.range f) :
    z ∈ Set.range fun d ↦ (I.old hLR d).castSucc := by
  have huniv {C : Finset (Fin 3)} (hC : C = univ) (hCf : (C : Set (Fin 3)) ⊆ Set.range f) :
      False := by
    subst hC
    refine hf (eq_univ_of_forall fun x ↦ ?_)
    obtain ⟨y, hy⟩ := hCf (mem_coe.mpr (mem_univ x))
    exact mem_map.mpr ⟨y, mem_univ _, hy⟩
  induction z using Fin.lastCases with
  | last =>
    exact (huniv (congrArg Prod.fst (I.gradedIndex_doubledApex_last hLR hI)) hz).elim
  | cast z =>
    have hs : (I.doubledApex hLR hI).toCellScheme.scope z.castSucc =
        (I.doubled hLR).toCellScheme.scope z :=
      congrArg Prod.fst (I.gradedIndex_doubledApex_castSucc hLR hI z)
    obtain ⟨a, rfl⟩ := I.exists_old_eq hLR (d := z) fun he ↦ huniv (hs.trans he) hz
    exact ⟨a, rfl⟩

/-- The enumeration of the cells visible through a coatom, through the old cells. -/
private theorem cellMap_doubledApex_eq {f : Fin 2 ↪ Fin 3} (hf : univ.map f ≠ univ)
    {k : Fin ((I.doubledApex hLR hI).toScheme.comap f).card}
    {i : Fin (I.amalgam.toScheme.comap f).card} (hik : (i : ℕ) = k) :
    (I.doubledApex hLR hI).toScheme.cellMap f k =
      (I.old hLR (I.amalgam.toScheme.cellMap f i)).castSucc := by
  refine Scheme.cellMap_eq_of_strictMono_of_mem_range (S := I.amalgam.toScheme)
    (T := (I.doubledApex hLR hI).toScheme) (φ := fun d ↦ (I.old hLR d).castSucc) f ?_ ?_
    (I.mem_range_old_castSucc hLR hI hf) hik
  · exact Fin.strictMono_castSucc.comp
      ((Fin.strictMono_castAdd _).comp (Fin.strictMono_castAdd _))
  · intro d
    exact congrArg Prod.fst ((I.gradedIndex_doubledApex_castSucc hLR hI _).trans
      (I.gradedIndex_old hLR d))

/-- **The copies along the first coatom**: the cell of the doubled coface at a position of its face
along `Fin.castSuccEmb` is the copy along the first coatom of the cell of `T` at that position. -/
theorem cellMap_doubledApex_left
    {k : Fin ((I.doubledApex hLR hI).toScheme.comap Fin.castSuccEmb).card} {z : Fin I.left.card}
    (hkz : (k : ℕ) = z) :
    (I.doubledApex hLR hI).toScheme.cellMap Fin.castSuccEmb k =
      (I.old hLR (StageType.faceCell I.restrictFace_left z)).castSucc :=
  I.cellMap_doubledApex_eq hLR hI Coatom.univ_map_left_ne (i := Fin.cast
    (congrArg Scheme.card (StageType.comap_toScheme_of_restrictFace I.restrictFace_left)).symm z)
    hkz.symm

/-- **The copies along the second coatom.** -/
theorem cellMap_doubledApex_right
    {k : Fin ((I.doubledApex hLR hI).toScheme.comap (extendByLast Fin.castSuccEmb)).card}
    {z : Fin I.left.card} (hkz : (k : ℕ) = z) :
    (I.doubledApex hLR hI).toScheme.cellMap (extendByLast Fin.castSuccEmb) k =
      (I.old hLR (StageType.faceCell (I.restrictFace_right_left hLR) z)).castSucc :=
  I.cellMap_doubledApex_eq hLR hI Coatom.univ_map_right_ne (i := Fin.cast
    (congrArg Scheme.card
      (StageType.comap_toScheme_of_restrictFace (I.restrictFace_right_left hLR))).symm z)
    hkz.symm

/-- The cells of the doubled coface other than the apex have grade at most `2`. -/
theorem grade_doubled_le_two (d : Fin (I.doubled hLR).card) :
    (I.doubled hLR).toCellScheme.grade d ≤ 2 := by
  rw [← (I.isDoubling_doubled hLR).grade_eq]
  exact I.left.grade_le _

/-- **Rigidity**: a stage type on the scheme of the doubled coface with face `T` along the first
coatom labels every cell other than the apex as `T` labels the cell under it.  Its labels on the
doubled completion are lawful, hence symmetric below the full pair
(`Seed.eq_of_isLawfulBelow_doubled`), and on the copies along the first coatom they are those of
`T`. -/
theorem label_doubledApex_eq {Q : StageType.{u} α 3}
    (hQ : Q.toScheme = (I.doubledApex hLR hI).toScheme)
    (hQf : restrictFace Fin.castSuccEmb Q = some I.left) (d : Fin (I.doubled hLR).card)
    (v : Fin Q.card) (hv : (v : ℕ) = d.castSucc) :
    Q.label v = I.left.label (I.doubledCell hLR d) := by
  obtain ⟨Qs, Ql, Qwf, Qc, Qlaw, Qat⟩ := Q
  change Qs = _ at hQ
  subst hQ
  obtain rfl : v = d.castSucc := Fin.ext hv
  -- the labels on the doubled completion are lawful
  have hw : (I.doubled hLR).rows.IsLawful fun e ↦ Ql e.castSucc := by
    have hlow := Scheme.isLowerEmbedding_castSucc (S := I.doubled hLR) 3
      (apexRow (t := I.doubledWithLabel hLR hI) (I.doubledCompletion hLR hI).isLegalBelowFullGrade)
      (I.doubledCompletion hLR hI).isLegalBelowFullGrade.not_le
    have hc : CellScheme.Rows.comap (I.doubledApex hLR hI).rows hlow = (I.doubled hLR).rows :=
      Scheme.comap_rows_castSucc (h := (I.doubledCompletion hLR hI).isLegalBelowFullGrade.not_le)
    have h := Qlaw.comap hlow
    rw [hc] at h
    exact h
  have hbelow (e : Fin (I.doubled hLR).card) :
      e ∈ (I.doubled hLR).toCellScheme.below ((univ : Finset (Fin 3)), 2) :=
    ⟨subset_univ _, I.grade_doubled_le_two hLR e⟩
  -- the copy along the first coatom
  set z := I.doubledCell hLR d
  obtain ⟨k, hkz, hlab, -⟩ := exists_cellMap_of_restrictFace_eq hQf z
  have hk := I.cellMap_doubledApex_left hLR hI hkz
  have hsym := I.eq_of_isLawfulBelow_doubled hLR hI le_rfl (w := fun e ↦ Ql e.castSucc)
    (hw.isLawfulBelow _) (hbelow d)
    (hbelow (I.old hLR (StageType.faceCell I.restrictFace_left z)))
    (by rw [doubledCell_old, doublingCell_faceCell_left])
  change Ql d.castSucc = _
  rw [hsym, ← hlab]
  change _ = Ql ((I.doubledApex hLR hI).toScheme.cellMap Fin.castSuccEmb k)
  rw [hk]

/-- The cells of the doubled completion lie below every cell of graded index `(univ, 2)`. -/
theorem mem_below_of_gradedIndex_eq {x : Fin (I.doubled hLR).card}
    (hx : (I.doubled hLR).toCellScheme.gradedIndex x = ((univ : Finset (Fin 3)), 2))
    (d : Fin (I.doubled hLR).card) :
    d ∈ (I.doubled hLR).toCellScheme.below ((I.doubled hLR).toCellScheme.gradedIndex x) := by
  rw [CellScheme.mem_below, hx]
  exact ⟨subset_univ _, I.grade_doubled_le_two hLR d⟩

/-- In the doubled coface, the old cells lie below every copy of graded index `(univ, 2)`. -/
theorem mem_below_doubledApex {x : Fin (I.doubled hLR).card}
    (hx : (I.doubled hLR).toCellScheme.gradedIndex x = ((univ : Finset (Fin 3)), 2))
    (d : Fin (I.doubled hLR).card) :
    d.castSucc ∈ (I.doubledApex hLR hI).toCellScheme.below
      ((I.doubledApex hLR hI).toCellScheme.gradedIndex x.castSucc) := by
  change (I.doubledApex hLR hI).toCellScheme.gradedIndex d.castSucc ≤
    (I.doubledApex hLR hI).toCellScheme.gradedIndex x.castSucc
  rw [I.gradedIndex_doubledApex_castSucc hLR hI, I.gradedIndex_doubledApex_castSucc hLR hI]
  exact I.mem_below_of_gradedIndex_eq hLR hx d

/-- The row of a copy of graded index `(univ, 2)` at an old cell, through `T`. -/
theorem row_doubledApex {x d : Fin (I.doubled hLR).card}
    (hx : (I.doubled hLR).toCellScheme.gradedIndex x = ((univ : Finset (Fin 3)), 2))
    (hd : d.castSucc ∈ (I.doubledApex hLR hI).toCellScheme.below
      ((I.doubledApex hLR hI).toCellScheme.gradedIndex x.castSucc)) :
    (I.doubledApex hLR hI).rows.row x.castSucc ⟨d.castSucc, hd⟩ =
      I.left.rowAt (I.doubledCell hLR x) (I.doubledCell hLR d) := by
  rw [← Scheme.rowAt_of_mem hd]
  exact I.rowAt_doubledApex_castSucc hLR hI (I.mem_below_of_gradedIndex_eq hLR hx d)

/-- **The reading of the doubled coface is the reading of `T`**: the copy of full scope and grade
`2` over a cell `c` of `T` reads the copy of `j` along the second coatom through the copy of `b`
along the first, as `j` is labelled in `T`, exactly when `c` reads `j` through `b` in `T`. -/
theorem readsThroughCap_doubledApex_iff {x : Fin (I.doubled hLR).card}
    (hx : (I.doubled hLR).toCellScheme.gradedIndex x = ((univ : Finset (Fin 3)), 2))
    {b' : Fin ((I.doubledApex hLR hI).toScheme.comap Fin.castSuccEmb).card}
    {b : Fin I.left.card} (hbb : (b' : ℕ) = b)
    {i : Fin ((I.doubledApex hLR hI).toScheme.comap (extendByLast Fin.castSuccEmb)).card}
    {j : Fin I.left.card} (hij : (i : ℕ) = j) :
    I.left.ReadsThroughCap (I.doubledApex hLR hI).toScheme b' x.castSucc
        ((I.doubledApex hLR hI).toScheme.cellMap (extendByLast Fin.castSuccEmb) i)
        (I.left.label j) ↔
      I.left.ReadsOwnCellThroughCap (I.doubledCell hLR x) b j := by
  have hT := StageType.comap_toScheme_of_restrictFace (I.restrictFace_left_doubledApex hLR hI)
  set c := I.doubledCell hLR x
  -- the cells involved, as old cells
  set e₀ := I.old hLR (StageType.faceCell (I.restrictFace_right_left hLR) j)
  set b₀ := I.old hLR (StageType.faceCell I.restrictFace_left b)
  have he : (I.doubledApex hLR hI).toScheme.cellMap (extendByLast Fin.castSuccEmb) i =
      e₀.castSucc := I.cellMap_doubledApex_right hLR hI hij
  have hb : (I.doubledApex hLR hI).toScheme.cellMap Fin.castSuccEmb b' = b₀.castSucc :=
    I.cellMap_doubledApex_left hLR hI hbb
  have hπe : I.doubledCell hLR e₀ = j := by rw [doubledCell_old, doublingCell_faceCell_right]
  have hπb : I.doubledCell hLR b₀ = b := by rw [doubledCell_old, doublingCell_faceCell_left]
  have hgb : (I.doubledApex hLR hI).toCellScheme.grade
      ((I.doubledApex hLR hI).toScheme.cellMap Fin.castSuccEmb b') = I.left.toCellScheme.grade b :=
    Scheme.grade_congr hT hbb
  have hmem := I.mem_below_doubledApex hLR hI hx
  -- the rows at the three cells, through `T`
  have hR {y : Fin (I.doubledApex hLR hI).card} {d : Fin (I.doubled hLR).card}
      (hy : y = d.castSucc) (hy' : y ∈ (I.doubledApex hLR hI).toCellScheme.below
        ((I.doubledApex hLR hI).toCellScheme.gradedIndex x.castSucc)) :
      (I.doubledApex hLR hI).rows.row x.castSucc ⟨y, hy'⟩ =
        I.left.rowAt c (I.doubledCell hLR d) := by
    subst hy
    exact I.row_doubledApex hLR hI hx hy'
  have hmemy {y : Fin (I.doubledApex hLR hI).card} {d : Fin (I.doubled hLR).card}
      (hy : y = d.castSucc) : y ∈ (I.doubledApex hLR hI).toCellScheme.below
        ((I.doubledApex hLR hI).toCellScheme.gradedIndex x.castSucc) := hy ▸ hmem d
  have hRe := hR he
  have hRb := hR hb
  rw [hπe] at hRe
  rw [hπb] at hRb
  -- a reference cell along the first coatom: the copy of a cell of `T`
  have hRa {a : Fin ((I.doubledApex hLR hI).toScheme.comap Fin.castSuccEmb).card}
      {a₀ : Fin I.left.card} (haa : (a : ℕ) = a₀) :
      (I.doubledApex hLR hI).toScheme.cellMap Fin.castSuccEmb a =
        (I.old hLR (StageType.faceCell I.restrictFace_left a₀)).castSucc ∧
      I.doubledCell hLR (I.old hLR (StageType.faceCell I.restrictFace_left a₀)) = a₀ :=
    ⟨I.cellMap_doubledApex_left hLR hI haa, by
      rw [doubledCell_old, doublingCell_faceCell_left]⟩
  constructor
  · intro h
    obtain ⟨hbot, htop, hord⟩ := h (hmemy he) (hmemy hb)
    refine ⟨fun hl ↦ ?_, fun hl ↦ ?_, fun μ k hμ hl ↦ ?_⟩
    · rw [← hRe (hmemy he)]
      exact hbot hl
    · rw [← hRe (hmemy he), ← hRb (hmemy hb)]
      exact htop hl
    · obtain ⟨hk, -, -, -, c', -, -, -, -, -, hre⟩ := hord μ k hμ hl
      exact ⟨hgb ▸ hk, c', by rw [← hRe (hmemy he)]; exact hre⟩
  · rintro ⟨hbot, htop, hord⟩ he' hb'
    refine ⟨fun hl ↦ ?_, fun hl ↦ ?_, fun μ k hμ hl ↦ ?_⟩
    · rw [hRe he']
      exact hbot hl
    · rw [hRe he', hRb hb']
      exact htop hl
    · obtain ⟨hk, c', hc'⟩ := hord μ k hμ hl
      set a : Fin ((I.doubledApex hLR hI).toScheme.comap Fin.castSuccEmb).card :=
        Fin.cast (congrArg Scheme.card hT).symm j
      have ha := hRa (a := a) (a₀ := j) rfl
      refine ⟨hgb.symm ▸ hk, a, j, k, c', rfl, hl, hgb.symm ▸ hk, hmemy ha.1, ?_, ?_⟩
      · rw [hR ha.1 (hmemy ha.1), ha.2]
        exact hc'
      · rw [hRe he']
        exact hc'

/-! ### The copies of full scope and grade `2` -/

/-- A cell of the doubled completion of graded index `(univ, 2)` is a copy of full scope. -/
theorem exists_natAdd_eq {x : Fin (I.doubled hLR).card}
    (hx : (I.doubled hLR).toCellScheme.gradedIndex x = ((univ : Finset (Fin 3)), 2)) :
    ∃ i, Fin.natAdd _ i = x := by
  induction x using Fin.addCases with
  | right i => exact ⟨i, rfl⟩
  | left d =>
    exfalso
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd] at hx
    induction d using Fin.addCases with
    | left a =>
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd] at hx
      exact I.scope_ne_univ a (congrArg Prod.fst hx)
    | right i =>
      rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd] at hx
      exact absurd (congrArg Prod.snd hx) (by decide)

/-- The cell of `T` under a copy of full scope and grade `2` has graded index `(univ, 2)`. -/
theorem gradedIndex_doubledCell {x : Fin (I.doubled hLR).card}
    (hx : (I.doubled hLR).toCellScheme.gradedIndex x = ((univ : Finset (Fin 3)), 2)) :
    I.left.toCellScheme.gradedIndex (I.doubledCell hLR x) = ((univ : Finset (Fin 2)), 2) := by
  rw [(I.isDoubling_doubled hLR).gradedIndex_eq, show (I.doubled hLR).toCellScheme.scope x = univ
    from congrArg Prod.fst hx, Scheme.image_collapseLast_univ,
    show (I.doubled hLR).toCellScheme.grade x = 2 from congrArg Prod.snd hx]

/-- Every cell of `T` of graded index `(univ, 2)` has a copy of full scope. -/
theorem exists_doubledCell_eq {c : Fin I.left.card}
    (hc : I.left.toCellScheme.gradedIndex c = ((univ : Finset (Fin 2)), 2)) :
    ∃ x, (I.doubled hLR).toCellScheme.gradedIndex x = ((univ : Finset (Fin 3)), 2) ∧
      I.doubledCell hLR x = c := by
  obtain ⟨i, rfl⟩ := Scheme.exists_fullCell_eq hc
  exact ⟨Fin.natAdd _ i, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i,
    by rw [doubledCell, Fin.append_right]⟩

/-- The copies of full scope and grade `2` are one for each cell of `T` under them. -/
theorem eq_of_doubledCell_eq {x x' : Fin (I.doubled hLR).card}
    (hx : (I.doubled hLR).toCellScheme.gradedIndex x = ((univ : Finset (Fin 3)), 2))
    (hx' : (I.doubled hLR).toCellScheme.gradedIndex x' = ((univ : Finset (Fin 3)), 2))
    (h : I.doubledCell hLR x = I.doubledCell hLR x') : x = x' := by
  obtain ⟨i, rfl⟩ := I.exists_natAdd_eq hLR hx
  obtain ⟨i', rfl⟩ := I.exists_natAdd_eq hLR hx'
  rw [doubledCell, Fin.append_right, Fin.append_right, Scheme.fullCell, Scheme.fullCell] at h
  rw [(I.left.toScheme.fullCells 2).equivFin.symm.injective (Subtype.ext h)]

/-- A cell of the doubled coface of graded index `(univ, 2)` is the copy of a cell of the doubled
completion. -/
theorem exists_castSucc_eq {u : Fin (I.doubledApex hLR hI).card}
    (hu : (I.doubledApex hLR hI).toCellScheme.gradedIndex u = ((univ : Finset (Fin 3)), 2)) :
    ∃ x, x.castSucc = u ∧
      (I.doubled hLR).toCellScheme.gradedIndex x = ((univ : Finset (Fin 3)), 2) := by
  induction u using Fin.lastCases with
  | last =>
    rw [I.gradedIndex_doubledApex_last hLR hI] at hu
    exact absurd (congrArg Prod.snd hu) (by decide)
  | cast x => exact ⟨x, rfl, (I.gradedIndex_doubledApex_castSucc hLR hI x).symm.trans hu⟩

/-! ### Gated reading extensions on the doubled coface -/

variable {ξ : Ordinal.{u}} (J : Seed.{u} (blockStage (ξ + 1)) 1) (hJ : J.left = J.right)
  (hJl : J.left.IsLegal)

/-- **The doubled coface is a gated reading extension when `T` carries the gate.**  Let `T` (the
coatom type of a seed whose two coatom types are equal) have a cap `b` of grade `2`, a gate `c_G`
at `(univ, 2)` whose row is `⊥` at every other cell there outside a set `S_T`, a ceiling in `S_T`,
and readers `S_T` at `(univ, 2)` each reading every new cell of `T` (a cell whose scope contains
the point `1`) through `b` (`StageType.ReadsOwnCellThroughCap`), with `c_G` not labelled `⊥`.  Then
the copies of full scope over `c_G` and over `S_T` are a gate and readers of a gated reading
extension on the doubled coface for `T⁺ = T`, `f = Fin.castSuccEmb` and `D = T`; and every stage
type on the doubled coface with face `T` labels the gate as `T` labels `c_G`. -/
theorem isGatedReadingExtension_doubledApex {b : Fin J.left.card}
    (hb2 : J.left.toCellScheme.grade b = 2) {cG : Fin J.left.card} {ST : Set (Fin J.left.card)}
    (hG : J.left.toCellScheme.gradedIndex cG = ((univ : Finset (Fin 2)), 2))
    (honly : J.left.rows.ReadsOnly cG ST)
    (hceil : ∃ K ∈ ST, ∃ hKG : J.left.toCellScheme.gradedIndex K =
      J.left.toCellScheme.gradedIndex cG, J.left.rows.row cG
        ⟨cG, CellScheme.mem_below_gradedIndex _ cG⟩ ≤ J.left.rows.row cG ⟨K, hKG.le⟩)
    (hreaders : ∀ c ∈ ST, J.left.toCellScheme.gradedIndex c = J.left.toCellScheme.gradedIndex cG ∧
      ∀ j, Fin.last 1 ∈ J.left.toCellScheme.scope j → J.left.ReadsOwnCellThroughCap c b j)
    (hdisp : J.left.label cG ≠ ⊥) :
    ∃ (G : Fin (J.doubledApex hJ hJl).card) (S : Set (Fin (J.doubledApex hJ hJl).card)),
      IsGatedReadingExtension J.left Fin.castSuccEmb J.left b (J.doubledApex hJ hJl).toScheme
        G S ∧
      ∀ Q : StageType.{u} (blockStage (ξ + 1)) 3, Q.toScheme = (J.doubledApex hJ hJl).toScheme →
        restrictFace Fin.castSuccEmb Q = some J.left →
          ∀ v : Fin Q.card, (v : ℕ) = G → Q.label v = J.left.label cG := by
  set E := J.doubledApex hJ hJl
  obtain ⟨xG, hxG, hπG⟩ := J.exists_doubledCell_eq hJ hG
  set S : Set (Fin E.card) := {u | ∃ x, x.castSucc = u ∧
    (J.doubled hJ).toCellScheme.gradedIndex x = ((univ : Finset (Fin 3)), 2) ∧
      J.doubledCell hJ x ∈ ST}
  have hfL := J.restrictFace_left_doubledApex hJ hJl
  have hfR := J.restrictFace_right_doubledApex hJ hJl
  have hgi (x : Fin (J.doubled hJ).card)
      (hx : (J.doubled hJ).toCellScheme.gradedIndex x = ((univ : Finset (Fin 3)), 2)) :
      E.toCellScheme.gradedIndex x.castSucc = ((univ : Finset (Fin 3)), 2) :=
    (J.gradedIndex_doubledApex_castSucc hJ hJl x).trans hx
  have hGidx := hgi xG hxG
  -- the row of the gate at a copy of full scope
  have hrowG (x : Fin (J.doubled hJ).card) (hx' : x.castSucc ∈ E.toCellScheme.below
      (E.toCellScheme.gradedIndex xG.castSucc)) :
      E.rows.row xG.castSucc ⟨x.castSucc, hx'⟩ = J.left.rowAt cG (J.doubledCell hJ x) := by
    rw [J.row_doubledApex hJ hJl hxG hx', hπG]
  refine ⟨xG.castSucc, S, ⟨J.isLegal_doubledApex hJ hJl,
    ((restrictFace_eq_some_iff _ _).mp hfL).1, comap_toScheme_of_restrictFace hfL,
    ((restrictFace_eq_some_iff _ _).mp hfR).1, comap_toScheme_of_restrictFace hfR,
    by rw [hGidx, hb2], ?_, ?_, ?_, ?_⟩, fun Q hQ hQf v hv ↦ ?_⟩
  · -- the gate reads only the readers
    intro t ht htG htS
    obtain ⟨x, rfl, hx⟩ := J.exists_castSucc_eq hJ hJl (ht.trans hGidx)
    have hcx := J.gradedIndex_doubledCell hJ hx
    have hne : J.doubledCell hJ x ≠ cG := fun h ↦
      htG (by rw [J.eq_of_doubledCell_eq hJ hx hxG (h.trans hπG.symm)])
    have hnS : J.doubledCell hJ x ∉ ST := fun h ↦ htS ⟨x, rfl, hx, h⟩
    refine (hrowG x _).trans ?_
    rw [Scheme.rowAt_of_mem ((hcx.trans hG.symm).le)]
    exact honly _ (hcx.trans hG.symm) hne hnS
  · -- the ceiling
    obtain ⟨K, hK, hKG, hrow⟩ := hceil
    obtain ⟨xK, hxK, hπK⟩ := J.exists_doubledCell_eq hJ (hKG.trans hG)
    have hKG' : E.toCellScheme.gradedIndex xK.castSucc = E.toCellScheme.gradedIndex xG.castSucc :=
      (hgi xK hxK).trans hGidx.symm
    refine ⟨xK.castSucc, ⟨xK, rfl, hxK, hπK ▸ hK⟩, hKG', ?_⟩
    refine le_of_eq_of_le (hrowG xG _) (le_of_le_of_eq ?_ (hrowG xK _).symm)
    rw [hπG, hπK, Scheme.rowAt_of_mem (CellScheme.mem_below_gradedIndex _ cG),
      Scheme.rowAt_of_mem hKG.le]
    exact hrow
  · -- the readers
    rintro u ⟨x, rfl, hx, hxS⟩
    obtain ⟨-, hread⟩ := hreaders _ hxS
    refine ⟨(hgi x hx).trans hGidx.symm, Fin.cast (congrArg Scheme.card
      (comap_toScheme_of_restrictFace hfL)).symm b, rfl, fun i j hij hj ↦ ?_⟩
    exact (J.readsThroughCap_doubledApex_iff hJ hJl hx rfl hij).mpr (hread j hj)
  · -- the display: the stage reduction of the doubled coface
    refine ⟨E.reduce (isSuccPrelimit_blockStage ξ),
      reduce_mem_cofaces _ (J.mem_cofaces_doubledApex hJ hJl), rfl, fun i hi ↦ ?_⟩
    obtain rfl : i = xG.castSucc := Fin.ext hi
    change Label.reduce _ (E.label xG.castSucc) ≠ ⊥
    rw [Ne, reduce_eq_bot_iff, J.label_doubledApex_castSucc hJ hJl, hπG]
    exact hdisp
  · rw [J.label_doubledApex_eq hJ hJl hQ hQf xG v hv, hπG]

/-- **A gated reading extension on the doubled coface gives the reading in `T`**: for a cap `b` of
grade `2`, some cell of `T` at `(univ, 2)` (the cell under a ceiling) reads every new cell of `T`
through `b`. -/
theorem IsGatedReadingExtension.exists_readsOwnCellThroughCap_doubledApex {b : Fin J.left.card}
    (hb2 : J.left.toCellScheme.grade b = 2) {G : Fin (J.doubledApex hJ hJl).card}
    {S : Set (Fin (J.doubledApex hJ hJl).card)}
    (h : IsGatedReadingExtension J.left Fin.castSuccEmb J.left b (J.doubledApex hJ hJl).toScheme
      G S) :
    ∃ c, J.left.toCellScheme.gradedIndex c = ((univ : Finset (Fin 2)), 2) ∧
      ∀ j, Fin.last 1 ∈ J.left.toCellScheme.scope j → J.left.ReadsOwnCellThroughCap c b j := by
  obtain ⟨K, hK, -⟩ := h.exists_ceiling
  obtain ⟨hKG, b', hbb, hread⟩ := h.readers K hK
  have hKidx : (J.doubledApex hJ hJl).toCellScheme.gradedIndex K =
      ((univ : Finset (Fin 3)), 2) := by
    rw [hKG, h.gradedIndex_gate, hb2]
  obtain ⟨x, rfl, hx⟩ := J.exists_castSucc_eq hJ hJl hKidx
  refine ⟨J.doubledCell hJ x, J.gradedIndex_doubledCell hJ hx, fun j hj ↦ ?_⟩
  have hT := comap_toScheme_of_restrictFace (J.restrictFace_right_doubledApex hJ hJl)
  set i : Fin ((J.doubledApex hJ hJl).toScheme.comap (extendByLast Fin.castSuccEmb)).card :=
    Fin.cast (congrArg Scheme.card hT).symm j
  exact (J.readsThroughCap_doubledApex_iff hJ hJl hx hbb (i := i) rfl).mp (hread i j rfl hj)

/-- **Recovery at the self-donor without reading** (by rigidity): the doubled coface is a stable
recovery scheme for `T`, `f = Fin.castSuccEmb`, the donor `D = T` and every `γ`.  Every stage type
on it with face `T` along the first coatom has face exactly `T` along the second: it labels the
copy of a cell of `T` as `T` does.  No gate, reader or cap is used. -/
theorem isStableRecoveryScheme_doubledApex (γ : Ordinal.{u}) :
    J.left.IsStableRecoveryScheme Fin.castSuccEmb J.left γ (J.doubledApex hJ hJl).toScheme := by
  have hfR := J.restrictFace_right_doubledApex hJ hJl
  refine ⟨⟨(J.doubledApex hJ hJl).reduce (isSuccPrelimit_blockStage ξ),
    reduce_mem_cofaces _ (J.mem_cofaces_doubledApex hJ hJl), rfl⟩, fun Q' hQ' hQ'f ↦ ?_⟩
  obtain ⟨Qs, Ql, Qwf, Qc, Qlaw, Qat⟩ := Q'
  change Qs = _ at hQ'
  subst hQ'
  have hmem : univ.map (extendByLast Fin.castSuccEmb) ∈
      (J.doubledApex hJ hJl).toCellScheme.faces := ((restrictFace_eq_some_iff _ _).mp hfR).1
  refine ⟨StageType.comap ⟨_, Ql, Qwf, Qc, Qlaw, Qat⟩ _ hmem,
    restrictFace_of_mem (t := ⟨_, Ql, Qwf, Qc, Qlaw, Qat⟩) _ hmem,
    (comap_toScheme_of_restrictFace hfR : (J.doubledApex hJ hJl).toScheme.comap _ = _),
    fun i j hij ↦ ?_⟩
  -- the label at the copy along the second coatom
  have hlab : (StageType.comap ⟨_, Ql, Qwf, Qc, Qlaw, Qat⟩ _ hmem).label i = J.left.label j := by
    change Ql ((J.doubledApex hJ hJl).toScheme.cellMap (extendByLast Fin.castSuccEmb) i) = _
    rw [J.cellMap_doubledApex_right hJ hJl hij]
    refine (J.label_doubledApex_eq hJ hJl (Q := ⟨_, Ql, Qwf, Qc, Qlaw, Qat⟩) rfl hQ'f _ _
      rfl).trans ?_
    rw [doubledCell_old, doublingCell_faceCell_right]
  refine ⟨fun _ ↦ hlab, fun htop ↦ ?_⟩
  rw [hlab, htop]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)

/-- **Two blocks**: in a gated reading extension on the doubled coface, a reader over a cell of
`T` labelled at least `μ₂ + N` (`N` the grade of the cap) does not read two new cells of blocks
`μ₁ < μ₂` both in the natural strip.  The doubled coface itself is a stage type with face `T` that
labels the reader as `T` labels the cell under it (`StageType.IsGatedReadingExtension.label_lt_of_
lt_omega0`). -/
theorem IsGatedReadingExtension.not_lt_omega0_doubledApex {b : Fin J.left.card}
    {G : Fin (J.doubledApex hJ hJl).card} {S : Set (Fin (J.doubledApex hJ hJl).card)}
    (h : IsGatedReadingExtension J.left Fin.castSuccEmb J.left b (J.doubledApex hJ hJl).toScheme
      G S) {x : Fin (J.doubled hJ).card} (hu : x.castSucc ∈ S) {j₁ j₂ : Fin J.left.card}
    (hj₁ : Fin.last 1 ∈ J.left.toCellScheme.scope j₁)
    (hj₂ : Fin.last 1 ∈ J.left.toCellScheme.scope j₂) {μ₁ μ₂ : Ordinal.{u}}
    (hμ₁ : Order.IsSuccPrelimit μ₁) (hμ₂ : Order.IsSuccPrelimit μ₂) (hμ : μ₁ < μ₂) {n₁ n₂ : ℕ}
    (hD₁ : J.left.label j₁ = ((μ₁ + n₁ : Ordinal.{u}) : Label.{u}))
    (hD₂ : J.left.label j₂ = ((μ₂ + n₂ : Ordinal.{u}) : Label.{u}))
    (hlab : ((μ₂ + J.left.toCellScheme.grade b : Ordinal.{u}) : Label.{u}) ≤
      J.left.label (J.doubledCell hJ x))
    {i₁ i₂ : Fin ((J.doubledApex hJ hJl).toScheme.comap (extendByLast Fin.castSuccEmb)).card}
    (hij₁ : (i₁ : ℕ) = j₁) (hij₂ : (i₂ : ℕ) = j₂)
    (he₁ : (J.doubledApex hJ hJl).toScheme.cellMap (extendByLast Fin.castSuccEmb) i₁ ∈
      (J.doubledApex hJ hJl).toCellScheme.below
        ((J.doubledApex hJ hJl).toCellScheme.gradedIndex x.castSucc))
    (he₂ : (J.doubledApex hJ hJl).toScheme.cellMap (extendByLast Fin.castSuccEmb) i₂ ∈
      (J.doubledApex hJ hJl).toCellScheme.below
        ((J.doubledApex hJ hJl).toCellScheme.gradedIndex x.castSucc)) :
    ¬ ((J.doubledApex hJ hJl).rows.row x.castSucc ⟨_, he₁⟩ < ((ω : Ordinal.{u}) : Label.{u}) ∧
      (J.doubledApex hJ hJl).rows.row x.castSucc ⟨_, he₂⟩ < ((ω : Ordinal.{u}) : Label.{u})) := by
  rintro ⟨hs₁, hs₂⟩
  have hlt := h.label_lt_of_lt_omega0 hu hj₁ hj₂ hμ₁ hμ₂ hμ hD₁ hD₂ hij₁ hij₂ he₁ he₂ hs₁ hs₂
    (J.doubledApex hJ hJl) rfl (J.restrictFace_left_doubledApex hJ hJl) x.castSucc rfl
  rw [J.label_doubledApex_castSucc hJ hJl] at hlt
  exact (lt_of_lt_of_le hlt hlab).false

end Seed

/-! ### Types with an apex -/

namespace StageType

variable {α ξ : Ordinal.{u}} {n : ℕ} {t : StageType.{u} α n} (ht : t.IsLegalBelowFullGrade)
  (hn : 0 < n)

/-- **The apex reads every cell through its block coding**: its row at a cell is the coded copy
of the label of the cell. -/
theorem rowAt_addApex_last (d : Fin (t.addApex ht hn).card) :
    (t.addApex ht hn).rowAt (Fin.last _) d =
      blockEncode (apexCodes ht) n ((t.addApex ht hn).label d) := by
  have hmem : d ∈ (t.addApex ht hn).toCellScheme.below
      ((t.addApex ht hn).toCellScheme.gradedIndex (Fin.last _)) := by
    have hg : (t.addApex ht hn).toCellScheme.gradedIndex (Fin.last _) = (univ, n) :=
      Scheme.appendFullCellScheme_gradedIndex_last _ _
    change (t.addApex ht hn).toCellScheme.gradedIndex d ≤
      (t.addApex ht hn).toCellScheme.gradedIndex (Fin.last _)
    refine le_of_le_of_eq (b := ((univ : Finset (Fin n)), n)) ?_ hg.symm
    exact ⟨subset_univ _, (t.addApex ht hn).grade_le d⟩
  rw [Scheme.rowAt_of_mem hmem]
  refine (Scheme.appendFullCell_row_last (r := apexRow ht) (h := ht.not_le) ⟨d, hmem⟩).trans ?_
  induction d using Fin.lastCases with
  | last => rw [apexRow_last, addApex_label_last]
  | cast d => rw [apexRow_castSucc, addApex_label_castSucc]

/-- **The apex reads every cell through itself as cap**, for a stage type whose ordinal labels
have finite parts below `2`: `⊥` as `⊥`, `⊤` as the apex reads itself, and `μ + k` at
`ω · c' + k` for the code rank `c'` of its block. -/
theorem readsOwnCellThroughCap_addApex (hcap : ∀ (j : Fin (t.addApex ht hn).card)
      (μ : Ordinal.{u}) (k : ℕ), Order.IsSuccPrelimit μ →
        (t.addApex ht hn).label j = ((μ + k : Ordinal.{u}) : Label.{u}) → k < n)
    (j : Fin (t.addApex ht hn).card) :
    (t.addApex ht hn).ReadsOwnCellThroughCap (Fin.last _) (Fin.last _) j := by
  refine ⟨fun hl ↦ ?_, fun hl ↦ ?_, fun μ k hμ hl ↦ ⟨?_, ?_⟩⟩
  · refine (rowAt_addApex_last ht hn j).trans ?_
    rw [hl, blockEncode_bot]
  · refine (rowAt_addApex_last ht hn j).trans ((rowAt_addApex_last ht hn _).trans ?_).symm
    rw [hl]
    exact congrArg _ (addApex_label_last ht hn)
  · exact lt_of_lt_of_eq (hcap j μ k hμ hl) (Scheme.appendFullCellScheme_grade_last _ _).symm
  · -- the label is a code value
    have hV : ((μ + k : Ordinal.{u}) : Label.{u}) ∈ apexCodes ht := by
      induction j using Fin.lastCases with
      | last =>
        have h' : (⊤ : Label.{u}) = ((μ + k : Ordinal.{u}) : Label.{u}) :=
          (addApex_label_last ht hn).symm.trans hl
        exact absurd h'.symm (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne
      | cast d =>
        rw [addApex_label_castSucc] at hl
        rw [← hl]
        exact label_mem_apexCodes ht d
    obtain ⟨c, rfl⟩ := isSuccPrelimit_iff_omega0_dvd.mp hμ
    have hdiv : (ω * c + k) / ω = c := by
      rw [Ordinal.mul_add_div _ omega0_ne_zero, Ordinal.div_eq_zero_of_lt (natCast_lt_omega0 k),
        add_zero]
    have hblock := div_mem_valueBlocks hV
    refine ⟨(codeRank (apexCodes ht) c : Ordinal.{u}), ?_⟩
    refine (rowAt_addApex_last ht hn j).trans ?_
    have hb' : c ∈ valueBlocks (apexCodes ht) := hdiv ▸ hblock
    rw [hl, blockEncode_coe, blockEncodeOrd, hdiv, Ordinal.mul_add_mod_self,
      Ordinal.mod_eq_of_lt (natCast_lt_omega0 k)]
    simp only [hb', ↓reduceIte]

end StageType


/-! ### Every type with an apex is an instance -/

namespace StageType

variable {ξ : Ordinal.{u}}

/-- **The doubled coface of a type with an apex is a gated reading extension.**  Let `T⁺` be a
type on two points with an apex (`t.addApex`, `t` legal below the full grade), with face `p` along
`Fin.castSuccEmb`, and let the apex be a graded cap of `T⁺` for the self-donor `D = T⁺`.  The apex
reads every cell through its block coding, so it is its own gate, reader and ceiling in `T⁺`; the
doubled coface of the seed of `T⁺` with itself is a gated reading extension for `T⁺`,
`f = Fin.castSuccEmb`, `D = T⁺` and the apex as cap, and every stage type on it with face `T⁺`
labels its gate `⊤`. -/
theorem exists_isGatedReadingExtension_doubledApex_addApex
    {t : StageType.{u} (blockStage (ξ + 1)) 2} (ht : t.IsLegalBelowFullGrade)
    {p : StageType.{u} (blockStage (ξ + 1)) 1}
    (hp : restrictFace Fin.castSuccEmb (t.addApex ht two_pos) = some p) {γ : Ordinal.{u}}
    (hcap : IsGradedCap ξ (t.addApex ht two_pos) (t.addApex ht two_pos) γ (Fin.last _)) :
    ∃ (G : Fin _) (S : Set (Fin _)),
      IsGatedReadingExtension (t.addApex ht two_pos) Fin.castSuccEmb (t.addApex ht two_pos)
        (Fin.last _) ((Seed.ofCoatoms (isLegal_addApex ht two_pos) (isLegal_addApex ht two_pos)
          hp hp).doubledApex rfl (isLegal_addApex ht two_pos)).toScheme G S ∧
      ∀ Q : StageType.{u} (blockStage (ξ + 1)) 3, Q.toScheme = ((Seed.ofCoatoms
          (isLegal_addApex ht two_pos) (isLegal_addApex ht two_pos) hp hp).doubledApex rfl
            (isLegal_addApex ht two_pos)).toScheme →
        restrictFace Fin.castSuccEmb Q = some (t.addApex ht two_pos) →
          ∀ v : Fin Q.card, (v : ℕ) = G → Q.label v = ⊤ := by
  set Tp := t.addApex ht two_pos
  have hT := isLegal_addApex ht two_pos
  have hgl : Tp.toCellScheme.gradedIndex (Fin.last _) = ((univ : Finset (Fin 2)), 2) :=
    Scheme.appendFullCellScheme_gradedIndex_last _ _
  -- the finite parts of the ordinal labels lie below `2`
  have hfin (j : Fin Tp.card) (μ : Ordinal.{u}) (k : ℕ) (hμ : Order.IsSuccPrelimit μ)
      (hl : Tp.label j = ((μ + k : Ordinal.{u}) : Label.{u})) : k < 2 := by
    obtain ⟨μ', k', -, -, hμ', he, hk', -⟩ := hcap.2.2.2 j (μ + k) hl
    obtain ⟨-, rfl⟩ := (add_natCast_eq_add_natCast_iff hμ hμ').mp he
    exact lt_of_lt_of_eq hk' (Scheme.appendFullCellScheme_grade_last _ _)
  obtain ⟨G, S, hGS, hlab⟩ := Seed.isGatedReadingExtension_doubledApex
    (Seed.ofCoatoms hT hT hp hp) rfl hT (b := Fin.last _)
    (Scheme.appendFullCellScheme_grade_last _ _) (cG := Fin.last _) (ST := {Fin.last _}) hgl
    (fun t' ht' htG _ ↦ absurd (eq_of_grade_addApex ht two_pos
      ((congrArg Prod.snd ht').trans (congrArg Prod.snd hgl))) htG)
    ⟨Fin.last _, rfl, rfl, le_rfl⟩
    (fun c hc ↦ by
      obtain rfl : c = Fin.last _ := hc
      exact ⟨rfl, fun j _ ↦ readsOwnCellThroughCap_addApex ht two_pos hfin j⟩)
    (by
      change Tp.label (Fin.last _) ≠ ⊥
      rw [addApex_label_last]
      exact top_ne_bot)
  refine ⟨G, S, hGS, fun Q hQ hQf v hv ↦ (hlab Q hQ hQf v hv).trans ?_⟩
  exact addApex_label_last ht two_pos

/-! ### The requirement on the doubling design, and its refutation -/

variable (ξ) in
/-- **Doubled gated readings** (the requirement on the doubling design at the self-donor, defined,
not assumed anywhere): for every legal `T⁺` on two points at `λ_{ξ+1}` with face `p` along
`Fin.castSuccEmb`, and every graded cap `b` of `T⁺` for the self-donor `D = T⁺`, the doubled coface
of the seed of `T⁺` with itself carries a gate and readers forming a gated reading extension.  One
extension per input (the doubled coface), not per labelling. -/
def HasDoubledGatedReadings : Prop :=
  ∀ (Tp : StageType.{u} (blockStage (ξ + 1)) 2) (hT : Tp.IsLegal)
    (p : StageType.{u} (blockStage (ξ + 1)) 1) (hp : restrictFace Fin.castSuccEmb Tp = some p)
    (γ : Ordinal.{u}) (b : Fin Tp.card), IsGradedCap ξ Tp Tp γ b →
      ∃ (G : Fin _) (S : Set (Fin _)), IsGatedReadingExtension Tp Fin.castSuccEmb Tp b
        ((Seed.ofCoatoms hT hT hp hp).doubledApex rfl hT).toScheme G S

end StageType

namespace GatedExtensionCounterexample

/-- The face `{0}` of the private type `P`. -/
theorem mem_faces_castSuccEmb (α : Ordinal.{u}) :
    univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∈ (P α).toCellScheme.faces := by
  change _ ∈ Geometry.intervalPlan univ
  decide

/-- The seed of `P` with itself, along its face `{0}`. -/
noncomputable abbrev seedP (α : Ordinal.{u}) : Seed.{u} α 1 :=
  Seed.ofCoatoms (isLegal_P α) (isLegal_P α) (restrictFace_of_mem _ _ (mem_faces_castSuccEmb α))
    (restrictFace_of_mem _ _ (mem_faces_castSuccEmb α))

/-- The doubled coface of `P`. -/
noncomputable abbrev doubledP (α : Ordinal.{u}) : StageType.{u} α 3 :=
  (seedP α).doubledApex rfl (isLegal_P α)

/-- The cells of `P` of grade `2` are the two cells of full scope. -/
private theorem eq_three_or_four {x : Fin 5} (h : cellGrade x = 2) : x = 3 ∨ x = 4 := by
  fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl | (exfalso; revert h; decide)

/-- The rows of the two full cells of `P` at the full cells: `3` at the cell itself, `2` at the
other. -/
private theorem rowAt_P {α : Ordinal.{u}} {c d : Fin 5} (hc : cellGrade c = 2)
    (hd : cellGrade d = 2) :
    (P α).rowAt c d = if c = d then ((3 : ℕ) : Label.{u}) else ((2 : ℕ) : Label.{u}) := by
  have hmem : d ∈ (P α).toCellScheme.below ((P α).toCellScheme.gradedIndex c) := by
    change d ∈ cells.below (cells.gradedIndex c)
    rw [CellScheme.mem_below, gradedIndex_cells, gradedIndex_cells]
    fin_cases c <;> fin_cases d <;> first | decide | (exfalso; revert hc hd; decide)
  rw [Scheme.rowAt_of_mem hmem]
  fin_cases c <;> fin_cases d <;> first | rfl | (exfalso; revert hc hd; decide)

/-- **The doubled coface of `P` is a gated reading extension for no gate and readers**, at either
cap of grade `2` (the two cells of full scope, both `⊤`).  A reader is a copy over a cell `c` of
full scope, which would have to read both cells of full scope, labelled `⊤`, as it reads the cap;
the rows of `P` read them as `3` and `2`.  The failing clause is `readers`. -/
theorem not_isGatedReadingExtension_doubledApex (ξ : Ordinal.{u}) {b : Fin 5}
    (hb : cellGrade b = 2) (G : Fin (doubledP (blockStage (ξ + 1))).card)
    (S : Set (Fin (doubledP (blockStage (ξ + 1))).card)) :
    ¬ IsGatedReadingExtension (P (blockStage (ξ + 1))) Fin.castSuccEmb (P (blockStage (ξ + 1)))
      b (doubledP (blockStage (ξ + 1))).toScheme G S := by
  intro h
  obtain ⟨c, hc, hread⟩ := Seed.IsGatedReadingExtension.exists_readsOwnCellThroughCap_doubledApex
    (seedP (blockStage (ξ + 1))) rfl (isLegal_P _) (b := b) hb h
  have hc2 : cellGrade c = 2 := congrArg Prod.snd hc
  -- the cell of full scope other than the cap
  obtain ⟨j, hjb, hj2⟩ : ∃ j : Fin 5, j ≠ b ∧ cellGrade j = 2 := by
    fin_cases b
    all_goals first | (exfalso; revert hb; decide) | exact ⟨3, by decide, rfl⟩ |
      exact ⟨4, by decide, rfl⟩
  have hjs : Fin.last 1 ∈ cellScope j := by
    fin_cases j <;> first | decide | (exfalso; revert hj2; decide)
  have hjl : (P (blockStage (ξ + 1))).label j = ⊤ := by
    fin_cases j <;> first | rfl | (exfalso; revert hj2; decide)
  have heq := (hread j hjs).2.1 hjl
  change (P (blockStage (ξ + 1))).rowAt c j = (P (blockStage (ξ + 1))).rowAt c b at heq
  rw [rowAt_P hc2 hj2, rowAt_P hc2 hb] at heq
  rcases eq_three_or_four hc2 with rfl | rfl <;> rcases eq_three_or_four hb with rfl | rfl <;>
    rcases eq_three_or_four hj2 with rfl | rfl <;>
    first | exact hjb rfl | (simp at heq)

end GatedExtensionCounterexample

/-- **The requirement on the doubling design is false at every stage**: at the private type `P`
with the cap `3` (a graded cap for the self-donor, every label of `P` being `⊥` or `⊤`), the doubled
coface is a gated reading extension for no gate and readers
(`GatedExtensionCounterexample.not_isGatedReadingExtension_doubledApex`).  This refutes the
doubling design as a universal source of gated readings at the self-donor, not (R4). -/
theorem StageType.not_hasDoubledGatedReadings (ξ : Ordinal.{u}) :
    ¬ StageType.HasDoubledGatedReadings ξ := by
  intro h
  have hcap : IsGradedCap ξ (GatedExtensionCounterexample.P (blockStage (ξ + 1)))
      (GatedExtensionCounterexample.P (blockStage (ξ + 1))) 0 (3 : Fin 5) := by
    refine ⟨le_top, show 1 < 2 by omega, ?_, fun j o hj ↦ ?_⟩
    · change (0 : Ordinal.{u}) < blockStage ξ + ((2 : ℕ) : Ordinal.{u})
      exact lt_of_lt_of_le (by exact_mod_cast Nat.two_pos) le_add_self
    · exfalso
      fin_cases j <;>
        first | exact WithBot.bot_ne_coe hj | exact WithTop.top_ne_coe (WithBot.coe_injective hj)
  obtain ⟨G, S, hGS⟩ := h (GatedExtensionCounterexample.P (blockStage (ξ + 1)))
    (GatedExtensionCounterexample.isLegal_P _) _
    (restrictFace_of_mem _ _ (GatedExtensionCounterexample.mem_faces_castSuccEmb _)) 0
    (3 : Fin 5) hcap
  exact GatedExtensionCounterexample.not_isGatedReadingExtension_doubledApex ξ (b := 3) rfl G S
    hGS

end VaughtConjecture
