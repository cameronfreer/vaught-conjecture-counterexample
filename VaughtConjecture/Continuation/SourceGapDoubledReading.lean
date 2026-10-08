/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapDoubledCompletion
import VaughtConjecture.Continuation.SourceGapCoatomStep
import VaughtConjecture.Continuation.SourceGapSeparationObstruction

/-!
# The doubled coface reads each new top

Roadmap, Layer 3 ((R2) of the table of 3.4, the coatom step of
`VaughtConjecture.Continuation.SourceGapCoatomStep` when the donor is the context itself).

Let `T` be a legal stage type on two points with a face `p` on one point along `Fin.castSuccEmb`.
The seed of `T` with itself (`Seed.ofCoatoms`) has equal coatom types, and its doubled completion
(`Seed.doubledCompletion`) with the apex added (`StageType.addApex`) is **the doubled coface**
`Seed.doubledCoface`: a legal one-point coface of `T` whose face along `extendByLast
Fin.castSuccEmb` is `T` again.

**Reading** (compiled in this repository, `Seed.readsEachNewTop_doubledCoface`).  For every root
`h` missing a point, the doubled coface reads each new top along `h` at **every** cell of full
scope (`StageType.ReadsEachNewTop`, so also at its tops): a new top `x` (a cell other than the apex,
labelled `⊤`) lies over a cell `c` of `T`, and its copy along the first coatom is the cell of a
private top `s` of the face (labelled as `x`); every cell of full scope reads the two copies of
`c` alike, as `T` reads `c`.

* `StageType.exists_coatomStep_self`: **the top-reading coatom step holds when the donor is the
  context itself** along the first coatom: for every legal `t'` on two points, every root
  `h = g.trans Fin.castSuccEmb`, and the face `p` of `t'`, the coface `D'` exists with face `t'`
  along `extendByLast Fin.castSuccEmb` and reads each new top at its tops.  This is the instance of
  `StageType.HasTopReadingCoatomSteps` at the coatom `Fin.castSuccEmb` and the donor `d' = t'`; no
  hypothesis on the stage or on the context is used.
* `StageType.exists_readsEachNewTop_T`: at the input `SeparationObstruction.T α` it gives a reading
  coface built by the general construction (generalizing `ReadingInstance.E α`).
* `Seed.rowAt_doubled_copies` (**the negative test**): every cell of full scope of the doubled
  completion reads the two copies of a cell of `T` alike, so no cell of full scope reads `o'`
  below `o` as in `Scheme.IsMixedSite.exists_top_lt`; and the mixed labelling is not lawful below
  the full pair (`Seed.eq_of_isLawfulBelow_doubled`).

**The symmetry hypothesis.**  The donor must be the context: the two coatom types of the seed are
equal.  The coatom step for a donor other than the context, and at a coatom other than
`Fin.castSuccEmb` up to relabelling the points, is not proved here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ} {t : StageType.{u} α n} (ht : t.IsLegalBelowFullGrade)
  (hn : 0 < n)

/-- The old cells are read after adding the apex as before. -/
theorem rowAt_addApex_castSucc (a d : Fin t.card) :
    (t.addApex ht hn).rowAt a.castSucc d.castSucc = t.rowAt a d :=
  Scheme.rowAt_appendFullCell_castSucc (S := t.toScheme) (j := n) (r := apexRow ht)
    (h := ht.not_le) a d

/-- The old cells keep their graded indices after adding the apex. -/
theorem gradedIndex_addApex_castSucc (d : Fin t.card) :
    (t.addApex ht hn).toCellScheme.gradedIndex d.castSucc = t.toCellScheme.gradedIndex d :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc _ _ _

/-- The apex has graded index `(univ, n)`. -/
theorem gradedIndex_addApex_last :
    (t.addApex ht hn).toCellScheme.gradedIndex (Fin.last _) = ((univ : Finset (Fin n)), n) :=
  Scheme.appendFullCellScheme_gradedIndex_last _ _

end StageType

namespace Seed

variable {α : Ordinal.{u}} (I : Seed.{u} α 1) (hLR : I.left = I.right)

/-- **The negative test**: every cell of full scope of the doubled completion reads the two copies
of a cell `c` of `T` (along the two coatoms) alike, as the cell of `T` under it reads `c`. -/
theorem rowAt_doubled_copies {a : Fin (I.doubled hLR).card} {g : ℕ}
    (ha : (I.doubled hLR).toCellScheme.gradedIndex a = ((univ : Finset (Fin 3)), g))
    {c : Fin I.left.card} (hc : I.left.toCellScheme.grade c ≤ g) :
    (I.doubled hLR).rowAt a (I.old hLR (StageType.faceCell I.restrictFace_left c)) =
      (I.doubled hLR).rowAt a (I.old hLR (StageType.faceCell (I.restrictFace_right_left hLR) c))
    := by
  have hD := I.isDoubling_doubled hLR
  have hmem (f : Fin 2 ↪ Fin 3) {t : StageType.{u} α 2}
      (hf : StageType.restrictFace f I.amalgam = some t) (z : Fin t.card)
      (hz : t.toCellScheme.grade z ≤ g) :
      I.old hLR (StageType.faceCell hf z) ∈
        (I.doubled hLR).toCellScheme.below ((I.doubled hLR).toCellScheme.gradedIndex a) := by
    rw [CellScheme.mem_below, ha, gradedIndex_old]
    exact ⟨subset_univ _, (StageType.grade_faceCell hf z).le.trans hz⟩
  rw [hD.rowAt_eq _ _ (hmem _ _ c hc), hD.rowAt_eq _ _ (hmem _ _ c hc), doubledCell_old,
    doubledCell_old, doublingCell_faceCell_left, doublingCell_faceCell_right]

variable (hI : I.left.IsLegal)

/-- The doubled completion with the labels of `T`, as a stage type. -/
noncomputable abbrev doubledLabelled : StageType.{u} α (1 + 2) :=
  (I.doubledCompletion hLR hI).withLabel (I.doubledCompletion hLR hI).isLawful
    (I.atStage_doubledCompletion hLR hI)

/-- The **doubled coface**: the doubled completion, with the labels of `T`, and the apex. -/
noncomputable def doubledCoface : StageType.{u} α 3 :=
  (I.doubledLabelled hLR hI).addApex (I.doubledCompletion hLR hI).isLegalBelowFullGrade
    (Nat.succ_pos _)

theorem isLegal_doubledCoface : (I.doubledCoface hLR hI).IsLegal :=
  StageType.isLegal_addApex _ _

theorem restrictFace_left_doubledCoface :
    restrictFace Fin.castSuccEmb (I.doubledCoface hLR hI) = some I.left :=
  (StageType.restrictFace_addApex _ _ _ Coatom.univ_map_left_ne).trans
    (((I.doubledCompletion hLR hI).restrictFace_withLabel _ _
      (I.doubledCompletion hLR hI).label_embed _ Coatom.univ_map_left_ne).trans
      I.restrictFace_left)

theorem restrictFace_right_doubledCoface :
    restrictFace (extendByLast Fin.castSuccEmb) (I.doubledCoface hLR hI) = some I.left :=
  (StageType.restrictFace_addApex _ _ _ Coatom.univ_map_right_ne).trans
    (((I.doubledCompletion hLR hI).restrictFace_withLabel _ _
      (I.doubledCompletion hLR hI).label_embed _ Coatom.univ_map_right_ne).trans
      (I.restrictFace_right_left hLR))

theorem mem_cofaces_doubledCoface : I.doubledCoface hLR hI ∈ I.left.cofaces :=
  ⟨I.isLegal_doubledCoface hLR hI, I.restrictFace_left_doubledCoface hLR hI⟩

theorem rowAt_doubledCoface_castSucc (a d : Fin (I.doubled hLR).card) :
    (I.doubledCoface hLR hI).rowAt a.castSucc d.castSucc = (I.doubled hLR).rowAt a d :=
  StageType.rowAt_addApex_castSucc (t := I.doubledLabelled hLR hI) _ _ a d

theorem gradedIndex_doubledCoface_castSucc (d : Fin (I.doubled hLR).card) :
    (I.doubledCoface hLR hI).toCellScheme.gradedIndex d.castSucc =
      (I.doubled hLR).toCellScheme.gradedIndex d :=
  StageType.gradedIndex_addApex_castSucc (t := I.doubledLabelled hLR hI) _ _ d

theorem label_doubledCoface_castSucc (d : Fin (I.doubled hLR).card) :
    (I.doubledCoface hLR hI).label d.castSucc = I.left.label (I.doubledCell hLR d) :=
  StageType.addApex_label_castSucc (t := I.doubledLabelled hLR hI) _ _ d

theorem gradedIndex_doubledCoface_last :
    (I.doubledCoface hLR hI).toCellScheme.gradedIndex (Fin.last _) =
      ((univ : Finset (Fin 3)), 3) :=
  StageType.gradedIndex_addApex_last (t := I.doubledLabelled hLR hI) _ _

/-- **The doubled coface reads each new top** along every root missing a point, at every cell of
full scope. -/
theorem readsEachNewTop_doubledCoface {n : ℕ} (h : Fin n ↪ Fin 2) (hh : ∃ y, y ∉ Set.range h) :
    ReadsEachNewTop (I.restrictFace_left_doubledCoface hLR hI) h := by
  have hD := I.isDoubling_doubled hLR
  have h₁ := I.restrictFace_left_doubledCoface hLR hI
  intro x hx _ hxt
  -- the new top is not the apex: the root misses a point
  induction x using Fin.lastCases with
  | last =>
    obtain ⟨y, hy⟩ := hh
    have hsub := Scheme.mem_visibleCells.mp hx
    have hmem : y.castSucc ∈ (I.doubledCoface hLR hI).toCellScheme.scope (Fin.last _) := by
      rw [show (I.doubledCoface hLR hI).toCellScheme.scope (Fin.last _) = univ from
        congrArg Prod.fst (I.gradedIndex_doubledCoface_last hLR hI)]
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
    set c := I.doubledCell hLR x
    set v := I.old hLR (StageType.faceCell I.restrictFace_left c)
    have hv : Fin.last 2 ∉ (I.doubledCoface hLR hI).toCellScheme.scope v.castSucc := by
      have e1 : (I.doubledCoface hLR hI).toCellScheme.scope v.castSucc =
          I.amalgam.toCellScheme.scope (StageType.faceCell I.restrictFace_left c) :=
        congrArg Prod.fst ((I.gradedIndex_doubledCoface_castSucc hLR hI v).trans
          (I.gradedIndex_old hLR _))
      rw [e1]
      exact StageType.last_notMem_scope_faceCell I.restrictFace_left c
    obtain ⟨s, hs⟩ := StageType.exists_faceCell_eq_of_last_notMem h₁ hv
    have hvc : I.doubledCell hLR v = c := by
      rw [doubledCell_old, doublingCell_faceCell_left]
    have hgv : (I.doubled hLR).toCellScheme.grade v = I.left.toCellScheme.grade c := by
      rw [← hD.grade_eq, hvc]
    have hgx : (I.doubled hLR).toCellScheme.grade x = I.left.toCellScheme.grade c :=
      (hD.grade_eq x).symm
    have hgs : I.left.toCellScheme.grade s = I.left.toCellScheme.grade c := by
      rw [← StageType.grade_faceCell h₁, hs]
      exact (congrArg Prod.snd (I.gradedIndex_doubledCoface_castSucc hLR hI v)).trans hgv
    have hls : I.left.label s = I.left.label c := by
      rw [← StageType.label_faceCell h₁, hs, label_doubledCoface_castSucc, hvc]
    have hlx : (I.doubledCoface hLR hI).label x.castSucc = I.left.label c :=
      I.label_doubledCoface_castSucc hLR hI x
    refine ⟨s, s, by rw [hls, ← hlx, hxt], by rw [hls, ← hlx, hxt], le_rfl, ?_, fun a ha ↦ ?_⟩
    · rw [hgs]
      exact ((congrArg Prod.snd (I.gradedIndex_doubledCoface_castSucc hLR hI x)).trans hgx).le
    · -- a cell of full scope at the grade of `c` reads both copies as `T` reads `c`
      induction a using Fin.lastCases with
      | last =>
        have h2 := congrArg Prod.snd ((I.gradedIndex_doubledCoface_last hLR hI).symm.trans ha)
        have h3 := I.left.isWellFormed.isWellFormed.gradedIndex_mem s
        have h4 : #(I.left.toCellScheme.scope s) ≤ 2 := (card_le_univ _).trans (by simp)
        simp only at h2
        have h5 : I.left.toCellScheme.grade s ≤ 2 := h3.2.2.trans h4
        omega
      | cast a =>
        rw [hs, show (I.doubledCoface hLR hI).rowAt a.castSucc v.castSucc = _ from
          I.rowAt_doubledCoface_castSucc hLR hI a v,
          show (I.doubledCoface hLR hI).rowAt a.castSucc x.castSucc = _ from
          I.rowAt_doubledCoface_castSucc hLR hI a x]
        have ha' : (I.doubled hLR).toCellScheme.gradedIndex a =
            ((univ : Finset (Fin 3)), I.left.toCellScheme.grade c) := by
          rw [← hgs]
          exact (I.gradedIndex_doubledCoface_castSucc hLR hI a).symm.trans ha
        have hvb : v ∈ (I.doubled hLR).toCellScheme.below
            ((I.doubled hLR).toCellScheme.gradedIndex a) := by
          rw [CellScheme.mem_below, ha']
          exact ⟨subset_univ _, hgv.le⟩
        have hxb : x ∈ (I.doubled hLR).toCellScheme.below
            ((I.doubled hLR).toCellScheme.gradedIndex a) := by
          change (I.doubled hLR).toCellScheme.gradedIndex x ≤ _
          rw [ha']
          exact ⟨subset_univ _, hgx.le⟩
        rw [hD.rowAt_eq _ _ hvb, hD.rowAt_eq _ _ hxb, hvc]

end Seed

namespace StageType

variable {α : Ordinal.{u}}

/-- **The top-reading coatom step when the donor is the context** (at the coatom
`Fin.castSuccEmb` and the donor `d' = t'`): for every legal stage type `t'` on two points with
face `p` along `Fin.castSuccEmb`, and every root `h = g.trans Fin.castSuccEmb`, some legal
one-point coface of `t'` has face `t'` along `extendByLast Fin.castSuccEmb` and reads each new top
along `h` at its tops (indeed at every cell of full scope). -/
theorem exists_coatomStep_self {t' : StageType.{u} α 2} (ht' : t'.IsLegal)
    {p : StageType.{u} α 1} (hp : restrictFace Fin.castSuccEmb t' = some p) {n : ℕ}
    (g : Fin n ↪ Fin 1) {h : Fin n ↪ Fin 2} (hg : g.trans Fin.castSuccEmb = h) :
    ∃ (D' : StageType.{u} α 3) (hD' : D' ∈ t'.cofaces),
      restrictFace (extendByLast Fin.castSuccEmb) D' = some t' ∧ ReadsEachNewTop hD'.2 h ∧
        ReadsEachNewTopAtTops hD'.2 h := by
  set I := Seed.ofCoatoms ht' ht' hp hp
  have hLR : I.left = I.right := rfl
  have hmiss : ∃ y, y ∉ Set.range h := ⟨Fin.last 1, fun ⟨i, hi⟩ ↦ by
    rw [← hg] at hi
    exact (Fin.castSucc_lt_last (g i)).ne hi⟩
  have hr := I.readsEachNewTop_doubledCoface hLR ht' h hmiss
  exact ⟨I.doubledCoface hLR ht', I.mem_cofaces_doubledCoface hLR ht',
    I.restrictFace_right_doubledCoface hLR ht', hr, hr.atTops⟩

/-- **A reading coface at `SeparationObstruction.T α`** from the general construction: the doubled
coface of the input with itself reads each new top along the root `{0}`. -/
theorem exists_readsEachNewTop_T (α : Ordinal.{u}) :
    ∃ (D' : StageType.{u} α 3) (hD' : D' ∈ (SeparationObstruction.T α).cofaces),
      restrictFace (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) D' =
        some (SeparationObstruction.T α) ∧
      ReadsEachNewTop hD'.2 (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∧
      ReadsEachNewTopAtTops hD'.2 (Fin.castSuccEmb : Fin 1 ↪ Fin 2) := by
  have hf : univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∈
      (SeparationObstruction.T α).toCellScheme.faces := by
    -- the faces of the input are the interval plan
    change _ ∈ Geometry.intervalPlan univ
    decide
  exact exists_coatomStep_self (SeparationObstruction.isLegal_T α)
    (restrictFace_of_mem _ _ hf) (Function.Embedding.refl _) rfl

end StageType

end VaughtConjecture
