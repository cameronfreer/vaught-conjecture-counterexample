/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Tactic.FinCases
import VaughtConjecture.Extension.MultiLayerStep
import VaughtConjecture.Extension.OrderedLayerTop
import VaughtConjecture.Extension.Gluing
import VaughtConjecture.Extension.Tower

/-!
# The canonical multi-layer scheme: copies of the full cells of the coatoms

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`: a
finite family of new cells defined for every seed on five points, what holds for every seed, and a
sufficient hypothesis for its step that does not); semantic contract, items 2–4.

Let `I` be a seed on five points (`m = 3`), with coatoms `C = {0, 1, 2, 3}`, `D = {0, 1, 2, 4}`
and common face `C ∩ D = {0, 1, 2}`.

**The family** (`OrderedLayer.canonicalMultiScheme I R`).  At each grade `k + 1 = 1, …, 4` there
are two new cells of full scope, the *copies* `multiNewCell k 0` and `multiNewCell k 1` of the
*originals* `copyOrig I k 0` and `copyOrig I k 1`, cells of the amalgam at the full coatom graded
faces `(C, k + 1)` and `(D, k + 1)` (`OrderedLayer.copyOrig`, chosen by completeness of the
amalgam; the proofs use only the graded index of an original, `OrderedLayer.gradedIndex_copyOrig`,
so they hold for any choice of originals).  So the multiplicities are `2, 2, 2, 2`
(`OrderedLayer.canonicalMult`).  Each cell has a *base* in the amalgam (`OrderedLayer.copyBase`):
an old cell is its own base, a copy has its original as base.  The rows are given by *copy rows*
`R k i`, labellings of the amalgam: the row of the copy `(k, i)` reads every cell through its
base, `z ↦ R k i (copyBase z)` (`OrderedLayer.canonicalRows`).  In particular a copy reads every
copy of grade at most `k + 1` exactly as it reads that copy's original.  *Canonical* refers to the
cells and the shape of the rows, which the seed fixes up to the choice of originals; the values of
the rows, the copy rows `R`, are a parameter.

**What holds for every seed and all copy rows** (compiled):

* well-formedness and completeness (two cells at each `(univ, k)`), from
  `VaughtConjecture.Extension.MultiLayerStep`;
* **forcedness** (`OrderedLayer.eq_copyOrig_of_isLawfulBelow`): every labelling lawful below
  `(univ, j)` carries at each copy of grade at most `j` the label of its original.  Each copy reads
  itself and the other copy of its grade as it reads their originals, and availability puts each
  original below one of the two copies; in a linear order these force both values
  (`OrderedLayer.eq_of_forced_pair`);
* **one direction of the classification**
  (`OrderedLayer.isLawfulBelow_coatom_of_isLawfulBelow_univ`,
  `OrderedLayer.eq_copyBase_of_isLawfulBelow`): a labelling lawful below `(univ, j)` is, on the old
  cells, a labelling of the amalgam lawful below `(C, j)` and below `(D, j)` (so a pair of coatom
  labellings agreeing on the common face), and it is that labelling read through the bases;
* **the lifts from the common face** (`Seed.HasCommonFaceLifts`, proved for every seed:
  `Seed.hasCommonFaceLifts`): the capped lifts of the amalgam from `(C ∩ D, min k 3)` into `(C, k)`
  and into `(D, k)`, `1 ≤ k ≤ 4`, from the bountifulness of the amalgam (a field of the seed,
  given for the amalgam of two legal coatom types by `Coatom.isBountiful_amalgamType`).

**The product clause** (`Seed.CanonicalProduct I R j`, a named hypothesis on the seed, the copy
rows and the grade): the converse of the classification, that every labelling of the amalgam
lawful below `(C, j)` and `(D, j)`, read through the bases, is lawful below `(univ, j)`.  It is
exactly the statement that the lawful labellings below `(univ, j)` are the pairs of coatom
labellings agreeing on the common face (`OrderedLayer.isLawfulBelow_canonical_iff`).  It is not a
field of the multi-layer step (`Seed.MultiLayerStep`) but a sufficient hypothesis for it: the only
hypothesis of `Seed.canonicalMultiStep_of_product` beyond copy rows coded and lawful below both
coatoms (the form below the top grade adds bottom apexes and the top row).  It is not necessary:
for `seedHG` the step holds at the grade `4` although the clause fails there (below).  Its content
is locality at the copies, one row reading the other coatom's parameters for every pair at once.

**From the product clause** (compiled):

* the capped lift from `(C, k)` (resp. `(D, k)`) into `(univ, k)` is the prescription glued with the
  lift of the ambient from the common face into the other coatom
  (`OrderedLayer.cappedLift_of_canonicalProduct`):
  the lift of the other coatom's type from `(C ∩ D, min k 3)` is the lift of the family;
* the step (`Seed.canonicalMultiStep_of_product`): the product clause at the grades `1, …, 4`, with
  copy rows that are coded and lawful below both coatoms, gives the multi-layer step, hence a
  completion below the full grade (`Seed.nonempty_completionBelowFullGrade_of_canonicalProduct`);
  its hypothesis at the grade `4` fails at all six compiled seeds (below), so this form applies at
  none of them;
* for a seed with bottom apexes and the top row at the grade `4`, the product clause at the grades
  `1, 2, 3`, with copy rows at those grades coded and lawful below both coatoms, suffices
  (`Seed.canonicalMultiStep_of_productBelowTop`), the grade `4` coming from the grade `3`
  (`OrderedLayer.cappedLift_four_of_oldCells`) and not from the product clause.  The top row
  restricts the lawful labellings below `(univ, 4)`: one that is not `⊥` at the first copy of
  grade `4` is `⊥` below the grade `4` (`OrderedLayer.eq_bot_of_grade_four_canonical`), so the
  labellings of the decoding refutation (`⊤` at a copy of grade `4`, `1` or `2` at a cell of grade
  `1`) are not lawful there.

**Status at the compiled seeds** (compiled).  For every copy rows, the product clause fails at the
grades `2`, `3`, `4` for `seed4`, `seed5`, `seedL`, `seedLM`, `seedLL` (two parameters of grade
`1`, one on each coatom, cross below a copy labelled `⊤`), and at the grade `4` for all six seeds,
`seedHG` included (a copy labelled `⊤` at the grade `4` cannot read a parameter of grade `1` at
both `1` and `2`): `VaughtConjecture.Extension.CanonicalMultiSchemeCounterexample`.  For `seedHG`
it holds at the grades `1`, `2`, `3` with the rows of `CrossedCouplingCounterexample.schemeHG`, so
the canonical multi-layer scheme completes every seed of `TH` and `TG`
(`Seed.canonicalMultiStep_of_TH_TG`, `VaughtConjecture.Extension.CanonicalMultiSchemeExamples`),
the grade `4` coming from the top row and not from the product clause.  So the product clause is
not uniform in the seed, and what is refuted is the family *as a fibre product* at those seeds and
grades, not the family's step (which holds for `seedHG` at the grade `4`) and not the completion.
Copy rows restricting the pairs: the oriented rows of an ordered-layer step whose layer rows are
oriented (both copies of a grade read every old cell as the new cell of the layer scheme does)
give the step exactly when that ordered-layer step holds, an exact reformulation of it
(`VaughtConjecture.Extension.CanonicalMultiSchemeOriented`).  So the family has a step at `seed4`,
`seed5`, `seedL`, `seedLM`, `seedLL`, which their ordered-layer steps already complete, and the
oriented rows give none at `seedHG`.  A seed *has a step of the canonical multi-layer scheme*
(`Seed.HasCanonicalMultiStep`) when some copy rows give the step; it then has a completion below
the full grade (`Seed.HasCanonicalMultiStep.nonempty_completionBelowFullGrade`).  Whether every
seed has one is open; for instance rows under which each copy of `(B, k)` reads the parameters of
its own coatom above those of the other (opposite orientations for the two copies of a grade).

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

The completion has the shape of [Kni26, Definition 4.3.14] (the old cells kept, the new cells of
full scope, several at one graded face); its rows are not those of that definition, and neither
printed proof of [Kni26, Lemma 4.3.16] or [Kni26, Lemma 4.3.20] is used.
-/

universe u

namespace VaughtConjecture.OrderedLayer

open Finset Label CellScheme

/-! ### The originals -/

/-- The coatom of the `i`-th copy at each grade: `C` for `i = 0`, `D` for `i = 1`. -/
def copyCoatom (i : Fin 2) : Finset (Fin 5) := if i = 0 then coatomC else coatomD

/-- The coatom of a copy is `C` or `D`. -/
theorem copyCoatom_eq (i : Fin 2) : copyCoatom i = coatomC ∨ copyCoatom i = coatomD := by
  unfold copyCoatom; split_ifs
  exacts [.inl rfl, .inr rfl]

/-- The coatom of a copy is not the ground set. -/
theorem copyCoatom_ne_univ (i : Fin 2) : copyCoatom i ≠ univ := by
  rcases copyCoatom_eq i with h | h <;> rw [h] <;> decide

/-- The coatom of a copy has four points. -/
theorem card_copyCoatom (i : Fin 2) : #(copyCoatom i) = 4 := by
  rcases copyCoatom_eq i with h | h <;> rw [h] <;> decide

variable {α : Ordinal.{u}} (I : Seed.{u} α 3)

/-- The full coatom graded faces `(C, k + 1)` and `(D, k + 1)` are graded faces of the amalgam. -/
theorem copyCoatom_mem_gradedFaces (k : Fin 4) (i : Fin 2) :
    (copyCoatom i, (k : ℕ) + 1) ∈ I.amalgam.toCellScheme.gradedFaces := by
  refine ⟨?_, Nat.succ_pos _, ?_⟩
  · rcases copyCoatom_eq i with h | h <;> rw [h]
    exacts [coatomC_mem_faces I, coatomD_mem_faces I]
  · rw [card_copyCoatom]; omega

/-- **The original** of the `i`-th copy of grade `k + 1`: a cell of the amalgam at the full coatom
graded face `(copyCoatom i, k + 1)`, chosen by completeness of the amalgam. -/
noncomputable def copyOrig (k : Fin 4) (i : Fin 2) : Fin I.amalgam.card :=
  (I.exists_gradedIndex_eq _ (copyCoatom_mem_gradedFaces I k i) (copyCoatom_ne_univ i)).choose

/-- The original of the `i`-th copy of grade `k + 1` has graded index `(copyCoatom i, k + 1)`. -/
theorem gradedIndex_copyOrig (k : Fin 4) (i : Fin 2) :
    I.amalgam.toCellScheme.gradedIndex (copyOrig I k i) = (copyCoatom i, (k : ℕ) + 1) :=
  (I.exists_gradedIndex_eq _ (copyCoatom_mem_gradedFaces I k i) (copyCoatom_ne_univ i)).choose_spec

/-- The original of a copy of grade `k + 1` has grade `k + 1`. -/
theorem grade_copyOrig (k : Fin 4) (i : Fin 2) :
    I.amalgam.toCellScheme.grade (copyOrig I k i) = (k : ℕ) + 1 :=
  congrArg Prod.snd (gradedIndex_copyOrig I k i)

/-! ### The canonical multi-layer scheme -/

/-- The canonical multiplicities: two copies at each graded face of full scope. -/
abbrev canonicalMult : Fin 4 → ℕ := fun _ ↦ 2

/-- **The base** of a cell of the canonical multi-layer scheme: an old cell is its own base, the
`i`-th copy of grade `k + 1` has base its original `copyOrig I k i`. -/
noncomputable def copyBase (z : Fin (multiCard I canonicalMult)) : Fin I.amalgam.card :=
  Fin.addCases (Fin.addCases (Fin.addCases (Fin.addCases id (copyOrig I 0)) (copyOrig I 1))
    (copyOrig I 2)) (copyOrig I 3) z

/-- An old cell is its own base. -/
@[simp] theorem copyBase_multiOldCell (d : Fin I.amalgam.card) :
    copyBase I (multiOldCell I canonicalMult d) = d := by
  simp [copyBase, multiOldCell]

/-- A copy has its original as base. -/
@[simp] theorem copyBase_multiNewCell (k : Fin 4) (i : Fin 2) :
    copyBase I (multiNewCell I canonicalMult k i) = copyOrig I k i := by
  fin_cases k <;> simp [copyBase, multiNewCell]

/-- **Copy rows**: for each grade `k + 1` and each `i`, a labelling of the amalgam, read by the
`i`-th copy through the bases. -/
abbrev CopyRows : Type (u + 1) := Fin 4 → Fin 2 → Fin I.amalgam.card → Label.{u}

variable {I} (R : CopyRows I)

variable (I) in
/-- **The canonical rows** of copy rows `R`: the `i`-th copy of grade `k + 1` reads every cell
through its base, by `R k i`. -/
noncomputable def canonicalRows (R : CopyRows I) : MultiRows I canonicalMult :=
  fun k i z ↦ if h : i < 2 then R k ⟨i, h⟩ (copyBase I z) else ⊥

/-- The canonical rows read through the bases. -/
@[simp] theorem canonicalRows_apply (k : Fin 4) (i : Fin 2) (z : Fin (multiCard I canonicalMult)) :
    canonicalRows I R k i z = R k i (copyBase I z) := by
  simp [canonicalRows, i.isLt]

variable (I) in
/-- **The canonical multi-layer scheme** of a seed on five points with copy rows `R`: the amalgam
followed by the two copies of `(C, k)` and `(D, k)` at each `(univ, k)`, `k = 1, …, 4`, each
reading through the bases. -/
noncomputable abbrev canonicalMultiScheme (R : CopyRows I) : Scheme.{u} 5 :=
  multiLayerScheme I canonicalMult (canonicalRows I R)

/-- **The row of a copy** reads every cell below it through its base. -/
theorem row_canonical (k : Fin 4) (i : Fin 2)
    (t : (canonicalMultiScheme I R).toCellScheme.below
      ((canonicalMultiScheme I R).toCellScheme.gradedIndex (multiNewCell I canonicalMult k i))) :
    (canonicalMultiScheme I R).rows.row (multiNewCell I canonicalMult k i) t =
      R k i (copyBase I t.1) :=
  (row_multiNewCell (r := canonicalRows I R) k i t).trans (canonicalRows_apply R k i t.1)

/-- A cell and its base have one grade. -/
theorem grade_copyBase (z : Fin (canonicalMultiScheme I R).card) :
    I.amalgam.toCellScheme.grade (copyBase I z) =
      (canonicalMultiScheme I R).toCellScheme.grade z := by
  rcases multiCell_cases (r := canonicalRows I R) z with ⟨d, rfl⟩ | ⟨k, i, rfl⟩
  · rw [copyBase_multiOldCell, grade_multiOldCell]
  · rw [copyBase_multiNewCell, grade_copyOrig, grade_multiNewCell]

/-- The base of a cell below `(univ, j)`, as an old cell, is below `(univ, j)`. -/
theorem multiOldCell_copyBase_mem_below {j : ℕ} {z : Fin (canonicalMultiScheme I R).card}
    (hz : z ∈ (canonicalMultiScheme I R).toCellScheme.below ((univ : Finset (Fin 5)), j)) :
    multiOldCell I canonicalMult (copyBase I z) ∈
      (canonicalMultiScheme I R).toCellScheme.below ((univ : Finset (Fin 5)), j) :=
  multiOldCell_mem_below ⟨subset_univ _, (grade_copyBase R z).trans_le hz.2⟩

/-! ### Forcedness -/

/-- **Forcedness**: below `(univ, j)`, a lawful labelling carries at each copy of grade at most `j`
the label of its original.  Each copy reads itself and the other copy of its grade as their
originals, and each original is at most one of the two copies (availability). -/
theorem eq_copyOrig_of_isLawfulBelow {j : ℕ} {w : Fin (canonicalMultiScheme I R).card → Label.{u}}
    (hw : (canonicalMultiScheme I R).rows.IsLawfulBelow ((univ : Finset (Fin 5)), j)
      fun z ↦ w z)
    {k : Fin 4} (hk : (k : ℕ) + 1 ≤ j) (i : Fin 2) :
    w (multiNewCell I canonicalMult k i) = w (multiOldCell I canonicalMult (copyOrig I k i)) := by
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  -- The copies `multiNewCell k i` and the originals `multiOldCell (copyOrig k i)`.
  have gκ (i : Fin 2) : (canonicalMultiScheme I R).toCellScheme.grade
      (multiNewCell I canonicalMult k i) = (k : ℕ) + 1 :=
    grade_multiNewCell (r := canonicalRows I R) k i
  have go (i : Fin 2) : (canonicalMultiScheme I R).toCellScheme.grade
      (multiOldCell I canonicalMult (copyOrig I k i)) = (k : ℕ) + 1 := by
    rw [grade_multiOldCell, grade_copyOrig]
  have bel (i : Fin 2) (z : Fin (canonicalMultiScheme I R).card)
      (hz : (canonicalMultiScheme I R).toCellScheme.grade z = (k : ℕ) + 1) :
      z ∈ (canonicalMultiScheme I R).toCellScheme.below
        ((canonicalMultiScheme I R).toCellScheme.gradedIndex
          (multiNewCell I canonicalMult k i)) := by
    rw [gradedIndex_multiNewCell]; exact ⟨subset_univ _, hz.le⟩
  have memU (i : Fin 2) : multiNewCell I canonicalMult k i ∈
      (canonicalMultiScheme I R).toCellScheme.below ((univ : Finset (Fin 5)), j) :=
    multiNewCell_mem_below (r := canonicalRows I R) i hk
  -- Each copy reads each original as the corresponding copy.
  have read (i i' : Fin 2) : min (w (multiOldCell I canonicalMult (copyOrig I k i')))
      (w (multiNewCell I canonicalMult k i)) =
        min (w (multiNewCell I canonicalMult k i')) (w (multiNewCell I canonicalMult k i)) := by
    have L := hl _ (memU i)
    have hrow : (canonicalMultiScheme I R).rows.row (multiNewCell I canonicalMult k i)
          ⟨_, bel i _ (go i')⟩ =
        (canonicalMultiScheme I R).rows.row (multiNewCell I canonicalMult k i)
          ⟨_, bel i _ (gκ i')⟩ := by
      rw [row_canonical, row_canonical, copyBase_multiOldCell, copyBase_multiNewCell]
    have hg := (go i').trans (gκ i').symm
    exact le_antisymm (L.le_of_le hrow.le hg.ge) (L.le_of_le hrow.ge hg.le)
  have self (i : Fin 2) : w (multiNewCell I canonicalMult k i) ≤
      w (multiOldCell I canonicalMult (copyOrig I k i)) := by
    have := read i i
    rw [min_self] at this
    exact this ▸ min_le_left _ _
  -- Availability: each original is at most one of the two copies.
  have avail (i' : Fin 2) : w (multiOldCell I canonicalMult (copyOrig I k i')) ≤
      w (multiNewCell I canonicalMult k 0) ∨ w (multiOldCell I canonicalMult (copyOrig I k i')) ≤
        w (multiNewCell I canonicalMult k 1) := by
    obtain ⟨u, hu, hle⟩ := ha _ _ (memU 0)
      (by rw [scope_multiNewCell]; exact subset_univ _) ((go i').trans (gκ 0).symm)
    obtain ⟨k', i'', hk', rfl⟩ := exists_eq_multiNewCell (hu.trans (gradedIndex_multiNewCell k 0))
    obtain rfl : k' = k := Fin.ext (by omega)
    match i'' with
    | ⟨0, _⟩ => exact .inl hle
    | ⟨1, _⟩ => exact .inr hle
  obtain ⟨h0, h1⟩ := eq_of_forced_pair (self 0) (self 1) (read 0 1) (read 1 0) (avail 0) (avail 1)
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1

/-- **Below `(univ, j)`, a lawful labelling is read through the bases**: at every cell below
`(univ, j)` it carries the label of the base. -/
theorem eq_copyBase_of_isLawfulBelow {j : ℕ} {w : Fin (canonicalMultiScheme I R).card → Label.{u}}
    (hw : (canonicalMultiScheme I R).rows.IsLawfulBelow ((univ : Finset (Fin 5)), j)
      fun z ↦ w z)
    {z : Fin (canonicalMultiScheme I R).card}
    (hz : z ∈ (canonicalMultiScheme I R).toCellScheme.below ((univ : Finset (Fin 5)), j)) :
    w z = w (multiOldCell I canonicalMult (copyBase I z)) := by
  rcases multiCell_cases (r := canonicalRows I R) z with ⟨d, rfl⟩ | ⟨k, i, rfl⟩
  · rw [copyBase_multiOldCell]
  · rw [copyBase_multiNewCell]
    exact eq_copyOrig_of_isLawfulBelow R hw ((grade_multiNewCell k i).symm.trans_le hz.2) i

/-- **One direction of the classification**: below `(univ, j)`, a lawful labelling is, on the old
cells, lawful below each coatom at the grade `j`. -/
theorem isLawfulBelow_coatom_of_isLawfulBelow_univ {j : ℕ}
    {w : Fin (canonicalMultiScheme I R).card → Label.{u}}
    (hw : (canonicalMultiScheme I R).rows.IsLawfulBelow ((univ : Finset (Fin 5)), j)
      fun z ↦ w z)
    {B : Finset (Fin 5)} (hB : B ≠ univ) :
    I.amalgam.rows.IsLawfulBelow (B, j) fun d ↦ w (multiOldCell I canonicalMult d) :=
  (isLawfulBelow_multiOldCell_iff hB).mp (hw.mono (X := (B, j)) ⟨subset_univ _, le_rfl⟩)

end VaughtConjecture.OrderedLayer

namespace VaughtConjecture.Seed

open Finset Label CellScheme OrderedLayer

variable {α : Ordinal.{u}} (I : Seed.{u} α 3) (R : CopyRows I)

/-! ### The product clause and the common face -/

/-- **The product clause** at the grade `j`: every labelling of the amalgam lawful below `(C, j)`
and below `(D, j)`, read through the bases, is lawful below `(univ, j)` in the canonical
multi-layer scheme of the copy rows `R`.  With forcedness it says that the lawful labellings below
`(univ, j)` are exactly the pairs of coatom labellings agreeing on the common face
(`OrderedLayer.isLawfulBelow_canonical_iff`). -/
def CanonicalProduct (j : ℕ) : Prop :=
  ∀ v : Fin I.amalgam.card → Label.{u},
    I.amalgam.rows.IsLawfulBelow (coatomC, j) (fun d ↦ v d) →
    I.amalgam.rows.IsLawfulBelow (coatomD, j) (fun d ↦ v d) →
    (canonicalMultiScheme I R).rows.IsLawfulBelow ((univ : Finset (Fin 5)), j)
      fun z ↦ v (copyBase I z)

/-- The common face `C ∩ D = {0, 1, 2}` is a face of the amalgam. -/
theorem inter_coatoms_mem_faces : coatomC ∩ coatomD ∈ I.amalgam.toCellScheme.faces := by
  have h : coatomC ∩ coatomD =
      (univ.erase (Fin.last (3 + 1))).erase (Fin.castSucc (Fin.last 3)) := by
    decide
  rw [h]
  exact I.commonFace_mem_faces

/-- **The lifts from the common face into each coatom**, at every grade `1 ≤ k ≤ 4`: the capped
lifts of the amalgam from `(C ∩ D, min k 3)` into `(C, k)` and into `(D, k)`.  These are the
capped lifts of each coatom type from its face on `{0, 1, 2}` (the cells below `(C ∩ D, 4)` are
those below `(C ∩ D, 3)`). -/
def HasCommonFaceLifts : Prop :=
  ∀ k, 1 ≤ k → k ≤ 4 →
    I.amalgam.rows.CappedLift (X := (coatomC ∩ coatomD, min k 3)) (Y := (coatomC, k))
        ⟨inter_subset_left, min_le_left _ _⟩ ∧
      I.amalgam.rows.CappedLift (X := (coatomC ∩ coatomD, min k 3)) (Y := (coatomD, k))
        ⟨inter_subset_right, min_le_left _ _⟩

/-- **Every seed on five points has the lifts from the common face**: they are capped lifts
between graded faces of the amalgam, whose rows are bountiful. -/
theorem hasCommonFaceLifts : I.HasCommonFaceLifts := by
  intro k hk1 hk4
  have hF : ((coatomC ∩ coatomD : Finset (Fin 5)), min k 3) ∈ I.amalgam.toCellScheme.gradedFaces :=
    ⟨I.inter_coatoms_mem_faces, lt_min hk1 (by omega),
      (min_le_right _ _).trans (by decide : 3 ≤ #(coatomC ∩ coatomD))⟩
  have hC : ((coatomC : Finset (Fin 5)), k) ∈ I.amalgam.toCellScheme.gradedFaces :=
    ⟨coatomC_mem_faces I, hk1, hk4.trans (show (4 : ℕ) ≤ #coatomC by decide)⟩
  have hD : ((coatomD : Finset (Fin 5)), k) ∈ I.amalgam.toCellScheme.gradedFaces :=
    ⟨coatomD_mem_faces I, hk1, hk4.trans (show (4 : ℕ) ≤ #coatomD by decide)⟩
  exact ⟨I.isBountiful hF hC _, I.isBountiful hF hD _⟩

end VaughtConjecture.Seed

namespace VaughtConjecture.OrderedLayer

open Finset Label CellScheme

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} (R : CopyRows I)

/-! ### The classification under the product clause -/

/-- **The classification**: under the product clause at the grade `j`, a labelling is lawful below
`(univ, j)` exactly when it is lawful below both coatoms at the grade `j` on the old cells and is
read through the bases below `(univ, j)`. -/
theorem isLawfulBelow_canonical_iff {j : ℕ} (hP : I.CanonicalProduct R j)
    {w : Fin (canonicalMultiScheme I R).card → Label.{u}} :
    (canonicalMultiScheme I R).rows.IsLawfulBelow ((univ : Finset (Fin 5)), j) (fun z ↦ w z) ↔
      I.amalgam.rows.IsLawfulBelow (coatomC, j) (fun d ↦ w (multiOldCell I canonicalMult d)) ∧
      I.amalgam.rows.IsLawfulBelow (coatomD, j) (fun d ↦ w (multiOldCell I canonicalMult d)) ∧
      ∀ z ∈ (canonicalMultiScheme I R).toCellScheme.below ((univ : Finset (Fin 5)), j),
        w z = w (multiOldCell I canonicalMult (copyBase I z)) := by
  refine ⟨fun hw ↦ ⟨isLawfulBelow_coatom_of_isLawfulBelow_univ R hw (by decide),
    isLawfulBelow_coatom_of_isLawfulBelow_univ R hw (by decide),
    fun z hz ↦ eq_copyBase_of_isLawfulBelow R hw hz⟩, fun ⟨hC, hD, he⟩ ↦ ?_⟩
  exact (Rows.isLawfulBelow_congr he).mpr
    (hP (fun d ↦ w (multiOldCell I canonicalMult d)) hC hD)

/-- A cell below both coatoms at the grade `k` lies below the common face at the grade
`min k 3`. -/
theorem mem_below_inter_coatoms {k : ℕ} {d : Fin I.amalgam.card}
    (hC : d ∈ I.amalgam.toCellScheme.below (coatomC, k))
    (hD : d ∈ I.amalgam.toCellScheme.below (coatomD, k)) :
    d ∈ I.amalgam.toCellScheme.below (coatomC ∩ coatomD, min k 3) := by
  have hsub := subset_inter hC.1 hD.1
  exact ⟨hsub, le_min hC.2 ((I.amalgam.isWellFormed.isWellFormed.grade_le_card d).trans
    ((card_le_card hsub).trans (by decide : #(coatomC ∩ coatomD) ≤ 3)))⟩

/-- **The capped lift from a coatom into the full scope, from the product clause.**  Let `B` be one
coatom and `B'` the other.  Under the product clause at the grade `k` and the lift of the amalgam
from the common face into `B'`, the canonical multi-layer scheme lifts capped from `(B, k)` to
`(univ, k)`: glue the prescription on `B` with the lift into `B'` of the ambient's labelling of
`B'` (prescribed on the common face by the prescription), and read the result through the bases.
The ambient is read through the bases (forcedness), so the cap agreement holds at the copies. -/
theorem cappedLift_of_canonicalProduct {B B' : Finset (Fin 5)}
    (hBB' : (B = coatomC ∧ B' = coatomD) ∨ (B = coatomD ∧ B' = coatomC)) {k : ℕ}
    (hP : I.CanonicalProduct R k)
    (hsub : coatomC ∩ coatomD ⊆ B')
    (hF : I.amalgam.rows.CappedLift (X := (coatomC ∩ coatomD, min k 3)) (Y := (B', k))
      ⟨hsub, min_le_left _ _⟩) :
    (canonicalMultiScheme I R).rows.CappedLift (X := (B, k)) (Y := ((univ : Finset (Fin 5)), k))
      ⟨subset_univ _, le_rfl⟩ := by
  classical
  have hB : B ≠ univ := by rcases hBB' with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hB' : B' ≠ univ := by rcases hBB' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  -- A cell below both coatoms at the grade `k` is below the common face.
  have hface (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (B, k))
      (hd' : d ∈ I.amalgam.toCellScheme.below (B', k)) :
      d ∈ I.amalgam.toCellScheme.below (coatomC ∩ coatomD, min k 3) := by
    rcases hBB' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [mem_below_inter_coatoms hd hd', mem_below_inter_coatoms hd' hd]
  -- An old cell below `(univ, k)` lies below one of the two coatoms.
  have hcov (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ k) :
      d ∈ I.amalgam.toCellScheme.below (B, k) ∨ d ∈ I.amalgam.toCellScheme.below (B', k) := by
    rcases I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem d)
      (I.scope_ne_univ d) with h | h <;> rcases hBB' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [.inl ⟨h, hd⟩, .inr ⟨h, hd⟩, .inr ⟨h, hd⟩, .inl ⟨h, hd⟩]
  have hFB : ((coatomC ∩ coatomD : Finset (Fin 5)), min k 3) ≤ (B, k) :=
    ⟨by rcases hBB' with ⟨rfl, -⟩ | ⟨rfl, -⟩
        exacts [inter_subset_left, inter_subset_right], min_le_left _ _⟩
  refine (Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  -- The prescription and the ambient as labellings of all cells.
  set P := Rows.extendBot (D := (canonicalMultiScheme I R).toCellScheme) (B, k) p with hPdef
  set Q := Rows.extendBot (D := (canonicalMultiScheme I R).toCellScheme)
    ((univ : Finset (Fin 5)), k) q with hQdef
  have hQ : (canonicalMultiScheme I R).rows.IsLawfulBelow ((univ : Finset (Fin 5)), k)
      fun z ↦ Q z := Rows.isLawfulBelow_extendBot.mpr hq
  have hPA : I.amalgam.rows.IsLawfulBelow (B, k) fun d ↦ P (multiOldCell I canonicalMult d) :=
    (isLawfulBelow_multiOldCell_iff hB).mp (Rows.isLawfulBelow_extendBot.mpr hp)
  have hQA : I.amalgam.rows.IsLawfulBelow (B', k) fun d ↦ Q (multiOldCell I canonicalMult d) :=
    (isLawfulBelow_multiOldCell_iff hB').mp (hQ.mono (X := (B', k)) ⟨subset_univ _, le_rfl⟩)
  -- The prescription agrees with the ambient capped at `c` at the old cells below `B`.
  have hagree (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (B, k)) :
      min (Q (multiOldCell I canonicalMult d)) c = min (P (multiOldCell I canonicalMult d)) c := by
    have hm : multiOldCell I canonicalMult d ∈
        (canonicalMultiScheme I R).toCellScheme.below (B, k) :=
      multiOldCell_mem_below hd
    have hmU : multiOldCell I canonicalMult d ∈
        (canonicalMultiScheme I R).toCellScheme.below ((univ : Finset (Fin 5)), k) :=
      multiOldCell_mem_below ⟨subset_univ _, hd.2⟩
    rw [hQdef, hPdef, Rows.extendBot_of_mem q hmU, Rows.extendBot_of_mem p hm]
    exact hpq ⟨_, hm⟩
  -- The lift of the ambient on `B'` from the common face, prescribed there by `P`.
  obtain ⟨r, hr, hrc, hrp⟩ := (Rows.cappedLift_iff_forall_exists _).mp hF c hc
    (fun d ↦ P (multiOldCell I canonicalMult d.1)) (fun d ↦ Q (multiOldCell I canonicalMult d.1))
    (hPA.mono hFB) hQA fun d ↦ hagree d.1 (I.amalgam.toCellScheme.below_mono hFB d.2)
  -- The glued labelling of the amalgam.
  set V : Fin I.amalgam.card → Label.{u} := fun d ↦
    if hd : d ∈ I.amalgam.toCellScheme.below (B, k) then P (multiOldCell I canonicalMult d)
    else Rows.extendBot (B', k) r d with hVdef
  have hVB (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (B, k)) :
      V d = P (multiOldCell I canonicalMult d) := dite_eq_left hd
  have hVB' (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (B', k)) :
      V d = r ⟨d, hd⟩ := by
    by_cases hdB : d ∈ I.amalgam.toCellScheme.below (B, k)
    · rw [hVB d hdB]
      exact (hrp ⟨d, hface d hdB hd⟩).symm
    · rw [hVdef]
      simp only [dite_eq_right hdB]
      exact Rows.extendBot_of_mem r hd
  have hVlB : I.amalgam.rows.IsLawfulBelow (B, k) fun d ↦ V d :=
    (Rows.isLawfulBelow_congr hVB).mpr hPA
  have hVlB' : I.amalgam.rows.IsLawfulBelow (B', k) fun d ↦ V d :=
    (Rows.isLawfulBelow_congr fun d hd ↦ (hVB' d hd).trans
      (Rows.extendBot_of_mem r hd).symm).mpr (Rows.isLawfulBelow_extendBot.mpr hr)
  have hlaw : (canonicalMultiScheme I R).rows.IsLawfulBelow ((univ : Finset (Fin 5)), k)
      fun z ↦ V (copyBase I z) := by
    rcases hBB' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hP V hVlB hVlB', hP V hVlB' hVlB]
  refine ⟨fun z ↦ V (copyBase I z), hlaw, fun z ↦ ?_, fun d ↦ ?_⟩
  · -- The cap agreement: the ambient is read through the bases.
    have hqz : q z = Q (multiOldCell I canonicalMult (copyBase I z)) := by
      rw [← eq_copyBase_of_isLawfulBelow R hQ z.2, hQdef, Rows.extendBot_of_mem q z.2]
    -- The labelling at a cell below the cap is `V` at its base, by definition.
    change min (V (copyBase I z.1)) c = _
    rw [hqz]
    have hgz : I.amalgam.toCellScheme.grade (copyBase I z) ≤ k :=
      (grade_copyBase R z.1).trans_le z.2.2
    rcases hcov _ hgz with h | h
    · rw [hVB _ h, hagree _ h]
    · by_cases hdB : copyBase I z.1 ∈ I.amalgam.toCellScheme.below (B, k)
      · rw [hVB _ hdB, hagree _ hdB]
      · rw [hVB' _ h]
        exact hrc ⟨_, h⟩
  · -- The restriction to `(B, k)` is the prescription.
    obtain ⟨e, he⟩ := exists_eq_multiOldCell (r := canonicalRows I R) (z := d.1)
      fun hU ↦ hB (univ_subset_iff.mp (hU ▸ d.2.1))
    have heB : e ∈ I.amalgam.toCellScheme.below (B, k) := by
      have := d.2
      rw [he, CellScheme.mem_below, gradedIndex_multiOldCell] at this
      exact this
    -- The restricted labelling at `d` is `V` at its base, by definition.
    change V (copyBase I d.1) = p d
    rw [he, copyBase_multiOldCell, hVB e heB, hPdef, ← he, Rows.extendBot_of_mem p d.2]

end VaughtConjecture.OrderedLayer

namespace VaughtConjecture.Seed

open Finset Label CellScheme OrderedLayer

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} {R : CopyRows I}

/-! ### The step from the product clause -/

/-- **The multi-layer step from the product clause.**  Under the product clause at the grades
`1, …, 4`, copy rows that are coded and lawful below both coatoms give the multi-layer step of the
canonical multi-layer scheme: the rows are consistent by the product clause, the lifts into the
full scope are the lifts from the common face (`Seed.hasCommonFaceLifts`), and the glued labelling
read through the bases is lawful.  The hypothesis at the grade `4` fails at all six compiled seeds,
for every copy rows (`Seed.not_canonicalProduct_seedHG` and its companions), so this form applies
at none of them; the form that applies to `seedHG` is
`Seed.canonicalMultiStep_of_productBelowTop`. -/
theorem canonicalMultiStep_of_product
    (hP : ∀ j, 1 ≤ j → j ≤ 4 → I.CanonicalProduct R j)
    (hcode : ∀ (k : Fin 4) (i : Fin 2) (d : Fin I.amalgam.card),
      I.amalgam.toCellScheme.grade d ≤ (k : ℕ) + 1 →
        R k i d < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hpair : ∀ (k : Fin 4) (i : Fin 2),
      I.amalgam.rows.IsLawfulBelow (coatomC, (k : ℕ) + 1) (fun d ↦ R k i d) ∧
        I.amalgam.rows.IsLawfulBelow (coatomD, (k : ℕ) + 1) (fun d ↦ R k i d)) :
    I.MultiLayerStep canonicalMult (canonicalRows I R) where
  pos _ := two_pos
  row_lt k i z hz := by
    rw [canonicalRows_apply R k i z]
    exact hcode k i _ ((grade_copyBase R z).trans_le hz.2)
  isLawfulBelow_row k i := by
    have := hP ((k : ℕ) + 1) (by omega) (by omega) (R k i) (hpair k i).1 (hpair k i).2
    simpa only [canonicalRows_apply] using this
  cappedLift_left k hk1 hk4 := cappedLift_of_canonicalProduct R (.inl ⟨rfl, rfl⟩) (hP k hk1 hk4)
    inter_subset_right (I.hasCommonFaceLifts k hk1 hk4).2
  cappedLift_right k hk1 hk4 := cappedLift_of_canonicalProduct R (.inr ⟨rfl, rfl⟩) (hP k hk1 hk4)
    inter_subset_left (I.hasCommonFaceLifts k hk1 hk4).1
  exists_isLawful := by
    have hlab := I.amalgam.isLawful
    refine ⟨fun z ↦ I.amalgam.label (copyBase I z), ?_,
      fun d ↦ congrArg I.amalgam.label (copyBase_multiOldCell I d)⟩
    exact (hP 4 (by omega) le_rfl _ (hlab.isLawfulBelow _) (hlab.isLawfulBelow _)).isLawful
      fun z ↦ mem_below_univ_four_multi z

/-- **The completion from the product clause**: a seed on five points with copy rows satisfying the
product clause at the grades `1, …, 4`, coded and lawful below both coatoms, has a completion below
the full grade (the canonical multi-layer scheme). -/
theorem nonempty_completionBelowFullGrade_of_canonicalProduct
    (hP : ∀ j, 1 ≤ j → j ≤ 4 → I.CanonicalProduct R j)
    (hcode : ∀ (k : Fin 4) (i : Fin 2) (d : Fin I.amalgam.card),
      I.amalgam.toCellScheme.grade d ≤ (k : ℕ) + 1 →
        R k i d < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hpair : ∀ (k : Fin 4) (i : Fin 2),
      I.amalgam.rows.IsLawfulBelow (coatomC, (k : ℕ) + 1) (fun d ↦ R k i d) ∧
        I.amalgam.rows.IsLawfulBelow (coatomD, (k : ℕ) + 1) (fun d ↦ R k i d)) :
    Nonempty (CompletionBelowFullGrade I) :=
  (canonicalMultiStep_of_product hP hcode hpair).nonempty_completionBelowFullGrade

variable (I) in
/-- A seed on five points **has a step of the canonical multi-layer scheme** when some copy rows
give the canonical multi-layer scheme the multi-layer step. -/
def HasCanonicalMultiStep : Prop :=
  ∃ R : CopyRows I, I.MultiLayerStep canonicalMult (canonicalRows I R)

/-- **A step of the canonical multi-layer scheme gives a completion below the full grade.** -/
theorem HasCanonicalMultiStep.nonempty_completionBelowFullGrade (h : I.HasCanonicalMultiStep) :
    Nonempty (CompletionBelowFullGrade I) :=
  h.choose_spec.nonempty_completionBelowFullGrade

end VaughtConjecture.Seed

namespace VaughtConjecture.OrderedLayer

open Finset Label CellScheme

variable {α : Ordinal.{u}}

/-! ### The top grade for seeds with bottom apexes -/

/-- **The labelling of `Ω` alone at the grade `4`** is lawful below `(univ, 4)` in a scheme on five
points whose grades are at most `4` and in which the row of every cell of grade `4` is `⊥` exactly
at the cells of grade other than `4`: at the cells of grade `4` the top shifter is a witness. -/
theorem isLawfulBelow_omega_of_rows {S : Scheme.{u} 5} (hgr : ∀ z, S.toCellScheme.grade z ≤ 4)
    (hrow : ∀ s, S.toCellScheme.grade s = 4 →
      ∀ t : S.toCellScheme.below (S.toCellScheme.gradedIndex s),
        S.rows.row s t = ⊥ ↔ S.toCellScheme.grade t.1 ≠ 4)
    {Ω : Label.{u}} (hΩ : IsSelfVisible 4 Ω) :
    S.rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4)
      fun z ↦ if S.toCellScheme.grade z = 4 then Ω else ⊥ := by
  refine (Rows.isLawfulBelow_iff_forall
    (w := fun z ↦ if S.toCellScheme.grade z = 4 then Ω else ⊥)).mpr
    ⟨fun d _ ↦ ?_, fun s _ ↦ ?_, fun s t _ hst hg ↦ ?_⟩
  · split_ifs with h
    · rw [h]; exact hΩ
    · exact isSelfVisible_bot _
  · by_cases hs : S.toCellScheme.grade s = 4
    · refine transformsTo_of_eq_bot_iff _
        (fun d : S.toCellScheme.below (S.toCellScheme.gradedIndex s) ↦ hgr d.1) hΩ _ _
        fun d ↦ ?_
      have key := hrow s hs d
      rw [ite_eq_left hs]
      by_cases hd4 : S.toCellScheme.grade d.1 = 4
      · rw [ite_eq_left hd4, min_self, ite_eq_right (fun h ↦ (key.mp h) hd4)]
      · rw [ite_eq_right hd4, min_bot_left, ite_eq_left (key.mpr hd4)]
    · simp only [ite_eq_right hs, min_bot_right]
      exact TransformsTo.bot _ _
  · exact ⟨t, rfl, by rw [hg]⟩

variable {I : Seed.{u} α 3}

variable (I) in
/-- **The top row of the amalgam**: `ω + 4` at the cells of grade `4`, `⊥` elsewhere. -/
noncomputable def amalgamTopRow (d : Fin I.amalgam.card) : Label.{u} :=
  topRow (I.amalgam.toCellScheme.gradedIndex d)

/-- The top row of the amalgam is `ω + 4` at the cells of grade `4` and `⊥` elsewhere. -/
theorem amalgamTopRow_apply (d : Fin I.amalgam.card) :
    amalgamTopRow I d = if I.amalgam.toCellScheme.grade d = 4 then gridPoint 4 1 else ⊥ := rfl

variable {R : CopyRows I}

/-- With the top row at the grade `4`, the row of every cell of grade `4` of the canonical
multi-layer scheme over a seed with bottom apexes is `⊥` exactly at the cells of grade other
than `4`. -/
theorem row_eq_bot_iff_of_grade_four_canonical (hI : I.HasBottomApexes)
    (hR3 : ∀ i, R 3 i = amalgamTopRow I) {s : Fin (canonicalMultiScheme I R).card}
    (hs : (canonicalMultiScheme I R).toCellScheme.grade s = 4)
    (t : (canonicalMultiScheme I R).toCellScheme.below
      ((canonicalMultiScheme I R).toCellScheme.gradedIndex s)) :
    (canonicalMultiScheme I R).rows.row s t = ⊥ ↔
      (canonicalMultiScheme I R).toCellScheme.grade t.1 ≠ 4 := by
  rcases multiCell_cases (r := canonicalRows I R) s with ⟨a, rfl⟩ | ⟨k, i, rfl⟩
  · rw [grade_multiOldCell] at hs
    exact row_multiOldCell_eq_bot_iff hI hs t
  · rw [grade_multiNewCell] at hs
    obtain rfl : k = 3 := Fin.ext (by omega)
    rw [row_canonical, hR3, amalgamTopRow, topRow]
    -- The top row at the base, by its definition through the graded index.
    change (if I.amalgam.toCellScheme.grade (copyBase I t.1) = 4 then _ else _) = ⊥ ↔ _
    rw [grade_copyBase]
    split_ifs with h
    · exact ⟨fun h' ↦ absurd h' (gridPoint_ne_bot 4 1), fun h' ↦ absurd h h'⟩
    · exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩

/-- With the top row at the grade `4`, a labelling lawful below `(univ, 4)` is constant on the
cells of grade `4`: both copies of grade `4` read every cell of grade `4` at `ω + 4`, so each is
at most every cell of grade `4`, and each cell of grade `4` is at most one of them. -/
theorem eq_of_grade_four_canonical (hR3 : ∀ i, R 3 i = amalgamTopRow I)
    {w : Fin (canonicalMultiScheme I R).card → Label.{u}}
    (hw : (canonicalMultiScheme I R).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4)
      fun z ↦ w z)
    {z : Fin (canonicalMultiScheme I R).card}
    (hz : (canonicalMultiScheme I R).toCellScheme.grade z = 4) :
    w z = w (multiNewCell I canonicalMult 3 0) := by
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  have gκ (i : Fin 2) : (canonicalMultiScheme I R).toCellScheme.grade
      (multiNewCell I canonicalMult 3 i) = 4 :=
    grade_multiNewCell (r := canonicalRows I R) 3 i
  have bel (i : Fin 2) (y : Fin (canonicalMultiScheme I R).card) :
      y ∈ (canonicalMultiScheme I R).toCellScheme.below
        ((canonicalMultiScheme I R).toCellScheme.gradedIndex
          (multiNewCell I canonicalMult 3 i)) := by
    rw [gradedIndex_multiNewCell]; exact ⟨subset_univ _, grade_le_four_multi y⟩
  -- Each copy of grade `4` is at most every cell of grade `4`.
  have low (i : Fin 2) (y : Fin (canonicalMultiScheme I R).card)
      (hy : (canonicalMultiScheme I R).toCellScheme.grade y = 4) :
      w (multiNewCell I canonicalMult 3 i) ≤ w y := by
    have L := hl _ (mem_below_univ_four_multi (multiNewCell I canonicalMult 3 i))
    have hrow : (canonicalMultiScheme I R).rows.row (multiNewCell I canonicalMult 3 i)
          ⟨multiNewCell I canonicalMult 3 i, bel i _⟩ ≤
        (canonicalMultiScheme I R).rows.row (multiNewCell I canonicalMult 3 i) ⟨y, bel i y⟩ := by
      rw [row_canonical, row_canonical, hR3, amalgamTopRow, amalgamTopRow, topRow, topRow]
      -- Both readings are the top row at the bases, by its definition through the graded index.
      change (if I.amalgam.toCellScheme.grade (copyBase I (multiNewCell I canonicalMult 3 i)) = 4
        then _ else _) ≤ (if I.amalgam.toCellScheme.grade (copyBase I y) = 4 then _ else _)
      rw [grade_copyBase, grade_copyBase, gκ, hy]
    have := L.le_of_le hrow (by dsimp only; rw [hy, gκ])
    simp only [min_self] at this
    exact this.trans (min_le_left _ _)
  have h01 : w (multiNewCell I canonicalMult 3 0) = w (multiNewCell I canonicalMult 3 1) :=
    le_antisymm (low 0 _ (gκ 1)) (low 1 _ (gκ 0))
  refine le_antisymm ?_ (low 0 z hz)
  obtain ⟨u, hu, hle⟩ := ha z _ (mem_below_univ_four_multi (multiNewCell I canonicalMult 3 0))
    (by rw [scope_multiNewCell]; exact subset_univ _) (hz.trans (gκ 0).symm)
  obtain ⟨k', i'', hk', rfl⟩ := exists_eq_multiNewCell (hu.trans (gradedIndex_multiNewCell 3 0))
  obtain rfl : k' = 3 := Fin.ext (by omega)
  match i'' with
  | ⟨0, _⟩ => exact hle
  | ⟨1, _⟩ => exact hle.trans h01.ge

/-- With the top row at the grade `4`, a labelling lawful below `(univ, 4)` that is not `⊥` at the
first copy of grade `4` is `⊥` below the grade `4`: the row of that copy is `⊥` there. -/
theorem eq_bot_of_grade_four_canonical (hI : I.HasBottomApexes)
    (hR3 : ∀ i, R 3 i = amalgamTopRow I)
    {w : Fin (canonicalMultiScheme I R).card → Label.{u}}
    (hw : (canonicalMultiScheme I R).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4)
      fun z ↦ w z)
    (hΩ : w (multiNewCell I canonicalMult 3 0) ≠ ⊥) {z : Fin (canonicalMultiScheme I R).card}
    (hz : (canonicalMultiScheme I R).toCellScheme.grade z ≠ 4) : w z = ⊥ := by
  obtain ⟨-, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  have hz' : z ∈ (canonicalMultiScheme I R).toCellScheme.below
      ((canonicalMultiScheme I R).toCellScheme.gradedIndex (multiNewCell I canonicalMult 3 0)) := by
    rw [gradedIndex_multiNewCell]; exact ⟨subset_univ _, grade_le_four_multi z⟩
  have := (hl _ (mem_below_univ_four_multi (multiNewCell I canonicalMult 3 0))).eq_bot
    (d := ⟨z, hz'⟩) ((row_eq_bot_iff_of_grade_four_canonical hI hR3
      (grade_multiNewCell 3 0) ⟨z, hz'⟩).mpr hz)
  exact (min_eq_bot.mp this).resolve_right hΩ

end VaughtConjecture.OrderedLayer

namespace VaughtConjecture.Seed

open Finset Label CellScheme OrderedLayer

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} {R : CopyRows I}

/-- **The multi-layer step from the product clause below the top grade**, for a seed with bottom
apexes and the top row at the grade `4`: the product clause at the grades `1, 2, 3`, with copy rows
at those grades coded and lawful below both coatoms, gives the multi-layer step.  At the grade `4`
the row is the labelling of `ω + 4` alone, the lifts come from those at the grade `3`
(`OrderedLayer.cappedLift_four_of_oldCells`), and the glued labelling is the labelling of `⊤`
alone. -/
theorem canonicalMultiStep_of_productBelowTop (hI : I.HasBottomApexes)
    (hR3 : ∀ i, R 3 i = amalgamTopRow I)
    (hP : ∀ j, 1 ≤ j → j ≤ 3 → I.CanonicalProduct R j)
    (hcode : ∀ (k : Fin 4) (i : Fin 2) (d : Fin I.amalgam.card), (k : ℕ) ≤ 2 →
      I.amalgam.toCellScheme.grade d ≤ (k : ℕ) + 1 →
        R k i d < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hpair : ∀ (k : Fin 4) (i : Fin 2), (k : ℕ) ≤ 2 →
      I.amalgam.rows.IsLawfulBelow (coatomC, (k : ℕ) + 1) (fun d ↦ R k i d) ∧
        I.amalgam.rows.IsLawfulBelow (coatomD, (k : ℕ) + 1) (fun d ↦ R k i d)) :
    I.MultiLayerStep canonicalMult (canonicalRows I R) := by
  -- The grade `4` of the canonical multi-layer scheme.
  have hΩ (Ω : Label.{u}) (h : IsSelfVisible 4 Ω) := isLawfulBelow_omega_of_rows
    (S := canonicalMultiScheme I R) grade_le_four_multi
    (fun _ hs ↦ row_eq_bot_iff_of_grade_four_canonical hI hR3 hs) h
  have lift4 {B : Finset (Fin 5)} (hB : B = coatomC ∨ B = coatomD)
      (h3 : (canonicalMultiScheme I R).rows.CappedLift (X := (B, 3))
        (Y := ((univ : Finset (Fin 5)), 3)) ⟨subset_univ _, le_rfl⟩) :=
    cappedLift_four_of_oldCells hI (S := canonicalMultiScheme I R) (multiOldCell I canonicalMult)
      gradedIndex_multiOldCell (fun _ hz ↦ exists_eq_multiOldCell hz)
      (fun _ ha ↦ row_multiOldCell_eq_bot_iff hI ha) grade_le_four_multi
      (multiNewCell I canonicalMult 3 0) (fun _ hw _ hz ↦ eq_of_grade_four_canonical hR3 hw hz)
      (fun _ hw hT _ hz ↦ eq_bot_of_grade_four_canonical hI hR3 hw hT hz) hΩ hB h3
  have liftC (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :=
    cappedLift_of_canonicalProduct R (.inl ⟨rfl, rfl⟩) (hP k hk1 hk3) inter_subset_right
      (I.hasCommonFaceLifts k hk1 (by omega)).2
  have liftD (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :=
    cappedLift_of_canonicalProduct R (.inr ⟨rfl, rfl⟩) (hP k hk1 hk3) inter_subset_left
      (I.hasCommonFaceLifts k hk1 (by omega)).1
  refine ⟨fun _ ↦ two_pos, fun k i z hz ↦ ?_, fun k i ↦ ?_, fun k hk1 hk4 ↦ ?_,
    fun k hk1 hk4 ↦ ?_, ⟨fun z ↦ if (canonicalMultiScheme I R).toCellScheme.grade z = 4 then ⊤
      else ⊥, (hΩ ⊤ (isSelfVisible_top 4)).isLawful mem_below_univ_four_multi, fun d ↦ ?_⟩⟩
  · rw [canonicalRows_apply R k i z]
    rcases (show (k : ℕ) ≤ 2 ∨ k = 3 by omega) with hk | rfl
    · exact hcode k i _ hk ((grade_copyBase R z).trans_le hz.2)
    · rw [hR3, amalgamTopRow, topRow]
      split_ifs
      · exact gridPoint_lt_omega0_sq 4 1
      · exact WithBot.bot_lt_coe _
  · rcases (show (k : ℕ) ≤ 2 ∨ k = 3 by omega) with hk | rfl
    · have := hP ((k : ℕ) + 1) (by omega) (by omega) (R k i) (hpair k i hk).1 (hpair k i hk).2
      simpa only [canonicalRows_apply] using this
    · have h4 := hΩ _ (isSelfVisible_gridPoint 4 1)
      refine (Rows.isLawfulBelow_congr (X := ((univ : Finset (Fin 5)), 4))
        (w := fun z ↦ if (canonicalMultiScheme I R).toCellScheme.grade z = 4 then gridPoint 4 1
          else ⊥) fun z _ ↦ ?_).mp h4
      simp only [canonicalRows_apply, hR3, amalgamTopRow_apply, grade_copyBase]
  · rcases (show k ≤ 3 ∨ k = 4 by omega) with hk3 | rfl
    · exact liftC k hk1 hk3
    · exact lift4 (.inl rfl) (liftC 3 (by omega) le_rfl)
  · rcases (show k ≤ 3 ∨ k = 4 by omega) with hk3 | rfl
    · exact liftD k hk1 hk3
    · exact lift4 (.inr rfl) (liftD 3 (by omega) le_rfl)
  · dsimp only
    rw [grade_multiOldCell, hI.label_eq]

/-- **The completion from the product clause below the top grade**, for a seed with bottom apexes
and the top row at the grade `4`. -/
theorem nonempty_completionBelowFullGrade_of_canonicalProductBelowTop (hI : I.HasBottomApexes)
    (hR3 : ∀ i, R 3 i = amalgamTopRow I)
    (hP : ∀ j, 1 ≤ j → j ≤ 3 → I.CanonicalProduct R j)
    (hcode : ∀ (k : Fin 4) (i : Fin 2) (d : Fin I.amalgam.card), (k : ℕ) ≤ 2 →
      I.amalgam.toCellScheme.grade d ≤ (k : ℕ) + 1 →
        R k i d < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hpair : ∀ (k : Fin 4) (i : Fin 2), (k : ℕ) ≤ 2 →
      I.amalgam.rows.IsLawfulBelow (coatomC, (k : ℕ) + 1) (fun d ↦ R k i d) ∧
        I.amalgam.rows.IsLawfulBelow (coatomD, (k : ℕ) + 1) (fun d ↦ R k i d)) :
    Nonempty (CompletionBelowFullGrade I) :=
  (canonicalMultiStep_of_productBelowTop hI hR3 hP hcode hpair).nonempty_completionBelowFullGrade

end VaughtConjecture.Seed
