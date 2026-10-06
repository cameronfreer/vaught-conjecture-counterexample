/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Legal
import VaughtConjecture.Extension.CoatomAmalgam

/-!
# Correspondence: the amalgam of two coatom types

Roadmap, "Manuscript concordance", row 15.

## The setting of [Kni26, §4.3]

A finite set `A` of size `n ≥ 2`, a plan `P` on `A`, distinct `a, b ∈ A` with `A \ {a}` and
`A \ {b}` in `P`, and complete domains `D^a` on `A \ {a}` and `D^b` on `A \ {b}` with
`D^a_{⟨A \ {b}, n - 2⟩} = D^b_{⟨A \ {a}, n - 2⟩}`, equivalently (the cells of `D^a` have scope in
`A \ {a}`, those of `D^b` in `A \ {b}`) whose restrictions to `⟨A \ {a, b}, n - 2⟩` coincide;
`E^a`, `E^b` are their semantics.  Here `A = Fin (m + 2)`, `a` is the last point and `b = m`;
`D^a` and `D^b` are schemes `Sa` and `Sb` on `m + 1` points placed along `Coatom.left m` and
`Coatom.right m`, and the coincidence of the restrictions is the hypothesis
`h : Sa.comap (face m) = Sb.comap (face m)`.  The cells of a scheme are positions `Fin card`;
the printed codes are forgotten under the corrected convention of row 7.  The comparison is
made on these numbered schemes, with the common-face numbering preserved: coincidence of their
restrictions is the literal equality `h`, cell order included, not an assertion that the schemes
recover the printed codes.  The
identification of a cell of the common face of `Sa` with the same cell of `Sb` is
`Coatom.overlap h`.  Neither completeness nor any other law of `Sa` and `Sb` is assumed by the
identification below, which therefore holds in particular under them.

## Definition 4.3.1: the amalgam

The printed definition has two clauses, `D = D^a ∪ D^b` and `E = E^a ∪ E^b`.  A cell scheme `D`
with rows `R` and maps `ea`, `eb` of the cells of `Sa` and `Sb` into it satisfies them when
(`Coatom.PrintedAmalgam`):

| Printed | Fields |
| --- | --- |
| setting: the points `A` and the plan `P = Q ∪ R ∪ {A}` | `ground`, `faces` |
| `D^a ⊆ D`, with `D^a_{B,j} ⊆ D_{B,j}` | `injective_left`, `scope_left`, `grade_left` |
| `D^b ⊆ D`, with `D^b_{B,j} ⊆ D_{B,j}` | `injective_right`, `scope_right`, `grade_right` |
| `D^a ∩ D^b` is the common restriction | `eq_iff` |
| `D ⊆ D^a ∪ D^b` | `cover` |
| `E = E^a ∪ E^b` | `row_left`, `row_right` |

The plan of the setting is `Q ∪ R ∪ {A}` with `Q` and `R` the plans of `D^a` and `D^b`
([Kni26, Definition 2.1.1, clause 3(c)]), which is `Coatom.amalgamFaces Sa Sb`.

**Identification** (`Coatom.printedAmalgam_iff`): `(D, R, ea, eb)` satisfies the printed
definition exactly when it is the amalgamated cell scheme `Coatom.amalgamCellScheme h` with its
rows `Coatom.amalgamRows h`, reindexed along a bijection of cells that sends the cells of `Sa` and
`Sb` to `ea` and `eb`.  In particular the amalgamated scheme `Coatom.amalgam h`, with the positions
`Coatom.posLeft h` and `Coatom.posRight h` of the cells of `Sa` and `Sb`, is the printed amalgam
(`Coatom.printedAmalgam_amalgam`).  The stage type `Coatom.amalgamType hta htb` has this scheme,
and its labels are those of `ta` on the cells of `Sa` and of `tb` on the cells of `Sb`
(`Coatom.amalgamType_label_posLeft`, `Coatom.amalgamType_label_posRight`): the union of the two
types, which Definition 4.3.1 does not mention.

**Departures.**
1. *The enumeration of the cells.*  The cells of `Coatom.amalgam h` are enumerated in the merged
   order (`Coatom.amalgamEnum`), an order the printed domain does not carry; the identification
   holds for every enumeration (`Coatom.printedAmalgam_iff` quantifies over all bijections).
2. *The laws of `D^a` and `D^b`*: harmless, since `Coatom.printedAmalgam_iff` holds without them.

## Lemma 4.3.2: the rows of the amalgam

The printed lemma has three conclusions; they are compared separately.
1. *`D` is a domain.*  **Not correct as stated**: a domain carries a complete semantics
   ([Kni26, Definitions 2.6.1 and 2.5.15]), and the amalgam has no cell of full scope, so the
   graded face `⟨A, 1⟩` of the printed plan carries no cell (`Coatom.not_isComplete_amalgamType`,
   with `CellScheme.IsComplete` the printed completeness verbatim); the amalgam is not legal
   (`Coatom.not_isLegal_amalgamType`).  The end of [Kni26, §4.2] says as much: the
   union is "consistent and bountiful; it is merely not complete".  What holds: every other graded
   face carries a cell (`Coatom.exists_gradedIndex_eq_amalgamType`), the scheme is well formed and
   coded (`Coatom.isWellFormed_amalgam`, `Coatom.isCoded_amalgam`).
2. *`E` is a consistent semantics.*  Consistency [Kni26, Definition 2.5.12] asks that every row
   `E(Σ)` respect the semantics below `Σ` in the sense of row 4 (`PrintedRespects`), which
   includes the orderliness of `E(Σ)` that a semantics requires [Kni26, Definition 2.5.3].  In
   this printed form, from the printed hypotheses on `Sa` and `Sb`, at every stage that is zero or
   a limit: `Coatom.printedRespects_row_amalgam`, from `Coatom.isConsistent_amalgam` through
   `CellScheme.Rows.printedRespects_below_iff`, the identification of row 4 below a cell.
3. *`E` is bountiful.*  This rests on row 6.  From bountiful `Sa` and `Sb` in the sense of
   `IsBountiful`, the rows of the amalgam are bountiful as printed at `ω₁`
   (`Coatom.printedBountiful_omega_one_amalgamType`); from rows bountiful as printed at every stage
   that is zero or a limit, so are the rows of the amalgam
   (`Coatom.forall_printedBountiful_amalgam`).
   From rows bountiful as printed at `ω₁` alone, nothing is proved: that would need the converse
   of `CellScheme.Rows.IsBountiful.printedBountiful` at a single stage, which row 6 lacks.

## Placement

The concordance and its notes are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Coatom

variable {m : ℕ} {Sa Sb : Scheme.{u} (m + 1)} (h : Sa.comap (face m) = Sb.comap (face m))

/-! ### The amalgam, [Kni26, Definition 4.3.1] -/

section Printed

variable {ι : Type*}

/-- **The amalgam** [Kni26, Definition 4.3.1]: the cell scheme `D` on `Fin (m + 2)` with rows `R`
is the union of `Sa` and `Sb`, placed along the two coatoms, with the cells of `Sa` and `Sb` at
`ea` and `eb` and the cells of the common face identified by `Coatom.overlap h`. -/
structure PrintedAmalgam (D : CellScheme ι (Fin (m + 2))) (R : D.Rows.{u})
    (ea : Fin Sa.card → ι) (eb : Fin Sb.card → ι) : Prop where
  /-- The setting of [Kni26, §4.3]: the points are `A`. -/
  ground : D.ground = univ
  /-- The setting of [Kni26, §4.3]: the plan is `Q ∪ R ∪ {A}`, with `Q` and `R` the plans of `D^a`
  and `D^b` ([Kni26, Definition 2.1.1, clause 3(c)]). -/
  faces : D.faces = amalgamFaces Sa Sb
  /-- Clause `D = D^a ∪ D^b` of [Kni26, Definition 4.3.1]: `D^a ⊆ D`. -/
  injective_left : Function.Injective ea
  /-- Clause `D = D^a ∪ D^b` of [Kni26, Definition 4.3.1]: a cell of `D^a_{B,j}` lies in
  `D_{B,j}`, its scope moved along the first coatom. -/
  scope_left (i : Fin Sa.card) : D.scope (ea i) = (Sa.toCellScheme.scope i).map (left m)
  /-- Clause `D = D^a ∪ D^b` of [Kni26, Definition 4.3.1]: a cell of `D^a_{B,j}` lies in
  `D_{B,j}`. -/
  grade_left (i : Fin Sa.card) : D.grade (ea i) = Sa.toCellScheme.grade i
  /-- Clause `D = D^a ∪ D^b` of [Kni26, Definition 4.3.1]: `D^b ⊆ D`. -/
  injective_right : Function.Injective eb
  /-- Clause `D = D^a ∪ D^b` of [Kni26, Definition 4.3.1]: a cell of `D^b_{B,j}` lies in
  `D_{B,j}`, its scope moved along the second coatom. -/
  scope_right (j : Fin Sb.card) : D.scope (eb j) = (Sb.toCellScheme.scope j).map (right m)
  /-- Clause `D = D^a ∪ D^b` of [Kni26, Definition 4.3.1]: a cell of `D^b_{B,j}` lies in
  `D_{B,j}`. -/
  grade_right (j : Fin Sb.card) : D.grade (eb j) = Sb.toCellScheme.grade j
  /-- Clause `D = D^a ∪ D^b` of [Kni26, Definition 4.3.1]: a cell of `D^a` and a cell of `D^b` are
  the same element of the union exactly when they are the same cell of the common restriction.
  The "if" direction is the equality of the two restrictions in the setting of [Kni26, §4.3]; the
  "only if" direction is [Kni26, Proposition 2.6.3, clause 6]: a cell of `D^a` whose scope is not
  contained in `A \ {b}` is not a cell of `D^b`, and symmetrically. -/
  eq_iff (i : Fin Sa.card) (j : Fin Sb.card) :
    ea i = eb j ↔ ∃ t, Sa.cellMap (face m) t = i ∧ overlap h t = j
  /-- Clause `D = D^a ∪ D^b` of [Kni26, Definition 4.3.1]: `D ⊆ D^a ∪ D^b`. -/
  cover (d : ι) : (∃ i, ea i = d) ∨ ∃ j, eb j = d
  /-- Clause `E = E^a ∪ E^b` of [Kni26, Definition 4.3.1]: on a cell of `D^a`, `E` is `E^a`. -/
  row_left (i i' : Fin Sa.card)
    (hi : i' ∈ Sa.toCellScheme.below (Sa.toCellScheme.gradedIndex i))
    (hd : ea i' ∈ D.below (D.gradedIndex (ea i))) :
    R.row (ea i) ⟨ea i', hd⟩ = Sa.rows.row i ⟨i', hi⟩
  /-- Clause `E = E^a ∪ E^b` of [Kni26, Definition 4.3.1]: on a cell of `D^b`, `E` is `E^b`. -/
  row_right (j j' : Fin Sb.card)
    (hj : j' ∈ Sb.toCellScheme.below (Sb.toCellScheme.gradedIndex j))
    (hd : eb j' ∈ D.below (D.gradedIndex (eb j))) :
    R.row (eb j) ⟨eb j', hd⟩ = Sb.rows.row j ⟨j', hj⟩

/-- A cell of `Sa` and a cell of `Sb` are the same cell of the amalgam exactly when they are the
same cell of the common face. -/
theorem inl_eq_rightFun_iff (i : Fin Sa.card) (j : Fin Sb.card) :
    (Merge.inl i : AmalgamCell h) = Merge.rightFun _ (overlap h) j ↔
      ∃ t, Sa.cellMap (face m) t = i ∧ overlap h t = j := by
  by_cases hj : j ∈ Set.range (overlap h)
  · obtain ⟨t, rfl⟩ := hj
    rw [Merge.rightFun_eb, Merge.inl.injEq]
    refine ⟨fun hi ↦ ⟨t, hi.symm, rfl⟩, ?_⟩
    rintro ⟨t', rfl, ht'⟩
    rw [(overlap h).injective ht']
  · rw [Merge.rightFun_of_notMem _ _ hj]
    exact ⟨fun he ↦ (by cases he), fun ⟨t, _, ht⟩ ↦ absurd ⟨t, ht⟩ hj⟩

variable {h} {D : CellScheme ι (Fin (m + 2))} {R : D.Rows.{u}} {ea : Fin Sa.card → ι}
  {eb : Fin Sb.card → ι}

/-- The cell map of a printed amalgam, from the cells of the amalgamated cell scheme. -/
def PrintedAmalgam.cellFun (_ : PrintedAmalgam h D R ea eb) : AmalgamCell h → ι
  | .inl i => ea i
  | .inr j _ => eb j

/-- The cell map of a printed amalgam sends the cells of `Sb` to `eb`. -/
theorem PrintedAmalgam.cellFun_rightFun (hP : PrintedAmalgam h D R ea eb) (j : Fin Sb.card) :
    hP.cellFun (Merge.rightFun _ (overlap h) j) = eb j := by
  by_cases hj : j ∈ Set.range (overlap h)
  · obtain ⟨t, rfl⟩ := hj
    rw [Merge.rightFun_eb]
    exact (hP.eq_iff _ _).mpr ⟨t, rfl, rfl⟩
  · rw [Merge.rightFun_of_notMem _ _ hj]
    rfl

/-- The cell map of a printed amalgam is a bijection. -/
theorem PrintedAmalgam.bijective_cellFun (hP : PrintedAmalgam h D R ea eb) :
    Function.Bijective hP.cellFun := by
  refine ⟨?_, fun d ↦ ?_⟩
  · rintro (i | ⟨j, hj⟩) (i' | ⟨j', hj'⟩) he
    · exact congrArg _ (hP.injective_left he)
    · obtain ⟨t, -, ht⟩ := (hP.eq_iff i j').mp he
      exact absurd ⟨t, ht⟩ hj'
    · obtain ⟨t, -, ht⟩ := (hP.eq_iff i' j).mp he.symm
      exact absurd ⟨t, ht⟩ hj
    · cases hP.injective_right he
      rfl
  · rcases hP.cover d with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨.inl i, rfl⟩
    · exact ⟨_, hP.cellFun_rightFun j⟩

/-- **The amalgam is the printed amalgam** [Kni26, Definition 4.3.1]: a cell scheme with rows
satisfies the two clauses of the printed definition, with the cells of `Sa` and `Sb` at `ea` and
`eb`, exactly when it is the amalgamated cell scheme with its rows, reindexed along a bijection of
cells sending the cells of `Sa` and `Sb` to `ea` and `eb`. -/
theorem printedAmalgam_iff :
    PrintedAmalgam h D R ea eb ↔ ∃ e : AmalgamCell h ≃ ι,
      (∀ i, e (.inl i) = ea i) ∧ (∀ j, e (Merge.rightFun _ (overlap h) j) = eb j) ∧
      D = (amalgamCellScheme h).reindex e.symm ∧
      ∀ x y (hy : y ∈ (amalgamCellScheme h).below ((amalgamCellScheme h).gradedIndex x))
        (hd : e y ∈ D.below (D.gradedIndex (e x))),
        R.row (e x) ⟨e y, hd⟩ = (amalgamRows h).row x ⟨y, hy⟩ := by
  constructor
  · intro hP
    set e := Equiv.ofBijective _ hP.bijective_cellFun
    have hscope (x : AmalgamCell h) : D.scope (e x) = (amalgamCellScheme h).scope x := by
      rcases x with i | ⟨j, hj⟩
      · exact hP.scope_left i
      · exact hP.scope_right j
    have hgrade (x : AmalgamCell h) : D.grade (e x) = (amalgamCellScheme h).grade x := by
      rcases x with i | ⟨j, hj⟩
      · exact hP.grade_left i
      · exact hP.grade_right j
    refine ⟨e, fun _ ↦ rfl, hP.cellFun_rightFun, ?_, fun x y hy hd ↦ ?_⟩
    · ext1
      · exact hP.ground
      · exact hP.faces
      · funext d
        rw [CellScheme.reindex_scope, ← hscope, e.apply_symm_apply]
      · funext d
        rw [CellScheme.reindex_grade, ← hgrade, e.apply_symm_apply]
    rcases x with i | ⟨j, hj⟩
    · -- a cell below a cell of `Sa` is a cell of `Sa`
      obtain ⟨i', rfl⟩ := exists_eq_inl_of_scope_subset h
        (hy.1.trans (map_subset_map.mpr (subset_univ _)))
      rw [amalgamRows_inl_inl]
      exact hP.row_left i i' _ hd
    · -- a cell below a cell of `Sb` is a cell of `Sb`
      obtain ⟨j', rfl⟩ := mem_range_right_of_scope_subset h
        (hy.1.trans (map_subset_map.mpr (subset_univ _)))
      have hjj : (Merge.inr j hj : AmalgamCell h) = Merge.rightFun _ (overlap h) j :=
        (Merge.rightFun_of_notMem _ _ hj).symm
      have hy' : j' ∈ Sb.toCellScheme.below (Sb.toCellScheme.gradedIndex j) :=
        ((isLowerEmbedding_right h).le_iff j' j).mp (by rw [← hjj]; exact hy)
      have hej : e (Merge.rightFun _ (overlap h) j') = eb j' := hP.cellFun_rightFun j'
      rw [amalgamRows_inr_right h j hj ⟨j', hy'⟩ hy]
      refine (R.row_congr (t := ⟨_, hd⟩) (t' := ⟨eb j', by rw [← hej]; exact hd⟩)
        (rfl : e (Merge.inr j hj) = eb j) hej).trans ?_
      exact hP.row_right j j' hy' _
  · rintro ⟨e, hl, hr, rfl, hrow⟩
    have hscope (x : AmalgamCell h) :
        ((amalgamCellScheme h).reindex e.symm).scope (e x) = (amalgamCellScheme h).scope x := by
      rw [CellScheme.reindex_scope, e.symm_apply_apply]
    have hgrade (x : AmalgamCell h) :
        ((amalgamCellScheme h).reindex e.symm).grade (e x) = (amalgamCellScheme h).grade x := by
      rw [CellScheme.reindex_grade, e.symm_apply_apply]
    have hindex (x : AmalgamCell h) :
        ((amalgamCellScheme h).reindex e.symm).gradedIndex (e x) =
          (amalgamCellScheme h).gradedIndex x :=
      congrArg₂ Prod.mk (hscope x) (hgrade x)
    refine
      { ground := rfl
        faces := rfl
        injective_left := fun i i' he ↦ by
          rw [← hl, ← hl] at he
          exact Merge.inl.inj (e.injective he)
        scope_left := fun i ↦ by rw [← hl, hscope]; rfl
        grade_left := fun i ↦ by rw [← hl, hgrade]; rfl
        injective_right := fun j j' he ↦ by
          rw [← hr, ← hr] at he
          exact (Merge.right _ (overlap h)).injective (e.injective he)
        scope_right := fun j ↦ by rw [← hr, hscope, amalgamScope_right]
        grade_right := fun j ↦ by rw [← hr, hgrade, amalgamGrade_right]
        eq_iff := fun i j ↦ by rw [← hl, ← hr, e.apply_eq_iff_eq, inl_eq_rightFun_iff]
        cover := fun d ↦ by
          obtain ⟨x, rfl⟩ := e.surjective d
          rcases x with i | ⟨j, hj⟩
          · exact Or.inl ⟨i, (hl i).symm⟩
          · exact Or.inr ⟨j, by rw [← hr, Merge.rightFun_of_notMem _ _ hj]⟩
        row_left := fun i i' hi hd ↦ ?_
        row_right := fun j j' hj hd ↦ ?_ }
    · have hd' : e (.inl i') ∈ ((amalgamCellScheme h).reindex e.symm).below
          (((amalgamCellScheme h).reindex e.symm).gradedIndex (e (.inl i))) := by
        rw [CellScheme.mem_below, hindex, hindex]
        exact ((isLowerEmbedding_left h).le_iff i' i).mpr hi
      rw [R.row_congr (hl i).symm (t' := ⟨_, hd'⟩) (hl i').symm,
        hrow _ _ (((isLowerEmbedding_left h).le_iff i' i).mpr hi)]
      exact amalgamRows_inl_inl h i i' _
    · have hle := ((isLowerEmbedding_right h).le_iff j' j).mpr hj
      have hd' : e (Merge.rightFun _ (overlap h) j') ∈
          ((amalgamCellScheme h).reindex e.symm).below
            (((amalgamCellScheme h).reindex e.symm).gradedIndex
              (e (Merge.rightFun _ (overlap h) j))) := by
        rw [CellScheme.mem_below, hindex, hindex]
        exact hle
      rw [R.row_congr (hr j).symm (t' := ⟨_, hd'⟩) (hr j').symm, hrow _ _ hle]
      have hrow' := congrArg (fun R ↦ R.row j ⟨j', hj⟩) (comap_amalgamRows_right h)
      simpa only [CellScheme.Rows.comap_row] using hrow'

end Printed

/-- **The amalgamated cell scheme is the printed amalgam** [Kni26, Definition 4.3.1], with the
cells of `Sa` and `Sb` at `Merge.inl` and `Merge.rightFun`. -/
theorem printedAmalgam_amalgamCellScheme :
    PrintedAmalgam h (amalgamCellScheme h) (amalgamRows h) Merge.inl
      (Merge.rightFun _ (overlap h)) :=
  printedAmalgam_iff.mpr ⟨Equiv.refl _, fun _ ↦ rfl, fun _ ↦ rfl, rfl, fun _ _ _ _ ↦ rfl⟩

/-- **The amalgamated scheme is the printed amalgam** [Kni26, Definition 4.3.1], with the cells of
`Sa` and `Sb` at their positions `posLeft h` and `posRight h`. -/
theorem printedAmalgam_amalgam :
    PrintedAmalgam h (amalgam h).toCellScheme (amalgam h).rows (posLeft h) (posRight h) :=
  printedAmalgam_iff.mpr ⟨(amalgamEnum h).symm.toEquiv, fun _ ↦ rfl, fun _ ↦ rfl, rfl,
    fun x y _ _ ↦ by
      rw [amalgam_row]
      exact CellScheme.Rows.row_congr _ ((amalgamEnum h).apply_symm_apply x)
        ((amalgamEnum h).apply_symm_apply y)⟩

/-! ### The amalgam of two coatom stage types -/

section StageType

variable {α : Ordinal.{u}} {ta tb : StageType.{u} α (m + 1)} {p : StageType.{u} α m}
  (hta : StageType.restrictFace (face m) ta = some p)
  (htb : StageType.restrictFace (face m) tb = some p)

/-- **The labels of the amalgam on the cells of `ta`** are those of `ta`. -/
theorem amalgamType_label_posLeft (i : Fin ta.card) :
    (amalgamType hta htb).label (posLeft _ i) = ta.label i := by
  -- the label of the amalgam at a position is `amalgamLabel` at the cell enumerated there
  change amalgamLabel hta htb (amalgamEnum _ (posLeft _ i)) = _
  rw [amalgamEnum_posLeft]
  rfl

/-- **The labels of the amalgam on the cells of `tb`** are those of `tb`. -/
theorem amalgamType_label_posRight (j : Fin tb.card) :
    (amalgamType hta htb).label (posRight _ j) = tb.label j := by
  -- the label of the amalgam at a position is `amalgamLabel` at the cell enumerated there
  change amalgamLabel hta htb (amalgamEnum _ (posRight _ j)) = _
  rw [amalgamEnum_posRight]
  exact amalgamLabel_rightFun hta htb j

/-- **The scheme of the amalgam of two coatom stage types is the printed amalgam**
[Kni26, Definition 4.3.1]. -/
theorem printedAmalgam_amalgamType :
    PrintedAmalgam (comap_eq_of_restrictFace hta htb) (amalgamType hta htb).toCellScheme
      (amalgamType hta htb).rows (posLeft _) (posRight _) :=
  printedAmalgam_amalgam _

end StageType

/-! ### The rows of the amalgam, [Kni26, Lemma 4.3.2] -/

variable {h}

/-- The rows of the amalgam take their values among the values of the rows of `Sa` and `Sb`. -/
theorem atStage_amalgam_row {θ : Ordinal.{u}} (ha : ∀ s t, AtStage θ (Sa.rows.row s t))
    (hb : ∀ s t, AtStage θ (Sb.rows.row s t)) (s : Fin (amalgam h).card)
    (t : (amalgam h).toCellScheme.below ((amalgam h).toCellScheme.gradedIndex s)) :
    AtStage θ ((amalgam h).rows.row s t) := by
  have key (x : AmalgamCell h)
      (y : (amalgamCellScheme h).below ((amalgamCellScheme h).gradedIndex x)) :
      AtStage θ ((amalgamRows h).row x y) := by
    rcases x with i | ⟨j, hj⟩
    · exact ha i _
    · exact hb j _
  rw [amalgam_row]
  exact key _ _

/-- **The rows of the amalgam are a consistent semantics** [Kni26, Lemma 4.3.2], in the printed
form of [Kni26, Definition 2.5.12] (for every `⟨B, j⟩ ∈ P̂` and `Σ ∈ D_{B,j}`, `E(Σ)` respects the
semantics `E_{⟨B,j⟩}`; in particular `E(Σ)` is orderly, as a semantics requires,
[Kni26, Definition 2.5.3]): at a stage `θ` that is zero or a limit, if the rows of `Sa` and `Sb`
have values at stage `θ` and are consistent as printed, so are those of the amalgam. -/
theorem printedRespects_row_amalgam {θ : Ordinal.{u}} (hθ : Order.IsSuccPrelimit θ)
    (hSa : Sa.IsWellFormed) (hSb : Sb.IsWellFormed)
    (hf : univ.map (face m) ∈ Sa.toCellScheme.faces) (ha : ∀ s t, AtStage θ (Sa.rows.row s t))
    (hb : ∀ s t, AtStage θ (Sb.rows.row s t))
    (hca : ∀ s, Sa.toCellScheme.gradedIndex s ∈ Sa.toCellScheme.gradedFaces →
      (Sa.rows.comap (CellScheme.IsLowerEmbedding.subtypeVal_below Sa.toCellScheme
        (Sa.toCellScheme.gradedIndex s))).PrintedRespects θ (Sa.rows.row s))
    (hcb : ∀ s, Sb.toCellScheme.gradedIndex s ∈ Sb.toCellScheme.gradedFaces →
      (Sb.rows.comap (CellScheme.IsLowerEmbedding.subtypeVal_below Sb.toCellScheme
        (Sb.toCellScheme.gradedIndex s))).PrintedRespects θ (Sb.rows.row s))
    (s : Fin (amalgam h).card)
    (hs : (amalgam h).toCellScheme.gradedIndex s ∈ (amalgam h).toCellScheme.gradedFaces) :
    ((amalgam h).rows.comap (CellScheme.IsLowerEmbedding.subtypeVal_below
      (amalgam h).toCellScheme ((amalgam h).toCellScheme.gradedIndex s))).PrintedRespects θ
        ((amalgam h).rows.row s) :=
  (CellScheme.Rows.printedConsistent_iff hθ
      (isWellFormed_amalgam h hSa hSb hf).isWellFormed.gradedIndex_mem
      (atStage_amalgam_row ha hb)).mpr
    (isConsistent_amalgam h
      ((CellScheme.Rows.printedConsistent_iff hθ hSa.isWellFormed.gradedIndex_mem ha).mp hca)
      ((CellScheme.Rows.printedConsistent_iff hθ hSb.isWellFormed.gradedIndex_mem hb).mp hcb))
    s hs

/-- **The rows of the amalgam are bountiful as printed at every stage** [Kni26, Lemma 4.3.2], in
the form of row 6: if the rows of `Sa` and `Sb` are bountiful as printed
[Kni26, Definition 2.5.14] at every stage that is zero or a limit and carries their values, so are
the rows of the amalgam. -/
theorem forall_printedBountiful_amalgam (hSa : Sa.IsWellFormed) (hSb : Sb.IsWellFormed)
    (hf : univ.map (face m) ∈ Sa.toCellScheme.faces)
    (ha : ∀ θ : Ordinal.{u}, Order.IsSuccPrelimit θ → (∀ s t, AtStage θ (Sa.rows.row s t)) →
      Sa.rows.PrintedBountiful θ)
    (hb : ∀ θ : Ordinal.{u}, Order.IsSuccPrelimit θ → (∀ s t, AtStage θ (Sb.rows.row s t)) →
      Sb.rows.PrintedBountiful θ) :
    ∀ θ : Ordinal.{u}, Order.IsSuccPrelimit θ → (∀ s t, AtStage θ ((amalgam h).rows.row s t)) →
      (amalgam h).rows.PrintedBountiful θ :=
  (CellScheme.Rows.isBountiful_iff_forall_printedBountiful
      (isWellFormed_amalgam h hSa hSb hf).isWellFormed.gradedIndex_mem).mp
    (isBountiful_amalgam h hSa hSb hf
      ((CellScheme.Rows.isBountiful_iff_forall_printedBountiful
        hSa.isWellFormed.gradedIndex_mem).mpr ha)
      ((CellScheme.Rows.isBountiful_iff_forall_printedBountiful
        hSb.isWellFormed.gradedIndex_mem).mpr hb))

section StageType

variable {α : Ordinal.{u}} {ta tb : StageType.{u} α (m + 1)} {p : StageType.{u} α m}
  {hta : StageType.restrictFace (face m) ta = some p}
  {htb : StageType.restrictFace (face m) tb = some p}

/-- **The rows of the amalgam of two legal stage types are bountiful as printed at `ω₁`**
[Kni26, Lemma 4.3.2], from the bountifulness of `ta` and `tb` in the sense of `IsBountiful`. -/
theorem printedBountiful_omega_one_amalgamType (hla : ta.IsLegal) (hlb : tb.IsLegal) :
    (amalgamType hta htb).rows.PrintedBountiful (Ordinal.omega 1) :=
  (isBountiful_amalgamType hta htb hla hlb).printedBountiful_omega_one
    (amalgamType hta htb).isWellFormed.isWellFormed.gradedIndex_mem
    (amalgamType hta htb).isCoded.atStage_omega_one

end StageType

end Coatom

end VaughtConjecture
