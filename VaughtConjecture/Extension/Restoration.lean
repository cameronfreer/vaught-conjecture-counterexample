/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Gluing
import VaughtConjecture.Extension.SourcePrefix

/-!
# Restoration of lower prescriptions, and the one-grade lift

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.4 (the restoration of lower prescriptions, the prescribed
labels at the grades below the one being built; each lift preserves its cap on every coordinate);
Layer 1 (bountifulness, cap by cap); semantic contract, item 3 (capped observations need not be
lawful).

Everything here holds for arbitrary semantic rows `R` of a cell scheme `D`; no consistency,
bountifulness, or completeness is assumed unless it is a hypothesis.  The completion of the coatom
amalgam builds the cells of each grade `j + 1` after those of the grades `≤ j`, and must lift a
lawful prescription `p` below a pair `X = (C, j + 1)` to a lawful labelling below `Y = (B, j + 1)`,
`C ⊆ B`, keeping at a cap `c` the observation of a labelling `q` lawful below `Y` (the **ambient**
labelling of the lift).

**Caps, coordinate by coordinate.**  Agreement of two labels capped at `M` gives their agreement
capped at every `c ≤ M` (`Label.min_eq_min_of_le`).  Every lift below states its cap at every cell
below the target pair (the prescribed cells, the other old cells, and the new cells alike), not
only at the target cell.

**The splice** (`CellScheme.splice`).  For a grade `j` and labellings `q` (upper) and `v` (lower)
of the cells, `D.splice j q v` is `v` at the cells of grade at most `j` and `q` above.  If `q` is
lawful below `(B, J)`, `v` is lawful below `(B, j)`, the values of `q` above the grade `j` are at
most `M`, and `v` agrees with `q` capped at `M` below `(B, j)`, the splice is lawful below
`(B, J)` (`CellScheme.Rows.IsLawfulBelow.splice`) and agrees with `q` capped at `M` at every cell
below `(B, J)` (`CellScheme.min_splice_eq`).  Availability stays on one side of the splice, since
its witnesses have the grade of the requesting cell; no visibility of `M` is used.

**Restoration** (`CellScheme.Rows.exists_restoration`).  Let `X ≤ Y`, `j ≤ X.2`, and suppose
the rows lift capped from `(X.1, j)` to `(Y.1, j)` (the **lift at the lower grade**, which the
recursion on the grade supplies from the scheme reached after the grade `j`).  Let `p` be lawful
below `X`, `w` lawful below `Y` with `w = min p M` on the cells below `X` (an owner-capped lift,
below), `M` self-visible at the grade of `Y`, and `p` at most `M` at the cells of grade above `j`.
Then some `r` lawful below `Y` restores `p` literally on the cells below `X`, agrees with `w`
capped at `M` at every cell below `Y`, and is at most `M` above the grade `j`: cap `w` at `M`, lift
its lower part with the prescription below `(X.1, j)` by the lift at the lower grade, and splice.
The lower prescribed labels may exceed `M`, be pairwise distinct, be the formal top, and need not
be self-visible at the grade of `Y`.

**The lift below the cap** (`CellScheme.Rows.exists_lift_of_le_cap`): when the prescription is at
most the cap `c` above the grade `j`, the lift at the lower grade alone gives the capped lift from
`X` to `Y` (restoration with `w = min q c`).

**Owners, and the one-grade lift.**  An owner is a cell together with its row (roadmap, Layer 3,
3.1).  Below a graded face `X` at which some cell sits, on finitely many cells, a lawful
prescription has an **owner of the prescription** (`CellScheme.Rows.IsLawfulBelow.exists_owner`):
an owner of graded index `X` whose label is at least that of every prescribed cell of the grade of
`X`, by availability.  Its label is self-visible at that grade
(`CellScheme.Rows.IsLawfulBelow.isSelfVisible_of_gradedIndex_eq`), and its locality reads the
prescription capped at its label.  An **owner-capped lift** is a lawful labelling below `Y` that
reads the prescription capped at the owner label below `X` and keeps the ambient observation at
the cap at every cell below `Y`.  The **one-grade lift**
(`CellScheme.Rows.cappedLift_of_ownerCappedLift`): from the lift at the lower grade `j`, the lift
at the cap `⊥` (a lawful extension), and an owner-capped lift for every prescription whose owner
label exceeds a cap other than `⊥`, the rows lift capped from `(C, j + 1)` to `(B, j + 1)`.  At or
below the cap the lift is the lift below the cap.  The owner-capped lift itself depends on the
rows of the new cells; it is the subject of the owner alignment of the completion.

## Placement

Checkpoint 2.4 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

Lawful sections are [Kni26, Definition 2.5.4], with availability its second clause; bountifulness
is [Kni26, Definition 2.5.14]; capping is [Kni26, Lemma 2.5.8].
-/

universe u

namespace VaughtConjecture

open Label

/-! ### Caps, coordinate by coordinate -/

/-- **Agreement at a cap gives agreement at every smaller cap**, label by label: if `x` and `y`
agree capped at `M`, they agree capped at every `c ≤ M`.  It is used to pass from the cap of a
restoration to the cap of a lift, at every coordinate. -/
theorem Label.min_eq_min_of_le {x y M c : Label.{u}} (h : min x M = min y M) (hc : c ≤ M) :
    min x c = min y c := by
  simpa only [min_assoc, min_eq_right hc] using congrArg (fun z ↦ min z c) h

namespace CellScheme

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {X Y : Finset α × ℕ}
  {B : Finset α} {j J : ℕ}

/-! ### The splice -/

variable (D) in
/-- The **splice** at the grade `j` of an upper labelling `q` and a lower labelling `v` of the
cells: `v` at the cells of grade at most `j`, and `q` above. -/
def splice (j : ℕ) (q v : ι → Label.{u}) (d : ι) : Label.{u} :=
  if D.grade d ≤ j then v d else q d

/-- The splice is the lower labelling at the cells of grade at most `j`. -/
theorem splice_of_le {q v : ι → Label.{u}} {d : ι} (h : D.grade d ≤ j) :
    D.splice j q v d = v d :=
  ite_eq_left h

/-- The splice is the upper labelling at the cells of grade above `j`. -/
theorem splice_of_lt {q v : ι → Label.{u}} {d : ι} (h : j < D.grade d) :
    D.splice j q v d = q d :=
  ite_eq_right h.not_ge

/-- **The splice keeps the cap at every cell**: if the lower labelling agrees with the upper one
capped at `M` at the cells below `(B, j)`, the splice agrees with the upper labelling capped at
`M` at every cell whose scope lies in `B`. -/
theorem min_splice_eq {q v : ι → Label.{u}} {M : Label.{u}}
    (hag : ∀ d ∈ D.below (B, j), min (v d) M = min (q d) M) {d : ι} (hd : D.scope d ⊆ B) :
    min (D.splice j q v d) M = min (q d) M := by
  by_cases h : D.grade d ≤ j
  · rw [splice_of_le h]
    exact hag d ⟨hd, h⟩
  · rw [splice_of_lt (not_le.mp h)]

namespace Rows

/-- **The splice is lawful.**  Let `q` be lawful below `(B, J)` and `v` lawful below `(B, j)`.  If
the values of `q` at the cells of grade above `j` are at most `M` and `v` agrees with `q` capped
at `M` below `(B, j)`, the splice of `q` and `v` at `j` is lawful below `(B, J)`.  It places a
lower lift inside a lawful upper labelling without changing any upper locality, and is used to
restore the lower prescriptions of a lift in the one-grade step. -/
theorem IsLawfulBelow.splice {q v : ι → Label.{u}} {M : Label.{u}}
    (hq : R.IsLawfulBelow (B, J) fun d ↦ q d) (hv : R.IsLawfulBelow (B, j) fun d ↦ v d)
    (hbound : ∀ d ∈ D.below (B, J), j < D.grade d → q d ≤ M)
    (hag : ∀ d ∈ D.below (B, j), min (v d) M = min (q d) M) :
    R.IsLawfulBelow (B, J) fun d ↦ D.splice j q v d := by
  obtain ⟨hoq, hlq, haq⟩ := isLawfulBelow_iff_forall.mp hq
  obtain ⟨hov, hlv, hav⟩ := isLawfulBelow_iff_forall.mp hv
  refine isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · by_cases h : D.grade d ≤ j
    · rw [splice_of_le h]
      exact hov d ⟨hd.1, h⟩
    · rw [splice_of_lt (not_le.mp h)]
      exact hoq d hd
  · by_cases h : D.grade s ≤ j
    · -- Every cell below a low cell is low: the locality of `v`.
      have he : (fun d : D.below (D.gradedIndex s) ↦ min (D.splice j q v d) (D.splice j q v s)) =
          fun d : D.below (D.gradedIndex s) ↦ min (v d) (v s) := by
        funext d
        rw [splice_of_le h, splice_of_le ((d.2.2 : D.grade d.1 ≤ D.grade s).trans h)]
      rw [he]
      exact hlv s ⟨hs.1, h⟩
    · -- Above `j` the locality is that of `q`: below the label of `s`, which is at most `M`,
      -- the lower values read as the upper ones.
      have hsM : q s ≤ M := hbound s hs (not_le.mp h)
      have he : (fun d : D.below (D.gradedIndex s) ↦ min (D.splice j q v d) (D.splice j q v s)) =
          fun d : D.below (D.gradedIndex s) ↦ min (q d) (q s) := by
        funext d
        rw [splice_of_lt (not_le.mp h)]
        exact Label.min_eq_min_of_le (min_splice_eq hag ((d.2.1 : D.scope d.1 ⊆ D.scope s).trans
          hs.1)) hsM
      rw [he]
      exact hlq s hs
  · by_cases h : D.grade t ≤ j
    · have hsj : D.grade s ≤ j := hg ▸ h
      obtain ⟨w, hw, hle⟩ := hav s t ⟨ht.1, h⟩ hst hg
      have hwj : D.grade w ≤ j := (congrArg Prod.snd hw).le.trans h
      refine ⟨w, hw, ?_⟩
      rwa [splice_of_le hsj, splice_of_le hwj]
    · have hsj : j < D.grade s := hg ▸ not_le.mp h
      obtain ⟨w, hw, hle⟩ := haq s t ht hst hg
      have hwj : j < D.grade w := by
        rw [show D.grade w = D.grade t from congrArg Prod.snd hw]
        exact not_le.mp h
      refine ⟨w, hw, ?_⟩
      rwa [splice_of_lt hsj, splice_of_lt hwj]

/-! ### Restoration -/

/-- **Restoration of the lower prescriptions.**  Let `X ≤ Y` be pairs and `j` at most the grade of
`X`, and suppose the rows lift capped from `(X.1, j)` to `(Y.1, j)` (the lift at the lower
grade).  Let `p` be lawful below `X` (the prescription), `M` self-visible at the grade of `Y`, and
`w` lawful below `Y` reading `p` capped at `M` on the cells below `X` (an owner-capped lift), with
`p` at most `M` at the prescribed cells of grade above `j`.  Then some `r` lawful below `Y`

* reads `p` literally on the cells below `X`,
* agrees with `w` capped at `M` at every cell below `Y`, and
* is at most `M` at the cells of grade above `j`.

The prescribed labels of grade at most `j` may exceed `M`, be pairwise distinct, be the formal top,
and need not be self-visible at the grade of `Y`.  It is used in the one-grade step to restore the
prescribed labels at the grades below the one being built after an owner-capped lift. -/
theorem exists_restoration (hXY : X ≤ Y) (hj : j ≤ X.2)
    (hlift : R.CappedLift (X := (X.1, j)) (Y := (Y.1, j)) ⟨hXY.1, le_rfl⟩)
    {p : D.below X → Label.{u}} (hp : R.IsLawfulBelow X p)
    {w : D.below Y → Label.{u}} (hw : R.IsLawfulBelow Y w)
    {M : Label.{u}} (hM : IsSelfVisible Y.2 M)
    (hread : ∀ e, w (Set.inclusion (D.below_mono hXY) e) = min (p e) M)
    (hhigh : ∀ e : D.below X, j < D.grade e → p e ≤ M) :
    ∃ r : D.below Y → Label.{u}, R.IsLawfulBelow Y r ∧
      (∀ e, r (Set.inclusion (D.below_mono hXY) e) = p e) ∧
      (∀ d, min (r d) M = min (w d) M) ∧
      ∀ d : D.below Y, j < D.grade d → r d ≤ M := by
  classical
  have hjY : j ≤ Y.2 := hj.trans hXY.2
  -- Cap the owner-capped lift at `M`, and lift its lower part with the lower prescription.
  set v : D.below Y → Label.{u} := fun d ↦ min (w d) M with hv_def
  have hv : R.IsLawfulBelow Y v := hw.min_const_of_isSelfVisible hM
  have hXl : ((X.1, j) : Finset α × ℕ) ≤ X := ⟨subset_rfl, hj⟩
  have hYl : ((Y.1, j) : Finset α × ℕ) ≤ Y := ⟨subset_rfl, hjY⟩
  have hl : ((X.1, j) : Finset α × ℕ) ≤ (Y.1, j) := ⟨hXY.1, le_rfl⟩
  -- The lower prescription agrees with the capped lift at `M`.
  have hagree (d : D.below (X.1, j)) :
      min ((p ∘ Set.inclusion (D.below_mono hXl)) d) M =
        min ((v ∘ Set.inclusion (D.below_mono hYl)) (Set.inclusion (D.below_mono hl) d)) M := by
    have h := hread ⟨d.1, le_trans d.2 hXl⟩
    change min (p ⟨d.1, _⟩) M = min (min (w ⟨d.1, _⟩) M) M
    rw [h, min_assoc, min_self, min_assoc, min_self]
  obtain ⟨s, ⟨hs, hsM⟩, hsp⟩ := hlift M (hM.mono hjY) (v ∘ Set.inclusion (D.below_mono hYl))
    (hv.mono hYl) ⟨hp.mono hXl, hagree⟩
  -- Splice the lower lift into the capped lift.
  have hag (d : ι) (hd : d ∈ D.below (Y.1, j)) :
      min (Rows.extendBot (Y.1, j) s d) M = min (Rows.extendBot Y v d) M := by
    rw [extendBot_of_mem s hd, extendBot_of_mem v (le_trans hd hYl)]
    exact hsM ⟨d, hd⟩
  have hsplice := IsLawfulBelow.splice (R := R) (B := Y.1) (J := Y.2) (j := j) (M := M)
    (q := Rows.extendBot Y v) (v := Rows.extendBot (Y.1, j) s)
    (isLawfulBelow_extendBot.mpr hv) (isLawfulBelow_extendBot.mpr hs)
    (fun d hd _ ↦ by rw [extendBot_of_mem v hd]; exact min_le_right _ _) hag
  refine ⟨fun d ↦ D.splice j (Rows.extendBot Y v) (Rows.extendBot (Y.1, j) s) d, hsplice,
    fun e ↦ ?_, fun d ↦ ?_, fun d hd ↦ ?_⟩
  · change D.splice j (Rows.extendBot Y v) (Rows.extendBot (Y.1, j) s) e.1 = p e
    by_cases he : D.grade e.1 ≤ j
    · have heX : e.1 ∈ D.below (X.1, j) := ⟨e.2.1, he⟩
      rw [splice_of_le he, extendBot_of_mem s (le_trans heX hl)]
      exact congrFun hsp ⟨e.1, heX⟩
    · rw [splice_of_lt (not_le.mp he), extendBot_of_mem v (D.below_mono hXY e.2)]
      change min (w (Set.inclusion (D.below_mono hXY) e)) M = p e
      rw [hread e, min_assoc, min_self, min_eq_left (hhigh e (not_le.mp he))]
  · have h := min_splice_eq (D := D) (B := Y.1) (j := j) (M := M) hag d.2.1
    rw [extendBot_of_mem v d.2] at h
    exact h.trans (min_assoc _ _ _ |>.trans (by rw [min_self]))
  · change D.splice j (Rows.extendBot Y v) (Rows.extendBot (Y.1, j) s) d.1 ≤ M
    rw [splice_of_lt hd, extendBot_of_mem v d.2]
    exact min_le_right _ _

/-- **The lift below the cap.**  Let `X ≤ Y`, `j` at most the grade of `X`, and suppose the rows
lift capped from `(X.1, j)` to `(Y.1, j)`.  For a cap `c` self-visible at the grade of `Y`, a
prescription `p` lawful below `X` that is at most `c` at its cells of grade above `j`, and a lawful
`q` below `Y` with the same observation at `c` below `X`, some `r` lawful below `Y` reads `p`
literally below `X` and has the observation of `q` at `c` at every cell below `Y`.  It is the
one-grade lift when the owner label is at most the cap. -/
theorem exists_lift_of_le_cap (hXY : X ≤ Y) (hj : j ≤ X.2)
    (hlift : R.CappedLift (X := (X.1, j)) (Y := (Y.1, j)) ⟨hXY.1, le_rfl⟩)
    {p : D.below X → Label.{u}} (hp : R.IsLawfulBelow X p)
    {q : D.below Y → Label.{u}} (hq : R.IsLawfulBelow Y q)
    {c : Label.{u}} (hc : IsSelfVisible Y.2 c)
    (hag : ∀ e, min (q (Set.inclusion (D.below_mono hXY) e)) c = min (p e) c)
    (hhigh : ∀ e : D.below X, j < D.grade e → p e ≤ c) :
    ∃ r : D.below Y → Label.{u}, R.IsLawfulBelow Y r ∧
      (∀ d, min (r d) c = min (q d) c) ∧
      ∀ e, r (Set.inclusion (D.below_mono hXY) e) = p e := by
  obtain ⟨r, hr, hrp, hrc, -⟩ := exists_restoration hXY hj hlift hp
    (hq.min_const_of_isSelfVisible hc) hc (fun e ↦ (hag e).trans rfl) hhigh
  exact ⟨r, hr, fun d ↦ (hrc d).trans (by rw [min_assoc, min_self]), hrp⟩

/-! ### Owners, and the one-grade lift -/

/-- **The owner of a prescription.**  Below a graded face `X` at which some cell sits, on finitely
many cells, a lawful prescription `p` has an owner: a cell of graded index `X` whose label is at
least that of every prescribed cell of the grade of `X`.  It is a cell of graded index `X` of
largest label; availability bounds every prescribed label of that grade by the label of a cell of
graded index `X`.  It is used in the one-grade step to choose the cap of the restoration. -/
theorem IsLawfulBelow.exists_owner [Finite (D.below X)] {p : D.below X → Label.{u}}
    (hp : R.IsLawfulBelow X p) (hX : ∃ c, D.gradedIndex c = X) :
    ∃ o : D.below X, D.gradedIndex o = X ∧ ∀ e : D.below X, D.grade e = X.2 → p e ≤ p o := by
  classical
  have := Fintype.ofFinite (D.below X)
  obtain ⟨c, hc⟩ := hX
  set S : Finset (D.below X) := Finset.univ.filter fun o ↦ D.gradedIndex o = X
  have hcS : (⟨c, hc.le⟩ : D.below X) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  obtain ⟨o, hoS, ho⟩ := Finset.exists_max_image S p ⟨_, hcS⟩
  refine ⟨o, (Finset.mem_filter.mp hoS).2, fun e he ↦ ?_⟩
  obtain ⟨u, hu, hle⟩ := (isLawfulBelow_iff.mp hp).availability e ⟨c, hc.le⟩
    ((e.2.1 : D.scope e ⊆ X.1).trans (congrArg Prod.fst hc).ge)
    (he.trans (congrArg Prod.snd hc).symm)
  exact hle.trans (ho u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.trans hc⟩))

/-- The label of an owner is self-visible at the grade of the pair. -/
theorem IsLawfulBelow.isSelfVisible_of_gradedIndex_eq {p : D.below X → Label.{u}}
    (hp : R.IsLawfulBelow X p) {o : D.below X} (ho : D.gradedIndex o = X) :
    IsSelfVisible X.2 (p o) :=
  (congrArg Prod.snd ho) ▸ (isLawfulBelow_iff.mp hp).orderly o

/-- **The one-grade lift.**  Let `C ⊆ B`, with finitely many cells below `(C, j + 1)`, some cell of
graded index `(C, j + 1)`, and a capped lift of the rows from `(C, j)` to `(B, j)` (the lift at
the lower grade).  Suppose that

* every prescription `p` lawful below `(C, j + 1)` extends to a labelling lawful below `(B, j + 1)`
  that reads it literally (the lift at the cap `⊥`), and
* for every cap `c ≠ ⊥` self-visible at `j + 1`, every prescription `p` lawful below `(C, j + 1)`,
  every ambient `q` lawful below `(B, j + 1)` with the same observation at `c`, and every owner `o`
  of `p` whose label exceeds `c`, there is an owner-capped lift: a labelling lawful below
  `(B, j + 1)` reading `p` capped at the label of `o` below `(C, j + 1)` and with the observation
  of `q` at `c` at every cell below `(B, j + 1)`.

Then the rows lift capped from `(C, j + 1)` to `(B, j + 1)`.  An owner label at most the cap needs
no owner-capped lift (the lift below the cap); otherwise the owner-capped lift is restored at the
owner label.  It is the step of the recursion on the grade that proves the lifts to the pairs of
the grade being built, the three cases being the cap `⊥`, an owner label at most the cap, and an
owner label above a cap other than `⊥`. -/
theorem cappedLift_of_ownerCappedLift {C : Finset α} [Finite (D.below (C, j + 1))]
    (hCB : C ⊆ B) (hX : ∃ c, D.gradedIndex c = (C, j + 1))
    (hlift : R.CappedLift (X := (C, j)) (Y := (B, j)) ⟨hCB, le_rfl⟩)
    (hext : ∀ p : D.below (C, j + 1) → Label.{u}, R.IsLawfulBelow (C, j + 1) p →
      ∃ r : D.below (B, j + 1) → Label.{u}, R.IsLawfulBelow (B, j + 1) r ∧
        ∀ e, r (Set.inclusion (D.below_mono
          (show ((C, j + 1) : Finset α × ℕ) ≤ (B, j + 1) from ⟨hCB, le_rfl⟩)) e) = p e)
    (hown : ∀ c : Label.{u}, IsSelfVisible (j + 1) c → c ≠ ⊥ →
      ∀ (p : D.below (C, j + 1) → Label.{u}) (q : D.below (B, j + 1) → Label.{u}),
      R.IsLawfulBelow (C, j + 1) p → R.IsLawfulBelow (B, j + 1) q →
      (∀ e, min (q (Set.inclusion (D.below_mono
        (show ((C, j + 1) : Finset α × ℕ) ≤ (B, j + 1) from ⟨hCB, le_rfl⟩)) e)) c = min (p e) c) →
      ∀ o : D.below (C, j + 1), D.gradedIndex o = (C, j + 1) →
      (∀ e : D.below (C, j + 1), D.grade e = j + 1 → p e ≤ p o) → c < p o →
      ∃ w : D.below (B, j + 1) → Label.{u}, R.IsLawfulBelow (B, j + 1) w ∧
        (∀ e, w (Set.inclusion (D.below_mono
          (show ((C, j + 1) : Finset α × ℕ) ≤ (B, j + 1) from ⟨hCB, le_rfl⟩)) e) =
            min (p e) (p o)) ∧
        ∀ d, min (w d) c = min (q d) c) :
    R.CappedLift (X := (C, j + 1)) (Y := (B, j + 1)) ⟨hCB, le_rfl⟩ := by
  refine (cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hag ↦ ?_
  by_cases hcb : c = ⊥
  · -- The cap `⊥`: any lawful extension.
    obtain ⟨r, hr, hrp⟩ := hext p hp
    exact ⟨r, hr, fun d ↦ by simp only [hcb, min_bot_right], hrp⟩
  obtain ⟨o, ho, hop⟩ := hp.exists_owner hX
  -- A prescribed cell of grade above `j` below `(C, j + 1)` has the grade `j + 1`.
  have hgrade (e : D.below (C, j + 1)) (he : j < D.grade e) : D.grade e = j + 1 :=
    le_antisymm e.2.2 he
  rcases le_or_gt (p o) c with hoc | hoc
  · -- The lift below the cap.
    obtain ⟨r, hr, hrc, hrp⟩ := exists_lift_of_le_cap (X := (C, j + 1)) (Y := (B, j + 1))
      ⟨hCB, le_rfl⟩ (Nat.le_succ j) hlift hp hq hc hag
      fun e he ↦ (hop e (hgrade e he)).trans hoc
    exact ⟨r, hr, hrc, hrp⟩
  · -- The owner-capped lift, restored at the owner label.
    obtain ⟨w, hw, hwp, hwc⟩ := hown c hc hcb p q hp hq hag o ho hop hoc
    obtain ⟨r, hr, hrp, hrM, -⟩ := exists_restoration (X := (C, j + 1)) (Y := (B, j + 1))
      ⟨hCB, le_rfl⟩ (Nat.le_succ j) hlift hp hw (hp.isSelfVisible_of_gradedIndex_eq ho) hwp
      fun e he ↦ hop e (hgrade e he)
    exact ⟨r, hr, fun d ↦ (Label.min_eq_min_of_le (hrM d) hoc.le).trans (hwc d), hrp⟩

end Rows

end CellScheme

end VaughtConjecture
