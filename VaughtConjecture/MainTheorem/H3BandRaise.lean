/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.H3Band

/-!
# The direct raises of the band (work file for `h3`)

Work file (placement later).  The donor raise in the band (`CapRequests.DonorRaiseBandAt`) by a
direct raise of a labelling `W` of the donor coatom equal to `f` on the common face and agreeing
with `P` capped at `h`, at the cells through the new point where `W` is at least `h`.  Compiled in
this file (theorem named):

* **The direct raise** (`CapRequests.raiseThrough`, `CapRequests.isLawfulBelow_raiseThrough`,
  `CapRequests.RaisedCellRefines`, `CapRequests.donorRaiseBandAt_of_raisedCellRefines`,
  `CapRequests.capFillPosBandAt_of_raisedCellRefines`, `H3.capFillPosBandAt_of_raisedCellRefines`,
  `H3.exists_classCompletion_top_of_raisedCellRefines`): `⊤` at the cells through `xp` where a
  labelling `W` of the donor coatom (equal to `f` on the common face, agreeing with `P` capped at
  `h`) is at least `h`, `W` elsewhere.  Order and availability hold, and locality at the cells
  not raised; at a raised cell `s` locality is the named condition: the row of `s` reads the raise
  uncapped (`CapRequests.raiseThrough_le_of_refines`).  It forces `⊤` at every cell off `xp` read
  by `s` at least at `s` itself (`CapRequests.eq_top_of_raiseThrough_local`), and so **fails** at a
  donor cell labelled `⊤` through the new point reading a cell off it at least at itself
  (`H3.not_raisedCellRefines`: the labels capped at `ω + (k + 1)` are below `⊤` everywhere).  The
  raise to `⊤` collides with the values of `f` at least `M` on the common face; `P` fixes only the
  values below `h`.
* **The raise to the marker value** (`CapRequests.raiseTo`, `CapRequests.isLawfulBelow_raiseTo`,
  `CapRequests.RaisedCellRefinesTo`, `CapRequests.capFillPosBandAt_of_raisedCellRefinesTo`,
  `H3.capFillPosBandAt_of_raisedCellRefinesTo`,
  `H3.exists_classCompletion_top_of_raisedCellRefinesTo`): at the raised cells the larger of `W`
  and the least label at least `M` self-visible at the grade of the cell.  Order, availability
  and locality at the cells not raised hold; locality at a raised cell is the named condition.  A
  cell read by a raised cell `s` at least at `s` now needs only `W e ≥ max (W s) M_s`
  (`CapRequests.raiseTo_le_of_refinesTo`), not `⊤`, so the datum of `H3.not_raisedCellRefines`
  (common value `M`) passes this test.  The necessary content is collision-freeness
  (`CapRequests.le_of_raiseTo_local`): a cell off the raise read by `s` at least at a raised cell
  `e'` of larger grade carries at least `M_{e'}`.  Where `f` has no common value in `[h, c)`
  the raise is a uniform witness and the gap route already applies; where it has, locality at the
  raised cells needs a witness separating those values by the rows, which is not built here.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme ProfileTower

namespace CapRequests

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {xp xd : Fin (m + 2)}

/-! ### The direct raise -/

variable (xp) in
/-- **The direct raise** of a labelling `W` above the cap `h`: `⊤` at the cells through the point
`xp` where `W` is at least `h`, `W` elsewhere. -/
noncomputable def raiseThrough (h : Label.{u}) (W : Prof I) : Prof I := fun d ↦
  if xp ∈ I.amalgam.toCellScheme.scope d ∧ h ≤ W d then ⊤ else W d

theorem raiseThrough_of_raised {h : Label.{u}} {W : Prof I} {d : Fin I.amalgam.card}
    (hd : xp ∈ I.amalgam.toCellScheme.scope d ∧ h ≤ W d) : raiseThrough xp h W d = ⊤ :=
  ite_eq_left hd

theorem raiseThrough_of_not {h : Label.{u}} {W : Prof I} {d : Fin I.amalgam.card}
    (hd : ¬ (xp ∈ I.amalgam.toCellScheme.scope d ∧ h ≤ W d)) : raiseThrough xp h W d = W d :=
  ite_eq_right hd

theorem le_raiseThrough (h : Label.{u}) (W : Prof I) (d : Fin I.amalgam.card) :
    W d ≤ raiseThrough xp h W d := by
  by_cases hd : xp ∈ I.amalgam.toCellScheme.scope d ∧ h ≤ W d
  · rw [raiseThrough_of_raised hd]; exact le_top
  · rw [raiseThrough_of_not hd]

theorem min_raiseThrough (h : Label.{u}) (W : Prof I) (d : Fin I.amalgam.card) :
    min (raiseThrough xp h W d) h = min (W d) h := by
  by_cases hd : xp ∈ I.amalgam.toCellScheme.scope d ∧ h ≤ W d
  · rw [raiseThrough_of_raised hd, min_top_left, min_eq_right hd.2]
  · rw [raiseThrough_of_not hd]

/-- **The direct raise is lawful when it is local at the raised cells**: order holds (`⊤` is
self-visible); availability holds (a cell available for a raised cell is through `xp` and at least
`h`, so raised); locality at a cell not raised is locality of `W` (a raised cell below it is at
least `h`, above the value at the cell); at a raised cell it is the hypothesis. -/
theorem isLawfulBelow_raiseThrough {X : Finset (Fin (m + 2)) × ℕ} {h : Label.{u}} {W : Prof I}
    (hW : I.amalgam.rows.IsLawfulBelow X fun d ↦ W d)
    (hloc : ∀ s ∈ I.amalgam.toCellScheme.below X, xp ∈ I.amalgam.toCellScheme.scope s →
      h ≤ W s → TransformsTo (fun d : I.amalgam.toCellScheme.below
        (I.amalgam.toCellScheme.gradedIndex s) ↦ I.amalgam.toCellScheme.grade d)
        (I.amalgam.rows.row s) (fun d ↦ raiseThrough xp h W d)) :
    I.amalgam.rows.IsLawfulBelow X fun d ↦ raiseThrough xp h W d := by
  obtain ⟨ho, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hW
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · by_cases hr : xp ∈ I.amalgam.toCellScheme.scope d ∧ h ≤ W d
    · rw [raiseThrough_of_raised hr]; exact isSelfVisible_top _
    · rw [raiseThrough_of_not hr]; exact ho d hd
  · by_cases hr : xp ∈ I.amalgam.toCellScheme.scope s ∧ h ≤ W s
    · convert hloc s hs hr.1 hr.2 using 1
      funext d
      rw [raiseThrough_of_raised hr, min_top_right]
    · convert hl s hs using 1
      funext d
      rw [raiseThrough_of_not hr]
      by_cases hd : xp ∈ I.amalgam.toCellScheme.scope d.1 ∧ h ≤ W d.1
      · rw [raiseThrough_of_raised hd, min_top_left]
        have hds : I.amalgam.toCellScheme.scope d.1 ⊆ I.amalgam.toCellScheme.scope s :=
          ((I.amalgam.toCellScheme.gradedIndex_le_iff).mp d.2).1
        have hWs : W s < h := lt_of_not_ge fun h' ↦ hr ⟨hds hd.1, h'⟩
        exact (min_eq_right (hWs.le.trans hd.2)).symm
      · rw [raiseThrough_of_not hd]
  · obtain ⟨u, hu, hle⟩ := ha s t ht hst hg
    refine ⟨u, hu, ?_⟩
    by_cases hr : xp ∈ I.amalgam.toCellScheme.scope s ∧ h ≤ W s
    · have hsu : I.amalgam.toCellScheme.scope u = I.amalgam.toCellScheme.scope t :=
        congrArg Prod.fst hu
      rw [raiseThrough_of_raised hr, raiseThrough_of_raised ⟨hsu ▸ hst hr.1, hr.2.trans hle⟩]
    · rw [raiseThrough_of_not hr]
      exact hle.trans (le_raiseThrough h W u)

variable (r xp xd) in
/-- **The raised cells refine** (a named condition) at the grade `k`: for every datum of the band
some labelling `W` lawful below the donor coatom, equal to `f` on the common face and agreeing with
`P` capped at `h`, has its direct raise local at every raised cell `s` (through `xp`, `W s ≥ h`):
the raise below `s` is a transformation of the row of `s`.  Since the raise is `⊤` at `s`, this
asks the row of `s` to read the raise uncapped: `f` itself on the common face below `s`, and `⊤`
on the raised cells below `s`. -/
def RaisedCellRefines (k : ℕ) : Prop :=
  ∀ h : Label.{u}, IsSelfVisible k h → IsShort k h → ⊥ < h → ∀ P : Prof I,
    IsCutLawful I k P → r.IsCorrect (hat I k P) →
    ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) (fun d ↦ f d) →
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k), min (f d) h = min (P d) h) →
      h < f r.cap →
      ∃ W : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) (fun d ↦ W d) ∧
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k),
          d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k) → W d = f d) ∧
        (∀ d, min (W d) h = min (P d) h) ∧
        ∀ s ∈ I.amalgam.toCellScheme.below (univ.erase xd, k),
          xp ∈ I.amalgam.toCellScheme.scope s → h ≤ W s →
          TransformsTo (fun d : I.amalgam.toCellScheme.below
            (I.amalgam.toCellScheme.gradedIndex s) ↦ I.amalgam.toCellScheme.grade d)
            (I.amalgam.rows.row s) (fun d ↦ raiseThrough xp h W d)

/-- **The donor raise in the band from the refinement at the raised cells**: the direct raise is
lawful (`CapRequests.isLawfulBelow_raiseThrough`), `f` on the common face (no cell there is
through `xp`), agrees with `P` capped at `h`, and at a new top `y` it is `⊤` where `W y ≥ h`, and
`W y = P y`, at least the marker value (`CapRequests.markerValue_le_of_lt`), where `W y < h`. -/
theorem donorRaiseBandAt_of_raisedCellRefines (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    {k : ℕ} (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k)
    (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp)
    (hmarkC : I.amalgam.toCellScheme.scope r.marker ⊆ univ.erase xp)
    (hT : ∀ y ∈ r.T, ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp)
    (href : RaisedCellRefines r xp xd k) : DonorRaiseBandAt r xp xd k := by
  intro h hh hs hb P hP hPc f hf hfP hfc
  obtain ⟨W, hW, hWf, hWP, hloc⟩ := href h hh hs hb P hP hPc f hf hfP hfc
  refine ⟨raiseThrough xp h W, isLawfulBelow_raiseThrough hW hloc, fun d hdC hdD ↦ ?_,
    fun d ↦ by rw [min_raiseThrough, hWP], fun y hy ↦ ?_⟩
  · have hnot : ¬ (xp ∈ I.amalgam.toCellScheme.scope d ∧ h ≤ W d) := fun h' ↦
      (mem_erase.mp (hdC.1 h'.1)).1 rfl
    rw [raiseThrough_of_not hnot]
    exact hWf d hdC hdD
  · have hyx : xp ∈ I.amalgam.toCellScheme.scope y := by
      by_contra hn
      exact hT y hy fun z hz ↦ mem_erase.mpr ⟨fun h' ↦ hn (h' ▸ hz), mem_univ _⟩
    by_cases hWy : h ≤ W y
    · rw [raiseThrough_of_raised ⟨hyx, hWy⟩]; exact le_top
    · have hlt : W y < h := not_le.mp hWy
      have hPy : P y = W y := eq_of_min_eq_of_lt_cap (hWP y).symm hlt
      rw [raiseThrough_of_not fun h' ↦ hWy h'.2]
      have hmg : I.amalgam.toCellScheme.grade r.marker ≤ k := hgr.grade_marker_le.trans hNk
      have hM := markerValue_le_of_lt hgr hNk (hh.mono (hgr.le_grade_cap.trans hNk)) hPc
        (hfP _ ⟨hmarkC, hmg⟩) (hfP _ ⟨hcapC, hNk⟩) hfc hy (hPy ▸ hlt)
      rwa [hPy] at hM

/-- **The band from the refinement at the raised cells**
(`CapRequests.donorRaiseBandAt_of_raisedCellRefines`,
`CapRequests.capFillPosBandAt_of_donorRaiseBandAt`). -/
theorem capFillPosBandAt_of_raisedCellRefines (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hxd : xd ∈ (Pts : Finset (Fin (m + 2))))
    (hne : xd ≠ xp) {k : ℕ} (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k)
    (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp)
    (hmarkC : I.amalgam.toCellScheme.scope r.marker ⊆ univ.erase xp)
    (hT : ∀ y ∈ r.T, ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp)
    (hZ : r.Z = ∅) (hF : r.F = ∅) (href : RaisedCellRefines r xp xd k) :
    CapFillPosBandAt r xp k :=
  capFillPosBandAt_of_donorRaiseBandAt hgr hxp hxd hne hNk hcapC hmarkC hT hZ hF
    (donorRaiseBandAt_of_raisedCellRefines hgr hNk hcapC hmarkC hT href)

/-- **What the refinement at a raised cell asks** (necessary): if the direct raise of `W` is local
at a raised cell `s`, then for cells `e`, `e'` below `s` with `grade e' ≤ grade e` and the row of
`s` at `e` at most that at `e'`, the raise at `e` is at most that at `e'`.  In particular (i) on
the common face below `s` the row of `s` refines `W` (that is `f`) **uncapped**, and (ii) a cell of
the common face read by `s` at least at a raised cell of larger grade is `⊤` under `W`. -/
theorem raiseThrough_le_of_refines {s : Fin I.amalgam.card} {h : Label.{u}} {W : Prof I}
    (hloc : TransformsTo (fun d : I.amalgam.toCellScheme.below
        (I.amalgam.toCellScheme.gradedIndex s) ↦ I.amalgam.toCellScheme.grade d)
        (I.amalgam.rows.row s) (fun d ↦ raiseThrough xp h W d))
    {e e' : I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s)}
    (hrow : I.amalgam.rows.row s e ≤ I.amalgam.rows.row s e')
    (hg : I.amalgam.toCellScheme.grade e'.1 ≤ I.amalgam.toCellScheme.grade e.1) :
    raiseThrough xp h W e ≤ raiseThrough xp h W e' :=
  hloc.le_of_le hrow hg

/-- **The refinement at a raised cell forces `⊤` on the cells off `xp` read by it at least at
itself**: if the direct raise is local at a raised cell `s`, every cell `e` below `s` not through
`xp` whose row value at `s` is at least that of `s` itself carries `⊤` under `W` (on the common
face, `f e = ⊤`).  By locality of `W` at `s` such a cell carries at least `W s ≥ h`; the
condition asks more, `⊤`, for every prescription. -/
theorem eq_top_of_raiseThrough_local {s : Fin I.amalgam.card} {h : Label.{u}} {W : Prof I}
    (hs : xp ∈ I.amalgam.toCellScheme.scope s ∧ h ≤ W s)
    (hloc : TransformsTo (fun d : I.amalgam.toCellScheme.below
        (I.amalgam.toCellScheme.gradedIndex s) ↦ I.amalgam.toCellScheme.grade d)
        (I.amalgam.rows.row s) (fun d ↦ raiseThrough xp h W d))
    {e : Fin I.amalgam.card}
    (he : e ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s))
    (hxe : xp ∉ I.amalgam.toCellScheme.scope e)
    (hrow : I.amalgam.rows.row s ⟨s, I.amalgam.toCellScheme.mem_below_gradedIndex s⟩ ≤
      I.amalgam.rows.row s ⟨e, he⟩) :
    W e = ⊤ := by
  have h1 := raiseThrough_le_of_refines hloc hrow he.2
  change raiseThrough xp h W s ≤ raiseThrough xp h W e at h1
  rw [raiseThrough_of_raised hs, raiseThrough_of_not fun h' ↦ hxe h'.1] at h1
  exact top_le_iff.mp h1

/-! ### The raise to the marker value -/

variable (xp) in
/-- **The raise to `M`** of a labelling `W` above the cap `h`: at the cells through the point `xp`
where `W` is at least `h`, the larger of `W` and the least label at least `M` self-visible at the
grade of the cell (`visibilityReplace j j M` at the grade `j`); `W` elsewhere. -/
noncomputable def raiseTo (h M : Label.{u}) (W : Prof I) : Prof I := fun d ↦
  if xp ∈ I.amalgam.toCellScheme.scope d ∧ h ≤ W d then
    max (W d) (visibilityReplace (I.amalgam.toCellScheme.grade d)
      (I.amalgam.toCellScheme.grade d) M)
  else W d

theorem raiseTo_of_raised {h M : Label.{u}} {W : Prof I} {d : Fin I.amalgam.card}
    (hd : xp ∈ I.amalgam.toCellScheme.scope d ∧ h ≤ W d) :
    raiseTo xp h M W d = max (W d) (visibilityReplace (I.amalgam.toCellScheme.grade d)
      (I.amalgam.toCellScheme.grade d) M) :=
  ite_eq_left hd

theorem raiseTo_of_not {h M : Label.{u}} {W : Prof I} {d : Fin I.amalgam.card}
    (hd : ¬ (xp ∈ I.amalgam.toCellScheme.scope d ∧ h ≤ W d)) : raiseTo xp h M W d = W d :=
  ite_eq_right hd

theorem le_raiseTo (h M : Label.{u}) (W : Prof I) (d : Fin I.amalgam.card) :
    W d ≤ raiseTo xp h M W d := by
  by_cases hd : xp ∈ I.amalgam.toCellScheme.scope d ∧ h ≤ W d
  · rw [raiseTo_of_raised hd]; exact le_max_left _ _
  · rw [raiseTo_of_not hd]

theorem min_raiseTo (h M : Label.{u}) (W : Prof I) (d : Fin I.amalgam.card) :
    min (raiseTo xp h M W d) h = min (W d) h := by
  by_cases hd : xp ∈ I.amalgam.toCellScheme.scope d ∧ h ≤ W d
  · rw [raiseTo_of_raised hd, min_eq_right (hd.2.trans (le_max_left _ _)), min_eq_right hd.2]
  · rw [raiseTo_of_not hd]

/-- At a raised cell the raise to `M` is at least `M`. -/
theorem le_raiseTo_of_raised {h M : Label.{u}} {W : Prof I} {d : Fin I.amalgam.card}
    (hd : xp ∈ I.amalgam.toCellScheme.scope d ∧ h ≤ W d) : M ≤ raiseTo xp h M W d := by
  rw [raiseTo_of_raised hd]
  exact (le_visibilityReplace (by omega) M).trans (le_max_right _ _)

/-- **The raise to `M` is lawful when it is local at the raised cells**: order (the maximum of two
labels self-visible at the grade of the cell), availability (a cell available for a raised cell
has its grade and is raised, and the raise is monotone in `W` at a fixed grade), and locality at
the cells not raised (a raised cell below one not raised is above its value), as for
`CapRequests.isLawfulBelow_raiseThrough`; at a raised cell locality is the hypothesis. -/
theorem isLawfulBelow_raiseTo {X : Finset (Fin (m + 2)) × ℕ} {h M : Label.{u}} {W : Prof I}
    (hW : I.amalgam.rows.IsLawfulBelow X fun d ↦ W d)
    (hloc : ∀ s ∈ I.amalgam.toCellScheme.below X, xp ∈ I.amalgam.toCellScheme.scope s →
      h ≤ W s → TransformsTo (fun d : I.amalgam.toCellScheme.below
        (I.amalgam.toCellScheme.gradedIndex s) ↦ I.amalgam.toCellScheme.grade d)
        (I.amalgam.rows.row s)
        (fun d ↦ min (raiseTo xp h M W d) (raiseTo xp h M W s))) :
    I.amalgam.rows.IsLawfulBelow X fun d ↦ raiseTo xp h M W d := by
  obtain ⟨ho, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hW
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · by_cases hr : xp ∈ I.amalgam.toCellScheme.scope d ∧ h ≤ W d
    · rw [raiseTo_of_raised hr]
      exact (ho d hd).max (isSelfVisible_visibilityReplace_self _ _)
    · rw [raiseTo_of_not hr]; exact ho d hd
  · by_cases hr : xp ∈ I.amalgam.toCellScheme.scope s ∧ h ≤ W s
    · exact hloc s hs hr.1 hr.2
    · convert hl s hs using 1
      funext d
      rw [raiseTo_of_not hr]
      by_cases hd : xp ∈ I.amalgam.toCellScheme.scope d.1 ∧ h ≤ W d.1
      · have hds : I.amalgam.toCellScheme.scope d.1 ⊆ I.amalgam.toCellScheme.scope s :=
          ((I.amalgam.toCellScheme.gradedIndex_le_iff).mp d.2).1
        have hWs : W s < h := lt_of_not_ge fun h' ↦ hr ⟨hds hd.1, h'⟩
        rw [min_eq_right (hWs.le.trans (hd.2.trans (le_raiseTo h M W d.1))),
          min_eq_right (hWs.le.trans hd.2)]
      · rw [raiseTo_of_not hd]
  · obtain ⟨u, hu, hle⟩ := ha s t ht hst hg
    refine ⟨u, hu, ?_⟩
    by_cases hr : xp ∈ I.amalgam.toCellScheme.scope s ∧ h ≤ W s
    · have hsu : I.amalgam.toCellScheme.scope u = I.amalgam.toCellScheme.scope t :=
        congrArg Prod.fst hu
      have hgu : I.amalgam.toCellScheme.grade u = I.amalgam.toCellScheme.grade s :=
        (congrArg Prod.snd hu).trans hg.symm
      rw [raiseTo_of_raised hr, raiseTo_of_raised ⟨hsu ▸ hst hr.1, hr.2.trans hle⟩, hgu]
      exact max_le_max hle le_rfl
    · rw [raiseTo_of_not hr]
      exact hle.trans (le_raiseTo h M W u)

variable (r xp xd) in
/-- **The raised cells refine to the marker value** (a named condition) at the grade `k`: for every
datum of the band, some labelling `W` lawful below the donor coatom, equal to `f` on the common
face and agreeing with `P` capped at `h`, has its raise to the marker value `M` of `f`
(`CapRequests.raiseTo`) local at every raised cell `s`: the raise below `s`, capped at its value
at `s`, is a transformation of the row of `s`. -/
def RaisedCellRefinesTo (k : ℕ) : Prop :=
  ∀ h : Label.{u}, IsSelfVisible k h → IsShort k h → ⊥ < h → ∀ P : Prof I,
    IsCutLawful I k P → r.IsCorrect (hat I k P) →
    ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) (fun d ↦ f d) →
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k), min (f d) h = min (P d) h) →
      h < f r.cap →
      ∃ W : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) (fun d ↦ W d) ∧
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k),
          d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k) → W d = f d) ∧
        (∀ d, min (W d) h = min (P d) h) ∧
        ∀ s ∈ I.amalgam.toCellScheme.below (univ.erase xd, k),
          xp ∈ I.amalgam.toCellScheme.scope s → h ≤ W s →
          TransformsTo (fun d : I.amalgam.toCellScheme.below
            (I.amalgam.toCellScheme.gradedIndex s) ↦ I.amalgam.toCellScheme.grade d)
            (I.amalgam.rows.row s)
            (fun d ↦ min (raiseTo xp h (r.markerValue f) W d)
              (raiseTo xp h (r.markerValue f) W s))

/-- **The donor raise in the band from the refinement to the marker value**: the raise to `M` is
lawful (`CapRequests.isLawfulBelow_raiseTo`), `f` on the common face, agrees with `P` capped at
`h`, and at a new top it is at least `M`, raised where `W ≥ h` and `P`, at least `M`
(`CapRequests.markerValue_le_of_lt`), where `W < h`. -/
theorem donorRaiseBandAt_of_raisedCellRefinesTo (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    {k : ℕ} (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k)
    (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp)
    (hmarkC : I.amalgam.toCellScheme.scope r.marker ⊆ univ.erase xp)
    (hT : ∀ y ∈ r.T, ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp)
    (href : RaisedCellRefinesTo r xp xd k) : DonorRaiseBandAt r xp xd k := by
  intro h hh hs hb P hP hPc f hf hfP hfc
  obtain ⟨W, hW, hWf, hWP, hloc⟩ := href h hh hs hb P hP hPc f hf hfP hfc
  refine ⟨raiseTo xp h (r.markerValue f) W, isLawfulBelow_raiseTo hW hloc, fun d hdC hdD ↦ ?_,
    fun d ↦ by rw [min_raiseTo, hWP], fun y hy ↦ ?_⟩
  · have hnot : ¬ (xp ∈ I.amalgam.toCellScheme.scope d ∧ h ≤ W d) := fun h' ↦
      (mem_erase.mp (hdC.1 h'.1)).1 rfl
    rw [raiseTo_of_not hnot]
    exact hWf d hdC hdD
  · have hyx : xp ∈ I.amalgam.toCellScheme.scope y := by
      by_contra hn
      exact hT y hy fun z hz ↦ mem_erase.mpr ⟨fun h' ↦ hn (h' ▸ hz), mem_univ _⟩
    by_cases hWy : h ≤ W y
    · exact le_raiseTo_of_raised ⟨hyx, hWy⟩
    · have hlt : W y < h := not_le.mp hWy
      have hPy : P y = W y := eq_of_min_eq_of_lt_cap (hWP y).symm hlt
      rw [raiseTo_of_not fun h' ↦ hWy h'.2]
      have hmg : I.amalgam.toCellScheme.grade r.marker ≤ k := hgr.grade_marker_le.trans hNk
      have hM := markerValue_le_of_lt hgr hNk (hh.mono (hgr.le_grade_cap.trans hNk)) hPc
        (hfP _ ⟨hmarkC, hmg⟩) (hfP _ ⟨hcapC, hNk⟩) hfc hy (hPy ▸ hlt)
      rwa [hPy] at hM

/-- **The band from the refinement to the marker value**
(`CapRequests.donorRaiseBandAt_of_raisedCellRefinesTo`,
`CapRequests.capFillPosBandAt_of_donorRaiseBandAt`). -/
theorem capFillPosBandAt_of_raisedCellRefinesTo (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hxd : xd ∈ (Pts : Finset (Fin (m + 2))))
    (hne : xd ≠ xp) {k : ℕ} (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k)
    (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp)
    (hmarkC : I.amalgam.toCellScheme.scope r.marker ⊆ univ.erase xp)
    (hT : ∀ y ∈ r.T, ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp)
    (hZ : r.Z = ∅) (hF : r.F = ∅) (href : RaisedCellRefinesTo r xp xd k) :
    CapFillPosBandAt r xp k :=
  capFillPosBandAt_of_donorRaiseBandAt hgr hxp hxd hne hNk hcapC hmarkC hT hZ hF
    (donorRaiseBandAt_of_raisedCellRefinesTo hgr hNk hcapC hmarkC hT href)

/-- **The refinement to the marker value at a raised cell bounds the cells read at least at it**:
if the raise to `M` is local at a raised cell `s`, every cell `e` below `s` whose row value at `s`
is at least that of `s` itself carries at least the raise at `s` (by locality of the raise
capped at its value at `s`).  Off `xp` this asks `W e ≥ max (W s) M_s`, `M_s` the least label at
least `M` self-visible at the grade of `s`; it no longer asks `⊤`. -/
theorem raiseTo_le_of_refinesTo {s : Fin I.amalgam.card} {h M : Label.{u}} {W : Prof I}
    (hloc : TransformsTo (fun d : I.amalgam.toCellScheme.below
        (I.amalgam.toCellScheme.gradedIndex s) ↦ I.amalgam.toCellScheme.grade d)
        (I.amalgam.rows.row s) (fun d ↦ min (raiseTo xp h M W d) (raiseTo xp h M W s)))
    {e : Fin I.amalgam.card}
    (he : e ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s))
    (hrow : I.amalgam.rows.row s ⟨s, I.amalgam.toCellScheme.mem_below_gradedIndex s⟩ ≤
      I.amalgam.rows.row s ⟨e, he⟩) :
    raiseTo xp h M W s ≤ raiseTo xp h M W e := by
  have h1 := hloc.le_of_le hrow he.2
  change min (raiseTo xp h M W s) (raiseTo xp h M W s) ≤
    min (raiseTo xp h M W e) (raiseTo xp h M W s) at h1
  rw [min_self] at h1
  exact h1.trans (min_le_left _ _)

/-- **The collision condition is necessary for the raise to `M`**: if the raise to `M` is local
at a raised cell `s`, a cell `e` below `s` not raised, read by `s` at least at a raised cell `e'`
of grade at least that of `e`, carries `W e ≥ M_{e'}`, the least label at least `M` self-visible at
the grade of `e'` (in particular `W e ≥ M`).  On the common face, `W e = f e`: a value of `f` in
`[h, M)` there must not be read by a raised cell at least at another raised cell. -/
theorem le_of_raiseTo_local {s : Fin I.amalgam.card} {h M : Label.{u}} {W : Prof I}
    (hs : xp ∈ I.amalgam.toCellScheme.scope s ∧ h ≤ W s)
    (hloc : TransformsTo (fun d : I.amalgam.toCellScheme.below
        (I.amalgam.toCellScheme.gradedIndex s) ↦ I.amalgam.toCellScheme.grade d)
        (I.amalgam.rows.row s) (fun d ↦ min (raiseTo xp h M W d) (raiseTo xp h M W s)))
    {e e' : I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s)}
    (he : ¬ (xp ∈ I.amalgam.toCellScheme.scope e.1 ∧ h ≤ W e.1))
    (he' : xp ∈ I.amalgam.toCellScheme.scope e'.1 ∧ h ≤ W e'.1)
    (hrow : I.amalgam.rows.row s e' ≤ I.amalgam.rows.row s e)
    (hg : I.amalgam.toCellScheme.grade e.1 ≤ I.amalgam.toCellScheme.grade e'.1) :
    visibilityReplace (I.amalgam.toCellScheme.grade e'.1) (I.amalgam.toCellScheme.grade e'.1) M ≤
      W e.1 := by
  have h1 := hloc.le_of_le hrow hg
  change min (raiseTo xp h M W e'.1) (raiseTo xp h M W s) ≤
    min (raiseTo xp h M W e.1) (raiseTo xp h M W s) at h1
  rw [raiseTo_of_not he] at h1
  have hge : I.amalgam.toCellScheme.grade e'.1 ≤ I.amalgam.toCellScheme.grade s := e'.2.2
  have hM : visibilityReplace (I.amalgam.toCellScheme.grade e'.1)
      (I.amalgam.toCellScheme.grade e'.1) M ≤ raiseTo xp h M W s := by
    rw [raiseTo_of_raised hs]
    refine le_trans ?_ (le_max_right _ _)
    exact (monotone_visibilityReplace le_rfl (le_visibilityReplace (by omega) M)).trans_eq
      (((isSelfVisible_visibilityReplace_self _ M).mono hge).visibilityReplace_eq _)
  have h2 : visibilityReplace (I.amalgam.toCellScheme.grade e'.1)
      (I.amalgam.toCellScheme.grade e'.1) M ≤
      min (raiseTo xp h M W e'.1) (raiseTo xp h M W s) := by
    rw [raiseTo_of_raised he']
    exact le_min (le_max_right _ _) hM
  exact (h2.trans h1).trans (min_le_left _ _)

end CapRequests

namespace H3

open StageType

variable {α : Ordinal.{u}} {n k : ℕ}

section Band

variable {t' : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {tb : StageType.{u} α (k + 1)}
  (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces)
  {g : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)}

/-- **The band at an acquired context from the refinement at the raised cells**
(`CapRequests.capFillPosBandAt_of_raisedCellRefines`), at every cut grade from the cap. -/
theorem capFillPosBandAt_of_raisedCellRefines (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r) {k' : ℕ}
    (hk' : t'.toCellScheme.grade c ≤ k')
    (href : CapRequests.RaisedCellRefines
      (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)) (Fin.last (k + 1))
      (Fin.castSucc (Fin.last k)) k') :
    CapRequests.CapFillPosBandAt (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega))
      (Fin.last (k + 1)) k' := by
  have hrc : t'.toCellScheme.grade r ≤ t'.toCellScheme.grade c := by
    have h := hctx.2.1.2.1
    rw [CellScheme.mem_below] at h
    exact (Prod.le_def.mp h).2
  have hn := hctx.2.2.1
  have hgr := isGraded_requests ht' hp htb hd (r := r) (by omega) hrc hn
  have hL := restrictFace_left_seed ht' hp htb
  have hA := restrictFace_donor_seed ht' hp htb hd
  have hcapC : (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL c) =
      univ.erase (Fin.last (k + 1)) := by
    rw [scope_faceCell, hctx.1.1]
    exact Coatom.univ_map_left
  have hmarkC : (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL r) ⊆
      univ.erase (Fin.last (k + 1)) := by
    rw [scope_faceCell, ← Coatom.univ_map_left]
    exact map_subset_map.mpr (subset_univ _)
  have hTC (y) (hy : y ∈ (requests ht' hp htb hd c r (by omega)).T) :
      ¬ (seed ht' hp htb).amalgam.toCellScheme.scope y ⊆ univ.erase (Fin.last (k + 1)) := by
    obtain ⟨j, -, hjl, rfl⟩ := hy
    intro hsub
    have hmem : Fin.last (k + 1) ∈
        (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hA j) := by
      rw [scope_faceCell]
      exact mem_map.mpr ⟨Fin.last n, hjl, by simp⟩
    simpa using hsub hmem
  have hNk : (seed ht' hp htb).amalgam.toCellScheme.grade
      (requests ht' hp htb hd c r (by omega)).cap ≤ k' := (grade_faceCell hL c).trans_le hk'
  exact CapRequests.capFillPosBandAt_of_raisedCellRefines hgr (by simp) (by simp)
    Seed.last_ne_castSucc.symm hNk hcapC.le hmarkC hTC rfl rfl href

/-- **The completion with rows admitted in the class at a cap of the top grade from the donor
raise and the refinement at the raised cells** (as `H3.exists_classCompletion_top_of_gap`, with
the band from `H3.capFillPosBandAt_of_raisedCellRefines` in place of the gap). -/
theorem exists_classCompletion_top_of_raisedCellRefines
    (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hkN : k < t'.toCellScheme.grade c)
    (hraise : ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
      CapRequests.DonorRaiseBotAtIn (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega))
        (classCells ht' hp htb hd) (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k')
    (href : CapRequests.RaisedCellRefines
      (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)) (Fin.last (k + 1))
      (Fin.castSucc (Fin.last k)) (k + 1)) :
    ∃ F : CompletionBelowFullGrade (seed ht' hp htb),
      F.HasAdmittedRows (t'.toCellScheme.grade c)
        ((requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)).Admits
          (classCells ht' hp htb hd) ∅) := by
  have hn := hctx.2.2.1
  have hck : t'.toCellScheme.grade c ≤ k + 1 := t'.grade_le c
  refine exists_classCompletion_of_fills₀ ht' hp htb hd hctx
    (donorLiftProvisions_of_lt ht' hp htb hd hctx hkN) hraise fun k' hk' hkm ↦ ?_
  obtain rfl : k' = k + 1 := by omega
  exact capFillPosBandAt_of_raisedCellRefines ht' hp htb hd hctx hk' href

/-- **The band at an acquired context from the refinement to the marker value**
(`CapRequests.capFillPosBandAt_of_raisedCellRefinesTo`), at every cut grade from the cap. -/
theorem capFillPosBandAt_of_raisedCellRefinesTo (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r) {k' : ℕ}
    (hk' : t'.toCellScheme.grade c ≤ k')
    (href : CapRequests.RaisedCellRefinesTo
      (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)) (Fin.last (k + 1))
      (Fin.castSucc (Fin.last k)) k') :
    CapRequests.CapFillPosBandAt (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega))
      (Fin.last (k + 1)) k' := by
  have hrc : t'.toCellScheme.grade r ≤ t'.toCellScheme.grade c := by
    have h := hctx.2.1.2.1
    rw [CellScheme.mem_below] at h
    exact (Prod.le_def.mp h).2
  have hn := hctx.2.2.1
  have hgr := isGraded_requests ht' hp htb hd (r := r) (by omega) hrc hn
  have hL := restrictFace_left_seed ht' hp htb
  have hA := restrictFace_donor_seed ht' hp htb hd
  have hcapC : (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL c) =
      univ.erase (Fin.last (k + 1)) := by
    rw [scope_faceCell, hctx.1.1]
    exact Coatom.univ_map_left
  have hmarkC : (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL r) ⊆
      univ.erase (Fin.last (k + 1)) := by
    rw [scope_faceCell, ← Coatom.univ_map_left]
    exact map_subset_map.mpr (subset_univ _)
  have hTC (y) (hy : y ∈ (requests ht' hp htb hd c r (by omega)).T) :
      ¬ (seed ht' hp htb).amalgam.toCellScheme.scope y ⊆ univ.erase (Fin.last (k + 1)) := by
    obtain ⟨j, -, hjl, rfl⟩ := hy
    intro hsub
    have hmem : Fin.last (k + 1) ∈
        (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hA j) := by
      rw [scope_faceCell]
      exact mem_map.mpr ⟨Fin.last n, hjl, by simp⟩
    simpa using hsub hmem
  have hNk : (seed ht' hp htb).amalgam.toCellScheme.grade
      (requests ht' hp htb hd c r (by omega)).cap ≤ k' := (grade_faceCell hL c).trans_le hk'
  exact CapRequests.capFillPosBandAt_of_raisedCellRefinesTo hgr (by simp) (by simp)
    Seed.last_ne_castSucc.symm hNk hcapC.le hmarkC hTC rfl rfl href

/-- **The completion with rows admitted in the class at a cap of the top grade from the donor
raise and the refinement to the marker value** (as `H3.exists_classCompletion_top_of_gap`, with
the band from `H3.capFillPosBandAt_of_raisedCellRefinesTo` in place of the gap). -/
theorem exists_classCompletion_top_of_raisedCellRefinesTo
    (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hkN : k < t'.toCellScheme.grade c)
    (hraise : ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
      CapRequests.DonorRaiseBotAtIn (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega))
        (classCells ht' hp htb hd) (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k')
    (href : CapRequests.RaisedCellRefinesTo
      (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)) (Fin.last (k + 1))
      (Fin.castSucc (Fin.last k)) (k + 1)) :
    ∃ F : CompletionBelowFullGrade (seed ht' hp htb),
      F.HasAdmittedRows (t'.toCellScheme.grade c)
        ((requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)).Admits
          (classCells ht' hp htb hd) ∅) := by
  have hn := hctx.2.2.1
  have hck : t'.toCellScheme.grade c ≤ k + 1 := t'.grade_le c
  refine exists_classCompletion_of_fills₀ ht' hp htb hd hctx
    (donorLiftProvisions_of_lt ht' hp htb hd hctx hkN) hraise fun k' hk' hkm ↦ ?_
  obtain rfl : k' = k + 1 := by omega
  exact capFillPosBandAt_of_raisedCellRefinesTo ht' hp htb hd hctx hk' href

/-- **The refinement at the raised cells fails at a donor cell labelled `⊤` reading a cell off the
new point at least at itself.**  Take the cap `h = k + 1`, `P` the labels of the amalgam, and `f`
the labels capped at `ω + (k + 1)` (lawful, below `⊤` everywhere, above `h` at the cap).  The
cell `s` through the new point, labelled `⊤`, is raised under every admissible `W`, and the
refinement there forces `W e = ⊤` at the cell `e` (`CapRequests.eq_top_of_raiseThrough_local`),
while `W e = f e < ⊤`. -/
theorem not_raisedCellRefines (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    {s e : Fin (seed ht' hp htb).amalgam.card}
    (hsD : s ∈ (seed ht' hp htb).amalgam.toCellScheme.below
      (univ.erase (Fin.castSucc (Fin.last k)), k + 1))
    (hsx : Fin.last (k + 1) ∈ (seed ht' hp htb).amalgam.toCellScheme.scope s)
    (hst : (seed ht' hp htb).amalgam.label s = ⊤)
    (he : e ∈ (seed ht' hp htb).amalgam.toCellScheme.below
      ((seed ht' hp htb).amalgam.toCellScheme.gradedIndex s))
    (hxe : Fin.last (k + 1) ∉ (seed ht' hp htb).amalgam.toCellScheme.scope e)
    (hrow : (seed ht' hp htb).amalgam.rows.row s
        ⟨s, (seed ht' hp htb).amalgam.toCellScheme.mem_below_gradedIndex s⟩ ≤
      (seed ht' hp htb).amalgam.rows.row s ⟨e, he⟩) :
    ¬ CapRequests.RaisedCellRefines
      (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)) (Fin.last (k + 1))
      (Fin.castSucc (Fin.last k)) (k + 1) := by
  intro href
  have hL := restrictFace_left_seed ht' hp htb
  have hA := restrictFace_donor_seed ht' hp htb hd
  have hn := hctx.2.2.1
  have hrc : t'.toCellScheme.grade r ≤ t'.toCellScheme.grade c := by
    have h := hctx.2.1.2.1
    rw [CellScheme.mem_below] at h
    exact (Prod.le_def.mp h).2
  have hgr := isGraded_requests ht' hp htb hd (r := r) (by omega) hrc hn
  have hglued : (requests ht' hp htb hd c r (by omega)).IsCorrect
      fun e ↦ (seed ht' hp htb).amalgam.label e :=
    CapRequests.isCorrect_of_forall (fun z hz ↦ absurd hz (Set.notMem_empty _))
      (fun f hf ↦ absurd hf (Set.notMem_empty _))
      fun y hy ↦ by
        obtain ⟨j, hj, -, rfl⟩ := hy
        rw [label_faceCell hA j, hj]; exact le_top
  have hP : ProfileTower.IsCutLawful (seed ht' hp htb) (k + 1)
      fun e ↦ (seed ht' hp htb).amalgam.label e :=
    ⟨(seed ht' hp htb).amalgam.isLawful.isLawfulBelow _,
      (seed ht' hp htb).amalgam.isLawful.isLawfulBelow _⟩
  have hcapt : (seed ht' hp htb).amalgam.label (faceCell hL c) = ⊤ :=
    (label_faceCell hL c).trans hctx.1.2.1
  set h : Label.{u} := ((k + 1 : ℕ) : Label.{u}) with hhdef
  set h₂ : Label.{u} := ((Ordinal.omega0 + ((k + 1 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})
    with hh₂def
  have hh₂ : IsSelfVisible (k + 1) h₂ :=
    isSelfVisible_coe_add Ordinal.isSuccLimit_omega0.isSuccPrelimit le_rfl
  have hhh₂ : h < h₂ := by
    rw [hhdef, hh₂def]
    refine WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ?_)
    exact (Ordinal.natCast_lt_omega0 _).trans_le le_self_add
  have hh₂t : h₂ < ⊤ := WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
  have hf : (seed ht' hp htb).amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (k + 1)), k + 1)
      fun e ↦ min ((seed ht' hp htb).amalgam.label e) h₂ :=
    CellScheme.Rows.isLawfulBelow_iff.mpr
      ((CellScheme.Rows.isLawfulBelow_iff.mp ((seed ht' hp htb).amalgam.isLawful.isLawfulBelow
        (univ.erase (Fin.last (k + 1)), k + 1))).min_const_of_isSelfVisible
        (K := k + 1) (fun d ↦ d.2.2) hh₂)
  obtain ⟨W, -, hWf, hWP, hloc⟩ := href h ((isSelfVisible_natCast _).mpr le_rfl)
    (by
      rw [hhdef, show ((k + 1 : ℕ) : Label.{u}) =
          (((k + 1 : ℕ) : Ordinal.{u}) : Label.{u}) from rfl,
        isShort_coe, Ordinal.natCast_mod_omega0])
    (WithBot.bot_lt_coe _) (fun e ↦ (seed ht' hp htb).amalgam.label e) hP (hglued.hat hgr (k + 1))
    (fun e ↦ min ((seed ht' hp htb).amalgam.label e) h₂) hf
    (fun d _ ↦ by rw [min_assoc, min_eq_right hhh₂.le])
    (by
      change h < min ((seed ht' hp htb).amalgam.label (faceCell hL c)) h₂
      rw [hcapt, min_top_left]; exact hhh₂)
  have hWs : h ≤ W s := by
    have e1 := hWP s
    rw [hst, min_top_left] at e1
    exact e1 ▸ min_le_left _ _
  have hWe := CapRequests.eq_top_of_raiseThrough_local ⟨hsx, hWs⟩ (hloc s hsD hsx hWs) he hxe hrow
  have hes : (seed ht' hp htb).amalgam.toCellScheme.gradedIndex e ≤
      (seed ht' hp htb).amalgam.toCellScheme.gradedIndex s := he
  have heC : e ∈ (seed ht' hp htb).amalgam.toCellScheme.below
      (univ.erase (Fin.last (k + 1)), k + 1) :=
    ⟨fun z hz ↦ mem_erase.mpr ⟨fun h' ↦ hxe (h' ▸ hz), mem_univ _⟩, hes.2.trans hsD.2⟩
  have heD : e ∈ (seed ht' hp htb).amalgam.toCellScheme.below
      (univ.erase (Fin.castSucc (Fin.last k)), k + 1) :=
    ⟨hes.1.trans hsD.1, hes.2.trans hsD.2⟩
  rw [hWf e heC heD] at hWe
  exact absurd hWe ((min_le_right _ _).trans_lt hh₂t).ne

end Band

end H3

end VaughtConjecture
