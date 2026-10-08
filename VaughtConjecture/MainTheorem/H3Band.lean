/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.H3Small

/-!
# The band of the fill at the positive caps (work file for `h3`)

Work file (placement later).  The band (`CapRequests.CapFillPosBandAt`) asks, at a cut grade `k`
from the grade `N` of the cap, for every cap `h` self-visible and short at `k` (so `h` is `⊤` or
has finite part exactly `k`), every profile `P` lawful on the cut with correct splice, and every
`f` lawful below the private coatom agreeing with `P` capped at `h` there with `h < f cap`, a
profile lawful on the cut equal to `f` on the private coatom, agreeing with `P` capped at `h`
everywhere, with correct splice.  Compiled in this file (theorem named):

* **The band from a donor raise in the band** (`CapRequests.DonorRaiseBandAt`,
  `CapRequests.capFillPosBandAt_of_donorRaiseBandAt`): a labelling of the donor coatom equal to
  `f` on the common face, agreeing with `P` capped at `h`, and at least the marker value `M` of
  `f` at the new tops.
* **Below `h` the new tops are free** (`CapRequests.markerValue_le_of_lt`): a new top read below
  `h` by a correct `P` is read at least `M`.
* **Below the cut grade, across a gap** (`CapRequests.BandGapBelowAt`,
  `CapRequests.donorRaiseBandBelowAt_of_bandGapBelowAt`): raising to `⊤` above `h` is a witness
  at the grades below the finite part of `h`, that is below the cut grade (`Label.isWitness_raise`;
  it is not one at the cut grade).  If `f` takes no value in `[h, c)` on the common face below the
  cut grade, `c ≥ M` self-visible, the capped lift at `c` from the common face along the raised
  `P` (bountifulness of the amalgam) is the donor raise below the cut grade.  This is the raise of
  the new tops of grade below the cut grade, at the grade `1` for the small caps; with `c = ⊤`
  when `f` is below `h` on the common face (`CapRequests.bandGapBelowAt_of_lt`, for instance `f`
  is `⊥` there, the condition of the fill at the grade `1` of the reading layer).
* **The top grade of the donor coatom** (`CapRequests.DonorTopLiftAt`, a named hypothesis: the
  lift from the union of the common face at the cut grade and the donor coatom below it);
  `CapRequests.donorRaiseBandAt_of_below_of_topLift`.  It holds when the common face has no cell
  of the cut grade (`CapRequests.donorTopLiftAt_of_face`), in particular at the top cut grade.
* **The refining server is necessary** (`CapRequests.exists_refiningServer_of_isLawfulBelow`,
  `CapRequests.CapFillPosBandAt.exists_refiningServer`): the band at `k` gives, for every datum
  and every new top `y`, a cell `u` of graded index `(univ.erase xd, grade y)` whose row refines
  `f` capped at `M` on the cells of the common face below it.  The row of `u` is a datum of the
  donor, `f` any prescription; the gap is a sufficient condition for such refinement, not a
  necessary one.
* **The gap at the grade `1`** (`CapRequests.bandGapBelowAt_of_le`,
  `CapRequests.bandGapBelowAt_one`, `H3.markerValue_le_of_rowAt_le`,
  `H3.bandGapBelowAt_one_of_rowAt_le`): the least value of `f` at least `h` on the finite common
  face is a gap as soon as all such values are at least `M`; a cell `z` of `t'` read by the cap
  at least at the marker (`rowAt c r ≤ rowAt c z`, `grade z ≤ grade r`; every cell labelled `⊤`)
  carries at least `M` under every prescription, by locality at the cap.  So for a cap of grade
  at most `2` the gap at the grade `1` holds when the cells of grade `1` of the common face are
  read by the cap at least at the marker; a cell read below the marker may carry a value in
  `[h, M)`, and then the raise must separate it.
* **The gap at a cap of the top grade** (`CapRequests.bandGapBelowAt_of_visibilityReplace_le`,
  `Label.visibilityReplace_markerValue_le`, `H3.bandGapBelowAt_top_of_rowAt`,
  `H3.bandGapBelowAt_top_of_labels`): with the marker of grade at least `k`, the gap below the
  cut grade `k + 1` holds when every cell of the common face is read by the cap as `⊥` or at
  least at the marker; for instance when every such cell is labelled `⊤`, or labelled `⊥` and read
  as `⊥`.  This condition excludes ordinal labels on the common face
  (`H3.bot_lt_rowAt_lt_marker`, `H3.label_eq_top_or_bot_of_rowAt`), and the gap itself **fails**
  at an ordinal label at least `k + 1` on the common face (`H3.not_bandGapBelowAt_of_label`: the
  labels of the amalgam, with `h = k + 1`, have marker value `⊤`).  There the band holds (by the
  labels themselves for that datum) but not through a gap.
* **At an acquired context** (`H3.capFillPosBandAt_of_gap`, `H3.exists_classCompletion_of_gap`,
  `H3.exists_classCompletion_top_of_gap`): the band at every cut grade from the gap and the top
  grade of the donor coatom; at a cap of the top grade (`k < N`, the small caps with `k = 1`) the
  completion from the donor raise and the gap at the cut grade `k + 1` alone; on three points
  (`H3.exists_classCompletion_one_of_rowAt_le`) from the donor raise when the cells of grade `1`
  of the common face are read by the cap at least at the marker.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme ProfileTower

/-- Visibility replacement with the value `0` does not increase a label. -/
theorem Label.visibilityReplace_zero_le (k : ℕ) (x : Label.{u}) : visibilityReplace k 0 x ≤ x := by
  induction x using recBotCoeTop with
  | bot => exact le_rfl
  | top => exact le_rfl
  | coe o =>
    rw [visibilityReplace_coe]
    refine WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ?_)
    unfold Ordinal.visibilityReplace
    split_ifs
    · rw [Nat.cast_zero, add_zero]; exact Ordinal.mul_div_le o Ordinal.omega0
    · rw [Ordinal.div_add_mod]

/-- Replacing at the threshold `k + 1` with the value `k` does not increase a label self-visible at
`k`: its finite part is at least `k`. -/
theorem Label.visibilityReplace_succ_le {k : ℕ} {a : Label.{u}} (ha : IsSelfVisible k a) :
    visibilityReplace (k + 1) k a ≤ a := by
  induction a using recBotCoeTop with
  | bot => exact le_rfl
  | top => exact le_rfl
  | coe o =>
    rw [visibilityReplace_coe]
    refine WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ?_)
    have hk := isSelfVisible_coe.mp ha
    unfold Ordinal.visibilityReplace
    split_ifs
    · calc Ordinal.omega0 * (o / Ordinal.omega0) + (k : Ordinal.{u})
          ≤ Ordinal.omega0 * (o / Ordinal.omega0) + o % Ordinal.omega0 := add_le_add_right hk _
        _ = o := Ordinal.div_add_mod _ _
    · rw [Ordinal.div_add_mod]

/-- **The marker value replaced at `k` is at most the marker and the cap**: for a marker `a`
self-visible at `k ≥ 1` and a cap `b` self-visible at `k + 1`, replacing at the threshold `k` with
the value `k` the minimum of `b` and the replacement of `a` at `k + 1` with the value `0` gives at
most `min a b`. -/
theorem Label.visibilityReplace_markerValue_le {k : ℕ} (hk : 0 < k) {a b : Label.{u}}
    (ha : IsSelfVisible k a) (hb : IsSelfVisible (k + 1) b) :
    visibilityReplace k k (min (visibilityReplace (k + 1) 0 a) b) ≤ min a b := by
  rw [visibilityReplace_min le_rfl, (hb.mono (Nat.le_succ k)).visibilityReplace_eq,
    visibilityReplace_visibilityReplace_of_le (Nat.le_succ k)]
  simp only [hk, ↓reduceIte]
  exact min_le_min_right _ (Label.visibilityReplace_succ_le ha)

namespace CapRequests

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {xp xd : Fin (m + 2)}

variable (r xp xd) in
/-- **The donor raise in the band** at the grade `k`: for every cap `h` self-visible and short at
`k`, every profile `P` lawful on the cut with correct splice, and every labelling `f` lawful below
the private coatom agreeing with `P` capped at `h` below it, whose cap lies strictly above `h`,
some labelling lawful below the donor coatom is `f` on the common face, agrees with `P` capped at
`h` everywhere, and is at least the marker value of `f` at every cell of `T`. -/
def DonorRaiseBandAt (k : ℕ) : Prop :=
  ∀ h : Label.{u}, IsSelfVisible k h → IsShort k h → ⊥ < h → ∀ P : Prof I,
    IsCutLawful I k P → r.IsCorrect (hat I k P) →
    ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) (fun d ↦ f d) →
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k), min (f d) h = min (P d) h) →
      h < f r.cap →
      ∃ v : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) (fun d ↦ v d) ∧
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k),
          d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k) → v d = f d) ∧
        (∀ d, min (v d) h = min (P d) h) ∧
        ∀ y ∈ r.T, r.markerValue f ≤ v y

/-- **The band from the donor raise in the band**: the prescription on the private coatom, the
raise elsewhere; lawful on both coatoms (they agree on the common face), agreeing with `P` capped
at `h`, and correct (the cells of `T` are off the private coatom and read at least the marker
value, which is at most the cap). -/
theorem capFillPosBandAt_of_donorRaiseBandAt (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hxd : xd ∈ (Pts : Finset (Fin (m + 2))))
    (hne : xd ≠ xp) {k : ℕ} (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k)
    (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp)
    (hmarkC : I.amalgam.toCellScheme.scope r.marker ⊆ univ.erase xp)
    (hT : ∀ y ∈ r.T, ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp)
    (hZ : r.Z = ∅) (hF : r.F = ∅) (hraise : DonorRaiseBandAt r xp xd k) :
    CapFillPosBandAt r xp k := by
  classical
  intro h hh hs hb P hP hPc f hf hfP hfc
  obtain ⟨v, hv, hvf, hvP, hvT⟩ := hraise h hh hs hb P hP hPc f hf hfP hfc
  set W : Prof I := fun d ↦
    if d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) then f d else v d with hW
  have hWf (d) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k)) : W d = f d := by
    rw [hW]; simp only [hd, ite_true]
  have hWv (d) (hd : d ∉ I.amalgam.toCellScheme.below (univ.erase xp, k)) : W d = v d := by
    rw [hW]; simp only [hd, ite_false]
  have hWC : I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) fun d ↦ W d :=
    (Rows.isLawfulBelow_congr (w := f) (w' := W) fun d hd ↦ (hWf d hd).symm).mp hf
  have hWD : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ W d := by
    refine (Rows.isLawfulBelow_congr (w := v) (w' := W) fun d hd ↦ ?_).mp hv
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k)
    · rw [hWf d hdC]
      exact hvf d hdC hd
    · exact (hWv d hdC).symm
  have hmg : I.amalgam.toCellScheme.grade r.marker ≤ k := hgr.grade_marker_le.trans hNk
  refine ⟨W, lawful_pair hxp hxd hne.symm hWC hWD, hWf, fun d ↦ ?_, ?_⟩
  · by_cases hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k)
    · rw [hWf d hdC]; exact hfP d hdC
    · rw [hWv d hdC]; exact hvP d
  refine isCorrect_of_forall (fun z hz ↦ by simp [hZ] at hz) (fun f' hf' ↦ by simp [hF] at hf')
    fun y hy ↦ ?_
  have hyg : I.amalgam.toCellScheme.grade y ≤ k := (hgr.grade_le_of_mem_T y hy).trans hNk
  have hmv : r.markerValue (hat I k W) = r.markerValue f := by
    unfold markerValue
    rw [hat_of_le hmg, hat_of_le hNk, hWf _ ⟨hmarkC, hmg⟩, hWf _ ⟨hcapC, hNk⟩]
  rw [hmv, hat_of_le hyg, hWv y fun h' ↦ hT y hy h'.1]
  exact hvT y hy

/-- Two labels agreeing capped at `h`, one of them below `h`, are equal. -/
theorem eq_of_min_eq_of_lt_cap {a b h : Label.{u}} (hab : min a h = min b h) (hb : b < h) :
    a = b := by
  rcases lt_or_ge a h with ha | ha
  · rwa [min_eq_left ha.le, min_eq_left hb.le] at hab
  · rw [min_eq_right ha, min_eq_left hb.le] at hab
    exact absurd hab.symm hb.ne

/-- **A correct profile reads its cells below the cap `h` at least the marker value of the
prescription**: if `P` has correct splice at `k`, agrees with `f` capped at `h` (self-visible at the
threshold) at the marker and the cap, the cap of `f` lies above `h`, and `P y < h` at a cell `y` of
`T`, then the marker value of `f` is at most `P y`.  The cap of `P` is at least `h`, so the
replaced marker of `P` is below `h`, hence so is the marker of `P`, which is then that of `f`. -/
theorem markerValue_le_of_lt (hgr : r.IsGraded I.amalgam.toCellScheme.grade) {k : ℕ}
    (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k) {h : Label.{u}} (hh : IsSelfVisible r.N h)
    {P f : Prof I} (hPc : r.IsCorrect (hat I k P))
    (hfr : min (f r.marker) h = min (P r.marker) h) (hfc' : min (f r.cap) h = min (P r.cap) h)
    (hfc : h < f r.cap) {y : Fin I.amalgam.card} (hy : y ∈ r.T) (hPy : P y < h) :
    r.markerValue f ≤ P y := by
  have hmg : I.amalgam.toCellScheme.grade r.marker ≤ k := hgr.grade_marker_le.trans hNk
  have hyg : I.amalgam.toCellScheme.grade y ≤ k := (hgr.grade_le_of_mem_T y hy).trans hNk
  have hPcap : h ≤ P r.cap := by
    rw [min_eq_right hfc.le] at hfc'
    exact hfc' ▸ min_le_left _ _
  have hcorr := hPc.markerValue_le y hy
  unfold markerValue at hcorr
  rw [hat_of_le hmg, hat_of_le hNk, hat_of_le hyg] at hcorr
  have hvlt : visibilityReplace r.N r.R (P r.marker) < h := by
    by_contra hge
    push Not at hge
    have := hcorr.trans (min_le_left _ _)
    exact absurd ((le_min hge hPcap).trans this) (not_le.mpr hPy)
  have hPr : P r.marker < h := by
    by_contra hge
    push Not at hge
    have h1 := monotone_visibilityReplace (k := r.N) (i := r.R) r.R_lt_N.le hge
    rw [hh.visibilityReplace_eq] at h1
    exact absurd h1 (not_le.mpr hvlt)
  have hfP : f r.marker = P r.marker := eq_of_min_eq_of_lt_cap hfr hPr
  calc r.markerValue f ≤ visibilityReplace r.N r.R (f r.marker) := min_le_left _ _
    _ = min (visibilityReplace r.N r.R (P r.marker)) (P r.cap) := by
        rw [hfP, min_eq_left (hvlt.le.trans hPcap)]
    _ ≤ min (P y) (P r.cap) := hcorr
    _ ≤ P y := min_le_left _ _

variable (r xp xd) in
/-- **The donor raise in the band below the cut grade** `K + 1`: as `CapRequests.DonorRaiseBandAt`
at the grade `K + 1`, with the labelling of the donor coatom only below the grade `K`. -/
def DonorRaiseBandBelowAt (K : ℕ) : Prop :=
  ∀ h : Label.{u}, IsSelfVisible (K + 1) h → IsShort (K + 1) h → ⊥ < h → ∀ P : Prof I,
    IsCutLawful I (K + 1) P → r.IsCorrect (hat I (K + 1) P) →
    ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, K + 1) (fun d ↦ f d) →
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1), min (f d) h = min (P d) h) →
      h < f r.cap →
      ∃ v : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xd, K) (fun d ↦ v d) ∧
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1),
          d ∈ I.amalgam.toCellScheme.below (univ.erase xd, K) → v d = f d) ∧
        (∀ d, min (v d) h = min (P d) h) ∧
        ∀ y ∈ r.T, r.markerValue f ≤ v y

variable (r xp xd) in
/-- **The top grade of the donor coatom in the band** at the cut grade `K + 1`: for every datum of
the band, every labelling lawful below the donor coatom at the grade `K`, equal to `f` on the
common face and agreeing with `P` capped at `h`, extends to a labelling lawful below the donor
coatom at the grade `K + 1`, equal to `f` on the common face and agreeing with `P` capped at `h`.
It is a lift from the union of the common face at `K + 1` and the donor coatom at `K`. -/
def DonorTopLiftAt (K : ℕ) : Prop :=
  ∀ h : Label.{u}, IsSelfVisible (K + 1) h → IsShort (K + 1) h → ⊥ < h → ∀ P : Prof I,
    IsCutLawful I (K + 1) P → r.IsCorrect (hat I (K + 1) P) →
    ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, K + 1) (fun d ↦ f d) →
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1), min (f d) h = min (P d) h) →
      h < f r.cap →
      ∀ v : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xd, K) (fun d ↦ v d) →
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1),
          d ∈ I.amalgam.toCellScheme.below (univ.erase xd, K) → v d = f d) →
        (∀ d, min (v d) h = min (P d) h) →
        ∃ v' : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xd, K + 1) (fun d ↦ v' d) ∧
          (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xd, K), v' d = v d) ∧
          (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1),
            d ∈ I.amalgam.toCellScheme.below (univ.erase xd, K + 1) → v' d = f d) ∧
          ∀ d, min (v' d) h = min (P d) h

/-- **The donor raise in the band from its part below the cut grade and the top grade of the
donor coatom**, when the cells of `T` lie below the cut grade. -/
theorem donorRaiseBandAt_of_below_of_topLift {K : ℕ}
    (hTg : ∀ y ∈ r.T, I.amalgam.toCellScheme.grade y ≤ K)
    (hTD : ∀ y ∈ r.T, I.amalgam.toCellScheme.scope y ⊆ univ.erase xd)
    (hbelow : DonorRaiseBandBelowAt r xp xd K) (htop : DonorTopLiftAt r xp xd K) :
    DonorRaiseBandAt r xp xd (K + 1) := by
  intro h hh hs hb P hP hPc f hf hfP hfc
  obtain ⟨v, hv, hvf, hvP, hvT⟩ := hbelow h hh hs hb P hP hPc f hf hfP hfc
  obtain ⟨v', hv', hv'v, hv'f, hv'P⟩ := htop h hh hs hb P hP hPc f hf hfP hfc v hv hvf hvP
  exact ⟨v', hv', hv'f, hv'P, fun y hy ↦ (hv'v y ⟨hTD y hy, hTg y hy⟩).symm ▸ hvT y hy⟩

variable (r xp xd) in
/-- **The gap of the band below the cut grade** `K + 1`: for every cap `h`, profile `P` and
prescription `f` of the band, some label `c` self-visible at `K`, at least `h` and at least the
marker value of `f`, is such that `f` takes no value in `[h, c)` on the common face of the two
coatoms below the grade `K`. -/
def BandGapBelowAt (K : ℕ) : Prop :=
  ∀ h : Label.{u}, IsSelfVisible (K + 1) h → IsShort (K + 1) h → ⊥ < h → ∀ P : Prof I,
    IsCutLawful I (K + 1) P → r.IsCorrect (hat I (K + 1) P) →
    ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, K + 1) (fun d ↦ f d) →
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1), min (f d) h = min (P d) h) →
      h < f r.cap →
      ∃ c : Label.{u}, IsSelfVisible K c ∧ h ≤ c ∧ r.markerValue f ≤ c ∧
        ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1),
          d ∈ I.amalgam.toCellScheme.below (univ.erase xd, K) → h ≤ f d → c ≤ f d

/-- **The gap with `c = ⊤`**: if every prescription of the band is below `h` on the common face
below the grade `K` (for instance `⊥` there), the gap holds with the cap `⊤`. -/
theorem bandGapBelowAt_of_lt {K : ℕ}
    (hlt : ∀ h : Label.{u}, IsSelfVisible (K + 1) h → IsShort (K + 1) h → ⊥ < h →
      ∀ P : Prof I, IsCutLawful I (K + 1) P → r.IsCorrect (hat I (K + 1) P) →
      ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, K + 1) (fun d ↦ f d) →
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1),
          min (f d) h = min (P d) h) → h < f r.cap →
        ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1),
          d ∈ I.amalgam.toCellScheme.below (univ.erase xd, K) → f d < h) :
    BandGapBelowAt r xp xd K := fun h hh hs hb P hP hPc f hf hfP hfc ↦
  ⟨⊤, isSelfVisible_top K, le_top, le_top, fun d hdC hdD hhd ↦
    absurd hhd (not_le.mpr (hlt h hh hs hb P hP hPc f hf hfP hfc d hdC hdD))⟩

/-- **The gap from the values on the common face**: if every value of `f` at least `h` at a cell
of the common face below `K` is at least the marker value of `f` and self-visible at `K`, the gap
holds with `c` the least such value (`⊤` if there is none): the face is finite. -/
theorem bandGapBelowAt_of_le {K : ℕ}
    (hle : ∀ h : Label.{u}, IsSelfVisible (K + 1) h → IsShort (K + 1) h → ⊥ < h →
      ∀ P : Prof I, IsCutLawful I (K + 1) P → r.IsCorrect (hat I (K + 1) P) →
      ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, K + 1) (fun d ↦ f d) →
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1),
          min (f d) h = min (P d) h) → h < f r.cap →
        ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1),
          d ∈ I.amalgam.toCellScheme.below (univ.erase xd, K) → h ≤ f d →
          r.markerValue f ≤ f d ∧ IsSelfVisible K (f d)) :
    BandGapBelowAt r xp xd K := by
  classical
  intro h hh hs hb P hP hPc f hf hfP hfc
  have hle' := hle h hh hs hb P hP hPc f hf hfP hfc
  set S := univ.filter fun d : Fin I.amalgam.card ↦
    d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1) ∧
      d ∈ I.amalgam.toCellScheme.below (univ.erase xd, K) ∧ h ≤ f d with hSdef
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨⊤, isSelfVisible_top K, le_top, le_top, fun d hdC hdD hhd ↦ absurd ?_
      (Finset.notMem_empty d)⟩
    rw [← hS]
    exact mem_filter.mpr ⟨mem_univ _, hdC, hdD, hhd⟩
  obtain ⟨d₀, hd₀, hmin⟩ := S.exists_min_image f hS
  obtain ⟨-, hd₀C, hd₀D, hhd₀⟩ := mem_filter.mp hd₀
  obtain ⟨hM, hsv⟩ := hle' d₀ hd₀C hd₀D hhd₀
  exact ⟨f d₀, hsv, hhd₀, hM, fun d hdC hdD hhd ↦
    hmin d (mem_filter.mpr ⟨mem_univ _, hdC, hdD, hhd⟩)⟩

/-- **The gap from the values on the common face, at every grade**: if every value of `f` at
least `h` at a cell of the common face below `K` is at least the replacement at `K` with the value
`K` of the marker value of `f`, the gap holds with `c` the larger of `h` and that replacement, which
is self-visible at `K`. -/
theorem bandGapBelowAt_of_visibilityReplace_le {K : ℕ}
    (hle : ∀ h : Label.{u}, IsSelfVisible (K + 1) h → IsShort (K + 1) h → ⊥ < h →
      ∀ P : Prof I, IsCutLawful I (K + 1) P → r.IsCorrect (hat I (K + 1) P) →
      ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, K + 1) (fun d ↦ f d) →
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1),
          min (f d) h = min (P d) h) → h < f r.cap →
        ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1),
          d ∈ I.amalgam.toCellScheme.below (univ.erase xd, K) → h ≤ f d →
          visibilityReplace K K (r.markerValue f) ≤ f d) :
    BandGapBelowAt r xp xd K := fun h hh hs hb P hP hPc f hf hfP hfc ↦
  ⟨max h (visibilityReplace K K (r.markerValue f)),
    (hh.mono (Nat.le_succ K)).max (isSelfVisible_visibilityReplace_self K _), le_max_left _ _,
    (le_visibilityReplace (by omega) _).trans (le_max_right _ _),
    fun d hdC hdD hhd ↦ max_le hhd (hle h hh hs hb P hP hPc f hf hfP hfc d hdC hdD hhd)⟩

/-- **The gap at the grade `1`** from the values on the common face: at `K = 1` every cell below
the cut has grade `1`, so its value under `f` is self-visible at `1`. -/
theorem bandGapBelowAt_one
    (hle : ∀ h : Label.{u}, IsSelfVisible 2 h → IsShort 2 h → ⊥ < h →
      ∀ P : Prof I, IsCutLawful I 2 P → r.IsCorrect (hat I 2 P) →
      ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, 2) (fun d ↦ f d) →
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, 2),
          min (f d) h = min (P d) h) → h < f r.cap →
        ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, 2),
          d ∈ I.amalgam.toCellScheme.below (univ.erase xd, 1) → h ≤ f d →
          r.markerValue f ≤ f d) :
    BandGapBelowAt r xp xd 1 :=
  bandGapBelowAt_of_le fun h hh hs hb P hP hPc f hf hfP hfc d hdC hdD hhd ↦
    ⟨hle h hh hs hb P hP hPc f hf hfP hfc d hdC hdD hhd, by
      have hsv := (Rows.isLawfulBelow_iff_forall.mp hf).1 d hdC
      have hg : I.amalgam.toCellScheme.grade d = 1 :=
        le_antisymm hdD.2 (I.amalgam.isWellFormed.isWellFormed.grade_pos d)
      rwa [hg] at hsv⟩

/-- **The donor raise in the band below the cut grade, across a gap.**  The cap `h` of the band is
self-visible and short at the cut grade `K + 1`, so its finite part is `K + 1`, and raising to `⊤`
above `h` is a witness at the grades at most `K` (`Label.isWitness_raise`), not at `K + 1`.  If
`f` takes no value in `[h, c)` on the common face below `K`, with `c` at least the marker value,
the capped lift at the cap `c` from the common face into the donor coatom at the grade `K`
(bountifulness of the amalgam), along the profile `P` raised to `⊤` above `h`, extends `f`; it
agrees with `P` capped at `h`, and at a cell `y` of `T` it is at least `c` where `P y ≥ h`, and
`P y`, at least the marker value (`CapRequests.markerValue_le_of_lt`), where `P y < h`. -/
theorem donorRaiseBandBelowAt_of_bandGapBelowAt (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) (hne : xd ≠ xp) {K : ℕ} (hK : 0 < K)
    (hKm : K ≤ m) (hNk : I.amalgam.toCellScheme.grade r.cap ≤ K + 1)
    (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp)
    (hmarkC : I.amalgam.toCellScheme.scope r.marker ⊆ univ.erase xp)
    (hTg : ∀ y ∈ r.T, I.amalgam.toCellScheme.grade y ≤ K)
    (hTD : ∀ y ∈ r.T, I.amalgam.toCellScheme.scope y ⊆ univ.erase xd)
    (hgap : BandGapBelowAt r xp xd K) : DonorRaiseBandBelowAt r xp xd K := by
  classical
  intro h hh hs hb P hP hPc f hf hfP hfc
  obtain ⟨c, hc, hhc, hMc, hgapc⟩ := hgap h hh hs hb P hP hPc f hf hfP hfc
  obtain ⟨hOf, hOcard⟩ := inter_props (I := I) hxp hxd hne.symm
  set X : Finset (Fin (m + 2)) × ℕ := (univ.erase xp ∩ univ.erase xd, K) with hXdef
  set Y : Finset (Fin (m + 2)) × ℕ := (univ.erase xd, K) with hYdef
  have hXf : X ∈ I.amalgam.toCellScheme.gradedFaces :=
    ⟨hOf, hK, by simp only [hXdef]; rw [hOcard]; exact hKm⟩
  have hYf : Y ∈ I.amalgam.toCellScheme.gradedFaces :=
    ⟨I.erase_mem_faces hxd, hK, by simp only [hYdef]; rw [Seed.card_erase]; omega⟩
  have hXY : X ≤ Y := ⟨inter_subset_right, le_rfl⟩
  have hXC : X ≤ (univ.erase xp, K + 1) := ⟨inter_subset_left, Nat.le_succ K⟩
  have hPY : I.amalgam.rows.IsLawfulBelow Y fun d ↦ P d :=
    (hP.erase hxd).mono (X := Y) ⟨subset_rfl, Nat.le_succ K⟩
  have hSY : I.amalgam.rows.IsLawfulBelow Y fun d ↦ raise h (P d) :=
    hPY.map_of_apply_eq_bot (fun d ↦ d.2.2) (isWitness_raise (K := K) hh hb)
      fun _ h0 ↦ eq_bot_of_raise_eq_bot h0
  have hagree (d : I.amalgam.toCellScheme.below X) :
      min (raise h (P (Set.inclusion (I.amalgam.toCellScheme.below_mono hXY) d))) c =
        min (f d) c := by
    change min (raise h (P d.1)) c = min (f d.1) c
    have hdC : d.1 ∈ I.amalgam.toCellScheme.below (univ.erase xp, K + 1) :=
      I.amalgam.toCellScheme.below_mono hXC d.2
    have hdD : d.1 ∈ I.amalgam.toCellScheme.below (univ.erase xd, K) :=
      I.amalgam.toCellScheme.below_mono hXY d.2
    have e := hfP d.1 hdC
    rcases lt_or_ge (f d.1) h with hl | hl
    · have hPf : P d.1 = f d.1 := eq_of_min_eq_of_lt_cap e.symm hl
      unfold raise
      rw [ite_eq_right (by rw [hPf]; exact not_le.mpr hl), hPf]
    · have hPh : h ≤ P d.1 := by
        rw [min_eq_right hl] at e
        exact e ▸ min_le_left _ _
      unfold raise
      rw [ite_eq_left hPh, min_top_left, min_eq_right (hgapc d.1 hdC hdD hl)]
  obtain ⟨q, hq, hqS, hqf⟩ := (Rows.cappedLift_iff_forall_exists hXY).mp
    (I.isBountiful hXf hYf hXY) c hc (fun d ↦ f d) (fun d ↦ raise h (P d))
    (hf.mono (X := X) hXC) hSY hagree
  set v : Prof I := fun d ↦ if hd : d ∈ I.amalgam.toCellScheme.below Y then q ⟨d, hd⟩ else P d
    with hvdef
  have hvY (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below Y) :
      v d = q ⟨d, hd⟩ := by
    rw [hvdef]; simp only [hd, dite_true]
  have hvc (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below Y) :
      min (v d) c = min (raise h (P d)) c := by
    rw [hvY d hd]; exact hqS ⟨d, hd⟩
  refine ⟨v, ?_, fun d hdC hdD ↦ ?_, fun d ↦ ?_, fun y hy ↦ ?_⟩
  · convert hq using 1
    exact funext fun d ↦ hvY d.1 d.2
  · rw [hvY d hdD]
    exact hqf ⟨d, ⟨subset_inter hdC.1 hdD.1, hdD.2⟩⟩
  · by_cases hd : d ∈ I.amalgam.toCellScheme.below Y
    · have e1 (a : Label.{u}) : min a h = min (min a c) h := by
        rw [min_assoc, min_eq_right hhc]
      rw [e1 (v d), hvc d hd, ← e1, min_raise]
    · rw [hvdef]; simp only [hd, dite_false]
  · have hyY : y ∈ I.amalgam.toCellScheme.below Y := ⟨hTD y hy, hTg y hy⟩
    have e := hvc y hyY
    rcases lt_or_ge (P y) h with hl | hl
    · have hraise' : raise h (P y) = P y := by unfold raise; rw [ite_eq_right (not_le.mpr hl)]
      rw [hraise', min_eq_left (hl.le.trans hhc)] at e
      have hmg : I.amalgam.toCellScheme.grade r.marker ≤ K + 1 := hgr.grade_marker_le.trans hNk
      have hM := markerValue_le_of_lt hgr hNk (hh.mono (hgr.le_grade_cap.trans hNk)) hPc
        (hfP _ ⟨hmarkC, hmg⟩) (hfP _ ⟨hcapC, hNk⟩) hfc hy hl
      exact hM.trans (e ▸ min_le_left _ _)
    · have hraise' : raise h (P y) = ⊤ := by unfold raise; rw [ite_eq_left hl]
      rw [hraise', min_top_left] at e
      exact hMc.trans (e ▸ min_le_left _ _)

/-- **The top grade of the donor coatom when the common face has no cell of the cut grade**: if
every cell of the common face has grade at most `K`, the lift from the donor coatom at `K` to the
donor coatom at `K + 1` is the capped lift at the cap `h` along `P` (bountifulness of the
amalgam); the common face at `K + 1` lies below the donor coatom at `K`.  In particular at the top
cut grade `K + 1 = m + 1`, the common face having `m` points. -/
theorem donorTopLiftAt_of_face (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) {K : ℕ} (hK : 0 < K)
    (hKm : K ≤ m)
    (hface : ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∩ univ.erase xd →
      I.amalgam.toCellScheme.grade d ≤ K) :
    DonorTopLiftAt r xp xd K := by
  classical
  intro h hh _ _ P hP _ f _ _ _ v hv hvf hvP
  set X : Finset (Fin (m + 2)) × ℕ := (univ.erase xd, K) with hXdef
  set Y : Finset (Fin (m + 2)) × ℕ := (univ.erase xd, K + 1) with hYdef
  have hXf : X ∈ I.amalgam.toCellScheme.gradedFaces :=
    ⟨I.erase_mem_faces hxd, hK, by simp only [hXdef]; rw [Seed.card_erase]; omega⟩
  have hYf : Y ∈ I.amalgam.toCellScheme.gradedFaces :=
    ⟨I.erase_mem_faces hxd, by simp only [hYdef]; omega,
      by simp only [hYdef]; rw [Seed.card_erase]; omega⟩
  have hXY : X ≤ Y := ⟨subset_rfl, Nat.le_succ K⟩
  obtain ⟨q, hq, hqP, hqv⟩ := (Rows.cappedLift_iff_forall_exists hXY).mp
    (I.isBountiful hXf hYf hXY) h hh (fun d ↦ v d) (fun d ↦ P d) hv (hP.erase hxd)
    fun d ↦ (hvP d.1).symm
  set v' : Prof I := fun d ↦ if hd : d ∈ I.amalgam.toCellScheme.below Y then q ⟨d, hd⟩ else P d
    with hv'def
  have hv'Y (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below Y) :
      v' d = q ⟨d, hd⟩ := by
    rw [hv'def]; simp only [hd, dite_true]
  have hv'X (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below X) : v' d = v d := by
    rw [hv'Y d (I.amalgam.toCellScheme.below_mono hXY hd)]
    exact hqv ⟨d, hd⟩
  refine ⟨v', ?_, hv'X, fun d hdC hdD ↦ ?_, fun d ↦ ?_⟩
  · convert hq using 1
    exact funext fun d ↦ hv'Y d.1 d.2
  · have hdX : d ∈ I.amalgam.toCellScheme.below X :=
      ⟨hdD.1, hface d (subset_inter hdC.1 hdD.1)⟩
    rw [hv'X d hdX]
    exact hvf d ⟨hdC.1, hdC.2⟩ hdX
  · by_cases hd : d ∈ I.amalgam.toCellScheme.below Y
    · rw [hv'Y d hd]; exact hqP ⟨d, hd⟩
    · rw [hv'def]; simp only [hd, dite_false]

/-! ### The refining server: necessary for the band -/

/-- **A lawful labelling has a refining server at the graded index of every cell above a given
one**: for `w` lawful below `X`, a cell `y` and a cell `t` below `X` of the grade of `y` whose
scope contains that of `y`, some cell `u` of the graded index of `t` with `w y ≤ w u` has a row
refining `w` capped at `w y` at the cells below it (availability at `y`, then locality at `u`). -/
theorem exists_refiningServer_of_isLawfulBelow {X : Finset (Fin (m + 2)) × ℕ} {w : Prof I}
    (hw : I.amalgam.rows.IsLawfulBelow X fun d ↦ w d) {y t : Fin I.amalgam.card}
    (ht : t ∈ I.amalgam.toCellScheme.below X)
    (hyt : I.amalgam.toCellScheme.scope y ⊆ I.amalgam.toCellScheme.scope t)
    (hg : I.amalgam.toCellScheme.grade y = I.amalgam.toCellScheme.grade t) :
    ∃ u, I.amalgam.toCellScheme.gradedIndex u = I.amalgam.toCellScheme.gradedIndex t ∧
      w y ≤ w u ∧ ∀ e e' (he : e ∈ I.amalgam.toCellScheme.below
        (I.amalgam.toCellScheme.gradedIndex u)) (he' : e' ∈ I.amalgam.toCellScheme.below
        (I.amalgam.toCellScheme.gradedIndex u)),
        I.amalgam.toCellScheme.grade e' ≤ I.amalgam.toCellScheme.grade e →
        I.amalgam.rows.row u ⟨e, he⟩ ≤ I.amalgam.rows.row u ⟨e', he'⟩ →
        min (w e) (w y) ≤ min (w e') (w y) := by
  obtain ⟨-, hloc, havail⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  obtain ⟨u, hu, hyu⟩ := havail y t ht hyt hg
  have huX : u ∈ I.amalgam.toCellScheme.below X := by
    rw [CellScheme.mem_below, hu]; exact ht
  refine ⟨u, hu, hyu, fun e e' he he' hg' hrow ↦ ?_⟩
  have h1 := (hloc u huX).le_of_le (d := ⟨e, he⟩) (d' := ⟨e', he'⟩) hrow hg'
  change min (w e) (w u) ≤ min (w e') (w u) at h1
  calc min (w e) (w y) = min (min (w e) (w u)) (w y) := by rw [min_assoc, min_eq_right hyu]
    _ ≤ min (min (w e') (w u)) (w y) := min_le_min_right _ h1
    _ = min (w e') (w y) := by rw [min_assoc, min_eq_right hyu]

/-- **The band needs a refining server at the grade of each cell of `T`.**  If the band holds at
the grade `k`, then for every datum `(h, P, f)` of the band, every cell `y` of `T` below the donor
coatom at `k`, and every cell `t` of graded index `(univ.erase xd, grade y)`, some cell `u` of that
graded index has a row refining `f` capped at the marker value of `f` on the cells of the common
face below it: if the row of `u` at `e` is at most its row at `e'`, with `grade e' ≤ grade e`, then
`min (f e) M ≤ min (f e') M`, `M` the marker value.  The row of `u` is a datum of the donor; `f`
is any prescription of the band. -/
theorem CapFillPosBandAt.exists_refiningServer (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) {k : ℕ}
    (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k)
    (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp)
    (hmarkC : I.amalgam.toCellScheme.scope r.marker ⊆ univ.erase xp)
    (hband : CapFillPosBandAt r xp k) {h : Label.{u}} (hh : IsSelfVisible k h)
    (hs : IsShort k h) (hb : ⊥ < h) {P : Prof I} (hP : IsCutLawful I k P)
    (hPc : r.IsCorrect (hat I k P)) {f : Prof I}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) (fun d ↦ f d))
    (hfP : ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k), min (f d) h = min (P d) h)
    (hfc : h < f r.cap) {y t : Fin I.amalgam.card} (hy : y ∈ r.T)
    (hyD : I.amalgam.toCellScheme.scope y ⊆ univ.erase xd)
    (ht : I.amalgam.toCellScheme.gradedIndex t = (univ.erase xd, I.amalgam.toCellScheme.grade y)) :
    ∃ u, I.amalgam.toCellScheme.gradedIndex u =
        (univ.erase xd, I.amalgam.toCellScheme.grade y) ∧
      ∀ e e' (he : e ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex u))
        (he' : e' ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex u)),
        e ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) →
        e' ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) →
        I.amalgam.toCellScheme.grade e' ≤ I.amalgam.toCellScheme.grade e →
        I.amalgam.rows.row u ⟨e, he⟩ ≤ I.amalgam.rows.row u ⟨e', he'⟩ →
        min (f e) (r.markerValue f) ≤ min (f e') (r.markerValue f) := by
  obtain ⟨W, hW, hWf, -, hWc⟩ := hband h hh hs hb P hP hPc f hf hfP hfc
  have hyg : I.amalgam.toCellScheme.grade y ≤ k := (hgr.grade_le_of_mem_T y hy).trans hNk
  have hmg : I.amalgam.toCellScheme.grade r.marker ≤ k := hgr.grade_marker_le.trans hNk
  have hmv : r.markerValue (hat I k W) = r.markerValue f := by
    unfold markerValue
    rw [hat_of_le hmg, hat_of_le hNk, hWf _ ⟨hmarkC, hmg⟩, hWf _ ⟨hcapC, hNk⟩]
  have hMW : r.markerValue f ≤ W y := by
    have := hWc.markerValue_le y hy
    rw [hmv, hat_of_le hyg, hat_of_le hNk] at this
    exact this.trans (min_le_left _ _)
  have htD : t ∈ I.amalgam.toCellScheme.below (univ.erase xd, k) := by
    rw [CellScheme.mem_below, ht]; exact ⟨subset_rfl, hyg⟩
  have hyt : I.amalgam.toCellScheme.scope y ⊆ I.amalgam.toCellScheme.scope t := by
    rw [show I.amalgam.toCellScheme.scope t = univ.erase xd from congrArg Prod.fst ht]
    exact hyD
  obtain ⟨u, hu, -, href⟩ := exists_refiningServer_of_isLawfulBelow (hW.erase hxd) htD hyt
    (congrArg Prod.snd ht).symm
  refine ⟨u, hu.trans ht, fun e e' he he' heC he'C hg' hrow ↦ ?_⟩
  have h1 := href e e' he he' hg' hrow
  rw [hWf e heC, hWf e' he'C] at h1
  calc min (f e) (r.markerValue f) = min (min (f e) (W y)) (r.markerValue f) := by
        rw [min_assoc, min_eq_right hMW]
    _ ≤ min (min (f e') (W y)) (r.markerValue f) := min_le_min_right _ h1
    _ = min (f e') (r.markerValue f) := by rw [min_assoc, min_eq_right hMW]

end CapRequests

namespace H3

open StageType

variable {α : Ordinal.{u}} {n k : ℕ}

section Band

variable {t' : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {tb : StageType.{u} α (k + 1)}
  (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces)
  {g : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)}

/-- **The band at an acquired context from the gap below the cut grade and the top grade of the
donor coatom**: at every cut grade `K + 1` from the grade `N` of the cap, the band of the requests
holds when `f` takes no value in a gap `[h, c)` on the common face below `K`
(`CapRequests.BandGapBelowAt`) and the donor coatom extends from the grade `K` to `K + 1` along
the common face (`CapRequests.DonorTopLiftAt`).  The new tops lie below the donor coatom and have
grade at most `n + 1 < N ≤ K + 1`. -/
theorem capFillPosBandAt_of_gap (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r) {K : ℕ}
    (hK : t'.toCellScheme.grade c ≤ K + 1) (hKk : K + 1 ≤ k + 1)
    (hgap : CapRequests.BandGapBelowAt
      (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)) (Fin.last (k + 1))
      (Fin.castSucc (Fin.last k)) K)
    (htop : CapRequests.DonorTopLiftAt
      (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)) (Fin.last (k + 1))
      (Fin.castSucc (Fin.last k)) K) :
    CapRequests.CapFillPosBandAt (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega))
      (Fin.last (k + 1)) (K + 1) := by
  have hrc : t'.toCellScheme.grade r ≤ t'.toCellScheme.grade c := by
    have h := hctx.2.1.2.1
    rw [CellScheme.mem_below] at h
    exact (Prod.le_def.mp h).2
  have hn := hctx.2.2.1
  have hgr := isGraded_requests ht' hp htb hd (r := r) (by omega) hrc hn
  have hL := restrictFace_left_seed ht' hp htb
  have hA := restrictFace_donor_seed ht' hp htb hd
  have hcapg' : (seed ht' hp htb).amalgam.toCellScheme.grade
      (requests ht' hp htb hd c r (by omega)).cap = t'.toCellScheme.grade c := grade_faceCell hL c
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
  have hTD (y) (hy : y ∈ (requests ht' hp htb hd c r (by omega)).T) :
      (seed ht' hp htb).amalgam.toCellScheme.scope y ⊆ univ.erase (Fin.castSucc (Fin.last k)) := by
    obtain ⟨j, -, -, rfl⟩ := hy
    rw [scope_faceCell]
    intro z hz
    obtain ⟨i, -, rfl⟩ := mem_map.mp hz
    refine mem_erase.mpr ⟨?_, mem_univ _⟩
    induction i using Fin.lastCases with
    | last => rw [extendByLast_last]; exact Fin.castSucc_ne_last _ |>.symm
    | cast i =>
      rw [extendByLast_castSucc]
      intro h
      have := Fin.castSucc_injective _ h
      exact Fin.castSucc_ne_last _ this
  have hTg (y) (hy : y ∈ (requests ht' hp htb hd c r (by omega)).T) :
      (seed ht' hp htb).amalgam.toCellScheme.grade y ≤ K := by
    obtain ⟨j, -, -, rfl⟩ := hy
    rw [grade_faceCell]
    have := d.grade_le j
    omega
  have hNk : (seed ht' hp htb).amalgam.toCellScheme.grade
      (requests ht' hp htb hd c r (by omega)).cap ≤ K + 1 := hcapg'.trans_le hK
  exact CapRequests.capFillPosBandAt_of_donorRaiseBandAt hgr (by simp) (by simp)
    Seed.last_ne_castSucc.symm hNk hcapC.le hmarkC hTC rfl rfl
    (CapRequests.donorRaiseBandAt_of_below_of_topLift hTg hTD
      (CapRequests.donorRaiseBandBelowAt_of_bandGapBelowAt hgr (by simp) (by simp)
        Seed.last_ne_castSucc.symm (by omega) (by omega) hNk hcapC.le hmarkC hTg hTD hgap)
      htop)

/-- **The completion with rows admitted in the class from the donor lift provisions, the donor
raise, and the gap and the top grade of the donor coatom at every cut grade from the cap**
(`H3.exists_classCompletion_of_fills₀` with the band from `H3.capFillPosBandAt_of_gap`). -/
theorem exists_classCompletion_of_gap (hd : restrictFace (extendByLast g) tb = some d)
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
    (hgap : ∀ K, t'.toCellScheme.grade c ≤ K + 1 → K + 1 ≤ k + 1 →
      CapRequests.BandGapBelowAt
        (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)) (Fin.last (k + 1))
        (Fin.castSucc (Fin.last k)) K)
    (htop : ∀ K, t'.toCellScheme.grade c ≤ K + 1 → K + 1 ≤ k + 1 →
      CapRequests.DonorTopLiftAt
        (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)) (Fin.last (k + 1))
        (Fin.castSucc (Fin.last k)) K) :
    ∃ F : CompletionBelowFullGrade (seed ht' hp htb),
      F.HasAdmittedRows (t'.toCellScheme.grade c)
        ((requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)).Admits
          (classCells ht' hp htb hd) ∅) := by
  have hn := hctx.2.2.1
  refine exists_classCompletion_of_fills₀ ht' hp htb hd hctx hdon hraise fun k' hk' hkm ↦ ?_
  obtain ⟨K, rfl⟩ : ∃ K, k' = K + 1 := ⟨k' - 1, by omega⟩
  exact capFillPosBandAt_of_gap ht' hp htb hd hctx hk' hkm (hgap K hk' hkm) (htop K hk' hkm)

/-- **The completion with rows admitted in the class at a cap of the top grade** (`k < N`, so
`N = k + 1`; at the small caps, `k = 1`): from the donor raise and the gap of the band at the
cut grade `k + 1` alone.  The lift provisions from the donor coatom hold
(`H3.donorLiftProvisions_of_lt`), and the top grade of the donor coatom extends freely
(`CapRequests.donorTopLiftAt_of_face`), the common face having `k` points. -/
theorem exists_classCompletion_top_of_gap (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hkN : k < t'.toCellScheme.grade c)
    (hraise : ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
      CapRequests.DonorRaiseBotAtIn (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega))
        (classCells ht' hp htb hd) (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k')
    (hgap : CapRequests.BandGapBelowAt
        (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)) (Fin.last (k + 1))
        (Fin.castSucc (Fin.last k)) k) :
    ∃ F : CompletionBelowFullGrade (seed ht' hp htb),
      F.HasAdmittedRows (t'.toCellScheme.grade c)
        ((requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)).Admits
          (classCells ht' hp htb hd) ∅) := by
  have hn := hctx.2.2.1
  have hck : t'.toCellScheme.grade c ≤ k + 1 := t'.grade_le c
  have hk0 : 0 < k := by omega
  refine exists_classCompletion_of_gap ht' hp htb hd hctx
    (donorLiftProvisions_of_lt ht' hp htb hd hctx hkN) hraise
    (fun K hK hKk ↦ by
      obtain rfl : K = k := by omega
      exact hgap)
    fun K hK hKk ↦ ?_
  obtain rfl : K = k := by omega
  refine CapRequests.donorTopLiftAt_of_face (by simp) hk0 le_rfl fun e he ↦ ?_
  obtain ⟨-, hOcard⟩ := ProfileTower.inter_props (I := seed ht' hp htb)
    (x := Fin.last (K + 1)) (y := Fin.castSucc (Fin.last K)) (by simp) (by simp)
    Seed.last_ne_castSucc
  have h1 := (seed ht' hp htb).amalgam.isWellFormed.isWellFormed.grade_le_card e
  have h2 := card_le_card he
  omega

/-- **A cell read by the cap at least at the marker carries at least the marker and the cap**: for
`f` lawful below the private coatom at a cut grade at least the grade of the cap, and a cell `z` of
`t'` with `rowAt c r ≤ rowAt c z` and `grade z ≤ grade r`, locality of `f` at the cap gives
`min (f r) (f c) ≤ min (f z) (f c) ≤ f z`. -/
theorem min_marker_cap_le_of_rowAt_le {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r) {K : ℕ}
    (hK : t'.toCellScheme.grade c ≤ K) {f : ProfileTower.Prof (seed ht' hp htb)}
    (hf : (seed ht' hp htb).amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (k + 1)), K)
      (fun e ↦ f e)) {z : Fin t'.card} (hzr : t'.rowAt c r ≤ t'.rowAt c z)
    (hgz : t'.toCellScheme.grade z ≤ t'.toCellScheme.grade r) :
    min (f (faceCell (restrictFace_left_seed ht' hp htb) r))
        (f (faceCell (restrictFace_left_seed ht' hp htb) c)) ≤
      f (faceCell (restrictFace_left_seed ht' hp htb) z) := by
  have hL := restrictFace_left_seed ht' hp htb
  set A := (seed ht' hp htb).amalgam
  have hrc : r ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex c) := hctx.2.1.2.1
  have hrc' : t'.toCellScheme.grade r ≤ t'.toCellScheme.grade c := by
    rw [CellScheme.mem_below] at hrc
    exact (Prod.le_def.mp hrc).2
  have hcb : faceCell hL c ∈ A.toCellScheme.below (univ.erase (Fin.last (k + 1)), K) := by
    refine ⟨?_, ?_⟩
    · change A.toCellScheme.scope (faceCell hL c) ⊆ _
      rw [scope_faceCell, hctx.1.1, Coatom.univ_map_left]
    · change A.toCellScheme.grade (faceCell hL c) ≤ K
      rw [grade_faceCell]; exact hK
  have hmem (x : Fin t'.card) (hx : t'.toCellScheme.grade x ≤ t'.toCellScheme.grade c) :
      faceCell hL x ∈ A.toCellScheme.below (A.toCellScheme.gradedIndex (faceCell hL c)) := by
    rw [CellScheme.mem_below]
    refine Prod.mk_le_mk.mpr ⟨?_, ?_⟩
    · change A.toCellScheme.scope (faceCell hL x) ⊆ A.toCellScheme.scope (faceCell hL c)
      rw [scope_faceCell, scope_faceCell, hctx.1.1]
      exact map_subset_map.mpr (subset_univ _)
    · change A.toCellScheme.grade (faceCell hL x) ≤ A.toCellScheme.grade (faceCell hL c)
      rw [grade_faceCell, grade_faceCell]; exact hx
  have hrm := hmem r hrc'
  have hzm := hmem z (hgz.trans hrc')
  obtain ⟨-, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hf
  have hrow : A.rows.row (faceCell hL c) ⟨faceCell hL r, hrm⟩ ≤
      A.rows.row (faceCell hL c) ⟨faceCell hL z, hzm⟩ := by
    rw [← Scheme.rowAt_of_mem, ← Scheme.rowAt_of_mem]
    rw [rowAt_faceCell, rowAt_faceCell]
    exact hzr
  have h1 := (hloc _ hcb).le_of_le (d := ⟨faceCell hL r, hrm⟩) (d' := ⟨faceCell hL z, hzm⟩) hrow
    (by
      change A.toCellScheme.grade (faceCell hL z) ≤ A.toCellScheme.grade (faceCell hL r)
      rw [grade_faceCell, grade_faceCell]; exact hgz)
  change min (f (faceCell hL r)) (f (faceCell hL c)) ≤
    min (f (faceCell hL z)) (f (faceCell hL c)) at h1
  exact h1.trans (min_le_left _ _)

/-- **A cell read by the cap at least at the marker carries at least the marker value**
(`H3.min_marker_cap_le_of_rowAt_le`).  In particular at every cell of `t'` labelled `⊤` of grade
at most that of the marker. -/
theorem markerValue_le_of_rowAt_le (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r) {K : ℕ}
    (hK : t'.toCellScheme.grade c ≤ K) {f : ProfileTower.Prof (seed ht' hp htb)}
    (hf : (seed ht' hp htb).amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (k + 1)), K)
      (fun e ↦ f e)) {z : Fin t'.card} (hzr : t'.rowAt c r ≤ t'.rowAt c z)
    (hgz : t'.toCellScheme.grade z ≤ t'.toCellScheme.grade r) :
    (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)).markerValue f ≤
      f (faceCell (restrictFace_left_seed ht' hp htb) z) :=
  (min_le_min_right _ (Label.visibilityReplace_zero_le _ _)).trans
    (min_marker_cap_le_of_rowAt_le ht' hp htb hctx hK hf hzr hgz)

/-- **The gap at the grade `1` for a cap of grade at most `2`**, when every cell of grade `1` of
the common face (the cells of `t'` of grade `1` avoiding its last point) is read by the cap at
least at the marker: then every prescription carries at least the marker value there
(`H3.markerValue_le_of_rowAt_le`), and the gap holds (`CapRequests.bandGapBelowAt_one`).  At a
cell of grade `1` read by the cap below the marker a prescription may take a value in `[h, M)`,
and the raise must separate it from the new tops. -/
theorem bandGapBelowAt_one_of_rowAt_le (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hN : t'.toCellScheme.grade c ≤ 2)
    (hface : ∀ z : Fin t'.card, t'.toCellScheme.grade z = 1 →
      Fin.last k ∉ t'.toCellScheme.scope z → t'.rowAt c r ≤ t'.rowAt c z) :
    CapRequests.BandGapBelowAt (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega))
      (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) 1 := by
  have hL := restrictFace_left_seed ht' hp htb
  refine CapRequests.bandGapBelowAt_one fun h _ _ _ P _ _ f hf _ _ e heC heD _ ↦ ?_
  have hlast : Fin.last (k + 1) ∉ (seed ht' hp htb).amalgam.toCellScheme.scope e := fun hm ↦
    (mem_erase.mp (heC.1 hm)).1 rfl
  obtain ⟨z, rfl⟩ := exists_faceCell_eq_of_last_notMem hL hlast
  have hg1 : t'.toCellScheme.grade z = 1 := by
    have h1 : (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL z) ≤ 1 := heD.2
    have h2 := (seed ht' hp htb).amalgam.isWellFormed.isWellFormed.grade_pos (faceCell hL z)
    rw [grade_faceCell] at h1 h2
    omega
  have hzl : Fin.last k ∉ t'.toCellScheme.scope z := fun hm ↦ by
    have h1 : Fin.castSucc (Fin.last k) ∈
        (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL z) := by
      rw [scope_faceCell]
      exact mem_map.mpr ⟨_, hm, rfl⟩
    exact (mem_erase.mp (heD.1 h1)).1 rfl
  have hgr : t'.toCellScheme.grade z ≤ t'.toCellScheme.grade r := by
    rw [hg1]; exact t'.isWellFormed.isWellFormed.grade_pos r
  exact markerValue_le_of_rowAt_le ht' hp htb hd hctx hN hf (hface z hg1 hzl) hgr

/-- **The small caps on three points** (`k = 1`, the cap of grade `2`): the completion with rows
admitted in the class from the donor raise alone, when the cells of grade `1` of the common face
are read by the cap at least at the marker (`H3.exists_classCompletion_top_of_gap`,
`H3.bandGapBelowAt_one_of_rowAt_le`). -/
theorem exists_classCompletion_one_of_rowAt_le (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hkN : k < t'.toCellScheme.grade c) (hN : t'.toCellScheme.grade c ≤ 2)
    (hraise : ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
      CapRequests.DonorRaiseBotAtIn (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega))
        (classCells ht' hp htb hd) (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k')
    (hface : ∀ z : Fin t'.card, t'.toCellScheme.grade z = 1 →
      Fin.last k ∉ t'.toCellScheme.scope z → t'.rowAt c r ≤ t'.rowAt c z) :
    ∃ F : CompletionBelowFullGrade (seed ht' hp htb),
      F.HasAdmittedRows (t'.toCellScheme.grade c)
        ((requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)).Admits
          (classCells ht' hp htb hd) ∅) := by
  have hn := hctx.2.2.1
  have hck : t'.toCellScheme.grade c ≤ k + 1 := t'.grade_le c
  obtain rfl : k = 1 := by omega
  exact exists_classCompletion_top_of_gap ht' hp htb hd hctx hkN hraise
    (bandGapBelowAt_one_of_rowAt_le ht' hp htb hd hctx hN hface)

/-- **A cell read by the cap as `⊥` is `⊥` under every prescription not `⊥` at the cap**: by
locality of `f` at the cap, `min (f z) (f c)` is the image of `⊥` under a witness. -/
theorem eq_bot_of_rowAt_eq_bot {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r) {K : ℕ}
    (hK : t'.toCellScheme.grade c ≤ K) {f : ProfileTower.Prof (seed ht' hp htb)}
    (hf : (seed ht' hp htb).amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (k + 1)), K)
      (fun e ↦ f e)) (hfc : f (faceCell (restrictFace_left_seed ht' hp htb) c) ≠ ⊥)
    {z : Fin t'.card} (hgz : t'.toCellScheme.grade z ≤ t'.toCellScheme.grade c)
    (hz : t'.rowAt c z = ⊥) :
    f (faceCell (restrictFace_left_seed ht' hp htb) z) = ⊥ := by
  have hL := restrictFace_left_seed ht' hp htb
  set A := (seed ht' hp htb).amalgam
  have hcb : faceCell hL c ∈ A.toCellScheme.below (univ.erase (Fin.last (k + 1)), K) := by
    refine ⟨?_, ?_⟩
    · change A.toCellScheme.scope (faceCell hL c) ⊆ _
      rw [scope_faceCell, hctx.1.1, Coatom.univ_map_left]
    · change A.toCellScheme.grade (faceCell hL c) ≤ K
      rw [grade_faceCell]; exact hK
  have hzm : faceCell hL z ∈ A.toCellScheme.below (A.toCellScheme.gradedIndex (faceCell hL c)) := by
    rw [CellScheme.mem_below]
    refine Prod.mk_le_mk.mpr ⟨?_, ?_⟩
    · change A.toCellScheme.scope (faceCell hL z) ⊆ A.toCellScheme.scope (faceCell hL c)
      rw [scope_faceCell, scope_faceCell, hctx.1.1]
      exact map_subset_map.mpr (subset_univ _)
    · change A.toCellScheme.grade (faceCell hL z) ≤ A.toCellScheme.grade (faceCell hL c)
      rw [grade_faceCell, grade_faceCell]; exact hgz
  obtain ⟨-, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hf
  obtain ⟨g', σ, hw, heq⟩ := hloc _ hcb
  have e := heq ⟨faceCell hL z, hzm⟩
  have hrow : A.rows.row (faceCell hL c) ⟨faceCell hL z, hzm⟩ = ⊥ := by
    rw [← Scheme.rowAt_of_mem, rowAt_faceCell]; exact hz
  change min (f (faceCell hL z)) (f (faceCell hL c)) = _ at e
  rw [hrow, hw.map_bot, min_bot_left, min_eq_bot] at e
  exact e.resolve_right hfc

/-- **The gap of the band at a cap of the top grade** (`k < N`, so `N = k + 1`, the cut grade
`k + 1`), from two conditions on the context: the marker has grade at least `k`, and every cell of
the common face (the cells of `t'` avoiding its last point) is read by the cap as `⊥` or at least
at the marker.  A cell read as `⊥` is `⊥` under every prescription (`H3.eq_bot_of_rowAt_eq_bot`);
a cell read at least at the marker carries at least `min (f r) (f c)`
(`H3.min_marker_cap_le_of_rowAt_le`), which is at least the marker value replaced at `k`
(`Label.visibilityReplace_markerValue_le`: `f r` is self-visible at `grade r ≥ k`, `f c` at
`k + 1`); so the gap holds (`CapRequests.bandGapBelowAt_of_visibilityReplace_le`).  The cells
labelled `⊤` are read at least at the marker, which is least among them. -/
theorem bandGapBelowAt_top_of_rowAt (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hkN : k < t'.toCellScheme.grade c) (hrk : k ≤ t'.toCellScheme.grade r)
    (hface : ∀ z : Fin t'.card, Fin.last k ∉ t'.toCellScheme.scope z →
      t'.rowAt c z ≠ ⊥ → t'.rowAt c r ≤ t'.rowAt c z) :
    CapRequests.BandGapBelowAt (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega))
      (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k := by
  have hL := restrictFace_left_seed ht' hp htb
  have hn := hctx.2.2.1
  have hck : t'.toCellScheme.grade c ≤ k + 1 := t'.grade_le c
  have hN : t'.toCellScheme.grade c = k + 1 := by omega
  have hk0 : 0 < k := by omega
  have hK : t'.toCellScheme.grade c ≤ k + 1 := hck
  refine CapRequests.bandGapBelowAt_of_visibilityReplace_le
    fun h _ _ hb P _ _ f hf _ hfc e heC heD hhe ↦ ?_
  have hlast : Fin.last (k + 1) ∉ (seed ht' hp htb).amalgam.toCellScheme.scope e := fun hm ↦
    (mem_erase.mp (heC.1 hm)).1 rfl
  obtain ⟨z, rfl⟩ := exists_faceCell_eq_of_last_notMem hL hlast
  have hzl : Fin.last k ∉ t'.toCellScheme.scope z := fun hm ↦ by
    have h1 : Fin.castSucc (Fin.last k) ∈
        (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL z) := by
      rw [scope_faceCell]
      exact mem_map.mpr ⟨_, hm, rfl⟩
    exact (mem_erase.mp (heD.1 h1)).1 rfl
  have hgz : t'.toCellScheme.grade z ≤ k := by
    have h1 := t'.isWellFormed.isWellFormed.grade_le_card z
    have h2 : #(t'.toCellScheme.scope z) ≤ #(univ.erase (Fin.last k)) :=
      card_le_card fun x hx ↦ mem_erase.mpr ⟨fun h' ↦ hzl (h' ▸ hx), mem_univ _⟩
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at h2
    omega
  have hcap : f (faceCell hL c) ≠ ⊥ := (hb.trans hfc).ne'
  by_cases hz : t'.rowAt c z = ⊥
  · have := eq_bot_of_rowAt_eq_bot ht' hp htb hctx hK hf hcap (by omega) hz
    rw [this] at hhe
    exact absurd (le_bot_iff.mp hhe) hb.ne'
  have h1 := min_marker_cap_le_of_rowAt_le ht' hp htb hctx hK hf (hface z hzl hz) (by omega)
  obtain ⟨hord, -, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hf
  have hrC : faceCell hL r ∈ (seed ht' hp htb).amalgam.toCellScheme.below
      (univ.erase (Fin.last (k + 1)), k + 1) := by
    refine ⟨?_, ?_⟩
    · change (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL r) ⊆ _
      rw [scope_faceCell, ← Coatom.univ_map_left]
      exact map_subset_map.mpr (subset_univ _)
    · change (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL r) ≤ k + 1
      rw [grade_faceCell]; exact t'.grade_le r
  have hcC : faceCell hL c ∈ (seed ht' hp htb).amalgam.toCellScheme.below
      (univ.erase (Fin.last (k + 1)), k + 1) := by
    refine ⟨?_, ?_⟩
    · change (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL c) ⊆ _
      rw [scope_faceCell, ← Coatom.univ_map_left]
      exact map_subset_map.mpr (subset_univ _)
    · change (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL c) ≤ k + 1
      rw [grade_faceCell]; exact hck
  have har : IsSelfVisible k (f (faceCell hL r)) := by
    have := hord _ hrC
    rw [grade_faceCell] at this
    exact this.mono hrk
  have hac : IsSelfVisible (k + 1) (f (faceCell hL c)) := by
    have := hord _ hcC
    rw [grade_faceCell, hN] at this
    exact this
  refine le_trans ?_ h1
  change visibilityReplace k k (min (visibilityReplace (t'.toCellScheme.grade c) 0
    (f (faceCell hL r))) (f (faceCell hL c))) ≤ _
  rw [hN]
  exact Label.visibilityReplace_markerValue_le hk0 har hac

/-- At a context, a cell of grade at most that of the cap lies below the cap (of full scope). -/
theorem mem_below_cap {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r) {z : Fin t'.card}
    (hzc : t'.toCellScheme.grade z ≤ t'.toCellScheme.grade c) :
    z ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex c) := by
  change t'.toCellScheme.gradedIndex z ≤ t'.toCellScheme.gradedIndex c
  exact Prod.mk_le_mk.mpr ⟨by rw [hctx.1.1]; exact subset_univ _, hzc⟩

/-- **An ordinal-labelled cell is read by the cap strictly between `⊥` and the marker**, at a cell
of grade at most that of the marker: by locality of `t'` at the cap (labelled `⊤`), a row at
least that of the marker forces the label `⊤`, and the row `⊥` forces the label `⊥`. -/
theorem bot_lt_rowAt_lt_marker {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r) {z : Fin t'.card}
    (hgz : t'.toCellScheme.grade z ≤ t'.toCellScheme.grade r) (hzt : t'.label z ≠ ⊤)
    (hzb : t'.label z ≠ ⊥) : ⊥ < t'.rowAt c z ∧ t'.rowAt c z < t'.rowAt c r := by
  have hrc : r ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex c) := hctx.2.1.2.1
  have hrc' : t'.toCellScheme.grade r ≤ t'.toCellScheme.grade c := by
    rw [CellScheme.mem_below] at hrc
    exact (Prod.le_def.mp hrc).2
  have hzc := mem_below_cap hctx (hgz.trans hrc')
  refine ⟨bot_lt_iff_ne_bot.mpr fun h0 ↦ hzb ?_, lt_of_not_ge fun hle ↦ hzt ?_⟩
  · obtain ⟨g', σ, hw, heq⟩ := t'.isLawful.locality c
    have e := heq ⟨z, hzc⟩
    change min (t'.label z) (t'.label c) = _ at e
    rw [Scheme.rowAt_of_mem hzc] at h0
    rw [h0, hw.map_bot, min_bot_left, hctx.1.2.1, min_top_right] at e
    exact e
  · have h1 := (t'.isLawful.locality c).le_of_le (d := ⟨r, hrc⟩) (d' := ⟨z, hzc⟩)
      (by rw [← Scheme.rowAt_of_mem, ← Scheme.rowAt_of_mem]; exact hle) hgz
    change min (t'.label r) (t'.label c) ≤ min (t'.label z) (t'.label c) at h1
    rw [hctx.2.1.1, hctx.1.2.1, min_self, min_top_right] at h1
    exact top_le_iff.mp h1

/-- **The gap of the band at a cap of the top grade from the labels of the common face**: the
marker has grade at least `k`, and every cell of the common face is labelled `⊤`, or labelled `⊥`
and read by the cap as `⊥` (at the root cells labelled `⊥` this is
`StageType.RootBottomRespected`).  The cells labelled `⊤` are read at least at the marker, least
among them (`H3.bandGapBelowAt_top_of_rowAt`).  Conversely the condition of
`H3.bandGapBelowAt_top_of_rowAt` excludes ordinal labels on the common face
(`H3.bot_lt_rowAt_lt_marker`). -/
theorem bandGapBelowAt_top_of_labels (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hkN : k < t'.toCellScheme.grade c) (hrk : k ≤ t'.toCellScheme.grade r)
    (hlab : ∀ z : Fin t'.card, Fin.last k ∉ t'.toCellScheme.scope z →
      t'.label z = ⊤ ∨ (t'.label z = ⊥ ∧ t'.rowAt c z = ⊥)) :
    CapRequests.BandGapBelowAt (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega))
      (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k := by
  refine bandGapBelowAt_top_of_rowAt ht' hp htb hd hctx hkN hrk fun z hzl hz ↦ ?_
  rcases hlab z hzl with ht | ⟨-, hb⟩
  · exact hctx.2.1.2.2 z ht (mem_below_cap hctx ((t'.grade_le z).trans (by omega)))
  · exact absurd hb hz

/-- **The row condition at the top grade excludes ordinal labels on the common face**: under the
condition of `H3.bandGapBelowAt_top_of_rowAt`, every cell of the common face of grade at most that
of the marker is labelled `⊤` or `⊥` (`H3.bot_lt_rowAt_lt_marker`). -/
theorem label_eq_top_or_bot_of_rowAt {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hface : ∀ z : Fin t'.card, Fin.last k ∉ t'.toCellScheme.scope z →
      t'.rowAt c z ≠ ⊥ → t'.rowAt c r ≤ t'.rowAt c z)
    {z : Fin t'.card} (hzl : Fin.last k ∉ t'.toCellScheme.scope z)
    (hgz : t'.toCellScheme.grade z ≤ t'.toCellScheme.grade r) :
    t'.label z = ⊤ ∨ t'.label z = ⊥ := by
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2⟩ := bot_lt_rowAt_lt_marker hctx hgz hne.1 hne.2
  exact absurd (hface z hzl h1.ne') (not_le.mpr h2)

/-- **The gap of the band fails at an ordinal label of the common face at least `k + 1`.**  Take
the cap `h = k + 1` (self-visible and short at `k + 1`), `P` and `f` the labels of the amalgam
(correct: the cap, the marker and the new tops are `⊤`).  The marker value of `f` is `⊤`, so the
gap asks `⊤ ≤ c ≤ f z` at the cell `z`, whose label is an ordinal at least `h`. -/
theorem not_bandGapBelowAt_of_label (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hkN : k < t'.toCellScheme.grade c) {z : Fin t'.card}
    (hzl : Fin.last k ∉ t'.toCellScheme.scope z) {o : Ordinal.{u}}
    (hzo : t'.label z = (o : Label.{u})) (hko : ((k + 1 : ℕ) : Ordinal.{u}) ≤ o) :
    ¬ CapRequests.BandGapBelowAt (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega))
      (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k := by
  intro hgap
  have hL := restrictFace_left_seed ht' hp htb
  have hA := restrictFace_donor_seed ht' hp htb hd
  have hn := hctx.2.2.1
  have hck : t'.toCellScheme.grade c ≤ k + 1 := t'.grade_le c
  have hrc : t'.toCellScheme.grade r ≤ t'.toCellScheme.grade c := by
    have h := hctx.2.1.2.1
    rw [CellScheme.mem_below] at h
    exact (Prod.le_def.mp h).2
  have hgr := isGraded_requests ht' hp htb hd (r := r) (by omega) hrc hn
  set A := (seed ht' hp htb).amalgam
  have hglued : (requests ht' hp htb hd c r (by omega)).IsCorrect fun e ↦ A.label e :=
    CapRequests.isCorrect_of_forall (fun z hz ↦ absurd hz (Set.notMem_empty _))
      (fun f hf ↦ absurd hf (Set.notMem_empty _))
      fun y hy ↦ by
        obtain ⟨j, hj, -, rfl⟩ := hy
        rw [label_faceCell hA j, hj]; exact le_top
  have hP : ProfileTower.IsCutLawful (seed ht' hp htb) (k + 1) fun e ↦ A.label e :=
    ⟨A.isLawful.isLawfulBelow _, A.isLawful.isLawfulBelow _⟩
  have hcapt : A.label (faceCell hL c) = ⊤ := (label_faceCell hL c).trans hctx.1.2.1
  have hmt : A.label (faceCell hL r) = ⊤ := (label_faceCell hL r).trans hctx.2.1.1
  obtain ⟨c', -, -, hMc, hgapc⟩ := hgap ((k + 1 : ℕ) : Label.{u})
    ((isSelfVisible_natCast _).mpr le_rfl)
    (by
      rw [show ((k + 1 : ℕ) : Label.{u}) = (((k + 1 : ℕ) : Ordinal.{u}) : Label.{u}) from rfl,
        isShort_coe]
      rw [Ordinal.natCast_mod_omega0])
    (WithBot.bot_lt_coe _) (fun e ↦ A.label e) hP (hglued.hat hgr (k + 1)) (fun e ↦ A.label e)
    (A.isLawful.isLawfulBelow _) (fun _ _ ↦ rfl)
    (by change _ < A.label (faceCell hL c); rw [hcapt]; exact WithBot.coe_lt_coe.mpr
          (WithTop.coe_lt_top _))
  have hM : (requests ht' hp htb hd c r (by omega)).markerValue (fun e ↦ A.label e) = ⊤ := by
    change min (visibilityReplace _ 0 (A.label (faceCell hL r))) (A.label (faceCell hL c)) = ⊤
    rw [hmt, hcapt, visibilityReplace_top, min_self]
  rw [hM, top_le_iff] at hMc
  subst hMc
  have hzC : faceCell hL z ∈ A.toCellScheme.below (univ.erase (Fin.last (k + 1)), k + 1) := by
    refine ⟨?_, ?_⟩
    · change A.toCellScheme.scope (faceCell hL z) ⊆ _
      rw [scope_faceCell, ← Coatom.univ_map_left]
      exact map_subset_map.mpr (subset_univ _)
    · change A.toCellScheme.grade (faceCell hL z) ≤ k + 1
      rw [grade_faceCell]; exact t'.grade_le z
  have hzD : faceCell hL z ∈ A.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last k)), k) := by
    refine ⟨?_, ?_⟩
    · change A.toCellScheme.scope (faceCell hL z) ⊆ _
      rw [scope_faceCell]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      refine mem_erase.mpr ⟨fun h' ↦ hzl ?_, mem_univ _⟩
      have : y = Fin.last k := Fin.castSucc_injective _ h'
      exact this ▸ hy
    · change A.toCellScheme.grade (faceCell hL z) ≤ k
      rw [grade_faceCell]
      have h1 := t'.isWellFormed.isWellFormed.grade_le_card z
      have h2 : #(t'.toCellScheme.scope z) ≤ #(univ.erase (Fin.last k)) :=
        card_le_card fun x hx ↦ mem_erase.mpr ⟨fun h' ↦ hzl (h' ▸ hx), mem_univ _⟩
      rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at h2
      omega
  have hle := hgapc _ hzC hzD (by
    change _ ≤ A.label (faceCell hL z)
    rw [label_faceCell, hzo]
    exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hko))
  change ⊤ ≤ A.label (faceCell hL z) at hle
  rw [label_faceCell, hzo, top_le_iff] at hle
  exact WithTop.coe_ne_top (WithBot.coe_injective hle)

end Band

end H3

end VaughtConjecture
