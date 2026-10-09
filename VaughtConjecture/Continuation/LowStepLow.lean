/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStepTie
import VaughtConjecture.Continuation.LowTowerLevel
import VaughtConjecture.Continuation.H2GeneralBelow

/-!
# The tie case of the LOW step for every donor

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the LOW step from the
private coatom at the tie); semantic contract, items 3, 4 and 8.

The tie case `StageType.LowStepTie` was compiled for donors with a top of grade `K`
(`StageType.lowStepTie_of_top`: the raise of the ambient donor face through the row of a cell
labelled `⊤` of graded index `(univ, K)`), leaving the donors whose tops all have grades below `K`
(`StageType.LowStepTieLow`).  This file proves the tie case for every LOW family; in particular
`StageType.LowStepTieLow` holds.

**Raising below a gap** (`H2.lawfulAt_raise_below`, compiled in this repository).  Let `R` be
lawful at `K`, `j ≤ K`, and `h` a label with every cell of grade in `(j, K]` read by `R` below `h`.
A labelling `W` lawful at `j`, equal to `R` at the cells of grade at most `j` that `R` reads below
`h`, and at least `h` at those `R` reads at least at `h`, spliced with `R` above `j`, is lawful at
`K`.  The order and availability laws hold grade by grade.  At a cell `s` of grade at most `j` the
locality is that of `W`.  At a cell `s` of grade in `(j, K]` the locality is that of `R`: the label
of `s` is `R s < h`, and capping at it erases the change, since a changed cell `d` has both
`R d` and its new label at least `h > R s`.

**The raise of the tops** (`StageType.exists_raised_tops`, compiled in this repository).  In a
legal stage type `tb` of top grade at most `K`, let `R` be lawful at `K` with a gap at a positive
label `h`: every top read at least at `h`, every proper cell of grade at most `K` below `h`.  For
every `c` self-visible at `K`, some `W` lawful at `K` equals `R` at every proper cell and reads
every top at least at `c`.  Let `j` be the largest grade of a top and `Z` a cell labelled `⊤` of
graded index `(univ, j)` (availability).  The face `R` truncated above `j` is raised through the
row of `Z` (`StageType.exists_raised_at_top` at the grade `j`): the proper cells are read at
`min (R d) (R Z) = R d`, the tops at least at `c`.  The cells of grade in `(j, K]` are proper, so
the raise spliced with `R` above `j` is lawful at `K` by raising below the gap.  The reading grade
stays `K`; the template is needed only up to the grade of the tops.

**The tie case for every LOW family** (`StageType.IsLowFamily.lowStepTie`,
`StageType.IsLowFamily.lowStepTieLow`, compiled in this repository).  The ambient donor face `R`
has the gap at the cap `h` (the hypotheses of `StageType.LowStepTie`, with the root tops at least
`h` through the private face, which reads them at least at the frontier `c > h`).  Its raise at
`c` agrees with `R` capped at `h` and with the private face on the root capped at `c`, and the
capped lift at `c` from the root of the private face with this ambient (bountifulness of the
donor) is the face asked for, exactly as in `StageType.lowStepTie_of_top`.

**The capped lift into the LOW layer, and the LOW level, for every donor**
(`ProfileTower.Lvl.Good.cappedLift_lowS_seed'`, `ProfileTower.Lvl.Good.lowNext'`, compiled in this
repository): the statements of `ProfileTower.Lvl.Good.cappedLift_lowS_seed` and
`ProfileTower.Lvl.Good.lowNext` without the donor top of grade `g + 1`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType

variable {α : Ordinal.{u}} {n : ℕ}

/-- **Raising below a gap.**  Let `R` be lawful at `K`, `j ≤ K`, and `h` a label such that `R`
reads every cell of grade in `(j, K]` below `h` (`hmid`).  If `W` is lawful at `j`, equals `R` at
every cell of grade at most `j` read by `R` below `h` (`hlo`), and is at least `h` at every cell of
grade at most `j` read by `R` at least at `h` (`hhi`), then `V`, equal to `W` at the cells of grade
at most `j` and to `R` at the others, is lawful at `K`.

*Which cells change.*  `V` differs from `R` only at cells of grade at most `j` that `R` reads at
least at `h` (by `hlo`), and there `V` is at least `h` (by `hhi`).  Above `K`, `V = R = ⊥`.

*The three laws* (checked pointwise, `CellScheme.Rows.isLawfulBelow_iff_forall`).  Order: at a cell
of grade at most `j` it is the order law of `W`, at the others that of `R`.  Availability: the
cells compared have equal grades, so both lie at most `j` (availability of `W`, the cell found has
the same grade) or both above (availability of `R`).  Locality at a cell `s`: if the grade of `s`
is at most `j`, so is that of every cell below `s`, and the target `d ↦ min (V d) (V s)` is
`d ↦ min (W d) (W s)` (locality of `W`).  If the grade of `s` is in `(j, K]`, then `V s = R s < h`
by `hmid`, and the target is `d ↦ min (R d) (R s)` (locality of `R`): at a cell `d` with `R d < h`,
`V d = R d`; at a cell `d` with `R d ≥ h`, both `V d` and `R d` are at least `h > R s`, so both
minima are `R s`.  The capping by the label `R s < h` of the reader erases the change.  This is the
only place `hmid` is used. -/
theorem lawfulAt_raise_below {t : StageType.{u} α n} {j K : ℕ} (hjK : j ≤ K) {h : Label.{u}}
    {R W : Fin t.card → Label.{u}} (hR : LawfulAt t K R) (hW : LawfulAt t j W)
    (hmid : ∀ d, j < t.toCellScheme.grade d → t.toCellScheme.grade d ≤ K → R d < h)
    (hlo : ∀ d, t.toCellScheme.grade d ≤ j → R d < h → W d = R d)
    (hhi : ∀ d, t.toCellScheme.grade d ≤ j → h ≤ R d → h ≤ W d) :
    LawfulAt t K fun d ↦ if t.toCellScheme.grade d ≤ j then W d else R d := by
  classical
  obtain ⟨hRo, hRl, hRa⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hR.1
  obtain ⟨hWo, hWl, hWa⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hW.1
  refine ⟨(CellScheme.Rows.isLawfulBelow_iff_forall
    (w := fun d ↦ if t.toCellScheme.grade d ≤ j then W d else R d)).mpr
    ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s u hu hsu hg ↦ ?_⟩, fun d hd ↦ ?_⟩
  · -- order
    split_ifs with hdj
    · exact hWo d ⟨subset_univ _, hdj⟩
    · exact hRo d hd
  · -- locality
    by_cases hsj : t.toCellScheme.grade s ≤ j
    · have he : (fun d : t.toCellScheme.below (t.toCellScheme.gradedIndex s) ↦
          min (if t.toCellScheme.grade d.1 ≤ j then W d.1 else R d.1)
            (if t.toCellScheme.grade s ≤ j then W s else R s)) =
          fun d ↦ min (W d.1) (W s) := by
        funext d
        have hdj : t.toCellScheme.grade d.1 ≤ j := d.2.2.trans hsj
        rw [ite_eq_left hdj, ite_eq_left hsj]
      rw [he]
      exact hWl s ⟨subset_univ _, hsj⟩
    · have hRs : R s < h := hmid s (not_le.mp hsj) hs.2
      have he : (fun d : t.toCellScheme.below (t.toCellScheme.gradedIndex s) ↦
          min (if t.toCellScheme.grade d.1 ≤ j then W d.1 else R d.1)
            (if t.toCellScheme.grade s ≤ j then W s else R s)) =
          fun d ↦ min (R d.1) (R s) := by
        funext d
        rw [ite_eq_right hsj]
        split_ifs with hdj
        · rcases lt_or_ge (R d.1) h with hd | hd
          · rw [hlo d.1 hdj hd]
          · rw [min_eq_right (hRs.le.trans (hhi d.1 hdj hd)), min_eq_right (hRs.le.trans hd)]
        · rfl
      rw [he]
      exact hRl s hs
  · -- availability
    have hgu (v : Fin t.card) (hv : t.toCellScheme.gradedIndex v = t.toCellScheme.gradedIndex u) :
        t.toCellScheme.grade v = t.toCellScheme.grade u := congrArg Prod.snd hv
    by_cases huj : t.toCellScheme.grade u ≤ j
    · obtain ⟨v, hv, hle⟩ := hWa s u ⟨subset_univ _, huj⟩ hsu hg
      refine ⟨v, hv, ?_⟩
      rw [ite_eq_left (hg ▸ huj), ite_eq_left ((hgu v hv).trans_le huj)]
      exact hle
    · obtain ⟨v, hv, hle⟩ := hRa s u hu hsu hg
      refine ⟨v, hv, ?_⟩
      rw [ite_eq_right (hg ▸ huj), ite_eq_right (by rw [hgu v hv]; exact huj)]
      exact hle
  · -- above `K`
    exact (ite_eq_right fun (h' : t.toCellScheme.grade d ≤ j) ↦ hd (h'.trans hjK)).trans
      (hR.2 d hd)

end VaughtConjecture.H2

namespace VaughtConjecture.StageType

open Finset Label H2

variable {α : Ordinal.{u}} {n : ℕ}

/-- **The raise of the tops.**  In a legal stage type `tb` on `n` points of top grade at most
`K ≤ n` (`htg`), let `R` be lawful at `K` with a gap at a positive label `h`: every cell labelled
`⊤` read at least at `h` (`htop`), every other cell of grade at most `K` below `h` (`hlow`).  For
every `c` self-visible at `K`, some `W` lawful at `K` equals `R` at every cell not labelled `⊤`
and reads every cell labelled `⊤` at least at `c`.

*Construction.*  Without tops, `W = R`.  Otherwise `j` is the largest grade of a top (so every top
has grade at most `j`, and `j ≤ K` by `htg`), `Z` a cell labelled `⊤` of graded index `(univ, j)`
(`StageType.exists_top_cell_univ`).  `W'` is the raise of `R` truncated above `j` through the row
of `Z` at the grade `j` (`StageType.exists_raised_at_top`, with `c` self-visible at `j ≤ K`): it
reads a proper cell `d` of grade at most `j` as `min (R d) (R Z)`, which is `R d` since
`R d < h ≤ R Z` (`hlow` and `htop` at `Z`), and every top `d` as `max (min (R d) (R Z)) c ≥ c`
(`R d ≠ ⊥` by `htop` and `⊥ < h`).  Then `W` is `W'` at the cells of grade at most `j` and `R`
above (`H2.lawfulAt_raise_below`).

*Which cells change.*  Only the tops, all of grade at most `j`: every proper cell keeps `R`.

*Hypotheses of the splice.*  `hmid`: a cell of grade in `(j, K]` is not a top (maximality of `j`),
so `R` reads it below `h` by `hlow`.  `hlo`: a cell of grade at most `j` read below `h` is not a
top (`htop`), so it keeps `R`.  `hhi`: a cell of grade at most `j` read at least at `h` is a top
(`hlow`), read by `W'` at least at `min (R d) (R Z) ≥ h`.

Capped agreement with `R` at `h` and literalness on a root are not claimed here; they are
established in `StageType.IsLowFamily.lowStepTie`. -/
theorem exists_raised_tops {tb : StageType.{u} α n} (htb : tb.IsLegal) {K : ℕ} (hKn : K ≤ n)
    (htg : tb.topGrade ≤ K) {R : Fin tb.card → Label.{u}} (hR : LawfulAt tb K R)
    {h c : Label.{u}} (hb : ⊥ < h) (hc : IsSelfVisible K c)
    (htop : ∀ d, tb.label d = ⊤ → h ≤ R d)
    (hlow : ∀ d, tb.label d ≠ ⊤ → tb.toCellScheme.grade d ≤ K → R d < h) :
    ∃ W : Fin tb.card → Label.{u}, LawfulAt tb K W ∧ (∀ d, tb.label d ≠ ⊤ → W d = R d) ∧
      ∀ d, tb.label d = ⊤ → c ≤ W d := by
  classical
  by_cases hT : (univ.filter fun x : Fin tb.card ↦ tb.label x = ⊤).Nonempty
  swap
  · refine ⟨R, hR, fun _ _ ↦ rfl, fun d hd ↦ absurd ⟨d, mem_filter.mpr ⟨mem_univ _, hd⟩⟩ hT⟩
  obtain ⟨x, hxT, hxmax⟩ := Finset.exists_max_image _ tb.toCellScheme.grade hT
  have hx : tb.label x = ⊤ := (mem_filter.mp hxT).2
  set j := tb.toCellScheme.grade x with hj
  have hmax (y : Fin tb.card) (hy : tb.label y = ⊤) : tb.toCellScheme.grade y ≤ j :=
    hxmax y (mem_filter.mpr ⟨mem_univ _, hy⟩)
  have hj0 : 0 < j := tb.isWellFormed.isWellFormed.grade_pos x
  have hjK : j ≤ K := topGrade_le_iff.mp htg x hx
  obtain ⟨Z, hZ, hZi⟩ := exists_top_cell_univ htb hx
  have hgZ : tb.toCellScheme.grade Z = j := congrArg Prod.snd hZi
  set W₁ : Fin tb.card → Label.{u} := fun d ↦ if tb.toCellScheme.grade d ≤ j then R d else ⊥
    with hW₁_def
  have hW₁ : LawfulAt tb j W₁ := lawfulAt_trunc hR.1 hjK
  have hW₁le (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ j) : W₁ d = R d :=
    ite_eq_left hd
  have hRZ : h ≤ R Z := htop Z hZ
  have hZ0 : W₁ Z ≠ ⊥ := by rw [hW₁le Z hgZ.le]; exact ne_bot_of_gt (hb.trans_le hRZ)
  obtain ⟨W', hW', hW'p, -, hW't⟩ :=
    exists_raised_at_top htb hj0 (hjK.trans hKn) hZ hZi hW₁ hZ0 (hc.mono hjK)
  -- the raise keeps every proper cell of grade at most `j`
  have hp' (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ j) (hdt : tb.label d ≠ ⊤) :
      W' d = R d := by
    rw [hW'p d hd hdt, hW₁le d hd, hW₁le Z hgZ.le]
    exact min_eq_left ((hlow d hdt (hd.trans hjK)).le.trans hRZ)
  -- and reads every top at least at `c`
  have ht' (d : Fin tb.card) (hdt : tb.label d = ⊤) : c ≤ W' d := by
    have hd := hmax d hdt
    have h0 : W₁ d ≠ ⊥ := by rw [hW₁le d hd]; exact ne_bot_of_gt (hb.trans_le (htop d hdt))
    rw [hW't d hd hdt h0]
    exact le_max_right _ _
  have hmid (d : Fin tb.card) (hjd : j < tb.toCellScheme.grade d)
      (hdK : tb.toCellScheme.grade d ≤ K) : R d < h :=
    hlow d (fun hdt ↦ absurd (hmax d hdt) (not_le.mpr hjd)) hdK
  have hlo (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ j) (hRd : R d < h) : W' d = R d :=
    hp' d hd fun hdt ↦ absurd (htop d hdt) (not_le.mpr hRd)
  have hhi (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ j) (hRd : h ≤ R d) : h ≤ W' d := by
    by_cases hdt : tb.label d = ⊤
    · rw [hW't d hd hdt (by rw [hW₁le d hd]; exact ne_bot_of_gt (hb.trans_le hRd)),
        hW₁le d hd, hW₁le Z hgZ.le]
      exact (le_min hRd hRZ).trans (le_max_left _ _)
    · exact absurd (hlow d hdt (hd.trans hjK)) (not_lt.mpr hRd)
  refine ⟨_, lawfulAt_raise_below hjK hR hW' hmid hlo hhi, fun d hdt ↦ ?_, fun d hdt ↦ ?_⟩
  · split_ifs with hd
    · exact hp' d hd hdt
    · rfl
  · rw [ite_eq_left (hmax d hdt)]
    exact ht' d hdt

variable {k K : ℕ} {t' tb : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {o r : Fin t'.card}

/-- **The tie case holds at every LOW family**, indeed the conclusion of `StageType.LowStepTie`
without its tie premise.

*The gap.*  Every top `d` of the donor has `h ≤ R d`: off the root by the hypothesis of the tie
case, on the root because the private face reads its copy at least at the frontier `c > h` (strict
source gaps, `H2.frontier_le_lawfulAt`) and agrees there with `R` capped at `h`.  Every proper cell
of grade at most `K` has `R d < h` (hypothesis of the tie case).  So `StageType.exists_raised_tops`
gives `W'` lawful at `K`, equal to `R` at every proper cell, at least `c` at every top.

*Capped agreement at `h`* (`W'` with `R`): at proper cells `W' = R`; at tops both are at least `h`
(`W' ≥ c > h`).

*Agreement on the root capped at `c`* (`W'` with the private face `f`): at a root top both are at
least `c`; at a proper root cell of grade at most `K`, `R < h` and `f` agrees with `R` capped at
`h`, so `f = R = W'`; above `K` both are `⊥`.

*Literal root.*  The capped lift at `c` from the root of `f` with the ambient `W'`
(`H2.hasCappedLifts_lawfulAt'`, bountifulness of the donor) gives `W` lawful at `K`, equal to `f`
at every root cell, and agreeing with `W'` capped at `c`.  The root cells that `W'` moved are the
root tops (to at least `c`), and `W` puts them back to `f` exactly; no other root cell moved.
From the capped agreement at `c`: `W` agrees with `R` capped at `h` (since `h < c`), and reads
every top off the root at least at `c`. -/
theorem IsLowFamily.lowStepTie (hF : IsLowFamily K t' tb p o r) :
    LowStepTie K t' tb hF.face_private hF.face_donor o r := by
  classical
  intro h c hh hb hhc R f hR hf hag hc htop hlow _
  have hs := hF.isSourceGapContextAt
  have hK0 : 0 < K := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  have hKk : K ≤ k + 1 := hs.grade_owner ▸ t'.grade_le o
  have hfo := frontier_le_lawfulAt hF.isLegal_private hs hf
  have hcv : IsSelfVisible K c := by
    rw [hc]
    rcases min_choice (f o) (visibilityReplace K K (f r)) with h1 | h1 <;> rw [h1]
    · exact hfo.1
    · exact visibilityReplace_self_visibilityReplace le_rfl _
  -- the root tops of `f` are at least `c`
  have hroot_top (x : Fin p.card) (hx : tb.label (faceCell hF.face_donor x) = ⊤) :
      c ≤ f (faceCell hF.face_private x) := by
    rw [hc]
    refine hfo.2 _ ?_ (last_notMem_scope_faceCell hF.face_private x)
    rw [label_faceCell, ← label_faceCell hF.face_donor x]
    exact hx
  -- every top of `R` is at least `h`
  have hRh (d : Fin tb.card) (hd : tb.label d = ⊤) : h ≤ R d := by
    by_cases hv : d ∈ tb.toScheme.visibleCells Fin.castSuccEmb
    · obtain ⟨x, rfl⟩ := exists_faceCell_eq hF.face_donor hv
      have h1 := hag x
      have h2 : h ≤ f (faceCell hF.face_private x) := hhc.le.trans (hroot_top x hd)
      rw [min_eq_right h2] at h1
      exact min_eq_right_iff.mp h1.symm
    · exact htop d hd (hF.grade_le hd) hv
  obtain ⟨W', hW', hW'p, hW't⟩ :=
    exists_raised_tops hF.isLegal_donor hKk hF.topGrade_donor hR hb hcv hRh hlow
  -- `W'` agrees with `R` capped at `h`
  have hW'R (d : Fin tb.card) : min (W' d) h = min (R d) h := by
    by_cases hdt : tb.label d = ⊤
    · rw [min_eq_right (hhc.le.trans (hW't d hdt)), min_eq_right (hRh d hdt)]
    · rw [hW'p d hdt]
  -- the root of `f` agrees with `W'` capped at `c`
  have hagc (x : Fin p.card) :
      min (f (faceCell hF.face_private x)) c = min (W' (faceCell hF.face_donor x)) c := by
    set d := faceCell hF.face_donor x
    have hgd : tb.toCellScheme.grade d = t'.toCellScheme.grade (faceCell hF.face_private x) := by
      rw [grade_faceCell, grade_faceCell]
    by_cases hdt : tb.label d = ⊤
    · rw [min_eq_right (hroot_top x hdt), min_eq_right (hW't d hdt)]
    · rw [hW'p d hdt]
      by_cases hdK : tb.toCellScheme.grade d ≤ K
      · have hRd := hlow d hdt hdK
        have hfx : f (faceCell hF.face_private x) = R d := eq_of_min_eq_of_lt (hag x).symm hRd
        rw [hfx]
      · rw [hR.2 d hdK, hf.2 _ (hgd ▸ hdK)]
  obtain ⟨W, hW, hWr, hWc⟩ := hasCappedLifts_lawfulAt' hK0 hKk hF.isLegal_private
    hF.face_private hF.isLegal_donor hF.face_donor hcv hW' hf hagc
  refine ⟨W, hW, hWr, fun d ↦ ?_, fun d hd _ _ ↦ ?_⟩
  · calc min (W d) h = min (min (W d) c) h := by rw [min_assoc, min_eq_right hhc.le]
      _ = min (min (W' d) c) h := by rw [hWc d]
      _ = min (W' d) h := by rw [min_assoc, min_eq_right hhc.le]
      _ = min (R d) h := hW'R d
  · have h2 := hWc d
    rw [min_eq_right (hW't d hd)] at h2
    exact min_eq_right_iff.mp h2

/-- **The case of a donor without a top of grade `K` holds** at every LOW family
(`StageType.IsLowFamily.lowStepTie`). -/
theorem IsLowFamily.lowStepTieLow (hF : IsLowFamily K t' tb p o r) :
    LowStepTieLow K t' tb hF.face_private hF.face_donor o r :=
  fun _ ↦ hF.lowStepTie

end VaughtConjecture.StageType

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The capped lift from either coatom into the LOW layer for the seed's designations, for every
donor**: `ProfileTower.Lvl.Good.cappedLift_lowS_seed` without a donor top of grade `g + 1`, by
`ProfileTower.Lvl.Good.cappedLift_lowS_seed_of_low` and `StageType.IsLowFamily.lowStepTieLow`. -/
theorem Lvl.Good.cappedLift_lowS_seed' {g : ℕ} {L : Lvl I g} (hL : L.Good) (hgm : g + 1 ≤ m)
    {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ g + 1) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    (L.lowS (lowCat I (g + 1) (lowN I (g + 1)) (lowT I)
      (StageType.faceCell I.restrictFace_left o')
      (StageType.faceCell I.restrictFace_left r'))).rows.CappedLift
      (X := (univ.erase x, g + 1)) (Y := ((univ : Finset (Fin (m + 2))), g + 1))
      ⟨erase_subset _ _, le_rfl⟩ :=
  hL.cappedLift_lowS_seed_of_low hgm hs htb
    (StageType.IsLowFamily.lowStepTieLow (hF := ⟨I.isLegal_left, I.isLegal_right,
      I.restrictFace_face_left, I.restrictFace_face_right, hs, htb⟩)) hx

/-- **The LOW layer over a good level is a good level, for every donor**:
`ProfileTower.Lvl.Good.lowNext` without a donor top of grade `g + 1`, from
`ProfileTower.Lvl.Good.cappedLift_lowS_seed'`. -/
theorem Lvl.Good.lowNext' {g : ℕ} {L : Lvl I g} (hL : L.Good) (hgm : g + 1 ≤ m)
    {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ g + 1) :
    (L.catNext (lowPred (g + 1) (lowN I (g + 1)) (lowT I)
      (StageType.faceCell I.restrictFace_left o')
      (StageType.faceCell I.restrictFace_left r'))).Good :=
  hL.catNext hgm lowPred_withCut_bot fun _ hx ↦ hL.cappedLift_lowS_seed' hgm hs htb hx

end VaughtConjecture.ProfileTower
