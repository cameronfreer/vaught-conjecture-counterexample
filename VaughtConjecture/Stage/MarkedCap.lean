/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Band
import VaughtConjecture.Stage.Threshold
import VaughtConjecture.Stage.TopFree

/-!
# Marked caps: forced thresholds are read by the row of a top cap

Roadmap, Layer 3 ((R3) of the table of 3.4: the hollow context, with its private cap and
marker).  Everything here concerns labels and stage types only: no
realization and no model is involved.

Throughout, `β` is a limit stage and `α ≥ β + ω`; in the application `β = λ_ξ` and
`α = λ_{ξ+1}` are consecutive block stages.

**The splice of two witnesses** (`Label.TransformsTo.splice_bandMap`, compiled in this repository
(theorem named)) is in `Label/Band`; the band lift below uses it at every cell labelled `⊤`.

**Top caps and markers.**  A **top cap** of a stage type `q` (`StageType.IsTopCap`) is a cell of
full scope labelled `⊤` whose grade `N` is the largest grade of a cell labelled `⊤`; every cell
labelled `⊤` lies below it (`StageType.IsTopCap.mem_below`), and a legal stage type that is not
top-free has one (`StageType.exists_isTopCap`, from completeness and availability).  A **marker**
of a cell `c` (`StageType.IsMarker`) is a cell below `c` labelled `⊤` at which the row of `c`, read
with `Scheme.rowAt`, is least among the cells below `c` labelled `⊤`; every cell labelled `⊤` has
one (`StageType.exists_isMarker`, no hypothesis).

**The band lift** (`StageType.IsMarker.exists_lift`, compiled in this repository (theorem named)).
For a legal `q` at `β` with a top cap `c` of grade `N` and a marker `r`, the row of `c` reads `r`
at an ordinal `μ + j` (`μ` zero or a limit), and the labelling equal to `q` below `β` and to the
band map from `μ` to `β` at `N` of the row of `c` at the cells labelled `⊤` is a lawful lift of
`q` to `α`.  Order: the rows are orderly.  Availability at a cell labelled `⊤`: availability of
the row of `c` (lawful below `c` by consistency), whose cell is labelled `⊤` by locality of `q` at
`c`.  Locality at a cell `s` labelled `⊤`: the splice of locality of `q` at `s` with locality at
`s` of the row of `c`.  The other cells keep the laws of `q`.

**Forcing is read by the rows** (`StageType.IsMarker.le_grade_and_visibilityReplace_rowAt_le`,
`StageType.ForcesThreshold.le_grade_and_visibilityReplace_rowAt_le`, compiled in this repository
(theorem named)).  Cover-hollowness reads the provisional values of the tops through forcing
(every lift of a rooted cover); the hollow construction of the roadmap (Layer 3, 3.3: the private
cap and the marker labelled `⊤`, and the marker clause of `Correct`) reads them through the row of
a top cap, the **row reading**.  The implication holds: if `(q, f)` forces the threshold `L` at a
cell of the root labelled `⊤`, transported to the cell `e` of `q`, then for every top cap `c` of
grade `N` and every marker `r` of `c`, `L ≤ N` and
`visibilityReplace N L (q.rowAt c r) ≤ q.rowAt c e`.  The band lift has the label `β + min j' N`
at `e` when the row of `c` reads `e` in the block of the marker, at `μ + j'`, and `β + N`
otherwise; forcing `L` makes it at least `β + L`.  Where the inequality says something (the marker
read at `μ + j` with `j < N`), it gives `q.rowAt c e ≥ μ + L`.  When the forcing comes from the
order law or from the rows (`StageType.forcesThreshold_of_row_le_of_grade_le`), this already
follows from the minimality of the marker; the content of the statement lies in thresholds forced
by all lifts in some other way, which no compiled instance exhibits.

**The marked-cap context** (`StageType.IsMarkedCapContext`, defined in this repository; acquisition
proved, general determination open).  A stage type `t'` on `k` points is a marked-cap context along
`h : Fin n ↪ Fin k` when it has a top cap `c` of grade `N > n + 1` and a marker `r` of `c` with
`visibilityReplace N (n + 1) (t'.rowAt c r) ≤ t'.rowAt c a` at every cell `a` of the root (visible
through `h`) labelled `⊤`.  The finite step from forcing is compiled: a legal rooted cover with a
top cap of grade above `n + 1` that forces `n + 1` at every cell of its root labelled `⊤` is a
marked-cap context (`StageType.isMarkedCapContext_of_forcesThreshold`).  A marked-cap context is
not top-free (`StageType.IsMarkedCapContext.not_isTopFree`), so a context on no points is not one
(`StageType.not_isMarkedCapContext_of_zero`), and neither is a context whose cells labelled `⊤`
have grades at most `n + 1` (`StageType.not_isMarkedCapContext_of_grade_le`).  The
statements with the top grade, the form at a cover-hollow realization, and the exclusion of the
determination counterexamples are in `VaughtConjecture.Continuation.MarkedCap`.

Acquisition (`Realization.HollowAcquisition` for this predicate) is proved
(`Realization.hollowAcquisition_isMarkedCapContext`, in
`VaughtConjecture.Continuation.MarkedCarrierAcquisition`).  Determination in general
(`Realization.SchemeDetermination` or `Realization.CutoffDetermination` for it) is open, and
nothing here proves (R3).

## Placement

This file belongs to Layer 1 of `roadmap/README.md`; the splice and its lemmas about the band map
are in `Label/Band`.

## References

The band map and the band rule are the post-composition in the proof of [Kni26, Lemma 5.3.5];
the transformation relation is [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Finset Order
open scoped Ordinal

namespace Label

section Helper

variable {β : Ordinal.{u}}

/-- A label between an ordinal and a stage is an ordinal below the stage. -/
private theorem exists_coe_eq_of_le_of_lt {x : Label.{u}} {o : Ordinal.{u}}
    (h₀ : (o : Label.{u}) ≤ x) (h : x < β) : ∃ ν : Ordinal.{u}, x = ν ∧ ν < β := by
  induction x using recBotCoeTop with
  | bot => exact absurd h₀ (not_le.mpr (WithBot.bot_lt_coe _))
  | coe ν => exact ⟨ν, rfl, WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h)⟩
  | top => exact absurd h (not_lt.mpr le_top)

end Helper

end Label

namespace StageType

open Label

variable {α β : Ordinal.{u}} {m k n : ℕ} {q : StageType.{u} β m} {c r e : Fin q.card}

/-! ### Top caps and markers -/

/-- A **top cap** of `q`: a cell of full scope labelled `⊤` whose grade is at least the grade of
every cell labelled `⊤`, so that its grade is the largest grade of a cell labelled `⊤`. -/
def IsTopCap (q : StageType.{u} β m) (c : Fin q.card) : Prop :=
  q.toCellScheme.scope c = univ ∧ q.label c = ⊤ ∧
    ∀ x, q.label x = ⊤ → q.toCellScheme.grade x ≤ q.toCellScheme.grade c

/-- Every cell labelled `⊤` lies below a top cap. -/
theorem IsTopCap.mem_below (hc : q.IsTopCap c) {x : Fin q.card} (hx : q.label x = ⊤) :
    x ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex c) := by
  -- membership below `c` is the comparison of graded indices
  change q.toCellScheme.gradedIndex x ≤ q.toCellScheme.gradedIndex c
  exact Prod.mk_le_mk.mpr ⟨by rw [hc.1]; exact subset_univ _,
    hc.2.2 x hx⟩

/-- **A legal stage type with a cell labelled `⊤` has a top cap**: completeness gives a cell of
full scope at the largest grade `K` of a cell labelled `⊤`, and availability gives one such cell
labelled `⊤`. -/
theorem exists_isTopCap (hq : q.IsLegal) (h : ¬ q.IsTopFree) : ∃ c, q.IsTopCap c := by
  classical
  set T := univ.filter fun d : Fin q.card ↦ q.label d = ⊤
  have hT : T.Nonempty := by
    obtain ⟨s, hs⟩ : ∃ s, q.label s = ⊤ := by
      by_contra h'
      exact h fun d hd ↦ h' ⟨d, hd⟩
    exact ⟨s, mem_filter.mpr ⟨mem_univ _, hs⟩⟩
  obtain ⟨E, hE, hEmax⟩ := T.exists_max_image (fun d ↦ q.toCellScheme.grade d) hT
  have hEt : q.label E = ⊤ := (mem_filter.mp hE).2
  have hpos : 0 < q.toCellScheme.grade E := q.isWellFormed.isWellFormed.grade_pos E
  obtain ⟨D', hD'⟩ := hq.isComplete ((univ : Finset (Fin m)), q.toCellScheme.grade E)
    ⟨q.univ_mem_faces, hpos, by
      -- the second component of the pair is the grade, the first the whole ground set
      change q.toCellScheme.grade E ≤ #(Finset.univ : Finset (Fin m))
      rw [Finset.card_univ, Fintype.card_fin]
      exact q.grade_le E⟩
  have hD's : q.toCellScheme.scope D' = univ := congrArg Prod.fst hD'
  have hD'g : q.toCellScheme.grade D' = q.toCellScheme.grade E := congrArg Prod.snd hD'
  obtain ⟨C, hC, hEC⟩ := q.isLawful.availability E D' (hD's ▸ subset_univ _) hD'g.symm
  have hCi : q.toCellScheme.gradedIndex C = (univ, q.toCellScheme.grade E) := hC.trans hD'
  refine ⟨C, congrArg Prod.fst hCi, top_le_iff.mp (hEt ▸ hEC), fun x hx ↦ ?_⟩
  rw [show q.toCellScheme.grade C = q.toCellScheme.grade E from congrArg Prod.snd hCi]
  exact hEmax x (mem_filter.mpr ⟨mem_univ _, hx⟩)

/-- A **marker** of the cell `c`: a cell below `c` labelled `⊤` at which the row of `c` is least
among the cells below `c` labelled `⊤`. -/
def IsMarker (q : StageType.{u} β m) (c r : Fin q.card) : Prop :=
  q.label r = ⊤ ∧ r ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex c) ∧
    ∀ x, q.label x = ⊤ → x ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex c) →
      q.rowAt c r ≤ q.rowAt c x

/-- **Every cell labelled `⊤` has a marker**: the cells below it labelled `⊤` form a finite set
containing the cell itself, and the row takes a least value on it. -/
theorem exists_isMarker (hc : q.label c = ⊤) : ∃ r, q.IsMarker c r := by
  classical
  set S := univ.filter fun x : Fin q.card ↦
    q.label x = ⊤ ∧ x ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex c)
  have hS : S.Nonempty :=
    ⟨c, mem_filter.mpr ⟨mem_univ _, hc, q.toCellScheme.mem_below_gradedIndex c⟩⟩
  obtain ⟨r, hr, hmin⟩ := S.exists_min_image (q.rowAt c) hS
  obtain ⟨-, hrt, hrc⟩ := mem_filter.mp hr
  exact ⟨r, hrt, hrc, fun x hx hxc ↦ hmin x (mem_filter.mpr ⟨mem_univ _, hx, hxc⟩)⟩

/-! ### The band lift of the marker's block -/

/-- **The band lift.**  Let `β` be a limit, `β + ω ≤ α`, `q` a legal stage type at `β`, `c` a top
cap of `q` of grade `N`, and `r` a marker of `c`.  The entry of the row of `c` at `r` is `μ + j`
with `μ` zero or a limit, and some stage type at `α` reducing to `q` carries, at every cell `d`
labelled `⊤` in `q`, the band map from `μ` to `β` at `N` of the row of `c` read at `d`.

The labels below `β` are kept.  Order: the rows are orderly, and the band map keeps
self-visibility at the grades at most `N`.  Availability: at a cell labelled `⊤` it is
availability of the row of `c`, which is lawful below `c`; the cell it gives is labelled `⊤` by
locality of `q` at `c`.  Locality at a cell `s` labelled `⊤` is the splice
(`Label.TransformsTo.splice_bandMap`) of locality of `q` at `s` with locality at `s` of the row of
`c`; at the other cells it is locality of `q`. -/
theorem IsMarker.exists_lift (hβ : IsSuccLimit β) (hα : β + ω ≤ α) (hq : q.IsLegal)
    (hc : q.IsTopCap c) (hr : q.IsMarker c r) :
    ∃ (μ : Ordinal.{u}) (j : ℕ), IsSuccPrelimit μ ∧
      q.rowAt c r = ((μ + j : Ordinal.{u}) : Label.{u}) ∧
      ∃ Q : StageType.{u} α m, Q.reduce hβ.isSuccPrelimit = q ∧
        ∀ (d : Fin q.card) (d' : Fin Q.card), (d' : ℕ) = d → q.label d = ⊤ →
          Q.label d' = bandMap β μ (q.toCellScheme.grade c) (q.rowAt c d) := by
  classical
  have hβ' := hβ.isSuccPrelimit
  set N := q.toCellScheme.grade c
  obtain ⟨hrt, hrc, hrmin⟩ := hr
  -- the entry at the marker is an ordinal `μ + j`
  have hne_bot : q.rowAt c r ≠ ⊥ := by
    intro h
    rw [Scheme.rowAt_of_mem hrc] at h
    have := (q.isLawful.locality c).eq_bot (d := ⟨r, hrc⟩) h
    rw [hrt, hc.2.1, min_self] at this
    exact top_ne_bot this
  have hne_top : q.rowAt c r ≠ ⊤ := ((q.isCoded.rowAt_lt c r).trans_le le_top).ne
  obtain ⟨o, ho⟩ : ∃ o : Ordinal.{u}, q.rowAt c r = o := by
    induction h : q.rowAt c r using recBotCoeTop with
    | bot => exact absurd h hne_bot
    | coe o => exact ⟨o, rfl⟩
    | top => exact absurd h hne_top
  obtain ⟨μ, hμ, j, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o
  have hμle (d : Fin q.card) (hd : q.label d = ⊤) : (μ : Label.{u}) ≤ q.rowAt c d :=
    (ho ▸ coe_le_coe_add μ j).trans (hrmin d hd (hc.mem_below hd))
  have hband_ge (d : Fin q.card) (hd : q.label d = ⊤) :
      (β : Label.{u}) ≤ bandMap β μ N (q.rowAt c d) :=
    coe_le_bandMap ((WithBot.bot_lt_coe _).trans_le (hμle d hd)).ne'
  -- the labels of the lift
  set ℓ : Fin q.card → Label.{u} := fun d ↦
    if q.label d = ⊤ then bandMap β μ N (q.rowAt c d) else q.label d
  have hℓtop (d : Fin q.card) (hd : q.label d = ⊤) : ℓ d = bandMap β μ N (q.rowAt c d) :=
    ite_eq_left hd
  have hℓlow (d : Fin q.card) (hd : q.label d ≠ ⊤) : ℓ d = q.label d := ite_eq_right hd
  have hlt (d : Fin q.card) (hd : q.label d ≠ ⊤) : q.label d < β :=
    (q.atStage d).resolve_right hd
  have hlaw : q.rows.IsLawful ℓ := by
    refine ⟨fun d ↦ ?_, fun s ↦ ?_, fun s t hst hg ↦ ?_⟩
    · -- order
      by_cases hd : q.label d = ⊤
      · have hdc := hc.mem_below hd
        rw [hℓtop d hd]
        refine isSelfVisible_bandMap hβ' hμ (hc.2.2 d hd) (hμle d hd) ?_
        rw [Scheme.rowAt_of_mem hdc]
        exact hq.isConsistent.isOrderly c ⟨d, hdc⟩
      · rw [hℓlow d hd]
        exact q.isLawful.orderly d
    · -- locality
      by_cases hs : q.label s = ⊤
      · have hsc := hc.mem_below hs
        have hgs : q.toCellScheme.grade s ≤ N := hc.2.2 s hs
        have hcons := CellScheme.Rows.isLawfulBelow_iff.mp (hq.isConsistent c)
        have hbelow (x : Fin q.card)
            (hx : x ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex s)) :
            x ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex c) :=
          -- membership below a cell is the comparison of graded indices, which is transitive
          show q.toCellScheme.gradedIndex x ≤ q.toCellScheme.gradedIndex c from le_trans hx hsc
        have h₂ : TransformsTo
            (fun d : q.toCellScheme.below (q.toCellScheme.gradedIndex s) ↦
              q.toCellScheme.grade d)
            (q.rows.row s) (fun d : q.toCellScheme.below (q.toCellScheme.gradedIndex s) ↦
              min (q.rows.row c ⟨d.1, hbelow d.1 d.2⟩) (q.rows.row c ⟨s, hsc⟩)) :=
          (hcons.locality ⟨s, hsc⟩).reindex
            fun d : q.toCellScheme.below (q.toCellScheme.gradedIndex s) ↦
              ⟨⟨d.1, hbelow d.1 d.2⟩, d.2⟩
        refine TransformsTo.splice_bandMap hβ hμ
          (fun d : q.toCellScheme.below (q.toCellScheme.gradedIndex s) ↦ d.2.2.trans hgs)
          (q.isLawful.locality s) h₂ (fun d ↦ ?_) (fun d hd ↦ ?_) (fun d hd ↦ ?_)
          (fun d hd ↦ ?_)
        · rw [hs, min_top_right]
          exact q.atStage d
        · rw [hs, min_top_right] at hd
          have h₁ := hμle d hd
          have h₂ := hμle s hs
          rw [Scheme.rowAt_of_mem (hbelow d.1 d.2)] at h₁
          rw [Scheme.rowAt_of_mem hsc] at h₂
          exact le_min h₁ h₂
        · rw [hs, min_top_right] at hd ⊢
          rw [hℓlow d.1 (hd.trans_le le_top).ne, hℓtop s hs]
          exact min_eq_left (hd.le.trans (hband_ge s hs))
        · rw [hs, min_top_right] at hd
          rw [hℓtop d.1 hd, hℓtop s hs, Scheme.rowAt_of_mem (hbelow d.1 d.2),
            Scheme.rowAt_of_mem hsc]
          exact ((monotone_bandMap β μ N).map_min).symm
      · have hfun : (fun d : q.toCellScheme.below (q.toCellScheme.gradedIndex s) ↦
            min (ℓ d) (ℓ s)) =
            fun d : q.toCellScheme.below (q.toCellScheme.gradedIndex s) ↦
              min (q.label d) (q.label s) := by
          funext d
          rw [hℓlow s hs]
          by_cases hd : q.label d = ⊤
          · rw [hℓtop d hd, hd, min_top_left,
              min_eq_right ((hlt s hs).le.trans (hband_ge d hd))]
          · rw [hℓlow d hd]
        rw [hfun]
        exact q.isLawful.locality s
    · -- availability
      by_cases hs : q.label s = ⊤
      · have hsc := hc.mem_below hs
        have htc : t ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex c) := by
          -- membership below `c` is the comparison of graded indices
          change q.toCellScheme.gradedIndex t ≤ q.toCellScheme.gradedIndex c
          exact Prod.mk_le_mk.mpr ⟨by rw [hc.1]; exact subset_univ _,
            hg ▸ hc.2.2 s hs⟩
        obtain ⟨u, hu, hrow⟩ := (CellScheme.Rows.isLawfulBelow_iff.mp
          (hq.isConsistent c)).availability ⟨s, hsc⟩ ⟨t, htc⟩ hst hg
        have hu' : q.toCellScheme.gradedIndex u.1 = q.toCellScheme.gradedIndex t := hu
        have hug : q.toCellScheme.grade u.1 = q.toCellScheme.grade s :=
          (congrArg Prod.snd hu').trans hg.symm
        have hloc := (q.isLawful.locality c).le_of_le (d := ⟨s, hsc⟩) (d' := u) hrow hug.le
        have hut : q.label u.1 = ⊤ := by
          -- locality of `q` at `c`, read at the cells `s` and `u`
          change min (q.label s) (q.label c) ≤ min (q.label u.1) (q.label c) at hloc
          rw [hs, hc.2.1, min_self] at hloc
          exact top_le_iff.mp (hloc.trans (min_le_left _ _))
        refine ⟨u.1, hu', ?_⟩
        rw [hℓtop s hs, hℓtop u.1 hut, Scheme.rowAt_of_mem hsc, Scheme.rowAt_of_mem u.2]
        exact monotone_bandMap β μ N hrow
      · obtain ⟨u, hu, hle⟩ := q.isLawful.availability s t hst hg
        refine ⟨u, hu, ?_⟩
        rw [hℓlow s hs]
        by_cases hut : q.label u = ⊤
        · rw [hℓtop u hut]
          exact (hlt s hs).le.trans (hband_ge u hut)
        · rw [hℓlow u hut]
          exact hle
  have hNα : β + N < α :=
    ((add_lt_add_iff_left β).mpr (Ordinal.natCast_lt_omega0 N)).trans_le hα
  refine ⟨μ, j, hμ, ho, ⟨q.toScheme, ℓ, q.isWellFormed, q.isCoded, hlaw, fun d ↦ ?_⟩, ?_,
    fun d d' hdd' hd ↦ ?_⟩
  · -- every label of the lift occurs at `α`
    by_cases hd : q.label d = ⊤
    · rw [hℓtop d hd]
      exact .inl ((bandMap_le _).trans_lt (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hNα)))
    · rw [hℓlow d hd]
      exact (q.atStage d).mono ((le_self_add.trans hα))
  · -- the lift reduces to `q`
    refine StageType.ext rfl fun i i' hii' ↦ ?_
    obtain rfl : i = i' := Fin.ext hii'
    -- the reduced label is the reduction of `ℓ i`
    change Label.reduce β (ℓ i) = q.label i
    by_cases hd : q.label i = ⊤
    · rw [hd, Label.reduce_of_le (by rw [hℓtop i hd]; exact hband_ge i hd)]
    · rw [hℓlow i hd, Label.reduce_of_lt (hlt i hd)]
  · -- the label of the lift at a cell labelled `⊤`
    obtain rfl : d' = d := Fin.ext hdd'
    exact hℓtop d' hd

/-- A cell of `q` transported from a cell of the root labelled `⊤` is labelled `⊤`. -/
theorem label_cellMap_eq_top {f : Fin k ↪ Fin m} {p : StageType.{u} β k}
    (hp : restrictFace f q = some p) {d : Fin p.card} (hd : p.label d = ⊤)
    (i : Fin (q.toScheme.comap f).card) (hi : (i : ℕ) = d) : q.label (q.cellMap f i) = ⊤ := by
  obtain ⟨hf, hqp⟩ := (restrictFace_eq_some_iff q f).mp hp
  -- the label of `q` at the transported cell is the label of the face at `i`
  change (q.comap f hf).label i = ⊤
  exact (label_congr hqp hi).trans hd

/-! ### Forcing is read by the row of a top cap -/

/-- **Thresholds bounded below in every lift are read by the row of a top cap.**  Let `β` be a
limit, `β + ω ≤ α`, `q` a legal stage type at `β`, `c` a top cap of `q` of grade `N`, `r` a marker
of `c`, and `e` a cell labelled `⊤`.  If every stage type at `α` reducing to `q` has a label at
least `β + L` at `e`, then `L ≤ N` and
`visibilityReplace N L (q.rowAt c r) ≤ q.rowAt c e`.

The band lift (`StageType.IsMarker.exists_lift`) has the label `β + min j' N` at `e` when the row
of `c` reads `e` in the block `[μ, μ + ω)` of the marker, at `μ + j'`, and `β + N` otherwise. -/
theorem IsMarker.le_grade_and_visibilityReplace_rowAt_le (hβ : IsSuccLimit β) (hα : β + ω ≤ α)
    (hq : q.IsLegal) (hc : q.IsTopCap c) (hr : q.IsMarker c r) (he : q.label e = ⊤) {L : ℕ}
    (hL : ∀ (Q : StageType.{u} α m) (e' : Fin Q.card), Q.reduce hβ.isSuccPrelimit = q →
      (e' : ℕ) = e → ((β + L : Ordinal.{u}) : Label.{u}) ≤ Q.label e') :
    L ≤ q.toCellScheme.grade c ∧
      visibilityReplace (q.toCellScheme.grade c) L (q.rowAt c r) ≤ q.rowAt c e := by
  obtain ⟨μ, j, hμ, hrj, Q, hQ, hQl⟩ := hr.exists_lift hβ hα hq hc
  set N := q.toCellScheme.grade c
  set e' : Fin Q.card :=
    ⟨e, lt_of_lt_of_eq e.2 (congrArg (fun t : StageType.{u} β m ↦ t.card) hQ).symm⟩
  have h := hL Q e' hQ rfl
  rw [hQl e e' rfl he] at h
  have hLN : L ≤ N := by
    have h' := h.trans (bandMap_le _)
    exact_mod_cast (add_le_add_iff_left β).mp (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h'))
  refine ⟨hLN, ?_⟩
  have hre : q.rowAt c r ≤ q.rowAt c e := hr.2.2 e he (hc.mem_below he)
  rw [hrj] at hre ⊢
  have hblock (i : ℕ) : ((μ + i : Ordinal.{u}) : Label.{u}) < ((μ + ω : Ordinal.{u}) : Label.{u}) :=
    WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
      ((add_lt_add_iff_left μ).mpr (Ordinal.natCast_lt_omega0 i)))
  rw [visibilityReplace_coe_add hμ]
  by_cases hω : ((μ + ω : Ordinal.{u}) : Label.{u}) ≤ q.rowAt c e
  · split_ifs
    · exact ((hblock L).trans_le hω).le
    · exact ((hblock j).trans_le hω).le
  -- the row of `c` reads `e` at `μ + j'`
  obtain ⟨ν, hν, -⟩ := exists_coe_eq_of_le_of_lt ((coe_le_coe_add μ j).trans hre) (not_le.mp hω)
  have hν₁ : μ ≤ ν := by
    have := (coe_le_coe_add μ j).trans (hν ▸ hre)
    exact WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp this)
  have hν₂ : ν < μ + ω := by
    have := hν ▸ not_le.mp hω
    exact WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp this)
  obtain ⟨j', rfl⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0 hν₁ hν₂
  rw [hν] at hre h ⊢
  rw [bandMap_coe_add_natCast] at h
  have hLj' : L ≤ j' := by
    have h' := (add_le_add_iff_left β).mp (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h))
    have : L ≤ min j' N := by exact_mod_cast h'
    exact this.trans (min_le_left _ _)
  have hjj' : j ≤ j' := by
    have h' := (add_le_add_iff_left μ).mp (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hre))
    exact_mod_cast h'
  split_ifs
  · exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
      ((add_le_add_iff_left μ).mpr (by exact_mod_cast hLj')))
  · exact hre

/-- **Forcing is read by the rows.**  Let `β` be a limit, `β + ω ≤ α`, `q` a legal stage
type at `β` restricting along `f` to a root `p`, `c` a top cap of `q` of grade `N`, and `r` a
marker of `c`.  If `(q, f)` forces the threshold `L` at a cell `d` of `p` labelled `⊤`, and `e` is
the cell of `q` transported from `d`, then `L ≤ N` and
`visibilityReplace N L (q.rowAt c r) ≤ q.rowAt c e`. -/
theorem ForcesThreshold.le_grade_and_visibilityReplace_rowAt_le (hβ : IsSuccLimit β)
    (hα : β + ω ≤ α) (hq : q.IsLegal) (hc : q.IsTopCap c) (hr : q.IsMarker c r) {f : Fin k ↪ Fin m}
    {p : StageType.{u} β k} {d : Fin p.card} {L : ℕ}
    (hforce : ForcesThreshold α hβ.isSuccPrelimit q f p d L) (hd : p.label d = ⊤)
    (he : ∀ i : Fin (q.toScheme.comap f).card, (i : ℕ) = d → q.cellMap f i = e) :
    L ≤ q.toCellScheme.grade c ∧
      visibilityReplace (q.toCellScheme.grade c) L (q.rowAt c r) ≤ q.rowAt c e := by
  obtain ⟨hf, hqp⟩ := (restrictFace_eq_some_iff q f).mp hforce.1
  have hcard : (q.comap f hf).card = p.card :=
    congrArg (fun s : StageType.{u} β k ↦ s.card) hqp
  set i₀ : Fin (q.comap f hf).card := ⟨d, lt_of_lt_of_eq d.2 hcard.symm⟩
  have hie : q.cellMap f i₀ = e := he i₀ rfl
  have hel : q.label e = ⊤ := by
    rw [← hie, ← comap_label q f hf i₀]
    exact (label_congr hqp rfl).trans hd
  refine hr.le_grade_and_visibilityReplace_rowAt_le hβ hα hq hc hel fun Q e' hQ he' ↦ ?_
  subst hQ
  have hf' : univ.map f ∈ Q.toCellScheme.faces := hf
  have h := hforce.2 Q (Q.comap f hf') rfl (restrictFace_of_mem Q f hf') i₀ rfl
  -- the label of the face of `Q` at `i₀` is the label of `Q` at the transported cell
  change ((β + L : Ordinal.{u}) : Label.{u}) ≤ Q.label (Q.cellMap f i₀) at h
  -- the cells of `Q` and of its reduction are the same, by position
  have hpos : Q.cellMap f i₀ = e' := Fin.ext (by rw [he']; exact congrArg Fin.val hie)
  rwa [hpos] at h

/-! ### The marked-cap context -/

/-- A stage type `t'` on `k` points is a **marked-cap context** along `h : Fin n ↪ Fin k` when it
has a top cap `c` of grade `N > n + 1` with a marker `r`, and at every cell `a` of the root (a cell
visible through `h`) labelled `⊤` the row of `c` satisfies
`visibilityReplace N (n + 1) (t'.rowAt c r) ≤ t'.rowAt c a`.  The grade of a top cap is the top
grade of `t'`, the largest grade of a cell labelled `⊤`. -/
def IsMarkedCapContext (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) : Prop :=
  ∃ c r, t'.IsTopCap c ∧ t'.IsMarker c r ∧ n + 1 < t'.toCellScheme.grade c ∧
    ∀ a ∈ t'.visibleCells h, t'.label a = ⊤ →
      visibilityReplace (t'.toCellScheme.grade c) (n + 1) (t'.rowAt c r) ≤ t'.rowAt c a

/-- **A marked-cap context is not top-free**: its top cap is labelled `⊤`. -/
theorem IsMarkedCapContext.not_isTopFree {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    (ht : t'.IsMarkedCapContext h) : ¬ t'.IsTopFree :=
  fun htf ↦ let ⟨c, _, hc, _⟩ := ht; htf c hc.2.1

/-- **The root of a marked-cap context is not onto**: its top cap has grade above `n + 1`, at most
the number `k` of points of the context, so `n < k`. -/
theorem IsMarkedCapContext.not_surjective {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    (ht : t'.IsMarkedCapContext h) :
    ¬ Function.Surjective h := by
  obtain ⟨c, -, -, -, hn, -⟩ := ht
  intro hs
  have hkn : k ≤ n := by simpa using Fintype.card_le_of_surjective h hs
  have := t'.grade_le c
  omega

/-- A top-free stage type is a marked-cap context along no embedding. -/
theorem not_isMarkedCapContext_of_isTopFree {t' : StageType.{u} α k} (ht : t'.IsTopFree)
    (h : Fin n ↪ Fin k) : ¬ t'.IsMarkedCapContext h :=
  fun hm ↦ hm.not_isTopFree ht

/-- A stage type on no points is a marked-cap context along no embedding: it is top-free. -/
theorem not_isMarkedCapContext_of_zero (t : StageType.{u} α 0) (h : Fin n ↪ Fin 0) :
    ¬ t.IsMarkedCapContext h :=
  not_isMarkedCapContext_of_isTopFree (isTopFree_of_zero t) h

/-- **Over the empty root, a top cap of grade above `1` gives a marked-cap context**: no cell of
positive grade is visible through an embedding of no points, so the row inequality is vacuous. -/
theorem isMarkedCapContext_of_isTopCap_of_zero {t' : StageType.{u} α k} {c : Fin t'.card}
    (hc : t'.IsTopCap c) (h1 : 1 < t'.toCellScheme.grade c) (h : Fin 0 ↪ Fin k) :
    t'.IsMarkedCapContext h := by
  obtain ⟨r, hr⟩ := exists_isMarker hc.2.1
  refine ⟨c, r, hc, hr, h1, fun a ha _ ↦ absurd ?_ (Nat.lt_irrefl 0)⟩
  have hs : t'.toCellScheme.scope a = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun z hz ↦ ?_
    obtain ⟨i, -⟩ := Scheme.mem_visibleCells.mp ha (Finset.mem_coe.mpr hz)
    exact i.elim0
  have hcard := t'.isWellFormed.isWellFormed.grade_le_card a
  rw [hs, Finset.card_empty] at hcard
  exact lt_of_lt_of_le (t'.isWellFormed.isWellFormed.grade_pos a) hcard

/-- **A context whose cells labelled `⊤` have grades at most `n + 1` is a marked-cap context along
no embedding of `n` points**: the grade of a top cap is the grade of a cell labelled `⊤`. -/
theorem not_isMarkedCapContext_of_grade_le {t' : StageType.{u} α k}
    (ht : ∀ x, t'.label x = ⊤ → t'.toCellScheme.grade x ≤ n + 1) (h : Fin n ↪ Fin k) :
    ¬ t'.IsMarkedCapContext h :=
  fun ⟨c, _, hc, _, hn, _⟩ ↦ (ht c hc.2.1).not_gt hn

/-- **Forcing at the root gives a marked-cap context.**  Let `β` be a limit, `β + ω ≤ α`, `q` a
legal stage type at `β` restricting along `f : Fin n ↪ Fin m` to `p`, and `c` a top cap of `q` of
grade above `n + 1`.  If `(q, f)` forces the threshold `n + 1` at every cell of
`p` labelled `⊤`, then `q` is a marked-cap context along `f`, with any marker of `c`. -/
theorem isMarkedCapContext_of_forcesThreshold (hβ : IsSuccLimit β) (hα : β + ω ≤ α)
    (hq : q.IsLegal) {f : Fin n ↪ Fin m} {p : StageType.{u} β n}
    (hp : restrictFace f q = some p) (hc : q.IsTopCap c)
    (hn : n + 1 < q.toCellScheme.grade c)
    (hforce : ∀ d : Fin p.card, p.label d = ⊤ →
      ForcesThreshold α hβ.isSuccPrelimit q f p d (n + 1)) :
    q.IsMarkedCapContext f := by
  obtain ⟨r, hr⟩ := exists_isMarker hc.2.1
  refine ⟨c, r, hc, hr, hn, fun a ha hat ↦ ?_⟩
  obtain ⟨hf, hqp⟩ := (restrictFace_eq_some_iff q f).mp hp
  have hcard : (q.comap f hf).card = p.card :=
    congrArg (fun s : StageType.{u} β n ↦ s.card) hqp
  obtain ⟨i, rfl⟩ : a ∈ Set.range (q.cellMap f) := by
    rw [Scheme.range_cellMap]
    exact ha
  set d : Fin p.card := ⟨i, lt_of_lt_of_eq i.2 hcard⟩
  have hd : p.label d = ⊤ := by
    rw [← hat]
    exact (label_congr hqp.symm rfl).trans (comap_label q f hf i)
  exact (ForcesThreshold.le_grade_and_visibilityReplace_rowAt_le hβ hα hq hc hr (hforce d hd) hd
    fun i' hi' ↦ congrArg (q.cellMap f) (Fin.ext hi')).2

end StageType

end VaughtConjecture
