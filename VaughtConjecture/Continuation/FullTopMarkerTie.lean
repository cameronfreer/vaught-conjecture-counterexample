/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.FullTopSaturation

/-!
# Full-top saturation through the marker-tie extension

Roadmap, Layer 3 ((R3) of the table of 3.4) and Layer 4 (cover-hollowness).

Full-top saturation (`Realization.HasFullTopSaturation`) asks, over an occurrence `x` of a model,
for a point `y` such that the type of `x` extended by `y` has a prescribed scheme `S₀` and is `⊤`
at prescribed cells of full grade.  It is not a consequence of the clauses of `IsModel` at the
occurrence itself: setting every cell of full grade to `⊥` keeps a labelling lawful, so no scheme
on `x` and `y` forces `⊤` there.  This file reduces it, in a hollow model, to the legality of one
scheme on a larger tuple.

**The marker-tie extension** (`Scheme.IsMarkerTieScheme`).  Let `Zt` be a stage type on `m`
points with a root face `t` along `g : Fin n ↪ Fin m`, a top cap `w` of grade `j`, and a marker
`r` of `w`.  A marker-tie extension of `Zt` over a one-point coface scheme `S₀` of the root is a
scheme `S` on `m + 1` points such that:

* its face along the first `m` points is the scheme of `Zt`, and its face along the root followed
  by the new point is `S₀`;
* it has a cell of graded index `(univ, j)`, and the row of every such cell `w'` reads every
  target cell of `S₀` (the cells of full grade `n + 1` at which the prescription is `⊤`) at least
  at its value at the marker, with its visibility replaced at `n + 1`:
  `visibilityReplace j (n + 1) (row_{w'} r)`.

The intended construction has exactly one such cell, with the row of `w` on the old cells; the
predicate asks neither, and the reading off below uses neither.

**Reading off the formal top** (`Scheme.IsMarkerTieScheme.mem_fullTopFamily`, compiled).  In
every coface `q` of `Zt` on such a scheme, availability from the copy of `w` (scope in `univ`,
grade `j`, label `⊤`) gives a cell `w'` of graded index `(univ, j)` labelled `⊤`
(`StageType.exists_label_eq_top_of_availability`).  Locality at `w'` then puts `⊤` at every cell
its row reads at least at the visibility-replaced value of a cell labelled `⊤`
(`StageType.label_eq_top_of_reading`): the suppressor is `⊤` up to the grade `j`, so the shifter
commutes with the visibility replacement at `j`, and it sends the value of the marker to `⊤`.  So
the face of `q` along the root and the new point is in the full-top family.

**The legality of the scheme** (`Realization.MarkerTieLegality`, the single statement not proved
here; the theorem `Realization.markerTieLegality` is `sorry`).  At a type `Zt` of a block stage
forcing the threshold `n + 1` at the root cells labelled `⊤` (the output of
`Realization.IsModel.exists_forcing_floor`), with a top cap `w` of grade above `n + 1` and a
marker `r`, for every legal one-point coface `D₀` of the root, some marker-tie extension of `Zt`
over the scheme of `D₀`, with the targets the cells of full grade labelled `⊤` in `D₀`, carries a
legal coface of `Zt`.  Its content is the bountifulness of the rows of the new cells below the
full grade: a relabelling of the root must extend to the scheme of `D₀` with the targets at least
the marker value (the forcing threshold is meant to make the lifts with the root tops only at
least `λ + n + 1` the only ones), and the cells of graded index `(univ, j)` must serve the
availability from every cell of grade `j`.

**Composition** (compiled, conditional on `Realization.MarkerTieLegality`):
`Realization.hasFullTopSaturation_of_markerTieLegality` proves full-top saturation in every model
at a block stage that is cover-hollow with unbounded growth: synchronize `x` to a forcing floor
`Z` (`Realization.IsModel.exists_forcing_floor`), take a top cap and a marker of its type, realize
the marker-tie extension over `Z` by generalized saturation (clause 4(a)i), and read off `⊤` on
the face along the root and the new point.  Hence `Realization.HollowFullTopSaturation`
(`Realization.hollowFullTopSaturation_of_markerTieLegality`) and
`Realization.HollowFullTopSaturationReceiving`
(`Realization.hollowFullTopSaturationReceiving_of_markerTieLegality`).  Finite-cut receiving is
not used; hollowness is used only through the forcing floor.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label

/-! ### Reading off the formal top -/

namespace StageType

variable {α : Ordinal.{u}} {k : ℕ}

/-- **Availability of the formal top**: if a cell `a` labelled `⊤` has its scope in the scope of
a cell `t` and the grade of `t`, some cell of the graded index of `t` is labelled `⊤`. -/
theorem exists_label_eq_top_of_availability (q : StageType.{u} α k) {a t : Fin q.card}
    (ha : q.label a = ⊤) (hsub : q.toCellScheme.scope a ⊆ q.toCellScheme.scope t)
    (hg : q.toCellScheme.grade a = q.toCellScheme.grade t) :
    ∃ u, q.toCellScheme.gradedIndex u = q.toCellScheme.gradedIndex t ∧ q.label u = ⊤ := by
  obtain ⟨u, hu, hle⟩ := q.isLawful.availability a t hsub hg
  exact ⟨u, hu, top_le_iff.mp (ha ▸ hle)⟩

/-- **Reading at a cell labelled `⊤`**: let `s` be labelled `⊤`, and let its row read a cell `y`
at least at the value at a cell `e` labelled `⊤`, with its visibility replaced at the grade of `s`
by `i ≤ grade s`.  Then `y` is labelled `⊤`.  Locality at `s` writes the labels below `s` as
`min (σ (row s ·)) (g (grade ·))`; the suppressor is `⊤` up to the grade of `s` and the shifter is
`⊤` at the value of `e`, so it commutes with the visibility replacement there. -/
theorem label_eq_top_of_reading (q : StageType.{u} α k) {s y e : Fin q.card}
    (hs : q.label s = ⊤) (hy : y ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex s))
    (he : e ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex s)) (hle : q.label e = ⊤)
    {i : ℕ} (hi : i ≤ q.toCellScheme.grade s)
    (hrow : visibilityReplace (q.toCellScheme.grade s) i (q.rowAt s e) ≤ q.rowAt s y) :
    q.label y = ⊤ := by
  obtain ⟨g, σ, hw, heq⟩ := q.isLawful.locality s
  have hss := heq ⟨s, q.toCellScheme.mem_below_gradedIndex s⟩
  have hee := heq ⟨e, he⟩
  have hyy := heq ⟨y, hy⟩
  simp only [hs, min_self, le_top, min_eq_left, hle] at hss hee hyy
  -- the suppressor is `⊤` at the grade of `s`, and the shifter at the value of `e`
  have hgs : g (q.toCellScheme.grade s) = ⊤ := top_le_iff.mp (hss.le.trans (min_le_right _ _))
  have hσe : σ (q.rows.row s ⟨e, he⟩) = ⊤ := top_le_iff.mp (hee.le.trans (min_le_left _ _))
  have hgy : g (q.toCellScheme.grade y) = ⊤ :=
    top_le_iff.mp (hgs ▸ hw.antitone ((q.toCellScheme.mem_below).mp hy).2)
  have hcomm := hw.visibilityReplace_comm (q.rows.row s ⟨e, he⟩) (q.toCellScheme.grade s)
    (hgs ▸ le_top) i hi
  rw [hσe, visibilityReplace_top] at hcomm
  rw [Scheme.rowAt_of_mem he, Scheme.rowAt_of_mem hy] at hrow
  have hσy : σ (q.rows.row s ⟨y, hy⟩) = ⊤ := top_le_iff.mp (hcomm ▸ hw.monotone hrow)
  rw [hyy, hσy, hgy, min_self]

end StageType

/-! ### The marker-tie extension -/

namespace Scheme

variable {n m : ℕ}

/-- Cells of one face with equal positions are equal, whatever the target scheme is called. -/
theorem faceCell_congr (S : Scheme.{u} m) (f : Fin n ↪ Fin m) {T T' : Scheme.{u} n}
    (he : S.comap f = T) (he' : S.comap f = T') (i : Fin T.card) (j : Fin T'.card)
    (hij : (i : ℕ) = j) : S.faceCell f he i = S.faceCell f he' j := by
  unfold faceCell
  congr 1
  exact Fin.ext hij

/-- Cells with equal positions of equal schemes have equal grades. -/
theorem grade_congr {S S' : Scheme.{u} n} (h : S = S') (i : Fin S.card) (j : Fin S'.card)
    (hij : (i : ℕ) = j) : S.toCellScheme.grade i = S'.toCellScheme.grade j := by
  subst h
  rw [Fin.ext hij]

/-- A **marker-tie extension** of a scheme `T` on `m` points, with a cell `w` (a top cap) and a
cell `r` (its marker), over a scheme `S₀` on `n + 1` points along `g : Fin n ↪ Fin m`, with targets
the cells of `S₀` of full grade `n + 1` at which `ρ` is `⊤`: a scheme `S` on `m + 1` points whose
face along the first `m` points is `T` and whose face along `g` followed by the new point is `S₀`,
with a cell of graded index `(univ, grade w)`, every such cell `w'` reading every target at least
at `visibilityReplace (grade w) (n + 1) (row_{w'} r)`.  The intended construction has one such
cell, with the row of `w` on the old cells, so that `row_{w'} r = row_w r`; the predicate asks
neither. -/
structure IsMarkerTieScheme (S : Scheme.{u} (m + 1)) (T : Scheme.{u} m) (g : Fin n ↪ Fin m)
    (S₀ : Scheme.{u} (n + 1)) (ρ : Fin S₀.card → Label.{u}) (w r : Fin T.card) : Prop where
  /-- The face along the first `m` points is `T`. -/
  comap_castSucc : S.comap Fin.castSuccEmb = T
  /-- The root followed by the new point spans a closed face. -/
  mem_faces : univ.map (extendByLast g) ∈ S.toCellScheme.faces
  /-- The face along the root followed by the new point is `S₀`. -/
  comap_extendByLast : S.comap (extendByLast g) = S₀
  /-- A cell of graded index `(univ, grade w)`. -/
  exists_cell : ∃ w' : Fin S.card, S.toCellScheme.gradedIndex w' = (univ, T.toCellScheme.grade w)
  /-- The tie: every cell of graded index `(univ, grade w)` reads the targets at least at its
  value at the copy of `r`, visibility replaced at `n + 1`. -/
  tie : ∀ w' : Fin S.card, S.toCellScheme.gradedIndex w' = (univ, T.toCellScheme.grade w) →
    ∀ i, S₀.toCellScheme.grade i = n + 1 → ρ i = ⊤ →
      visibilityReplace (T.toCellScheme.grade w) (n + 1)
          (S.rowAt w' (S.faceCell Fin.castSuccEmb comap_castSucc r)) ≤
        S.rowAt w' (S.faceCell (extendByLast g) comap_extendByLast i)

variable {α : Ordinal.{u}} {S : Scheme.{u} (m + 1)} {Zt : StageType.{u} α m} {g : Fin n ↪ Fin m}
  {S₀ : Scheme.{u} (n + 1)} {ρ : Fin S₀.card → Label.{u}} {w r : Fin Zt.card}

/-- **Reading off the formal top on a marker-tie extension.**  If `w` is a cell labelled `⊤` of
grade at least `n + 1` and `r` a cell below it labelled `⊤`, every coface `q` of
`Zt` on a marker-tie extension restricts along the root and the new point to a member of the
full-top family of `S₀` and `ρ`: some tie cell is `⊤` by availability from the copy of `w`, and
the targets are `⊤` by locality at that cell. -/
theorem IsMarkerTieScheme.mem_fullTopFamily (hS : IsMarkerTieScheme S Zt.toScheme g S₀ ρ w r)
    (hw : Zt.label w = ⊤)
    (hr : Zt.label r = ⊤) (hrw : r ∈ Zt.toCellScheme.below (Zt.toCellScheme.gradedIndex w))
    (hn : n + 1 ≤ Zt.toCellScheme.grade w) {q : StageType.{u} α (m + 1)}
    (hq : q ∈ Zt.cofaces ∩ StageType.saturationFamily S) :
    ∃ d, StageType.restrictFace (extendByLast g) q = some d ∧
      d ∈ Realization.fullTopFamily S₀ ρ := by
  obtain ⟨⟨-, hq₁⟩, hqS⟩ := hq
  change q.toScheme = S at hqS
  subst hqS
  set fc := q.toScheme.faceCell Fin.castSuccEmb hS.comap_castSucc
  have hfc (x : Fin Zt.card) : q.label (fc x) = Zt.label x := StageType.label_faceCell hq₁ x
  -- availability from the copy of `w` gives a tie cell labelled `⊤`
  obtain ⟨w₀, hw₀⟩ := hS.exists_cell
  have hw₀s : q.toCellScheme.scope w₀ = univ := congrArg Prod.fst hw₀
  have hw₀g : q.toCellScheme.grade w₀ = Zt.toCellScheme.grade w := congrArg Prod.snd hw₀
  obtain ⟨w', hw'w₀, hw'top⟩ := q.exists_label_eq_top_of_availability (t := w₀)
    ((hfc w).trans hw) (hw₀s ▸ subset_univ _)
    ((Scheme.grade_faceCell hS.comap_castSucc w).trans hw₀g.symm)
  have hw'i := hw'w₀.trans hw₀
  have htie := hS.tie w' hw'i
  have hw'g : q.toCellScheme.grade w' = Zt.toCellScheme.grade w := congrArg Prod.snd hw'i
  have hbelow {x : Fin q.card} (hx : q.toCellScheme.grade x ≤ Zt.toCellScheme.grade w) :
      x ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex w') :=
    (q.toCellScheme.mem_below).mpr (hw'i ▸ ⟨subset_univ _, hx⟩)
  have hrb : fc r ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex w') := by
    refine hbelow ?_
    rw [Scheme.grade_faceCell hS.comap_castSucc r]
    exact ((Zt.toCellScheme.mem_below).mp hrw).2
  have hf : univ.map (extendByLast g) ∈ q.toCellScheme.faces := hS.mem_faces
  refine ⟨q.comap (extendByLast g) hf, StageType.restrictFace_of_mem q _ hf, ?_, ?_⟩
  · exact (StageType.comap_toScheme_of_restrictFace (StageType.restrictFace_of_mem q _ hf)).trans
      hS.comap_extendByLast
  · intro i j hij hgi hρ
    have hd := StageType.restrictFace_of_mem q _ hf
    rw [← StageType.label_faceCell hd i]
    have hcell : StageType.faceCell hd i =
        q.toScheme.faceCell (extendByLast g) hS.comap_extendByLast j :=
      q.toScheme.faceCell_congr _ _ _ i j hij
    have hgj : S₀.toCellScheme.grade j = n + 1 :=
      (Scheme.grade_faceCell hS.comap_extendByLast j).symm.trans
        ((congrArg q.toCellScheme.grade hcell).symm.trans
          ((StageType.grade_faceCell hd i).trans hgi))
    rw [hcell]
    refine q.label_eq_top_of_reading hw'top (hbelow ?_) hrb ((hfc r).trans hr) (hw'g ▸ hn) ?_
    · rw [Scheme.grade_faceCell, hgj]
      exact hn
    · rw [hw'g]
      exact htie j hgj hρ

end Scheme

/-! ### The legality of the marker-tie extension, and the composition -/

namespace Realization

/-- **The legality of the marker-tie extension** (a named statement, not proved here): at a type
`Zt` of a block stage `λ_ξ` on `m` points with a root face `t` along `g`, forcing the threshold
`n + 1` at every root cell labelled `⊤` at `λ_{ξ+1}`, with a top cap `w` of grade above `n + 1`
and a marker `r` of `w`, for every legal one-point coface `D₀` of the root some marker-tie
extension of the scheme of `Zt` over the scheme of `D₀`, with the targets the cells of full grade
labelled `⊤` in `D₀`, carries a legal coface of `Zt`. -/
def MarkerTieLegality : Prop :=
  ∀ ⦃ξ : Ordinal.{u}⦄ ⦃n m : ℕ⦄ (Zt : StageType.{u} (blockStage ξ) m) (g : Fin n ↪ Fin m)
    (t : StageType.{u} (blockStage ξ) n), Zt.IsLegal → StageType.restrictFace g Zt = some t →
    (∀ a, t.label a = ⊤ → StageType.ForcesThreshold (blockStage (ξ + 1))
      (isSuccPrelimit_blockStage ξ) Zt g t a (n + 1)) →
    ∀ w r : Fin Zt.card, Zt.IsTopCap w → Zt.IsMarker w r → n + 1 < Zt.toCellScheme.grade w →
    ∀ D₀ ∈ t.cofaces, ∃ S : Scheme.{u} (m + 1),
      Scheme.IsMarkerTieScheme S Zt.toScheme g D₀.toScheme D₀.label w r ∧
        (Zt.cofaces ∩ StageType.saturationFamily S).Nonempty

variable {ξ : Ordinal.{u}} {M : Type w} {R : Realization.{u, w} (blockStage ξ) M}

/-- **Full-top saturation from the legality of the marker-tie extension**: in a model at a block
stage, cover-hollow, with unbounded growth.  Synchronize the occurrence to a forcing floor `Z`
(`Realization.IsModel.exists_forcing_floor`), take a top cap and a marker of its type, realize the
marker-tie extension over `Z` by generalized saturation, and read off `⊤` on the face along the
root and the new point (`Scheme.IsMarkerTieScheme.mem_fullTopFamily`). -/
theorem hasFullTopSaturation_of_markerTieLegality (hleg : MarkerTieLegality.{u})
    (hR : R.IsModel) (hhol : R.IsCoverHollow) (htop : R.topGradeSup = ⊤) :
    R.HasFullTopSaturation := by
  intro x S₀ ρ ⟨D₀, hD₀, hD₀S, hD₀top⟩
  subst hD₀S
  obtain ⟨Z, g, hg, hNZ, -, hforce⟩ := hR.exists_forcing_floor hhol htop 0 x
  have htZ : StageType.restrictFace g Z.type = some x.type :=
    Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent hg
  have hZl := hR.isLegal _ _ Z.eval_tuple
  have hnt : ¬ Z.type.IsTopFree := fun htf ↦ by
    rw [← StageType.topGrade_eq_zero_iff] at htf
    omega
  obtain ⟨cw, hcw⟩ := StageType.exists_isTopCap hZl hnt
  obtain ⟨r, hr⟩ := StageType.exists_isMarker hcw.2.1
  have hcwg : x.arity + 1 < Z.type.toCellScheme.grade cw := by
    rw [hcw.grade_eq_topGrade]
    exact hNZ
  obtain ⟨S, hS, hne⟩ := hleg Z.type g x.type hZl htZ hforce cw r hcw hr hcwg D₀ hD₀
  obtain ⟨u, hu, q, hq, hev⟩ :=
    (hR.saturation Z S hne).inter_cofaces hR.isConsistent hR.isLegal
  obtain ⟨d, hd, hdS, hdtop⟩ :=
    hS.mem_fullTopFamily hcw.2.1 hr.1 hr.2.1 hcwg.le hq
  refine ⟨(extendByLast g).trans u, Function.Embedding.ext fun i ↦ ?_, d,
    ⟨hdS, fun i j hij hgi hρ ↦ hdtop i j hij hgi
      (hD₀top j j rfl ((Scheme.grade_congr hdS i j hij).symm.trans hgi) hρ)⟩, ?_⟩
  · have h₁ := DFunLike.congr_fun hu (g i)
    have h₂ := DFunLike.congr_fun hg i
    simp only [Function.Embedding.trans_apply, Fin.coe_castSuccEmb, extendByLast_castSucc]
      at h₁ h₂ ⊢
    rw [h₁, h₂]
  · rw [← hd]
    exact hR.isConsistent u q (extendByLast g) hev

/-- **`HollowFullTopSaturation` from the legality of the marker-tie extension.** -/
theorem hollowFullTopSaturation_of_markerTieLegality (hleg : MarkerTieLegality.{u}) :
    HollowFullTopSaturation.{u, w} := by
  intro α M R _ hR hH htop
  obtain ⟨ξ, rfl, hhol⟩ := hH
  exact hasFullTopSaturation_of_markerTieLegality hleg hR hhol htop

/-- **`HollowFullTopSaturationReceiving` from the legality of the marker-tie extension**;
finite-cut receiving is not used. -/
theorem hollowFullTopSaturationReceiving_of_markerTieLegality (hleg : MarkerTieLegality.{u}) :
    HollowFullTopSaturationReceiving.{u, w} :=
  (hollowFullTopSaturation_of_markerTieLegality hleg).receiving

set_option warningAsError false in
/-- **SCAFFOLD (`sorry`): the legality of the marker-tie extension.**  The predicate
`Realization.MarkerTieLegality` is the statement.  What is open is the bountifulness of the rows
of the new cells below the full grade, at the tie cells of graded index `(univ, j)` in
particular: every relabelling `f` lawful on the old cells below a pair must lift with the targets
at least the marker value `min (visibilityReplace j (n + 1) (f r)) (f w)`, that is, a relabelling
of the root must extend to the scheme of `D₀` with the targets raised to the marker value (a
block-reading lift of the root to `D₀`), and the tie cells must serve the availability of every
cell of grade `j`.  The forcing threshold at the root tops is the hypothesis meant for the first.
Without it the statement would give full-top saturation in every model with unbounded
growth, which fails (argued, not compiled) at the reductions of models at the next block stage. -/
theorem markerTieLegality : MarkerTieLegality.{u} := by
  sorry

/-- **Full-top saturation of the hollow receiving models**, through the marker-tie extension;
it depends on `Realization.markerTieLegality`, which is `sorry`.  The form conditional on the
legality is `Realization.hollowFullTopSaturationReceiving_of_markerTieLegality`. -/
theorem hollowFullTopSaturationReceiving : HollowFullTopSaturationReceiving.{u, w} :=
  hollowFullTopSaturationReceiving_of_markerTieLegality markerTieLegality

end Realization

end VaughtConjecture
