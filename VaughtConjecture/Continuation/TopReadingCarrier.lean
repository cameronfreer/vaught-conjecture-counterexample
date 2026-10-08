/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.MarkedCarrierAcquisition

/-!
# Top-reading carriers: the reading asked only at the cells labelled `⊤`

Roadmap, Layer 3 ((R3) of the table of 3.4).

The cutoff form of determination
(`StageType.isDeterminedWithin_receivingFamily_of_isPrescribedExtension`) keeps every label of the
carrier other than `⊤`, so the reading of the new tops is needed only at the cells of graded index
`(univ, N)` that are labelled `⊤` in the carrier.  A **top-reading carrier**
(`StageType.IsTopReadingCarrier`, defined in this repository) asks exactly that; a prescribed
extension for the top-marked prescription is one
(`StageType.IsPrescribedExtension.isTopReadingCarrier`).  It determines the donor at a cutoff
(`StageType.isDeterminedWithin_receivingFamily_of_isTopReadingCarrier`, compiled in this repository
(theorem named)), and (R3) for cover-hollow models with finite-cut receiving follows from
**top-reading carriers** at every block stage (`StageType.HasTopReadingCarriers`, implied by
`StageType.HasTopMarkedCarriers`;
`Realization.hollowReceiving_withReceiving_of_hasTopReadingCarriers`).
`StageType.HasTopReadingCarriers` is assumed by that theorem at every arity; it is proved at no
arity here.  Contexts on at most four points are proposed test cases (prospective).  The route
through the canonical completion is closed: there a new cell labelled `⊤` is forced at entries
with different values where the input is `⊤` (`Continuation/FieldLayerForcedTops.lean`).

The cells of graded index `(univ, N)` with a label other than `⊤` are free: they may serve the
availability of the lawful labellings that a reading cell cannot.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ}

/-- A **top-reading carrier** over `t'` along `h` for `d`, with top cap `c` and marker `r`: a legal
one-point extension `D` of `t'` whose face along `extendByLast h` is `d`, such that every cell of
`D` of graded index `(univ, N)` (`N` the grade of `c`) **labelled `⊤` in `D`** reads every new
cell of `d` labelled `⊤` at least as `r`.  The cells of that graded index with a label other than
`⊤` are unconstrained. -/
structure IsTopReadingCarrier (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
    (d : StageType.{u} α (n + 1)) (c r : Fin t'.card) (D : StageType.{u} α (k + 1)) : Prop where
  /-- The carrier is legal. -/
  isLegal : D.IsLegal
  /-- Its face along the first points is `t'`. -/
  restrictFace_castSucc : restrictFace Fin.castSuccEmb D = some t'
  /-- Its face along `extendByLast h` is `d`. -/
  restrictFace_extendByLast : restrictFace (extendByLast h) D = some d
  /-- Every cell of graded index `(univ, N)` labelled `⊤` reads the new tops at least as `r`. -/
  reads : ∀ u, D.toCellScheme.gradedIndex u = ((univ : Finset (Fin (k + 1))),
      t'.toCellScheme.grade c) → D.label u = ⊤ → ∀ j : Fin d.card,
      Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊤ →
        D.rowAt u (faceCell restrictFace_castSucc r) ≤
          D.rowAt u (faceCell restrictFace_extendByLast j)

/-- **A prescribed extension for the top-marked prescription is a top-reading carrier**: it reads
the new tops at every cell of graded index `(univ, N)`, labelled `⊤` or not. -/
theorem IsPrescribedExtension.isTopReadingCarrier {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} {c r : Fin t'.card} {D : StageType.{u} α (k + 1)}
    (hD : IsPrescribedExtension t' h d (topMarkedPrescription t' d c r) D) :
    t'.IsTopReadingCarrier h d c r D := by
  obtain ⟨hDl, h₁, h₂, he₁, he₂, hS⟩ := hD
  exact ⟨hDl, h₁, h₂, fun u hu _ j hj hjt ↦ hS u _ hu rfl j hj hjt⟩

/-- **A top-reading carrier determines the donor at a cutoff.**  As
`StageType.isDeterminedWithin_receivingFamily_of_isPrescribedExtension`, with the reading asked
only at the cells labelled `⊤`: a member of the receiving family at a cutoff above the labels of
`D` other than `⊤` is `⊤` at a cell only where `D` is, so the cell of graded index `(univ, N)`
labelled `⊤` given by availability from the top cap is labelled `⊤` in `D` and reads the new tops
at least as the marker. -/
theorem isDeterminedWithin_receivingFamily_of_isTopReadingCarrier {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} {t : StageType.{u} α n} {d : StageType.{u} α (n + 1)} {c r : Fin t'.card}
    (ht : restrictFace h t' = some t) (hd : restrictFace Fin.castSuccEmb d = some t)
    (hc : t'.IsTopCap c) (hr : t'.label r = ⊤) (hn : n + 1 ≤ t'.toCellScheme.grade c)
    {D : StageType.{u} α (k + 1)} (hD : t'.IsTopReadingCarrier h d c r D) {δ : Label.{u}}
    (hδ : ∀ j, D.label j ≠ ⊤ → D.label j < δ) :
    IsDeterminedWithin (receivingFamily D δ) t' h d := by
  obtain ⟨hDl, h₁, h₂, hS⟩ := hD
  rintro ⟨S, ℓ, hw, hcod, hl, hat⟩ ⟨hq, hcut⟩ hq₁
  -- the stage type `q` has the scheme of `D`
  change S = D.toScheme at hq
  subst hq
  set q : StageType.{u} α (k + 1) := ⟨D.toScheme, ℓ, hw, hcod, hl, hat⟩ with hqdef
  set N := t'.toCellScheme.grade c
  have hold (z : Fin t'.card) : ℓ (faceCell h₁ z) = t'.label z := label_faceCell hq₁ z
  obtain ⟨hf₂, -⟩ := (restrictFace_eq_some_iff D (extendByLast h)).mp h₂
  have hf₂' : univ.map (extendByLast h) ∈ q.toCellScheme.faces := hf₂
  have hlab (j : Fin d.card) : ℓ (faceCell h₂ j) = d.label j := by
    by_cases hjt : d.label j = ⊤
    · by_cases hj : Fin.last n ∈ d.toCellScheme.scope j
      · -- a new top: read by a cell of graded index `(univ, N)` labelled `⊤`
        have hNk : N ≤ k := t'.grade_le c
        have hpos : 0 < N := (Nat.succ_pos n).trans_le hn
        obtain ⟨u₀, hu₀⟩ := hDl.isComplete ((univ : Finset (Fin (k + 1))), N)
          ⟨D.univ_mem_faces, hpos, by simpa using hNk.trans (Nat.le_succ k)⟩
        have hc' : D.toCellScheme.grade (faceCell h₁ c) = N := grade_faceCell h₁ c
        have hsu₀ : D.toCellScheme.scope u₀ = univ := congrArg Prod.fst hu₀
        obtain ⟨u, hu, hcu⟩ := hl.availability (faceCell h₁ c) u₀
          (by rw [hsu₀]; exact subset_univ _) (hc'.trans (congrArg Prod.snd hu₀).symm)
        have hu' : D.toCellScheme.gradedIndex u = ((univ : Finset (Fin (k + 1))), N) :=
          hu.trans hu₀
        have hℓu : ℓ u = ⊤ := by
          have h' : ℓ (faceCell h₁ c) ≤ ℓ u := hcu
          rw [hold, hc.2.1] at h'
          exact top_le_iff.mp h'
        have hbelow (y : Fin D.card) (hy : D.toCellScheme.grade y ≤ N) :
            y ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) := by
          rw [CellScheme.mem_below, hu']
          exact Prod.mk_le_mk.mpr ⟨subset_univ _, hy⟩
        have hx : faceCell h₂ j ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) :=
          hbelow _ ((grade_faceCell h₂ j).trans_le ((d.grade_le j).trans hn))
        have hs : faceCell h₁ r ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) :=
          hbelow _ ((grade_faceCell h₁ r).trans_le (hc.2.2 r hr))
        -- the cell `u` is labelled `⊤` in `D`: the receiving family keeps the labels below `δ`
        have hDu : D.label u = ⊤ := by
          by_contra hne
          have hmin : min (ℓ u) δ = min (D.label u) δ := hcut u u rfl
          rw [hℓu, min_eq_right le_top, min_eq_left (hδ u hne).le] at hmin
          exact (hδ u hne).ne hmin.symm
        have hrow := hS u hu' hDu j hj hjt
        rw [Scheme.rowAt_of_mem hs, Scheme.rowAt_of_mem hx] at hrow
        rw [hjt]
        exact hl.eq_top_of_row_le hs hx hℓu ((hold r).trans hr) hrow
      · -- a top of the root: its label is that of `t'`
        obtain ⟨i, rfl⟩ := exists_faceCell_eq_of_last_notMem hd hj
        rw [← faceCell_faceCell h₁ h₂ ht hd i, hold, label_faceCell, label_faceCell]
    · -- a label other than `⊤` lies below the cutoff, where the receiving family keeps it
      set x : Fin D.card := faceCell h₂ j
      have hDx : D.label x = d.label j := label_faceCell h₂ j
      have hlt : D.label x < δ := hδ x (hDx ▸ hjt)
      have hmin := hcut x x rfl
      rw [min_eq_left hlt.le] at hmin
      rw [← hDx]
      rcases le_total (ℓ x) δ with hle | hle
      · rwa [min_eq_left hle] at hmin
      · rw [min_eq_right hle] at hmin
        exact absurd hmin hlt.ne'
  rw [restrictFace_of_mem q _ hf₂']
  refine congrArg some (StageType.ext ?_ fun i j hij ↦ ?_)
  · -- the scheme of the face of `q` is the face of the scheme of `D`
    change D.toScheme.comap (extendByLast h) = d.toScheme
    exact comap_toScheme_of_restrictFace h₂
  -- the label of the face at `i` is the label of `q` at the cell of `D` at `j`
  change ℓ (D.toScheme.cellMap (extendByLast h) i) = d.label j
  have hcell : D.toScheme.cellMap (extendByLast h) i = faceCell h₂ j := by
    change _ = D.toScheme.cellMap (extendByLast h) (Fin.cast _ j)
    congr 1
    exact Fin.ext hij
  rw [hcell, hlab]

variable (α) in
/-- **Top-reading carriers** at the stage `α`: over every legal marked-cap context `t'` along `h`
with top cap `c` and marker `r`, and every legal donor `d` that is a one-point coface of the face
of `t'` along `h`, there is a top-reading carrier.

It is assumed at every arity by
`Realization.hollowReceiving_withReceiving_of_hasTopReadingCarriers` and proved at no arity here;
contexts on at most four points are proposed test cases (prospective).  The canonical completion
does not prove it: there the new cells labelled `⊤` include entries with different values at two
cells where the input is `⊤` (`FieldLayerForcedTops.exists_forced_top`,
`FieldLayerForcedTops.orbitDecoder_fieldRow_eq_top`). -/
def HasTopReadingCarriers : Prop :=
  ∀ ⦃k n : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (t : StageType.{u} α n)
    (_ : restrictFace h t' = some t) (d : StageType.{u} α (n + 1))
    (_ : restrictFace Fin.castSuccEmb d = some t) (c r : Fin t'.card), t'.IsLegal → d.IsLegal →
    t'.IsMarkedCapContextAt h c r → ∃ D, t'.IsTopReadingCarrier h d c r D

/-- **Top-marked carriers give top-reading carriers.** -/
theorem HasTopMarkedCarriers.hasTopReadingCarriers (hcar : HasTopMarkedCarriers.{u} α) :
    HasTopReadingCarriers.{u} α := fun _ _ t' h t ht d hd c r ht' hd' hctx ↦
  let ⟨D, hD⟩ := hcar t' h t ht d hd c r ht' hd' hctx
  ⟨D, hD.isTopReadingCarrier⟩

end StageType

namespace Realization

/-- **(R3) for cover-hollow models with finite-cut receiving, from top-reading carriers**: as
`Realization.hollowReceiving_withReceiving_of_hasTopMarkedCarriers`, with
`StageType.HasTopReadingCarriers` (which `StageType.HasTopMarkedCarriers` implies). -/
theorem hollowReceiving_withReceiving_of_hasTopReadingCarriers
    (hcar : ∀ ξ : Ordinal.{u}, StageType.HasTopReadingCarriers.{u} (blockStage ξ)) :
    HollowReceiving.{u, w} IsCoverHollowWithReceivingAtBlock where
  exists_covers α M R hα hR hH htop n t c hc d hd := by
    obtain ⟨hH, hrec⟩ := hH
    obtain ⟨k, t', c', h, hc', hcc', ctx, r, hctx⟩ :=
      hollowAcquisition_isMarkedCapContext.exists_context hα hR hH htop t c hc
    obtain ⟨ξ, rfl, -⟩ := hH
    have ht : StageType.restrictFace h t' = some t := by
      rw [← hR.isConsistent ⟨c', hc'.injective⟩ t' h hc'.eval_eq, ← hc.eval_eq]
      congr 1
      ext i
      exact congrFun hcc' i
    obtain ⟨D, hD⟩ := hcar ξ t' h t ht d hd.2 ctx r (hR.isLegal _ _ hc'.eval_eq) hd.1 hctx
    obtain ⟨δ, hδα, hδ⟩ := D.exists_lt_forall_label_lt hα
    have hδc : IsPermittedCutoff (blockStage ξ) (δ : Label.{u}) := isPermittedCutoff_coe.mpr hδα
    have hdet := StageType.isDeterminedWithin_receivingFamily_of_isTopReadingCarrier ht hd.2
      hctx.1 hctx.2.1.1 hctx.2.2.1.le hD hδ
    rw [← hcc']
    exact exists_covers_snoc_of_isDeterminedWithin hR.isConsistent hc'
      (hrec.realizesOver_receivingFamily hc' ⟨hD.isLegal, hD.restrictFace_castSucc⟩ hδc) hdet

end Realization

end VaughtConjecture
