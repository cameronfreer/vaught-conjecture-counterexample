/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateStep

/-!
# The LOW step for states at the grade of the controllers

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the layer of states at
the grade of the controllers); semantic contract, items 3, 4 and 8.

At the grade `K` of the controllers the failure mode of the LOW step for states
(`ProfileTower.LowStateRaise`) is the situation of the LOW step on the amalgam: a profile `W₀`
lawful on the cut, agreeing with the serving state capped at the cap `h`, active below the cap
with frontier above it.  The repairs are those of the LOW step, now with no open case.

**From the donor coatom** (`ProfileTower.lowStateRaise_donor`, compiled in this repository): the
private face of `W₀` is replaced by a section with frontier at most the cap and the same root
(`StageType.IsSourceGapContextAt.exists_frontier_le_of_unserved`, with the unserved case below the
full grade `StageType.lowStepUnserved_of_le`); the frontier is then at most every donor top (at
most the cap, or below the cap by the LOW clause of the serving state).

**From the private coatom** (`ProfileTower.lowStateRaise_private`, compiled in this repository):
the donor face is replaced by one literal on the root, agreeing with the serving state capped at
the cap and reading every donor top off the root at least at the prescribed frontier
(`StageType.IsLowFamily.exists_raised_of_gap`: the raise of the donor tops through a top of the
largest grade, with the root restored by a capped lift, with no tie premise and no donor raising);
the root tops are at least the frontier by the strict source gaps.

**The step for states at `K`** (`ProfileTower.stateCatStep_low_seed`, compiled in this repository):
for the LOW designations of a seed whose private context is a source-gap context of grade
`K = g + 1 ≤ m` with the lost point last and whose donor has top grade at most `K`, the step for
states (`ProfileTower.StateCatStep`) holds at `K` from both coatoms, with no open hypothesis.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {N : Finset (Fin I.amalgam.card ⊕ Unit)}
  {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card} {g : ℕ}

/-- **The repair of the failure mode of the LOW step for states at `K`, from the donor
coatom** (`ProfileTower.LowStateRepair`).  For the
private context a source-gap context of grade `g + 1 ≤ m` with the lost point last, owner and lost
top the copies `o`, `r`, the proper donor fields and the donor tops cells below the donor coatom,
and the proper root cells proper donor fields: the private face of `W₀` is lowered to frontier at
most the cap with the same root (`StageType.lowStepUnserved_of_le`). -/
theorem lowStateRaise_donor (hgm : g + 1 ≤ m) {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (ho : o = StageType.faceCell I.restrictFace_left o')
    (hr : r = StageType.faceCell I.restrictFace_left r')
    (hNQ : ∀ f ∈ N, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, g + 1))
    (hTQ : ∀ f ∈ T, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, g + 1))
    (hNroot : ∀ i, I.left.toCellScheme.grade i ≤ g + 1 →
      Fin.last m ∉ I.left.toCellScheme.scope i → I.left.label i ≠ ⊤ →
        Sum.inl (StageType.faceCell I.restrictFace_left i) ∈ N) :
    LowStateRepair I (g + 1) (g + 1) N T o r (Fin.castSucc (Fin.last m)) := by
  classical
  intro P hPC hPlow h hh hb A hA hAP hact hfh
  have hU := StageType.lowStepUnserved_of_le I.isLegal_left hs hgm I.restrictFace_face_left
  have hAlC : I.amalgam.rows.IsLawfulBelow (coatC, g + 1) fun d ↦ A d := hA.1
  have hAlD : I.amalgam.rows.IsLawfulBelow (coatD, g + 1) fun d ↦ A d := hA.2
  have hfinish (W : Prof I) (hWC : I.amalgam.rows.IsLawfulBelow (coatC, g + 1) fun d ↦ W d)
      (hWD : ∀ d ∈ I.amalgam.toCellScheme.below (coatD, g + 1), W d = A d)
      (hWP : ∀ d, min (W d) h = min (P (Sum.inl d)) h)
      (hfr : ∀ x ∈ T, frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) ≤
        withCutoff W ⊥ x) :
      ∃ W : Prof I, IsCutLawful I (g + 1) W ∧
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last m)), g + 1),
          W d = A d) ∧
        (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧
        ∀ y ∈ T, frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCut W ⊥) ≤ withCut W ⊥ y :=
    ⟨W, ⟨hWC, (Rows.isLawfulBelow_congr fun d hd ↦ hWD d hd).mpr hAlD⟩, hWD, hWP, hfr⟩
  -- the private face, lowered
  have he := StageType.comap_toScheme_of_restrictFace I.restrictFace_left
  have hX : Prod.map (Finset.map (Coatom.left m)) id ((univ : Finset (Fin (m + 1))), g + 1) =
      (coatC, g + 1) := by
    rw [Prod.map_apply, Coatom.univ_map_left]; rfl
  set fc : Fin I.left.card → Fin I.amalgam.card := StageType.faceCell I.restrictFace_left with hfc
  set ut : Fin I.left.card → Label.{u} := fun i ↦ A (fc i) with hut_def
  have hut : I.left.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), g + 1)
      (fun i ↦ ut i) := by
    refine (Scheme.isLawfulBelow_faceCell_iff he _ A).mpr ?_
    rw [hX]
    exact hAlC
  have hMh : donorMax N (withCutoff A ⊥) < h := hact.trans_le (min_le_right _ _)
  have hroot : ∀ i, I.left.toCellScheme.grade i ≤ g + 1 →
      Fin.last m ∉ I.left.toCellScheme.scope i → I.left.label i ≠ ⊤ → ut i ≤ h := fun i hi hl ht ↦
    ((le_donorMax (a := withCutoff A ⊥) (hNroot i hi hl ht)).trans hMh.le)
  obtain ⟨vt, hvt, hvcap, hvroot, hvfr⟩ :=
    hs.exists_frontier_le_of_unserved I.isLegal_left hU hut hh hb hroot
  have hinj : Function.Injective fc := Scheme.faceCell_injective he
  set vt' : Fin I.left.card → Label.{u} := fun i ↦
    if I.left.toCellScheme.grade i ≤ g + 1 then vt i else ut i with hvt'
  set W : Prof I := Function.extend fc vt' A with hW
  have hWf (i : Fin I.left.card) : W (fc i) = vt' i := hinj.extend_apply _ _ i
  have hWle (i : Fin I.left.card) (hi : I.left.toCellScheme.grade i ≤ g + 1) :
      W (fc i) = vt i := (hWf i).trans (ite_eq_left hi)
  have hWgt (i : Fin I.left.card) (hi : ¬ I.left.toCellScheme.grade i ≤ g + 1) :
      W (fc i) = ut i := (hWf i).trans (ite_eq_right hi)
  have hWD (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatD, g + 1)) :
      W d = A d := by
    by_cases hex : ∃ i, fc i = d
    · obtain ⟨i, rfl⟩ := hex
      have hgi : I.left.toCellScheme.grade i ≤ g + 1 := by
        have := hd.2
        rwa [CellScheme.gradedIndex_snd, StageType.grade_faceCell] at this
      have hli : Fin.last m ∉ I.left.toCellScheme.scope i := by
        intro hm
        have h1 : Fin.castSucc (Fin.last m) ∈ I.amalgam.toCellScheme.scope (fc i) := by
          rw [hfc, StageType.scope_faceCell]
          exact mem_map_of_mem _ hm
        have h2 := hd.1 h1
        simp at h2
      rw [hWle i hgi]
      exact hvroot i hgi hli
    · exact Function.extend_apply' _ _ _ fun ⟨i, hi⟩ ↦ hex ⟨i, hi⟩
  have hWC : I.amalgam.rows.IsLawfulBelow (coatC, g + 1) fun d ↦ W d := by
    rw [← hX]
    refine (Scheme.isLawfulBelow_faceCell_iff he _ W).mp ?_
    exact (Rows.isLawfulBelow_congr (R := I.left.rows) (X := ((univ : Finset (Fin (m + 1))), g + 1))
      (w := fun i ↦ vt i) (w' := fun i ↦ W (fc i))
      fun i hi ↦ (hWle i (show I.left.toCellScheme.grade i ≤ g + 1 from hi.2)).symm).mp hvt
  have hWP (d : Fin I.amalgam.card) : min (W d) h = min (P (Sum.inl d)) h := by
    by_cases hex : ∃ i, fc i = d
    · obtain ⟨i, rfl⟩ := hex
      by_cases hgi : I.left.toCellScheme.grade i ≤ g + 1
      · rw [hWle i hgi, hvcap i hgi]; exact hAP _
      · rw [hWgt i hgi]; exact hAP _
    · have hWd : W d = A d := Function.extend_apply' _ _ _ fun ⟨i, hi⟩ ↦ hex ⟨i, hi⟩
      rw [hWd]; exact hAP d
  refine hfinish W hWC hWD hWP fun x hx ↦ ?_
  -- the frontier condition
  obtain ⟨d, rfl, hdD⟩ := hTQ x hx
  have hgo : I.left.toCellScheme.grade o' ≤ g + 1 := hs.grade_owner.le
  have hgr : I.left.toCellScheme.grade r' ≤ g + 1 :=
    hs.topGrade_eq ▸ StageType.grade_le_topGrade hs.label_lost
  have hfrW : frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) ≤ h := by
    unfold Label.frontier
    change min (W o) (visibilityReplace (g + 1) (g + 1) (W r)) ≤ h
    rw [ho, hr, hWle o' hgo, hWle r' hgr]
    exact hvfr
  change frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) ≤ W d
  rw [hWD d hdD]
  rcases le_or_gt h (A d) with hhA | hAh
  · exact hfrW.trans hhA
  -- below the cap: the serving profile is active and reads the donor top
  have hAPd : P (Sum.inl d) = A d := eq_of_min_eq_of_lt (hAP d) hAh
  have hNP : ∀ f ∈ N, P f = withCutoff A ⊥ f := by
    intro f hf
    obtain ⟨e, rfl, -⟩ := hNQ f hf
    exact eq_of_min_eq_of_lt (hAP e) ((le_donorMax (a := withCutoff A ⊥) hf).trans_lt hMh)
  have hPact : donorMax N P < P (Sum.inr ()) := by
    rw [donorMax_congr hNP]
    exact hact.trans_le (min_le_left _ _)
  have hPx := (le_max_right _ _).trans (hPlow hPact _ hx)
  have hmin := min_frontier_eq (K := g + 1) (o := Sum.inl o) (r := Sum.inl r)
    (a := withCutoff W ⊥) (b := P) hh (hWP o) (hWP r)
  have hfP : frontier (g + 1) (Sum.inl o) (Sum.inl r) P < h := hPx.trans_lt (hAPd ▸ hAh)
  have h2 : min (frontier (g + 1) (Sum.inl o) (Sum.inl r) P) h =
      min (frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥)) h := hmin.symm
  have hfW : frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) =
      frontier (g + 1) (Sum.inl o) (Sum.inl r) P := eq_of_min_eq_of_lt h2 hfP
  rw [hfW, ← hAPd]
  exact hPx


/-- **The repair of the failure mode of the LOW step for states at `K`, from the private
coatom** (`ProfileTower.LowStateRepair`).  For the
private context a source-gap context of grade `g + 1 ≤ m` with the lost point last, the donor of
top grade at most `g + 1`, owner and lost top the copies `o`, `r`, the donor tops the copies of the
tops of the donor, the copies of the proper donor cells of grade at most `g + 1` proper donor
fields, and the proper donor fields below the donor coatom: the donor face is raised
(`StageType.IsLowFamily.exists_raised_of_gap`). -/
theorem lowStateRaise_private {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ g + 1)
    (ho : o = StageType.faceCell I.restrictFace_left o')
    (hr : r = StageType.faceCell I.restrictFace_left r')
    (hNQ : ∀ f ∈ N, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, g + 1))
    (hTR : ∀ f ∈ T, ∃ t, I.right.label t = ⊤ ∧
      f = Sum.inl (StageType.faceCell I.restrictFace_right t))
    (hTtop : ∀ t, I.right.label t = ⊤ →
      Sum.inl (StageType.faceCell I.restrictFace_right t) ∈ T)
    (hLoN : ∀ t, I.right.label t ≠ ⊤ → I.right.toCellScheme.grade t ≤ g + 1 →
      Sum.inl (StageType.faceCell I.restrictFace_right t) ∈ N) :
    LowStateRepair I (g + 1) (g + 1) N T o r (Fin.last (m + 1)) := by
  classical
  intro P hPC hPlow h hh hb A hA hAP hact hfh
  have hPD : I.amalgam.rows.IsLawfulBelow (coatD, g + 1) fun d ↦ P (Sum.inl d) := hPC.2
  have hAlC : I.amalgam.rows.IsLawfulBelow (coatC, g + 1) fun d ↦ A d := hA.1
  have hAlD : I.amalgam.rows.IsLawfulBelow (coatD, g + 1) fun d ↦ A d := hA.2
  have hfinish (W : Prof I) (hWD : I.amalgam.rows.IsLawfulBelow (coatD, g + 1) fun d ↦ W d)
      (hWC : ∀ d ∈ I.amalgam.toCellScheme.below (coatC, g + 1), W d = A d)
      (hWP : ∀ d, min (W d) h = min (P (Sum.inl d)) h)
      (hfr : ∀ x ∈ T, frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) ≤
        withCutoff W ⊥ x) :
      ∃ W : Prof I, IsCutLawful I (g + 1) W ∧
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase (Fin.last (m + 1)), g + 1), W d = A d) ∧
        (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧
        ∀ y ∈ T, frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCut W ⊥) ≤ withCut W ⊥ y :=
    ⟨W, ⟨(Rows.isLawfulBelow_congr fun d hd ↦ hWC d hd).mpr hAlC, hWD⟩, hWC, hWP, hfr⟩
  have hMh : donorMax N (withCutoff A ⊥) < h := hact.trans_le (min_le_right _ _)
  have hNP : ∀ f ∈ N, P f = withCutoff A ⊥ f := by
    intro f hf
    obtain ⟨e, rfl, -⟩ := hNQ f hf
    exact eq_of_min_eq_of_lt (hAP e) ((le_donorMax (a := withCutoff A ⊥) hf).trans_lt hMh)
  have hPact : donorMax N P < P (Sum.inr ()) := by
    rw [donorMax_congr hNP]
    exact hact.trans_le (min_le_left _ _)
  set c := frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCutoff A ⊥) with hc_def
  have hgap : ∀ x ∈ T, min c h ≤ P x := fun x hx ↦
    min_frontier_le_of_isLowAt hPlow hPact hh (hAP o) (hAP r) x hx
  have hhc : h < c := hfh
  -- the donor raising
  have hF : StageType.IsLowFamily (g + 1) I.left I.right I.face o' r' :=
    ⟨I.isLegal_left, I.isLegal_right, I.restrictFace_face_left, I.restrictFace_face_right, hs, htb⟩
  set fcL := StageType.faceCell I.restrictFace_left with hfcL
  set fcR := StageType.faceCell I.restrictFace_right with hfcR
  set f : Fin I.left.card → Label.{u} := I.left.toCellScheme.splice (g + 1) (fun _ ↦ ⊥)
    fun i ↦ A (fcL i) with hf_def
  set R : Fin I.right.card → Label.{u} := I.right.toCellScheme.splice (g + 1) (fun _ ↦ ⊥)
    fun j ↦ P (Sum.inl (fcR j)) with hR_def
  have hf : H2.LawfulAt I.left (g + 1) f := lawfulAt_left hAlC
  have hR : H2.LawfulAt I.right (g + 1) R := lawfulAt_right (W := amal P) hPD
  have hfle (i : Fin I.left.card) (hi : I.left.toCellScheme.grade i ≤ g + 1) : f i = A (fcL i) :=
    CellScheme.splice_of_le hi
  have hRle (j : Fin I.right.card) (hj : I.right.toCellScheme.grade j ≤ g + 1) :
      R j = P (Sum.inl (fcR j)) := CellScheme.splice_of_le hj
  have hroot (x : Fin I.face.card) :
      fcL (StageType.faceCell I.restrictFace_face_left x) =
        fcR (StageType.faceCell I.restrictFace_face_right x) :=
    StageType.faceCell_faceCell I.restrictFace_left I.restrictFace_right
      I.restrictFace_face_left I.restrictFace_face_right x
  have hag (x : Fin I.face.card) :
      min (f (StageType.faceCell I.restrictFace_face_left x)) h =
        min (R (StageType.faceCell I.restrictFace_face_right x)) h := by
    have hg : I.left.toCellScheme.grade (StageType.faceCell I.restrictFace_face_left x) =
        I.right.toCellScheme.grade (StageType.faceCell I.restrictFace_face_right x) := by
      rw [StageType.grade_faceCell, StageType.grade_faceCell]
    by_cases hx : I.left.toCellScheme.grade (StageType.faceCell I.restrictFace_face_left x) ≤ g + 1
    · rw [hfle _ hx, hRle _ (hg ▸ hx), hroot]; exact hAP _
    · rw [hf_def, hR_def, CellScheme.splice_of_lt (_root_.not_le.mp hx),
        CellScheme.splice_of_lt (_root_.not_le.mp (hg ▸ hx))]
  have hgo : I.left.toCellScheme.grade o' ≤ g + 1 := hs.grade_owner.le
  have hgr : I.left.toCellScheme.grade r' ≤ g + 1 :=
    hs.topGrade_eq ▸ StageType.grade_le_topGrade hs.label_lost
  have hcf : c = min (f o') (visibilityReplace (g + 1) (g + 1) (f r')) := by
    rw [hc_def, hfle o' hgo, hfle r' hgr, ← ho, ← hr]; rfl
  have htop : ∀ t, I.right.label t = ⊤ → I.right.toCellScheme.grade t ≤ g + 1 →
      t ∉ I.right.toScheme.visibleCells Fin.castSuccEmb → h ≤ R t := fun t ht hg _ ↦ by
    rw [hRle t hg]
    have := hgap _ (hTtop t ht)
    rwa [min_eq_right hhc.le] at this
  have hlow : ∀ t, I.right.label t ≠ ⊤ → I.right.toCellScheme.grade t ≤ g + 1 → R t < h :=
    fun t ht hg ↦ by
      rw [hRle t hg, hNP _ (hLoN t ht hg)]
      exact (le_donorMax (a := withCutoff A ⊥) (hLoN t ht hg)).trans_lt hMh
  obtain ⟨Wt, hWt, hWtr, hWtR, hWtc⟩ :=
    hF.exists_raised_of_gap hb hhc hR hf hag hlow hcf htop
  -- glue the raised donor face on the amalgam
  have he := StageType.comap_toScheme_of_restrictFace I.restrictFace_right
  have hX : Prod.map (Finset.map (Coatom.right m)) id ((univ : Finset (Fin (m + 1))), g + 1) =
      (coatD, g + 1) := by
    rw [Prod.map_apply, Coatom.univ_map_right]; rfl
  have hinj : Function.Injective fcR := Scheme.faceCell_injective he
  set wt' : Fin I.right.card → Label.{u} := fun j ↦
    if I.right.toCellScheme.grade j ≤ g + 1 then Wt j else A (fcR j) with hwt'
  set W : Prof I := Function.extend fcR wt' A with hW
  have hWf (j : Fin I.right.card) : W (fcR j) = wt' j := hinj.extend_apply _ _ j
  have hWle (j : Fin I.right.card) (hj : I.right.toCellScheme.grade j ≤ g + 1) :
      W (fcR j) = Wt j := (hWf j).trans (ite_eq_left hj)
  have hWgt (j : Fin I.right.card) (hj : ¬ I.right.toCellScheme.grade j ≤ g + 1) :
      W (fcR j) = A (fcR j) := (hWf j).trans (ite_eq_right hj)
  have hWC (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatC, g + 1)) :
      W d = A d := by
    by_cases hex : ∃ j, fcR j = d
    · obtain ⟨j, rfl⟩ := hex
      have hgj : I.right.toCellScheme.grade j ≤ g + 1 := by
        have := hd.2
        rwa [CellScheme.gradedIndex_snd, StageType.grade_faceCell] at this
      have hlj : Fin.last m ∉ I.right.toCellScheme.scope j := by
        intro hm
        have h1 : Fin.last (m + 1) ∈ I.amalgam.toCellScheme.scope (fcR j) := by
          rw [hfcR, StageType.scope_faceCell]
          exact mem_map.mpr ⟨Fin.last m, hm, by simp [Coatom.right]⟩
        have h2 := hd.1 h1
        simp at h2
      obtain ⟨x, rfl⟩ := StageType.exists_faceCell_eq_of_last_notMem I.restrictFace_face_right hlj
      rw [hWle _ hgj, hWtr x, ← hroot]
      have hgx : I.left.toCellScheme.grade (StageType.faceCell I.restrictFace_face_left x) ≤
          g + 1 := by
        rw [StageType.grade_faceCell, ← StageType.grade_faceCell I.restrictFace_face_right]
        exact hgj
      exact hfle _ hgx
    · exact Function.extend_apply' _ _ _ fun ⟨j, hj⟩ ↦ hex ⟨j, hj⟩
  have hWD : I.amalgam.rows.IsLawfulBelow (coatD, g + 1) fun d ↦ W d := by
    rw [← hX]
    refine (Scheme.isLawfulBelow_faceCell_iff he _ W).mp ?_
    exact (Rows.isLawfulBelow_congr (R := I.right.rows)
      (X := ((univ : Finset (Fin (m + 1))), g + 1)) (w := fun j ↦ Wt j) (w' := fun j ↦ W (fcR j))
      fun j hj ↦ (hWle j (show I.right.toCellScheme.grade j ≤ g + 1 from hj.2)).symm).mp hWt.1
  have hWP (d : Fin I.amalgam.card) : min (W d) h = min (P (Sum.inl d)) h := by
    by_cases hex : ∃ j, fcR j = d
    · obtain ⟨j, rfl⟩ := hex
      by_cases hgj : I.right.toCellScheme.grade j ≤ g + 1
      · rw [hWle j hgj, hWtR j, hRle j hgj]
      · rw [hWgt j hgj]; exact hAP _
    · have hWd : W d = A d := Function.extend_apply' _ _ _ fun ⟨j, hj⟩ ↦ hex ⟨j, hj⟩
      rw [hWd]; exact hAP d
  refine hfinish W hWD hWC hWP fun x hx ↦ ?_
  -- the frontier condition: the frontier is the prescribed one, at most every donor top
  have hob : o ∈ I.amalgam.toCellScheme.below (coatC, g + 1) := by
    rw [ho, CellScheme.mem_below, CellScheme.gradedIndex, StageType.scope_faceCell,
      StageType.grade_faceCell]
    exact ⟨(map_subset_map.mpr (subset_univ _)).trans Coatom.univ_map_left.le, hgo⟩
  have hrb : r ∈ I.amalgam.toCellScheme.below (coatC, g + 1) := by
    rw [hr, CellScheme.mem_below, CellScheme.gradedIndex, StageType.scope_faceCell,
      StageType.grade_faceCell]
    exact ⟨(map_subset_map.mpr (subset_univ _)).trans Coatom.univ_map_left.le, hgr⟩
  have hfW : frontier (g + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) = c := by
    rw [hc_def]
    unfold Label.frontier
    change min (W o) (visibilityReplace (g + 1) (g + 1) (W r)) =
      min (A o) (visibilityReplace (g + 1) (g + 1) (A r))
    rw [hWC o hob, hWC r hrb]
  rw [hfW]
  obtain ⟨t, ht, rfl⟩ := hTR x hx
  have hgt : I.right.toCellScheme.grade t ≤ g + 1 :=
    (StageType.topGrade_le_iff.mp htb) t ht
  change c ≤ W (fcR t)
  by_cases hvis : t ∈ I.right.toScheme.visibleCells Fin.castSuccEmb
  · obtain ⟨y, rfl⟩ := StageType.exists_faceCell_eq I.restrictFace_face_right hvis
    rw [hWle _ hgt, hWtr y, hcf]
    have hfo := H2.frontier_le_lawfulAt I.isLegal_left hs hf
    refine hfo.2 _ ?_ (StageType.last_notMem_scope_faceCell I.restrictFace_face_left y)
    rw [StageType.label_faceCell, ← StageType.label_faceCell I.restrictFace_face_right]
    exact ht
  · rw [hWle _ hgt]
    exact hWtc t ht hgt hvis


/-- **The repair at `K` for the LOW designations of a seed**, over the proper donor fields of grade
at most `K` (`ProfileTower.lowStateRaise_private`, `ProfileTower.lowStateRaise_donor`), from both
coatoms. -/
theorem lowStateRepair_seed (hgm : g + 1 ≤ m) {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ g + 1) {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    LowStateRepair I (g + 1) (g + 1) (lowN I (g + 1)) (lowT I)
      (StageType.faceCell I.restrictFace_left o') (StageType.faceCell I.restrictFace_left r')
      x := by
  classical
  have hNQ : ∀ f ∈ lowN I (g + 1), ∃ d, f = Sum.inl d ∧
      d ∈ I.amalgam.toCellScheme.below (coatD, g + 1) := by
    intro f hf
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hf
    exact ⟨_, rfl, faceCell_right_mem_below (mem_filter.mp ht).2.2⟩
  have hTQ : ∀ f ∈ lowT I, ∃ d, f = Sum.inl d ∧
      d ∈ I.amalgam.toCellScheme.below (coatD, g + 1) := by
    rintro f ⟨t, ht, rfl⟩
    exact ⟨_, rfl, faceCell_right_mem_below (StageType.topGrade_le_iff.mp htb t ht)⟩
  have hNroot : ∀ i, I.left.toCellScheme.grade i ≤ g + 1 →
      Fin.last m ∉ I.left.toCellScheme.scope i → I.left.label i ≠ ⊤ →
        Sum.inl (StageType.faceCell I.restrictFace_left i) ∈ lowN I (g + 1) := by
    intro i hi hl hit
    obtain ⟨y, rfl⟩ := StageType.exists_faceCell_eq_of_last_notMem I.restrictFace_face_left hl
    rw [StageType.faceCell_faceCell I.restrictFace_left I.restrictFace_right
      I.restrictFace_face_left I.restrictFace_face_right y]
    refine mem_image.mpr ⟨_, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩, rfl⟩
    · rw [StageType.label_faceCell, ← StageType.label_faceCell I.restrictFace_face_left y]
      exact hit
    · rw [StageType.grade_faceCell, ← StageType.grade_faceCell I.restrictFace_face_left y]
      exact hi
  simp only [Pts, mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact lowStateRaise_private hs htb rfl rfl hNQ (fun f hf ↦ hf) (fun t ht ↦ ⟨t, ht, rfl⟩)
      fun t ht htK ↦ mem_image.mpr ⟨t, mem_filter.mpr ⟨mem_univ _, ht, htK⟩, rfl⟩
  · exact lowStateRaise_donor hgm hs rfl rfl hNQ hTQ hNroot

/-- **The LOW step for states at the grade of the controllers**, for the LOW designations of a
seed (`ProfileTower.lowN`, `ProfileTower.lowT`, the copies of the owner and the lost top), when the
private context is a source-gap context of grade `g + 1 ≤ m` with the lost point last and the
donor has top grade at most `g + 1`: the step for states holds from both coatoms
(`ProfileTower.stateCatStep_low_of_raise`, `ProfileTower.lowStateRaise_donor`,
`ProfileTower.lowStateRaise_private`, through `ProfileTower.lowStateRepair_seed`). -/
theorem stateCatStep_low_seed (hgm : g + 1 ≤ m) {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ g + 1) {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    StateCatStep I (g + 1) (lowPred (g + 1) (lowN I (g + 1)) (lowT I)
      (StageType.faceCell I.restrictFace_left o')
      (StageType.faceCell I.restrictFace_left r')) x := by
  classical
  have hN : Sum.inr () ∉ lowN I (g + 1) := fun hf ↦ by
    obtain ⟨t, -, ht⟩ := mem_image.mp hf
    cases ht
  have hT : Sum.inr () ∉ lowT I := fun hf ↦ by
    obtain ⟨t, -, ht⟩ := hf
    cases ht
  exact stateCatStep_low_of_raise (Nat.succ_pos g) hgm le_rfl hN hT hx
    ((lowStateRepair_seed hgm hs htb hx).lowStateRaise le_rfl)

end VaughtConjecture.ProfileTower
