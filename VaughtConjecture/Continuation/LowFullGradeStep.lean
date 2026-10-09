/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowFullGradeCatalogue
import VaughtConjecture.Continuation.LowFullGradeUnserved
import VaughtConjecture.Continuation.LowTowerLevel

/-!
# The capped lift into the LOW layer at the grade `m + 1`

Roadmap, Layer 3 ((R2), the LOW layer at the grade `K = k + 1`).

For a seed on `m + 2` points whose private context (on `k + 1 = m + 1` points) is a source-gap
context of grade `K = m + 1` with the lost point last, the owner is the cell of full scope and
grade `m + 1` of the private coatom, and the LOW layer is the catalogue layer at the grade `m + 1`
over a good level at the grade `m`.  The capped lift from either coatom into it
(`ProfileTower.Lvl.Good.cappedLift_lowS_seed_top`) holds under the designations of the seed with
no open hypothesis, as below the full grade (`ProfileTower.Lvl.Good.cappedLift_lowS_seed`):

* the unserved case at the full grade is `StageType.lowStepUnserved`;
* the tie case is that of a donor top of grade `K` (`StageType.lowStepTie_of_top_grade`);
* the two LOW steps from the coatoms (`ProfileTower.Lvl.Good.lowStep_donor_top`,
  `ProfileTower.Lvl.Good.lowStep_private_top`) are those below the full grade with the trace on
  the common face lifted from its graded face of grade `m` (the common face has `m` points); every
  cell below both coatoms lies below it;
* the capped lift from the LOW step is `ProfileTower.Lvl.Good.cappedLift_catS_of_catStep_top`.

## References

The LOW layer is the step of [AFK26] at the owner's grade; bountifulness is [Kni26, Definition
2.5.14].
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {N : Finset (Fin I.amalgam.card ⊕ Unit)}
  {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card} {L : Lvl I m}

local notation "𝒞" => lowCat I (m + 1) N T o r

/-- **The LOW step from the donor coatom, except in the unserved case.**  Let the private context
(the left face of the seed) be a source-gap context of grade `m + 1` with the lost point last,
owner `o'` and lost top `r'`, whose amalgam copies are the owner `o` and the lost top `r` of the
LOW catalogue, let the proper donor fields and the donor tops be cells below the donor coatom, and
let the proper root cells (avoiding the lost point, not tops) be proper donor fields.  Given the
unserved case of the private frontier (`StageType.LowStepUnserved`), the LOW step holds from the
donor coatom.  The trace of the prescription on the common face is lifted into the private coatom
capped at the cap (bountifulness of the amalgam); when the serving profile is active, the private
face is replaced by a section with frontier at most the cap and the same root
(`StageType.IsSourceGapContextAt.exists_frontier_le_of_unserved`); the frontier condition then
holds at every donor top, at most the cap or, below the cap, by the LOW clause of the serving
profile (capping commutes with the frontier); the cutoff is coded by `exists_codedCutoff`. -/
theorem Lvl.Good.lowStep_donor_top (hL : L.Good) {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (m + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (hU : StageType.LowStepUnserved (m + 1) I.left (Fin.last m) o' r')
    (ho : o = StageType.faceCell I.restrictFace_left o')
    (hr : r = StageType.faceCell I.restrictFace_left r')
    (hNQ : ∀ f ∈ N, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, m + 1))
    (hTQ : ∀ f ∈ T, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, m + 1))
    (hNroot : ∀ i, I.left.toCellScheme.grade i ≤ m + 1 →
      Fin.last m ∉ I.left.toCellScheme.scope i → I.left.label i ≠ ⊤ →
        Sum.inl (StageType.faceCell I.restrictFace_left i) ∈ N) :
    L.LowStep N T o r (Fin.castSucc (Fin.last m)) := by
  classical
  intro P hP h hh hsh hb w hw hwP
  obtain ⟨hPB, ⟨hPC, hPD⟩, hPo, hPlow⟩ := mem_lowCat.mp hP
  have hNinr : Sum.inr () ∉ N := fun hf ↦ by obtain ⟨d, hd, -⟩ := hNQ _ hf; cases hd
  have hTinr : Sum.inr () ∉ T := fun hf ↦ by obtain ⟨d, hd, -⟩ := hTQ _ hf; cases hd
  have hxP : Fin.castSucc (Fin.last m) ∈ (Pts : Finset (Fin (m + 2))) := by simp
  have hyP : Fin.last (m + 1) ∈ (Pts : Finset (Fin (m + 2))) := by simp
  have hxy : Fin.castSucc (Fin.last m) ≠ Fin.last (m + 1) := Seed.last_ne_castSucc.symm
  obtain ⟨hOf, hOcard⟩ := inter_props (I := I) hxP hyP hxy
  have hcard (z : Fin (m + 2)) : #(univ.erase z) = m + 1 := Seed.card_erase z
  -- the prescription, on the amalgam
  set a : Prof I := fun d ↦ w (Fin.castAdd _ (L.embed d)) with ha_def
  have ha : I.amalgam.rows.IsLawfulBelow (coatD, m + 1) fun d ↦ a d := by
    have h1 := (L.isLawfulBelow_lowS_iff (C := 𝒞) (fun h' ↦ Seed.ne_univ_erase _
      (univ_subset_iff.mp h'.1))).mp hw
    exact (hL.isLawfulBelow_old_iff (X := (coatD, m + 1)) (Seed.ne_univ_erase _)
      (w := fun e ↦ w (Fin.castAdd _ e))).mp h1
  have haP (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatD, m + 1)) :
      min (a d) h = min (P (Sum.inl d)) h := hwP d hd.2 hd.1
  -- lift the trace on the common face into the private coatom, capped at `h` along `P`
  set O : Finset (Fin (m + 2)) × ℕ := (coatD ∩ coatC, m) with hO
  have hOV : O ≤ (coatC, m + 1) := ⟨inter_subset_right, by simp only [hO]; omega⟩
  have hOU : O ≤ (coatD, m + 1) := ⟨inter_subset_left, by simp only [hO]; omega⟩
  have hlift : I.amalgam.rows.CappedLift hOV :=
    cappedLift_inter_succ hOf hOcard (I.erase_mem_faces hyP) (Seed.card_erase _) hOV
  obtain ⟨q', hq', hq'P, hq'a⟩ := (Rows.cappedLift_iff_forall_exists hOV).mp hlift h hh
    (fun d ↦ a d) (fun d ↦ P (Sum.inl d)) (ha.mono hOU) hPC
    fun d ↦ (haP d (I.amalgam.toCellScheme.below_mono hOU d.2)).symm
  -- the glued amalgam profile
  set A : Prof I := fun d ↦
    if hd : d ∈ I.amalgam.toCellScheme.below (coatD, m + 1) then a d
    else if hd' : d ∈ I.amalgam.toCellScheme.below (coatC, m + 1) then q' ⟨d, hd'⟩
    else P (Sum.inl d) with hA
  have hAD (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatD, m + 1)) :
      A d = a d := dite_eq_left hd
  have hAC (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatC, m + 1)) :
      A d = q' ⟨d, hd⟩ := by
    by_cases hdD : d ∈ I.amalgam.toCellScheme.below (coatD, m + 1)
    · rw [hAD d hdD]
      exact (hq'a ⟨d, ⟨subset_inter hdD.1 hd.1,
        (I.amalgam.isWellFormed.isWellFormed.grade_le_card d).trans
        ((card_le_card (subset_inter hdD.1 hd.1)).trans hOcard.le)⟩⟩).symm
    · exact (dite_eq_right hdD).trans (dite_eq_left hd)
  have hAP (d : Fin I.amalgam.card) : min (A d) h = min (P (Sum.inl d)) h := by
    by_cases hdD : d ∈ I.amalgam.toCellScheme.below (coatD, m + 1)
    · rw [hAD d hdD]; exact haP d hdD
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (coatC, m + 1)
    · rw [hAC d hdC]; exact hq'P ⟨d, hdC⟩
    · have hAd : A d = P (Sum.inl d) := (dite_eq_right hdD).trans (dite_eq_right hdC)
      rw [hAd]
  have hAlD : I.amalgam.rows.IsLawfulBelow (coatD, m + 1) fun d ↦ A d :=
    (Rows.isLawfulBelow_congr fun d hd ↦ (hAD d hd).symm).mp ha
  have hAlC : I.amalgam.rows.IsLawfulBelow (coatC, m + 1) fun d ↦ A d := by
    convert hq' using 1
    funext d
    exact hAC d.1 d.2
  -- the agreement and the coded cutoff, for a profile equal to `A` below the donor coatom
  have hfinish (W : Prof I) (hWC : I.amalgam.rows.IsLawfulBelow (coatC, m + 1) fun d ↦ W d)
      (hWD : ∀ d ∈ I.amalgam.toCellScheme.below (coatD, m + 1), W d = A d)
      (hWP : ∀ d, min (W d) h = min (P (Sum.inl d)) h)
      (hfr : donorMax N (withCutoff W ⊥) < min (P (Sum.inr ())) h →
        ∀ x ∈ T, frontier (m + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) ≤ withCutoff W ⊥ x) :
      ∃ (W : Prof I) (β : Label.{u}), IsCutLawful I (m + 1) W ∧
        (∀ d, I.amalgam.toCellScheme.grade d ≤ m + 1 →
          I.amalgam.toCellScheme.scope d ⊆ univ.erase (Fin.castSucc (Fin.last m)) →
            W d = w (Fin.castAdd _ (L.embed d))) ∧
        (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧ β ∈ codeGrid (m + 1) (bound I) ∧
        min β h = min (P (Sum.inr ())) h ∧
        IsLowAt (m + 1) N T (Sum.inl o) (Sum.inl r) (Sum.inr ())
          (withCutoff (orbitCode (m + 1) W) β) := by
    obtain ⟨β, hβB, hβ, hlow⟩ := exists_codedCutoff hP hh hsh hWP hNinr hTinr hfr
    exact ⟨W, β, ⟨hWC, (Rows.isLawfulBelow_congr fun d hd ↦ hWD d hd).mpr hAlD⟩,
      fun d hd hds ↦ (hWD d ⟨hds, hd⟩).trans (hAD d ⟨hds, hd⟩), hWP, hβB, hβ, hlow⟩
  by_cases hact : donorMax N (withCutoff A ⊥) < min (P (Sum.inr ())) h
  swap
  · exact hfinish A hAlC (fun _ _ ↦ rfl) hAP fun h' ↦ absurd h' hact
  -- the private face, lowered
  have he := StageType.comap_toScheme_of_restrictFace I.restrictFace_left
  have hX : Prod.map (Finset.map (Coatom.left m)) id ((univ : Finset (Fin (m + 1))), m + 1) =
      (coatC, m + 1) := by
    rw [Prod.map_apply, Coatom.univ_map_left]; rfl
  set fc : Fin I.left.card → Fin I.amalgam.card := StageType.faceCell I.restrictFace_left with hfc
  set ut : Fin I.left.card → Label.{u} := fun i ↦ A (fc i) with hut_def
  have hut : I.left.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), m + 1)
      (fun i ↦ ut i) := by
    refine (Scheme.isLawfulBelow_faceCell_iff he _ A).mpr ?_
    rw [hX]
    exact hAlC
  have hMh : donorMax N (withCutoff A ⊥) < h := hact.trans_le (min_le_right _ _)
  have hroot : ∀ i, I.left.toCellScheme.grade i ≤ m + 1 →
      Fin.last m ∉ I.left.toCellScheme.scope i → I.left.label i ≠ ⊤ → ut i ≤ h := fun i hi hl ht ↦
    ((le_donorMax (a := withCutoff A ⊥) (hNroot i hi hl ht)).trans hMh.le)
  obtain ⟨vt, hvt, hvcap, hvroot, hvfr⟩ :=
    hs.exists_frontier_le_of_unserved I.isLegal_left hU hut hh hb hroot
  have hinj : Function.Injective fc := Scheme.faceCell_injective he
  set vt' : Fin I.left.card → Label.{u} := fun i ↦
    if I.left.toCellScheme.grade i ≤ m + 1 then vt i else ut i with hvt'
  set W : Prof I := Function.extend fc vt' A with hW
  have hWf (i : Fin I.left.card) : W (fc i) = vt' i := hinj.extend_apply _ _ i
  have hWle (i : Fin I.left.card) (hi : I.left.toCellScheme.grade i ≤ m + 1) :
      W (fc i) = vt i := (hWf i).trans (ite_eq_left hi)
  have hWgt (i : Fin I.left.card) (hi : ¬ I.left.toCellScheme.grade i ≤ m + 1) :
      W (fc i) = ut i := (hWf i).trans (ite_eq_right hi)
  have hWD (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatD, m + 1)) :
      W d = A d := by
    by_cases hex : ∃ i, fc i = d
    · obtain ⟨i, rfl⟩ := hex
      have hgi : I.left.toCellScheme.grade i ≤ m + 1 := by
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
  have hWC : I.amalgam.rows.IsLawfulBelow (coatC, m + 1) fun d ↦ W d := by
    rw [← hX]
    refine (Scheme.isLawfulBelow_faceCell_iff he _ W).mp ?_
    exact (Rows.isLawfulBelow_congr (R := I.left.rows) (X := ((univ : Finset (Fin (m + 1))), m + 1))
      (w := fun i ↦ vt i) (w' := fun i ↦ W (fc i))
      fun i hi ↦ (hWle i (show I.left.toCellScheme.grade i ≤ m + 1 from hi.2)).symm).mp hvt
  have hWP (d : Fin I.amalgam.card) : min (W d) h = min (P (Sum.inl d)) h := by
    by_cases hex : ∃ i, fc i = d
    · obtain ⟨i, rfl⟩ := hex
      by_cases hgi : I.left.toCellScheme.grade i ≤ m + 1
      · rw [hWle i hgi, hvcap i hgi]; exact hAP _
      · rw [hWgt i hgi]; exact hAP _
    · have hWd : W d = A d := Function.extend_apply' _ _ _ fun ⟨i, hi⟩ ↦ hex ⟨i, hi⟩
      rw [hWd]; exact hAP d
  refine hfinish W hWC hWD hWP fun _ x hx ↦ ?_
  -- the frontier condition
  obtain ⟨d, rfl, hdD⟩ := hTQ x hx
  have hgo : I.left.toCellScheme.grade o' ≤ m + 1 := hs.grade_owner.le
  have hgr : I.left.toCellScheme.grade r' ≤ m + 1 :=
    (StageType.grade_le_topGrade hs.label_lost).trans hs.topGrade_eq.le
  have hfrW : frontier (m + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) ≤ h := by
    unfold Label.frontier
    change min (W o) (visibilityReplace (m + 1) (m + 1) (W r)) ≤ h
    rw [ho, hr, hWle o' hgo, hWle r' hgr]
    exact hvfr
  change frontier (m + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) ≤ W d
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
  have hmin := min_frontier_eq (K := m + 1) (o := Sum.inl o) (r := Sum.inl r)
    (a := withCutoff W ⊥) (b := P) hh (hWP o) (hWP r)
  have hfP : frontier (m + 1) (Sum.inl o) (Sum.inl r) P < h := hPx.trans_lt (hAPd ▸ hAh)
  have h2 : min (frontier (m + 1) (Sum.inl o) (Sum.inl r) P) h =
      min (frontier (m + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥)) h := hmin.symm
  have hfW : frontier (m + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) =
      frontier (m + 1) (Sum.inl o) (Sum.inl r) P := eq_of_min_eq_of_lt h2 hfP
  rw [hfW, ← hAPd]
  exact hPx

/-- **The LOW step from the private coatom, except in the tie case.**  Let the private context be
a source-gap context of grade `m + 1` with the lost point last, owner `o'` and lost top `r'`
(copies `o`, `r`), the donor of top grade at most `m + 1`, the donor tops the copies of the tops of
the donor, the copies of the proper donor cells of grade at most `m + 1` proper donor fields, and
the proper donor fields cells below the donor coatom.  Given the tie case of the donor face
(`StageType.LowStepTie`), the LOW step holds from the private coatom.  The trace of the
prescription on the common face is lifted into the donor coatom capped at the cap; when the
serving profile is active and the prescribed private frontier `c` is above the cap, the donor face
is replaced by one reading every donor top off the root at least at `c`
(`StageType.IsLowFamily.exists_raised`; the root tops are at least `c` by the strict source gaps);
when `c` is at most the cap, the capped agreement with the serving profile already gives the
frontier condition; the cutoff is coded by `exists_codedCutoff`. -/
theorem Lvl.Good.lowStep_private_top (hL : L.Good) {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (m + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ m + 1)
    (hTie : StageType.LowStepTie (m + 1) I.left I.right I.restrictFace_face_left
      I.restrictFace_face_right o' r')
    (ho : o = StageType.faceCell I.restrictFace_left o')
    (hr : r = StageType.faceCell I.restrictFace_left r')
    (hNQ : ∀ f ∈ N, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, m + 1))
    (hTR : ∀ f ∈ T, ∃ t, I.right.label t = ⊤ ∧
      f = Sum.inl (StageType.faceCell I.restrictFace_right t))
    (hTtop : ∀ t, I.right.label t = ⊤ →
      Sum.inl (StageType.faceCell I.restrictFace_right t) ∈ T)
    (hLoN : ∀ t, I.right.label t ≠ ⊤ → I.right.toCellScheme.grade t ≤ m + 1 →
      Sum.inl (StageType.faceCell I.restrictFace_right t) ∈ N) :
    L.LowStep N T o r (Fin.last (m + 1)) := by
  classical
  intro P hP h hh hsh hb w hw hwP
  obtain ⟨hPB, ⟨hPC, hPD⟩, hPo, hPlow⟩ := mem_lowCat.mp hP
  have hNinr : Sum.inr () ∉ N := fun hf ↦ by obtain ⟨d, hd, -⟩ := hNQ _ hf; cases hd
  have hTinr : Sum.inr () ∉ T := fun hf ↦ by obtain ⟨d, -, hd⟩ := hTR _ hf; cases hd
  have hxP : Fin.last (m + 1) ∈ (Pts : Finset (Fin (m + 2))) := by simp
  have hyP : Fin.castSucc (Fin.last m) ∈ (Pts : Finset (Fin (m + 2))) := by simp
  have hxy : Fin.last (m + 1) ≠ Fin.castSucc (Fin.last m) := Seed.last_ne_castSucc
  obtain ⟨hOf, hOcard⟩ := inter_props (I := I) hxP hyP hxy
  have hcard (z : Fin (m + 2)) : #(univ.erase z) = m + 1 := Seed.card_erase z
  set a : Prof I := fun d ↦ w (Fin.castAdd _ (L.embed d)) with ha_def
  have ha : I.amalgam.rows.IsLawfulBelow (coatC, m + 1) fun d ↦ a d := by
    have h1 := (L.isLawfulBelow_lowS_iff (C := 𝒞) (fun h' ↦ Seed.ne_univ_erase _
      (univ_subset_iff.mp h'.1))).mp hw
    exact (hL.isLawfulBelow_old_iff (X := (coatC, m + 1)) (Seed.ne_univ_erase _)
      (w := fun e ↦ w (Fin.castAdd _ e))).mp h1
  have haP (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatC, m + 1)) :
      min (a d) h = min (P (Sum.inl d)) h := hwP d hd.2 hd.1
  set O : Finset (Fin (m + 2)) × ℕ := (coatC ∩ coatD, m) with hO
  have hOV : O ≤ (coatD, m + 1) := ⟨inter_subset_right, by simp only [hO]; omega⟩
  have hOU : O ≤ (coatC, m + 1) := ⟨inter_subset_left, by simp only [hO]; omega⟩
  have hlift : I.amalgam.rows.CappedLift hOV :=
    cappedLift_inter_succ hOf hOcard (I.erase_mem_faces hyP) (Seed.card_erase _) hOV
  obtain ⟨q', hq', hq'P, hq'a⟩ := (Rows.cappedLift_iff_forall_exists hOV).mp hlift h hh
    (fun d ↦ a d) (fun d ↦ P (Sum.inl d)) (ha.mono hOU) hPD
    fun d ↦ (haP d (I.amalgam.toCellScheme.below_mono hOU d.2)).symm
  set A : Prof I := fun d ↦
    if hd : d ∈ I.amalgam.toCellScheme.below (coatC, m + 1) then a d
    else if hd' : d ∈ I.amalgam.toCellScheme.below (coatD, m + 1) then q' ⟨d, hd'⟩
    else P (Sum.inl d) with hA
  have hAC (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatC, m + 1)) :
      A d = a d := dite_eq_left hd
  have hAD (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatD, m + 1)) :
      A d = q' ⟨d, hd⟩ := by
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (coatC, m + 1)
    · rw [hAC d hdC]
      exact (hq'a ⟨d, ⟨subset_inter hdC.1 hd.1,
        (I.amalgam.isWellFormed.isWellFormed.grade_le_card d).trans
        ((card_le_card (subset_inter hdC.1 hd.1)).trans hOcard.le)⟩⟩).symm
    · exact (dite_eq_right hdC).trans (dite_eq_left hd)
  have hAP (d : Fin I.amalgam.card) : min (A d) h = min (P (Sum.inl d)) h := by
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (coatC, m + 1)
    · rw [hAC d hdC]; exact haP d hdC
    by_cases hdD : d ∈ I.amalgam.toCellScheme.below (coatD, m + 1)
    · rw [hAD d hdD]; exact hq'P ⟨d, hdD⟩
    · have hAd : A d = P (Sum.inl d) := (dite_eq_right hdC).trans (dite_eq_right hdD)
      rw [hAd]
  have hAlC : I.amalgam.rows.IsLawfulBelow (coatC, m + 1) fun d ↦ A d :=
    (Rows.isLawfulBelow_congr fun d hd ↦ (hAC d hd).symm).mp ha
  have hAlD : I.amalgam.rows.IsLawfulBelow (coatD, m + 1) fun d ↦ A d := by
    convert hq' using 1
    funext d
    exact hAD d.1 d.2
  have hfinish (W : Prof I) (hWD : I.amalgam.rows.IsLawfulBelow (coatD, m + 1) fun d ↦ W d)
      (hWC : ∀ d ∈ I.amalgam.toCellScheme.below (coatC, m + 1), W d = A d)
      (hWP : ∀ d, min (W d) h = min (P (Sum.inl d)) h)
      (hfr : donorMax N (withCutoff W ⊥) < min (P (Sum.inr ())) h →
        ∀ x ∈ T, frontier (m + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) ≤ withCutoff W ⊥ x) :
      ∃ (W : Prof I) (β : Label.{u}), IsCutLawful I (m + 1) W ∧
        (∀ d, I.amalgam.toCellScheme.grade d ≤ m + 1 →
          I.amalgam.toCellScheme.scope d ⊆ univ.erase (Fin.last (m + 1)) →
            W d = w (Fin.castAdd _ (L.embed d))) ∧
        (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧ β ∈ codeGrid (m + 1) (bound I) ∧
        min β h = min (P (Sum.inr ())) h ∧
        IsLowAt (m + 1) N T (Sum.inl o) (Sum.inl r) (Sum.inr ())
          (withCutoff (orbitCode (m + 1) W) β) := by
    obtain ⟨β, hβB, hβ, hlow⟩ := exists_codedCutoff hP hh hsh hWP hNinr hTinr hfr
    exact ⟨W, β, ⟨(Rows.isLawfulBelow_congr fun d hd ↦ hWC d hd).mpr hAlC, hWD⟩,
      fun d hd hds ↦ (hWC d ⟨hds, hd⟩).trans (hAC d ⟨hds, hd⟩), hWP, hβB, hβ, hlow⟩
  by_cases hact : donorMax N (withCutoff A ⊥) < min (P (Sum.inr ())) h
  swap
  · exact hfinish A hAlD (fun _ _ ↦ rfl) hAP fun h' ↦ absurd h' hact
  have hMh : donorMax N (withCutoff A ⊥) < h := hact.trans_le (min_le_right _ _)
  have hNP : ∀ f ∈ N, P f = withCutoff A ⊥ f := by
    intro f hf
    obtain ⟨e, rfl, -⟩ := hNQ f hf
    exact eq_of_min_eq_of_lt (hAP e) ((le_donorMax (a := withCutoff A ⊥) hf).trans_lt hMh)
  have hPact : donorMax N P < P (Sum.inr ()) := by
    rw [donorMax_congr hNP]
    exact hact.trans_le (min_le_left _ _)
  -- the prescribed private frontier
  set c := frontier (m + 1) (Sum.inl o) (Sum.inl r) (withCutoff A ⊥) with hc_def
  have hgap : ∀ x ∈ T, min c h ≤ P x := fun x hx ↦
    min_frontier_le_of_isLowAt hPlow hPact hh (hAP o) (hAP r) x hx
  by_cases hch : c ≤ h
  · refine hfinish A hAlD (fun _ _ ↦ rfl) hAP fun _ x hx ↦ ?_
    obtain ⟨t, -, rfl⟩ := hTR x hx
    have h1 := hgap _ hx
    rw [min_eq_left hch] at h1
    have h2 : min c h ≤ min (A (StageType.faceCell I.restrictFace_right t)) h := by
      rw [hAP]; exact le_min ((min_le_left _ _).trans h1) (min_le_right _ _)
    rw [min_eq_left hch] at h2
    exact h2.trans (min_le_left _ _)
  have hhc : h < c := _root_.not_le.mp hch
  -- the donor raising
  have hF : StageType.IsLowFamily (m + 1) I.left I.right I.face o' r' :=
    ⟨I.isLegal_left, I.isLegal_right, I.restrictFace_face_left, I.restrictFace_face_right, hs, htb⟩
  set fcL := StageType.faceCell I.restrictFace_left with hfcL
  set fcR := StageType.faceCell I.restrictFace_right with hfcR
  set f : Fin I.left.card → Label.{u} := I.left.toCellScheme.splice (m + 1) (fun _ ↦ ⊥)
    fun i ↦ A (fcL i) with hf_def
  set R : Fin I.right.card → Label.{u} := I.right.toCellScheme.splice (m + 1) (fun _ ↦ ⊥)
    fun j ↦ P (Sum.inl (fcR j)) with hR_def
  have hf : H2.LawfulAt I.left (m + 1) f := lawfulAt_left hAlC
  have hR : H2.LawfulAt I.right (m + 1) R := lawfulAt_right (W := amal P) hPD
  have hfle (i : Fin I.left.card) (hi : I.left.toCellScheme.grade i ≤ m + 1) : f i = A (fcL i) :=
    CellScheme.splice_of_le hi
  have hRle (j : Fin I.right.card) (hj : I.right.toCellScheme.grade j ≤ m + 1) :
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
    by_cases hx : I.left.toCellScheme.grade (StageType.faceCell I.restrictFace_face_left x) ≤ m + 1
    · rw [hfle _ hx, hRle _ (hg ▸ hx), hroot]; exact hAP _
    · rw [hf_def, hR_def, CellScheme.splice_of_lt (_root_.not_le.mp hx),
        CellScheme.splice_of_lt (_root_.not_le.mp (hg ▸ hx))]
  have hgo : I.left.toCellScheme.grade o' ≤ m + 1 := hs.grade_owner.le
  have hgr : I.left.toCellScheme.grade r' ≤ m + 1 :=
    (StageType.grade_le_topGrade hs.label_lost).trans hs.topGrade_eq.le
  have hcf : c = min (f o') (visibilityReplace (m + 1) (m + 1) (f r')) := by
    rw [hc_def, hfle o' hgo, hfle r' hgr, ← ho, ← hr]; rfl
  have htop : ∀ t, I.right.label t = ⊤ → I.right.toCellScheme.grade t ≤ m + 1 →
      t ∉ I.right.toScheme.visibleCells Fin.castSuccEmb → h ≤ R t := fun t ht hg _ ↦ by
    rw [hRle t hg]
    have := hgap _ (hTtop t ht)
    rwa [min_eq_right hhc.le] at this
  have hlow : ∀ t, I.right.label t ≠ ⊤ → I.right.toCellScheme.grade t ≤ m + 1 → R t < h :=
    fun t ht hg ↦ by
      rw [hRle t hg, hNP _ (hLoN t ht hg)]
      exact (le_donorMax (a := withCutoff A ⊥) (hLoN t ht hg)).trans_lt hMh
  obtain ⟨Wt, hWt, hWtr, hWtR, hWtc⟩ :=
    hF.exists_raised hTie hh hb hhc hR hf hag hlow hcf htop
  -- glue the raised donor face on the amalgam
  have he := StageType.comap_toScheme_of_restrictFace I.restrictFace_right
  have hX : Prod.map (Finset.map (Coatom.right m)) id ((univ : Finset (Fin (m + 1))), m + 1) =
      (coatD, m + 1) := by
    rw [Prod.map_apply, Coatom.univ_map_right]; rfl
  have hinj : Function.Injective fcR := Scheme.faceCell_injective he
  set wt' : Fin I.right.card → Label.{u} := fun j ↦
    if I.right.toCellScheme.grade j ≤ m + 1 then Wt j else A (fcR j) with hwt'
  set W : Prof I := Function.extend fcR wt' A with hW
  have hWf (j : Fin I.right.card) : W (fcR j) = wt' j := hinj.extend_apply _ _ j
  have hWle (j : Fin I.right.card) (hj : I.right.toCellScheme.grade j ≤ m + 1) :
      W (fcR j) = Wt j := (hWf j).trans (ite_eq_left hj)
  have hWgt (j : Fin I.right.card) (hj : ¬ I.right.toCellScheme.grade j ≤ m + 1) :
      W (fcR j) = A (fcR j) := (hWf j).trans (ite_eq_right hj)
  have hWC (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatC, m + 1)) :
      W d = A d := by
    by_cases hex : ∃ j, fcR j = d
    · obtain ⟨j, rfl⟩ := hex
      have hgj : I.right.toCellScheme.grade j ≤ m + 1 := by
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
          m + 1 := by
        rw [StageType.grade_faceCell, ← StageType.grade_faceCell I.restrictFace_face_right]
        exact hgj
      exact hfle _ hgx
    · exact Function.extend_apply' _ _ _ fun ⟨j, hj⟩ ↦ hex ⟨j, hj⟩
  have hWD : I.amalgam.rows.IsLawfulBelow (coatD, m + 1) fun d ↦ W d := by
    rw [← hX]
    refine (Scheme.isLawfulBelow_faceCell_iff he _ W).mp ?_
    exact (Rows.isLawfulBelow_congr (R := I.right.rows)
      (X := ((univ : Finset (Fin (m + 1))), m + 1)) (w := fun j ↦ Wt j) (w' := fun j ↦ W (fcR j))
      fun j hj ↦ (hWle j (show I.right.toCellScheme.grade j ≤ m + 1 from hj.2)).symm).mp hWt.1
  have hWP (d : Fin I.amalgam.card) : min (W d) h = min (P (Sum.inl d)) h := by
    by_cases hex : ∃ j, fcR j = d
    · obtain ⟨j, rfl⟩ := hex
      by_cases hgj : I.right.toCellScheme.grade j ≤ m + 1
      · rw [hWle j hgj, hWtR j, hRle j hgj]
      · rw [hWgt j hgj]; exact hAP _
    · have hWd : W d = A d := Function.extend_apply' _ _ _ fun ⟨j, hj⟩ ↦ hex ⟨j, hj⟩
      rw [hWd]; exact hAP d
  refine hfinish W hWD hWC hWP fun _ x hx ↦ ?_
  -- the frontier condition: the frontier is the prescribed one, at most every donor top
  have hob : o ∈ I.amalgam.toCellScheme.below (coatC, m + 1) := by
    rw [ho, CellScheme.mem_below, CellScheme.gradedIndex, StageType.scope_faceCell,
      StageType.grade_faceCell]
    exact ⟨(map_subset_map.mpr (subset_univ _)).trans Coatom.univ_map_left.le, hgo⟩
  have hrb : r ∈ I.amalgam.toCellScheme.below (coatC, m + 1) := by
    rw [hr, CellScheme.mem_below, CellScheme.gradedIndex, StageType.scope_faceCell,
      StageType.grade_faceCell]
    exact ⟨(map_subset_map.mpr (subset_univ _)).trans Coatom.univ_map_left.le, hgr⟩
  have hfW : frontier (m + 1) (Sum.inl o) (Sum.inl r) (withCutoff W ⊥) = c := by
    rw [hc_def]
    unfold Label.frontier
    change min (W o) (visibilityReplace (m + 1) (m + 1) (W r)) =
      min (A o) (visibilityReplace (m + 1) (m + 1) (A r))
    rw [hWC o hob, hWC r hrb]
  rw [hfW]
  obtain ⟨t, ht, rfl⟩ := hTR x hx
  have hgt : I.right.toCellScheme.grade t ≤ m + 1 :=
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

/-- **The capped lift from a coatom into the LOW layer at the grade `m + 1` from the LOW step**
(`ProfileTower.Lvl.Good.cappedLift_catS_of_catStep_top`; the profiles with the cutoff `⊥` are
LOW). -/
theorem Lvl.Good.cappedLift_lowS_of_lowStep_top (hL : L.Good) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) (hstep : L.LowStep N T o r x) :
    (L.lowS 𝒞).rows.CappedLift (X := (univ.erase x, m + 1))
      (Y := ((univ : Finset (Fin (m + 2))), m + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  hL.cappedLift_catS_of_catStep_top hx lowPred_withCut_bot hstep

/-- **The capped lift from either coatom into the LOW layer over a good level, from the two
named cases.**  Under the designations of `ProfileTower.Lvl.Good.lowStep_donor` and
`ProfileTower.Lvl.Good.lowStep_private`, the unserved case of the private frontier
(`StageType.LowStepUnserved`) and the tie case of the donor face (`StageType.LowStepTie`) give the
capped lift from either coatom at the grade `m + 1` into `(univ, m + 1)`
(`ProfileTower.Lvl.Good.cappedLift_lowS_of_lowStep`). -/
theorem Lvl.Good.cappedLift_lowS_of_unserved_tie_top (hL : L.Good)
    {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (m + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ m + 1)
    (hU : StageType.LowStepUnserved (m + 1) I.left (Fin.last m) o' r')
    (hTie : StageType.LowStepTie (m + 1) I.left I.right I.restrictFace_face_left
      I.restrictFace_face_right o' r')
    (ho : o = StageType.faceCell I.restrictFace_left o')
    (hr : r = StageType.faceCell I.restrictFace_left r')
    (hNQ : ∀ f ∈ N, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, m + 1))
    (hTQ : ∀ f ∈ T, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, m + 1))
    (hNroot : ∀ i, I.left.toCellScheme.grade i ≤ m + 1 →
      Fin.last m ∉ I.left.toCellScheme.scope i → I.left.label i ≠ ⊤ →
        Sum.inl (StageType.faceCell I.restrictFace_left i) ∈ N)
    (hTR : ∀ f ∈ T, ∃ t, I.right.label t = ⊤ ∧
      f = Sum.inl (StageType.faceCell I.restrictFace_right t))
    (hTtop : ∀ t, I.right.label t = ⊤ →
      Sum.inl (StageType.faceCell I.restrictFace_right t) ∈ T)
    (hLoN : ∀ t, I.right.label t ≠ ⊤ → I.right.toCellScheme.grade t ≤ m + 1 →
      Sum.inl (StageType.faceCell I.restrictFace_right t) ∈ N)
    {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    (L.lowS 𝒞).rows.CappedLift (X := (univ.erase x, m + 1))
      (Y := ((univ : Finset (Fin (m + 2))), m + 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  refine hL.cappedLift_lowS_of_lowStep_top hx ?_
  rcases Finset.mem_insert.mp hx with rfl | hx'
  · exact hL.lowStep_private_top hs htb hTie ho hr hNQ hTR hTtop hLoN
  · rw [Finset.mem_singleton.mp hx']
    exact hL.lowStep_donor_top hs hU ho hr hNQ hTQ hNroot

/-- **The capped lift from either coatom into the LOW layer over a good level, from the tie case
alone**: at the full grade the unserved case holds (`StageType.lowStepUnserved`, `K = k + 1`
included), so `ProfileTower.Lvl.Good.cappedLift_lowS_of_unserved_tie_top` needs only
`StageType.LowStepTie`. -/
theorem Lvl.Good.cappedLift_lowS_of_tie_top (hL : L.Good)
    {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (m + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ m + 1)
    (hTie : StageType.LowStepTie (m + 1) I.left I.right I.restrictFace_face_left
      I.restrictFace_face_right o' r')
    (ho : o = StageType.faceCell I.restrictFace_left o')
    (hr : r = StageType.faceCell I.restrictFace_left r')
    (hNQ : ∀ f ∈ N, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, m + 1))
    (hTQ : ∀ f ∈ T, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, m + 1))
    (hNroot : ∀ i, I.left.toCellScheme.grade i ≤ m + 1 →
      Fin.last m ∉ I.left.toCellScheme.scope i → I.left.label i ≠ ⊤ →
        Sum.inl (StageType.faceCell I.restrictFace_left i) ∈ N)
    (hTR : ∀ f ∈ T, ∃ t, I.right.label t = ⊤ ∧
      f = Sum.inl (StageType.faceCell I.restrictFace_right t))
    (hTtop : ∀ t, I.right.label t = ⊤ →
      Sum.inl (StageType.faceCell I.restrictFace_right t) ∈ T)
    (hLoN : ∀ t, I.right.label t ≠ ⊤ → I.right.toCellScheme.grade t ≤ m + 1 →
      Sum.inl (StageType.faceCell I.restrictFace_right t) ∈ N)
    {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    (L.lowS 𝒞).rows.CappedLift (X := (univ.erase x, m + 1))
      (Y := ((univ : Finset (Fin (m + 2))), m + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  hL.cappedLift_lowS_of_unserved_tie_top hs htb
    (StageType.lowStepUnserved I.isLegal_left hs I.restrictFace_face_left) hTie ho hr
    hNQ hTQ hNroot hTR hTtop hLoN hx

/-- **The capped lift from either coatom into the LOW layer over a good level, when the donor has
a top of grade `m + 1`**: the tie case holds (`StageType.lowStepTie_of_top_grade`), so the capped
lift needs only the LOW designations. -/
theorem Lvl.Good.cappedLift_lowS_of_top_top (hL : L.Good)
    {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (m + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ m + 1) {z : Fin I.right.card} (hz : I.right.label z = ⊤)
    (hzK : I.right.toCellScheme.grade z = m + 1)
    (ho : o = StageType.faceCell I.restrictFace_left o')
    (hr : r = StageType.faceCell I.restrictFace_left r')
    (hNQ : ∀ f ∈ N, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, m + 1))
    (hTQ : ∀ f ∈ T, ∃ d, f = Sum.inl d ∧ d ∈ I.amalgam.toCellScheme.below (coatD, m + 1))
    (hNroot : ∀ i, I.left.toCellScheme.grade i ≤ m + 1 →
      Fin.last m ∉ I.left.toCellScheme.scope i → I.left.label i ≠ ⊤ →
        Sum.inl (StageType.faceCell I.restrictFace_left i) ∈ N)
    (hTR : ∀ f ∈ T, ∃ t, I.right.label t = ⊤ ∧
      f = Sum.inl (StageType.faceCell I.restrictFace_right t))
    (hTtop : ∀ t, I.right.label t = ⊤ →
      Sum.inl (StageType.faceCell I.restrictFace_right t) ∈ T)
    (hLoN : ∀ t, I.right.label t ≠ ⊤ → I.right.toCellScheme.grade t ≤ m + 1 →
      Sum.inl (StageType.faceCell I.restrictFace_right t) ∈ N)
    {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    (L.lowS 𝒞).rows.CappedLift (X := (univ.erase x, m + 1))
      (Y := ((univ : Finset (Fin (m + 2))), m + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  hL.cappedLift_lowS_of_tie_top hs htb
    (StageType.lowStepTie_of_top_grade (hF := ⟨I.isLegal_left, I.isLegal_right,
      I.restrictFace_face_left, I.restrictFace_face_right, hs, htb⟩) hz hzK) ho hr
    hNQ hTQ hNroot hTR hTtop hLoN hx

end VaughtConjecture.ProfileTower

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The capped lift from either coatom into the LOW layer at the grade `m + 1`, for the LOW
designations of the seed** (as `ProfileTower.Lvl.Good.cappedLift_lowS_seed`, at `g = m`), when
the private context is a source-gap context of grade `m + 1`
with the lost point last and the donor has top grade `m + 1`, attained: the designation hypotheses
of `ProfileTower.Lvl.Good.cappedLift_lowS_of_top` hold for `lowN`, `lowT` and the copies of the
owner and the lost top. -/
theorem Lvl.Good.cappedLift_lowS_seed_top {L : Lvl I m} (hL : L.Good)
    {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (m + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ m + 1) {z : Fin I.right.card} (hz : I.right.label z = ⊤)
    (hzK : I.right.toCellScheme.grade z = m + 1) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    (L.lowS (lowCat I (m + 1) (lowN I (m + 1)) (lowT I)
      (StageType.faceCell I.restrictFace_left o')
      (StageType.faceCell I.restrictFace_left r'))).rows.CappedLift
      (X := (univ.erase x, m + 1)) (Y := ((univ : Finset (Fin (m + 2))), m + 1))
      ⟨erase_subset _ _, le_rfl⟩ := by
  classical
  refine hL.cappedLift_lowS_of_top_top hs htb hz hzK rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ hx
  · intro f hf
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hf
    exact ⟨_, rfl, faceCell_right_mem_below (mem_filter.mp ht).2.2⟩
  · rintro f ⟨t, ht, rfl⟩
    exact ⟨_, rfl, faceCell_right_mem_below (StageType.topGrade_le_iff.mp htb t ht)⟩
  · intro i hi hl hit
    obtain ⟨y, rfl⟩ := StageType.exists_faceCell_eq_of_last_notMem I.restrictFace_face_left hl
    rw [StageType.faceCell_faceCell I.restrictFace_left I.restrictFace_right
      I.restrictFace_face_left I.restrictFace_face_right y]
    refine mem_image.mpr ⟨_, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩, rfl⟩
    · rw [StageType.label_faceCell, ← StageType.label_faceCell I.restrictFace_face_left y]
      exact hit
    · rw [StageType.grade_faceCell, ← StageType.grade_faceCell I.restrictFace_face_left y]
      exact hi
  · exact fun f hf ↦ hf
  · exact fun t ht ↦ ⟨t, ht, rfl⟩
  · exact fun t ht htK ↦ mem_image.mpr ⟨t, mem_filter.mpr ⟨mem_univ _, ht, htK⟩, rfl⟩

end VaughtConjecture.ProfileTower

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {g : ℕ} {L : Lvl I g}
  {A : CProf I → Prop}

local notation "𝒞" => predCat I (g + 1) A

/-- **The good level below the catalogue layer, and the catalogue layer lifting from the two
coatoms at the grade `g + 1`, give a good level**, for `g + 1 ≤ m + 1` (as
`ProfileTower.Lvl.Good.catNext`): the catalogue layer may be the layer of grade `m + 1`. -/
theorem Lvl.Good.catNext_succ (hL : L.Good) (hgm : g + 1 ≤ m + 1)
    (hA0 : ∀ W : Prof I, A (withCut W ⊥))
    (hlift : ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      (L.catS 𝒞).rows.CappedLift (X := (univ.erase x, g + 1))
        (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩) :
    (L.catNext A).Good := by
  have hCsub : ∀ P ∈ 𝒞, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧
      IsCutLawful I (g + 1) (camal P) := fun P hP ↦ ⟨(mem_predCat.mp hP).1, (mem_predCat.mp hP).2.1⟩
  have hemb := Scheme.isLowerEmbedding_castAdd (S := L.S) (g + 1) (𝒞).card
    (fun i ↦ L.Φcat 𝒞 ((𝒞).equivFin.symm i).1) L.not_le
  refine
    { lowerEmb := hemb.comp hL.lowerEmb
      scope_embed := fun d ↦ (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
        (hL.scope_embed d)
      comap_rows := ?_
      mem_range := ?_
      faces := hL.faces
      wf := Scheme.isWellFormed_appendFullCells (M := (𝒞).card)
        (r := fun i ↦ L.Φcat 𝒞 ((𝒞).equivFin.symm i).1) (h := L.not_le) hL.wf (by omega)
        (by omega)
      coded := Scheme.isCoded_appendFullCells (h := L.not_le) hL.coded fun i d ↦
        lt_omega0_sq_of_mem_codeGrid (hL.Φcat_mem_codeGrid (hCsub _ ((𝒞).equivFin.symm i).2).1 d)
      consistent := hL.catS_consistent hCsub
      lawful := fun P hP ↦ ?_
      mem := fun P hP z ↦ ?_
      literal := fun P d ↦ ?_
      capAgree := fun P P' hP h hh hs hag z ↦ ?_
      readable := fun Q hQ hQB z ↦ ?_
      lift := fun x hx j hj ↦ ?_
      complete := fun j hj0 hj ↦ ?_ }
  · have h := Rows.comap_comap (L.catS 𝒞).rows hemb hL.lowerEmb
    rw [Scheme.comap_rows_castAdd, hL.comap_rows] at h
    exact h.symm
  · intro z hz
    induction z using Fin.addCases with
    | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
    | left e =>
      have hz' : L.S.toCellScheme.scope e ≠ univ := by
        have := (Scheme.appendFullCellsScheme_scope_castAdd L.S (g + 1) (𝒞).card e)
        exact fun h ↦ hz (this.trans h)
      obtain ⟨d, rfl⟩ := hL.mem_range e hz'
      exact ⟨d, rfl⟩
  · -- lawful
    have hQ := withCut_code_mem_predCat hA0 hP
    have h := (hL.isLawfulBelow_Φcat hQ (hCsub _ hQ).1 (hCsub _ hQ).2).map_of_apply_eq_bot
      (fun z ↦ z.2.2)
      (isWitness_upperDecoderAt (w := hat I (g + 1) P) (B := bound I) (K := g + 2) (by omega))
      (fun _ ↦ eq_bot_of_upperDecoderAt_eq_bot)
    refine (Rows.isLawfulBelow_congr (R := (L.catS 𝒞).rows)
      (w := fun z ↦ upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) P)
        (L.Φcat 𝒞 (withCut (code (g + 1) P) ⊥) z)) (w' := L.catσ A P) fun z hz ↦ ?_).mp h
    exact (L.catσ_of_le hz.2).symm
  · -- mem
    change L.catσ A P z ∈ _
    by_cases hz : (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade z ≤ g + 1
    · rw [L.catσ_of_le hz]
      exact upperDecoderAt_mem_codeGrid_of_mem (by omega) (hat_mem_codeGrid hP)
        (hL.Φcat_mem_codeGrid (withCut_code_mem_codeGrid _) z)
    · obtain ⟨d, rfl⟩ := hL.exists_old_of_lt_cat hz
      rw [hL.catσ_old_of_lt hz]
      exact hP d
  · -- literal
    change L.catσ A P (Fin.castAdd _ (L.embed d)) = P d
    by_cases hd : (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade
        (Fin.castAdd _ (L.embed d)) ≤ g + 1
    · rw [L.catσ_of_le hd, Lvl.Φcat_castAdd, hL.literal]
      change upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) P)
        (code (g + 1) P d) = P d
      rw [upperDecoderAt_orbitCode, hat_of_le]
      rw [Scheme.appendFullCellsScheme_grade_castAdd, hL.lowerEmb.grade_eq] at hd
      exact hd
    · exact hL.catσ_old_of_lt hd
  · -- capAgree
    change min (L.catσ A P z) h = min (L.catσ A P' z) h
    by_cases hz : (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade z ≤ g + 1
    · rw [L.catσ_of_le hz, L.catσ_of_le hz]
      refine min_upperDecoderAt_comp_eq (k := g + 1) (K := g + 2) (by omega) hh hs
        (fun d ↦ le_gridPoint_of_mem_codeGrid (hat_mem_codeGrid hP d)) (min_hat_eq hag)
        (fun c ↦ L.Φcat 𝒞 (withCut c ⊥)) (fun c c' hc hc' Γ hΓv hΓs hcc z ↦ ?_) z
      have hcB (d : Fin I.amalgam.card) : c d ∈ codeGrid (g + 1) (bound I) :=
        codeGrid_mono (by simp only [Fintype.card_fin, bound]; omega) (hc d)
      have hcB' (d : Fin I.amalgam.card) : c' d ∈ codeGrid (g + 1) (bound I) :=
        codeGrid_mono (by simp only [Fintype.card_fin, bound]; omega) (hc' d)
      induction z using Fin.addCases with
      | left e =>
        rw [Lvl.Φcat_castAdd, Lvl.Φcat_castAdd]
        exact hL.capAgree c c' hcB Γ hΓv hΓs hcc e
      | right i =>
        rw [Lvl.Φcat_natAdd, Lvl.Φcat_natAdd]
        refine min_agreementHeight_eq_of_isShort hΓv hΓs (fun f ↦ ?_) (fun f ↦ ?_) _
        · rcases f with d | z
          · exact ⟨hcB d, hcB' d⟩
          · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
        · rcases f with d | z
          · exact hcc d
          · rfl
    · obtain ⟨d, rfl⟩ := hL.exists_old_of_lt_cat hz
      rw [hL.catσ_old_of_lt hz, hL.catσ_old_of_lt hz]
      exact hag d
  · -- readable
    change IsReadableAt (g + 1 + 1) Q (L.catσ A Q z)
    by_cases hz : (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade z ≤ g + 1
    · rw [L.catσ_of_le hz]
      refine isReadableAt_upperDecoderAt_of_mem hQ (by omega) (hat_mem_codeGrid hQB)
        (fun d ↦ ?_) (hL.Φcat_mem_codeGrid (withCut_code_mem_codeGrid _) z)
      by_cases hd : I.amalgam.toCellScheme.grade d ≤ g + 1
      · rw [hat_of_le hd]; exact isReadableAt_apply Q d
      · rw [hat_of_lt (_root_.not_le.mp hd)]; exact .inl rfl
    · obtain ⟨d, rfl⟩ := hL.exists_old_of_lt_cat hz
      rw [hL.catσ_old_of_lt hz]
      exact isReadableAt_apply Q d
  · -- lift
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact (L.cappedLift_catS_iff _ fun h ↦ absurd h.2 (by simp only; omega)).mpr
        (hL.lift x hx j (by omega))
    · exact hlift x hx
  · -- complete
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · obtain ⟨e, he⟩ := hL.complete j hj0 (by omega)
      exact ⟨Fin.castAdd _ e, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e).trans he⟩
    · obtain ⟨i₀, -⟩ := exists_equivFin_eq (C := 𝒞) (bot_mem_predCat (hA0 (fun _ ↦ ⊥) |> fun h ↦
        by convert h using 1; funext f; rcases f with d | z <;> rfl))
      exact ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩

/-- **The LOW layer at the grade `m + 1` is a good level**, for the LOW designations of the seed,
when the private context is a source-gap context of grade `m + 1` with the lost point last and the
donor has top grade `m + 1`, attained (`ProfileTower.Lvl.Good.catNext_succ`,
`ProfileTower.Lvl.Good.cappedLift_lowS_seed_top`). -/
theorem Lvl.Good.lowNext_top {L : Lvl I m} (hL : L.Good) {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (m + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ m + 1) {z : Fin I.right.card} (hz : I.right.label z = ⊤)
    (hzK : I.right.toCellScheme.grade z = m + 1) :
    (L.catNext (lowPred (m + 1) (lowN I (m + 1)) (lowT I)
      (StageType.faceCell I.restrictFace_left o')
      (StageType.faceCell I.restrictFace_left r'))).Good :=
  hL.catNext_succ le_rfl lowPred_withCut_bot fun _ hx ↦
    hL.cappedLift_lowS_seed_top hs htb hz hzK hx

end VaughtConjecture.ProfileTower
