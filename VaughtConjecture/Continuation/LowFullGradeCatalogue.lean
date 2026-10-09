/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.TowerCatalogueLayer

/-!
# The catalogue layer as the layer of grade `m + 1`

Roadmap, Layer 3 ((R2), the LOW layer at the grade `K = k + 1`).

The capped lift from a coatom into a catalogue layer over a good level
(`ProfileTower.Lvl.Good.cappedLift_catS`) and its cap `⊥` and cap-ball steps on the amalgam
(`ProfileTower.Lvl.Good.exists_cutLawful_of_coatom`,
`ProfileTower.Lvl.Good.exists_cutLawful_of_coatom_cap`) were stated for `g + 1 ≤ m`.  On a seed of
`m + 2` points the coatoms have `m + 1` points, so the catalogue layer may sit at the grade
`m + 1`, the largest grade below the apex.

* `ProfileTower.Lvl.Good.cappedLift_catS_succ`: the capped lift for `g + 1 ≤ m + 1`, with the same
  proof (the coatom carries a cell of every grade up to `m + 1`).
* `ProfileTower.Lvl.Good.exists_cutLawful_of_coatom_top`,
  `ProfileTower.Lvl.Good.exists_cutLawful_of_coatom_cap_top`: the steps on the amalgam at the
  grade `m + 1`.  The common face of the two coatoms has `m` points, so it carries no cell of the
  grade `m + 1`: the trace on it is lifted from the graded face `(C ∩ D, m)` into the other coatom
  at the grade `m + 1` (bountifulness of the amalgam between graded faces of different grades), and
  every cell below both coatoms lies below `(C ∩ D, m)`.
* `ProfileTower.Lvl.Good.cappedLift_catS_of_catStep_top`: the capped lift at the grade `m + 1`
  from the catalogue step (`ProfileTower.Lvl.CatStep`).

## References

Bountifulness is [Kni26, Definition 2.5.14]; the catalogue layers are those of [Kni26, §4.3].
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

section Succ

variable {g : ℕ} {L : Lvl I g} {A : CProf I → Prop}

local notation "𝒞" => predCat I (g + 1) A

/-- **The capped lift from a coatom into the catalogue layer over a good level**, at the grade `g +
1`, for `g + 1 ≤ m`, given the catalogue step on the amalgam:

* at the cap `⊥`, every labelling lawful below the coatom is, at the amalgam cells below the coatom,
  an amalgam profile lawful on the grade-`(g + 1)` cut;
* at every profile `P` of the catalogue of `A` and every cap `h` self-visible and short at `g + 1`
  with `⊥ < h`, every labelling lawful below the coatom agreeing there with `P` capped at `h` is, at
  the amalgam cells below the coatom, an amalgam profile `W` lawful on the grade-`(g + 1)` cut
  agreeing with the amalgam part of `P` capped at `h`, with a coded cutoff `β` agreeing with that of
  `P` capped at `h` such that the orbit code of `W` with the cutoff `β` satisfies `A`.

The one-grade lift `CellScheme.Rows.cappedLift_of_boundary_short` with the boundary triple of the
coatom three times, the lift of the level at the grade `g`, and the extension through the
controllers (`ProfileTower.Lvl.Good.exists_extension_cat`,
`ProfileTower.Lvl.Good.exists_extension_cat_bot`). -/
theorem Lvl.Good.cappedLift_catS_succ (hL : L.Good) (hgm : g + 1 ≤ m + 1) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) (hA0 : A fun _ ↦ ⊥)
    (hbot : ∀ w : Fin (L.catS 𝒞).card → Label.{u},
      (L.catS 𝒞).rows.IsLawfulBelow (univ.erase x, g + 1) (fun z ↦ w z) →
      ∃ W : Prof I, IsCutLawful I (g + 1) W ∧
        (∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
          I.amalgam.toCellScheme.scope d ⊆ univ.erase x → W d = w (Fin.castAdd _ (L.embed d))) ∧
        A (withCut (orbitCode (g + 1) W) ⊥))
    (hstep : ∀ P ∈ 𝒞, ∀ h : Label.{u}, IsSelfVisible (g + 1) h → IsShort (g + 1) h → ⊥ < h →
      ∀ w : Fin (L.catS 𝒞).card → Label.{u},
      (L.catS 𝒞).rows.IsLawfulBelow (univ.erase x, g + 1) (fun z ↦ w z) →
      (∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
        I.amalgam.toCellScheme.scope d ⊆ univ.erase x →
          min (w (Fin.castAdd _ (L.embed d))) h = min (P (Sum.inl d)) h) →
      ∃ (W : Prof I) (β : Label.{u}), IsCutLawful I (g + 1) W ∧
        (∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
          I.amalgam.toCellScheme.scope d ⊆ univ.erase x → W d = w (Fin.castAdd _ (L.embed d))) ∧
        (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧ β ∈ codeGrid (g + 1) (bound I) ∧
        min β h = min (P (Sum.inr ())) h ∧
        A (withCut (orbitCode (g + 1) W) β)) :
    (L.catS 𝒞).rows.CappedLift (X := (univ.erase x, g + 1))
      (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  classical
  have hCsub : ∀ P ∈ 𝒞, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧
      IsCutLawful I (g + 1) (camal P) := fun P hP ↦ ⟨(mem_predCat.mp hP).1, (mem_predCat.mp hP).2.1⟩
  have hcard (z : Fin (m + 2)) : #(univ.erase z) = m + 1 := Seed.card_erase z
  have hlift : (L.catS 𝒞).rows.CappedLift (X := (univ.erase x, g))
      (Y := ((univ : Finset (Fin (m + 2))), g)) ⟨erase_subset _ _, le_rfl⟩ :=
    (L.cappedLift_catS_iff _ fun h ↦ absurd h.2 (by simp only; omega)).mpr (hL.lift x hx g le_rfl)
  obtain ⟨c, hc⟩ := I.exists_gradedIndex_eq (univ.erase x, g + 1)
    ⟨I.erase_mem_faces hx, by omega, show g + 1 ≤ #(univ.erase x) by rw [hcard]; omega⟩
    (Seed.ne_univ_erase x)
  have hle : ((univ.erase x, g + 1) : Finset (Fin (m + 2)) × ℕ) ≤
      ((univ : Finset (Fin (m + 2))), g + 1) := ⟨erase_subset _ _, le_rfl⟩
  -- the cells below the coatom are old amalgam cells
  have hcoat {z : Fin (L.catS 𝒞).card}
      (hz : z ∈ (L.catS 𝒞).toCellScheme.below (univ.erase x, g + 1)) :
      ∃ d, I.amalgam.toCellScheme.grade d ≤ g + 1 ∧
        I.amalgam.toCellScheme.scope d ⊆ univ.erase x ∧ z = Fin.castAdd _ (L.embed d) := by
    have hne : (L.catS 𝒞).toCellScheme.scope z ≠ univ := fun he ↦
      Seed.ne_univ_erase x (univ_subset_iff.mp (he ▸ (hz.1 :
        (L.catS 𝒞).toCellScheme.scope z ⊆ univ.erase x)))
    obtain ⟨d, hd, rfl⟩ := hL.exists_old_catS ((L.catS 𝒞).toCellScheme.below_mono hle hz) hne
    refine ⟨d, hd, ?_, rfl⟩
    have h1 : (L.catS 𝒞).toCellScheme.gradedIndex (Fin.castAdd _ (L.embed d)) ≤
        (univ.erase x, g + 1) := hz
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, hL.gradedIndex_embed] at h1
    exact h1.1
  obtain ⟨i₀, -⟩ := exists_equivFin_eq (C := 𝒞) (bot_mem_predCat hA0)
  refine Rows.cappedLift_of_boundary_short (U := (univ.erase x, g + 1))
    (V := (univ.erase x, g + 1)) (O := (univ.erase x, g + 1)) (erase_subset _ _)
    ⟨Fin.castAdd _ (L.embed c), by
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, hL.gradedIndex_embed, hc]⟩ hlift
    le_rfl le_rfl le_rfl hle hle (fun _ hd _ ↦ hd) (Rows.cappedLift_refl _)
    (Rows.cappedLift_refl _) ?_
    ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩ fun u hu ↦ ?_
  · -- the extension from the boundary at `⊥`
    intro w hw _ _
    obtain ⟨W, hW, hWw, hAW⟩ := hbot w hw
    have hQC : withCut (orbitCode (g + 1) W) ⊥ ∈ 𝒞 :=
      mem_predCat_of hW (mem_insert_self _ _) hAW
    obtain ⟨q, hq, hqW⟩ := hL.exists_extension_cat_bot hCsub hQC
    refine ⟨q, hq, fun z hz ↦ ?_, fun _ ↦ by simp⟩
    obtain ⟨z, hzY⟩ := z
    obtain ⟨d, hd, hds, rfl⟩ := hcoat (hz.elim id id)
    have := hqW d hd
    rwa [hWw d hd hds] at this
  · -- the serving controller and its row
    obtain ⟨i, rfl⟩ := L.exists_natAdd_eq_catS hu
    set P := ((𝒞).equivFin.symm i).1 with hP_def
    have hP : P ∈ 𝒞 := ((𝒞).equivFin.symm i).2
    obtain ⟨hPB, -, hPo, -⟩ := mem_predCat.mp hP
    have hrowB (z : (L.catS 𝒞).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
        (L.catS 𝒞).rows.rowBelow _ hu z = L.Φcat 𝒞 P z :=
      Scheme.appendFullCells_row_natAdd (S := L.S) (k := g + 1)
        (r := fun i ↦ L.Φcat 𝒞 ((𝒞).equivFin.symm i).1) (h := L.not_le) i _
    refine ⟨hL.catS_consistent hCsub _, fun z ↦ ?_, fun z ↦ ?_, fun h hh hs hb ↦ ?_⟩
    · rw [hrowB]; exact isShort_of_mem_codeGrid (hL.Φcat_mem_codeGrid hPB _)
    · rw [hrowB]; exact ne_top_of_mem_codeGrid (hL.Φcat_mem_codeGrid hPB _)
    · intro w hw _ hwS
      have hwP (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ g + 1)
          (hds : I.amalgam.toCellScheme.scope d ⊆ univ.erase x) :
          min (w (Fin.castAdd _ (L.embed d))) h = min (P (Sum.inl d)) h := by
        have hm : Fin.castAdd (𝒞).card (L.embed d) ∈
            (L.catS 𝒞).toCellScheme.below (univ.erase x, g + 1) := by
          rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd,
            hL.gradedIndex_embed]
          exact ⟨hds, hd⟩
        have h1 := hwS ⟨_, (L.catS 𝒞).toCellScheme.below_mono hle hm⟩ (.inl hm)
        rwa [hrowB, Lvl.Φcat_castAdd, hL.literal] at h1
      obtain ⟨W, β, hW, hWw, hWP, hβB, hβ, hlow⟩ := hstep P hP h hh hs hb w hw hwP
      obtain ⟨q, hq, hqW, hqa⟩ := hL.exists_extension_cat hCsub hP hPo hh hs hb.ne' hWP hβ
        (mem_predCat_of hW hβB hlow)
      refine ⟨q, hq, fun z hz ↦ ?_, fun z ↦ by rw [hrowB]; exact hqa z⟩
      obtain ⟨z, hzY⟩ := z
      obtain ⟨d, hd, hds, rfl⟩ := hcoat (hz.elim id id)
      have := hqW d hd
      rwa [hWw d hd hds] at this

end Succ

/-- **The lift from the common face of the two coatoms into a coatom at the grade `m + 1`**: the
common face has `m` points, so its graded face of grade `m` lies below the coatom at `m + 1`; for
`1 ≤ m` the lift is bountifulness of the amalgam, and for `m = 0` no cell lies below it. -/
theorem cappedLift_inter_succ {B C : Finset (Fin (m + 2))} (hB : B ∈ I.amalgam.toCellScheme.faces)
    (hBc : #B = m) (hC : C ∈ I.amalgam.toCellScheme.faces) (hCc : #C = m + 1)
    (h : ((B, m) : Finset (Fin (m + 2)) × ℕ) ≤ (C, m + 1)) : I.amalgam.rows.CappedLift h := by
  by_cases hm : 1 ≤ m
  · exact I.isBountiful
      (show ((B, m) : Finset (Fin (m + 2)) × ℕ) ∈ I.amalgam.toCellScheme.gradedFaces from
        ⟨hB, hm, hBc.ge⟩)
      (show ((C, m + 1) : Finset (Fin (m + 2)) × ℕ) ∈ I.amalgam.toCellScheme.gradedFaces from
        ⟨hC, by omega, hCc.ge⟩) h
  · refine (Rows.cappedLift_iff_forall_exists h).mpr fun _ _ _ q _ hq _ ↦
      ⟨q, hq, fun _ ↦ rfl, fun d ↦ ?_⟩
    exfalso
    have h1 : I.amalgam.toCellScheme.grade d.1 ≤ m := d.2.2
    have h2 := I.amalgam.isWellFormed.isWellFormed.grade_pos d.1
    omega

section Top

variable {L : Lvl I m} {A : CProf I → Prop} {C : Finset (CProf I)}

local notation "𝒞" => predCat I (m + 1) A

/-- **The catalogue step at the cap `⊥`**: for `m + 1 ≤ m`, every labelling of the catalogue layer
lawful below a coatom at the grade `m + 1` is, at the amalgam cells below the coatom, an amalgam
profile lawful on the grade-`(m + 1)` cut: lift its trace on the common face into the other coatom
at the cap `⊥` (bountifulness of the amalgam) and glue. -/
theorem Lvl.Good.exists_cutLawful_of_coatom_top (hL : L.Good) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) {w : Fin (L.catS C).card → Label.{u}}
    (hw : (L.catS C).rows.IsLawfulBelow (univ.erase x, m + 1) (fun z ↦ w z)) :
    ∃ W : Prof I, IsCutLawful I (m + 1) W ∧
      ∀ d, I.amalgam.toCellScheme.grade d ≤ m + 1 →
        I.amalgam.toCellScheme.scope d ⊆ univ.erase x → W d = w (Fin.castAdd _ (L.embed d)) := by
  classical
  obtain ⟨y, hy, hxy⟩ := Seed.exists_other hx
  obtain ⟨hOf, hOcard⟩ := inter_props (I := I) hx hy hxy
  have hcard (z : Fin (m + 2)) : #(univ.erase z) = m + 1 := Seed.card_erase z
  set a : Prof I := fun d ↦ w (Fin.castAdd _ (L.embed d)) with ha_def
  -- the amalgam labelling is lawful below the coatom `x`
  have ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, m + 1) fun d ↦ a d := by
    have h1 := (L.isLawfulBelow_catS_iff (C := C) (fun h ↦ Seed.ne_univ_erase x
      (univ_subset_iff.mp h.1))).mp hw
    exact (hL.isLawfulBelow_old_iff (X := (univ.erase x, m + 1)) (Seed.ne_univ_erase x)
      (w := fun e ↦ w (Fin.castAdd _ e))).mp h1
  -- lift the trace on the common face into the coatom `y` at the cap `⊥`
  set O : Finset (Fin (m + 2)) × ℕ := (univ.erase x ∩ univ.erase y, m) with hO
  have hOV : O ≤ (univ.erase y, m + 1) := ⟨inter_subset_right, by simp only [hO]; omega⟩
  have hOU : O ≤ (univ.erase x, m + 1) := ⟨inter_subset_left, by simp only [hO]; omega⟩
  have hlift : I.amalgam.rows.CappedLift hOV :=
    cappedLift_inter_succ hOf hOcard (I.erase_mem_faces hy) (Seed.card_erase _) hOV
  obtain ⟨q', hq', -, hq'a⟩ := (Rows.cappedLift_iff_forall_exists hOV).mp hlift ⊥
    (isSelfVisible_bot _) (fun d ↦ a d) (fun _ ↦ ⊥) (ha.mono hOU)
    (Rows.isLawfulBelow_const_bot _) fun _ ↦ by simp
  -- glue
  set W : Prof I := fun d ↦
    if hd : d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1) then a d
    else if hd' : d ∈ I.amalgam.toCellScheme.below (univ.erase y, m + 1) then q' ⟨d, hd'⟩
    else ⊥ with hW
  have hWx (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1)) :
      W d = a d := dite_eq_left hd
  have hWy (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase y, m + 1)) :
      W d = q' ⟨d, hd⟩ := by
    by_cases hdx : d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1)
    · rw [hWx d hdx]
      have hdO : d ∈ I.amalgam.toCellScheme.below O :=
        ⟨subset_inter hdx.1 hd.1, (I.amalgam.isWellFormed.isWellFormed.grade_le_card d).trans
          ((card_le_card (subset_inter hdx.1 hd.1)).trans hOcard.le)⟩
      exact (hq'a ⟨d, hdO⟩).symm
    · exact (dite_eq_right hdx).trans (dite_eq_left hd)
  have hWlx : I.amalgam.rows.IsLawfulBelow (univ.erase x, m + 1) fun d ↦ W d :=
    (Rows.isLawfulBelow_congr fun d hd ↦ (hWx d hd).symm).mp ha
  have hWly : I.amalgam.rows.IsLawfulBelow (univ.erase y, m + 1) fun d ↦ W d := by
    convert hq' using 1
    funext d
    exact hWy d.1 d.2
  refine ⟨W, lawful_pair hx hy hxy hWlx hWly, fun d hd hds ↦ hWx d ⟨hds, hd⟩⟩

/-- **The step on the amalgam at a positive cap, with the cap ball of a profile**: for a profile
`P` lawful on the grade-`(m + 1)` cut and a cap `h` self-visible at `m + 1`, every labelling lawful
below a coatom that agrees there with `P` capped at `h` is, at the amalgam cells below the coatom,
an amalgam profile lawful on the cut agreeing everywhere with `P` capped at `h`: the trace on the
common face is lifted into the other coatom in the cap ball of `P` (bountifulness of the amalgam),
and the cells above the cut keep `P`. -/
theorem Lvl.Good.exists_cutLawful_of_coatom_cap_top (hL : L.Good)
    {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) {P : Prof I}
    (hP : IsCutLawful I (m + 1) P) {h : Label.{u}} (hh : IsSelfVisible (m + 1) h)
    {w : Fin (L.catS C).card → Label.{u}}
    (hw : (L.catS C).rows.IsLawfulBelow (univ.erase x, m + 1) (fun z ↦ w z))
    (hwP : ∀ d, I.amalgam.toCellScheme.grade d ≤ m + 1 →
      I.amalgam.toCellScheme.scope d ⊆ univ.erase x →
        min (w (Fin.castAdd _ (L.embed d))) h = min (P d) h) :
    ∃ W : Prof I, IsCutLawful I (m + 1) W ∧
      (∀ d, I.amalgam.toCellScheme.grade d ≤ m + 1 →
        I.amalgam.toCellScheme.scope d ⊆ univ.erase x → W d = w (Fin.castAdd _ (L.embed d))) ∧
      ∀ d, min (W d) h = min (P d) h := by
  classical
  obtain ⟨y, hy, hxy⟩ := Seed.exists_other hx
  obtain ⟨hOf, hOcard⟩ := inter_props (I := I) hx hy hxy
  have hcard (z : Fin (m + 2)) : #(univ.erase z) = m + 1 := Seed.card_erase z
  set a : Prof I := fun d ↦ w (Fin.castAdd _ (L.embed d)) with ha_def
  have ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, m + 1) fun d ↦ a d := by
    have h1 := (L.isLawfulBelow_catS_iff (C := C) (fun h ↦ Seed.ne_univ_erase x
      (univ_subset_iff.mp h.1))).mp hw
    exact (hL.isLawfulBelow_old_iff (X := (univ.erase x, m + 1)) (Seed.ne_univ_erase x)
      (w := fun e ↦ w (Fin.castAdd _ e))).mp h1
  set O : Finset (Fin (m + 2)) × ℕ := (univ.erase x ∩ univ.erase y, m) with hO
  have hOV : O ≤ (univ.erase y, m + 1) := ⟨inter_subset_right, by simp only [hO]; omega⟩
  have hOU : O ≤ (univ.erase x, m + 1) := ⟨inter_subset_left, by simp only [hO]; omega⟩
  have hlift : I.amalgam.rows.CappedLift hOV :=
    cappedLift_inter_succ hOf hOcard (I.erase_mem_faces hy) (Seed.card_erase _) hOV
  obtain ⟨q', hq', hq'P, hq'a⟩ := (Rows.cappedLift_iff_forall_exists hOV).mp hlift h hh
    (fun d ↦ a d) (fun d ↦ P d) (ha.mono hOU) (hP.isLawfulBelow_erase hy)
    fun d ↦ (hwP d.1 (d.2.2.trans (by simp only [hO]; omega)) (subset_inter_iff.mp d.2.1).1).symm
  set W : Prof I := fun d ↦
    if hd : d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1) then a d
    else if hd' : d ∈ I.amalgam.toCellScheme.below (univ.erase y, m + 1) then q' ⟨d, hd'⟩
    else P d with hW
  have hWx (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1)) :
      W d = a d := dite_eq_left hd
  have hWy (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase y, m + 1)) :
      W d = q' ⟨d, hd⟩ := by
    by_cases hdx : d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1)
    · rw [hWx d hdx]
      have hdO : d ∈ I.amalgam.toCellScheme.below O :=
        ⟨subset_inter hdx.1 hd.1, (I.amalgam.isWellFormed.isWellFormed.grade_le_card d).trans
          ((card_le_card (subset_inter hdx.1 hd.1)).trans hOcard.le)⟩
      exact (hq'a ⟨d, hdO⟩).symm
    · exact (dite_eq_right hdx).trans (dite_eq_left hd)
  have hWlx : I.amalgam.rows.IsLawfulBelow (univ.erase x, m + 1) fun d ↦ W d :=
    (Rows.isLawfulBelow_congr fun d hd ↦ (hWx d hd).symm).mp ha
  have hWly : I.amalgam.rows.IsLawfulBelow (univ.erase y, m + 1) fun d ↦ W d := by
    convert hq' using 1
    funext d
    exact hWy d.1 d.2
  refine ⟨W, lawful_pair hx hy hxy hWlx hWly, fun d hd hds ↦ hWx d ⟨hds, hd⟩, fun d ↦ ?_⟩
  by_cases hdx : d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1)
  · rw [hWx d hdx]
    exact hwP d hdx.2 hdx.1
  · by_cases hdy : d ∈ I.amalgam.toCellScheme.below (univ.erase y, m + 1)
    · rw [hWy d hdy]
      exact hq'P ⟨d, hdy⟩
    · have hWd : W d = P d := (dite_eq_right hdx).trans (dite_eq_right hdy)
      rw [hWd]

/-- **The capped lift from a coatom into the catalogue layer at the grade `m + 1`, from the
catalogue step**: the cap `⊥` is `ProfileTower.Lvl.Good.exists_cutLawful_of_coatom_top`. -/
theorem Lvl.Good.cappedLift_catS_of_catStep_top (hL : L.Good) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) (hAbot : ∀ W : Prof I, A (withCut W ⊥))
    (hstep : L.CatStep A x) :
    (L.catS 𝒞).rows.CappedLift (X := (univ.erase x, m + 1))
      (Y := ((univ : Finset (Fin (m + 2))), m + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  have hA0 : A fun _ ↦ ⊥ := by
    convert hAbot (fun _ ↦ ⊥) using 1
    funext f
    rcases f with d | z <;> rfl
  hL.cappedLift_catS_succ le_rfl hx hA0 (fun _ hw ↦ by
    obtain ⟨W, hW, hWw⟩ := hL.exists_cutLawful_of_coatom_top hx hw
    exact ⟨W, hW, hWw, hAbot _⟩) hstep

end Top

end VaughtConjecture.ProfileTower
