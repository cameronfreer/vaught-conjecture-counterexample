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
  every cell below both coatoms lies below `(C ∩ D, m)`
  (`ProfileTower.exists_isCutLawful_of_coatom_succ`, for every `m`).
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
1`, for `g + 1 ≤ m + 1`, given the catalogue step on the amalgam:

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

section Top

variable {L : Lvl I m} {A : CProf I → Prop} {C : Finset (CProf I)}

local notation "𝒞" => predCat I (m + 1) A

/-- **The step on the amalgam at a positive cap, with the cap ball of a profile**: for a profile
`P` lawful on the grade-`(m + 1)` cut and a cap `h` self-visible at `m + 1`, every labelling lawful
below a coatom that agrees there with `P` capped at `h` is, at the amalgam cells below the coatom,
an amalgam profile lawful on the cut agreeing everywhere with `P` capped at `h`
(`ProfileTower.exists_isCutLawful_of_coatom_succ` at the old labels). -/
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
  have ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, m + 1)
      fun d ↦ w (Fin.castAdd _ (L.embed d)) :=
    (hL.isLawfulBelow_old_iff (X := (univ.erase x, m + 1)) (Seed.ne_univ_erase x)
      (w := fun e ↦ w (Fin.castAdd _ e))).mp ((L.isLawfulBelow_catS_iff (C := C)
        (fun h ↦ Seed.ne_univ_erase x (univ_subset_iff.mp h.1))).mp hw)
  obtain ⟨W, hW, hWa, hWP⟩ := exists_isCutLawful_of_coatom_succ hx hh hP
    (f := fun d ↦ w (Fin.castAdd _ (L.embed d))) ha fun d hd ↦ hwP d hd.2 hd.1
  exact ⟨W, hW, fun d hd hds ↦ hWa d ⟨hds, hd⟩, hWP⟩

/-- **The catalogue step at the cap `⊥`**: every labelling of the catalogue layer
lawful below a coatom at the grade `m + 1` is, at the amalgam cells below the coatom, an amalgam
profile lawful on the grade-`(m + 1)` cut
(`ProfileTower.Lvl.Good.exists_cutLawful_of_coatom_cap_top` at the profile `⊥` and the cap `⊥`). -/
theorem Lvl.Good.exists_cutLawful_of_coatom_top (hL : L.Good) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) {w : Fin (L.catS C).card → Label.{u}}
    (hw : (L.catS C).rows.IsLawfulBelow (univ.erase x, m + 1) (fun z ↦ w z)) :
    ∃ W : Prof I, IsCutLawful I (m + 1) W ∧
      ∀ d, I.amalgam.toCellScheme.grade d ≤ m + 1 →
        I.amalgam.toCellScheme.scope d ⊆ univ.erase x → W d = w (Fin.castAdd _ (L.embed d)) :=
  have ⟨W, hW, hWw, _⟩ := hL.exists_cutLawful_of_coatom_cap_top hx (P := fun _ ↦ ⊥)
    ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ (isSelfVisible_bot _) hw
    fun _ _ _ ↦ by simp
  ⟨W, hW, hWw⟩

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

/-! ### The case `m = 0`

The fill of the other coatom and the two steps on the amalgam at the grade `1`, on a seed of `2`
points: no positivity premise on `m`. -/

example {I : Seed.{u} α 0} {x : Fin 2} (hx : x ∈ (Pts : Finset (Fin 2))) {h : Label.{u}}
    (hh : IsSelfVisible 1 h) {P : Prof I} (hP : IsCutLawful I 1 P) {f : Prof I}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase x, 1) fun d ↦ f d)
    (hfP : ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, 1), min (f d) h = min (P d) h) :
    ∃ W : Prof I, IsCutLawful I 1 W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, 1), W d = f d) ∧
      ∀ d, min (W d) h = min (P d) h :=
  exists_isCutLawful_of_coatom_succ hx hh hP hf hfP

example {I : Seed.{u} α 0} {L : Lvl I 0} {C : Finset (CProf I)} (hL : L.Good) {x : Fin 2}
    (hx : x ∈ (Pts : Finset (Fin 2))) {P : Prof I} (hP : IsCutLawful I 1 P) {h : Label.{u}}
    (hh : IsSelfVisible 1 h) {w : Fin (L.catS C).card → Label.{u}}
    (hw : (L.catS C).rows.IsLawfulBelow (univ.erase x, 1) (fun z ↦ w z))
    (hwP : ∀ d, I.amalgam.toCellScheme.grade d ≤ 1 → I.amalgam.toCellScheme.scope d ⊆ univ.erase x →
      min (w (Fin.castAdd _ (L.embed d))) h = min (P d) h) :
    ∃ W : Prof I, IsCutLawful I 1 W ∧
      (∀ d, I.amalgam.toCellScheme.grade d ≤ 1 →
        I.amalgam.toCellScheme.scope d ⊆ univ.erase x → W d = w (Fin.castAdd _ (L.embed d))) ∧
      ∀ d, min (W d) h = min (P d) h :=
  hL.exists_cutLawful_of_coatom_cap_top hx hP hh hw hwP

example {I : Seed.{u} α 0} {L : Lvl I 0} {C : Finset (CProf I)} (hL : L.Good) {x : Fin 2}
    (hx : x ∈ (Pts : Finset (Fin 2))) {w : Fin (L.catS C).card → Label.{u}}
    (hw : (L.catS C).rows.IsLawfulBelow (univ.erase x, 1) (fun z ↦ w z)) :
    ∃ W : Prof I, IsCutLawful I 1 W ∧
      ∀ d, I.amalgam.toCellScheme.grade d ≤ 1 →
        I.amalgam.toCellScheme.scope d ⊆ univ.erase x → W d = w (Fin.castAdd _ (L.embed d)) :=
  hL.exists_cutLawful_of_coatom_top hx hw

end VaughtConjecture.ProfileTower
