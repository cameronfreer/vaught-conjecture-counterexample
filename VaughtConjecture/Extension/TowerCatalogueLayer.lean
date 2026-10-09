/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ProfileTower

/-!
# A catalogue layer over a level of the profile tower

Roadmap, Layer 3 (the controllers of the growth and LOW constructions over the lower full-scope
layers).

Over a level `L` of the profile tower at the grade `g` (`ProfileTower.Lvl`,
`VaughtConjecture.Extension.ProfileTower`), with a seed of two coatoms whose amalgam carries the
private context and the donor, this file appends the controllers at the grade `g + 1` for a
catalogue cut out by an arbitrary **predicate** `A` on profiles with a cutoff
(`ProfileTower.CProf`: labellings of the amalgam cells and one more field).

* **The catalogue of `A`** (`ProfileTower.predCat I k A`): the profiles with values in the code
  grid, amalgam part lawful on the grade-`k` cut and orbit-canonical, satisfying `A`.
* **The catalogue layer** (`ProfileTower.Lvl.catS`): one controller of scope `univ` and grade
  `g + 1` per profile, its row the section of the amalgam part and the agreement heights, cutoff
  included; lawful rows (`ProfileTower.Lvl.Good.isLawfulBelow_Φcat`) and consistency
  (`ProfileTower.Lvl.Good.catS_consistent`) over a good level, for every predicate.
* **Extension through the controllers** (`ProfileTower.Lvl.Good.exists_extension_cat`,
  `ProfileTower.Lvl.Good.exists_extension_cat_bot`).
* **The capped lift from a coatom** (`ProfileTower.Lvl.Good.cappedLift_catS`,
  `ProfileTower.Lvl.Good.cappedLift_catS_of_catStep`): when every profile with cutoff `⊥`
  satisfies `A`, the catalogue layer over a good level lifts capped from either coatom into the
  full face at the grade `g + 1`, given **the catalogue step** (`ProfileTower.Lvl.CatStep A`):
  closure of the catalogue under capped agreement from the coatom.  This is the one open
  hypothesis; the cap `⊥` is `ProfileTower.Lvl.Good.exists_cutLawful_of_coatom`.

**Instances.**  The LOW layer is the instance with `A` the LOW clause at the cutoff (every profile
with cutoff `⊥` is inactive, so LOW); the activation layer of the growth construction is the
instance with `A` the admission of a profile by the requests on the bottom class.  The
construction and proofs are those of the
LOW layer with the clause replaced by `A`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

variable (I) in
/-- A **profile with a cutoff** over the amalgam: a labelling of the cells of the amalgam and the
cutoff. -/
abbrev CProf : Type (u + 1) := Fin I.amalgam.card ⊕ Unit → Label.{u}

/-- The amalgam part of a profile with a cutoff. -/
abbrev camal (P : CProf I) : Prof I := fun d ↦ P (Sum.inl d)

/-- The profile with a cutoff of an amalgam profile and a cutoff. -/
abbrev withCut (W : Prof I) (β : Label.{u}) : CProf I := Sum.elim W fun _ ↦ β

variable (I) in
open Classical in
/-- The **catalogue of `A`** at the grade `k`: the profiles with a cutoff with values in the code
grid with block bound `2 N + 2`, whose amalgam part is lawful on the grade-`k` cut and
orbit-canonical at `k`. -/
noncomputable def predCat (k : ℕ) (A : CProf I → Prop) : Finset (CProf I) :=
  (Fintype.piFinset fun _ ↦ codeGrid k (bound I)).filter fun P ↦
    IsCutLawful I k (camal P) ∧ orbitCode k (camal P) = camal P ∧
      A P

variable {k : ℕ} {A : CProf I → Prop}

theorem mem_predCat {P : CProf I} : P ∈ predCat I k A ↔
    (∀ f, P f ∈ codeGrid k (bound I)) ∧ IsCutLawful I k (camal P) ∧
      orbitCode k (camal P) = camal P ∧ A P := by
  classical
  simp only [predCat, Finset.mem_filter, Fintype.mem_piFinset]

/-- **The coded profile of a cut-lawful amalgam profile with a coded cutoff lies in the
catalogue exactly when it satisfies `A`.** -/
theorem mem_predCat_of {W : Prof I} (hW : IsCutLawful I k W) {β : Label.{u}}
    (hβ : β ∈ codeGrid k (bound I))
    (hlow : A (withCut (orbitCode k W) β)) :
    withCut (orbitCode k W) β ∈ predCat I k A := by
  refine mem_predCat.mpr ⟨fun f ↦ ?_, ⟨hW.1.orbitCode fun d ↦ d.2.2,
    hW.2.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode, hlow⟩
  rcases f with d | z
  · exact codeGrid_mono (B := 2 * I.amalgam.card) (by simp only [bound]; omega)
      (orbitMap_mem_codeGrid (w := W) (by simp) _)
  · exact hβ

/-- The bottom profile is in the catalogue of `A`: it satisfies `A` by hypothesis. -/
theorem bot_mem_predCat (hA0 : A fun _ ↦ ⊥) : (fun _ ↦ ⊥ : CProf I) ∈ predCat I k A :=
  mem_predCat.mpr ⟨fun _ ↦ mem_insert_self _ _, (bot_mem_cat k |> mem_cat.mp).1,
    funext fun _ ↦ orbitCode_eq_bot_iff.mpr rfl, hA0⟩

/-! ### The catalogue layer over a level -/

variable {g : ℕ} {L : Lvl I g}

/-- The row labelling of a profile with a cutoff over a level at the grade `g`, for a finite set `C`
of profiles with a cutoff: the section of its amalgam part at the cells of the level, and the
agreement heights with the profiles of `C`, cutoff included. -/
noncomputable def Lvl.Φcat (L : Lvl I g) (C : Finset (CProf I)) (R : CProf I) :
    Fin (L.S.card + C.card) → Label.{u} :=
  Fin.append (L.σ (camal R)) fun i ↦
    agreementHeight (grid (g + 1) (bound I)) R (C.equivFin.symm i).1

/-- **The catalogue layer** over a level: one controller of scope `univ` and grade `g + 1` per
profile of `C`, with its row labelling. -/
noncomputable abbrev Lvl.catS (L : Lvl I g) (C : Finset (CProf I)) : Scheme.{u} (m + 2) :=
  L.S.appendFullCells (g + 1) C.card (fun i ↦ L.Φcat C (C.equivFin.symm i).1) L.not_le

variable {C : Finset (CProf I)}

@[simp] theorem Lvl.Φcat_castAdd (R : CProf I) (e : Fin L.S.card) :
    L.Φcat C R (Fin.castAdd _ e) = L.σ (camal R) e := Fin.append_left _ _ e

@[simp] theorem Lvl.Φcat_natAdd (R : CProf I) (i : Fin C.card) :
    L.Φcat C R (Fin.natAdd _ i) =
      agreementHeight (grid (g + 1) (bound I)) R (C.equivFin.symm i).1 :=
  Fin.append_right _ _ i

theorem exists_equivFin_eq {R : CProf I} (hR : R ∈ C) : ∃ i, (C.equivFin.symm i).1 = R :=
  ⟨C.equivFin ⟨R, hR⟩, by simp⟩

/-- The row labelling of a profile with values in the code grid lies in the code grid. -/
theorem Lvl.Good.Φcat_mem_codeGrid (hL : L.Good) {R : CProf I}
    (hR : ∀ f, R f ∈ codeGrid (g + 1) (bound I)) (z : Fin (L.S.card + C.card)) :
    L.Φcat C R z ∈ codeGrid (g + 1) (bound I) := by
  induction z using Fin.addCases with
  | left e => rw [Lvl.Φcat_castAdd]; exact hL.mem (camal R) (fun d ↦ hR _) e
  | right i =>
    rw [Lvl.Φcat_natAdd]
    exact grid_subset_codeGrid _ _ (agreementHeight_spec (bot_mem_grid _ _) _ _).1

/-- Lawfulness below a pair not above `(univ, g + 1)` in the catalogue layer is lawfulness in the
level. -/
theorem Lvl.isLawfulBelow_catS_iff {X : Finset (Fin (m + 2)) × ℕ}
    (hX : ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ X)
    {v : Fin (L.S.card + C.card) → Label.{u}} :
    (L.catS C).rows.IsLawfulBelow X (fun d ↦ v d) ↔
      L.S.rows.IsLawfulBelow X (fun d ↦ v (Fin.castAdd _ d)) :=
  Scheme.isLawfulBelow_appendFullCells_iff hX

/-- **The row labelling of a profile with a cutoff is lawful below `(univ, g + 1)`** in the
catalogue layer, for a profile of `C` with values in the code grid and amalgam part lawful on the
grade-`(g + 1)` cut. -/
theorem Lvl.Good.isLawfulBelow_Φcat (hL : L.Good) {R : CProf I} (hRC : R ∈ C)
    (hRB : ∀ f, R f ∈ codeGrid (g + 1) (bound I)) (hRc : IsCutLawful I (g + 1) (camal R)) :
    (L.catS C).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g + 1) fun z ↦ L.Φcat C R z := by
  classical
  obtain ⟨hC, hD⟩ := hRc
  have hlow : (L.catS C).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g)
      fun z ↦ L.Φcat C R z := by
    refine (L.isLawfulBelow_catS_iff (by rintro ⟨-, h⟩; simp only at h; omega)).mpr ?_
    simpa only [Lvl.Φcat_castAdd] using hL.lawful (camal R)
      ⟨hC.mono (X := (_, g)) ⟨subset_rfl, by omega⟩, hD.mono (X := (_, g)) ⟨subset_rfl, by omega⟩⟩
  have hcoat (x : Fin (m + 2))
      (hRX : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1) fun d ↦ camal R d) :
      (L.catS C).rows.IsLawfulBelow (univ.erase x, g + 1) fun z ↦ L.Φcat C R z := by
    refine (L.isLawfulBelow_catS_iff fun h ↦ Seed.ne_univ_erase x
      (univ_subset_iff.mp h.1)).mpr ?_
    simp only [Lvl.Φcat_castAdd]
    rw [hL.isLawfulBelow_old_iff (Seed.ne_univ_erase x)]
    exact (Rows.isLawfulBelow_congr (w' := fun d ↦ L.σ (camal R) (L.embed d))
      fun d _ ↦ (hL.literal (camal R) d).symm).mp hRX
  have hcC := hcoat _ hC
  have hcD := hcoat _ hD
  obtain ⟨ho2, hl2, ha2⟩ := Rows.isLawfulBelow_iff_forall.mp hlow
  obtain ⟨hoC, hlC, haC⟩ := Rows.isLawfulBelow_iff_forall.mp hcC
  obtain ⟨hoD, hlD, haD⟩ := Rows.isLawfulBelow_iff_forall.mp hcD
  have hcases {e : Fin L.S.card}
      (he : Fin.castAdd C.card e ∈
        (L.catS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
      Fin.castAdd C.card e ∈ (L.catS C).toCellScheme.below (coatC, g + 1) ∨
        Fin.castAdd C.card e ∈
          (L.catS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g) ∨
        Fin.castAdd C.card e ∈ (L.catS C).toCellScheme.below (coatD, g + 1) := by
    have he' : e ∈ L.S.toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) := by
      have := he
      rwa [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd] at this
    simp only [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
    exact hL.mem_below_cover (by simp) (by simp) Seed.last_ne_castSucc e he'
  obtain ⟨i₀, hi₀⟩ := exists_equivFin_eq hRC
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun z hz ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · induction z using Fin.addCases with
    | left e =>
      rcases hcases hz with h | h | h
      exacts [hoC _ h, ho2 _ h, hoD _ h]
    | right j =>
      rw [Scheme.appendFullCellsScheme_grade_natAdd, Lvl.Φcat_natAdd]
      exact isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid _ _) _ _).1
  · induction s using Fin.addCases with
    | left e =>
      rcases hcases hs with h | h | h
      exacts [hlC _ h, hl2 _ h, hlD _ h]
    | right j =>
      set κ := agreementHeight (grid (g + 1) (bound I)) R (C.equivFin.symm j).1 with hκ
      have hκm : κ ∈ grid (g + 1) (bound I) := (agreementHeight_spec (bot_mem_grid _ _) _ _).1
      have hκv : IsSelfVisible (g + 1) κ := isSelfVisible_of_mem_grid hκm
      refine ⟨constStepSuppressor (g + 1) κ, id, ⟨antitone_constStepSuppressor _ _,
        isSelfVisible_constStepSuppressor hκv, rfl, monotone_id, fun _ _ _ _ _ ↦ rfl⟩,
        fun t ↦ ?_⟩
      have htk : (L.catS C).toCellScheme.grade t ≤ g + 1 := t.2.2.trans_eq
        (congrArg Prod.snd (Scheme.appendFullCellsScheme_gradedIndex_natAdd L.S (g + 1) _ j))
      rw [Scheme.appendFullCells_row_natAdd, constStepSuppressor_of_le _ htk, id, Lvl.Φcat_natAdd]
      obtain ⟨t, -⟩ := t
      -- Beta-reduce the capped target at the cell `t`.
      dsimp only
      induction t using Fin.addCases with
      | left e =>
        rw [Lvl.Φcat_castAdd, Lvl.Φcat_castAdd]
        exact hL.capAgree (camal R) (camal (C.equivFin.symm j).1) (fun d ↦ hRB _) κ hκv
          (isShort_of_mem_grid hκm)
          (fun d ↦ (agreementHeight_spec (bot_mem_grid _ _) R (C.equivFin.symm j).1).2
            (Sum.inl d)) e
      | right j' =>
        rw [Lvl.Φcat_natAdd, Lvl.Φcat_natAdd]
        exact agreementHeight_tri (bot_mem_grid _ _) _ _ _
  · induction t using Fin.addCases with
    | left e =>
      rcases hcases ht with h | h | h
      exacts [haC s _ h hst hg, ha2 s _ h hst hg, haD s _ h hst hg]
    | right j =>
      refine ⟨Fin.natAdd _ i₀, by
        rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd,
          Scheme.appendFullCellsScheme_gradedIndex_natAdd], ?_⟩
      rw [Lvl.Φcat_natAdd, hi₀, agreementHeight_self (gridPoint_mem_grid le_rfl)
        (fun _ hx ↦ le_gridPoint_of_mem_grid hx)]
      exact le_gridPoint_of_mem_codeGrid (hL.Φcat_mem_codeGrid hRB s)

/-- **The catalogue layer over a good level is consistent**, when every profile of `C` has values in
the code grid and amalgam part lawful on the grade-`(g + 1)` cut. -/
theorem Lvl.Good.catS_consistent (hL : L.Good)
    (hCsub : ∀ P ∈ C, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧ IsCutLawful I (g + 1) (camal P)) :
    (L.catS C).rows.IsConsistent := by
  intro s
  induction s using Fin.addCases with
  | right i =>
    have hu := Scheme.appendFullCellsScheme_gradedIndex_natAdd L.S (g + 1) C.card i
    have hm := (C.equivFin.symm i).2
    have h := hL.isLawfulBelow_Φcat hm (hCsub _ hm).1 (hCsub _ hm).2
    change (L.catS C).rows.IsLawfulBelow ((L.catS C).toCellScheme.gradedIndex (Fin.natAdd _ i))
      ((L.catS C).rows.row (Fin.natAdd _ i))
    rw [Scheme.appendFullCells_row_natAdd_eq]
    rw [show (L.catS C).toCellScheme.gradedIndex (Fin.natAdd _ i) =
      ((univ : Finset (Fin (m + 2))), g + 1) from hu]
    exact h
  | left s =>
    have hφ := Scheme.isLowerEmbedding_castAdd (S := L.S) (g + 1) C.card
      (fun i ↦ L.Φcat C (C.equivFin.symm i).1) L.not_le
    refine (CellScheme.Rows.isLawfulBelow_comap_iff hφ (hφ.image_below_gradedIndex s)).mp ?_
    rw [Scheme.comap_rows_castAdd]
    convert hL.consistent s using 1
    funext t
    exact congrArg (fun R : L.S.toCellScheme.Rows ↦ R.row s t) Scheme.comap_rows_castAdd

/-- **Lifts below a pair not above `(univ, g + 1)`** are those of the level. -/
theorem Lvl.cappedLift_catS_iff {X Y : Finset (Fin (m + 2)) × ℕ} (hXY : X ≤ Y)
    (hY : ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ Y) :
    (L.catS C).rows.CappedLift hXY ↔ L.S.rows.CappedLift hXY := by
  have h : L.S.toCellScheme.IsSourcePrefix (L.catS C).toCellScheme (Fin.castAdd _) Y :=
    ⟨Scheme.isLowerEmbedding_castAdd (S := L.S) (g + 1) C.card
      (fun i ↦ L.Φcat C (C.equivFin.symm i).1) L.not_le,
      Scheme.appendFullCellsScheme_scope_castAdd L.S (g + 1) _,
      fun d hd ↦ ⟨⟨d, Scheme.lt_card_of_mem_below hY hd⟩, rfl⟩⟩
  rw [← h.cappedLift_iff hXY le_rfl, Scheme.comap_rows_castAdd]

/-- A cell of the catalogue layer of scope other than the ground set below `(univ, g + 1)` is an old
amalgam cell of grade at most `g + 1`. -/
theorem Lvl.Good.exists_old_catS (hL : L.Good) {z : Fin (L.catS C).card}
    (hz : z ∈ (L.catS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1))
    (hne : (L.catS C).toCellScheme.scope z ≠ univ) :
    ∃ d, I.amalgam.toCellScheme.grade d ≤ g + 1 ∧ z = Fin.castAdd _ (L.embed d) := by
  induction z using Fin.addCases with
  | right j => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ j) hne
  | left e =>
    rw [Scheme.appendFullCellsScheme_scope_castAdd] at hne
    obtain ⟨d, rfl⟩ := hL.mem_range e hne
    refine ⟨d, ?_, rfl⟩
    have := hz.2
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, hL.gradedIndex_embed] at this
    exact this

/-! ### Extension through the controllers -/

/-- **Extension through the catalogue layer at a positive cap.**  Let `P ∈ C` have values in the
code grid and an orbit-canonical amalgam part, `h` be self-visible and short at `g + 1`, `W` an
amalgam profile lawful on the grade-`(g + 1)` cut agreeing with the amalgam part of `P` capped at
`h`, and `β` a cutoff agreeing with that of `P` capped at `h`, such that the orbit code of `W` with
the cutoff `β` lies in `C`.  Then some labelling lawful below `(univ, g + 1)` in the catalogue layer
reads `W` at the amalgam cells of grade at most `g + 1` and agrees with the row of `P` capped at `h`
everywhere. -/
theorem Lvl.Good.exists_extension_cat (hL : L.Good)
    (hCsub : ∀ P ∈ C, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧ IsCutLawful I (g + 1) (camal P))
    {P : CProf I} (hP : P ∈ C) (hPo : orbitCode (g + 1) (camal P) = camal P) {h : Label.{u}}
    (hh : IsSelfVisible (g + 1) h) (hs : IsShort (g + 1) h) (hb : h ≠ ⊥) {W : Prof I}
    (hWP : ∀ d, min (W d) h = min (P (Sum.inl d)) h) {β : Label.{u}}
    (hβ : min β h = min (P (Sum.inr ())) h) (hQC : withCut (orbitCode (g + 1) W) β ∈ C) :
    ∃ q : (L.catS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) → Label.{u},
      (L.catS C).rows.IsLawfulBelow (univ, g + 1) q ∧
      (∀ d (hd : I.amalgam.toCellScheme.grade d ≤ g + 1),
        q ⟨Fin.castAdd _ (L.embed d), by
          rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd,
            hL.gradedIndex_embed]; exact ⟨subset_univ _, hd⟩⟩ = W d) ∧
      ∀ z, min (q z) h = min (L.Φcat C P z) h := by
  set Q : CProf I := withCut (orbitCode (g + 1) W) β with hQ
  have hQa : camal Q = orbitCode (g + 1) W := rfl
  have hQP (f : Fin I.amalgam.card ⊕ Unit) : min (Q f) h = min (P f) h := by
    rcases f with d | z
    · exact min_orbitCode_eq hh hs hPo hWP d
    · exact hβ
  have hQW (d : Fin I.amalgam.card) : min (orbitCode (g + 1) W d) h = min (W d) h :=
    (hQP (Sum.inl d)).trans (hWP d).symm
  obtain ⟨hQB, hQc⟩ := hCsub Q hQC
  obtain ⟨hPB, -⟩ := hCsub P hP
  have hag (z : (L.catS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
      min (orbitDecoder (g + 1) W h (L.Φcat C Q z)) h = min (L.Φcat C P z) h := by
    obtain ⟨z, -⟩ := z
    induction z using Fin.addCases with
    | left e =>
      rw [min_orbitDecoder_eq_of_isReadableAt hh hQW (by
          rw [Lvl.Φcat_castAdd, hQa]
          exact hL.readable _ orbitCode_orbitCode (fun d ↦ hQB (Sum.inl d)) e),
        Lvl.Φcat_castAdd, Lvl.Φcat_castAdd]
      exact hL.capAgree (camal Q) (camal P) (fun d ↦ hQB _) h hh hs (fun d ↦ hQP _) e
    | right j =>
      rw [Lvl.Φcat_natAdd, Lvl.Φcat_natAdd,
        min_orbitDecoder_eq (isSelfVisible_of_mem_grid (agreementHeight_spec
          (bot_mem_grid _ _) _ _).1)]
      exact min_agreementHeight_eq_of_isShort hh hs (fun f ↦ ⟨hQB f, hPB f⟩) hQP _
  refine ⟨fun z ↦ orbitDecoder (g + 1) W h (L.Φcat C Q z),
    (hL.isLawfulBelow_Φcat hQC hQB hQc).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_orbitDecoder hh hb) (fun _ ↦ eq_bot_of_orbitDecoder_eq_bot hb), fun d hd ↦ ?_,
    hag⟩
  change orbitDecoder (g + 1) W h (L.Φcat C Q (Fin.castAdd _ (L.embed d))) = W d
  rw [Lvl.Φcat_castAdd, hL.literal, hQa, orbitDecoder_orbitCode hQW d]

/-- **Extension through the catalogue layer at the cap `⊥`**: an amalgam profile lawful on the
grade-`(g + 1)` cut whose orbit code with the cutoff `⊥` lies in `C` extends to a labelling lawful
below `(univ, g + 1)` reading it at the amalgam cells of grade at most `g + 1`. -/
theorem Lvl.Good.exists_extension_cat_bot (hL : L.Good)
    (hCsub : ∀ P ∈ C, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧ IsCutLawful I (g + 1) (camal P))
    {W : Prof I} (hQC : withCut (orbitCode (g + 1) W) ⊥ ∈ C) :
    ∃ q : (L.catS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) → Label.{u},
      (L.catS C).rows.IsLawfulBelow (univ, g + 1) q ∧
      ∀ d (hd : I.amalgam.toCellScheme.grade d ≤ g + 1),
        q ⟨Fin.castAdd _ (L.embed d), by
          rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd,
            hL.gradedIndex_embed]; exact ⟨subset_univ _, hd⟩⟩ = W d := by
  set Q : CProf I := withCut (orbitCode (g + 1) W) ⊥ with hQ
  have hQa : camal Q = orbitCode (g + 1) W := rfl
  obtain ⟨hQB, hQc⟩ := hCsub Q hQC
  have hQW (d : Fin I.amalgam.card) :
      min (orbitCode (g + 1) W d) (gridPoint (g + 1) 0) = min (W d) (gridPoint (g + 1) 0) :=
    min_orbitCode_gridPoint_zero d
  refine ⟨fun z ↦ orbitDecoder (g + 1) W (gridPoint (g + 1) 0) (L.Φcat C Q z),
    (hL.isLawfulBelow_Φcat hQC hQB hQc).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_orbitDecoder (isSelfVisible_gridPoint _ 0) (gridPoint_ne_bot _ 0))
      (fun _ ↦ eq_bot_of_orbitDecoder_eq_bot (gridPoint_ne_bot _ 0)), fun d hd ↦ ?_⟩
  change orbitDecoder (g + 1) W (gridPoint (g + 1) 0) (L.Φcat C Q (Fin.castAdd _ (L.embed d))) =
    W d
  rw [Lvl.Φcat_castAdd, hL.literal, hQa, orbitDecoder_orbitCode hQW d]

/-! ### The capped lift from a coatom -/

/-- A cell of the catalogue layer of graded index `(univ, g + 1)` is a controller. -/
theorem Lvl.exists_natAdd_eq_catS (L : Lvl I g) {u : Fin (L.catS C).card}
    (hu : (L.catS C).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), g + 1)) :
    ∃ i, Fin.natAdd _ i = u := by
  by_cases hlt : (u : ℕ) < L.S.card
  · refine absurd ?_ (L.not_le ⟨u, hlt⟩)
    rw [← Scheme.appendFullCellsScheme_gradedIndex_of_lt hlt]
    exact hu.ge
  · have hu' : (u : ℕ) < L.S.card + C.card := u.2
    exact ⟨⟨u - L.S.card, by omega⟩, Fin.ext (by simp; omega)⟩

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
theorem Lvl.Good.cappedLift_catS (hL : L.Good) (hgm : g + 1 ≤ m) {x : Fin (m + 2)}
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

/-- **The catalogue step at the cap `⊥`**: for `g + 1 ≤ m`, every labelling of the catalogue layer
lawful below a coatom at the grade `g + 1` is, at the amalgam cells below the coatom, an amalgam
profile lawful on the grade-`(g + 1)` cut: lift its trace on the common face into the other coatom
at the cap `⊥` (bountifulness of the amalgam) and glue. -/
theorem Lvl.Good.exists_cutLawful_of_coatom (hL : L.Good) (hgm : g + 1 ≤ m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) {w : Fin (L.catS C).card → Label.{u}}
    (hw : (L.catS C).rows.IsLawfulBelow (univ.erase x, g + 1) (fun z ↦ w z)) :
    ∃ W : Prof I, IsCutLawful I (g + 1) W ∧
      ∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
        I.amalgam.toCellScheme.scope d ⊆ univ.erase x → W d = w (Fin.castAdd _ (L.embed d)) := by
  have ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1)
      fun d ↦ w (Fin.castAdd _ (L.embed d)) :=
    (hL.isLawfulBelow_old_iff (X := (univ.erase x, g + 1)) (Seed.ne_univ_erase x)
      (w := fun e ↦ w (Fin.castAdd _ e))).mp ((L.isLawfulBelow_catS_iff (C := C)
        (fun h ↦ Seed.ne_univ_erase x (univ_subset_iff.mp h.1))).mp hw)
  obtain ⟨W, hW, hWa, -⟩ := exists_isCutLawful_of_coatom (k := g + 1) (Nat.succ_pos g) hgm hx
    (isSelfVisible_bot (g + 1)) (P := fun _ ↦ ⊥) (f := fun d ↦ w (Fin.castAdd _ (L.embed d)))
    ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ ha fun _ _ ↦ by simp
  exact ⟨W, hW, fun d hd hds ↦ hWa d ⟨hds, hd⟩⟩

/-- A profile lawful on the cut is lawful below each of the two coatoms. -/
theorem IsCutLawful.isLawfulBelow_erase {k : ℕ} {P : Prof I} (hP : IsCutLawful I k P)
    {y : Fin (m + 2)} (hy : y ∈ (Pts : Finset (Fin (m + 2)))) :
    I.amalgam.rows.IsLawfulBelow (univ.erase y, k) fun d ↦ P d :=
  hP.erase hy

/-- **The step on the amalgam at a positive cap, with the cap ball of a profile**: for a profile
`P` lawful on the grade-`(g + 1)` cut and a cap `h` self-visible at `g + 1`, every labelling lawful
below a coatom that agrees there with `P` capped at `h` is, at the amalgam cells below the coatom,
an amalgam profile lawful on the cut agreeing everywhere with `P` capped at `h`: the trace on the
common face is lifted into the other coatom in the cap ball of `P` (bountifulness of the amalgam),
and the cells above the cut keep `P`. -/
theorem Lvl.Good.exists_cutLawful_of_coatom_cap (hL : L.Good) (hgm : g + 1 ≤ m)
    {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) {P : Prof I}
    (hP : IsCutLawful I (g + 1) P) {h : Label.{u}} (hh : IsSelfVisible (g + 1) h)
    {w : Fin (L.catS C).card → Label.{u}}
    (hw : (L.catS C).rows.IsLawfulBelow (univ.erase x, g + 1) (fun z ↦ w z))
    (hwP : ∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
      I.amalgam.toCellScheme.scope d ⊆ univ.erase x →
        min (w (Fin.castAdd _ (L.embed d))) h = min (P d) h) :
    ∃ W : Prof I, IsCutLawful I (g + 1) W ∧
      (∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
        I.amalgam.toCellScheme.scope d ⊆ univ.erase x → W d = w (Fin.castAdd _ (L.embed d))) ∧
      ∀ d, min (W d) h = min (P d) h := by
  have ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1)
      fun d ↦ w (Fin.castAdd _ (L.embed d)) :=
    (hL.isLawfulBelow_old_iff (X := (univ.erase x, g + 1)) (Seed.ne_univ_erase x)
      (w := fun e ↦ w (Fin.castAdd _ e))).mp ((L.isLawfulBelow_catS_iff (C := C)
        (fun h ↦ Seed.ne_univ_erase x (univ_subset_iff.mp h.1))).mp hw)
  obtain ⟨W, hW, hWa, hWP⟩ := exists_isCutLawful_of_coatom (k := g + 1) (Nat.succ_pos g) hgm hx
    hh hP (f := fun d ↦ w (Fin.castAdd _ (L.embed d))) ha fun d hd ↦ hwP d hd.2 hd.1
  exact ⟨W, hW, fun d hd hds ↦ hWa d ⟨hds, hd⟩, hWP⟩

variable (L A) in
/-- **The catalogue step on the amalgam** from the coatom `univ.erase x`, at the grade `g + 1`: at
every profile `P` of the catalogue of `A` and every cap `h` self-visible and short at `g + 1` with
`⊥ < h`, every labelling lawful below the coatom agreeing there with `P` capped at `h` is, at the
amalgam cells below the coatom, an amalgam profile `W` lawful on the grade-`(g + 1)` cut agreeing
with the amalgam part of `P` capped at `h`, with a coded cutoff `β` agreeing with that of `P` capped
at `h` such that the orbit code of `W` with the cutoff `β` satisfies `A`.  Open. -/
def Lvl.CatStep (x : Fin (m + 2)) : Prop :=
  ∀ P ∈ 𝒞, ∀ h : Label.{u}, IsSelfVisible (g + 1) h → IsShort (g + 1) h → ⊥ < h →
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
      A (withCut (orbitCode (g + 1) W) β)

/-- **The capped lift from a coatom into the catalogue layer over a good level from the catalogue
step**: the cap `⊥` is `ProfileTower.Lvl.Good.exists_cutLawful_of_coatom`, so the only hypothesis
left is the catalogue step at the positive caps (`ProfileTower.Lvl.CatStep`). -/
theorem Lvl.Good.cappedLift_catS_of_catStep (hL : L.Good) (hgm : g + 1 ≤ m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) (hAbot : ∀ W : Prof I, A (withCut W ⊥))
    (hstep : L.CatStep A x) :
    (L.catS 𝒞).rows.CappedLift (X := (univ.erase x, g + 1))
      (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  have hA0 : A fun _ ↦ ⊥ := by
    convert hAbot (fun _ ↦ ⊥) using 1
    funext f
    rcases f with d | z <;> rfl
  hL.cappedLift_catS hgm hx hA0 (fun _ hw ↦ by
    obtain ⟨W, hW, hWw⟩ := hL.exists_cutLawful_of_coatom hgm hx hw
    exact ⟨W, hW, hWw, hAbot _⟩) hstep

variable (L A) in
/-- **The catalogue step at the cap `⊥`** from the coatom `univ.erase x`: every labelling lawful
below the coatom is, at the amalgam cells below the coatom, an amalgam profile lawful on the
grade-`(g + 1)` cut whose orbit code with the cutoff `⊥` satisfies `A`. -/
def Lvl.CatStepBot (x : Fin (m + 2)) : Prop :=
  ∀ w : Fin (L.catS 𝒞).card → Label.{u},
    (L.catS 𝒞).rows.IsLawfulBelow (univ.erase x, g + 1) (fun z ↦ w z) →
    ∃ W : Prof I, IsCutLawful I (g + 1) W ∧
      (∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
        I.amalgam.toCellScheme.scope d ⊆ univ.erase x → W d = w (Fin.castAdd _ (L.embed d))) ∧
      A (withCut (orbitCode (g + 1) W) ⊥)

/-- **The capped lift from a coatom from the two catalogue steps**, for a predicate satisfied by
the bottom profile: the step at the cap `⊥` (`ProfileTower.Lvl.CatStepBot`) and at the positive
caps (`ProfileTower.Lvl.CatStep`). -/
theorem Lvl.Good.cappedLift_catS_of_steps (hL : L.Good) (hgm : g + 1 ≤ m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) (hA0 : A fun _ ↦ ⊥) (hbot : L.CatStepBot A x)
    (hstep : L.CatStep A x) :
    (L.catS 𝒞).rows.CappedLift (X := (univ.erase x, g + 1))
      (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  hL.cappedLift_catS hgm hx hA0 hbot hstep

end VaughtConjecture.ProfileTower
