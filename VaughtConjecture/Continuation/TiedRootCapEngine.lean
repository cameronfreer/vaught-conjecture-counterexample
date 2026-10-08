/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapAdmission

/-!
# The coatom provision of the admitted completion at the context with separated tied root cells

Roadmap, Layer 3 ((R3) of the table of 3.4).

The engine of the restricted catalogue builds completions whose rows at the reading grades are
reading rows: correct states for the cap requests, or states whose private cap is `⊥`.  Such a
completion is a selective carrier when the cells of the second kind stay below the cutoff.  Its
bountifulness needs the **coatom provision**, which is necessary for every admitted completion
(on the engine's branch).  This file tests the coatom provision at the context of
`TiedRootCapCounterexample`.

The definitions `TiedRootCapEngine.Prof` (the engine's `Seed.State`), `coatC`, `coatD`,
`IsCutLawful`, `hat`, `Pts`, `hat_of_le`, `ProvisionAt`, `CoatomProvision` and
`provisionAt_iff_of_eq_top` are copied verbatim from the engine's branch (`Extension/ProfileTower`
and `Extension/Admission` there), in their own namespace, so that this file does not depend on
that branch.

* **The seed** (`TiedRootCapCounterexample.seedFour`): the context and a legal three-point type
  over its face on `{0, 1}` carrying the donor (`TiedRootCapCounterexample.threePoint`, a coatom
  extension on three points); the faces of its amalgam are the context and, along
  `extendByLast rootEmb`, the donor (`restrictFace_amalgam_context`, `restrictFace_amalgam_donor`).
* **The requests** (`TiedRootCapCounterexample.capRequestsA`): the cap of the context as cap and
  marker, threshold `3`, the apex of the donor read from below; a correct state `⊤` at the cap is
  `⊤` at the apex (`apexA_eq_top_of_isCorrect`).
* **The coatom provision fails** (`TiedRootCapCounterexample.not_coatomProvision`, compiled in this
  repository (theorem named)): `¬ CoatomProvision seedFour 3 capRequestsA.IsCorrect`.  At the
  private coatom (the context) and the grade `3`, the lawful extension of the separating labelling
  is `⊤` at the cap, a cell of the grade `3`; so the cap of the provision is `⊤`
  (`TiedRootCapEngine.provisionAt_iff_of_eq_top`) and the provision asks the splice itself to be
  correct, `⊤` at the apex of the donor, which no state lawful below the donor's coatom and equal
  to the separating labelling on the root allows.

**What this says about the engine's design.**  The cells with private cap `⊥` cannot serve the
separating labelling: the provision caps the state at a label at least its value at the cap, which
is `⊤`.  With the admitted states the correct states (the admission of correct states of the engine,
whose fill from the private coatom is the same raise), no admitted completion over this seed
exists, by the necessity of the coatom provision (`CompletionBelowFullGrade.coatomProvision` on
the engine's branch, for requests graded by the amalgam; not compiled here); the engine's design
does not produce a selective carrier at this context.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Profiles, cuts, splices and the coatom provision -/

namespace TiedRootCapEngine

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- A **profile**: a labelling of the cells of the amalgam. -/
abbrev Prof : Type (u + 1) := Fin I.amalgam.card → Label.{u}

/-- The first coatom `C = univ.erase (m + 1)`. -/
abbrev coatC : Finset (Fin (m + 2)) := univ.erase (Fin.last (m + 1))

/-- The second coatom `D = univ.erase m`. -/
abbrev coatD : Finset (Fin (m + 2)) := univ.erase (Fin.castSucc (Fin.last m))

/-- A profile **lawful on the grade-`k` cut**: lawful below both coatoms at the grade `k`. -/
def IsCutLawful (k : ℕ) (P : Prof I) : Prop :=
  I.amalgam.rows.IsLawfulBelow (coatC, k) (fun d ↦ P d) ∧
    I.amalgam.rows.IsLawfulBelow (coatD, k) (fun d ↦ P d)

/-- The splice of a profile at the grade `k`: the profile up to the grade `k`, `⊥` above. -/
noncomputable def hat (k : ℕ) (P : Prof I) : Prof I :=
  I.amalgam.toCellScheme.splice k (fun _ ↦ ⊥) P

/-- The two points omitted by the coatoms. -/
abbrev Pts : Finset (Fin (m + 2)) := {Fin.last (m + 1), Fin.castSucc (Fin.last m)}

/-- **The provision at a grade and a boundary state**: some cap `H` self-visible at `k`, at least
every value of `W` at a cell of grade `k`, has the splice of `W` at `k` capped at `H` admitted. -/
def ProvisionAt (Adm : Prof I → Prop) (k : ℕ) (W : Prof I) : Prop :=
  ∃ H : Label.{u}, IsSelfVisible k H ∧
    (∀ d, I.amalgam.toCellScheme.grade d = k → W d ≤ H) ∧
      Adm fun d ↦ min (hat I k W d) H

/-- **The coatom provision from the grade `N`**: at every grade `k ≥ N` with `0 < k ≤ m + 1` and
either coatom `C`, every state lawful below `(C, k)` agrees below `(C, k)` with a state lawful on
the grade-`k` cut that has the provision at `k`. -/
def CoatomProvision (N : ℕ) (Adm : Prof I → Prop) : Prop :=
  ∀ ⦃k : ℕ⦄, N ≤ k → 0 < k → k ≤ m + 1 → ∀ ⦃x : Fin (m + 2)⦄,
    x ∈ (Pts : Finset (Fin (m + 2))) → ∀ ⦃W : Prof I⦄,
      I.amalgam.rows.IsLawfulBelow (univ.erase x, k) (fun d ↦ W d) →
      ∃ W' : Prof I, IsCutLawful I k W' ∧
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, k), W' d = W d) ∧
          ProvisionAt I Adm k W'

variable {I}

theorem hat_of_le {k : ℕ} {P : Prof I} {d : Fin I.amalgam.card}
    (hd : I.amalgam.toCellScheme.grade d ≤ k) : hat I k P d = P d :=
  CellScheme.splice_of_le hd

/-- **At a state with a top at the grade `k`, the provision is admission of the splice**: the cap
must be `⊤`. -/
theorem provisionAt_iff_of_eq_top {Adm : Prof I → Prop} {k : ℕ} {W : Prof I}
    {d₀ : Fin I.amalgam.card} (hd₀ : I.amalgam.toCellScheme.grade d₀ = k) (htop : W d₀ = ⊤) :
    ProvisionAt I Adm k W ↔ Adm (hat I k W) := by
  refine ⟨fun ⟨H, _, hle, hA⟩ ↦ ?_, fun h ↦ ⟨⊤, isSelfVisible_top _, fun _ _ ↦ le_top,
    by simpa only [min_top_right] using h⟩⟩
  obtain rfl : H = ⊤ := top_le_iff.mp (htop ▸ hle d₀ hd₀)
  simpa only [min_top_right] using hA

end TiedRootCapEngine

/-! ### Cells of the faces of a completion -/

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)
  (hα : Order.IsSuccPrelimit α)

/-- The cells of a proper face of the truncation are the old cells of the amalgam's face. -/
theorem faceCell_truncate {n : ℕ} {f : Fin n ↪ Fin (m + 2)} (hf : univ.map f ≠ univ)
    {s : StageType.{u} α n} (hs : StageType.restrictFace f (F.truncate hα) = some s)
    (hs' : StageType.restrictFace f I.amalgam = some s) (i : Fin s.card) :
    StageType.faceCell hs i = F.embed (StageType.faceCell hs' i) :=
  Scheme.cellMap_eq_of_strictMono_of_mem_range (S := I.amalgam.toScheme) (T := F.scheme) f
    (φ := F.embed) F.embed.strictMono F.scope_embed (fun z hz ↦ F.mem_range_embed z fun he ↦
      hf (eq_univ_of_forall fun x ↦ by
        obtain ⟨y, rfl⟩ : x ∈ Set.range f := hz (mem_coe.mpr (he.symm ▸ mem_univ x))
        exact mem_map_of_mem _ (mem_univ y))) rfl

end CompletionBelowFullGrade

/-! ### The seed of the context and a three-point carrier of the donor -/

namespace TiedRootCapCounterexample

open StageType TiedRootCapEngine

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- The face of the context on the points `{0, 1}` is defined. -/
theorem univ_map_castSuccEmb_mem_faces_context :
    univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ∈ (context hα).toCellScheme.faces :=
  ((restrictFace_eq_some_iff _ _).mp
    ((lower hα).restrictFace_left_truncate hα.isSuccPrelimit)).1

/-- The face of the context on the points `{0, 1}`. -/
noncomputable def faceZeroOne : StageType.{u} α 2 :=
  (context hα).comap Fin.castSuccEmb (univ_map_castSuccEmb_mem_faces_context hα)

theorem restrictFace_faceZeroOne :
    restrictFace Fin.castSuccEmb (context hα) = some (faceZeroOne hα) :=
  restrictFace_of_mem _ _ _

theorem isLegal_faceZeroOne : (faceZeroOne hα).IsLegal :=
  (isLegal_context hα).restrictFace _ (restrictFace_faceZeroOne hα)

theorem restrictFace_faceZeroOne_root :
    restrictFace Fin.castSuccEmb (faceZeroOne hα) = some (root hα) := by
  rw [restrictFace_trans _ _ _ (restrictFace_faceZeroOne hα)]
  exact restrictFace_context hα

theorem exists_threePoint : ∃ tb : StageType.{u} α 3, tb.IsLegal ∧
    restrictFace Fin.castSuccEmb tb = some (faceZeroOne hα) ∧
    restrictFace (extendByLast Fin.castSuccEmb) tb = some (donor hα) :=
  exists_coatomExtension_of_le_two hα.isSuccPrelimit (m := 1) (by omega) _ _ _
    (isLegal_faceZeroOne hα) (isLegal_donor hα) (restrictFace_faceZeroOne_root hα)
    (restrictFace_donor hα)

/-- A legal three-point type with faces the face of the context on `{0, 1}` and the donor. -/
noncomputable def threePoint : StageType.{u} α 3 := (exists_threePoint hα).choose

/-- **The seed of the context and the three-point type** over the face on `{0, 1}`: the seed of
the admitted completion carrying the donor over the context. -/
noncomputable def seedFour : Seed.{u} α 2 :=
  Seed.ofCoatoms (isLegal_context hα) (exists_threePoint hα).choose_spec.1
    (restrictFace_faceZeroOne hα) (exists_threePoint hα).choose_spec.2.1

/-- The face of the amalgam on the context. -/
theorem restrictFace_amalgam_context :
    restrictFace Fin.castSuccEmb (seedFour hα).amalgam = some (context hα) :=
  (seedFour hα).restrictFace_left

/-- The face of the amalgam on the donor, along `extendByLast rootEmb`. -/
theorem restrictFace_amalgam_donor :
    restrictFace (extendByLast rootEmb) (seedFour hα).amalgam = some (donor hα) := by
  have h : extendByLast rootEmb =
      (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)).trans
        (extendByLast (Fin.castSuccEmb : Fin 2 ↪ Fin 3)) := by
    rw [extendByLast_trans]
    rfl
  rw [h, ← restrictFace_trans _ _ _ (seedFour hα).restrictFace_right]
  exact (exists_threePoint hα).choose_spec.2.2

/-- The cap of the context in the amalgam. -/
noncomputable abbrev capA : Fin (seedFour hα).amalgam.card :=
  faceCell (restrictFace_amalgam_context hα) (capCell hα)

/-- The apex of the donor in the amalgam. -/
noncomputable abbrev apexA : Fin (seedFour hα).amalgam.card :=
  faceCell (restrictFace_amalgam_donor hα) (donorApex hα)

/-- **The cap requests of (R3) on the amalgam**: the cap of the context as cap and marker,
threshold `3`, and the apex of the donor read from below. -/
noncomputable def capRequestsA : CapRequests (Fin (seedFour hα).amalgam.card) where
  cap := capA hα
  N := 3
  R := 0
  R_lt_N := by omega
  Z := ∅
  F := ∅
  T := {apexA hα}
  ref := id
  off := fun _ ↦ 0
  marker := capA hα

/-- A correct state `⊤` at the cap is `⊤` at the apex of the donor. -/
theorem apexA_eq_top_of_isCorrect {s : Prof (seedFour hα)} (hcap : s (capA hα) = ⊤)
    (hs : (capRequestsA hα).IsCorrect s) : s (apexA hα) = ⊤ := by
  have h := hs.markerValue_le _ rfl
  simp only [CapRequests.markerValue, capRequestsA, hcap, visibilityReplace_top, min_self,
    min_top_right] at h
  exact top_le_iff.mp h

/-- **The coatom provision of the admission of correct states fails at the context.**  For every
admission whose admitted states are the correct states for the cap requests of (R3) (the
admission of correct states of the engine, `CapBot` the states with cap `⊥`), the coatom
provision from the grade `3` fails at the private coatom: the lawful extension of the separating
labelling, below the context, is `⊤` at the cap, a cell of the grade `3`, so the provision asks
its splice itself to be correct (`TiedRootCapEngine.provisionAt_iff_of_eq_top`: the cap `H` is
`⊤`), so `⊤` at the apex of the donor, which the separating labelling forbids on every state
lawful below the donor's coatom. -/
theorem not_coatomProvision :
    ¬ CoatomProvision (seedFour hα) 3 (capRequestsA hα).IsCorrect := by
  intro hprov
  have hα' := hα.isSuccPrelimit
  -- the separating labelling, extended through a completion of the seed
  obtain ⟨F⟩ := (seedFour hα).nonempty_completionBelowFullGrade_of_le_two le_rfl
  have hD := F.restrictFace_left_completion hα'
  obtain ⟨a, ha, hext, -⟩ := exists_extension_separating hα hD (F.isLegal_completion hα')
  set W : Prof (seedFour hα) := fun d ↦ a (F.embed d).castSucc
  have hCne : (univ.erase (Fin.last 3) : Finset (Fin 4)) ≠ univ := Seed.ne_univ_erase _
  have hW : (seedFour hα).amalgam.rows.IsLawfulBelow (univ.erase (Fin.last 3), 3)
      (fun d ↦ W d) := by
    have h := (F.isLawfulBelow_embed_iff (X := (univ.erase (Fin.last 3), 3)) hCne
      (w := fun z ↦ a z.castSucc)).mp
      ((F.isLawful_comp_castSucc hα' ha).isLawfulBelow _)
    exact h
  -- the cells of the context in the amalgam carry the separating labelling
  have hT := F.restrictFace_left_truncate hα'
  have hWz (z : Fin (context hα).card) :
      W (faceCell (restrictFace_amalgam_context hα) z) = separating hα z := by
    have h1 := F.faceCell_truncate hα' Coatom.univ_map_left_ne hT
      (restrictFace_amalgam_context hα) z
    have h2 := F.faceCell_completion hα' Coatom.univ_map_left_ne hT hD z
    have h3 : faceCell hD z = (F.embed (faceCell (restrictFace_amalgam_context hα) z)).castSucc :=
      h2.trans (congrArg Fin.castSucc h1)
    exact (congrArg a h3).symm.trans (hext z)
  obtain ⟨W', ⟨-, hW'D⟩, hW'W, hprovW⟩ :=
    hprov le_rfl (by omega) le_rfl (by simp) hW
  -- the context's cells lie below the private coatom
  have hbelowC (z : Fin (context hα).card) :
      faceCell (restrictFace_amalgam_context hα) z ∈
        (seedFour hα).amalgam.toCellScheme.below (univ.erase (Fin.last 3), 3) := by
    rw [CellScheme.mem_below]
    refine Prod.mk_le_mk.mpr ⟨?_, ?_⟩
    · change (seedFour hα).amalgam.toCellScheme.scope _ ⊆ _
      rw [scope_faceCell, ← Coatom.univ_map_left]
      exact map_subset_map.mpr (subset_univ _)
    · change (seedFour hα).amalgam.toCellScheme.grade _ ≤ 3
      rw [grade_faceCell]
      exact (context hα).grade_le z
  have hW'z (z : Fin (context hα).card) :
      W' (faceCell (restrictFace_amalgam_context hα) z) = separating hα z :=
    (hW'W _ (hbelowC z)).trans (hWz z)
  -- the provision at a top of the grade `3` is correctness of the splice
  have hcapg : (seedFour hα).amalgam.toCellScheme.grade (capA hα) = 3 :=
    (grade_faceCell _ _).trans (context_grade_cap hα)
  have hcapW' : W' (capA hα) = ⊤ := (hW'z _).trans (separating_capCell hα)
  have hcorr := (provisionAt_iff_of_eq_top hcapg hcapW').mp hprovW
  have happex : W' (apexA hα) = ⊤ := by
    have h := apexA_eq_top_of_isCorrect hα (by rw [hat_of_le hcapg.le]; exact hcapW') hcorr
    rwa [hat_of_le ((grade_faceCell _ _).trans_le (((donor hα).grade_le _).trans
      (by omega)))] at h
  -- locality at the apex of the donor, below the donor's coatom
  obtain ⟨-, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hW'D
  have hAb : apexA hα ∈ (seedFour hα).amalgam.toCellScheme.below
      ((univ : Finset (Fin 4)).erase (Fin.castSucc (Fin.last 2)), 3) := by
    rw [CellScheme.mem_below]
    refine Prod.mk_le_mk.mpr ⟨?_, ?_⟩
    · rw [scope_faceCell]
      intro x hx
      obtain ⟨y, -, rfl⟩ := mem_map.mp hx
      refine mem_erase.mpr ⟨?_, mem_univ _⟩
      induction y using Fin.lastCases with
      | last =>
        rw [extendByLast_last]
        exact fun h ↦ absurd (congrArg Fin.val h) (by simp)
      | cast y =>
        obtain rfl : y = 0 := Subsingleton.elim _ _
        rw [extendByLast_castSucc]
        exact fun h ↦ absurd (congrArg Fin.val h) (by simp [rootEmb])
    · rw [grade_faceCell]
      exact ((donor hα).grade_le _).trans (by omega)
  have hy (i : Fin 2) : faceCell (restrictFace_amalgam_donor hα)
      (faceCell (restrictFace_donor hα) i) ∈ (seedFour hα).amalgam.toCellScheme.below
        ((seedFour hα).amalgam.toCellScheme.gradedIndex (apexA hα)) := by
    have hz := mem_below_donor_last hα (faceCell (restrictFace_donor hα) i)
    rw [CellScheme.mem_below] at hz ⊢
    obtain ⟨hs, hgr⟩ := Prod.mk_le_mk.mp hz
    refine Prod.mk_le_mk.mpr ⟨?_, ?_⟩
    · change (seedFour hα).amalgam.toCellScheme.scope _ ⊆ (seedFour hα).amalgam.toCellScheme.scope _
      rw [scope_faceCell, scope_faceCell]
      exact map_subset_map.mpr hs
    · change (seedFour hα).amalgam.toCellScheme.grade _ ≤ (seedFour hα).amalgam.toCellScheme.grade _
      rw [grade_faceCell, grade_faceCell]
      exact hgr
  have hrow (i : Fin 2) : (seedFour hα).amalgam.rows.row (apexA hα) ⟨_, hy i⟩ =
      blockEncode (apexCodes (t := (donorLower hα).truncate hα.isSuccPrelimit)
        (donorLower hα).isLegalBelowFullGrade) 2 three := by
    rw [← Scheme.rowAt_of_mem (hy i), rowAt_faceCell (restrictFace_amalgam_donor hα),
      Scheme.rowAt_of_mem (mem_below_donor_last hα _)]
    exact donor_row_root hα _ _
  have hW'y (i : Fin 2) : W' (faceCell (restrictFace_amalgam_donor hα)
      (faceCell (restrictFace_donor hα) i)) = rootRow i := by
    rw [← faceCell_faceCell (restrictFace_amalgam_context hα) (restrictFace_amalgam_donor hα)
      (restrictFace_context hα) (restrictFace_donor hα) i, hW'z]
    exact separating_root hα i
  have hloc' := (hloc _ hAb).le_of_le (d := ⟨_, hy ⟨1, by decide⟩⟩)
    (d' := ⟨_, hy ⟨0, by decide⟩⟩) (le_of_eq ((hrow _).trans (hrow _).symm)) (by
      rw [grade_faceCell, grade_faceCell]
      exact le_of_eq ((grade_faceCell (restrictFace_donor hα) (⟨0, by decide⟩ : Fin 2)).trans
        (grade_faceCell (restrictFace_donor hα) (⟨1, by decide⟩ : Fin 2)).symm))
  change min (W' _) (W' _) ≤ min (W' _) (W' _) at hloc'
  rw [happex, min_top_right, min_top_right, hW'y, hW'y] at hloc'
  exact absurd (natCast_label_le.mp hloc') (by decide)

end TiedRootCapCounterexample

end VaughtConjecture
