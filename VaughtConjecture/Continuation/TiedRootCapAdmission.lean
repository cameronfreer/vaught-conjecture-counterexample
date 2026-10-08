/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapCarrier
import VaughtConjecture.Extension.CapTransport

/-!
# The orbit-literal admission at the context with separated tied root cells

Roadmap, Layer 3 ((R3) of the table of 3.4).

`CapRequests`, `CapRequests.refValue`, `CapRequests.markerValue` and `CapRequests.IsCorrect` are
copied verbatim from the cap-requests lane (`Extension/CapRequests.lean` there), so that this
file does not depend on that branch.

At the context of `TiedRootCapCounterexample`, with the cap requests of (R3)
(`TiedRootCapCounterexample.capRequests`: the cap as cap and marker, threshold `3`, the apex of the
donor read from below), the **orbit-literal admission**
(`TiedRootCapCounterexample.AdmOrbit`: a state whose private part is a capped transformation image
of the labels of the context, `TiedRootCapCounterexample.IsOrbitLiteral`, is correct) is tested
on every carrier (a legal one-point extension of the context whose face along `extendByLast rootEmb`
is the donor).  All three statements are compiled in this repository (theorem named).

* **(b) holds** (`TiedRootCapCounterexample.exists_admOrbit_separating`): the lawful extension of
  the separating labelling, `⊤` at the cell of graded index `(univ, 3)` that availability from the
  cap reaches, is admitted there, vacuously: it separates the two root cells, which carry the same
  label and grade, so it is not orbit-literal
  (`TiedRootCapCounterexample.not_isOrbitLiteral_of_separates`).
* **(a) fails** (`TiedRootCapCounterexample.exists_admOrbit_not_admOrbit_collapse`): the admission
  is not closed under images.  The collapse at `3` (`Label.collapseShifter`, a witness bounded by
  the grade `3`) sends that extension to a state literal on the context, which is not correct: the
  extension is not `⊤` at the apex of the donor
  (`TiedRootCapCounterexample.apex_ne_top_of_extends`), and the collapse sends only `⊤` to `⊤`.
* **(c) fails** (`TiedRootCapCounterexample.exists_literal_top_apex_ne_top`,
  `TiedRootCapCounterexample.not_recognition_admOrbit`): every carrier has a labelling lawful below
  `(univ, 3)`, equal to the labels of the context on the context, `⊤` at a cell of graded index
  `(univ, 3)` and not `⊤` at the apex of the donor (the collapse of the separating extension).  So
  recognition (every capped state of a labelling lawful below `(univ, 3)` at a cell of that graded
  index is admitted) fails for the orbit-literal admission, and for every admission whose class
  contains the literal states, at every carrier.

**What this does not reach.**  Determination at a cutoff (within the receiving family of a carrier)
asks the reading only at labellings of the whole carrier that agree with its own labelling below
the cutoff; the labelling of (c) is lawful below `(univ, 3)` and need not be one.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Cap requests and correctness -/

/-- **Cap requests** on a family of cells `ι`: the cap and its threshold `N`, the marker offset
`R < N`, the cells `Z`, `F`, `T` to be read as `⊥`, exactly, and from below, the reference cell and
the offset of each cell, and the marker. -/
structure CapRequests (ι : Type*) where
  /-- The cap. -/
  cap : ι
  /-- The threshold of the cap. -/
  N : ℕ
  /-- The marker offset. -/
  R : ℕ
  /-- The marker offset is below the threshold. -/
  R_lt_N : R < N
  /-- The cells read as `⊥` under the cap. -/
  Z : Set ι
  /-- The cells read exactly under the cap, through their references. -/
  F : Set ι
  /-- The cells read from below under the cap, through the marker. -/
  T : Set ι
  /-- The reference cell of a cell. -/
  ref : ι → ι
  /-- The offset of a cell. -/
  off : ι → ℕ
  /-- The marker. -/
  marker : ι

namespace CapRequests

variable {ι : Type*} (r : CapRequests ι) {s s' : ι → Label.{u}}

/-- The **reference value** of a cell `f` in a state `s`: the visibility replacement at `N` with
the offset of `f` of the value at the reference cell, capped at the cap. -/
noncomputable def refValue (s : ι → Label.{u}) (f : ι) : Label.{u} :=
  min (visibilityReplace r.N (r.off f) (s (r.ref f))) (s r.cap)

/-- The **marker value** of a state `s`: the visibility replacement at `N` with value `R` of the
value at the marker, capped at the cap. -/
noncomputable def markerValue (s : ι → Label.{u}) : Label.{u} :=
  min (visibilityReplace r.N r.R (s r.marker)) (s r.cap)

/-- A state is **correct** for the requests: capped at the cap, it is `⊥` on `Z`, the reference
value on `F`, and at least the marker value on `T`. -/
structure IsCorrect (s : ι → Label.{u}) : Prop where
  /-- The cells of `Z` are `⊥` under the cap. -/
  eq_bot : ∀ z ∈ r.Z, min (s z) (s r.cap) = ⊥
  /-- The cells of `F` are their reference values under the cap. -/
  eq_refValue : ∀ f ∈ r.F, min (s f) (s r.cap) = r.refValue s f
  /-- The cells of `T` are at least the marker value under the cap. -/
  markerValue_le : ∀ y ∈ r.T, r.markerValue s ≤ min (s y) (s r.cap)

end CapRequests

/-! ### The orbit-literal admission at the context -/

namespace TiedRootCapCounterexample

open StageType

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α) {D : StageType.{u} α 4}
  (h₁ : restrictFace Fin.castSuccEmb D = some (context hα))
  (h₂ : restrictFace (extendByLast rootEmb) D = some (donor hα))

/-- **The cap requests of (R3) at the context**, on the cells of a carrier: the cap of the context
as cap and marker, threshold `3`, offset `0`, and the apex of the donor read from below. -/
noncomputable def capRequests : CapRequests (Fin D.card) where
  cap := faceCell h₁ (capCell hα)
  N := 3
  R := 0
  R_lt_N := by omega
  Z := ∅
  F := ∅
  T := {faceCell h₂ (donorApex hα)}
  ref := id
  off := fun _ ↦ 0
  marker := faceCell h₁ (capCell hα)

/-- A state of a carrier is **orbit-literal** when its private part (the cells of the context) is
a capped transformation image of the labels of the context. -/
def IsOrbitLiteral (s : Fin D.card → Label.{u}) : Prop :=
  ∃ g σ, IsWitness g σ ∧ ∀ z, s (faceCell h₁ z) =
    min (σ ((context hα).label z)) (g ((context hα).toCellScheme.grade z))

/-- The **orbit-literal admission**: an orbit-literal state is correct for the cap requests. -/
def AdmOrbit (s : Fin D.card → Label.{u}) : Prop :=
  IsOrbitLiteral hα h₁ s → (capRequests hα h₁ h₂).IsCorrect s

/-- A state `⊤` at the cap and correct is `⊤` at the apex of the donor. -/
theorem apex_eq_top_of_isCorrect {s : Fin D.card → Label.{u}}
    (hcap : s (faceCell h₁ (capCell hα)) = ⊤) (hs : (capRequests hα h₁ h₂).IsCorrect s) :
    s (faceCell h₂ (donorApex hα)) = ⊤ := by
  have h := hs.markerValue_le _ rfl
  simp only [CapRequests.markerValue, capRequests, hcap, visibilityReplace_top, min_self,
    min_top_right] at h
  exact top_le_iff.mp h

/-- The labels of the context are orbit-literal for any state agreeing with them. -/
theorem isOrbitLiteral_of_eq {s : Fin D.card → Label.{u}}
    (hs : ∀ z, s (faceCell h₁ z) = (context hα).label z) : IsOrbitLiteral hα h₁ s :=
  ⟨fun _ ↦ ⊤, id, IsWitness.id_top, fun z ↦ by rw [hs, min_top_right]; rfl⟩

/-- **A state separating the root is not orbit-literal**: the two root cells carry the same label
`3` and the same grade in the context, so every capped transformation image of the labels ties
them. -/
theorem not_isOrbitLiteral_of_separates {s : Fin D.card → Label.{u}}
    (hs : s (faceCell h₁ (faceCell (restrictFace_context hα) (⟨0, by decide⟩ : Fin 2))) ≠
      s (faceCell h₁ (faceCell (restrictFace_context hα) (⟨1, by decide⟩ : Fin 2)))) :
    ¬ IsOrbitLiteral hα h₁ s := by
  rintro ⟨g, σ, -, hσ⟩
  apply hs
  rw [hσ, hσ]
  exact congrArg₂ (fun x y ↦ min (σ x) (g y))
    ((context_label_root hα _).trans (context_label_root hα _).symm)
    ((grade_faceCell (restrictFace_context hα) (⟨0, by decide⟩ : Fin 2)).trans
      (grade_faceCell (restrictFace_context hα) (⟨1, by decide⟩ : Fin 2)).symm)

/-- Every lawful extension of the separating labelling to a carrier is not `⊤` at the apex of the
donor (`TiedRootCapCounterexample.not_exists_fill_bot`). -/
theorem apex_ne_top_of_extends {a : Fin D.card → Label.{u}}
    (ha : D.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 3) (fun d ↦ a d))
    (hext : ∀ z, a (faceCell h₁ z) = separating hα z) :
    a (faceCell h₂ (donorApex hα)) ≠ ⊤ := fun htop ↦
  not_exists_fill_bot hα h₁ h₂ ⟨a, ha, hext, by rw [htop]; exact le_top⟩

/-- **A lawful extension of the separating labelling to a carrier**, `⊤` at a cell of graded index
`(univ, 3)` (availability from the cap). -/
theorem exists_extension_separating (hD : D.IsLegal) :
    ∃ a : Fin D.card → Label.{u}, D.rows.IsLawful a ∧
      (∀ z, a (faceCell h₁ z) = separating hα z) ∧
      ∃ u, D.toCellScheme.gradedIndex u = ((univ : Finset (Fin 4)), 3) ∧ a u = ⊤ := by
  obtain ⟨a, ha, hext⟩ := exists_isLawful_extend_of_restrictFace hD h₁ (isLawful_separating hα)
  obtain ⟨u₀, hu₀⟩ := hD.isComplete ((univ : Finset (Fin 4)), 3)
    ⟨D.univ_mem_faces, by omega, by simp⟩
  have hcg : D.toCellScheme.grade (faceCell h₁ (capCell hα)) = 3 :=
    (grade_faceCell h₁ _).trans (context_grade_cap hα)
  obtain ⟨u, hu, hcu⟩ := ha.availability (faceCell h₁ (capCell hα)) u₀
    (by rw [show D.toCellScheme.scope u₀ = univ from congrArg Prod.fst hu₀]; exact subset_univ _)
    (hcg.trans (congrArg Prod.snd hu₀).symm)
  refine ⟨a, ha, hext, u, hu.trans hu₀, top_le_iff.mp ?_⟩
  rw [hext, separating_capCell] at hcu
  exact hcu

/-- The collapse of the separating labelling is the labelling of the context. -/
theorem collapse_separating (z : Fin (context hα).card) :
    collapseShifter three (separating hα z) = (context hα).label z := by
  induction z using Fin.lastCases with
  | last => rw [separating_capCell, collapseShifter_top, context_label_cap]
  | cast d => rw [separating_castSucc, context_label_castSucc]

/-- **(c) fails: a literal labelling `⊤` at a cell of graded index `(univ, 3)` and not at the
apex.**  Every carrier has a labelling lawful below `(univ, 3)`, equal to the labels of the context
on the context (orbit-literal with the identity), `⊤` at a cell of graded index `(univ, 3)`, and not
`⊤` at the apex of the donor: the collapse (`Label.collapseShifter` at `3`, a witness bounded by the
grade `3` sending only `⊥` to `⊥` and only `⊤` to `⊤`) of a lawful extension of the separating
labelling. -/
theorem exists_literal_top_apex_ne_top (hD : D.IsLegal) :
    ∃ q : Fin D.card → Label.{u}, D.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 3)
      (fun d ↦ q d) ∧ (∀ z, q (faceCell h₁ z) = (context hα).label z) ∧
      ∃ u, D.toCellScheme.gradedIndex u = ((univ : Finset (Fin 4)), 3) ∧ q u = ⊤ ∧
        q (faceCell h₂ (donorApex hα)) ≠ ⊤ := by
  obtain ⟨a, ha, hext, u, hu, hau⟩ := exists_extension_separating hα h₁ hD
  have haB := ha.isLawfulBelow ((univ : Finset (Fin 4)), 3)
  refine ⟨collapseShifter three ∘ a, ?_, fun z ↦ ?_, u, hu, ?_, fun h ↦ ?_⟩
  · exact haB.map_of_apply_eq_bot (fun d ↦ d.2.2) isWitness_three
      fun _ hd ↦ eq_bot_of_collapseShifter_eq_bot three_ne_bot hd
  · rw [Function.comp_apply, hext, collapse_separating]
  · rw [Function.comp_apply, hau, collapseShifter_top]
  · exact apex_ne_top_of_extends hα h₁ h₂ haB hext (eq_top_of_collapseShifter_eq_top three_ne_top h)

/-- **Recognition with the orbit-literal admission fails at every carrier**: no legal carrier has
every capped state of a labelling lawful below `(univ, 3)` at a cell of graded index `(univ, 3)`
admitted.  The literal labelling of `exists_literal_top_apex_ne_top`, capped at a cell labelled
`⊤`, is orbit-literal and not correct. -/
theorem not_recognition_admOrbit (hD : D.IsLegal) :
    ¬ ∀ q : Fin D.card → Label.{u}, D.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 3)
      (fun d ↦ q d) → ∀ u, D.toCellScheme.gradedIndex u = ((univ : Finset (Fin 4)), 3) →
        AdmOrbit hα h₁ h₂ (fun d ↦ min (q d) (q u)) := by
  intro hrec
  obtain ⟨q, hq, hlit, u, hu, hqu, hapex⟩ := exists_literal_top_apex_ne_top hα h₁ h₂ hD
  have hadm := hrec q hq u hu
  simp only [hqu, min_top_right] at hadm
  have hcap : q (faceCell h₁ (capCell hα)) = ⊤ := by rw [hlit, context_label_cap]
  exact hapex (apex_eq_top_of_isCorrect hα h₁ h₂ hcap
    (hadm (isOrbitLiteral_of_eq hα h₁ hlit)))

/-- **(a) fails: the orbit-literal admission is not closed under images.**  At every carrier, the
lawful extension of the separating labelling (`⊤` at the cap) is admitted (vacuously: it separates
the root, so it is not orbit-literal), and its collapse, the image under a witness bounded by the
grade `3`, is orbit-literal and not correct. -/
theorem exists_admOrbit_not_admOrbit_collapse (hD : D.IsLegal) :
    ∃ s : Fin D.card → Label.{u}, AdmOrbit hα h₁ h₂ s ∧
      ¬ AdmOrbit hα h₁ h₂ (collapseShifter three ∘ s) := by
  obtain ⟨a, ha, hext, -⟩ := exists_extension_separating hα h₁ hD
  refine ⟨a, fun hlit ↦ absurd hlit (not_isOrbitLiteral_of_separates hα h₁ ?_), fun hadm ↦ ?_⟩
  · rw [hext, hext, separating_root, separating_root]
    exact fun h ↦ absurd (natCast_label_inj.mp h) (by decide)
  · have hlit : ∀ z, (collapseShifter three ∘ a) (faceCell h₁ z) = (context hα).label z :=
      fun z ↦ by rw [Function.comp_apply, hext, collapse_separating]
    have hcap : (collapseShifter three ∘ a) (faceCell h₁ (capCell hα)) = ⊤ := by
      rw [hlit, context_label_cap]
    have h := apex_eq_top_of_isCorrect hα h₁ h₂ hcap (hadm (isOrbitLiteral_of_eq hα h₁ hlit))
    exact apex_ne_top_of_extends hα h₁ h₂ (ha.isLawfulBelow _) hext
      (eq_top_of_collapseShifter_eq_top three_ne_top h)

/-- **(b) holds: the separating extension is admitted** at the cell of graded index `(univ, 3)`
that availability reaches: its capped state there is the extension itself, which separates the
root and so is not orbit-literal. -/
theorem exists_admOrbit_separating (hD : D.IsLegal) :
    ∃ a : Fin D.card → Label.{u}, D.rows.IsLawful a ∧
      (∀ z, a (faceCell h₁ z) = separating hα z) ∧
      ∃ u, D.toCellScheme.gradedIndex u = ((univ : Finset (Fin 4)), 3) ∧ a u = ⊤ ∧
        AdmOrbit hα h₁ h₂ (fun d ↦ min (a d) (a u)) := by
  obtain ⟨a, ha, hext, u, hu, hau⟩ := exists_extension_separating hα h₁ hD
  refine ⟨a, ha, hext, u, hu, hau,
    fun hlit ↦ absurd hlit (not_isOrbitLiteral_of_separates hα h₁ ?_)⟩
  simp only [hau, min_top_right]
  rw [hext, hext, separating_root, separating_root]
  exact fun h ↦ absurd (natCast_label_inj.mp h) (by decide)

end TiedRootCapCounterexample

end VaughtConjecture
