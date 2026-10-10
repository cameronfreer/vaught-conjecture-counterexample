/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthRecognition
import VaughtConjecture.Extension.TowerCatalogueLevel
import VaughtConjecture.MainTheorem.GrowthCatalogueStep

/-!
# The admitted levels of the growth construction

Roadmap, Layer 3 ((R3) and (R4), the full-scope layers of the growth carrier at and above the
threshold).

Over a seed whose amalgam carries the context `t'` and the donor `d`, an amalgam profile is
**admitted** (`ProfileTower.GrowthAdmitsOnClass`) when its context and donor parts are admitted on
the exact class (`StageType.GrowthRequests.AdmitsOnClass`).  The admitted profiles are closed under
the code of the levels at every grade at least the threshold
(`ProfileTower.GrowthAdmitsOnClass.code`): the splice keeps every cell read by the requests, and the
orbit map is monotone, bottom exactly at bottom, and commutes with visibility replacement at the
threshold (`StageType.GrowthRequests.AdmitsOnClass.map`).  The bottom profile is admitted, its cap
being `⊥`.

Hence **the admitted catalogue layer over a level good on the admitted profiles is again good on
the admitted profiles** (`ProfileTower.Lvl.GoodAt.admittedNext`), given its lifts from the two
coatoms: the levels at and above the threshold are admitted catalogue layers, and the only
hypothesis left at each grade is the lift from the two coatoms (the catalogue steps).  A good level
is good on the admitted profiles (`ProfileTower.Lvl.Good.goodAt`), so the first admitted layer may
sit on the canonical levels below the threshold.

**Limits of these levels for recognition.**  The levels built here cannot carry the field ladder of
`Continuation/GrowthLadderRecognition.lean`: (1) a controller at the threshold `N` reads every old
cell through the section of the level at grade `N - 1`, which sees a profile only through its
values at the cells of grade at most `N - 1` (`ProfileTower.Lvl.catσ_eq_of_hat_eq`, compiled), so a
ladder installed in the base cannot carry the values at the cells of grade `N`; (2) overriding the
controllers' rows at the ladder cells with the member's table conflicts with locality at the old
cells of full scope of grades `2, …, N - 1`, which read the ladder (argued); (3) copies of cells of
full scope at the mixed faces are cells of proper scope that are not amalgam cells, against the
invariant `ProfileTower.Lvl.GoodAt.mem_range` (argued).  The recognizing carrier is therefore built
as its own construction (`VaughtConjecture.Extension.LadderBase` for its first layer).

## References

The controllers of the growth step are those of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType.GrowthRequests

variable {α : Ordinal.{u}} {n k : ℕ} {t' : StageType.{u} α k} {D : Scheme.{u} (n + 1)}
  {Q : GrowthRequests t' D}

/-- **Admission on the exact class is carried by a monotone map bottom exactly at bottom** and
commuting with visibility replacement at the threshold. -/
theorem AdmitsOnClass.map {s : Fin t'.card → Label.{u}} {v : Fin D.card → Label.{u}}
    (h : Q.AdmitsOnClass s v) {Ψ : Label.{u} → Label.{u}} (hΨ : Monotone Ψ)
    (hΨb : ∀ x, Ψ x = ⊥ ↔ x = ⊥)
    (hΨv : ∀ i ≤ Q.threshold, ∀ x, Ψ (visibilityReplace Q.threshold i x) =
      visibilityReplace Q.threshold i (Ψ x))
    (hoff : ∀ j ∈ Q.exacts, Q.offset j ≤ Q.threshold) (hR : Q.markerOffset ≤ Q.threshold) :
    Q.AdmitsOnClass (Ψ ∘ s) (Ψ ∘ v) := fun hcls hcap j ↦
  (h (fun x hx ↦ (hΨb _).symm.trans (hcls x hx)) (fun h0 ↦ hcap ((hΨb _).mpr h0)) j).map hΨ
    ((hΨb ⊥).mpr rfl) hΨv (fun hf ↦ hoff j hf) hR

/-- **Admission on the exact class reads the context only below the cap**, the references and the
marker lying below it. -/
theorem AdmitsOnClass.congr {s s' : Fin t'.card → Label.{u}} {v v' : Fin D.card → Label.{u}}
    (h : Q.AdmitsOnClass s v)
    (hs : ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap), s x = s' x)
    (hv : ∀ j, v j = v' j)
    (href : ∀ j ∈ Q.exacts, Q.ref j ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap))
    (hmk : Q.marker ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap)) :
    Q.AdmitsOnClass s' v' := by
  intro hcls hcap j
  have hcb : Q.cap ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) :=
    CellScheme.mem_below_gradedIndex _ _
  have h1 := h (fun x hx ↦ by rw [hs x hx]; exact hcls x hx) (by rw [hs _ hcb]; exact hcap) j
  rw [hv j] at h1
  exact h1.congr (hs _ hcb) (fun hf ↦ hs _ (href j hf)) (hs _ hmk)

end StageType.GrowthRequests

namespace ProfileTower

open StageType

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {t' : StageType.{u} α (m + 1)}
  {d : StageType.{u} α (n + 1)} {e : Fin n ↪ Fin (m + 1)}
  (hleft : I.left = t') (hdon : restrictFace (extendByLast e) I.amalgam = some d)
  (Q : GrowthRequests t' d.toScheme)

/-- An amalgam profile is **admitted** when its context and donor parts are admitted on the exact
class. -/
def GrowthAdmitsOnClass (W : Prof I) : Prop :=
  Q.AdmitsOnClass (fun x ↦ W (ctxCell hleft x)) (fun j ↦ W (donCell hdon j))

/-- The **admitted catalogue predicate**: the amalgam part of a profile with a cutoff is
admitted. -/
def AdmittedCat (P : CProf I) : Prop := GrowthAdmitsOnClass hleft hdon Q (camal P)

variable {hleft hdon Q}

/-- The bottom profile is admitted: its cap is `⊥`. -/
theorem admittedCat_bot : AdmittedCat hleft hdon Q fun _ ↦ ⊥ :=
  fun _ hcap ↦ absurd rfl hcap

/-- **The admitted profiles are closed under the code at a grade `k` at least the threshold**:
the splice at `k` keeps every cell the requests read, and the orbit code is a monotone map bottom
exactly at bottom commuting with visibility replacement at the threshold. -/
theorem GrowthAdmitsOnClass.code {W : Prof I} (h : GrowthAdmitsOnClass hleft hdon Q W)
    {k : ℕ} (hk : Q.threshold ≤ k) (hdN : ∀ j, d.toCellScheme.grade j ≤ Q.threshold)
    (href : ∀ j ∈ Q.exacts,
      Q.ref j ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) ∧
        Q.offset j ≤ Q.threshold)
    (hmk : Q.marker ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) ∧
      Q.markerOffset ≤ Q.threshold) :
    GrowthAdmitsOnClass hleft hdon Q (code k W) := by
  -- the splice
  have hhat : GrowthAdmitsOnClass hleft hdon Q (hat I k W) := by
    refine h.congr (fun x hx ↦ ?_) (fun j ↦ ?_) (fun j hj ↦ (href j hj).1) hmk.1
    · refine (hat_of_le ?_).symm
      rw [(ctxCell_mem hleft x).2]
      exact hx.2.trans hk
    · refine (hat_of_le ?_).symm
      rw [donCell, I.amalgam.toScheme.grade_faceCell]
      exact (hdN j).trans hk
  -- the orbit code
  exact hhat.map (monotone_orbitMap k _) (fun _ ↦ orbitMap_eq_bot_iff)
    (fun i hi x ↦ (isWitness_orbitMap k (hat I k W)).visibilityReplace_comm x _
      (by rw [stepSuppressor_of_le hk]; exact le_top) i hi)
    (fun j hj ↦ (href j hj).2) hmk.2

/-- **The admitted catalogue layer over a level good on the admitted profiles is good on the
admitted profiles**, at a grade `g + 1 ≤ m` at least the threshold, given its lifts from the two
coatoms (`ProfileTower.Lvl.GoodAt.catNext`). -/
theorem Lvl.GoodAt.admittedNext {g : ℕ} {L : Lvl I g}
    (hL : L.GoodAt (GrowthAdmitsOnClass hleft hdon Q)) (hgm : g + 1 ≤ m)
    (hN : Q.threshold ≤ g + 1) (hdN : ∀ j, d.toCellScheme.grade j ≤ Q.threshold)
    (href : ∀ j ∈ Q.exacts,
      Q.ref j ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) ∧
        Q.offset j ≤ Q.threshold)
    (hmk : Q.marker ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) ∧
      Q.markerOffset ≤ Q.threshold)
    (hlift : ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      (L.catS (predCat I (g + 1) (AdmittedCat hleft hdon Q))).rows.CappedLift
        (X := (univ.erase x, g + 1)) (Y := ((univ : Finset (Fin (m + 2))), g + 1))
        ⟨erase_subset _ _, le_rfl⟩) :
    (L.catNext (AdmittedCat hleft hdon Q)).GoodAt (GrowthAdmitsOnClass hleft hdon Q) :=
  hL.catNext hgm (fun _ h ↦ h) (fun _ hP _ ↦ hP.code hN hdN href hmk) admittedCat_bot hlift

/-- **The admitted profiles are closed under the orbit code** at a grade at least the
threshold. -/
theorem GrowthAdmitsOnClass.orbitCode {W : Prof I} (h : GrowthAdmitsOnClass hleft hdon Q W)
    {k : ℕ} (hk : Q.threshold ≤ k)
    (href : ∀ j ∈ Q.exacts, Q.offset j ≤ Q.threshold) (hR : Q.markerOffset ≤ Q.threshold) :
    GrowthAdmitsOnClass hleft hdon Q (orbitCode k W) :=
  h.map (monotone_orbitMap k _) (fun _ ↦ orbitMap_eq_bot_iff)
    (fun i hi x ↦ (isWitness_orbitMap k W).visibilityReplace_comm x _
      (by rw [stepSuppressor_of_le hk]; exact le_top) i hi) href hR

/-- The label of the amalgam at a cell of the context is the label of the context. -/
theorem amalgam_label_ctxCell (x : Fin t'.card) :
    I.amalgam.label (ctxCell hleft x) = t'.label x := by
  subst hleft
  exact StageType.label_faceCell I.restrictFace_left x

/-- The label of the amalgam at a cell of the donor is the label of the donor. -/
theorem amalgam_label_donCell (j : Fin d.card) : I.amalgam.label (donCell hdon j) = d.label j :=
  StageType.label_faceCell hdon j

/-- **The glued labels of the amalgam are admitted**, for requests read exactly at the labels of
the context. -/
theorem growthAdmitsOnClass_label (hex : ∀ j ℓ, Q.CorrectAt t'.label j ℓ ↔ ℓ = d.label j) :
    GrowthAdmitsOnClass hleft hdon Q I.amalgam.label := by
  intro _ _ j
  have h1 : (fun x ↦ I.amalgam.label (ctxCell hleft x)) = t'.label :=
    funext amalgam_label_ctxCell
  rw [h1]
  exact (hex j _).mpr (amalgam_label_donCell j)

/-- **The admitted levels above a level good on the admitted profiles**, at grades at least the
threshold, are good on the admitted profiles up to the grade `m`, given the lifts of every layer
from the two coatoms (`ProfileTower.Lvl.GoodAt.catIter`). -/
theorem Lvl.GoodAt.admittedIter {g' : ℕ} {N : Lvl I g'}
    (hN : N.GoodAt (GrowthAdmitsOnClass hleft hdon Q)) (hthr : Q.threshold ≤ g' + 1)
    (hdN : ∀ j, d.toCellScheme.grade j ≤ Q.threshold)
    (href : ∀ j ∈ Q.exacts,
      Q.ref j ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) ∧
        Q.offset j ≤ Q.threshold)
    (hmk : Q.marker ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) ∧
      Q.markerOffset ≤ Q.threshold)
    (hlift : ∀ j, g' + j + 1 ≤ m → ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      ((N.catIter (AdmittedCat hleft hdon Q) j).catS
        (predCat I (g' + j + 1) (AdmittedCat hleft hdon Q))).rows.CappedLift
        (X := (univ.erase x, g' + j + 1)) (Y := ((univ : Finset (Fin (m + 2))), g' + j + 1))
        ⟨erase_subset _ _, le_rfl⟩) :
    ∀ j, g' + j ≤ m →
      (N.catIter (AdmittedCat hleft hdon Q) j).GoodAt (GrowthAdmitsOnClass hleft hdon Q) :=
  hN.catIter (fun _ h ↦ h) (fun _ hk _ hP _ ↦ hP.code (by omega) hdN href hmk) admittedCat_bot
    hlift

/-- **The completion below the full grade of the admitted construction**: over a level good on
the admitted profiles at a grade `g'` with the threshold at most `g' + 1`, the admitted levels up to
the grade `m = g' + j` (`j ≥ 1`) and the top layer, given the lifts of every layer from the two
coatoms and the bottom step at the top (`ProfileTower.Lvl.TopBotStep`); the last level extends at
`⊥` on the admitted profiles (`ProfileTower.Lvl.GoodAt.hasBotExtensionOn_catNext`), and the glued
labels of the amalgam are admitted (`ProfileTower.growthAdmitsOnClass_label`). -/
theorem Lvl.GoodAt.nonempty_admittedCompletion {g' : ℕ} {N : Lvl I g'}
    (hN : N.GoodAt (GrowthAdmitsOnClass hleft hdon Q)) (hthr : Q.threshold ≤ g' + 1)
    (hex : ∀ j ℓ, Q.CorrectAt t'.label j ℓ ↔ ℓ = d.label j)
    (hdN : ∀ j, d.toCellScheme.grade j ≤ Q.threshold)
    (href : ∀ j ∈ Q.exacts,
      Q.ref j ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) ∧
        Q.offset j ≤ Q.threshold)
    (hmk : Q.marker ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) ∧
      Q.markerOffset ≤ Q.threshold)
    {j : ℕ} (hj : g' + (j + 1) = m) (hm : 1 ≤ m)
    (hlift : ∀ i, g' + i + 1 ≤ m → ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      ((N.catIter (AdmittedCat hleft hdon Q) i).catS
        (predCat I (g' + i + 1) (AdmittedCat hleft hdon Q))).rows.CappedLift
        (X := (univ.erase x, g' + i + 1)) (Y := ((univ : Finset (Fin (m + 2))), g' + i + 1))
        ⟨erase_subset _ _, le_rfl⟩)
    (hstep : ∀ M : Lvl I m, M.GoodAt (GrowthAdmitsOnClass hleft hdon Q) →
      M.TopBotStep (GrowthAdmitsOnClass hleft hdon Q)) :
    Nonempty (CompletionBelowFullGrade I) := by
  have hgood := hN.admittedIter hthr hdN href hmk hlift
  have hlast := hgood (j + 1) (by omega)
  have hprev := hgood j (by omega)
  have hbot : (N.catIter (AdmittedCat hleft hdon Q) (j + 1)).HasBotExtensionOn
      (GrowthAdmitsOnClass hleft hdon Q) :=
    hprev.hasBotExtensionOn_catNext (fun _ h ↦ h)
      (fun _ hW _ ↦ hW.orbitCode (by omega) (fun i hi ↦ (href i hi).2) hmk.2)
  subst hj
  exact ⟨hlast.completion_of_step hbot (hstep _ hlast) (growthAdmitsOnClass_label hex) hm⟩

end ProfileTower

end VaughtConjecture
