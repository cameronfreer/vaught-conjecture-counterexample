/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthAdmittedStep
import VaughtConjecture.Extension.TowerCatalogueLayer
import VaughtConjecture.MainTheorem.GrowthSeed

/-!
# The catalogue step of the growth construction at the context coatom

Roadmap, Layer 3 ((R3) and (R4), the controllers at the activation grade over the growth seed).

Over a seed `I` whose first coatom type is the context `t'` (`StageType.exists_growthSeed`) and
whose amalgam has the donor `d` as its face along the root followed by the new point, the
**admitted catalogue** is the catalogue (`ProfileTower.predCat`) of the predicate
`ProfileTower.GrowthAdmits`: the profile, read on the context face and on the donor face, is
admitted by the requests (`StageType.GrowthRequests.Admits`).  The capped lift from the context
coatom into the catalogue layer over a good level (`ProfileTower.Lvl.Good.cappedLift_catS`) needs
the catalogue step at that coatom (`ProfileTower.Lvl.CatStep`) and its bottom-cap form.

**The step below the cap value** (`ProfileTower.Lvl.catStep_of_catStepAbove`).  At a positive cap
`h` above the cap value of the labelling, the step holds: the amalgam's capped lift at `h`
(`ProfileTower.Lvl.Good.exists_cutLawful_of_coatom_cap`), the admitted step below the cap value
(`StageType.GrowthRequests.admits_of_min_eq_of_lt`), and invariance of admission under the orbit
code (`StageType.GrowthRequests.Admits.orbitMap`).  So the catalogue step at the context coatom is
**equivalent** to its part at the caps `h` at most the cap value
(`ProfileTower.Lvl.CatStepAbove`, open): a lawful completion of the context section on the donor
face, agreeing with an admitted profile capped at `h` and reading the requests below the cap value
(the request lift of `GrowthCarrier.exists_requestLift_of_cappedLift`).

## References

The controllers of the growth step are those of [Kni26, §4].
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme StageType

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {t' : StageType.{u} α (m + 1)}
  {d : StageType.{u} α (n + 1)} {e : Fin n ↪ Fin (m + 1)}

/-- The context face of the amalgam of a seed whose first coatom type is `t'`. -/
theorem comap_left_eq (hleft : I.left = t') :
    I.amalgam.toScheme.comap (Coatom.left m) = t'.toScheme := by
  obtain ⟨hf, hc⟩ := (restrictFace_eq_some_iff _ _).mp I.restrictFace_left
  rw [← hleft, ← hc]
  rfl

/-- The donor face of the amalgam along the root followed by the new point. -/
theorem comap_donor_eq (hdon : restrictFace (extendByLast e) I.amalgam = some d) :
    I.amalgam.toScheme.comap (extendByLast e) = d.toScheme := by
  obtain ⟨hf, hc⟩ := (restrictFace_eq_some_iff _ _).mp hdon
  rw [← hc]
  rfl

/-- The cell of the amalgam at a cell of the context. -/
noncomputable def ctxCell (hleft : I.left = t') (x : Fin t'.card) : Fin I.amalgam.card :=
  I.amalgam.toScheme.faceCell (Coatom.left m) (comap_left_eq hleft) x

/-- The cell of the amalgam at a cell of the donor. -/
noncomputable def donCell (hdon : restrictFace (extendByLast e) I.amalgam = some d)
    (j : Fin d.card) : Fin I.amalgam.card :=
  I.amalgam.toScheme.faceCell (extendByLast e) (comap_donor_eq hdon) j

/-- The predicate of the **admitted catalogue**: the profile, read on the context face and on the
donor face, is admitted by the requests. -/
def GrowthAdmits (hleft : I.left = t') (hdon : restrictFace (extendByLast e) I.amalgam = some d)
    (Q : GrowthRequests t' d.toScheme) (P : CProf I) : Prop :=
  Q.Admits (fun x ↦ P (Sum.inl (ctxCell hleft x))) (fun j ↦ P (Sum.inl (donCell hdon j)))

/-- The bottom profile is admitted: its cap value is `⊥`. -/
theorem growthAdmits_bot (hleft : I.left = t')
    (hdon : restrictFace (extendByLast e) I.amalgam = some d) (Q : GrowthRequests t' d.toScheme) :
    GrowthAdmits hleft hdon Q fun _ ↦ ⊥ :=
  fun _ hcap ↦ absurd rfl hcap

/-- A cell of the context lies in the context coatom of the amalgam, at its grade. -/
theorem ctxCell_mem (hleft : I.left = t') (x : Fin t'.card) :
    I.amalgam.toCellScheme.scope (ctxCell hleft x) ⊆ univ.erase (Fin.last (m + 1)) ∧
      I.amalgam.toCellScheme.grade (ctxCell hleft x) = t'.toCellScheme.grade x := by
  refine ⟨?_, I.amalgam.toScheme.grade_faceCell _ x⟩
  rw [ctxCell, I.amalgam.toScheme.scope_faceCell]
  intro z hz
  obtain ⟨i, -, rfl⟩ := mem_map.mp hz
  simp

variable {g : ℕ} {L : Lvl I g}

variable (L) in
/-- **The catalogue step above the cap value**, at the context coatom: the part of
`ProfileTower.Lvl.CatStep` at the caps `h` at most the value of the labelling at the cap of the
context.  Open. -/
def Lvl.CatStepAbove (hleft : I.left = t')
    (hdon : restrictFace (extendByLast e) I.amalgam = some d) (Q : GrowthRequests t' d.toScheme) :
    Prop :=
  ∀ P ∈ predCat I (g + 1) (GrowthAdmits hleft hdon Q), ∀ h : Label.{u},
    IsSelfVisible (g + 1) h → IsShort (g + 1) h → ⊥ < h →
    ∀ w : Fin (L.catS (predCat I (g + 1) (GrowthAdmits hleft hdon Q))).card → Label.{u},
    (L.catS (predCat I (g + 1) (GrowthAdmits hleft hdon Q))).rows.IsLawfulBelow
      (univ.erase (Fin.last (m + 1)), g + 1) (fun z ↦ w z) →
    (∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
      I.amalgam.toCellScheme.scope d ⊆ univ.erase (Fin.last (m + 1)) →
        min (w (Fin.castAdd _ (L.embed d))) h = min (P (Sum.inl d)) h) →
    h ≤ w (Fin.castAdd _ (L.embed (ctxCell hleft Q.cap))) →
    ∃ (W : Prof I) (β : Label.{u}), IsCutLawful I (g + 1) W ∧
      (∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
        I.amalgam.toCellScheme.scope d ⊆ univ.erase (Fin.last (m + 1)) →
          W d = w (Fin.castAdd _ (L.embed d))) ∧
      (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧ β ∈ codeGrid (g + 1) (bound I) ∧
      min β h = min (P (Sum.inr ())) h ∧
      GrowthAdmits hleft hdon Q (withCut (orbitCode (g + 1) W) β)

/-- **The catalogue step at the context coatom from its part above the cap value**: below the
cap value the step holds, by the capped lift of the amalgam, the admitted step below the cap value,
and invariance of admission under the orbit code. -/
theorem Lvl.Good.catStep_of_catStepAbove (hL : L.Good) (hgm : g + 1 ≤ m)
    (hleft : I.left = t') (hdon : restrictFace (extendByLast e) I.amalgam = some d)
    (Q : GrowthRequests t' d.toScheme) (hN : Q.threshold = g + 1)
    (hoff : ∀ j ∈ Q.exacts, Q.offset j ≤ Q.threshold) (hR : Q.markerOffset ≤ Q.threshold)
    (habove : L.CatStepAbove hleft hdon Q) :
    L.CatStep (GrowthAdmits hleft hdon Q) (Fin.last (m + 1)) := by
  intro P hP h hh hs hb w hw hwP
  set c := ctxCell hleft Q.cap with hc
  by_cases hhc : h ≤ w (Fin.castAdd _ (L.embed c))
  · exact habove P hP h hh hs hb w hw hwP hhc
  have hlt : w (Fin.castAdd _ (L.embed c)) < h := _root_.not_le.mp hhc
  obtain ⟨hPB, hPc, -, hPA⟩ := mem_predCat.mp hP
  have hx : Fin.last (m + 1) ∈ (Pts : Finset (Fin (m + 2))) := by simp [Pts]
  obtain ⟨W, hW, hWw, hWP⟩ := hL.exists_cutLawful_of_coatom_cap hgm hx hPc hh hw hwP
  have hcmem := ctxCell_mem hleft Q.cap
  have hcN : I.amalgam.toCellScheme.grade c = g + 1 := hcmem.2.trans hN
  have hWc : W c = w (Fin.castAdd _ (L.embed c)) := hWw c hcN.le hcmem.1
  -- the cap value is self-visible at the threshold
  have hvis : IsSelfVisible Q.threshold (W c) := by
    obtain ⟨hord, -, -⟩ := Rows.isLawfulBelow_iff_forall.mp hW.1
    have := hord c ⟨by
      have h1 := hcmem.1
      intro z hz
      exact h1 hz, hcN.le⟩
    rw [hN, ← hcN]
    exact this
  -- admission of `W`, then of its orbit code
  have hadmW : Q.Admits (fun x ↦ W (ctxCell hleft x)) (fun j ↦ W (donCell hdon j)) :=
    StageType.GrowthRequests.admits_of_min_eq_of_lt hPA hb.ne' (fun x ↦ hWP _) (fun j ↦ hWP _)
      (by rw [← hWc] at hlt; exact hlt) hvis hoff hR
  refine ⟨W, P (Sum.inr ()), hW, hWw, hWP, hPB _, rfl, ?_⟩
  exact hadmW.orbitMap hN.le W hoff hR

/-- **The capped lift from the context coatom into the admitted catalogue layer**, from the two
open parts of the catalogue step at the context coatom: the step at the cap `⊥`
(`ProfileTower.Lvl.CatStepBot`, a request lift at the cap `⊥`) and the step above the cap value
(`ProfileTower.Lvl.CatStepAbove`). -/
theorem Lvl.Good.cappedLift_context_of_open (hL : L.Good) (hgm : g + 1 ≤ m)
    (hleft : I.left = t') (hdon : restrictFace (extendByLast e) I.amalgam = some d)
    (Q : GrowthRequests t' d.toScheme) (hN : Q.threshold = g + 1)
    (hoff : ∀ j ∈ Q.exacts, Q.offset j ≤ Q.threshold) (hR : Q.markerOffset ≤ Q.threshold)
    (hbot : L.CatStepBot (GrowthAdmits hleft hdon Q) (Fin.last (m + 1)))
    (habove : L.CatStepAbove hleft hdon Q) :
    (L.catS (predCat I (g + 1) (GrowthAdmits hleft hdon Q))).rows.CappedLift
      (X := (univ.erase (Fin.last (m + 1)), g + 1))
      (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  hL.cappedLift_catS_of_steps hgm (by simp [Pts]) (growthAdmits_bot hleft hdon Q) hbot
    (hL.catStep_of_catStepAbove hgm hleft hdon Q hN hoff hR habove)

/-- **The capped lift from the donor coatom into the admitted catalogue layer**, from the two
catalogue steps at the donor coatom `univ.erase m` (both open): the donor-face lift. -/
theorem Lvl.Good.cappedLift_donor_of_open (hL : L.Good) (hgm : g + 1 ≤ m)
    (hleft : I.left = t') (hdon : restrictFace (extendByLast e) I.amalgam = some d)
    (Q : GrowthRequests t' d.toScheme)
    (hbot : L.CatStepBot (GrowthAdmits hleft hdon Q) (Fin.castSucc (Fin.last m)))
    (hstep : L.CatStep (GrowthAdmits hleft hdon Q) (Fin.castSucc (Fin.last m))) :
    (L.catS (predCat I (g + 1) (GrowthAdmits hleft hdon Q))).rows.CappedLift
      (X := (univ.erase (Fin.castSucc (Fin.last m)), g + 1))
      (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  hL.cappedLift_catS_of_steps hgm (by simp [Pts]) (growthAdmits_bot hleft hdon Q) hbot hstep

end VaughtConjecture.ProfileTower
