/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowProfile
import VaughtConjecture.Extension.TowerCatalogueLayer

/-!
# The LOW layer over a level of the profile tower

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the controllers over the
lower full-scope layers); semantic contract, items 3, 4 and 8.

The display of the LOW construction [Kni26, §3.3] is built on the coatom amalgam of the private
context and the donor, with full-scope layers of every grade.  Below the grade `K` of the
controllers these are the levels of the profile tower (`ProfileTower.Lvl`,
`VaughtConjecture.Extension.ProfileTower`); a good level at the grade `g = K - 1`
(`ProfileTower.Lvl.Good`) lifts capped from either coatom into the full face at every grade at
most `g`.  This file appends the controllers at the grade `g + 1` to such a level in the way the
next level of the tower is appended (`ProfileTower.Lvl.next`): profiles on the amalgam, here with
one more field, the cutoff, and rows through the section operator of the level.

**The instance of the tower catalogue layer** (`VaughtConjecture.Extension.TowerCatalogueLayer`).
The LOW layer is the catalogue layer for the predicate `ProfileTower.lowPred` (the LOW clause at
the grade `g + 1` for the designated fields): LOW profiles are profiles with a cutoff
(`ProfileTower.LProf = ProfileTower.CProf`), the LOW catalogue is the catalogue of the LOW clause
(`ProfileTower.lowCat = ProfileTower.predCat`), the LOW layer is the catalogue layer
(`ProfileTower.Lvl.lowS = ProfileTower.Lvl.catS`), and the LOW step is the catalogue step
(`ProfileTower.Lvl.LowStep = ProfileTower.Lvl.CatStep`).  The theorems of this file are the
instances; the bottom profile and every profile with the cutoff `⊥` satisfy the LOW clause (not
active), which is the hypothesis on the predicate at the cap `⊥`.

**The LOW catalogue** (`ProfileTower.lowCat`): profiles with values in the code grid with block
bound `2 N + 2`, amalgam part lawful on the grade-`k` cut and fixed by the orbit code at `k`, and
LOW.  The cutoff is coded on its own: the orbit code of the amalgam part together with the cutoff
need not restrict to an orbit-canonical amalgam profile, and the section operator is readable
only at those (`ProfileTower.Lvl.Good.readable`).

**Rows, extension, capped lift** (`ProfileTower.Lvl.Good.isLawfulBelow_Φlow`,
`ProfileTower.Lvl.Good.lowS_consistent`, `ProfileTower.Lvl.Good.exists_extension_low`,
`ProfileTower.Lvl.Good.exists_extension_low_bot`, `ProfileTower.Lvl.Good.cappedLift_lowS`,
`ProfileTower.Lvl.Good.cappedLift_lowS_of_lowStep`, compiled in this repository, as instances).
The rows are lawful and the layer consistent; an amalgam profile lawful on the cut agreeing with
a profile of the catalogue capped at a short cap, with a cutoff making the coded profile LOW,
extends through the level and the controllers; and the LOW layer over a good level lifts capped
from either coatom into the full face given the LOW step at the positive caps, a statement about
the coatom amalgam of the private context and the donor alone.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

variable (I) in
/-- A **LOW profile** over the amalgam: a profile with a cutoff (`ProfileTower.CProf`). -/
abbrev LProf : Type (u + 1) := CProf I

/-- The amalgam part of a LOW profile. -/
abbrev amal (P : LProf I) : Prof I := camal P

/-- The LOW profile of an amalgam profile and a cutoff. -/
abbrev withCutoff (W : Prof I) (β : Label.{u}) : LProf I := withCut W β

/-- The **LOW predicate** at the grade `k`: the LOW clause for the designated fields, the cutoff
being the extra field. -/
abbrev lowPred (k : ℕ) (N : Finset (Fin I.amalgam.card ⊕ Unit))
    (T : Set (Fin I.amalgam.card ⊕ Unit)) (o r : Fin I.amalgam.card) : LProf I → Prop :=
  IsLowAt k N T (Sum.inl o) (Sum.inl r) (Sum.inr ())

variable (I) in
/-- The **LOW catalogue** at the grade `k`: the catalogue of the LOW predicate. -/
noncomputable abbrev lowCat (k : ℕ) (N : Finset (Fin I.amalgam.card ⊕ Unit))
    (T : Set (Fin I.amalgam.card ⊕ Unit)) (o r : Fin I.amalgam.card) : Finset (LProf I) :=
  predCat I k (lowPred k N T o r)

variable {k : ℕ} {N : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
  {o r : Fin I.amalgam.card}

/-- **A profile with the cutoff `⊥` is LOW**: it is not active. -/
theorem lowPred_withCut_bot (W : Prof I) : lowPred k N T o r (withCut W ⊥) :=
  fun hact ↦ absurd hact not_lt_bot

theorem mem_lowCat {P : LProf I} : P ∈ lowCat I k N T o r ↔
    (∀ f, P f ∈ codeGrid k (bound I)) ∧ IsCutLawful I k (amal P) ∧
      orbitCode k (amal P) = amal P ∧ IsLowAt k N T (Sum.inl o) (Sum.inl r) (Sum.inr ()) P :=
  mem_predCat

/-- **The coded profile of a cut-lawful amalgam profile with a coded cutoff lies in the LOW
catalogue exactly when it is LOW.** -/
theorem mem_lowCat_of {W : Prof I} (hW : IsCutLawful I k W) {β : Label.{u}}
    (hβ : β ∈ codeGrid k (bound I))
    (hlow : IsLowAt k N T (Sum.inl o) (Sum.inl r) (Sum.inr ()) (withCutoff (orbitCode k W) β)) :
    withCutoff (orbitCode k W) β ∈ lowCat I k N T o r :=
  mem_predCat_of hW hβ hlow

/-- The bottom profile is in the LOW catalogue: inactive, so LOW. -/
theorem bot_mem_lowCat : (fun _ ↦ ⊥ : LProf I) ∈ lowCat I k N T o r :=
  bot_mem_predCat fun hact ↦ absurd hact not_lt_bot

/-! ### The LOW layer over a level -/

variable {g : ℕ} {L : Lvl I g}

/-- The row labelling of a LOW profile over a level (`ProfileTower.Lvl.Φcat`). -/
noncomputable abbrev Lvl.Φlow (L : Lvl I g) (C : Finset (LProf I)) (R : LProf I) :
    Fin (L.S.card + C.card) → Label.{u} :=
  L.Φcat C R

/-- **The LOW layer** over a level (`ProfileTower.Lvl.catS`). -/
noncomputable abbrev Lvl.lowS (L : Lvl I g) (C : Finset (LProf I)) : Scheme.{u} (m + 2) :=
  L.catS C

variable {C : Finset (LProf I)}

theorem Lvl.Φlow_castAdd (R : LProf I) (e : Fin L.S.card) :
    L.Φlow C R (Fin.castAdd _ e) = L.σ (amal R) e := Lvl.Φcat_castAdd R e

theorem Lvl.Φlow_natAdd (R : LProf I) (i : Fin C.card) :
    L.Φlow C R (Fin.natAdd _ i) =
      agreementHeight (grid (g + 1) (bound I)) R (C.equivFin.symm i).1 :=
  Lvl.Φcat_natAdd R i

/-- The row labelling of a profile with values in the code grid lies in the code grid. -/
theorem Lvl.Good.Φlow_mem_codeGrid (hL : L.Good) {R : LProf I}
    (hR : ∀ f, R f ∈ codeGrid (g + 1) (bound I)) (z : Fin (L.S.card + C.card)) :
    L.Φlow C R z ∈ codeGrid (g + 1) (bound I) :=
  hL.Φcat_mem_codeGrid hR z

/-- Lawfulness below a pair not above `(univ, g + 1)` in the LOW layer is lawfulness in the level.
-/
theorem Lvl.isLawfulBelow_lowS_iff {X : Finset (Fin (m + 2)) × ℕ}
    (hX : ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ X)
    {v : Fin (L.S.card + C.card) → Label.{u}} :
    (L.lowS C).rows.IsLawfulBelow X (fun d ↦ v d) ↔
      L.S.rows.IsLawfulBelow X (fun d ↦ v (Fin.castAdd _ d)) :=
  L.isLawfulBelow_catS_iff hX

/-- **The row labelling of a LOW profile is lawful below `(univ, g + 1)`** in the LOW layer. -/
theorem Lvl.Good.isLawfulBelow_Φlow (hL : L.Good) {R : LProf I} (hRC : R ∈ C)
    (hRB : ∀ f, R f ∈ codeGrid (g + 1) (bound I)) (hRc : IsCutLawful I (g + 1) (amal R)) :
    (L.lowS C).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g + 1) fun z ↦ L.Φlow C R z :=
  hL.isLawfulBelow_Φcat hRC hRB hRc

/-- **The LOW layer over a good level is consistent.** -/
theorem Lvl.Good.lowS_consistent (hL : L.Good)
    (hCsub : ∀ P ∈ C, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧ IsCutLawful I (g + 1) (amal P)) :
    (L.lowS C).rows.IsConsistent :=
  hL.catS_consistent hCsub

/-- **Lifts below a pair not above `(univ, g + 1)`** are those of the level. -/
theorem Lvl.cappedLift_lowS_iff {X Y : Finset (Fin (m + 2)) × ℕ} (hXY : X ≤ Y)
    (hY : ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ Y) :
    (L.lowS C).rows.CappedLift hXY ↔ L.S.rows.CappedLift hXY :=
  L.cappedLift_catS_iff hXY hY

/-- A cell of the LOW layer of scope other than the ground set below `(univ, g + 1)` is an old
amalgam cell of grade at most `g + 1`. -/
theorem Lvl.Good.exists_old_lowS (hL : L.Good) {z : Fin (L.lowS C).card}
    (hz : z ∈ (L.lowS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1))
    (hne : (L.lowS C).toCellScheme.scope z ≠ univ) :
    ∃ d, I.amalgam.toCellScheme.grade d ≤ g + 1 ∧ z = Fin.castAdd _ (L.embed d) :=
  hL.exists_old_catS hz hne

/-- **Extension through the LOW layer at a positive cap**
(`ProfileTower.Lvl.Good.exists_extension_cat`). -/
theorem Lvl.Good.exists_extension_low (hL : L.Good)
    (hCsub : ∀ P ∈ C, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧ IsCutLawful I (g + 1) (amal P))
    {P : LProf I} (hP : P ∈ C) (hPo : orbitCode (g + 1) (amal P) = amal P) {h : Label.{u}}
    (hh : IsSelfVisible (g + 1) h) (hs : IsShort (g + 1) h) (hb : h ≠ ⊥) {W : Prof I}
    (hWP : ∀ d, min (W d) h = min (P (Sum.inl d)) h) {β : Label.{u}}
    (hβ : min β h = min (P (Sum.inr ())) h) (hQC : withCutoff (orbitCode (g + 1) W) β ∈ C) :
    ∃ q : (L.lowS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) → Label.{u},
      (L.lowS C).rows.IsLawfulBelow (univ, g + 1) q ∧
      (∀ d (hd : I.amalgam.toCellScheme.grade d ≤ g + 1),
        q ⟨Fin.castAdd _ (L.embed d), by
          rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd,
            hL.gradedIndex_embed]; exact ⟨subset_univ _, hd⟩⟩ = W d) ∧
      ∀ z, min (q z) h = min (L.Φlow C P z) h :=
  hL.exists_extension_cat hCsub hP hPo hh hs hb hWP hβ hQC

/-- **Extension through the LOW layer at the cap `⊥`**
(`ProfileTower.Lvl.Good.exists_extension_cat_bot`). -/
theorem Lvl.Good.exists_extension_low_bot (hL : L.Good)
    (hCsub : ∀ P ∈ C, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧ IsCutLawful I (g + 1) (amal P))
    {W : Prof I} (hQC : withCutoff (orbitCode (g + 1) W) ⊥ ∈ C) :
    ∃ q : (L.lowS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) → Label.{u},
      (L.lowS C).rows.IsLawfulBelow (univ, g + 1) q ∧
      ∀ d (hd : I.amalgam.toCellScheme.grade d ≤ g + 1),
        q ⟨Fin.castAdd _ (L.embed d), by
          rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd,
            hL.gradedIndex_embed]; exact ⟨subset_univ _, hd⟩⟩ = W d :=
  hL.exists_extension_cat_bot hCsub hQC

/-- A cell of the LOW layer of graded index `(univ, g + 1)` is a controller. -/
theorem Lvl.exists_natAdd_eq_lowS (L : Lvl I g) {u : Fin (L.lowS C).card}
    (hu : (L.lowS C).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), g + 1)) :
    ∃ i, Fin.natAdd _ i = u :=
  L.exists_natAdd_eq_catS hu

local notation "𝒞" => lowCat I (g + 1) N T o r

/-- **The capped lift from a coatom into the LOW layer over a good level**, given the LOW step on
the amalgam with the cap `⊥` part explicit (`ProfileTower.Lvl.Good.cappedLift_catS`). -/
theorem Lvl.Good.cappedLift_lowS (hL : L.Good) (hgm : g + 1 ≤ m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2))))
    (hbot : ∀ w : Fin (L.lowS 𝒞).card → Label.{u},
      (L.lowS 𝒞).rows.IsLawfulBelow (univ.erase x, g + 1) (fun z ↦ w z) →
      ∃ W : Prof I, IsCutLawful I (g + 1) W ∧
        ∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
          I.amalgam.toCellScheme.scope d ⊆ univ.erase x → W d = w (Fin.castAdd _ (L.embed d)))
    (hstep : ∀ P ∈ 𝒞, ∀ h : Label.{u}, IsSelfVisible (g + 1) h → IsShort (g + 1) h → ⊥ < h →
      ∀ w : Fin (L.lowS 𝒞).card → Label.{u},
      (L.lowS 𝒞).rows.IsLawfulBelow (univ.erase x, g + 1) (fun z ↦ w z) →
      (∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
        I.amalgam.toCellScheme.scope d ⊆ univ.erase x →
          min (w (Fin.castAdd _ (L.embed d))) h = min (P (Sum.inl d)) h) →
      ∃ (W : Prof I) (β : Label.{u}), IsCutLawful I (g + 1) W ∧
        (∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
          I.amalgam.toCellScheme.scope d ⊆ univ.erase x → W d = w (Fin.castAdd _ (L.embed d))) ∧
        (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧ β ∈ codeGrid (g + 1) (bound I) ∧
        min β h = min (P (Sum.inr ())) h ∧
        IsLowAt (g + 1) N T (Sum.inl o) (Sum.inl r) (Sum.inr ())
          (withCutoff (orbitCode (g + 1) W) β)) :
    (L.lowS 𝒞).rows.CappedLift (X := (univ.erase x, g + 1))
      (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  hL.cappedLift_catS hgm hx lowPred_withCut_bot hbot hstep

/-- **The LOW step on the amalgam** from the coatom `univ.erase x` at the grade `g + 1`: the
catalogue step (`ProfileTower.Lvl.CatStep`) for the LOW predicate.  Open. -/
abbrev Lvl.LowStep (L : Lvl I g) (N : Finset (Fin I.amalgam.card ⊕ Unit))
    (T : Set (Fin I.amalgam.card ⊕ Unit)) (o r : Fin I.amalgam.card) (x : Fin (m + 2)) : Prop :=
  L.CatStep (lowPred (g + 1) N T o r) x

/-- **The capped lift from a coatom into the LOW layer over a good level from the LOW step**
(`ProfileTower.Lvl.Good.cappedLift_catS_of_catStep`; the profiles with the cutoff `⊥` are LOW). -/
theorem Lvl.Good.cappedLift_lowS_of_lowStep (hL : L.Good) (hgm : g + 1 ≤ m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) (hstep : L.LowStep N T o r x) :
    (L.lowS 𝒞).rows.CappedLift (X := (univ.erase x, g + 1))
      (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  hL.cappedLift_catS_of_catStep hgm hx lowPred_withCut_bot hstep

end VaughtConjecture.ProfileTower
