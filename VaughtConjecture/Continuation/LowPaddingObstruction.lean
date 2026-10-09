/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowDisplayActual
import VaughtConjecture.Extension.AdmittedLift

/-!
# Two designs of the padding that fail

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the display above the
controllers when the faces carry labels other than `⊥` above `K`); semantic contract, items 3, 4
and 8.

Over the canonical levels the separator `hi` labelled `⊤` forces `⊥` at every cell of grade in
`(K, m]` (`ProfileTower.lowDisplay_label_eq_bot`): every cell of full scope above `K` reads `hi`
through a section of the catalogue layer read at the cutoff `⊥`.  A **padding** is a display in
which the cells of full scope above `K` read `hi` above `⊥`, so that the labels of the two faces
above `K`, which availability puts below the labels of cells of full scope, survive.  This file
records two designs that fail, with the lemma that fails.

**A cutoff read off the amalgam profile, capped-continuously**
(`Label.cutoff_le_donorMax_of_min_eq`, compiled in this repository).  Let the section of the
catalogue layer read the controllers at the profile `P` with a cutoff `β P`.
Lawfulness of the section at `P` needs the profile with the cutoff `β P` to be LOW; capped
agreement of the section needs `β` to agree capped at every cap
where the profiles do.  Then, at a profile `a` whose donor maximum is below a cap `h`, if a profile
`a'` agreeing with `a` capped at `h` is LOW and has a donor top below its frontier, the cutoff of
`a` is at most its donor maximum: `a'` is active with the same donor maximum, and the LOW clause
fails at the top.  The reading of `hi` at the actual profile needs the cutoff above the cutoff cut,
hence above the donor maximum; so such a cutoff function can read `hi` above `⊥` only when no
profile capped-equal to the actual one at a cap above its donor maximum has a donor top below its
frontier (`ProfileTower.cutoff_le_donorMax_of_capped`).

**A sub-catalogue at a positive constant cutoff** (`ProfileTower.not_botLiftProvisionIn_of_forall`,
`ProfileTower.not_botLiftProvisionIn_lowConst`, compiled in this repository).  Restricting the
layers above `K` to the profiles that are LOW at a fixed positive cutoff (so that the section read
at that cutoff is lawful at every profile with a cell) breaks the lift provision at the cap `⊥`
from the donor coatom: the labelling `⊥` below the donor coatom has no completion in the
sub-catalogue, since a profile `⊥` on every donor cell is active at a positive cutoff and its donor
tops are below it.  More generally, no sub-catalogue all of whose profiles are positive somewhere
below a coatom has the provision at `⊥` from that coatom.

So, under the premises of these theorems, a capped-continuous cutoff chosen from the profile reads
`hi` above `⊥` only at a profile with no capped-equal LOW profile having a donor top below its
frontier, and a restriction of the layers above `K` to the profiles LOW at a positive constant
cutoff loses the provision at `⊥` from a coatom below which lie every proper donor field and some
donor top.  Neither theorem gives such a profile or such a coatom in general, so they do not
show that every padding with a cutoff read off the profile fails; they show where these two designs
fail.  The padded construction of [AFK26] carries the cutoff as a field of every profile
above `K` (states: donor labels, private labels, cutoff), with one cell per LOW state at every
grade; `VaughtConjecture.Continuation.LowPaddingLevel` takes the cutoff from the owner instead,
which keeps the profiles `⊥` below the donor coatom.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Label

open Finset

variable {X : Type*} {K : ℕ} {N : Finset X} {T : Set X} {o r β : X}

/-- **A capped-continuous LOW cutoff is at most the donor maximum** at a profile `a` whose donor
maximum is below a cap `h`, when a LOW profile `a'` agreeing with `a` capped at `h` (cutoff
included) has a donor top below its frontier. -/
theorem cutoff_le_donorMax_of_min_eq {a a' : X → Label.{u}} {h : Label.{u}}
    (hag : ∀ f, min (a' f) h = min (a f) h) (hdm : donorMax N a < h)
    (hlow : IsLowAt K N T o r β a') {x : X} (hx : x ∈ T) (hxa : a' x < frontier K o r a') :
    a β ≤ donorMax N a := by
  by_contra hlt
  rw [not_le] at hlt
  have hN : ∀ f ∈ N, a' f = a f := fun f hf ↦ by
    have hfh : a f < h := (le_donorMax hf).trans_lt hdm
    have h1 := hag f
    rw [min_eq_left hfh.le] at h1
    rcases le_or_gt h (a' f) with h2 | h2
    · rw [min_eq_right h2] at h1
      exact absurd h1 (ne_of_gt hfh)
    · rwa [min_eq_left h2.le] at h1
  have hdm' : donorMax N a' = donorMax N a := donorMax_congr hN
  have hβ : donorMax N a < a' β := by
    have h1 := hag β
    have h2 : donorMax N a < min (a β) h := lt_min hlt hdm
    rw [← h1] at h2
    exact h2.trans_le (min_le_left _ _)
  have := hlow (hdm' ▸ hβ) x hx
  exact absurd ((le_max_right _ _).trans this) (not_le.mpr hxa)

end VaughtConjecture.Label

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-! ### A cutoff read off the amalgam profile -/

/-- **A capped-continuous cutoff on amalgam profiles, LOW at the profiles where its section is
lawful, is at most the donor maximum** at every profile `P` with donor maximum below a cap `h` that
agrees capped at `h` with such a profile `P'` having a donor top below its frontier. -/
theorem cutoff_le_donorMax_of_capped {K : ℕ} {N : Finset (Fin I.amalgam.card ⊕ Unit)}
    {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card} (β : Prof I → Label.{u})
    {P P' : Prof I} {h : Label.{u}} (hag : ∀ d, min (P' d) h = min (P d) h)
    (hβ : min (β P') h = min (β P) h)
    (hdm : donorMax N (withCut P (β P)) < h)
    (hlow : lowPred K N T o r (withCut P' (β P')))
    {x : Fin I.amalgam.card ⊕ Unit} (hx : x ∈ T)
    (hxa : withCut P' (β P') x < frontier K (Sum.inl o) (Sum.inl r) (withCut P' (β P'))) :
    β P ≤ donorMax N (withCut P (β P)) :=
  cutoff_le_donorMax_of_min_eq (a := withCut P (β P)) (a' := withCut P' (β P'))
    (fun f ↦ by rcases f with d | z; exacts [hag d, hβ]) hdm hlow hx hxa

/-! ### A sub-catalogue at a positive constant cutoff -/

/-- **A sub-catalogue all of whose profiles are positive somewhere below a coatom has no lift
provision at `⊥` from that coatom**: the labelling `⊥` below the coatom has no completion with its
code in the sub-catalogue. -/
theorem not_botLiftProvisionIn_of_forall {C : Finset (Prof I)} {k : ℕ} {x : Fin (m + 2)}
    (hC : ∀ R ∈ C, ∃ z ∈ I.amalgam.toCellScheme.below (univ.erase x, k), R z ≠ ⊥) :
    ¬ BotLiftProvisionIn C k x := by
  intro h
  obtain ⟨W, -, hWf, hWC⟩ := h (fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _)
  obtain ⟨z, hz, hne⟩ := hC _ hWC
  apply hne
  rw [orbitCode_eq_bot_iff, hat_of_le hz.2]
  exact hWf z hz

open Classical in
/-- The **sub-catalogue at a constant cutoff** `β` at the grade `k`: the profiles of the catalogue
whose profile with the cutoff `β` satisfies the LOW clause. -/
noncomputable def lowConstCat (k K : ℕ) (N : Finset (Fin I.amalgam.card ⊕ Unit))
    (T : Set (Fin I.amalgam.card ⊕ Unit)) (o r : Fin I.amalgam.card) (β : Label.{u}) :
    Finset (Prof I) :=
  (cat I k).filter fun R ↦ lowPred K N T o r (withCut R β)

/-- **A sub-catalogue at a positive constant cutoff has no lift provision at `⊥` from a coatom
below which lie every proper donor field and some donor top**: a profile `⊥` below the coatom is
active at the cutoff, with that donor top below it. -/
theorem not_botLiftProvisionIn_lowConst {k K : ℕ} {N : Finset (Fin I.amalgam.card ⊕ Unit)}
    {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card} {β : Label.{u}}
    (hβ : β ≠ ⊥) {x : Fin (m + 2)}
    (hN : ∀ f ∈ N, ∃ z ∈ I.amalgam.toCellScheme.below (univ.erase x, k), f = Sum.inl z)
    {z₀ : Fin I.amalgam.card} (hz₀ : Sum.inl z₀ ∈ T)
    (hz₀b : z₀ ∈ I.amalgam.toCellScheme.below (univ.erase x, k)) :
    ¬ BotLiftProvisionIn (lowConstCat k K N T o r β) k x := by
  classical
  refine not_botLiftProvisionIn_of_forall fun R hR ↦ ?_
  by_contra hall
  push Not at hall
  have hlow := (Finset.mem_filter.mp hR).2
  have hdm : donorMax N (withCut R β) = ⊥ := by
    refine le_bot_iff.mp (Finset.sup_le fun f hf ↦ ?_)
    obtain ⟨z, hz, rfl⟩ := hN f hf
    exact (hall z hz).le
  have h := hlow (by rw [hdm]; exact bot_lt_iff_ne_bot.mpr hβ) _ hz₀
  have h' : withCut R β (Sum.inl z₀) = ⊥ := hall z₀ hz₀b
  rw [h'] at h
  exact hβ (le_bot_iff.mp ((le_max_left _ _).trans h))

end VaughtConjecture.ProfileTower
