/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStepLow

/-!
# The LOW step for states, on the amalgam

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the layers of states
above the controllers); semantic contract, items 3, 4 and 8.

Above the controllers the LOW construction indexes the layers by **states**: profiles with a
cutoff (`ProfileTower.CProf`), the cutoff a free field.  The capped lift of a layer of states at a
grade `j` from a coatom reduces, as for `ProfileTower.Lvl.CatStep`, to a statement on the amalgam
alone; for states the catalogue is not normalized, so no orbit code of the profile is taken.

**The step for states** (`ProfileTower.StateCatStep j A x`).  At every state `P` with values in
the code grid at `j`, amalgam part lawful on the grade-`j` cut and satisfying `A`, every cap `h`
self-visible and short at `j` with `⊥ < h`, and every amalgam labelling `a` lawful below the
coatom `univ.erase x` at `j` agreeing there with `P` capped at `h`: some amalgam profile `W`
lawful on the cut, equal to `a` below the coatom and agreeing with `P` capped at `h`, and a cutoff
`β` in the code grid agreeing with that of `P` capped at `h`, with `A (withCut W β)`.

**The step on the amalgam at a positive cap** (`ProfileTower.exists_cutLawful_of_coatom_cap'`,
compiled in this repository): the amalgam form of
`ProfileTower.Lvl.Good.exists_cutLawful_of_coatom_cap`, at every grade `0 < j ≤ m`.

**The LOW step for states reduces to its failure mode** (`ProfileTower.LowStateRaise`,
`ProfileTower.stateCatStep_low_of_raise`, compiled in this repository).  For the LOW clause at `K`
(`ProfileTower.lowPred`) with designated fields amalgam cells, take the cutoff
`β = min (P cutoff) h` (in the code grid, `Label.mem_codeGrid_of_le`).  The LOW clause of
`withCut W β` follows from that of `P` (`Label.isLowAt_of_min_eq`) once the frontier condition
holds: if the donor maximum of `W` is below `min (P cutoff) h`, every donor top of `W` is at least
the frontier of `W`.  For the profile `W₀` glued from the coatom (the step on the amalgam at the
cap), this condition fails only when `W₀` is active below the cap and its frontier is above the
cap: the frontier capped at `h` is that of `P`, at most every donor top of `P` by its LOW clause
(`Label.min_frontier_le_of_isLowAt`).  `ProfileTower.LowStateRaise j x` is exactly that case:
some profile lawful on the cut, equal to `W₀` below the coatom and agreeing with `P` capped at
`h`, reads every donor top at least at its frontier.  At the grade `K` it is the tie case (from
the private coatom) and the unserved case (from the donor coatom) of the LOW step.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-! ### The step for states -/

variable (I) in
/-- **The step for states** on the amalgam from the coatom `univ.erase x` at the grade `j`, for a
predicate `A` on states: `ProfileTower.Lvl.CatStep` for the catalogue of states, which is not
normalized (see the module docstring).  Open in general. -/
def StateCatStep (j : ℕ) (A : CProf I → Prop) (x : Fin (m + 2)) : Prop :=
  ∀ P : CProf I, (∀ f, P f ∈ codeGrid j (bound I)) → IsCutLawful I j (camal P) → A P →
    ∀ h : Label.{u}, IsSelfVisible j h → IsShort j h → ⊥ < h →
    ∀ a : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase x, j) (fun d ↦ a d) →
    (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j), min (a d) h = min (P (Sum.inl d)) h) →
    ∃ (W : Prof I) (β : Label.{u}), IsCutLawful I j W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j), W d = a d) ∧
      (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧ β ∈ codeGrid j (bound I) ∧
      min β h = min (P (Sum.inr ())) h ∧ A (withCut W β)

/-- **The step on the amalgam at a positive cap**: for `0 < j ≤ m`, a profile `P` lawful on the
grade-`j` cut and a cap `h` self-visible at `j`, every amalgam labelling lawful below a coatom at
`j` and agreeing there with `P` capped at `h` extends to a profile lawful on the cut, agreeing
with `P` capped at `h`: its trace on the common face is lifted into the other coatom in the cap
ball of `P` (bountifulness of the amalgam), and the cells above the cut keep `P`. -/
theorem exists_cutLawful_of_coatom_cap' {j : ℕ} (hj0 : 0 < j) (hjm : j ≤ m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) {P : Prof I} (hP : IsCutLawful I j P)
    {h : Label.{u}} (hh : IsSelfVisible j h) {a : Prof I}
    (ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, j) fun d ↦ a d)
    (haP : ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j), min (a d) h = min (P d) h) :
    ∃ W : Prof I, IsCutLawful I j W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j), W d = a d) ∧
      ∀ d, min (W d) h = min (P d) h := by
  classical
  obtain ⟨y, hy, hxy⟩ := Seed.exists_other hx
  obtain ⟨hOf, hOcard⟩ := inter_props (I := I) hx hy hxy
  have hcard (z : Fin (m + 2)) : #(univ.erase z) = m + 1 := Seed.card_erase z
  set O : Finset (Fin (m + 2)) × ℕ := (univ.erase x ∩ univ.erase y, j) with hO
  have hOV : O ≤ (univ.erase y, j) := ⟨inter_subset_right, le_rfl⟩
  have hOU : O ≤ (univ.erase x, j) := ⟨inter_subset_left, le_rfl⟩
  have hlift : I.amalgam.rows.CappedLift hOV := I.isBountiful
    ⟨hOf, hj0, show j ≤ #(univ.erase x ∩ univ.erase y) by rw [hOcard]; omega⟩
    ⟨I.erase_mem_faces hy, hj0, show j ≤ #(univ.erase y) by rw [hcard]; omega⟩ hOV
  obtain ⟨q', hq', hq'P, hq'a⟩ := (Rows.cappedLift_iff_forall_exists hOV).mp hlift h hh
    (fun d ↦ a d) (fun d ↦ P d) (ha.mono hOU) (hP.isLawfulBelow_erase hy)
    fun d ↦ (haP d.1 (I.amalgam.toCellScheme.below_mono hOU d.2)).symm
  set W : Prof I := fun d ↦
    if hd : d ∈ I.amalgam.toCellScheme.below (univ.erase x, j) then a d
    else if hd' : d ∈ I.amalgam.toCellScheme.below (univ.erase y, j) then q' ⟨d, hd'⟩
    else P d with hW
  have hWx (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase x, j)) :
      W d = a d := dite_eq_left hd
  have hWy (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase y, j)) :
      W d = q' ⟨d, hd⟩ := by
    by_cases hdx : d ∈ I.amalgam.toCellScheme.below (univ.erase x, j)
    · rw [hWx d hdx]
      exact (hq'a ⟨d, ⟨subset_inter hdx.1 hd.1, hdx.2⟩⟩).symm
    · exact (dite_eq_right hdx).trans (dite_eq_left hd)
  have hWlx : I.amalgam.rows.IsLawfulBelow (univ.erase x, j) fun d ↦ W d :=
    (Rows.isLawfulBelow_congr fun d hd ↦ (hWx d hd).symm).mp ha
  have hWly : I.amalgam.rows.IsLawfulBelow (univ.erase y, j) fun d ↦ W d := by
    convert hq' using 1
    funext d
    exact hWy d.1 d.2
  refine ⟨W, lawful_pair hx hy hxy hWlx hWly, hWx, fun d ↦ ?_⟩
  by_cases hdx : d ∈ I.amalgam.toCellScheme.below (univ.erase x, j)
  · rw [hWx d hdx]
    exact haP d hdx
  · by_cases hdy : d ∈ I.amalgam.toCellScheme.below (univ.erase y, j)
    · rw [hWy d hdy]
      exact hq'P ⟨d, hdy⟩
    · have hWd : W d = P d := (dite_eq_right hdx).trans (dite_eq_right hdy)
      rw [hWd]

/-! ### The LOW step for states and its failure mode -/

variable (I) in
/-- **The failure mode of the LOW step for states** at the grade `j` from the coatom
`univ.erase x` (open in general): for a state `P` with values in the code grid, amalgam part lawful
on the grade-`j` cut and LOW at `K`, a cap `h` self-visible and short at `j` with `⊥ < h`, and a
profile `W₀` lawful on the cut agreeing with `P` capped at `h`, active below the cap (its donor
maximum below `min (P cutoff) h`) with frontier above the cap, some profile lawful on the cut,
equal to `W₀` below the coatom and agreeing with `P` capped at `h`, reads every donor top at least
at its frontier. -/
def LowStateRaise (K j : ℕ) (N : Finset (Fin I.amalgam.card ⊕ Unit))
    (T : Set (Fin I.amalgam.card ⊕ Unit)) (o r : Fin I.amalgam.card) (x : Fin (m + 2)) : Prop :=
  ∀ P : CProf I, (∀ f, P f ∈ codeGrid j (bound I)) → IsCutLawful I j (camal P) →
    lowPred K N T o r P → ∀ h : Label.{u}, IsSelfVisible j h → IsShort j h → ⊥ < h →
    ∀ W₀ : Prof I, IsCutLawful I j W₀ → (∀ d, min (W₀ d) h = min (P (Sum.inl d)) h) →
    donorMax N (withCut W₀ ⊥) < min (P (Sum.inr ())) h →
    h < frontier K (Sum.inl o) (Sum.inl r) (withCut W₀ ⊥) →
    ∃ W : Prof I, IsCutLawful I j W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j), W d = W₀ d) ∧
      (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧
      ∀ y ∈ T, frontier K (Sum.inl o) (Sum.inl r) (withCut W ⊥) ≤ withCut W ⊥ y

variable {K j : ℕ} {N : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
  {o r : Fin I.amalgam.card}

/-- **The LOW clause of a state from the frontier condition**: for a state `P` LOW at `K`, a cap
`h` self-visible at `K` and a profile `W` agreeing with the amalgam part of `P` capped at `h`
whose donor tops are at least its frontier whenever its donor maximum is below
`min (P cutoff) h`, the state of `W` with the cutoff `min (P cutoff) h` is LOW at `K`
(`Label.isLowAt_of_min_eq`). -/
theorem lowPred_withCut_of_frontier (hN : Sum.inr () ∉ N) (hT : Sum.inr () ∉ T) {P : CProf I}
    (hP : lowPred K N T o r P) {h : Label.{u}} {W : Prof I}
    (hWP : ∀ d, min (W d) h = min (P (Sum.inl d)) h)
    (hfr : donorMax N (withCut W ⊥) < min (P (Sum.inr ())) h →
      ∀ y ∈ T, frontier K (Sum.inl o) (Sum.inl r) (withCut W ⊥) ≤ withCut W ⊥ y) :
    lowPred K N T o r (withCut W (min (P (Sum.inr ())) h)) := by
  set u : CProf I := withCut W (min (P (Sum.inr ())) h) with hu
  have hag : ∀ f, min (u f) h = min (P f) h := by
    rintro (d | z)
    · exact hWP d
    · cases z
      change min (min (P (Sum.inr ())) h) h = _
      rw [min_assoc, min_self]
  have hNu : donorMax N u = donorMax N (withCut W ⊥) := donorMax_congr fun f hf ↦ by
    rcases f with d | z
    · rfl
    · cases z; exact absurd hf hN
  refine isLowAt_of_min_eq hP hag (min_le_right _ _) fun hact y hy ↦ ?_
  rw [hNu] at hact
  have h1 := hfr hact y hy
  rcases y with y | z
  · exact h1
  · cases z; exact absurd hy hT

/-- **The LOW step for states from its failure mode.**  For `0 < j ≤ m` and the LOW clause at
`K` with designated fields amalgam cells (`Sum.inr ()` neither a proper donor field nor a donor
top), the step for states (`ProfileTower.StateCatStep`) holds from the coatom `univ.erase x`
given its failure mode (`ProfileTower.LowStateRaise`): glue the coatom data at the cap
(`ProfileTower.exists_cutLawful_of_coatom_cap'`); off the failure mode the glued profile already
satisfies the frontier condition (inactive below the cap, or frontier at most the cap, where the
LOW clause of `P` applies); take the cutoff `min (P cutoff) h`
(`ProfileTower.lowPred_withCut_of_frontier`). -/
theorem stateCatStep_low_of_raise (hj0 : 0 < j) (hjm : j ≤ m) (hKj : K ≤ j)
    (hN : Sum.inr () ∉ N) (hT : Sum.inr () ∉ T) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) (hR : LowStateRaise I K j N T o r x) :
    StateCatStep I j (lowPred K N T o r) x := by
  intro P hPB hPC hPlow h hh hs hb a ha haP
  obtain ⟨W₀, hW₀, hW₀a, hW₀P⟩ := exists_cutLawful_of_coatom_cap' hj0 hjm hx hPC hh ha haP
  have hhK : IsSelfVisible K h := hh.mono hKj
  -- a profile with the frontier condition, equal to `a` below the coatom
  obtain ⟨W, hW, hWa, hWP, hfr⟩ : ∃ W : Prof I, IsCutLawful I j W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j), W d = a d) ∧
      (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧
      (donorMax N (withCut W ⊥) < min (P (Sum.inr ())) h →
        ∀ y ∈ T, frontier K (Sum.inl o) (Sum.inl r) (withCut W ⊥) ≤ withCut W ⊥ y) := by
    by_cases hact : donorMax N (withCut W₀ ⊥) < min (P (Sum.inr ())) h
    swap
    · exact ⟨W₀, hW₀, hW₀a, hW₀P, fun h' ↦ absurd h' hact⟩
    by_cases hfh : frontier K (Sum.inl o) (Sum.inl r) (withCut W₀ ⊥) ≤ h
    · refine ⟨W₀, hW₀, hW₀a, hW₀P, fun _ y hy ↦ ?_⟩
      -- the serving state is active and reads every donor top above its frontier
      have hag : ∀ f ∈ N, min (withCut W₀ ⊥ f) h = min (P f) h := by
        rintro (d | z) hf
        · exact hW₀P d
        · cases z; exact absurd hf hN
      have hMh : donorMax N (withCut W₀ ⊥) < h := hact.trans_le (min_le_right _ _)
      have hPact : donorMax N P < P (Sum.inr ()) := by
        rw [← donorMax_eq_of_min_eq hag hMh]
        exact hact.trans_le (min_le_left _ _)
      have hgap := min_frontier_le_of_isLowAt (f := withCut W₀ ⊥) hPlow hPact hhK (hW₀P o)
        (hW₀P r) y hy
      rw [min_eq_left hfh] at hgap
      rcases y with y | z
      · have h2 : frontier K (Sum.inl o) (Sum.inl r) (withCut W₀ ⊥) ≤ min (W₀ y) h := by
          rw [hW₀P y]; exact le_min hgap hfh
        exact h2.trans (min_le_left _ _)
      · cases z; exact absurd hy hT
    obtain ⟨W, hW, hWW₀, hWP, hfr⟩ :=
      hR P hPB hPC hPlow h hh hs hb W₀ hW₀ hW₀P hact (not_le.mp hfh)
    exact ⟨W, hW, fun d hd ↦ (hWW₀ d hd).trans (hW₀a d hd), hWP, fun _ ↦ hfr⟩
  refine ⟨W, min (P (Sum.inr ())) h, hW, hWa, hWP, ?_, by rw [min_assoc, min_self],
    lowPred_withCut_of_frontier hN hT hPlow hWP hfr⟩
  rcases le_total (P (Sum.inr ())) h with hle | hle
  · rw [min_eq_left hle]; exact hPB _
  · rw [min_eq_right hle]; exact mem_codeGrid_of_le hh hs (hPB _) hle

end VaughtConjecture.ProfileTower
