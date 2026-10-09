/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateStep

/-!
# Raising above the cap

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the step for states above
the controllers); semantic contract, items 3 and 8.

The failure mode of the step for states at a grade `j ≥ K` (`ProfileTower.LowStateRaise`): a
profile `W₀` lawful on the cut, agreeing with the serving state `P` capped at a cap `h` self-visible
and short at `j`, active below the cap, with frontier `c > h`.  Every donor top of `W₀` is then at
least `h` (`ProfileTower.le_top_of_lowStateFail`: capped at `h` the frontier is that of `P`, at most
every donor top of `P`).

**Where shortness enters, and where it does not.**  In the lift of a state layer
(`ProfileTower.SLvl.Good.cappedLift_sS`) shortness is asked only of the caps `h` of the lift
(`Label.min_orbitCode_eq`, `ProfileTower.SLvl.Good.capAgree`,
`Label.min_agreementHeight_eq_of_isShort` in `ProfileTower.SLvl.Good.exists_extension_s`).  The
value `c' = R_j(c)` to which a repair raises the donor tops is not a cap of the lift; a capped lift
on faces lawful at `j` at the cap `c'` (`H2.hasCappedLifts_lawfulAt'` at the grade `j`) asks only
that `c'` be self-visible at `j`, which it is, and `c ≤ c'` keeps the frontier condition.  So the
shortness of `c'` is not an obstruction.

**The raise above the cap** (`Label.raiseAbove`, `Label.isWitness_raiseAbove`, compiled in this
repository).  For `h` and `c'` self-visible at `j`, the map fixing every label at most `h` and
sending a label above `h` to its maximum with `c'` is a witness bounded by `j`: it is monotone, and
visibility replacement at a grade `k ≤ j` keeps a label above `h` above `h`
(`Label.lt_visibilityReplace_of_lt`, from the owner lowering) and a label at most `h` at most `h`.
It agrees with the identity capped at `h`.

**The failure mode without a band** (`ProfileTower.lowStateFail_raise`, compiled in this
repository).  If no cell below the coatom carries a value of `W₀` strictly between `h` and `c'`, and
no donor top of `W₀` is exactly `h`, then `W = raiseAbove h c' ∘ W₀` repairs the failure: it is
lawful on the cut (a witness), equal to `W₀` below the coatom (the values there are at most `h` or
at least `c'`), agrees with `P` capped at `h`, its frontier is `c'` (the raise commutes with the
frontier), and every donor top, above `h`, is raised to at least `c'`.  The remaining cases of the
failure mode are a prescribed value in the band `(h, c')` (a cell below the coatom, possibly of
grade in `(K, j]`, which the repair may not move) and a donor top exactly at the cap.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Label

variable {k i j : ℕ} {h c x : Label.{u}}

/-- The **raise above the cap** `h` to `c`: every label at most `h` is kept, every label above `h`
goes to its maximum with `c`. -/
noncomputable def raiseAbove (h c : Label.{u}) (x : Label.{u}) : Label.{u} :=
  if x ≤ h then x else max x c

theorem raiseAbove_of_le (hx : x ≤ h) : raiseAbove h c x = x := ite_eq_left hx

theorem raiseAbove_of_lt (hx : h < x) : raiseAbove h c x = max x c := ite_eq_right (not_le.mpr hx)

theorem monotone_raiseAbove : Monotone (raiseAbove h c) := by
  intro x y hxy
  by_cases hy : y ≤ h
  · rw [raiseAbove_of_le (hxy.trans hy), raiseAbove_of_le hy]; exact hxy
  · rw [not_le] at hy
    rw [raiseAbove_of_lt hy]
    by_cases hx : x ≤ h
    · rw [raiseAbove_of_le hx]; exact hxy.trans (le_max_left _ _)
    · rw [raiseAbove_of_lt (not_le.mp hx)]; exact max_le_max hxy le_rfl

theorem min_raiseAbove (x : Label.{u}) : min (raiseAbove h c x) h = min x h := by
  by_cases hx : x ≤ h
  · rw [raiseAbove_of_le hx]
  · rw [not_le] at hx
    rw [raiseAbove_of_lt hx, min_eq_right (hx.le.trans (le_max_left _ _)), min_eq_right hx.le]

theorem raiseAbove_eq_bot_iff : raiseAbove h c x = ⊥ ↔ x = ⊥ := by
  constructor
  · intro hx
    by_cases hxh : x ≤ h
    · rwa [raiseAbove_of_le hxh] at hx
    · rw [raiseAbove_of_lt (not_le.mp hxh)] at hx
      exact le_bot_iff.mp ((le_max_left _ _).trans hx.le)
  · rintro rfl; exact raiseAbove_of_le bot_le

/-- **The raise above the cap is a witness bounded by `j`**, for `h` and `c` self-visible at
`j`. -/
theorem isWitness_raiseAbove (hh : IsSelfVisible j h) (hc : IsSelfVisible j c) :
    IsWitness (stepSuppressor j) (raiseAbove h c) where
  antitone := (IsWitness.id_step j).antitone
  isSelfVisible := (IsWitness.id_step j).isSelfVisible
  map_bot := raiseAbove_of_le bot_le
  monotone := monotone_raiseAbove
  visibilityReplace_comm x k hk i hi := by
    by_cases hkj : k ≤ j
    · have hhk : IsSelfVisible k h := hh.mono hkj
      have hck : IsSelfVisible k c := hc.mono hkj
      by_cases hx : x ≤ h
      · rw [raiseAbove_of_le hx, raiseAbove_of_le (visibilityReplace_le_of_le hi hhk hx)]
      · rw [not_le] at hx
        rw [raiseAbove_of_lt hx, raiseAbove_of_lt (lt_visibilityReplace_of_lt hi hhk hx),
          visibilityReplace_max hi, hck.visibilityReplace_eq i]
    · rw [stepSuppressor_of_lt (not_le.mp hkj), le_bot_iff, raiseAbove_eq_bot_iff] at hk
      rw [hk, visibilityReplace_bot, raiseAbove_of_le bot_le, visibilityReplace_bot]

end VaughtConjecture.Label

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {K j : ℕ}
  {N : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
  {o r : Fin I.amalgam.card}

/-- **In the failure mode every donor top is at least the cap.** -/
theorem le_top_of_lowStateFail {P : CProf I} (hPlow : lowPred K N T o r P) {h : Label.{u}}
    (hhK : IsSelfVisible K h) {W₀ : Prof I} (hW₀P : ∀ d, min (W₀ d) h = min (P (Sum.inl d)) h)
    (hN : Sum.inr () ∉ N) (hact : donorMax N (withCut W₀ ⊥) < min (P (Sum.inr ())) h)
    (hfh : h < Label.frontier K (Sum.inl o) (Sum.inl r) (withCut W₀ ⊥)) {y : Fin I.amalgam.card}
    (hy : Sum.inl y ∈ T) : h ≤ W₀ y := by
  have hag : ∀ f ∈ N, min (withCut W₀ ⊥ f) h = min (P f) h := by
    rintro (d | z) hf
    · exact hW₀P d
    · cases z; exact absurd hf hN
  have hMh : donorMax N (withCut W₀ ⊥) < h := hact.trans_le (min_le_right _ _)
  have hPact : donorMax N P < P (Sum.inr ()) := by
    rw [← donorMax_eq_of_min_eq hag hMh]
    exact hact.trans_le (min_le_left _ _)
  have h1 := min_frontier_le_of_isLowAt (f := withCut W₀ ⊥) hPlow hPact hhK (hW₀P o) (hW₀P r)
    (Sum.inl y) hy
  rw [min_eq_right hfh.le] at h1
  have h2 : min (W₀ y) h = h := by rw [hW₀P y]; exact min_eq_right h1
  exact h2 ▸ min_le_left _ _

/-- **The failure mode without a band is repaired by the raise above the cap**: when no value of
`W₀` below the coatom lies strictly between `h` and `c' = R_j(c)` (for the frontier `c`) and no
donor top of `W₀` is exactly `h`, the profile `raiseAbove h c' ∘ W₀` is lawful on the cut, equal to
`W₀` below the coatom, agrees with `P` capped at `h`, and reads every donor top at least at its
frontier. -/
theorem lowStateFail_raise (hKj : K ≤ j) {P : CProf I} (hPlow : lowPred K N T o r P)
    {h : Label.{u}} (hh : IsSelfVisible j h) {W₀ : Prof I} (hW₀ : IsCutLawful I j W₀)
    (hW₀P : ∀ d, min (W₀ d) h = min (P (Sum.inl d)) h) (hN : Sum.inr () ∉ N)
    (hT : ∀ y ∈ T, ∃ d, y = Sum.inl d)
    (hact : donorMax N (withCut W₀ ⊥) < min (P (Sum.inr ())) h)
    (hfh : h < Label.frontier K (Sum.inl o) (Sum.inl r) (withCut W₀ ⊥)) {x : Fin (m + 2)}
    (hband : ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j), ¬ (h < W₀ d ∧
      W₀ d < visibilityReplace j j (Label.frontier K (Sum.inl o) (Sum.inl r) (withCut W₀ ⊥))))
    (hcap : ∀ y, Sum.inl y ∈ T → W₀ y ≠ h) :
    ∃ W : Prof I, IsCutLawful I j W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j), W d = W₀ d) ∧
      (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧
      ∀ y ∈ T, Label.frontier K (Sum.inl o) (Sum.inl r) (withCut W ⊥) ≤ withCut W ⊥ y := by
  set c := Label.frontier K (Sum.inl o) (Sum.inl r) (withCut W₀ ⊥) with hc
  set c' := visibilityReplace j j c with hc'
  have hc'v : IsSelfVisible j c' := visibilityReplace_self_visibilityReplace le_rfl c
  have hcc : c ≤ c' := le_visibilityReplace (Nat.le_succ j) c
  set ρ := raiseAbove h c' with hρ
  have hρw : IsWitness (stepSuppressor j) ρ := isWitness_raiseAbove hh hc'v
  have hhK : IsSelfVisible K h := hh.mono hKj
  refine ⟨fun d ↦ ρ (W₀ d), ⟨?_, ?_⟩, fun d hd ↦ ?_, fun d ↦ ?_, fun y hy ↦ ?_⟩
  · exact hW₀.1.map_of_apply_eq_bot (fun d ↦ d.2.2) hρw fun _ ↦ raiseAbove_eq_bot_iff.mp
  · exact hW₀.2.map_of_apply_eq_bot (fun d ↦ d.2.2) hρw fun _ ↦ raiseAbove_eq_bot_iff.mp
  · by_cases hdh : W₀ d ≤ h
    · exact raiseAbove_of_le hdh
    · rw [not_le] at hdh
      have hge : c' ≤ W₀ d := not_lt.mp fun hlt ↦ hband d hd ⟨hdh, hlt⟩
      change raiseAbove h c' (W₀ d) = W₀ d
      rw [raiseAbove_of_lt hdh, max_eq_left hge]
  · change min (raiseAbove h c' (W₀ d)) h = _
    rw [min_raiseAbove]; exact hW₀P d
  · obtain ⟨y, rfl⟩ := hT y hy
    -- the frontier of the raised profile is the raise of the frontier
    have hfr : Label.frontier K (Sum.inl o) (Sum.inl r) (withCut (fun d ↦ ρ (W₀ d)) ⊥) =
        ρ c := by
      unfold Label.frontier
      change min (ρ (W₀ o)) (visibilityReplace K K (ρ (W₀ r))) =
        ρ (min (W₀ o) (visibilityReplace K K (W₀ r)))
      rw [← hρw.visibilityReplace_comm (W₀ r) K
          (by rw [stepSuppressor_of_le hKj]; exact le_top) K le_rfl,
        hρw.monotone.map_min]
    have hyh : h < W₀ y := lt_of_le_of_ne (le_top_of_lowStateFail hPlow hhK hW₀P hN hact hfh hy)
      (hcap y hy).symm
    change Label.frontier K (Sum.inl o) (Sum.inl r) (withCut (fun d ↦ ρ (W₀ d)) ⊥) ≤
      ρ (W₀ y)
    rw [hfr, hρ, raiseAbove_of_lt hfh, raiseAbove_of_lt hyh, max_eq_right hcc]
    exact le_max_right _ _

end VaughtConjecture.ProfileTower
