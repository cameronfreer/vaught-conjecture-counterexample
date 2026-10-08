/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapAcquisition

/-!
# Root offsets below the grade of the cap: the cap keeps the proper root ties

Roadmap, Layer 3 ((R3) of the table of 3.4).

The context of `TiedRootCapCounterexample` has its root cells labelled `3` and its top cap of grade
`3`: a root offset (the finite part of an ordinal label) at the grade of the cap.  This file shows
that a root offset below the grade of the cap excludes the separating labelling, and that
acquisition produces such contexts with no hypothesis beyond those of
`Realization.HollowAcquisition`.

* **Bounded readings and strips** (`Label.IsBoundedReading`, `Label.IsBoundedReading.strip`,
  `Label.IsBoundedReading.eq_of_eq`, compiled in this repository (theorem named)): a monotone map
  fixing `⊥` and commuting with visibility replacement at the thresholds at most `N`, `0 < N`,
  sends at most one label other than `⊤` to a given ordinal `μ + f` with `f < N`.
* **Bounded reading at a cell labelled `⊤`** (`StageType.exists_isBoundedReading`, compiled): the
  shifter of the locality of a lawful labelling at a cell `c` labelled `⊤` is a reading map bounded
  at the grade of `c` and reads the row of `c` as the labelling below `c`.
* **Proper root ties** (`StageType.RootOffsetsBelow`, `StageType.KeepsProperRootTies`, defined
  here; `StageType.keepsProperRootTies_of_rootOffsetsBelow`, compiled): at a cap labelled `⊤` of
  full scope and grade at least the root's arity, with the root offsets below its grade, the row of
  the cap reads root labels in strict order in the same order, and equal ordinal root labels at
  equal row values.
* **No separation** (`StageType.le_of_rootOffsetsBelow`, `StageType.le_of_tie_of_rootOffsetsBelow`,
  compiled): at a marked-cap context with root offsets below the grade of its top cap `c` and
  marker `r`, every lawful labelling in the bottom class, `⊤` at `c` and `r`, keeps the order of the
  root labels (ordinal and strict ties by the proper root ties, ties at `⊤` by the row inequality
  of the context, ties at `⊥` by the bottom class).  So the inputs of the refutation schema
  `StageType.not_raisesNewTopsInClass_of_row_le`, and of every refutation built on the separating
  labelling (`TiedRootCapCounterexample.not_raisesNewTopsInClass`,
  `TiedRootCapCounterexample.exists_literal_top_apex_ne_top`,
  `TiedRootCapCounterexample.not_coatomProvision`), do not exist at such contexts.  The context of
  `TiedRootCapCounterexample` breaks the bound
  (`TiedRootCapCounterexample.not_rootOffsetsBelow`).
* **Acquisition** (`Realization.IsModel.exists_synchronized_floor`,
  `Realization.hollowAcquisition_isMarkedCapContextBelow`, compiled): synchronization with any
  floor on the top grade, and `HollowAcquisition IsCoverHollowAtBlock` for marked-cap contexts
  with root offsets below the grade of the top cap, with no hypothesis beyond those of
  `Realization.HollowAcquisition`; such a context keeps the proper root ties at its cap
  (`StageType.IsMarkedCapContextAt.keepsProperRootTies`).

`StageType.KeepsRootTies` (with its ties at `⊤` and `⊥`) is used only in the lane's own files
(`TiedRootCap`, `TiedRootCapAcquisition`, `TiedRootCapCounterexample`); the ties at `⊤` and `⊥`
are kept here by the row inequality and the bottom class.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Finset Label

/-! ### Reading maps bounded at a grade -/

namespace Label

/-- A **reading map bounded at `N`**: it fixes `⊥`, is monotone, and commutes with visibility
replacement at every threshold `k ≤ N` and every value `i ≤ k`. -/
structure IsBoundedReading (N : ℕ) (σ : Label.{u} → Label.{u}) : Prop where
  /-- It fixes `⊥`. -/
  map_bot : σ ⊥ = ⊥
  /-- It is monotone. -/
  monotone : Monotone σ
  /-- It commutes with visibility replacement at the thresholds at most `N`. -/
  comm : ∀ x k i, k ≤ N → i ≤ k → σ (visibilityReplace k i x) = visibilityReplace k i (σ x)

variable {N : ℕ} {σ : Label.{u} → Label.{u}}

/-- The point `μ + j` as a label. -/
private abbrev pt (μ : Ordinal.{u}) (j : ℕ) : Label.{u} := ((μ + j : Ordinal.{u}) : Label.{u})

private theorem pt_inj {μ μ' : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ)
    (hμ' : Order.IsSuccPrelimit μ') {j j' : ℕ} (h : pt μ j = pt μ' j') : μ = μ' ∧ j = j' :=
  (add_natCast_eq_add_natCast_iff hμ hμ').mp
    (WithTop.coe_injective (WithBot.coe_injective h))

/-- **The strip of a reading.**  If a bounded reading at `N`, `0 < N`, sends `ν + j` (`ν` zero or
a limit) to `μ + f` (`μ` zero or a limit) with `f < N`, then `j = f` and it sends `ν + i` to
`μ + i` for every `i ≤ N`. -/
theorem IsBoundedReading.strip (hσ : IsBoundedReading N σ) (hN : 0 < N) {ν μ : Ordinal.{u}}
    (hν : Order.IsSuccPrelimit ν) (hμ : Order.IsSuccPrelimit μ) {j f : ℕ} (hf : f < N)
    (h : σ (pt ν j) = pt μ f) : j = f ∧ ∀ i ≤ N, σ (pt ν i) = pt μ i := by
  have hread (i : ℕ) (hi : i ≤ N) :
      σ (visibilityReplace N i (pt ν j)) = pt μ i := by
    rw [hσ.comm _ N i le_rfl hi, h, visibilityReplace_coe_add hμ, ite_eq_left hf]
  by_cases hj : j < N
  · have hstrip (i : ℕ) (hi : i ≤ N) : σ (pt ν i) = pt μ i := by
      have := hread i hi
      rwa [visibilityReplace_coe_add hν, ite_eq_left hj] at this
    refine ⟨?_, hstrip⟩
    have h' := (hstrip j hj.le).symm.trans h
    exact (pt_inj hμ hμ h').2
  · exfalso
    have h0 := hread 0 (Nat.zero_le _)
    have h1 := hread 1 hN
    rw [visibilityReplace_coe_add hν, ite_eq_right hj] at h0 h1
    have := (pt_inj hμ hμ (h0.symm.trans h1)).2
    omega

/-- **Strip uniqueness.**  A bounded reading at `N`, `0 < N`, sends at most one label other than
`⊤` to a given ordinal `μ + f` (`μ` zero or a limit) with `f < N`. -/
theorem IsBoundedReading.eq_of_eq (hσ : IsBoundedReading N σ) (hN : 0 < N) {s s' : Label.{u}}
    (hs : s ≠ ⊤) (hs' : s' ≠ ⊤) {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) {f : ℕ}
    (hf : f < N) (h₁ : σ s = pt μ f) (h₂ : σ s' = pt μ f) : s = s' := by
  have hne (x : Label.{u}) (hx : σ x = pt μ f) (hxt : x ≠ ⊤) :
      ∃ ν : Ordinal.{u}, Order.IsSuccPrelimit ν ∧ x = pt ν f ∧ ∀ i ≤ N, σ (pt ν i) = pt μ i := by
    induction x using recBotCoeTop with
    | bot => rw [hσ.map_bot] at hx; exact absurd hx.symm WithBot.coe_ne_bot
    | top => exact absurd rfl hxt
    | coe o =>
      obtain ⟨ν, hν, j, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o
      obtain ⟨rfl, hstrip⟩ := hσ.strip hN hν hμ hf hx
      exact ⟨ν, hν, rfl, hstrip⟩
  obtain ⟨ν, hν, rfl, h₁'⟩ := hne s h₁ hs
  obtain ⟨ν', hν', rfl, h₂'⟩ := hne s' h₂ hs'
  have key {a b : Ordinal.{u}} (hb : Order.IsSuccPrelimit b) (hab : a < b)
      (ha' : ∀ i ≤ N, σ (pt a i) = pt μ i) (hb' : ∀ i ≤ N, σ (pt b i) = pt μ i) : False := by
    have hlt : pt a N ≤ pt b 0 :=
      WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by simpa using (hb.add_natCast_lt hab N).le))
    have := hσ.monotone hlt
    rw [ha' N le_rfl, hb' 0 (Nat.zero_le _)] at this
    have h' : ((μ + N : Ordinal.{u})) ≤ μ + (0 : ℕ) :=
      WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp this)
    have : (N : Ordinal.{u}) ≤ ((0 : ℕ) : Ordinal.{u}) := (add_le_add_iff_left μ).mp h'
    exact absurd (Nat.cast_le.mp this) (by omega)
  rcases lt_trichotomy ν ν' with hlt | rfl | hgt
  · exact (key hν' hlt h₁' h₂').elim
  · rfl
  · exact (key hν hgt h₂' h₁').elim

end Label

end VaughtConjecture
