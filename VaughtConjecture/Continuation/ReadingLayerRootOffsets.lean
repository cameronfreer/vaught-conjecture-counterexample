/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerServers
import VaughtConjecture.Continuation.MarkedCarrier
import VaughtConjecture.Continuation.ApexContexts

/-!
# Root offsets below the grade of a cap: the cap keeps the proper root ties

Roadmap, Layer 3 ((R3) of the table of 3.4).

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
* **Root bottoms respected and the acquired predicates** (`StageType.RootBottomRespected`,
  `TiedRootCapRelabel.MarkedCapContextBelow`, `TiedRootCapRelabel.MarkedCapContextBelow'`,
  defined here): the row of the cap reads the root cells labelled `⊥` as `⊥`; the marked-cap
  context with root offsets below the grade of its cap, with and without that property.
* **Apex types as acquired contexts** (`StageType.markedCapContextBelow'_addApex`, compiled): an
  apex added to a type legal below the full grade, along a root of `n` points with `n + 1 < k`,
  root labels never `⊤` and root offsets below `k`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

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

/-! ### Bounded reading at a cell labelled `⊤` -/

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ}

/-- A cell visible through `h : Fin n ↪ Fin k` lies below every cell of full scope and grade at
least `n`. -/
theorem mem_below_of_mem_visibleCells {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {c y : Fin t'.card} (hc : t'.toCellScheme.scope c = univ)
    (hn : n ≤ t'.toCellScheme.grade c) (hy : y ∈ t'.visibleCells h) :
    y ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex c) := by
  rw [CellScheme.mem_below]
  refine Prod.mk_le_mk.mpr ⟨by rw [hc]; exact subset_univ _, ?_⟩
  have hsub : t'.toCellScheme.scope y ⊆ univ.map h := (mem_filter.mp hy).2
  calc t'.toCellScheme.grade y ≤ #(t'.toCellScheme.scope y) :=
        t'.isWellFormed.isWellFormed.grade_le_card y
    _ ≤ #(univ.map h) := card_le_card hsub
    _ = n := by simp
    _ ≤ _ := hn


/-- **Bounded reading at a cell labelled `⊤`.**  If a lawful labelling `a` of `t'` is `⊤` at `c`,
the shifter of its locality at `c` is a reading map bounded at the grade of `c` that reads the row
of `c` as `a` below `c`: the suppressor is `⊤` at the grade of `c` (evaluate at `c`), hence at
every smaller grade. -/
theorem exists_isBoundedReading {t' : StageType.{u} α k} {a : Fin t'.card → Label.{u}}
    (ha : t'.rows.IsLawful a) {c : Fin t'.card} (hc : a c = ⊤) :
    ∃ σ, IsBoundedReading (t'.toCellScheme.grade c) σ ∧
      ∀ d ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex c), a d = σ (t'.rowAt c d) := by
  obtain ⟨g, σ, hw, heq⟩ := ha.locality c
  have hcc := heq ⟨c, t'.toCellScheme.mem_below_gradedIndex c⟩
  change min (a c) (a c) = min (σ (t'.rows.row c ⟨c, _⟩)) (g (t'.toCellScheme.grade c)) at hcc
  rw [hc, min_self] at hcc
  have hgN : g (t'.toCellScheme.grade c) = ⊤ := (min_eq_top.mp hcc.symm).2
  have hg {j : ℕ} (hj : j ≤ t'.toCellScheme.grade c) : g j = ⊤ :=
    top_le_iff.mp (hgN ▸ hw.antitone hj)
  refine ⟨σ, ⟨hw.map_bot, hw.monotone, fun x j i hj hi ↦
    hw.visibilityReplace_comm x j (by rw [hg hj]; exact le_top) i hi⟩, fun d hd ↦ ?_⟩
  have h := heq ⟨d, hd⟩
  change min (a d) (a c) = min (σ (t'.rows.row c ⟨d, hd⟩)) (g (t'.toCellScheme.grade d)) at h
  have hgd : t'.toCellScheme.grade d ≤ t'.toCellScheme.grade c := by
    rw [CellScheme.mem_below] at hd
    exact hd.2
  rw [hc, min_top_right, hg hgd, min_top_right] at h
  rw [h, Scheme.rowAt_of_mem hd]

/-! ### Proper root ties -/

/-- The row of `c` **keeps the proper root ties** along `h`: at two cells visible through `h` with
labels in order, the first strictly below the second or an ordinal, the row of `c` reads them in
the same order. -/
def KeepsProperRootTies (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (c : Fin t'.card) : Prop :=
  ∀ y₁ ∈ t'.visibleCells h, ∀ y₂ ∈ t'.visibleCells h, t'.label y₁ ≤ t'.label y₂ →
    (t'.label y₁ < t'.label y₂ ∨ IsProper (t'.label y₁)) → t'.rowAt c y₁ ≤ t'.rowAt c y₂

/-- **A cap labelled `⊤` keeps the proper root ties when the root offsets lie below its grade.**
The labels below the cap are a bounded reading of its row: strict label order gives strict row
order (monotonicity), and equal ordinal labels with offset below the grade give equal row entries
(strip uniqueness, `Label.IsBoundedReading.eq_of_eq`; the rows are coded, so not `⊤`). -/
theorem keepsProperRootTies_of_rootOffsetsBelow {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {c : Fin t'.card} (hc : t'.label c = ⊤) (hcs : t'.toCellScheme.scope c = univ)
    (hn : n ≤ t'.toCellScheme.grade c) (hoff : t'.RootOffsetsBelow h (t'.toCellScheme.grade c)) :
    t'.KeepsProperRootTies h c := by
  obtain ⟨σ, hσ, hread⟩ := exists_isBoundedReading t'.isLawful hc
  have hpos : 0 < t'.toCellScheme.grade c := t'.isWellFormed.isWellFormed.grade_pos c
  intro y₁ hy₁ y₂ hy₂ hle hcase
  have hb₁ := mem_below_of_mem_visibleCells hcs hn hy₁
  have hb₂ := mem_below_of_mem_visibleCells hcs hn hy₂
  have hl₁ := hread y₁ hb₁
  have hl₂ := hread y₂ hb₂
  -- strict label order gives the row order
  have hstrict (hlt : t'.label y₁ < t'.label y₂) : t'.rowAt c y₁ ≤ t'.rowAt c y₂ := by
    by_contra hnot
    have := hσ.monotone (not_le.mp hnot).le
    rw [← hl₁, ← hl₂] at this
    exact absurd hlt (not_lt.mpr this)
  rcases hcase with hlt | hprop
  · exact hstrict hlt
  rcases hle.lt_or_eq with hlt | heq
  · exact hstrict hlt
  -- equal ordinal labels: strip uniqueness
  obtain ⟨o, ho⟩ := hprop
  obtain ⟨μ, hμ, f, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o
  have hf := hoff y₁ hy₁ μ f hμ ho.symm
  have hcode (y : Fin t'.card) (hy : y ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex c)) :
      t'.rowAt c y ≠ ⊤ := fun htop ↦ by
    have := t'.isCoded c ⟨y, hy⟩
    rw [← Scheme.rowAt_of_mem hy, htop] at this
    exact absurd this (not_lt.mpr le_top)
  refine (hσ.eq_of_eq hpos (hcode y₁ hb₁) (hcode y₂ hb₂) hμ hf ?_ ?_).le
  · rw [← hl₁, ← ho]
  · rw [← hl₂, ← heq, ← ho]

end StageType

namespace TiedRootCapRelabel

open StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- The **acquired marked-cap context** along `h`: a marked-cap context with top cap `c` and
marker `r` whose root offsets lie below the grade of `c`. -/
def MarkedCapContextBelow (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) : Prop :=
  ∃ c r, t'.IsMarkedCapContextAt h c r ∧ t'.RootOffsetsBelow h (t'.toCellScheme.grade c)

end TiedRootCapRelabel

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ}

end StageType

end VaughtConjecture
