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

/-! ### Bounded reading at a cell labelled `⊤` -/

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ}

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

/-- The **root offsets lie below `N`** along `h`: every label of a cell visible through `h` that
is an ordinal `μ + f` (`μ` zero or a limit) has `f < N`. -/
def RootOffsetsBelow (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (N : ℕ) : Prop :=
  ∀ y ∈ t'.visibleCells h, ∀ (μ : Ordinal.{u}) (f : ℕ), Order.IsSuccPrelimit μ →
    t'.label y = ((μ + f : Ordinal.{u}) : Label.{u}) → f < N

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

/-- **No separation at offsets below the cap.**  At a marked-cap context along `h` with top cap
`c` and marker `r` whose root offsets lie below the grade of `c`, every lawful labelling `a` of
`t'` in the bottom class of `t'`, `⊤` at `c` and at `r`, keeps the order of the root labels:
ordinal and strict ties by the proper root ties, ties at `⊤` by the row inequality of the context
(the marker is read at `⊤`), ties at `⊥` by the bottom class. -/
theorem le_of_rootOffsetsBelow {t' : StageType.{u} α k} {h : Fin n ↪ Fin k} {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt h c r)
    (hoff : t'.RootOffsetsBelow h (t'.toCellScheme.grade c)) {a : Fin t'.card → Label.{u}}
    (ha : t'.rows.IsLawful a) (hac : a c = ⊤) (har : a r = ⊤)
    (hcl : ∀ z, a z = ⊥ ↔ t'.label z = ⊥) {y₁ y₂ : Fin t'.card} (hy₁ : y₁ ∈ t'.visibleCells h)
    (hy₂ : y₂ ∈ t'.visibleCells h) (hl : t'.label y₁ ≤ t'.label y₂) : a y₁ ≤ a y₂ := by
  obtain ⟨⟨hcs, hct, -⟩, ⟨-, hrb, -⟩, hn, hmark⟩ := hctx
  obtain ⟨σ, hσ, hread⟩ := exists_isBoundedReading ha hac
  have hkeep := keepsProperRootTies_of_rootOffsetsBelow hct hcs (by omega) hoff
  have hb₁ := mem_below_of_mem_visibleCells hcs (by omega) hy₁
  have hb₂ := mem_below_of_mem_visibleCells hcs (by omega) hy₂
  by_cases hb : t'.label y₁ = ⊥
  · rw [(hcl y₁).mpr hb]
    exact bot_le
  by_cases ht : t'.label y₁ = ⊤
  · -- both are `⊤`: the marker inequality
    have ht₂ : t'.label y₂ = ⊤ := top_le_iff.mp (ht ▸ hl)
    have hm := hσ.monotone (hmark y₂ hy₂ ht₂)
    rw [hσ.comm _ _ _ le_rfl (by omega), ← hread r hrb, har, visibilityReplace_top,
      ← hread y₂ hb₂] at hm
    rw [top_le_iff.mp hm]
    exact le_top
  · rw [hread y₁ hb₁, hread y₂ hb₂]
    exact hσ.monotone (hkeep y₁ hy₁ y₂ hy₂ hl (.inr (isProper_iff_ne.mpr ⟨hb, ht⟩)))

/-- **The refutation schema has no input at offsets below the cap.**  Over a marked-cap context
`t'` along `h` with top cap `c`, marker `r` and root offsets below the grade of `c`, let a new top
`j` of a donor `d` read the root cell `y₁` at most as the root cell `y₂`, of grade at most that of
`y₁`.  Every lawful labelling of `t'` in the bottom class of `t'`, `⊤` at `c` and `r`, labels `y₁`
at most as `y₂`.  So the inputs of `StageType.not_raisesNewTopsInClass_of_row_le` (and of the
refutations built on the separating labelling) do not exist at such contexts. -/
theorem le_of_tie_of_rootOffsetsBelow {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} (ht : restrictFace h t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : restrictFace Fin.castSuccEmb d = some t) {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt h c r)
    (hoff : t'.RootOffsetsBelow h (t'.toCellScheme.grade c)) {a : Fin t'.card → Label.{u}}
    (ha : t'.rows.IsLawful a) (hac : a c = ⊤) (har : a r = ⊤)
    (hcl : ∀ z, a z = ⊥ ↔ t'.label z = ⊥) {j : Fin d.card} (hjt : d.label j = ⊤)
    {y₁ y₂ : Fin t.card}
    (hy₁ : faceCell hd y₁ ∈ d.toCellScheme.below (d.toCellScheme.gradedIndex j))
    (hy₂ : faceCell hd y₂ ∈ d.toCellScheme.below (d.toCellScheme.gradedIndex j))
    (hrow : d.rows.row j ⟨_, hy₁⟩ ≤ d.rows.row j ⟨_, hy₂⟩)
    (hg : t.toCellScheme.grade y₂ ≤ t.toCellScheme.grade y₁) :
    a (faceCell ht y₁) ≤ a (faceCell ht y₂) := by
  have hloc := (d.isLawful.locality j).le_of_le (d := ⟨_, hy₁⟩) (d' := ⟨_, hy₂⟩) hrow
    (by rw [grade_faceCell, grade_faceCell]; exact hg)
  change min (d.label (faceCell hd y₁)) (d.label j) ≤
    min (d.label (faceCell hd y₂)) (d.label j) at hloc
  rw [hjt, min_top_right, min_top_right, label_faceCell, label_faceCell] at hloc
  exact le_of_rootOffsetsBelow hctx hoff ha hac har hcl (faceCell_mem_visibleCells ht y₁)
    (faceCell_mem_visibleCells ht y₂) (by rwa [label_faceCell, label_faceCell])

end StageType

/-! ### The context with separated tied root cells breaks the offset bound -/

namespace TiedRootCapCounterexample

open StageType

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- **The context of `TiedRootCapCounterexample` has a root offset at the grade of its cap**: its
root cells are labelled `3` and its cap has grade `3`; otherwise the separating labelling (in the
bottom class, `⊤` at the cap and marker) would keep the tie of the root cells
(`StageType.le_of_rootOffsetsBelow`). -/
theorem not_rootOffsetsBelow :
    ¬ (context hα).RootOffsetsBelow rootEmb ((context hα).toCellScheme.grade (capCell hα)) := by
  intro hoff
  have h := le_of_rootOffsetsBelow (isMarkedCapContextAt_context hα) hoff (isLawful_separating hα)
    (separating_capCell hα) (separating_capCell hα) (separating_eq_bot_iff hα)
    (faceCell_mem_visibleCells (restrictFace_context hα) (⟨1, by decide⟩ : Fin 2))
    (faceCell_mem_visibleCells (restrictFace_context hα) (⟨0, by decide⟩ : Fin 2))
    ((context_label_root hα _).trans (context_label_root hα _).symm).le
  rw [separating_root, separating_root] at h
  exact absurd (natCast_label_le.mp h) (by decide)

end TiedRootCapCounterexample

/-! ### Acquisition with the root offsets below the grade of the cap -/

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ}

/-- A marked-cap context whose root offsets lie below the grade of its top cap keeps the proper
root ties at that cap. -/
theorem IsMarkedCapContextAt.keepsProperRootTies {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt h c r)
    (hoff : t'.RootOffsetsBelow h (t'.toCellScheme.grade c)) : t'.KeepsProperRootTies h c :=
  keepsProperRootTies_of_rootOffsetsBelow hctx.1.2.1 hctx.1.1 (by have := hctx.2.2.1; omega) hoff

/-- **A bound on the offsets of finitely many labels**: some `K` exceeds the offset `f` of every
label `μ + f` (`μ` zero or a limit) among the labels of a stage type. -/
theorem exists_offset_bound (t : StageType.{u} α n) :
    ∃ K : ℕ, ∀ d (μ : Ordinal.{u}) (f : ℕ), Order.IsSuccPrelimit μ →
      t.label d = ((μ + f : Ordinal.{u}) : Label.{u}) → f ≤ K := by
  classical
  have hd (d : Fin t.card) : ∃ K : ℕ, ∀ (μ : Ordinal.{u}) (f : ℕ), Order.IsSuccPrelimit μ →
      t.label d = ((μ + f : Ordinal.{u}) : Label.{u}) → f ≤ K := by
    by_cases hx : ∃ o : Ordinal.{u}, t.label d = o
    · obtain ⟨o, ho⟩ := hx
      obtain ⟨μ₀, hμ₀, j, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o
      refine ⟨j, fun μ f hμ hf ↦ ?_⟩
      have h := ho.symm.trans hf
      exact ((add_natCast_eq_add_natCast_iff hμ₀ hμ).mp
        (WithTop.coe_injective (WithBot.coe_injective h))).2.ge
    · exact ⟨0, fun μ f _ hf ↦ absurd ⟨_, hf⟩ hx⟩
  choose K hK using hd
  exact ⟨univ.sup K, fun d μ f hμ hf ↦ (hK d μ f hμ hf).trans (le_sup (mem_univ d))⟩

end StageType

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- **Synchronization with a floor on the top grade**: as `Realization.IsModel.exists_synchronized`,
with the top grade of `Z` moreover above a given `K` (unbounded growth gives an occurrence of top
grade above `K`, and covering one containing it and `y`). -/
theorem IsModel.exists_synchronized_floor (hR : R.IsModel) (hhol : R.IsCoverHollow)
    (htop : R.topGradeSup = ⊤) (K : ℕ) (x y : R.Occurrence) {f : Fin x.arity ↪ Fin y.arity}
    (hf : f.trans y.tuple = x.tuple) :
    ∃ (Z : R.Occurrence) (gy : Fin y.arity ↪ Fin Z.arity), gy.trans Z.tuple = y.tuple ∧
      y.arity + 1 < Z.type.topGrade ∧ K < Z.type.topGrade ∧ ∀ cc r, Z.type.IsTopCap cc →
        Z.type.IsMarker cc r → ∀ a ∈ Z.type.visibleCells (f.trans gy), Z.type.label a = ⊤ →
          visibilityReplace (Z.type.toCellScheme.grade cc) (x.arity + 1) (Z.type.rowAt cc r) ≤
            Z.type.rowAt cc a := by
  classical
  -- an occurrence of top grade above `K`, and one containing it and `y`
  obtain ⟨w, hw⟩ : ∃ w : R.Occurrence, K < w.type.topGrade := by
    have hlt : ((K : ℕ) : ℕ∞) < R.topGradeSup := htop ▸ ENat.natCast_lt_top _
    obtain ⟨w, hw⟩ := lt_iSup_iff.mp hlt
    exact ⟨w, by exact_mod_cast hw⟩
  obtain ⟨Y, hY⟩ := hR.isCovering.exists_subset_support (y.support ∪ w.support)
  have hyY : y ≤ Y := subset_union_left.trans hY
  have hwY : w ≤ Y := subset_union_right.trans hY
  obtain ⟨gY, hgY, -⟩ := (Occurrence.le_iff_exists_restrictFace hR.isConsistent).mp hyY
  have hfY : (f.trans gY).trans Y.tuple = x.tuple := by
    rw [Function.Embedding.trans_assoc, hgY, hf]
  obtain ⟨Z, gZ, hgZ, hNZ, hineq⟩ := hR.exists_synchronized hhol htop x Y hfY
  have hYZ : Y ≤ Z := (Occurrence.le_iff_exists_restrictFace hR.isConsistent).mpr
    ⟨gZ, hgZ, Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent hgZ⟩
  have hyar : y.arity ≤ Y.arity := by simpa using Fintype.card_le_of_embedding gY
  refine ⟨Z, gY.trans gZ, ?_, by omega,
    hw.trans_le ((Occurrence.topGrade_mono hR.isConsistent hwY).trans
      (Occurrence.topGrade_mono hR.isConsistent hYZ)), fun cc r hcc hr a ha hat ↦ ?_⟩
  · rw [Function.Embedding.trans_assoc, hgZ, hgY]
  · exact hineq cc r hcc hr a (by rwa [Function.Embedding.trans_assoc]) hat

/-- **Acquisition of marked-cap contexts with the root offsets below the grade of the cap**, with
no hypothesis beyond those of `Realization.HollowAcquisition`: synchronization with a floor above
every offset of the root's labels (`Realization.IsModel.exists_synchronized_floor`); the cells of
the context visible through the root carry the root's labels. -/
theorem hollowAcquisition_isMarkedCapContextBelow :
    HollowAcquisition.{u, w} IsCoverHollowAtBlock fun t' h ↦
      ∃ c r, t'.IsMarkedCapContextAt h c r ∧ t'.RootOffsetsBelow h (t'.toCellScheme.grade c) where
  exists_context α M R hα hR hH htop n t c hc := by
    obtain ⟨ξ, rfl, hhol⟩ := hH
    set x : R.Occurrence := ⟨n, ⟨c, hc.injective⟩, t, hc.eval_eq⟩
    obtain ⟨K, hK⟩ := StageType.exists_offset_bound t
    obtain ⟨Z, gy, hgy, hNZ, hKZ, hineq⟩ := hR.exists_synchronized_floor hhol htop K x x
      (f := Function.Embedding.refl _) (Function.Embedding.refl_trans _)
    have hnt : ¬ Z.type.IsTopFree := fun htf ↦ by
      rw [← StageType.topGrade_eq_zero_iff] at htf
      omega
    obtain ⟨cc, hcc⟩ := StageType.exists_isTopCap (hR.isLegal _ _ Z.eval_tuple) hnt
    obtain ⟨r, hr⟩ := StageType.exists_isMarker hcc.2.1
    have hfZ : ((Function.Embedding.refl _).trans gy).trans Z.tuple = x.tuple := by
      rw [Function.Embedding.trans_assoc, hgy]
      rfl
    have htZ := Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent hfZ
    refine ⟨Z.arity, Z.type, Z.tuple, (Function.Embedding.refl _).trans gy,
      covers_of_eval _ Z.eval_tuple, ?_, cc, r, ⟨hcc, hr, ?_, hineq cc r hcc hr⟩, ?_⟩
    · funext i
      exact DFunLike.congr_fun hgy i
    · rw [hcc.grade_eq_topGrade]
      exact hNZ
    · intro y hy μ f hμ hf
      obtain ⟨z, rfl⟩ := StageType.exists_faceCell_eq htZ hy
      rw [StageType.label_faceCell] at hf
      rw [hcc.grade_eq_topGrade]
      exact (hK z μ f hμ hf).trans_lt hKZ

end Realization

end VaughtConjecture
