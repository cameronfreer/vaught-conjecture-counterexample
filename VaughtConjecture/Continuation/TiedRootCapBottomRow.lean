/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapBottom

/-!
# The cap reading the root cells labelled `⊥` as `⊥`

Roadmap, Layer 3 ((R3) of the table of 3.4).

At an acquired marked-cap context (`TiedRootCapRelabel.MarkedCapContextBelow`) the ordinal root
ties and the ties at `⊤` (at labellings `⊤` at the marker) are kept by every lawful labelling `⊤`
at the cap; the ties at `⊥` are not (`BottomRootCounterexample.not_coatomProvision`).  This file
adds the property of the cap that keeps them.

* **Root bottoms respected** (`StageType.RootBottomRespected t' h c`, defined here): the row of `c`
  reads every root cell labelled `⊥` as `⊥`.
* **No separation without the bottom class**
  (`StageType.le_of_rootOffsetsBelow_of_rootBottomRespected`, compiled in this repository (theorem
  named)): at a marked-cap context with root offsets below the grade of its top cap `c`, marker
  `r`, and root bottoms respected, every lawful labelling `⊤` at `c` and `r` keeps the order of the
  root labels; the ties at `⊥` are kept by the row (a cell read as `⊥` by a cell labelled `⊤` is
  `⊥`), with no class hypothesis.
* **The predicate** (`TiedRootCapRelabel.MarkedCapContextBelow'`, defined here), with
  `MarkedCapContextBelow'.not_surjective` and `MarkedCapContextBelow'.reindex` (compiled).
* **The context with root cells labelled `⊥` breaks it**
  (`BottomRootCounterexample.not_rootBottomRespected`,
  `BottomRootCounterexample.not_markedCapContextBelow'`, compiled): its cap reads them as `1` and
  `2`.  So the input of `BottomRootCounterexample.not_coatomProvision` is absent at contexts in
  the predicate.

**Acquisition of the property** is not compiled.  The bottom-pattern clause of
`Realization.IsModel` realizes one-point cofaces with a prescribed bottom pattern at the cells of
grade at most the arity; it does not constrain the rows of the cap of an occurrence, and legality
does not give the property (the context of `BottomRootCounterexample` is legal and acquired in the
sense of `TiedRootCapRelabel.MarkedCapContextBelow`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- The row of `c` **respects the root bottoms** along `h`: it reads every cell visible through
`h` labelled `⊥` as `⊥`. -/
def RootBottomRespected (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (c : Fin t'.card) : Prop :=
  ∀ y ∈ t'.visibleCells h, t'.label y = ⊥ → t'.rowAt c y = ⊥

/-- **No separation without the bottom class.**  At a marked-cap context along `h` with top cap
`c` and marker `r`, root offsets below the grade of `c`, and a row of `c` respecting the root
bottoms, every lawful labelling `a` of `t'` that is `⊤` at `c` and `r` keeps the order of the root
labels: the ties at `⊥` are kept by the row (a cell read as `⊥` by a cell labelled `⊤` is `⊥`). -/
theorem le_of_rootOffsetsBelow_of_rootBottomRespected {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt h c r)
    (hoff : t'.RootOffsetsBelow h (t'.toCellScheme.grade c))
    (hbot : t'.RootBottomRespected h c) {a : Fin t'.card → Label.{u}}
    (ha : t'.rows.IsLawful a) (hac : a c = ⊤) (har : a r = ⊤) {y₁ y₂ : Fin t'.card}
    (hy₁ : y₁ ∈ t'.visibleCells h) (hy₂ : y₂ ∈ t'.visibleCells h)
    (hl : t'.label y₁ ≤ t'.label y₂) : a y₁ ≤ a y₂ := by
  obtain ⟨⟨hcs, hct, -⟩, ⟨-, hrb, -⟩, hn, hmark⟩ := hctx
  obtain ⟨σ, hσ, hread⟩ := exists_isBoundedReading ha hac
  have hkeep := keepsProperRootTies_of_rootOffsetsBelow hct hcs (by omega) hoff
  have hb₁ := mem_below_of_mem_visibleCells hcs (by omega) hy₁
  have hb₂ := mem_below_of_mem_visibleCells hcs (by omega) hy₂
  by_cases hb : t'.label y₁ = ⊥
  · rw [hread y₁ hb₁, hbot y₁ hy₁ hb, hσ.map_bot]
    exact bot_le
  by_cases ht : t'.label y₁ = ⊤
  · have ht₂ : t'.label y₂ = ⊤ := top_le_iff.mp (ht ▸ hl)
    have hm := hσ.monotone (hmark y₂ hy₂ ht₂)
    rw [hσ.comm _ _ _ le_rfl (by omega), ← hread r hrb, har, visibilityReplace_top,
      ← hread y₂ hb₂] at hm
    rw [top_le_iff.mp hm]
    exact le_top
  · rw [hread y₁ hb₁, hread y₂ hb₂]
    exact hσ.monotone (hkeep y₁ hy₁ y₂ hy₂ hl (.inr (isProper_iff_ne.mpr ⟨hb, ht⟩)))

end StageType

namespace TiedRootCapRelabel

open StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- The **acquired marked-cap context with the root bottoms respected**: a marked-cap context
with top cap `c` and marker `r`, root offsets below the grade of `c`, and the row of `c` reading
the root cells labelled `⊥` as `⊥`. -/
def MarkedCapContextBelow' (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) : Prop :=
  ∃ c r, t'.IsMarkedCapContextAt h c r ∧ t'.RootOffsetsBelow h (t'.toCellScheme.grade c) ∧
    t'.RootBottomRespected h c

theorem MarkedCapContextBelow'.markedCapContextBelow {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} (ht : MarkedCapContextBelow' t' h) : MarkedCapContextBelow t' h :=
  let ⟨c, r, hc, ho, _⟩ := ht
  ⟨c, r, hc, ho⟩

theorem MarkedCapContextBelow'.not_surjective {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    (ht : MarkedCapContextBelow' t' h) : ¬ Function.Surjective h :=
  ht.markedCapContextBelow.not_surjective

/-- **Invariance under relabelling**: the top cap, the marker and the root correspond through the
cell map of `σ`, with their labels and rows. -/
theorem MarkedCapContextBelow'.reindex {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    (ht : MarkedCapContextBelow' t' h) (σ : Equiv.Perm (Fin k)) :
    MarkedCapContextBelow' (t'.reindex σ) (h.trans σ.symm.toEmbedding) := by
  obtain ⟨c, r, hctx, hoff, hbot⟩ := ht
  have hsurj := t'.toScheme.surjective_cellMap_equiv σ
  obtain ⟨c', rfl⟩ := hsurj c
  obtain ⟨r', rfl⟩ := hsurj r
  have hvis (a : Fin (t'.reindex σ).card)
      (ha : a ∈ (t'.reindex σ).visibleCells (h.trans σ.symm.toEmbedding)) :
      t'.toScheme.cellMap σ.toEmbedding a ∈ t'.visibleCells h := by
    rw [Scheme.mem_visibleCells] at ha ⊢
    intro y hy
    have hy' : σ.symm y ∈ ((t'.reindex σ).toCellScheme.scope a : Set (Fin k)) := by
      change σ.symm y ∈ (t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding a)).preimage
        σ.toEmbedding σ.toEmbedding.injective.injOn
      simpa using hy
    obtain ⟨i, hi⟩ := ha hy'
    exact ⟨i, by simpa using congrArg σ hi⟩
  refine ⟨c', r', ?_, ?_, fun a ha hab ↦ ?_⟩
  · obtain ⟨⟨hcs, hcl, hcg⟩, ⟨hrl, hrb, hrm⟩, hn, hroot⟩ := hctx
    refine ⟨⟨?_, hcl, fun x hx ↦ hcg _ hx⟩, ⟨hrl, (mem_below_reindex_iff t' σ c' r').mpr hrb,
      fun x hx hxb ↦ ?_⟩, hn, fun a ha hat ↦ ?_⟩
    · change (t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding c')).preimage
        σ.toEmbedding σ.toEmbedding.injective.injOn = univ
      rw [hcs]
      exact Finset.preimage_univ _
    · exact (rowAt_reindex t' σ c' r').trans_le
        ((hrm _ hx ((mem_below_reindex_iff t' σ c' x).mp hxb)).trans_eq
          (rowAt_reindex t' σ c' x).symm)
    · exact (congrArg (visibilityReplace _ (n + 1)) (rowAt_reindex t' σ c' r')).trans_le
        ((hroot _ (hvis a ha) hat).trans_eq (rowAt_reindex t' σ c' a).symm)
  · exact fun a ha μ f hμ hf ↦ hoff _ (hvis a ha) μ f hμ hf
  · exact (rowAt_reindex t' σ c' a).trans (hbot _ (hvis a ha) hab)

end TiedRootCapRelabel

/-! ### The context with root cells labelled `⊥` does not respect them -/

namespace BottomRootCounterexample

open StageType TiedRootCapRelabel
open TiedRootCapCounterexample (rootRow rootEmb)

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- **The cap of the context with root cells labelled `⊥` reads them as `1` and `2`**, so its row
does not respect the root bottoms: the input of `BottomRootCounterexample.not_coatomProvision` is
absent at contexts whose cap respects them. -/
theorem not_rootBottomRespected : ¬ (context hα).RootBottomRespected rootEmb (capCell hα) := by
  intro hbot
  have hy := faceCell_mem_visibleCells (restrictFace_context hα) (⟨0, by decide⟩ : Fin 2)
  have h := hbot _ hy ((label_faceCell _ _).trans rfl)
  -- the separating labelling reads the cell through the row of the cap
  obtain ⟨σ, hσ, hread⟩ := exists_isBoundedReading (isLawful_separating hα)
    (separating_capCell hα)
  have hb := mem_below_of_mem_visibleCells (h := rootEmb) (context_scope_cap hα)
    (by rw [context_grade_cap]; omega) hy
  have := hread _ hb
  rw [h, hσ.map_bot, separating_root] at this
  exact absurd this (natCast_label_ne_bot _)

/-- The context with root cells labelled `⊥` is not an acquired context with the root bottoms
respected. -/
theorem not_markedCapContextBelow' : ¬ MarkedCapContextBelow' (context hα) rootEmb := by
  rintro ⟨c, r, ⟨⟨-, hcl, hcg⟩, -⟩, -, hbot⟩
  obtain rfl := eq_cap_of_label_eq_top hα hcl
  exact not_rootBottomRespected hα hbot

end BottomRootCounterexample

end VaughtConjecture
