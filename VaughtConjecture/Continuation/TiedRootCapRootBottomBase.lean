/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ExactReceiving
import VaughtConjecture.Continuation.Hollow
import VaughtConjecture.Continuation.MarkedCap
import VaughtConjecture.Extension.Apex
import VaughtConjecture.Extension.CodedSection

/-!
# Marked-cap contexts respecting the root bottoms (ported definitions)

Roadmap, Layer 3 ((R3) of the table of 3.4).

The definitions and lemmas used by the acquisition of marked-cap contexts respecting the root
bottoms: the marked-cap context at a given cap and marker (`StageType.IsMarkedCapContextAt`),
visible cells as cells of a face (`StageType.exists_faceCell_eq`), the marker inequality from
forcing (`StageType.IsMarker.visibilityReplace_le_of_forcesThreshold`), root offsets below a grade
and their bound (`StageType.RootOffsetsBelow`, `StageType.exists_offset_bound`), root bottoms
respected (`StageType.RootBottomRespected`) and the predicate
`TiedRootCapRelabel.MarkedCapContextBelow'`, the apex row
(`StageType.rowAt_addApex_last_eq_bot_iff`), and the named acquisition statement
`Realization.RootBottomAcquisition`.  Compiled in this repository (theorem named).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label
open scoped Ordinal

namespace StageType

variable {α β : Ordinal.{u}} {k m n : ℕ}

/-- Every cell visible through `h` is a cell of the face along `h`. -/
theorem exists_faceCell_eq {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} (ht : restrictFace h t' = some t) {i : Fin t'.card}
    (hi : i ∈ t'.visibleCells h) : ∃ y, faceCell ht y = i := by
  obtain ⟨z, rfl⟩ : i ∈ Set.range (t'.toScheme.cellMap h) := by
    rw [Scheme.range_cellMap]
    exact hi
  exact ⟨Fin.cast (congrArg Scheme.card (comap_toScheme_of_restrictFace ht)) z, by
    simp [faceCell, Scheme.faceCell]⟩

/-- The data of a marked-cap context along `h` with top cap `c` and marker `r`
(`StageType.IsMarkedCapContext` is `∃ c r, t'.IsMarkedCapContextAt h c r`). -/
def IsMarkedCapContextAt (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (c r : Fin t'.card) :
    Prop :=
  t'.IsTopCap c ∧ t'.IsMarker c r ∧ n + 1 < t'.toCellScheme.grade c ∧
    ∀ a ∈ t'.visibleCells h, t'.label a = ⊤ →
      visibilityReplace (t'.toCellScheme.grade c) (n + 1) (t'.rowAt c r) ≤ t'.rowAt c a

/-- **Forcing at the root tops gives the row inequality at a given marker**: let `β` be a limit,
`β + ω ≤ α`, `q` a legal stage type at `β` restricting along `f : Fin n ↪ Fin m` to `p`, `c` a
top cap of `q` and `r` a marker of `c`.  If `(q, f)` forces `n + 1` at every cell of `p` labelled
`⊤`, then `visibilityReplace N (n + 1) (q.rowAt c r) ≤ q.rowAt c a` at every cell `a` of `q`
visible through `f` and labelled `⊤`. -/
theorem IsMarker.visibilityReplace_le_of_forcesThreshold {q : StageType.{u} β m}
    {c r : Fin q.card} (hβ : Order.IsSuccLimit β)
    (hα : β + ω ≤ α) (hq : q.IsLegal) {f : Fin n ↪ Fin m} {p : StageType.{u} β n}
    (hp : restrictFace f q = some p) (hc : q.IsTopCap c) (hr : q.IsMarker c r)
    (hforce : ∀ d : Fin p.card, p.label d = ⊤ →
      ForcesThreshold α hβ.isSuccPrelimit q f p d (n + 1)) :
    ∀ a ∈ q.visibleCells f, q.label a = ⊤ →
      visibilityReplace (q.toCellScheme.grade c) (n + 1) (q.rowAt c r) ≤ q.rowAt c a := by
  intro a ha hat
  obtain ⟨hf, hqp⟩ := (restrictFace_eq_some_iff q f).mp hp
  have hcard : (q.comap f hf).card = p.card :=
    congrArg (fun s : StageType.{u} β n ↦ s.card) hqp
  obtain ⟨i, rfl⟩ : a ∈ Set.range (q.cellMap f) := by
    rw [Scheme.range_cellMap]
    exact ha
  set d : Fin p.card := ⟨i, lt_of_lt_of_eq i.2 hcard⟩
  have hd : p.label d = ⊤ := by
    rw [← hat]
    exact (label_congr hqp.symm rfl).trans (comap_label q f hf i)
  exact (ForcesThreshold.le_grade_and_visibilityReplace_rowAt_le hβ hα hq hc hr (hforce d hd) hd
    fun i' hi' ↦ congrArg (q.cellMap f) (Fin.ext hi')).2

/-- The **root offsets lie below `N`** along `h`: every label of a cell visible through `h` that
is an ordinal `μ + f` (`μ` zero or a limit) has `f < N`. -/
def RootOffsetsBelow (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (N : ℕ) : Prop :=
  ∀ y ∈ t'.visibleCells h, ∀ (μ : Ordinal.{u}) (f : ℕ), Order.IsSuccPrelimit μ →
    t'.label y = ((μ + f : Ordinal.{u}) : Label.{u}) → f < N

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

/-- The row of `c` **respects the root bottoms** along `h`: it reads every cell visible through
`h` and labelled `⊥` as `⊥`. -/
def RootBottomRespected (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (c : Fin t'.card) : Prop :=
  ∀ y ∈ t'.visibleCells h, t'.label y = ⊥ → t'.rowAt c y = ⊥

section Apex

variable {t₀ : StageType.{u} α k} (ht₀ : t₀.IsLegalBelowFullGrade) (hk : 0 < k)

/-- The apex row reads every cell at the code of its label. -/
theorem row_addApex_last_eq {z : Fin (t₀.addApex ht₀ hk).card}
    (hz : z ∈ (t₀.addApex ht₀ hk).toCellScheme.below
      ((t₀.addApex ht₀ hk).toCellScheme.gradedIndex (Fin.last _))) :
    (t₀.addApex ht₀ hk).rows.row (Fin.last _) ⟨z, hz⟩ =
      blockEncode (apexCodes ht₀) k ((t₀.addApex ht₀ hk).label z) := by
  -- the rows of `t₀.addApex` are those of `appendFullCell`
  change (t₀.toScheme.appendFullCell k (apexRow ht₀) ht₀.not_le).rows.row (Fin.last _) ⟨z, hz⟩ = _
  rw [Scheme.appendFullCell_row_last]
  change Fin (t₀.card + 1) at z
  induction z using Fin.lastCases with
  | last => rw [apexRow_last, addApex_label_last]
  | cast d => rw [apexRow_castSucc, addApex_label_castSucc]

/-- The apex has graded index `(univ, k)`. -/
theorem addApex_gradedIndex_last :
    (t₀.addApex ht₀ hk).toCellScheme.gradedIndex (Fin.last _) = (univ, k) :=
  Scheme.appendFullCellScheme_gradedIndex_last _ _

/-- Every cell lies below the apex. -/
theorem mem_below_addApex_last (z : Fin (t₀.addApex ht₀ hk).card) :
    z ∈ (t₀.addApex ht₀ hk).toCellScheme.below
      ((t₀.addApex ht₀ hk).toCellScheme.gradedIndex (Fin.last _)) := by
  rw [CellScheme.mem_below, addApex_gradedIndex_last ht₀ hk]
  exact Prod.mk_le_mk.mpr ⟨subset_univ _, (t₀.addApex ht₀ hk).grade_le z⟩

/-- The apex reads every cell at the code of its label. -/
theorem rowAt_addApex_last (z : Fin (t₀.addApex ht₀ hk).card) :
    (t₀.addApex ht₀ hk).toScheme.rowAt (Fin.last _) z =
      blockEncode (apexCodes ht₀) k ((t₀.addApex ht₀ hk).label z) := by
  rw [Scheme.rowAt_of_mem (mem_below_addApex_last ht₀ hk z)]
  exact row_addApex_last_eq ht₀ hk _

/-- **The apex reads a cell as `⊥` exactly when it is labelled `⊥`**: its row is the code of the
labels. -/
theorem rowAt_addApex_last_eq_bot_iff (z : Fin (t₀.addApex ht₀ hk).card) :
    (t₀.addApex ht₀ hk).toScheme.rowAt (Fin.last _) z = ⊥ ↔ (t₀.addApex ht₀ hk).label z = ⊥ := by
  rw [rowAt_addApex_last, blockEncode_eq_bot_iff]

end Apex

end StageType

namespace TiedRootCapRelabel

open StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **Acquired marked-cap contexts respecting the root bottoms**: a marked-cap context along `h`
whose root offsets lie below the grade of its cap and whose cap reads the root cells labelled `⊥`
as `⊥`. -/
def MarkedCapContextBelow' (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) : Prop :=
  ∃ c r, t'.IsMarkedCapContextAt h c r ∧ t'.RootOffsetsBelow h (t'.toCellScheme.grade c) ∧
    t'.RootBottomRespected h c

end TiedRootCapRelabel

namespace Realization

/-- **Acquisition of marked-cap contexts respecting the root bottoms**: hollow acquisition of the
marked-cap contexts with root offsets below the grade of the cap whose cap reads every root cell
labelled `⊥` as `⊥`. -/
def RootBottomAcquisition : Prop :=
  HollowAcquisition.{u, w} IsCoverHollowAtBlock fun t' h ↦
    TiedRootCapRelabel.MarkedCapContextBelow' t' h

end Realization

end VaughtConjecture
