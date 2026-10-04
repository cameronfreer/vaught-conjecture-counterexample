/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Normalization
import VaughtConjecture.Realization.Expansion
import VaughtConjecture.Realization.Model
import VaughtConjecture.Stage.TopFree

/-!
# Cover-hollowness and stable-label fixedness

Roadmap, Layer 4 (hollowness and its stable-label fixedness formulation; output 3 of higher-stage
reconstruction, the modelhood criterion); semantic contract, item 8.

Throughout, `R` is a realization at the block stage `λ_ξ = blockStage ξ` on a carrier `M`, and
`λ_{ξ+1} = λ_ξ + ω` is the next block stage.  Stable offsets and stable labels
(`Realization.stableOffset`, `Realization.stableLabel`, in
`VaughtConjecture.Continuation.Normalization`) are those of `R` itself, read at `λ_{ξ+1}`.

**Anchors at the top.**  Let `x` be an occurrence of `R`, `a` a cell of its type labelled the
formal top, and `N : ℕ`.  The triple `(x, a, N)` is an **anchor at the top**
(`Realization.IsTopAnchor`) when no rooted cover of `x` forces `N` at `a`: for every triple
`y = (m, q, f)` such that the tuple of `x` extends along `f` to a cover of `q` in `R`
(`Realization.ExtendsToCover`; these are the rooted covers compatible with `x`), the pair `(q, f)`
does not force the threshold `N` at `a` (`StageType.ForcesThreshold` at `λ_{ξ+1}`).  The threshold
is read at the transported position of `a`: on the face along `f` of a stage type at `λ_{ξ+1}`
reducing to `q`, at the cell at the position of `a`.  Unfolded, over every compatible rooted cover
`(q, f)` some stage type at `λ_{ξ+1}` reducing to `q` has, on its face along `f`, a label below
`λ_ξ + N` there.  The bound `N` is chosen before the quantifier over covers, and the condition
refers to all stage types reducing to the types of the covers.

* `N = 0` never gives an anchor (`Realization.not_isTopAnchor_zero`), and an anchor at `N` is one
  at every larger bound (`Realization.IsTopAnchor.mono`).
* An anchor is exactly a finite bound on the stable offset
  (`Realization.isTopAnchor_iff_not_natCast_le_stableOffset`).

**Cover-hollowness.**  `R` **has an anchor at the top** (`Realization.HasTopAnchor`) when some
anchor at the top exists, and `R` is **cover-hollow** (`Realization.IsCoverHollow`) when it has
none.  A realization whose types are top-free is cover-hollow vacuously
(`Realization.isCoverHollow_of_isTopFree`): cover-hollowness is not the assertion that there are no
cells labelled the formal top.

**Stable-label fixedness** (`Realization.isCoverHollow_iff_forall_stableLabel_eq_top`): `R` is
cover-hollow exactly when every cell of an occurrence labelled the formal top has the stable label
`⊤`.  Both directions unfold the thresholds of the stable offset
(`Realization.natCast_le_stableOffset_iff`) and the label of an offset
(`Label.ofOffset_eq_top_iff`); the tuple of an occurrence covers its type, and nothing else is used.
The theorem has **no hypothesis**: no exact consistency, covering, modelhood, finite-extension
receiving, (R1) or forcing donors.  When `R` is not cover-hollow, some cell labelled the formal top
has a proper stable label `λ_ξ + i`
(`Realization.exists_stableLabel_eq_coe_add_of_not_isCoverHollow`).

**Relation to the original definition of hollowness.**  The roadmap retains the original anchor
definition of hollowness (roadmap, Layer 4; semantic contract, item 8), with stable-label fixedness
as a theorem for models.  `IsCoverHollow` is a separate predicate, phrased through rooted covers
and forcing; it is not that definition, and no equivalence with it is claimed here.  The
equivalence of `IsCoverHollow` with the original hollowness is still to be proved.  The countable
cover of terminal classes (condition 2, terminal countability) and the modelhood criterion
(output 3) are to be stated with `IsCoverHollow`; both are prospective, and neither is stated
here.

The word *anchor* here is unrelated to the anchor of a donor cell in `Extension/Gate` (a private
cell from which a gate reading reads the label of a donor cell).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Ordinal

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v}

section Definitions

variable (R : Realization.{u, v} (blockStage ξ) M)

/-- An **anchor at the top**: the cell `a` of the type of the occurrence `x` is labelled the
formal top, and no rooted cover compatible with `x` forces the threshold `N` at `a`.  A compatible
rooted cover is a triple `y = (m, q, f)` such that the tuple of `x` extends along `f` to a cover of
`q` in `R`; forcing is read at `λ_{ξ+1}`, at the position of `a` on the face along `f`. -/
def IsTopAnchor (x : R.Occurrence) (a : Fin x.type.card) (N : ℕ) : Prop :=
  x.type.label a = ⊤ ∧ ∀ y : Σ m : ℕ, StageType.{u} (blockStage ξ) m × (Fin x.arity ↪ Fin m),
    R.ExtendsToCover x.tuple y →
      ¬ StageType.ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) y.2.1 y.2.2
        x.type a N

/-- The realization **has an anchor at the top**: some occurrence, cell and bound form one. -/
def HasTopAnchor : Prop :=
  ∃ (x : R.Occurrence) (a : Fin x.type.card) (N : ℕ), R.IsTopAnchor x a N

/-- The realization is **cover-hollow**: it has no anchor at the top.  This is not the original
anchor definition of hollowness of the roadmap; their equivalence is still to be proved. -/
def IsCoverHollow : Prop :=
  ¬ R.HasTopAnchor

end Definitions

variable {R : Realization.{u, v} (blockStage ξ) M} {x : R.Occurrence} {a : Fin x.type.card}
  {N N' : ℕ}

/-- An anchor at a bound is an anchor at every larger bound: forcing is downward closed. -/
theorem IsTopAnchor.mono (h : R.IsTopAnchor x a N) (hN : N ≤ N') : R.IsTopAnchor x a N' :=
  ⟨h.1, fun y hy hf ↦ h.2 y hy (hf.mono hN)⟩

/-- **No anchor at the bound `0`**: the trivial rooted cover forces `0` at every cell labelled the
formal top. -/
theorem not_isTopAnchor_zero (x : R.Occurrence) (a : Fin x.type.card) : ¬ R.IsTopAnchor x a 0 :=
  fun ⟨ha, h⟩ ↦ h ⟨x.arity, x.type, Function.Embedding.refl _⟩
    ⟨x.tuple, rfl, covers_of_eval _ x.eval_tuple⟩
    (StageType.forcesThreshold_zero (StageType.restrictFace_refl _) ha)

/-- **An anchor is a finite bound on the stable offset**: at a cell labelled the formal top,
`(x, a, N)` is an anchor at the top exactly when `N` exceeds the stable offset of `a` at `x`. -/
theorem isTopAnchor_iff_not_natCast_le_stableOffset (ha : x.type.label a = ⊤) :
    R.IsTopAnchor x a N ↔ ¬ (N : ℕ∞) ≤
      R.stableOffset (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) x.tuple x.type a := by
  rw [natCast_le_stableOffset_iff (covers_of_eval _ x.eval_tuple) ha, IsTopAnchor]
  simp only [ha, true_and, not_exists, not_and]
  exact forall_congr' fun y ↦ ⟨fun h hf hy ↦ h hy hf, fun h hy hf ↦ h hf hy⟩

/-- **Stable-label fixedness**: `R` is cover-hollow exactly when every cell of an occurrence that
is labelled the formal top has the stable label `⊤`.  No hypothesis on `R` is needed. -/
theorem isCoverHollow_iff_forall_stableLabel_eq_top :
    R.IsCoverHollow ↔ ∀ (x : R.Occurrence) (a : Fin x.type.card), x.type.label a = ⊤ →
      R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) x.tuple x.type a = ⊤ := by
  simp only [IsCoverHollow, HasTopAnchor, not_exists, stableLabel, Label.ofOffset_eq_top_iff]
  refine forall_congr' fun x ↦ forall_congr' fun a ↦ ⟨fun h ha ↦ ?_, fun h N hN ↦ ?_⟩
  · refine ENat.eq_top_iff_forall_ge.mpr fun N ↦ ?_
    by_contra hN
    exact h N ((isTopAnchor_iff_not_natCast_le_stableOffset ha).mpr hN)
  · exact (isTopAnchor_iff_not_natCast_le_stableOffset hN.1).mp hN ((h hN.1).symm ▸ le_top)

/-- **The attained proper stable label**: if `R` is not cover-hollow, some cell of an occurrence
that is labelled the formal top has the stable label `λ_ξ + i` for some `i : ℕ`. -/
theorem exists_stableLabel_eq_coe_add_of_not_isCoverHollow (h : ¬ R.IsCoverHollow) :
    ∃ (x : R.Occurrence) (a : Fin x.type.card) (i : ℕ), x.type.label a = ⊤ ∧
      R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) x.tuple x.type a =
        ((blockStage ξ + i : Ordinal.{u}) : Label.{u}) := by
  rw [isCoverHollow_iff_forall_stableLabel_eq_top] at h
  push Not at h
  obtain ⟨x, a, ha, hne⟩ := h
  have ho : R.stableOffset (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) x.tuple x.type a ≠
      ⊤ := fun ho ↦ hne (Label.ofOffset_eq_top_iff.mpr ho)
  exact ⟨x, a, _, ha, (ite_eq_right ho : Label.ofOffset _ _ = _)⟩

/-- **A top-free realization is cover-hollow**, vacuously: no cell is labelled the formal top. -/
theorem isCoverHollow_of_isTopFree (h : ∀ x : R.Occurrence, x.type.IsTopFree) :
    R.IsCoverHollow :=
  fun ⟨x, a, _, ha, _⟩ ↦ h x a ha

end Realization

end VaughtConjecture
