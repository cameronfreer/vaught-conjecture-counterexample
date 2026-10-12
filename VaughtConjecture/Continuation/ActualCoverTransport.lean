/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Hollow
import VaughtConjecture.Continuation.StableOffsetLeastLift

/-!
# Row anchors over the actual rooted covers bound the stable offset

Roadmap, Layer 4 (cover-hollowness and the anchor definition of hollowness); Layer 3, 3.1 (the
attained least lift and the threshold characterization, used here as inputs); semantic contract,
item 8.  A research file: one direction of the transport between two readings of an anchor, at
the actual rooted covers of a realization.

**The actual rooted covers.**  Let `R` be a realization, `x` an occurrence of `R` and `a` a cell
of its type labelled `⊤`.  The **actual rooted covers** of `x` are the triples
`y = (m, q, f)` with `R.ExtendsToCover x.tuple y` (`Realization.ExtendsToCover`): some tuple `s`
on `m` points covers `q` in `R` (so `q` is the type of the actual tuple `s`) and `s ∘ f` is the
tuple of `x`.  The literal root map is `f`, and the cell of `q` transported from `a` is
`q.cellMap f i` for the cell `i` of the face along `f` at the position of `a`, as in
`StageType.labellingOffset`.  This index family is the one of `Realization.stableOffset` and of
`Realization.IsTopAnchor`, unchanged.

**Two readings of an anchor at `(x, a)`.**

* The **cover reading** (`Realization.IsTopAnchor x a N`, in
  `VaughtConjecture.Continuation.Hollow`): no actual rooted cover forces `N` at `a`.  At a block
  stage it says exactly that the stable offset of `a` at `x` is below `N`
  (`Realization.isTopAnchor_iff_not_natCast_le_stableOffset`);
  the stable offset is the supremum over the actual rooted covers of the provisional offsets
  (`StageType.provisionalOffset`).
* The **row reading** (`Realization.IsRowAnchor x a K`, defined here): `a` is labelled `⊤`, and
  at every actual rooted cover `(q, f)` whose type restricts to the type of `x` along `f`, with
  `e` the cell transported from `a`, for every cell `θ` of `q` labelled `⊤` of grade at least `K`
  and every cell `σ` labelled `⊤` below `θ`, with `e` below `θ`,
  `q.rowAt θ e ≤ visibilityReplace K K (q.rowAt θ σ)`, strictly when the grade of `θ` exceeds `K`.
  It is a native reading of [Kni26, Definition 5.4.2] (the anchor at infinity, "minimal at
  infinity"), stated over the definitions of this repository: the semantics `E(Θ)` there is read
  as the row `q.rowAt θ`, and the bound `K'` there as `K`.  It is not shown to agree with the
  printed definition.  A realization **has a row anchor**
  (`Realization.HasRowAnchor`) when some occurrence, cell and bound form one.

**The transport proved: rows to covers.**  Let `R` be at a block stage `λ_ξ` with legal types.

* Per cover (`StageType.provisionalOffset_le_of_rowAt_lt`): for a legal stage type `q` at a limit
  `β`, `β + ω ≤ α`, restricting to `p` along `f`, a cell `d` of `p` labelled `⊤` transported to `e`,
  if `q.rowAt c e < visibilityReplace K K (q.rowAt c r)` for every top cap `c` of grade above `K`
  and every marker `r` of `c`, then the provisional offset of `d` at `(q, f)` is at most `K`.  The
  proof reads forcing through the rows of a top cap
  (`StageType.ForcesThreshold.le_grade_and_visibilityReplace_rowAt_le`): a forced `K + 1` gives a
  top cap of grade `N > K` with `visibilityReplace N (K + 1) (q.rowAt c r) ≤ q.rowAt c e`, and with
  the minimality of the marker this is at least `visibilityReplace K K (q.rowAt c r)`.
* At every actual rooted cover (`Realization.IsRowAnchor.provisionalOffset_le`) and for the
  stable offset (`Realization.IsRowAnchor.stableOffset_le`): a row anchor `(x, a, K)` bounds the
  provisional offset of `a` at every actual rooted cover of `x`, and hence the stable offset, by
  `K`.
* Hence a row anchor at `K` gives a cover anchor at `K + 1`
  (`Realization.IsRowAnchor.isTopAnchor`),
  and a realization with legal types and a row anchor has an anchor at the top
  (`Realization.HasRowAnchor.hasTopAnchor`).

**Premises, and where they come from.**  The only premise on `R` is `R.HasLegalTypes`, giving the
legality of the type of every actual rooted cover (`Realization.ExtendsToCover.isLegal`).  The
stage premises of the least-lift statements (`β` a limit, `β + ω ≤ α`) hold at consecutive block
stages (`isSuccLimit_blockStage`, `blockStage_add_one`).  At the callers that hold a model, legal
types are a clause of modelhood (`Realization.IsModel.hasLegalTypes`): the comparison under (R3)
(`Realization.HollowReceiving`, whose hypotheses include `R.IsModel` and, for receiving models,
`Realization.IsReceivingCoverHollowAtBlock`, of which cover-hollowness at a block stage is the
first conjunct) and the cover of the receiving-terminal receiving models by terminal properties
(`Realization.IsReceivingTerminalAt.isCoverHollow`, from a receiving model).  So a model that is
cover-hollow at a block stage has no row anchor
(`Realization.IsCoverHollowAtBlock.not_hasRowAnchor`).

**Coding.**  Strong coding of the rows (`CellScheme.Rows.IsStronglyCoded`) is not used: only the
range normalization carried by every stage type, through the band lift
(`StageType.IsMarker.exists_lift`), which places the row entry of a top cap at its marker at an
ordinal `μ + j`.  No exact consistency, covering or receiving of `R` is used.

**Open, not claimed here.**  The converse transport, from a cover anchor to a row anchor at some
bound, is not proved.  At one cover the least-lift characterization
(`StageType.IsMarker.forcesThreshold_iff_le_grade_and_visibilityReplace_rowAt_le`) gives the row
inequality only for `θ` a top cap and `σ` a marker of it; the row reading asks it at every cell
`θ` labelled `⊤` of grade at least the bound and every `σ` labelled `⊤` below `θ`.  One sufficient
route, not a requirement: at a legal stage type at a limit, for a top cap `c` with a marker `r`,
cells `θ`, `σ`, `e` labelled `⊤` with `σ` and `e` below `θ`, and `K` at most the grade of `θ`, if
`q.rowAt c e < visibilityReplace K K (q.rowAt c r)` then the row clause holds at `θ`, `σ`, `e`
(weakly, and strictly when the grade of `θ` exceeds `K`).  With legal types this statement gives
the converse at the bound `N` of a cover anchor; it is not proved, and refuting it would not
refute the converse, which may be reached through several covers instead.  No equivalence
of the two readings, of cover-hollowness with the absence of a row anchor, or any modelhood
statement is claimed, and `Realization.stableOffset` and the normalization of
`VaughtConjecture.Continuation.Normalization` are unchanged.

## Placement

This file belongs to Layer 4 of `roadmap/README.md` (research).

## References

The row reading is a reading of the anchor at infinity of [Kni26, Definition 5.4.2]; the
provisional values are [Kni26, Definition 5.3.1].
-/

universe u v w

namespace VaughtConjecture

open Order Label
open scoped Ordinal

namespace StageType

variable {α β : Ordinal.{u}} {m k : ℕ} {q : StageType.{u} β m} {f : Fin k ↪ Fin m}
  {p : StageType.{u} β k} {d : Fin p.card} {e : Fin q.card} {K : ℕ}

/-- **A strict row bound at the top caps excludes forcing `K + 1`.**  Let `β` be a limit,
`β + ω ≤ α`, `q` a legal stage type at `β` restricting to `p` along `f`, `d` a cell of `p` labelled
`⊤` and `e` the cell of `q` transported from `d`.  If
`q.rowAt c e < visibilityReplace K K (q.rowAt c r)` for every top cap `c` of grade above `K` and
every marker `r` of `c`, then `(q, f)` does not force `K + 1` at `d`. -/
theorem not_forcesThreshold_of_rowAt_lt (hβ : IsSuccLimit β) (hα : β + ω ≤ α) (hq : q.IsLegal)
    (hfp : restrictFace f q = some p) (hd : p.label d = ⊤)
    (he : ∀ i : Fin (q.toScheme.comap f).card, (i : ℕ) = d → q.cellMap f i = e)
    (hrow : ∀ c r : Fin q.card, q.IsTopCap c → q.IsMarker c r → K < q.toCellScheme.grade c →
      q.rowAt c e < visibilityReplace K K (q.rowAt c r)) :
    ¬ ForcesThreshold α hβ.isSuccPrelimit q f p d (K + 1) := by
  intro hforce
  have hel := label_eq_top_of_restrictFace hfp hd he
  obtain ⟨c, hc⟩ := exists_isTopCap hq fun h ↦ h e hel
  obtain ⟨r, hr⟩ := exists_isMarker hc.2.1
  obtain ⟨hKN, hvis⟩ := hforce.le_grade_and_visibilityReplace_rowAt_le hβ hα hq hc hr hd he
  have hlt := hrow c r hc hr hKN
  obtain ⟨μ, j, hμ, hrj, -⟩ := hr.exists_lift hβ hα hq hc
  have hre : q.rowAt c r ≤ q.rowAt c e := hr.2.2 e hel (hc.mem_below hel)
  rw [hrj] at hre hvis hlt
  rw [visibilityReplace_coe_add hμ] at hvis hlt
  refine hlt.not_ge ?_
  split_ifs at hlt ⊢ with hjK
  · rw [ite_eq_left (show j < q.toCellScheme.grade c by omega)] at hvis
    exact (coe_add_natCast_le_coe_add_natCast_iff.mpr (Nat.le_succ K)).trans hvis
  · exact hre

/-- **A strict row bound at the top caps bounds the provisional offset.**  Under the hypotheses of
`StageType.not_forcesThreshold_of_rowAt_lt`, the provisional offset of `d` at `(q, f)` is at most
`K`. -/
theorem provisionalOffset_le_of_rowAt_lt (hβ : IsSuccLimit β) (hα : β + ω ≤ α) (hq : q.IsLegal)
    (hfp : restrictFace f q = some p) (hd : p.label d = ⊤)
    (he : ∀ i : Fin (q.toScheme.comap f).card, (i : ℕ) = d → q.cellMap f i = e)
    (hrow : ∀ c r : Fin q.card, q.IsTopCap c → q.IsMarker c r → K < q.toCellScheme.grade c →
      q.rowAt c e < visibilityReplace K K (q.rowAt c r)) :
    provisionalOffset α hβ.isSuccPrelimit q f p d ≤ K :=
  iSup₂_le fun _ hn ↦ Nat.cast_le.mpr <| not_lt.mp fun hKn ↦
    not_forcesThreshold_of_rowAt_lt hβ hα hq hfp hd he hrow (hn.mono hKn)

end StageType

namespace Realization

section Definitions

variable {α : Ordinal.{u}} {M : Type v} (R : Realization.{u, v} α M)

/-- A **row anchor**: the cell `a` of the type of the occurrence `x` is labelled `⊤`, and at every
actual rooted cover `y = (m, q, f)` of `x` (`R.ExtendsToCover x.tuple y`) whose type restricts to
the type of `x` along `f`, with `e` the cell of `q` transported from `a`, every cell `θ` of `q`
labelled `⊤` of grade at least `K` and every cell `σ` labelled `⊤` below `θ`, with `e` below `θ`,
satisfy `q.rowAt θ e ≤ visibilityReplace K K (q.rowAt θ σ)`, strictly when the grade of `θ`
exceeds `K`.  A native reading, on the rows, of the anchor at infinity of
[Kni26, Definition 5.4.2]; it is not shown to agree with the printed definition. -/
def IsRowAnchor (x : R.Occurrence) (a : Fin x.type.card) (K : ℕ) : Prop :=
  x.type.label a = ⊤ ∧ ∀ y : Σ m : ℕ, StageType.{u} α m × (Fin x.arity ↪ Fin m),
    R.ExtendsToCover x.tuple y → StageType.restrictFace y.2.2 y.2.1 = some x.type →
    ∀ e : Fin y.2.1.card, (∀ i : Fin (y.2.1.toScheme.comap y.2.2).card, (i : ℕ) = a →
      y.2.1.cellMap y.2.2 i = e) →
    ∀ θ : Fin y.2.1.card, y.2.1.label θ = ⊤ → K ≤ y.2.1.toCellScheme.grade θ →
    ∀ σ : Fin y.2.1.card, y.2.1.label σ = ⊤ →
      σ ∈ y.2.1.toCellScheme.below (y.2.1.toCellScheme.gradedIndex θ) →
      e ∈ y.2.1.toCellScheme.below (y.2.1.toCellScheme.gradedIndex θ) →
      y.2.1.rowAt θ e ≤ visibilityReplace K K (y.2.1.rowAt θ σ) ∧
        (K < y.2.1.toCellScheme.grade θ →
          y.2.1.rowAt θ e < visibilityReplace K K (y.2.1.rowAt θ σ))

/-- The realization **has a row anchor**: some occurrence, cell and bound form one. -/
def HasRowAnchor : Prop :=
  ∃ (x : R.Occurrence) (a : Fin x.type.card) (K : ℕ), R.IsRowAnchor x a K

end Definitions

section Transport

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}
  {x : R.Occurrence} {a : Fin x.type.card} {K : ℕ}

/-- **A row anchor bounds the provisional offset at every actual rooted cover**: if `R` at `λ_ξ`
has legal types and `(x, a, K)` is a row anchor, then at every actual rooted cover `y = (m, q, f)`
of `x` the provisional offset of `a` at `(q, f)`, read at `λ_{ξ+1}`, is at most `K`. -/
theorem IsRowAnchor.provisionalOffset_le (hl : R.HasLegalTypes) (h : R.IsRowAnchor x a K)
    {y : Σ m : ℕ, StageType.{u} (blockStage ξ) m × (Fin x.arity ↪ Fin m)}
    (hy : R.ExtendsToCover x.tuple y) :
    StageType.provisionalOffset (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) y.2.1 y.2.2
      x.type a ≤ K := by
  by_cases hfp : StageType.restrictFace y.2.2 y.2.1 = some x.type
  · obtain ⟨e, he⟩ := StageType.exists_transported_cell hfp a
    have hel := StageType.label_eq_top_of_restrictFace hfp h.1 he
    exact StageType.provisionalOffset_le_of_rowAt_lt (isSuccLimit_blockStage ξ)
      (blockStage_add_one ξ).ge (hy.isLegal hl) hfp h.1 he fun c r hc hr hK ↦
        (h.2 y hy hfp e he c hc.2.1 hK.le r hr.1 hr.2.1 (hc.mem_below hel)).2 hK
  · -- a cover not restricting to the type of `x` forces nothing
    exact iSup₂_le fun _ hn ↦ absurd hn.1 hfp

/-- **A row anchor bounds the stable offset**: if `R` at `λ_ξ` has legal types and `(x, a, K)` is
a row anchor, the stable offset of `a` at `x`, read at `λ_{ξ+1}`, is at most `K`. -/
theorem IsRowAnchor.stableOffset_le (hl : R.HasLegalTypes) (h : R.IsRowAnchor x a K) :
    R.stableOffset (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) x.tuple x.type a ≤ K :=
  iSup₂_le fun _ hy ↦ h.provisionalOffset_le hl hy

/-- **A row anchor is a cover anchor at the next bound**: if `R` at `λ_ξ` has legal types and
`(x, a, K)` is a row anchor, then no actual rooted cover of `x` forces `K + 1` at `a`. -/
theorem IsRowAnchor.isTopAnchor (hl : R.HasLegalTypes) (h : R.IsRowAnchor x a K) :
    R.IsTopAnchor x a (K + 1) := by
  refine (isTopAnchor_iff_not_natCast_le_stableOffset h.1).mpr fun hle ↦ ?_
  have := hle.trans (h.stableOffset_le hl)
  exact (Nat.lt_succ_self K).not_ge (by exact_mod_cast this)

/-- **A row anchor gives an anchor at the top**, for `R` at `λ_ξ` with legal types. -/
theorem HasRowAnchor.hasTopAnchor (hl : R.HasLegalTypes) (h : R.HasRowAnchor) :
    R.HasTopAnchor :=
  let ⟨x, a, K, hx⟩ := h
  ⟨x, a, K + 1, hx.isTopAnchor hl⟩

/-- **A cover-hollow realization has no row anchor**, for `R` at `λ_ξ` with legal types.  One
implication only; the converse is not proved. -/
theorem IsCoverHollow.not_hasRowAnchor (hl : R.HasLegalTypes) (hH : R.IsCoverHollow) :
    ¬ R.HasRowAnchor :=
  fun h ↦ hH (h.hasTopAnchor hl)

end Transport

/-- **At the callers holding a model**: a model cover-hollow at a block stage has no row anchor.
Legal types are a clause of modelhood (`Realization.IsModel.hasLegalTypes`).  One implication only;
the converse is not proved. -/
theorem IsCoverHollowAtBlock.not_hasRowAnchor {α : Ordinal.{u}} {M : Type w}
    {R : Realization.{u, w} α M} (hR : R.IsModel) (hH : R.IsCoverHollowAtBlock) :
    ¬ R.HasRowAnchor := by
  obtain ⟨ξ, rfl, hH⟩ := hH
  exact hH.not_hasRowAnchor hR.hasLegalTypes

end Realization

end VaughtConjecture
