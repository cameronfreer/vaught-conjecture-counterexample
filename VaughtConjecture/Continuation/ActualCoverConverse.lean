/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ActualCoverTransport
import VaughtConjecture.Continuation.RowComparison

/-!
# A cover anchor at a model gives a row anchor at the same bound

Roadmap, Layer 4 (cover-hollowness and the anchor definition of hollowness); semantic contract,
item 8.  A research file: the converse, at models, of `Realization.IsRowAnchor.isTopAnchor` (in
`VaughtConjecture.Continuation.ActualCoverTransport`), for the native definitions
`Realization.IsTopAnchor` and `Realization.IsRowAnchor`.

**Stable offsets at an actual rooted cover** (`Realization.stableOffset_eq_of_covers`).  Let `S`
be an exactly consistent covering realization at a stage `β` that is zero or a limit, and let
`(m, q, f)` be an actual rooted cover of a tuple `c` with tuple `s`: `S.Covers q s` and
`s ∘ f = c`.  If `q` restricts to `p` along the literal root map `f` and `e` is the cell of `q`
transported from the cell `d` of `p` (`q.cellMap f i = e` for the cell `i` of the face along `f`
at the position of `d`), then the stable offset of `e` at `s` (root `q`) equals the stable offset
of `d` at `c` (root `p`).  This is `Realization.stableOffset_comap` at the typed tuple `s` along
the face `f`, whose type `q.comap f hf` is `p` by the restriction, with the cells matched by
position (`Realization.stableOffset_congr`).  Premises by use: exact consistency and covering of
`S` (for `Realization.stableOffset_comap`); the restriction of `q` to `p` along `f`; the cell
transport.

**The converse at the same bound** (`Realization.IsTopAnchor.isRowAnchor`).  Let `R` be a model
at `λ_ξ` and `(x, a, N)` a cover anchor: no actual rooted cover of `x` forces `N` at `a`.  Then
`(x, a, N)` is a row anchor; the statement has no other premise.  At each actual rooted cover the
label `⊤` of the transported cell and the equality of stable offsets are derived from the cover
(`StageType.label_eq_top_of_restrictFace`, `Realization.stableOffset_eq_of_covers`).  The
stable offset of `a` at `x` is below `N`
(`Realization.isTopAnchor_iff_not_natCast_le_stableOffset`); at each actual rooted cover
`(m, q, f)` of `x` with tuple `s` restricting to the type of `x`, the stable offset of the
transported cell `e` at `s` is the same, hence below `N`; and for every cell `θ` labelled `⊤` of
grade at least `N` and every `σ` labelled `⊤` below `θ`, with `e` below `θ`, the row comparison
through the lawful stable section
(`Realization.IsModel.rowAt_lt_visibilityReplace_of_stableOffset_lt`) gives
`q.rowAt θ e < visibilityReplace N N (q.rowAt θ σ)`.  The bound of the row anchor is `K = N`;
both clauses of the row anchor follow from this strict inequality.  Premises used from
modelhood: exact consistency and covering (the transport of stable offsets), and stable
lawfulness (`Realization.IsModel.isStablyLawful`, from exact consistency, covering and legal
types).  The stable candidate is not assumed to be a model.

**The bounds.**  The two transports are not at the same bound:

* `Realization.IsRowAnchor.isTopAnchor` (legal types): a row anchor at `K` gives a cover anchor
  at `K + 1`;
* `Realization.IsTopAnchor.isRowAnchor` (models): a cover anchor at `N` gives a row anchor at `N`.

So no statement `IsRowAnchor x a K ↔ IsTopAnchor x a K` at one bound is proved.

**The existential forms at a model** (`Realization.HasTopAnchor.hasRowAnchor`,
`Realization.IsModel.hasRowAnchor_iff_hasTopAnchor`,
`Realization.IsModel.isCoverHollow_iff_not_hasRowAnchor`).  At a model at a block stage, a row
anchor exists exactly when an anchor at the top exists, and the model is cover-hollow exactly when
it has no row anchor.  Existential quantification over the bound absorbs the shift of the bound;
these are not equivalences at one bound.

Both transports and their existential forms concern the native definitions
`Realization.IsTopAnchor` and `Realization.IsRowAnchor` of this repository;
`Realization.IsRowAnchor` is a reading of [Kni26, Definition 5.4.2] that is not shown to agree
with the printed definition, so nothing here is a statement about the manuscript's definition.

**The bound `0`.**  No cover anchor has the bound `0` (`Realization.not_isTopAnchor_zero`: the
trivial rooted cover forces `0`), so at `N = 0` the premise is impossible; the proof treats that
case through this lemma, with no positivity premise on `N`.

**Not claimed here.**  No modelhood statement, no change to `Realization.stableOffset`, to the
normalization of `VaughtConjecture.Continuation.Normalization`, or to the predicates of (R3).

## Placement

This file belongs to Layer 4 of `roadmap/README.md` (research).

## References

The row reading of an anchor is a reading of [Kni26, Definition 5.4.2].
-/

universe u v

namespace VaughtConjecture

open Order Label
open scoped Ordinal

namespace Realization

/-- **Stable offsets at an actual rooted cover.**  Let `S` be an exactly consistent covering
realization at a stage `β` that is zero or a limit, `s` a tuple covering `q` in `S` with
`s ∘ f = c`, `q` restricting to `p` along `f`, and `e` the cell of `q` transported from the cell
`d` of `p`.  Then the stable offset of `e` at `s` (root `q`) is the stable offset of `d` at `c`
(root `p`). -/
theorem stableOffset_eq_of_covers {α β : Ordinal.{u}} {hβ : IsSuccPrelimit β} {M : Type v}
    {S : Realization.{u, v} β M} (hS : S.IsConsistent) (hc : S.IsCovering) {k m : ℕ}
    {c : Fin k → M} {p : StageType.{u} β k} {q : StageType.{u} β m} {f : Fin k ↪ Fin m}
    {s : Fin m → M} (hs : S.Covers q s) (hsf : s ∘ f = c)
    (hfp : StageType.restrictFace f q = some p) {d : Fin p.card} {e : Fin q.card}
    (he : ∀ i : Fin (q.toScheme.comap f).card, (i : ℕ) = d → q.cellMap f i = e) :
    S.stableOffset α hβ s q e = S.stableOffset α hβ c p d := by
  obtain ⟨hf, hqp⟩ := (StageType.restrictFace_eq_some_iff q f).mp hfp
  have hcard : (q.comap f hf).card = p.card :=
    congrArg (fun t : StageType.{u} β k ↦ t.card) hqp
  set i₀ : Fin (q.comap f hf).card := ⟨d, lt_of_lt_of_eq d.2 hcard.symm⟩
  have h := stableOffset_comap (α := α) (hβ := hβ) hS hc (u := ⟨s, hs.injective⟩) hs.eval_eq f hf
    i₀
  have hc' : ((f.trans ⟨s, hs.injective⟩ : Fin k ↪ M) : Fin k → M) = c := hsf
  rw [hc', he i₀ rfl, stableOffset_congr hqp (d' := d) rfl] at h
  exact h.symm

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}
  {x : R.Occurrence} {a : Fin x.type.card} {N : ℕ}

/-- **A cover anchor at a model is a row anchor at the same bound**: if `R` at `λ_ξ` is a model
and no actual rooted cover of `x` forces `N` at `a`, then `(x, a, N)` is a row anchor.  The
forward transport `Realization.IsRowAnchor.isTopAnchor` gives a cover anchor at `K + 1` from a
row anchor at `K`, so the two transports do not have the same bound.  At `N = 0` the premise is
impossible (`Realization.not_isTopAnchor_zero`). -/
theorem IsTopAnchor.isRowAnchor (hR : R.IsModel) (h : R.IsTopAnchor x a N) :
    R.IsRowAnchor x a N := by
  rcases eq_or_ne N 0 with rfl | -
  · exact absurd h (not_isTopAnchor_zero x a)
  have hoff : R.stableOffset (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) x.tuple x.type a
      < N := not_le.mp ((isTopAnchor_iff_not_natCast_le_stableOffset h.1).mp h)
  refine ⟨h.1, fun y hy hfp e he θ hθ hK σ hσ hσθ heθ ↦ ?_⟩
  obtain ⟨s, hsf, hs⟩ := hy
  have heq := stableOffset_eq_of_covers (α := blockStage (ξ + 1))
    (hβ := isSuccPrelimit_blockStage ξ) hR.isConsistent hR.isCovering hs hsf hfp he
  have hel := StageType.label_eq_top_of_restrictFace hfp h.1 he
  have hlt := hR.rowAt_lt_visibilityReplace_of_stableOffset_lt (u := ⟨s, hs.injective⟩)
    hs.eval_eq hθ hσ hel hσθ heθ hK (heq.trans_lt hoff)
  exact ⟨hlt.le, fun _ ↦ hlt⟩

/-- **A model with an anchor at the top has a row anchor**, for `R` a model at `λ_ξ`.
Existential quantification absorbs the bound: a cover anchor at `N` gives a row anchor at `N`
at models, while a row anchor at `K` gives a cover anchor at `K + 1`.  This is not an equivalence
at one bound, and the native row reading is not identified with the definition of
[Kni26, Definition 5.4.2]. -/
theorem HasTopAnchor.hasRowAnchor (hR : R.IsModel) (h : R.HasTopAnchor) : R.HasRowAnchor :=
  let ⟨x, a, N, hx⟩ := h
  ⟨x, a, N, hx.isRowAnchor hR⟩

/-- **At a model, a row anchor exists exactly when an anchor at the top exists**, for `R` a model
at `λ_ξ`.  Existential quantification absorbs the bound shift: a row anchor at `K` gives a cover
anchor at `K + 1` (`Realization.IsRowAnchor.isTopAnchor`), and a cover anchor at `N` gives a row
anchor at `N` at models (`Realization.IsTopAnchor.isRowAnchor`).  This is not an equivalence at
one bound, and it concerns the native `Realization.IsRowAnchor`, which is not identified with the
definition of [Kni26, Definition 5.4.2]. -/
theorem IsModel.hasRowAnchor_iff_hasTopAnchor (hR : R.IsModel) :
    R.HasRowAnchor ↔ R.HasTopAnchor :=
  ⟨fun h ↦ h.hasTopAnchor hR.hasLegalTypes, fun h ↦ h.hasRowAnchor hR⟩

/-- **At a model, cover-hollowness is the absence of a row anchor**, for `R` a model at `λ_ξ`.
Existential quantification absorbs the bound shift (a row anchor at `K` gives a cover anchor at
`K + 1`; a cover anchor at `N` gives a row anchor at `N` at models).  This is not an equivalence
at one bound, and it concerns the native `Realization.HasRowAnchor`, which is not identified with
the anchor of [Kni26, Definition 5.4.2]. -/
theorem IsModel.isCoverHollow_iff_not_hasRowAnchor (hR : R.IsModel) :
    R.IsCoverHollow ↔ ¬ R.HasRowAnchor :=
  not_congr hR.hasRowAnchor_iff_hasTopAnchor.symm

end Realization

end VaughtConjecture
