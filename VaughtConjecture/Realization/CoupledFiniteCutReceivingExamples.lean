/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.CoupledFiniteCutReceiving

/-!
# Examples for finite-cut receiving from the coupled gated pinned extension property

Special cases of `VaughtConjecture.Realization.CoupledFiniteCutReceiving`, under the coupled gated
pinned extension property (`StageType.HasCoupledGatedPinnedExtensions`), a named hypothesis that is
open; none of them is a proof of (R1):

* **the empty root**: over an occurrence on no points the anchored private context has arity at
  least `2`, and the donor is received over it at every permitted cutoff;
* **the two routes**: the bottom-pattern clause, in place of generalized saturation, gives the
  same conclusion;
* **a donor whose new cells are all labelled `⊤`** is anchored below every cell, so it needs no
  reference cell (on `GatedExtensionCounterexample.P α`, the coupled gated extension for such a
  donor is not compiled: it needs the cap lowered, the open point of the hypothesis);
* **donor tops** come back only as values at least the cutoff: a member of the receiving family
  at `c` of a donor labelled `⊤` at a cell is labelled at least `c` there, and nothing more is
  known;
* **one cutoff at a time**: receiving at two cutoffs gives two received points, with no
  relation between them claimed.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture.Realization

open Finset Label StageType

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-! ### The empty root -/

/-- **The empty root, private context**: over an occurrence on no points, the anchored private
context has arity at least `2`. -/
example (hR : R.IsModel) (x : R.Occurrence) (hx : x.arity = 0) (d : StageType.{u} α (x.arity + 1))
    {γ : Ordinal.{u}} (hγ : γ < α) :
    ∃ (y : R.Occurrence) (C : Fin y.type.card), 2 ≤ y.arity ∧ IsAnchored y.type C d := by
  obtain ⟨y, -, C, -, -, hn, -, -, hanc⟩ := hR.exists_privateContext_isAnchored x d hγ
  exact ⟨y, C, by omega, hanc⟩

/-- **The empty root, receiving**: under the coupled gated pinned extension property, a model
receives every coface of the type of an occurrence on no points at every permitted cutoff. -/
example (hR : R.IsModel) (hg : HasCoupledGatedPinnedExtensions α) (x : R.Occurrence)
    (_hx : x.arity = 0) {d : StageType.{u} α (x.arity + 1)} (hd : d ∈ x.type.cofaces)
    {c : Label.{u}} (hc : IsPermittedCutoff α c) : R.RealizesOver x.tuple (receivingFamily d c) :=
  hR.hasFiniteCutReceiving_of_hasCoupledGatedPinnedExtensions hg x d hd c hc

/-! ### The two routes -/

/-- **The bottom-pattern clause gives the same conclusion as generalized saturation**: the assembly
of `IsModel.hasFiniteCutReceiving_of_hasCoupledGatedPinnedExtensions` with the bottom-pattern
clause for the scheme and labels of the display in place of generalized saturation (the
bottom-pattern family lies in the family of generalized saturation).  Conditional on the same open
named hypothesis; not a proof of (R1). -/
example (hR : R.IsModel) (hg : HasCoupledGatedPinnedExtensions α) : R.HasFiniteCutReceiving := by
  intro x d hd c hc
  obtain ⟨γ, hγα, rfl⟩ := isPermittedCutoff_iff.mp hc
  obtain ⟨y, f, C, hf, hfp, hn, hC, hγC, hanc⟩ := hR.exists_privateContext_isAnchored x d hγα
  obtain ⟨E, hE⟩ := hg y.type f x.type d C (hR.isLegal _ _ y.eval_tuple) hfp hd.1 hd.2 hC
    (ne_bot_of_gt hγC) hn hanc
  -- the bottom-pattern clause over `y`, witnessed nonempty by the display
  obtain ⟨u, hu, q, hq, he⟩ := hR.bottomPattern y E.display.toScheme E.display.label
    ⟨E.display, ⟨E.isLegal, E.restrictFace_castSuccEmb⟩, rfl, fun i j hij _ ↦ by
      rw [Fin.ext hij]⟩
  -- the literal private face of the realized type, by exact consistency
  have hqP : restrictFace Fin.castSuccEmb q = some y.type := by
    rw [← hR.isConsistent u q _ he, hu, y.eval_tuple]
  obtain ⟨d', hd', hmem⟩ := E.exists_restrictFace_mem_receivingFamily hqP hq.1
  refine ⟨(extendByLast f).trans u, ?_, d', mem_receivingFamily_of_le hmem
    (hγC.le.trans_eq hE.symm), ?_⟩
  · rw [← Function.Embedding.trans_assoc, castSuccEmb_trans_extendByLast,
      Function.Embedding.trans_assoc, hu, hf]
  · rw [hR.isConsistent u q _ he, hd']

/-! ### Donors whose new cells are labelled `⊤` -/

/-- **A donor whose new cells are all labelled `⊤` needs no reference cell**: it is anchored in
every `P` below every cell. -/
example {n m : ℕ} (P : StageType.{u} α n) (C : Fin P.card) {d : StageType.{u} α (m + 1)}
    (hd : ∀ j, Fin.last m ∈ d.toCellScheme.scope j → d.label j = ⊤) : IsAnchored P C d :=
  isAnchored_of_forall_label_eq_bot_or_top P C fun j hj ↦ Or.inr (hd j hj)

/-- **Donor tops come back only as values at least the cutoff**: a member of the receiving family
at `c` of a donor labelled `⊤` at a cell is labelled at least `c` at that cell. -/
example {n : ℕ} {d q : StageType.{u} α n} {c : Label.{u}} (hq : q ∈ receivingFamily d c)
    (i : Fin q.card) (j : Fin d.card) (hij : (i : ℕ) = j) (hj : d.label j = ⊤) :
    c ≤ q.label i := by
  have h := hq.2 i j hij
  rw [hj, top_inf_eq] at h
  exact min_eq_right_iff.mp h

/-! ### One cutoff at a time -/

/-- **Receiving one cutoff at a time**: at two permitted cutoffs a model receives a donor twice;
the two received points are not claimed to coincide, nor their types to be related beyond each
agreeing with the donor below its own cutoff. -/
example (hR : R.IsModel) (hg : HasCoupledGatedPinnedExtensions α) (x : R.Occurrence)
    {d : StageType.{u} α (x.arity + 1)} (hd : d ∈ x.type.cofaces) {c c' : Label.{u}}
    (hc : IsPermittedCutoff α c) (hc' : IsPermittedCutoff α c') :
    R.RealizesOver x.tuple (receivingFamily d c) ∧ R.RealizesOver x.tuple (receivingFamily d c') :=
  have h := hR.hasFiniteCutReceiving_of_hasCoupledGatedPinnedExtensions hg
  ⟨h x d hd c hc, h x d hd c' hc'⟩

end VaughtConjecture.Realization
