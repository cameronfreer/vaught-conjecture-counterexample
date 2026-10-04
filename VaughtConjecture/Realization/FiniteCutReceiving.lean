/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.GateRecovery
import VaughtConjecture.Realization.PrivateContext

/-!
# Finite-cut receiving for models, conditional on the gated pinned extension property

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): one occurrence over the private tuple with
the display's bottom pattern) and 3.3 (the recovery statement of (R1), item 1: agreement below a
cutoff); semantic contract, item 12 (receiving one permitted cutoff at a time).

**The theorem** (`IsModel.hasFiniteCutReceiving_of_hasGatedPinnedExtensions`).  Every model `R`
at a stage `α` at which the gated pinned extension property holds
(`StageType.HasGatedPinnedExtensions α`) has the finite-cut receiving property.  Over an
occurrence `x` (the **root**), for a coface `d` of its type (the **donor**) and a permitted
cutoff `c`, the construction is:

1. **The cutoff is an ordinal** `γ < α` (`Label.isPermittedCutoff_iff`).
2. **The private context** at the floor `γ` (`IsModel.exists_privateContext_isAnchored`): an
   occurrence `y` on `n` points containing the root as a literal face along `f`, with
   `x.arity + 1 < n`, a cell `C` of graded index `(univ, n)` labelled above `γ` (the private cap),
   and the donor anchored in the type of `y` below `C` (`StageType.IsAnchored`).
3. **The gated extension** `E` of the type of `y` over `f` with donor `d`, whose cap carries the
   label of `C`, from the gated pinned extension property.
4. **The bottom-pattern clause** over `y` for the scheme and labels of the display.  The instance
   is nonempty, witnessed by the display itself: it is a coface of the type of `y` (legal, with
   literal private face) and lies in the bottom-pattern family of its own labels.  So the guarded
   clause applies as stated, and its form for lawful sections
   (`IsModel.bottomPattern_of_isLawful`), which needs a stage that is zero or a limit, is not
   used.  The clause gives a point `u` extending `y` with type `q` in that family, and exact
   consistency gives the literal private face of `q`.
5. **Gate recovery** (`StageType.GatedExtension.exists_restrictFace_mem_receivingFamily`): the
   face `d'` of `q` along `extendByLast f` agrees with `d` below the label of the cap, which is
   that of `C`, above `γ`; so it agrees with `d` below `c` (`StageType.mem_receivingFamily_of_le`).
6. **The received occurrence** is `(extendByLast f).trans u`: it extends the root
   (`castSuccEmb_trans_extendByLast`), and its type is `d'` by exact consistency.  The new point
   is off the root because `u` is injective (`RealizesOver.exists_notMem`).

**Hypotheses, by use.**  Of the clauses of a model (`IsModel`) only these are used: uniformity
and high-arity dominance (step 2, through `IsModel.exists_privateContext`); legality of types
(the type of `y` is legal, a hypothesis of the gated pinned extension property); exact
consistency (steps 2, 4 and 6); and the bottom-pattern clause (step 4).  Nonemptiness of the
carrier, covering, and generalized saturation are not used.  There is **no hypothesis on the
stage** `α`: the floor `γ < α` comes from the cutoff, and neither a limit stage nor a stage that
is zero or a limit is assumed.

**What is and is not claimed.**  The theorem is (R1) of the table of Layer 3 **conditional on**
the named hypothesis `StageType.HasGatedPinnedExtensions α`, which is still to be proved: the
legality of a display contains an exact pinned extension of a face of the private type over the
root and a full-scope layer of grade `n` in which the gate and its twins are controlled (an
analysis, not compiled here).  This conditional theorem is not a proof of (R1).  At any stage at
which the hypothesis fails the theorem is vacuous; nothing here rules out that it fails at every
limit stage.  Receiving is at one cutoff at a time: different cutoffs may use different private
contexts and different occurrences, and nothing is claimed about uniqueness or coherence of the
received occurrences, nor about exact receiving or exact projected receiving (semantic contract,
item 12).  The received type is known only through its scheme (that of the display), its literal
private face, its bottom pattern at grades at most `n`, and its donor face, which agrees with `d`
below the cap; in particular donor tops come back only as values at least the cutoff
(`VaughtConjecture.Realization.FiniteCutReceivingExamples`).

**The anchoring corollary** (`IsModel.exists_privateContext_isAnchored`) restates the private
context of `IsModel.exists_privateContext` in the form of the anchoring hypothesis of the gated
pinned extension property: a non-bottom label of a new donor cell below the cap is not the formal
top, hence an ordinal, and its reference cell is an anchor.  A donor whose new cells are all
labelled `⊥` or `⊤` is anchored below every cell
(`StageType.isAnchored_of_forall_label_eq_bot_or_top`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-- **The private context, anchored**: over an occurrence `x` and for a donor `d` on
`x.arity + 1` points, an occurrence `y` containing `x` as a literal face along `f` (with its type
restricting along `f` to that of `x`), of arity above `x.arity + 1`, with a cell `C` of graded
index `(univ, y.arity)` labelled above `γ < α`, below which `d` is anchored in the type of `y`.
Only the uniformity, high-arity-dominance, and exact-consistency clauses are used. -/
theorem IsModel.exists_privateContext_isAnchored (hR : R.IsModel) (x : R.Occurrence)
    (d : StageType.{u} α (x.arity + 1)) {γ : Ordinal.{u}} (hγ : γ < α) :
    ∃ (y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity) (C : Fin y.type.card),
      f.trans y.tuple = x.tuple ∧ StageType.restrictFace f y.type = some x.type ∧
        x.arity + 1 < y.arity ∧ y.type.toCellScheme.gradedIndex C = (univ, y.arity) ∧
        (γ : Label.{u}) < y.type.label C ∧ StageType.IsAnchored y.type C d := by
  obtain ⟨y, f, C, hf, hn, -, hC, hγC, hanc⟩ := hR.exists_privateContext x d hγ 0
  refine ⟨y, f, C, hf, Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent hf, hn, hC,
    hγC, fun j _ hbot hlt ↦ ?_⟩
  induction hj : d.label j using recBotCoeTop with
  | bot => exact absurd hj hbot
  | coe o =>
    obtain ⟨z, i, hi, he, -, -⟩ := hanc j o hj
    exact ⟨z, i, hi.le, hj ▸ he⟩
  | top => exact absurd (hj ▸ hlt) not_top_lt

/-- **Finite-cut receiving for models, conditional on the gated pinned extension property**: a
model at a stage `α` at which `StageType.HasGatedPinnedExtensions α` holds has the finite-cut
receiving property.  This is (R1) of the table of Layer 3 conditional on that named hypothesis,
which is still to be proved; it is not a proof of (R1).

The private context at the floor of the cutoff (`IsModel.exists_privateContext_isAnchored`) and
the gated extension given by the hypothesis are realized over the private tuple by the
bottom-pattern clause, whose instance is witnessed nonempty by the display itself; gate recovery
(`StageType.GatedExtension.exists_restrictFace_mem_receivingFamily`) gives the donor face, in the
receiving family of the donor at the label of the cap, hence at the cutoff.  Of the clauses of a
model, uniformity, high-arity dominance, legality of types, exact consistency, and the
bottom-pattern clause are used; no hypothesis on the stage is.  Different cutoffs may use
different occurrences; nothing is claimed about uniqueness, coherence, or exact receiving. -/
theorem IsModel.hasFiniteCutReceiving_of_hasGatedPinnedExtensions (hR : R.IsModel)
    (hg : StageType.HasGatedPinnedExtensions α) : R.HasFiniteCutReceiving := by
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
  have hqP : StageType.restrictFace Fin.castSuccEmb q = some y.type := by
    rw [← hR.isConsistent u q _ he, hu, y.eval_tuple]
  obtain ⟨d', hd', hmem⟩ := E.exists_restrictFace_mem_receivingFamily hqP hq
  refine ⟨(extendByLast f).trans u, ?_, d', StageType.mem_receivingFamily_of_le hmem
    (hγC.le.trans_eq hE.symm), ?_⟩
  · rw [← Function.Embedding.trans_assoc, castSuccEmb_trans_extendByLast,
      Function.Embedding.trans_assoc, hu, hf]
  · rw [hR.isConsistent u q _ he, hd']

end Realization

end VaughtConjecture
