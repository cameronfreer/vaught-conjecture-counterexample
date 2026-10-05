/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.GateRecovery
import VaughtConjecture.Realization.PrivateContext

/-!
# Finite-cut receiving for models, conditional on the coupled gated pinned extension property

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): one occurrence over the private tuple on
the scheme of the display) and 3.3 (the recovery statement of (R1), item 1: agreement below a
cutoff); semantic contract, item 12 (receiving one permitted cutoff at a time).

**The theorem** (`IsModel.hasFiniteCutReceiving_of_hasCoupledGatedPinnedExtensions`).  Every model
`R` at a stage `α` at which the coupled gated pinned extension property holds
(`StageType.HasCoupledGatedPinnedExtensions α`) has the finite-cut receiving property.  The
hypothesis is **a named hypothesis that is open**, so this theorem is (R1) of the table of Layer 3
**conditional on it, and not a proof of (R1)**.  The gated pinned extension property
(`StageType.HasGatedPinnedExtensions`), whose displays label the twins of the gate `⊥`, fails at
every stage (`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`); the coupled property
replaces that clause by a condition on the rows of the display (`CellScheme.Rows.TwinsReadGate`:
every twin reads the gate at least as the cap).

Over an occurrence `x` (the **root**), for a coface `d` of its type (the **donor**) and a
permitted cutoff `c`, the construction is:

1. **The cutoff is an ordinal** `γ < α` (`Label.isPermittedCutoff_iff`).
2. **The private context** at the floor `γ` (`IsModel.exists_privateContext_isAnchored`): an
   occurrence `y` on `n` points containing the root as a literal face along `f`, with
   `x.arity + 1 < n`, a cell `C` of graded index `(univ, n)` labelled above `γ` (the private cap),
   and the donor anchored in the type of `y` below `C` (`StageType.IsAnchored`).
3. **The coupled gated extension** `E` of the type of `y` over `f` with donor `d`, whose cap
   carries the label of `C`, from the hypothesis.
4. **Generalized saturation** over `y` for the scheme of the display.  The instance is nonempty,
   witnessed by the display itself, a legal coface of the type of `y`.  The clause gives a point
   `u` extending `y` with a type `q` on the scheme of the display, and exact consistency gives the
   literal private face of `q`.
5. **Gate recovery** (`StageType.CoupledGatedExtension.exists_restrictFace_mem_receivingFamily`):
   the face `d'` of `q` along `extendByLast f` agrees with `d` below the label of the cap, which
   is that of `C`, above `γ`; so it agrees with `d` below `c`
   (`StageType.mem_receivingFamily_of_le`).
   The coupling gives the gate inequality for every lawful labelling of the rows of the display,
   so no label of `q` at the twins of the gate is read.
6. **The received occurrence** is `(extendByLast f).trans u`: it extends the root
   (`castSuccEmb_trans_extendByLast`), and its type is `d'` by exact consistency.

Steps 1–3 and 6 are those of the assembly from the gated pinned extension property.  Step 4 used
the bottom-pattern clause there, because gate recovery read the labels `⊥` of the twins in the
realized type; with the coupling, generalized saturation suffices.  The bottom-pattern clause also
works, since its family lies in the family of generalized saturation
(`VaughtConjecture.Realization.CoupledFiniteCutReceivingExamples`).

**Hypotheses, by use.**  Of the clauses of a model (`IsModel`) only these are used: uniformity
and high-arity dominance (step 2, through `IsModel.exists_privateContext`); legality of types (the
type of `y` is legal, a hypothesis of the coupled property); exact consistency (steps 2, 4 and 6);
and generalized saturation (step 4).  Nonemptiness of the carrier and covering are not used.  There
is **no hypothesis on the stage** `α`.

**The open point.**  The coupled property is proved at one input only, the input that refutes the
gated pinned extension property: the private type `GatedExtensionCounterexample.P α`, the empty
root, the donor `P α|{0}` (one cell, labelled `⊥`), and the cap `3`
(`CoupledGateExamples.exists_coupledGatedExtension_comap_g₁`).  Since the gate dominates the cap in
every lawful labelling, its general form needs, at each lift from a coatom whose prescriptions force
the gate below a label `v`, a lawful private labelling in the cap ball with the cap at most `v`.
**Cap lowering (CL)**, stated in the docstring of `StageType.HasCoupledGatedPinnedExtensions`, is
the uniform form of this requirement, over every labelling `p` lawful below `(F, n - 1)` in the cap
ball and every `v` at least the cap: a strengthening, not shown necessary.  A failure of (CL)
refutes the coupled design only at a pair `(p, v)` that a forcing prescription from an anchored
legal donor actually realizes.  The donor labelled `⊤` on `P α`, which exercises (CL), is not
compiled (prospective).  At any stage at which the hypothesis fails the theorem is vacuous, and
nothing here rules out that it fails at every limit stage.


**Special cases.**  The empty root; donors whose new cells are labelled `⊥` or `⊤`, which are
anchored below every cell (`StageType.isAnchored_of_forall_label_eq_bot_or_top`); donor tops,
which come back only as values at least the cutoff; and one cutoff at a time
(`VaughtConjecture.Realization.CoupledFiniteCutReceivingExamples`).

**Questions on the source.**  The private context of [Kni26, Lemma 8.1.1] carries a marker, which
is not acquired here (`IsModel.exists_privateContext` acquires the private cap and the reference
cells only) and not read by the coupled gated extension.  Four questions on that lemma and the
construction in its proof are open:

* (M1) In the scheme built on the private points and the new point, which cells besides the gate
  have graded index `(univ, n)`, and what are their entries at the gate and at the private cap: a
  unique gate, twins labelled `⊥` (refuted on `P α`), or twins coupled to the gate as here?
* (M2) Is the marker read by any row of that scheme, and with which entries: does every twin read
  it as `⊥`, with the marker not labelled `⊥` (which forces the twins to `⊥`, excluded on `P α`),
  or does the gate read every donor top through the marker, and does that reading replace the
  reading `top` and make the lift that lowers the cap possible?
* (M3) In the recovery argument, how is the case excluded in which a twin, not the gate, serves
  availability for the cap: by a bottom pattern, by a condition on the rows, by the marker, or not
  at all?
* (M4) Does the private context of the lemma satisfy a condition that excludes private types like
  `P α`, such as a marker of grade below `n` not labelled `⊥`, or a unique cell of full scope and
  full grade?

**What is not assumed.**  None of the following is assumed or claimed here: (R1), receiving,
uniqueness or coherence of expansions; the coupled property itself, beyond its one compiled
input; that the coupled property holds for `P α` at its other donors (a donor labelled `⊤`, donors
with several new cells) or for other private types; that the twins of the gate are `⊥` or that
the gate is unique; that a layer of copies of the private cells of full grade, with the gate the
copy of the cap, extends to the cells containing the new point; that the marker controls the
twins; that a cell added by `Scheme.fieldLayer` can serve as the gate; coding of the anchored
entries by `Label.canonicalCode`; the transitivity of [Kni26, Lemma 2.3.14] or the offset bound of
[Kni26, Lemma 2.5.13]; exact projected receiving.
Different cutoffs may use different private contexts and different occurrences.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-- **Finite-cut receiving for models, conditional on the coupled gated pinned extension
property**: a model at a stage `α` at which `StageType.HasCoupledGatedPinnedExtensions α` holds
has the finite-cut receiving property.  This is (R1) of the table of Layer 3 conditional on that
named hypothesis, which is open; it is not a proof of (R1).

The private context at the floor of the cutoff (`IsModel.exists_privateContext_isAnchored`) and
the coupled gated extension given by the hypothesis are realized over the private tuple by
generalized saturation, whose instance is witnessed nonempty by the display itself; gate recovery
with the twin–gate coupling
(`StageType.CoupledGatedExtension.exists_restrictFace_mem_receivingFamily`) gives the donor face,
in the receiving family of the donor at the label of the cap, hence at the cutoff.  Of the clauses
of a model, uniformity, high-arity dominance, legality of types, exact consistency, and
generalized saturation are used; no hypothesis on the stage is.  Different cutoffs may use
different occurrences; nothing is claimed about uniqueness, coherence, or exact receiving. -/
theorem IsModel.hasFiniteCutReceiving_of_hasCoupledGatedPinnedExtensions (hR : R.IsModel)
    (hg : StageType.HasCoupledGatedPinnedExtensions α) : R.HasFiniteCutReceiving := by
  intro x d hd c hc
  obtain ⟨γ, hγα, rfl⟩ := isPermittedCutoff_iff.mp hc
  obtain ⟨y, f, C, hf, hfp, hn, hC, hγC, hanc⟩ := hR.exists_privateContext_isAnchored x d hγα
  obtain ⟨E, hE⟩ := hg y.type f x.type d C (hR.isLegal _ _ y.eval_tuple) hfp hd.1 hd.2 hC
    (ne_bot_of_gt hγC) hn hanc
  -- generalized saturation over `y`, witnessed nonempty by the display
  obtain ⟨u, hu, q, hq, he⟩ := hR.saturation y E.display.toScheme
    ⟨E.display, ⟨E.isLegal, E.restrictFace_castSuccEmb⟩, rfl⟩
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
